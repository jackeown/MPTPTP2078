%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1432+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:40 EST 2020

% Result     : Theorem 2.38s
% Output     : CNFRefutation 2.38s
% Verified   : 
% Statistics : Number of formulae       :  179 ( 419 expanded)
%              Number of clauses        :  119 ( 131 expanded)
%              Number of leaves         :   12 ( 110 expanded)
%              Depth                    :   13
%              Number of atoms          : 1490 (5366 expanded)
%              Number of equality atoms :  267 ( 267 expanded)
%              Maximal formula depth    :   19 (   9 average)
%              Maximal clause size      :   32 (   7 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,X0)
             => ! [X3] :
                  ( m1_subset_1(X3,X1)
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                        & v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0)
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                            & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                            & v1_funct_1(X5) )
                         => ( ( r1_binop_1(X1,X3,X5)
                              & r1_binop_1(X0,X2,X4) )
                          <=> r1_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( r1_binop_1(X1,X3,X5)
                              & r1_binop_1(X0,X2,X4) )
                          <=> r1_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                          | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                      | ~ v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,X1) )
              | ~ m1_subset_1(X2,X0) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( r1_binop_1(X1,X3,X5)
                              & r1_binop_1(X0,X2,X4) )
                          <=> r1_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                          | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                      | ~ v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,X1) )
              | ~ m1_subset_1(X2,X0) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( ( r1_binop_1(X1,X3,X5)
                                & r1_binop_1(X0,X2,X4) )
                              | ~ r1_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5)) )
                            & ( r1_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5))
                              | ~ r1_binop_1(X1,X3,X5)
                              | ~ r1_binop_1(X0,X2,X4) ) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                          | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                      | ~ v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,X1) )
              | ~ m1_subset_1(X2,X0) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( ( r1_binop_1(X1,X3,X5)
                                & r1_binop_1(X0,X2,X4) )
                              | ~ r1_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5)) )
                            & ( r1_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5))
                              | ~ r1_binop_1(X1,X3,X5)
                              | ~ r1_binop_1(X0,X2,X4) ) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                          | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                      | ~ v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,X1) )
              | ~ m1_subset_1(X2,X0) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f42,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5))
      | ~ r1_binop_1(X1,X3,X5)
      | ~ r1_binop_1(X0,X2,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,X1)
      | ~ m1_subset_1(X2,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f5,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,X0)
             => ! [X3] :
                  ( m1_subset_1(X3,X1)
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                        & v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0)
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                            & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                            & v1_funct_1(X5) )
                         => ( ( r2_binop_1(X1,X3,X5)
                              & r2_binop_1(X0,X2,X4) )
                          <=> r2_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( r2_binop_1(X1,X3,X5)
                              & r2_binop_1(X0,X2,X4) )
                          <=> r2_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                          | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                      | ~ v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,X1) )
              | ~ m1_subset_1(X2,X0) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( r2_binop_1(X1,X3,X5)
                              & r2_binop_1(X0,X2,X4) )
                          <=> r2_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                          | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                      | ~ v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,X1) )
              | ~ m1_subset_1(X2,X0) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( ( r2_binop_1(X1,X3,X5)
                                & r2_binop_1(X0,X2,X4) )
                              | ~ r2_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5)) )
                            & ( r2_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5))
                              | ~ r2_binop_1(X1,X3,X5)
                              | ~ r2_binop_1(X0,X2,X4) ) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                          | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                      | ~ v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,X1) )
              | ~ m1_subset_1(X2,X0) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( ( r2_binop_1(X1,X3,X5)
                                & r2_binop_1(X0,X2,X4) )
                              | ~ r2_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5)) )
                            & ( r2_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5))
                              | ~ r2_binop_1(X1,X3,X5)
                              | ~ r2_binop_1(X0,X2,X4) ) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                          | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                      | ~ v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,X1) )
              | ~ m1_subset_1(X2,X0) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f45,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5))
      | ~ r2_binop_1(X1,X3,X5)
      | ~ r2_binop_1(X0,X2,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,X1)
      | ~ m1_subset_1(X2,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
            & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
            & v1_funct_1(X2) )
         => ( r3_binop_1(X0,X1,X2)
          <=> ( r2_binop_1(X0,X1,X2)
              & r1_binop_1(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r3_binop_1(X0,X1,X2)
          <=> ( r2_binop_1(X0,X1,X2)
              & r1_binop_1(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
          | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
          | ~ v1_funct_1(X2) )
      | ~ m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r3_binop_1(X0,X1,X2)
          <=> ( r2_binop_1(X0,X1,X2)
              & r1_binop_1(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
          | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
          | ~ v1_funct_1(X2) )
      | ~ m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f8])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r3_binop_1(X0,X1,X2)
              | ~ r2_binop_1(X0,X1,X2)
              | ~ r1_binop_1(X0,X1,X2) )
            & ( ( r2_binop_1(X0,X1,X2)
                & r1_binop_1(X0,X1,X2) )
              | ~ r3_binop_1(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
          | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
          | ~ v1_funct_1(X2) )
      | ~ m1_subset_1(X1,X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r3_binop_1(X0,X1,X2)
              | ~ r2_binop_1(X0,X1,X2)
              | ~ r1_binop_1(X0,X1,X2) )
            & ( ( r2_binop_1(X0,X1,X2)
                & r1_binop_1(X0,X1,X2) )
              | ~ r3_binop_1(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
          | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
          | ~ v1_funct_1(X2) )
      | ~ m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f20])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r2_binop_1(X0,X1,X2)
      | ~ r3_binop_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r1_binop_1(X0,X1,X2)
      | ~ r3_binop_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r3_binop_1(X0,X1,X2)
      | ~ r2_binop_1(X0,X1,X2)
      | ~ r1_binop_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f3,axiom,(
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

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k6_filter_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)),k2_zfmisc_1(X0,X1))))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k6_filter_1(X0,X1,X2,X3),k2_zfmisc_1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)),k2_zfmisc_1(X0,X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k6_filter_1(X0,X1,X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f44,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_binop_1(X1,X3,X5)
      | ~ r1_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,X1)
      | ~ m1_subset_1(X2,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f43,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_binop_1(X0,X2,X4)
      | ~ r1_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,X1)
      | ~ m1_subset_1(X2,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f46,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_binop_1(X0,X2,X4)
      | ~ r2_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,X1)
      | ~ m1_subset_1(X2,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f47,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_binop_1(X1,X3,X5)
      | ~ r2_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,X1)
      | ~ m1_subset_1(X2,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X1)
        & m1_subset_1(X2,X0)
        & ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k1_domain_1(X0,X1,X2,X3),k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k1_domain_1(X0,X1,X2,X3),k2_zfmisc_1(X0,X1))
      | ~ m1_subset_1(X3,X1)
      | ~ m1_subset_1(X2,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k1_domain_1(X0,X1,X2,X3),k2_zfmisc_1(X0,X1))
      | ~ m1_subset_1(X3,X1)
      | ~ m1_subset_1(X2,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k1_domain_1(X0,X1,X2,X3),k2_zfmisc_1(X0,X1))
      | ~ m1_subset_1(X3,X1)
      | ~ m1_subset_1(X2,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f6,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,X0)
             => ! [X3] :
                  ( m1_subset_1(X3,X1)
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                        & v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0)
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                            & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                            & v1_funct_1(X5) )
                         => ( ( r3_binop_1(X1,X3,X5)
                              & r3_binop_1(X0,X2,X4) )
                          <=> r3_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( m1_subset_1(X2,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,X1)
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                          & v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0)
                          & v1_funct_1(X4) )
                       => ! [X5] :
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                              & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                              & v1_funct_1(X5) )
                           => ( ( r3_binop_1(X1,X3,X5)
                                & r3_binop_1(X0,X2,X4) )
                            <=> r3_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5)) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ( r3_binop_1(X1,X3,X5)
                              & r3_binop_1(X0,X2,X4) )
                          <~> r3_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5)) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                          & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                      & v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0)
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,X1) )
              & m1_subset_1(X2,X0) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ( r3_binop_1(X1,X3,X5)
                              & r3_binop_1(X0,X2,X4) )
                          <~> r3_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5)) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                          & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                      & v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0)
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,X1) )
              & m1_subset_1(X2,X0) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ r3_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5))
                            | ~ r3_binop_1(X1,X3,X5)
                            | ~ r3_binop_1(X0,X2,X4) )
                          & ( r3_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5))
                            | ( r3_binop_1(X1,X3,X5)
                              & r3_binop_1(X0,X2,X4) ) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                          & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                      & v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0)
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,X1) )
              & m1_subset_1(X2,X0) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ r3_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5))
                            | ~ r3_binop_1(X1,X3,X5)
                            | ~ r3_binop_1(X0,X2,X4) )
                          & ( r3_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5))
                            | ( r3_binop_1(X1,X3,X5)
                              & r3_binop_1(X0,X2,X4) ) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                          & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                      & v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0)
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,X1) )
              & m1_subset_1(X2,X0) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f33,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ( ~ r3_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5))
            | ~ r3_binop_1(X1,X3,X5)
            | ~ r3_binop_1(X0,X2,X4) )
          & ( r3_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5))
            | ( r3_binop_1(X1,X3,X5)
              & r3_binop_1(X0,X2,X4) ) )
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
          & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
          & v1_funct_1(X5) )
     => ( ( ~ r3_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,sK5))
          | ~ r3_binop_1(X1,X3,sK5)
          | ~ r3_binop_1(X0,X2,X4) )
        & ( r3_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,sK5))
          | ( r3_binop_1(X1,X3,sK5)
            & r3_binop_1(X0,X2,X4) ) )
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
        & v1_funct_2(sK5,k2_zfmisc_1(X1,X1),X1)
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ( ~ r3_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5))
                | ~ r3_binop_1(X1,X3,X5)
                | ~ r3_binop_1(X0,X2,X4) )
              & ( r3_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5))
                | ( r3_binop_1(X1,X3,X5)
                  & r3_binop_1(X0,X2,X4) ) )
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
              & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
              & v1_funct_1(X5) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
          & v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0)
          & v1_funct_1(X4) )
     => ( ? [X5] :
            ( ( ~ r3_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,sK4,X5))
              | ~ r3_binop_1(X1,X3,X5)
              | ~ r3_binop_1(X0,X2,sK4) )
            & ( r3_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,sK4,X5))
              | ( r3_binop_1(X1,X3,X5)
                & r3_binop_1(X0,X2,sK4) ) )
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
            & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
            & v1_funct_1(X5) )
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
        & v1_funct_2(sK4,k2_zfmisc_1(X0,X0),X0)
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ( ~ r3_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5))
                    | ~ r3_binop_1(X1,X3,X5)
                    | ~ r3_binop_1(X0,X2,X4) )
                  & ( r3_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5))
                    | ( r3_binop_1(X1,X3,X5)
                      & r3_binop_1(X0,X2,X4) ) )
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                  & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                  & v1_funct_1(X5) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
              & v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0)
              & v1_funct_1(X4) )
          & m1_subset_1(X3,X1) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ( ~ r3_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,sK3),k6_filter_1(X0,X1,X4,X5))
                  | ~ r3_binop_1(X1,sK3,X5)
                  | ~ r3_binop_1(X0,X2,X4) )
                & ( r3_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,sK3),k6_filter_1(X0,X1,X4,X5))
                  | ( r3_binop_1(X1,sK3,X5)
                    & r3_binop_1(X0,X2,X4) ) )
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                & v1_funct_1(X5) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
            & v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0)
            & v1_funct_1(X4) )
        & m1_subset_1(sK3,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ( ~ r3_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5))
                        | ~ r3_binop_1(X1,X3,X5)
                        | ~ r3_binop_1(X0,X2,X4) )
                      & ( r3_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5))
                        | ( r3_binop_1(X1,X3,X5)
                          & r3_binop_1(X0,X2,X4) ) )
                      & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                      & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                      & v1_funct_1(X5) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                  & v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0)
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,X1) )
          & m1_subset_1(X2,X0) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ( ~ r3_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,sK2,X3),k6_filter_1(X0,X1,X4,X5))
                      | ~ r3_binop_1(X1,X3,X5)
                      | ~ r3_binop_1(X0,sK2,X4) )
                    & ( r3_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,sK2,X3),k6_filter_1(X0,X1,X4,X5))
                      | ( r3_binop_1(X1,X3,X5)
                        & r3_binop_1(X0,sK2,X4) ) )
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                    & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                    & v1_funct_1(X5) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                & v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0)
                & v1_funct_1(X4) )
            & m1_subset_1(X3,X1) )
        & m1_subset_1(sK2,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ r3_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5))
                            | ~ r3_binop_1(X1,X3,X5)
                            | ~ r3_binop_1(X0,X2,X4) )
                          & ( r3_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5))
                            | ( r3_binop_1(X1,X3,X5)
                              & r3_binop_1(X0,X2,X4) ) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                          & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                      & v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0)
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,X1) )
              & m1_subset_1(X2,X0) )
          & ~ v1_xboole_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ( ~ r3_binop_1(k2_zfmisc_1(X0,sK1),k1_domain_1(X0,sK1,X2,X3),k6_filter_1(X0,sK1,X4,X5))
                          | ~ r3_binop_1(sK1,X3,X5)
                          | ~ r3_binop_1(X0,X2,X4) )
                        & ( r3_binop_1(k2_zfmisc_1(X0,sK1),k1_domain_1(X0,sK1,X2,X3),k6_filter_1(X0,sK1,X4,X5))
                          | ( r3_binop_1(sK1,X3,X5)
                            & r3_binop_1(X0,X2,X4) ) )
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
                        & v1_funct_2(X5,k2_zfmisc_1(sK1,sK1),sK1)
                        & v1_funct_1(X5) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                    & v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0)
                    & v1_funct_1(X4) )
                & m1_subset_1(X3,sK1) )
            & m1_subset_1(X2,X0) )
        & ~ v1_xboole_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ( ~ r3_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5))
                              | ~ r3_binop_1(X1,X3,X5)
                              | ~ r3_binop_1(X0,X2,X4) )
                            & ( r3_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5))
                              | ( r3_binop_1(X1,X3,X5)
                                & r3_binop_1(X0,X2,X4) ) )
                            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                            & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                            & v1_funct_1(X5) )
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                        & v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0)
                        & v1_funct_1(X4) )
                    & m1_subset_1(X3,X1) )
                & m1_subset_1(X2,X0) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ r3_binop_1(k2_zfmisc_1(sK0,X1),k1_domain_1(sK0,X1,X2,X3),k6_filter_1(sK0,X1,X4,X5))
                            | ~ r3_binop_1(X1,X3,X5)
                            | ~ r3_binop_1(sK0,X2,X4) )
                          & ( r3_binop_1(k2_zfmisc_1(sK0,X1),k1_domain_1(sK0,X1,X2,X3),k6_filter_1(sK0,X1,X4,X5))
                            | ( r3_binop_1(X1,X3,X5)
                              & r3_binop_1(sK0,X2,X4) ) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                          & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
                      & v1_funct_2(X4,k2_zfmisc_1(sK0,sK0),sK0)
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,X1) )
              & m1_subset_1(X2,sK0) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ( ~ r3_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5))
      | ~ r3_binop_1(sK1,sK3,sK5)
      | ~ r3_binop_1(sK0,sK2,sK4) )
    & ( r3_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5))
      | ( r3_binop_1(sK1,sK3,sK5)
        & r3_binop_1(sK0,sK2,sK4) ) )
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    & v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    & v1_funct_1(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    & v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,sK1)
    & m1_subset_1(sK2,sK0)
    & ~ v1_xboole_0(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f27,f33,f32,f31,f30,f29,f28])).

fof(f60,plain,
    ( ~ r3_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5))
    | ~ r3_binop_1(sK1,sK3,sK5)
    | ~ r3_binop_1(sK0,sK2,sK4) ),
    inference(cnf_transformation,[],[f34])).

fof(f59,plain,
    ( r3_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5))
    | r3_binop_1(sK1,sK3,sK5) ),
    inference(cnf_transformation,[],[f34])).

fof(f58,plain,
    ( r3_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5))
    | r3_binop_1(sK0,sK2,sK4) ),
    inference(cnf_transformation,[],[f34])).

fof(f57,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) ),
    inference(cnf_transformation,[],[f34])).

fof(f56,plain,(
    v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f55,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f34])).

fof(f54,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) ),
    inference(cnf_transformation,[],[f34])).

fof(f53,plain,(
    v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f52,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f34])).

fof(f51,plain,(
    m1_subset_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f50,plain,(
    m1_subset_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f49,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f48,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_9,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_2(X2,k2_zfmisc_1(X3,X3),X3)
    | ~ r1_binop_1(X1,X4,X0)
    | ~ r1_binop_1(X3,X5,X2)
    | r1_binop_1(k2_zfmisc_1(X3,X1),k1_domain_1(X3,X1,X5,X4),k6_filter_1(X3,X1,X2,X0))
    | ~ m1_subset_1(X4,X1)
    | ~ m1_subset_1(X5,X3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X3,X3),X3)))
    | v1_xboole_0(X3)
    | v1_xboole_0(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_274,plain,
    ( ~ v1_funct_2(X0_46,k2_zfmisc_1(X0_45,X0_45),X0_45)
    | ~ v1_funct_2(X1_46,k2_zfmisc_1(X1_45,X1_45),X1_45)
    | ~ r1_binop_1(X0_45,X2_46,X0_46)
    | ~ r1_binop_1(X1_45,X3_46,X1_46)
    | r1_binop_1(k2_zfmisc_1(X1_45,X0_45),k1_domain_1(X1_45,X0_45,X3_46,X2_46),k6_filter_1(X1_45,X0_45,X1_46,X0_46))
    | ~ m1_subset_1(X2_46,X0_45)
    | ~ m1_subset_1(X3_46,X1_45)
    | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0_45,X0_45),X0_45)))
    | ~ m1_subset_1(X1_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1_45,X1_45),X1_45)))
    | v1_xboole_0(X1_45)
    | v1_xboole_0(X0_45)
    | ~ v1_funct_1(X0_46)
    | ~ v1_funct_1(X1_46) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_826,plain,
    ( ~ v1_funct_2(X0_46,k2_zfmisc_1(X0_45,X0_45),X0_45)
    | ~ v1_funct_2(X1_46,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ r1_binop_1(X0_45,X2_46,X0_46)
    | r1_binop_1(k2_zfmisc_1(X0_45,sK1),k1_domain_1(X0_45,sK1,X2_46,sK3),k6_filter_1(X0_45,sK1,X0_46,X1_46))
    | ~ r1_binop_1(sK1,sK3,X1_46)
    | ~ m1_subset_1(X2_46,X0_45)
    | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0_45,X0_45),X0_45)))
    | ~ m1_subset_1(X1_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ m1_subset_1(sK3,sK1)
    | v1_xboole_0(X0_45)
    | v1_xboole_0(sK1)
    | ~ v1_funct_1(X1_46)
    | ~ v1_funct_1(X0_46) ),
    inference(instantiation,[status(thm)],[c_274])).

cnf(c_1626,plain,
    ( ~ v1_funct_2(X0_46,k2_zfmisc_1(X0_45,X0_45),X0_45)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ r1_binop_1(X0_45,X1_46,X0_46)
    | r1_binop_1(k2_zfmisc_1(X0_45,sK1),k1_domain_1(X0_45,sK1,X1_46,sK3),k6_filter_1(X0_45,sK1,X0_46,sK5))
    | ~ r1_binop_1(sK1,sK3,sK5)
    | ~ m1_subset_1(X1_46,X0_45)
    | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0_45,X0_45),X0_45)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ m1_subset_1(sK3,sK1)
    | v1_xboole_0(X0_45)
    | v1_xboole_0(sK1)
    | ~ v1_funct_1(X0_46)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_826])).

cnf(c_1807,plain,
    ( ~ v1_funct_2(X0_46,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | r1_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,X0_46,sK5))
    | ~ r1_binop_1(sK1,sK3,sK5)
    | ~ r1_binop_1(sK0,sK2,X0_46)
    | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ m1_subset_1(sK3,sK1)
    | ~ m1_subset_1(sK2,sK0)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ v1_funct_1(X0_46)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_1626])).

cnf(c_1808,plain,
    ( v1_funct_2(X0_46,k2_zfmisc_1(sK0,sK0),sK0) != iProver_top
    | v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1) != iProver_top
    | r1_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,X0_46,sK5)) = iProver_top
    | r1_binop_1(sK1,sK3,sK5) != iProver_top
    | r1_binop_1(sK0,sK2,X0_46) != iProver_top
    | m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) != iProver_top
    | m1_subset_1(sK3,sK1) != iProver_top
    | m1_subset_1(sK2,sK0) != iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK0) = iProver_top
    | v1_funct_1(X0_46) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1807])).

cnf(c_1810,plain,
    ( v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1) != iProver_top
    | v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0) != iProver_top
    | r1_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5)) = iProver_top
    | r1_binop_1(sK1,sK3,sK5) != iProver_top
    | r1_binop_1(sK0,sK2,sK4) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) != iProver_top
    | m1_subset_1(sK3,sK1) != iProver_top
    | m1_subset_1(sK2,sK0) != iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK0) = iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1808])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_2(X2,k2_zfmisc_1(X3,X3),X3)
    | ~ r2_binop_1(X1,X4,X0)
    | ~ r2_binop_1(X3,X5,X2)
    | r2_binop_1(k2_zfmisc_1(X3,X1),k1_domain_1(X3,X1,X5,X4),k6_filter_1(X3,X1,X2,X0))
    | ~ m1_subset_1(X4,X1)
    | ~ m1_subset_1(X5,X3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X3,X3),X3)))
    | v1_xboole_0(X3)
    | v1_xboole_0(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_271,plain,
    ( ~ v1_funct_2(X0_46,k2_zfmisc_1(X0_45,X0_45),X0_45)
    | ~ v1_funct_2(X1_46,k2_zfmisc_1(X1_45,X1_45),X1_45)
    | ~ r2_binop_1(X0_45,X2_46,X0_46)
    | ~ r2_binop_1(X1_45,X3_46,X1_46)
    | r2_binop_1(k2_zfmisc_1(X1_45,X0_45),k1_domain_1(X1_45,X0_45,X3_46,X2_46),k6_filter_1(X1_45,X0_45,X1_46,X0_46))
    | ~ m1_subset_1(X2_46,X0_45)
    | ~ m1_subset_1(X3_46,X1_45)
    | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0_45,X0_45),X0_45)))
    | ~ m1_subset_1(X1_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1_45,X1_45),X1_45)))
    | v1_xboole_0(X1_45)
    | v1_xboole_0(X0_45)
    | ~ v1_funct_1(X0_46)
    | ~ v1_funct_1(X1_46) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_801,plain,
    ( ~ v1_funct_2(X0_46,k2_zfmisc_1(X0_45,X0_45),X0_45)
    | ~ v1_funct_2(X1_46,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ r2_binop_1(X0_45,X2_46,X0_46)
    | r2_binop_1(k2_zfmisc_1(X0_45,sK1),k1_domain_1(X0_45,sK1,X2_46,sK3),k6_filter_1(X0_45,sK1,X0_46,X1_46))
    | ~ r2_binop_1(sK1,sK3,X1_46)
    | ~ m1_subset_1(X2_46,X0_45)
    | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0_45,X0_45),X0_45)))
    | ~ m1_subset_1(X1_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ m1_subset_1(sK3,sK1)
    | v1_xboole_0(X0_45)
    | v1_xboole_0(sK1)
    | ~ v1_funct_1(X1_46)
    | ~ v1_funct_1(X0_46) ),
    inference(instantiation,[status(thm)],[c_271])).

cnf(c_1618,plain,
    ( ~ v1_funct_2(X0_46,k2_zfmisc_1(X0_45,X0_45),X0_45)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ r2_binop_1(X0_45,X1_46,X0_46)
    | r2_binop_1(k2_zfmisc_1(X0_45,sK1),k1_domain_1(X0_45,sK1,X1_46,sK3),k6_filter_1(X0_45,sK1,X0_46,sK5))
    | ~ r2_binop_1(sK1,sK3,sK5)
    | ~ m1_subset_1(X1_46,X0_45)
    | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0_45,X0_45),X0_45)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ m1_subset_1(sK3,sK1)
    | v1_xboole_0(X0_45)
    | v1_xboole_0(sK1)
    | ~ v1_funct_1(X0_46)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_801])).

cnf(c_1761,plain,
    ( ~ v1_funct_2(X0_46,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | r2_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,X0_46,sK5))
    | ~ r2_binop_1(sK1,sK3,sK5)
    | ~ r2_binop_1(sK0,sK2,X0_46)
    | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ m1_subset_1(sK3,sK1)
    | ~ m1_subset_1(sK2,sK0)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ v1_funct_1(X0_46)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_1618])).

cnf(c_1762,plain,
    ( v1_funct_2(X0_46,k2_zfmisc_1(sK0,sK0),sK0) != iProver_top
    | v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1) != iProver_top
    | r2_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,X0_46,sK5)) = iProver_top
    | r2_binop_1(sK1,sK3,sK5) != iProver_top
    | r2_binop_1(sK0,sK2,X0_46) != iProver_top
    | m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) != iProver_top
    | m1_subset_1(sK3,sK1) != iProver_top
    | m1_subset_1(sK2,sK0) != iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK0) = iProver_top
    | v1_funct_1(X0_46) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1761])).

cnf(c_1764,plain,
    ( v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1) != iProver_top
    | v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0) != iProver_top
    | r2_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5)) = iProver_top
    | r2_binop_1(sK1,sK3,sK5) != iProver_top
    | r2_binop_1(sK0,sK2,sK4) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) != iProver_top
    | m1_subset_1(sK3,sK1) != iProver_top
    | m1_subset_1(sK2,sK0) != iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK0) = iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1762])).

cnf(c_1,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | r2_binop_1(X1,X2,X0)
    | ~ r3_binop_1(X1,X2,X0)
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_282,plain,
    ( ~ v1_funct_2(X0_46,k2_zfmisc_1(X0_45,X0_45),X0_45)
    | r2_binop_1(X0_45,X1_46,X0_46)
    | ~ r3_binop_1(X0_45,X1_46,X0_46)
    | ~ m1_subset_1(X1_46,X0_45)
    | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0_45,X0_45),X0_45)))
    | ~ v1_funct_1(X0_46) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_460,plain,
    ( ~ v1_funct_2(X0_46,k2_zfmisc_1(sK1,sK1),sK1)
    | r2_binop_1(sK1,sK3,X0_46)
    | ~ r3_binop_1(sK1,sK3,X0_46)
    | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ m1_subset_1(sK3,sK1)
    | ~ v1_funct_1(X0_46) ),
    inference(instantiation,[status(thm)],[c_282])).

cnf(c_1738,plain,
    ( ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | r2_binop_1(sK1,sK3,sK5)
    | ~ r3_binop_1(sK1,sK3,sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ m1_subset_1(sK3,sK1)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_460])).

cnf(c_1742,plain,
    ( v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1) != iProver_top
    | r2_binop_1(sK1,sK3,sK5) = iProver_top
    | r3_binop_1(sK1,sK3,sK5) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) != iProver_top
    | m1_subset_1(sK3,sK1) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1738])).

cnf(c_2,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | r1_binop_1(X1,X2,X0)
    | ~ r3_binop_1(X1,X2,X0)
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_281,plain,
    ( ~ v1_funct_2(X0_46,k2_zfmisc_1(X0_45,X0_45),X0_45)
    | r1_binop_1(X0_45,X1_46,X0_46)
    | ~ r3_binop_1(X0_45,X1_46,X0_46)
    | ~ m1_subset_1(X1_46,X0_45)
    | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0_45,X0_45),X0_45)))
    | ~ v1_funct_1(X0_46) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_440,plain,
    ( ~ v1_funct_2(X0_46,k2_zfmisc_1(sK1,sK1),sK1)
    | r1_binop_1(sK1,sK3,X0_46)
    | ~ r3_binop_1(sK1,sK3,X0_46)
    | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ m1_subset_1(sK3,sK1)
    | ~ v1_funct_1(X0_46) ),
    inference(instantiation,[status(thm)],[c_281])).

cnf(c_1739,plain,
    ( ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | r1_binop_1(sK1,sK3,sK5)
    | ~ r3_binop_1(sK1,sK3,sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ m1_subset_1(sK3,sK1)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_440])).

cnf(c_1740,plain,
    ( v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1) != iProver_top
    | r1_binop_1(sK1,sK3,sK5) = iProver_top
    | r3_binop_1(sK1,sK3,sK5) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) != iProver_top
    | m1_subset_1(sK3,sK1) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1739])).

cnf(c_0,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ r1_binop_1(X1,X2,X0)
    | ~ r2_binop_1(X1,X2,X0)
    | r3_binop_1(X1,X2,X0)
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_283,plain,
    ( ~ v1_funct_2(X0_46,k2_zfmisc_1(X0_45,X0_45),X0_45)
    | ~ r1_binop_1(X0_45,X1_46,X0_46)
    | ~ r2_binop_1(X0_45,X1_46,X0_46)
    | r3_binop_1(X0_45,X1_46,X0_46)
    | ~ m1_subset_1(X1_46,X0_45)
    | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0_45,X0_45),X0_45)))
    | ~ v1_funct_1(X0_46) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_480,plain,
    ( ~ v1_funct_2(X0_46,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ r1_binop_1(sK1,sK3,X0_46)
    | ~ r2_binop_1(sK1,sK3,X0_46)
    | r3_binop_1(sK1,sK3,X0_46)
    | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ m1_subset_1(sK3,sK1)
    | ~ v1_funct_1(X0_46) ),
    inference(instantiation,[status(thm)],[c_283])).

cnf(c_1623,plain,
    ( ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ r1_binop_1(sK1,sK3,sK5)
    | ~ r2_binop_1(sK1,sK3,sK5)
    | r3_binop_1(sK1,sK3,sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ m1_subset_1(sK3,sK1)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_480])).

cnf(c_1624,plain,
    ( v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1) != iProver_top
    | r1_binop_1(sK1,sK3,sK5) != iProver_top
    | r2_binop_1(sK1,sK3,sK5) != iProver_top
    | r3_binop_1(sK1,sK3,sK5) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) != iProver_top
    | m1_subset_1(sK3,sK1) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1623])).

cnf(c_1077,plain,
    ( ~ v1_funct_2(X0_46,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ r1_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),X0_46)
    | ~ r2_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),X0_46)
    | r3_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),X0_46)
    | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))))
    | ~ m1_subset_1(k1_domain_1(sK0,sK1,sK2,sK3),k2_zfmisc_1(sK0,sK1))
    | ~ v1_funct_1(X0_46) ),
    inference(instantiation,[status(thm)],[c_283])).

cnf(c_1615,plain,
    ( ~ v1_funct_2(k6_filter_1(sK0,sK1,sK4,sK5),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ r1_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5))
    | ~ r2_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5))
    | r3_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5))
    | ~ m1_subset_1(k6_filter_1(sK0,sK1,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))))
    | ~ m1_subset_1(k1_domain_1(sK0,sK1,sK2,sK3),k2_zfmisc_1(sK0,sK1))
    | ~ v1_funct_1(k6_filter_1(sK0,sK1,sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_1077])).

cnf(c_1616,plain,
    ( v1_funct_2(k6_filter_1(sK0,sK1,sK4,sK5),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)) != iProver_top
    | r1_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5)) != iProver_top
    | r2_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5)) != iProver_top
    | r3_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5)) = iProver_top
    | m1_subset_1(k6_filter_1(sK0,sK1,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)))) != iProver_top
    | m1_subset_1(k1_domain_1(sK0,sK1,sK2,sK3),k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_funct_1(k6_filter_1(sK0,sK1,sK4,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1615])).

cnf(c_4,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_2(X2,k2_zfmisc_1(X3,X3),X3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X3,X3),X3)))
    | m1_subset_1(k6_filter_1(X1,X3,X0,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3)),k2_zfmisc_1(X1,X3))))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_279,plain,
    ( ~ v1_funct_2(X0_46,k2_zfmisc_1(X0_45,X0_45),X0_45)
    | ~ v1_funct_2(X1_46,k2_zfmisc_1(X1_45,X1_45),X1_45)
    | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0_45,X0_45),X0_45)))
    | ~ m1_subset_1(X1_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1_45,X1_45),X1_45)))
    | m1_subset_1(k6_filter_1(X0_45,X1_45,X0_46,X1_46),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0_45,X1_45),k2_zfmisc_1(X0_45,X1_45)),k2_zfmisc_1(X0_45,X1_45))))
    | ~ v1_funct_1(X0_46)
    | ~ v1_funct_1(X1_46) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1587,plain,
    ( ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
    | m1_subset_1(k6_filter_1(sK0,sK1,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_279])).

cnf(c_1588,plain,
    ( v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1) != iProver_top
    | v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0) != iProver_top
    | m1_subset_1(k6_filter_1(sK0,sK1,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)))) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1587])).

cnf(c_5,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_2(X2,k2_zfmisc_1(X3,X3),X3)
    | v1_funct_2(k6_filter_1(X1,X3,X0,X2),k2_zfmisc_1(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3)),k2_zfmisc_1(X1,X3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X3,X3),X3)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_278,plain,
    ( ~ v1_funct_2(X0_46,k2_zfmisc_1(X0_45,X0_45),X0_45)
    | ~ v1_funct_2(X1_46,k2_zfmisc_1(X1_45,X1_45),X1_45)
    | v1_funct_2(k6_filter_1(X0_45,X1_45,X0_46,X1_46),k2_zfmisc_1(k2_zfmisc_1(X0_45,X1_45),k2_zfmisc_1(X0_45,X1_45)),k2_zfmisc_1(X0_45,X1_45))
    | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0_45,X0_45),X0_45)))
    | ~ m1_subset_1(X1_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1_45,X1_45),X1_45)))
    | ~ v1_funct_1(X0_46)
    | ~ v1_funct_1(X1_46) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1583,plain,
    ( v1_funct_2(k6_filter_1(sK0,sK1,sK4,sK5),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_278])).

cnf(c_1584,plain,
    ( v1_funct_2(k6_filter_1(sK0,sK1,sK4,sK5),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)) = iProver_top
    | v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1) != iProver_top
    | v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1583])).

cnf(c_6,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_2(X2,k2_zfmisc_1(X3,X3),X3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X3,X3),X3)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | v1_funct_1(k6_filter_1(X1,X3,X0,X2)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_277,plain,
    ( ~ v1_funct_2(X0_46,k2_zfmisc_1(X0_45,X0_45),X0_45)
    | ~ v1_funct_2(X1_46,k2_zfmisc_1(X1_45,X1_45),X1_45)
    | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0_45,X0_45),X0_45)))
    | ~ m1_subset_1(X1_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1_45,X1_45),X1_45)))
    | ~ v1_funct_1(X0_46)
    | ~ v1_funct_1(X1_46)
    | v1_funct_1(k6_filter_1(X0_45,X1_45,X0_46,X1_46)) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1579,plain,
    ( ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | v1_funct_1(k6_filter_1(sK0,sK1,sK4,sK5))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_277])).

cnf(c_1580,plain,
    ( v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1) != iProver_top
    | v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) != iProver_top
    | v1_funct_1(k6_filter_1(sK0,sK1,sK4,sK5)) = iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1579])).

cnf(c_1079,plain,
    ( ~ v1_funct_2(X0_46,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | r1_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),X0_46)
    | ~ r3_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),X0_46)
    | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))))
    | ~ m1_subset_1(k1_domain_1(sK0,sK1,sK2,sK3),k2_zfmisc_1(sK0,sK1))
    | ~ v1_funct_1(X0_46) ),
    inference(instantiation,[status(thm)],[c_281])).

cnf(c_1575,plain,
    ( ~ v1_funct_2(k6_filter_1(sK0,sK1,sK4,sK5),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | r1_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5))
    | ~ r3_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5))
    | ~ m1_subset_1(k6_filter_1(sK0,sK1,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))))
    | ~ m1_subset_1(k1_domain_1(sK0,sK1,sK2,sK3),k2_zfmisc_1(sK0,sK1))
    | ~ v1_funct_1(k6_filter_1(sK0,sK1,sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_1079])).

cnf(c_1576,plain,
    ( v1_funct_2(k6_filter_1(sK0,sK1,sK4,sK5),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)) != iProver_top
    | r1_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5)) = iProver_top
    | r3_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5)) != iProver_top
    | m1_subset_1(k6_filter_1(sK0,sK1,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)))) != iProver_top
    | m1_subset_1(k1_domain_1(sK0,sK1,sK2,sK3),k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_funct_1(k6_filter_1(sK0,sK1,sK4,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1575])).

cnf(c_1078,plain,
    ( ~ v1_funct_2(X0_46,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | r2_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),X0_46)
    | ~ r3_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),X0_46)
    | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))))
    | ~ m1_subset_1(k1_domain_1(sK0,sK1,sK2,sK3),k2_zfmisc_1(sK0,sK1))
    | ~ v1_funct_1(X0_46) ),
    inference(instantiation,[status(thm)],[c_282])).

cnf(c_1572,plain,
    ( ~ v1_funct_2(k6_filter_1(sK0,sK1,sK4,sK5),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | r2_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5))
    | ~ r3_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5))
    | ~ m1_subset_1(k6_filter_1(sK0,sK1,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))))
    | ~ m1_subset_1(k1_domain_1(sK0,sK1,sK2,sK3),k2_zfmisc_1(sK0,sK1))
    | ~ v1_funct_1(k6_filter_1(sK0,sK1,sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_1078])).

cnf(c_1573,plain,
    ( v1_funct_2(k6_filter_1(sK0,sK1,sK4,sK5),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)) != iProver_top
    | r2_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5)) = iProver_top
    | r3_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5)) != iProver_top
    | m1_subset_1(k6_filter_1(sK0,sK1,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)))) != iProver_top
    | m1_subset_1(k1_domain_1(sK0,sK1,sK2,sK3),k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_funct_1(k6_filter_1(sK0,sK1,sK4,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1572])).

cnf(c_7,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_2(X2,k2_zfmisc_1(X3,X3),X3)
    | r1_binop_1(X1,X4,X0)
    | ~ r1_binop_1(k2_zfmisc_1(X3,X1),k1_domain_1(X3,X1,X5,X4),k6_filter_1(X3,X1,X2,X0))
    | ~ m1_subset_1(X4,X1)
    | ~ m1_subset_1(X5,X3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X3,X3),X3)))
    | v1_xboole_0(X3)
    | v1_xboole_0(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_276,plain,
    ( ~ v1_funct_2(X0_46,k2_zfmisc_1(X0_45,X0_45),X0_45)
    | ~ v1_funct_2(X1_46,k2_zfmisc_1(X1_45,X1_45),X1_45)
    | r1_binop_1(X0_45,X2_46,X0_46)
    | ~ r1_binop_1(k2_zfmisc_1(X1_45,X0_45),k1_domain_1(X1_45,X0_45,X3_46,X2_46),k6_filter_1(X1_45,X0_45,X1_46,X0_46))
    | ~ m1_subset_1(X2_46,X0_45)
    | ~ m1_subset_1(X3_46,X1_45)
    | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0_45,X0_45),X0_45)))
    | ~ m1_subset_1(X1_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1_45,X1_45),X1_45)))
    | v1_xboole_0(X1_45)
    | v1_xboole_0(X0_45)
    | ~ v1_funct_1(X0_46)
    | ~ v1_funct_1(X1_46) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_625,plain,
    ( ~ v1_funct_2(X0_46,k2_zfmisc_1(X0_45,X0_45),X0_45)
    | ~ v1_funct_2(X1_46,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ r1_binop_1(k2_zfmisc_1(X0_45,sK1),k1_domain_1(X0_45,sK1,X2_46,sK3),k6_filter_1(X0_45,sK1,X0_46,X1_46))
    | r1_binop_1(sK1,sK3,X1_46)
    | ~ m1_subset_1(X2_46,X0_45)
    | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0_45,X0_45),X0_45)))
    | ~ m1_subset_1(X1_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ m1_subset_1(sK3,sK1)
    | v1_xboole_0(X0_45)
    | v1_xboole_0(sK1)
    | ~ v1_funct_1(X1_46)
    | ~ v1_funct_1(X0_46) ),
    inference(instantiation,[status(thm)],[c_276])).

cnf(c_1406,plain,
    ( ~ v1_funct_2(X0_46,k2_zfmisc_1(X0_45,X0_45),X0_45)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ r1_binop_1(k2_zfmisc_1(X0_45,sK1),k1_domain_1(X0_45,sK1,X1_46,sK3),k6_filter_1(X0_45,sK1,X0_46,sK5))
    | r1_binop_1(sK1,sK3,sK5)
    | ~ m1_subset_1(X1_46,X0_45)
    | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0_45,X0_45),X0_45)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ m1_subset_1(sK3,sK1)
    | v1_xboole_0(X0_45)
    | v1_xboole_0(sK1)
    | ~ v1_funct_1(X0_46)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_625])).

cnf(c_1542,plain,
    ( ~ v1_funct_2(X0_46,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ r1_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,X0_46,sK5))
    | r1_binop_1(sK1,sK3,sK5)
    | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ m1_subset_1(sK3,sK1)
    | ~ m1_subset_1(sK2,sK0)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ v1_funct_1(X0_46)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_1406])).

cnf(c_1543,plain,
    ( v1_funct_2(X0_46,k2_zfmisc_1(sK0,sK0),sK0) != iProver_top
    | v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1) != iProver_top
    | r1_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,X0_46,sK5)) != iProver_top
    | r1_binop_1(sK1,sK3,sK5) = iProver_top
    | m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) != iProver_top
    | m1_subset_1(sK3,sK1) != iProver_top
    | m1_subset_1(sK2,sK0) != iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK0) = iProver_top
    | v1_funct_1(X0_46) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1542])).

cnf(c_1545,plain,
    ( v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1) != iProver_top
    | v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0) != iProver_top
    | r1_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5)) != iProver_top
    | r1_binop_1(sK1,sK3,sK5) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) != iProver_top
    | m1_subset_1(sK3,sK1) != iProver_top
    | m1_subset_1(sK2,sK0) != iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK0) = iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1543])).

cnf(c_8,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_2(X2,k2_zfmisc_1(X3,X3),X3)
    | r1_binop_1(X3,X4,X2)
    | ~ r1_binop_1(k2_zfmisc_1(X3,X1),k1_domain_1(X3,X1,X4,X5),k6_filter_1(X3,X1,X2,X0))
    | ~ m1_subset_1(X5,X1)
    | ~ m1_subset_1(X4,X3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X3,X3),X3)))
    | v1_xboole_0(X3)
    | v1_xboole_0(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_275,plain,
    ( ~ v1_funct_2(X0_46,k2_zfmisc_1(X0_45,X0_45),X0_45)
    | ~ v1_funct_2(X1_46,k2_zfmisc_1(X1_45,X1_45),X1_45)
    | r1_binop_1(X1_45,X2_46,X1_46)
    | ~ r1_binop_1(k2_zfmisc_1(X1_45,X0_45),k1_domain_1(X1_45,X0_45,X2_46,X3_46),k6_filter_1(X1_45,X0_45,X1_46,X0_46))
    | ~ m1_subset_1(X3_46,X0_45)
    | ~ m1_subset_1(X2_46,X1_45)
    | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0_45,X0_45),X0_45)))
    | ~ m1_subset_1(X1_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1_45,X1_45),X1_45)))
    | v1_xboole_0(X1_45)
    | v1_xboole_0(X0_45)
    | ~ v1_funct_1(X0_46)
    | ~ v1_funct_1(X1_46) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_600,plain,
    ( ~ v1_funct_2(X0_46,k2_zfmisc_1(X0_45,X0_45),X0_45)
    | ~ v1_funct_2(X1_46,k2_zfmisc_1(sK1,sK1),sK1)
    | r1_binop_1(X0_45,X2_46,X0_46)
    | ~ r1_binop_1(k2_zfmisc_1(X0_45,sK1),k1_domain_1(X0_45,sK1,X2_46,sK3),k6_filter_1(X0_45,sK1,X0_46,X1_46))
    | ~ m1_subset_1(X2_46,X0_45)
    | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0_45,X0_45),X0_45)))
    | ~ m1_subset_1(X1_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ m1_subset_1(sK3,sK1)
    | v1_xboole_0(X0_45)
    | v1_xboole_0(sK1)
    | ~ v1_funct_1(X1_46)
    | ~ v1_funct_1(X0_46) ),
    inference(instantiation,[status(thm)],[c_275])).

cnf(c_1266,plain,
    ( ~ v1_funct_2(X0_46,k2_zfmisc_1(X0_45,X0_45),X0_45)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | r1_binop_1(X0_45,X1_46,X0_46)
    | ~ r1_binop_1(k2_zfmisc_1(X0_45,sK1),k1_domain_1(X0_45,sK1,X1_46,sK3),k6_filter_1(X0_45,sK1,X0_46,sK5))
    | ~ m1_subset_1(X1_46,X0_45)
    | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0_45,X0_45),X0_45)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ m1_subset_1(sK3,sK1)
    | v1_xboole_0(X0_45)
    | v1_xboole_0(sK1)
    | ~ v1_funct_1(X0_46)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_600])).

cnf(c_1478,plain,
    ( ~ v1_funct_2(X0_46,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ r1_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,X0_46,sK5))
    | r1_binop_1(sK0,sK2,X0_46)
    | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ m1_subset_1(sK3,sK1)
    | ~ m1_subset_1(sK2,sK0)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ v1_funct_1(X0_46)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_1266])).

cnf(c_1479,plain,
    ( v1_funct_2(X0_46,k2_zfmisc_1(sK0,sK0),sK0) != iProver_top
    | v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1) != iProver_top
    | r1_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,X0_46,sK5)) != iProver_top
    | r1_binop_1(sK0,sK2,X0_46) = iProver_top
    | m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) != iProver_top
    | m1_subset_1(sK3,sK1) != iProver_top
    | m1_subset_1(sK2,sK0) != iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK0) = iProver_top
    | v1_funct_1(X0_46) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1478])).

cnf(c_1481,plain,
    ( v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1) != iProver_top
    | v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0) != iProver_top
    | r1_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5)) != iProver_top
    | r1_binop_1(sK0,sK2,sK4) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) != iProver_top
    | m1_subset_1(sK3,sK1) != iProver_top
    | m1_subset_1(sK2,sK0) != iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK0) = iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1479])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_2(X2,k2_zfmisc_1(X3,X3),X3)
    | r2_binop_1(X3,X4,X2)
    | ~ r2_binop_1(k2_zfmisc_1(X3,X1),k1_domain_1(X3,X1,X4,X5),k6_filter_1(X3,X1,X2,X0))
    | ~ m1_subset_1(X5,X1)
    | ~ m1_subset_1(X4,X3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X3,X3),X3)))
    | v1_xboole_0(X3)
    | v1_xboole_0(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_272,plain,
    ( ~ v1_funct_2(X0_46,k2_zfmisc_1(X0_45,X0_45),X0_45)
    | ~ v1_funct_2(X1_46,k2_zfmisc_1(X1_45,X1_45),X1_45)
    | r2_binop_1(X1_45,X2_46,X1_46)
    | ~ r2_binop_1(k2_zfmisc_1(X1_45,X0_45),k1_domain_1(X1_45,X0_45,X2_46,X3_46),k6_filter_1(X1_45,X0_45,X1_46,X0_46))
    | ~ m1_subset_1(X3_46,X0_45)
    | ~ m1_subset_1(X2_46,X1_45)
    | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0_45,X0_45),X0_45)))
    | ~ m1_subset_1(X1_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1_45,X1_45),X1_45)))
    | v1_xboole_0(X1_45)
    | v1_xboole_0(X0_45)
    | ~ v1_funct_1(X0_46)
    | ~ v1_funct_1(X1_46) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_520,plain,
    ( ~ v1_funct_2(X0_46,k2_zfmisc_1(X0_45,X0_45),X0_45)
    | ~ v1_funct_2(X1_46,k2_zfmisc_1(sK1,sK1),sK1)
    | r2_binop_1(X0_45,X2_46,X0_46)
    | ~ r2_binop_1(k2_zfmisc_1(X0_45,sK1),k1_domain_1(X0_45,sK1,X2_46,sK3),k6_filter_1(X0_45,sK1,X0_46,X1_46))
    | ~ m1_subset_1(X2_46,X0_45)
    | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0_45,X0_45),X0_45)))
    | ~ m1_subset_1(X1_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ m1_subset_1(sK3,sK1)
    | v1_xboole_0(X0_45)
    | v1_xboole_0(sK1)
    | ~ v1_funct_1(X1_46)
    | ~ v1_funct_1(X0_46) ),
    inference(instantiation,[status(thm)],[c_272])).

cnf(c_738,plain,
    ( ~ v1_funct_2(X0_46,k2_zfmisc_1(X0_45,X0_45),X0_45)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | r2_binop_1(X0_45,X1_46,X0_46)
    | ~ r2_binop_1(k2_zfmisc_1(X0_45,sK1),k1_domain_1(X0_45,sK1,X1_46,sK3),k6_filter_1(X0_45,sK1,X0_46,sK5))
    | ~ m1_subset_1(X1_46,X0_45)
    | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0_45,X0_45),X0_45)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ m1_subset_1(sK3,sK1)
    | v1_xboole_0(X0_45)
    | v1_xboole_0(sK1)
    | ~ v1_funct_1(X0_46)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_520])).

cnf(c_1376,plain,
    ( ~ v1_funct_2(X0_46,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ r2_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,X0_46,sK5))
    | r2_binop_1(sK0,sK2,X0_46)
    | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ m1_subset_1(sK3,sK1)
    | ~ m1_subset_1(sK2,sK0)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ v1_funct_1(X0_46)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_738])).

cnf(c_1377,plain,
    ( v1_funct_2(X0_46,k2_zfmisc_1(sK0,sK0),sK0) != iProver_top
    | v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1) != iProver_top
    | r2_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,X0_46,sK5)) != iProver_top
    | r2_binop_1(sK0,sK2,X0_46) = iProver_top
    | m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) != iProver_top
    | m1_subset_1(sK3,sK1) != iProver_top
    | m1_subset_1(sK2,sK0) != iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK0) = iProver_top
    | v1_funct_1(X0_46) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1376])).

cnf(c_1379,plain,
    ( v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1) != iProver_top
    | v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0) != iProver_top
    | r2_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5)) != iProver_top
    | r2_binop_1(sK0,sK2,sK4) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) != iProver_top
    | m1_subset_1(sK3,sK1) != iProver_top
    | m1_subset_1(sK2,sK0) != iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK0) = iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1377])).

cnf(c_10,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_2(X2,k2_zfmisc_1(X3,X3),X3)
    | r2_binop_1(X1,X4,X0)
    | ~ r2_binop_1(k2_zfmisc_1(X3,X1),k1_domain_1(X3,X1,X5,X4),k6_filter_1(X3,X1,X2,X0))
    | ~ m1_subset_1(X4,X1)
    | ~ m1_subset_1(X5,X3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X3,X3),X3)))
    | v1_xboole_0(X3)
    | v1_xboole_0(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_273,plain,
    ( ~ v1_funct_2(X0_46,k2_zfmisc_1(X0_45,X0_45),X0_45)
    | ~ v1_funct_2(X1_46,k2_zfmisc_1(X1_45,X1_45),X1_45)
    | r2_binop_1(X0_45,X2_46,X0_46)
    | ~ r2_binop_1(k2_zfmisc_1(X1_45,X0_45),k1_domain_1(X1_45,X0_45,X3_46,X2_46),k6_filter_1(X1_45,X0_45,X1_46,X0_46))
    | ~ m1_subset_1(X2_46,X0_45)
    | ~ m1_subset_1(X3_46,X1_45)
    | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0_45,X0_45),X0_45)))
    | ~ m1_subset_1(X1_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1_45,X1_45),X1_45)))
    | v1_xboole_0(X1_45)
    | v1_xboole_0(X0_45)
    | ~ v1_funct_1(X0_46)
    | ~ v1_funct_1(X1_46) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_545,plain,
    ( ~ v1_funct_2(X0_46,k2_zfmisc_1(X0_45,X0_45),X0_45)
    | ~ v1_funct_2(X1_46,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ r2_binop_1(k2_zfmisc_1(X0_45,sK1),k1_domain_1(X0_45,sK1,X2_46,sK3),k6_filter_1(X0_45,sK1,X0_46,X1_46))
    | r2_binop_1(sK1,sK3,X1_46)
    | ~ m1_subset_1(X2_46,X0_45)
    | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0_45,X0_45),X0_45)))
    | ~ m1_subset_1(X1_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ m1_subset_1(sK3,sK1)
    | v1_xboole_0(X0_45)
    | v1_xboole_0(sK1)
    | ~ v1_funct_1(X1_46)
    | ~ v1_funct_1(X0_46) ),
    inference(instantiation,[status(thm)],[c_273])).

cnf(c_708,plain,
    ( ~ v1_funct_2(X0_46,k2_zfmisc_1(X0_45,X0_45),X0_45)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ r2_binop_1(k2_zfmisc_1(X0_45,sK1),k1_domain_1(X0_45,sK1,X1_46,sK3),k6_filter_1(X0_45,sK1,X0_46,sK5))
    | r2_binop_1(sK1,sK3,sK5)
    | ~ m1_subset_1(X1_46,X0_45)
    | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0_45,X0_45),X0_45)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ m1_subset_1(sK3,sK1)
    | v1_xboole_0(X0_45)
    | v1_xboole_0(sK1)
    | ~ v1_funct_1(X0_46)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_545])).

cnf(c_1331,plain,
    ( ~ v1_funct_2(X0_46,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ r2_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,X0_46,sK5))
    | r2_binop_1(sK1,sK3,sK5)
    | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ m1_subset_1(sK3,sK1)
    | ~ m1_subset_1(sK2,sK0)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ v1_funct_1(X0_46)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_708])).

cnf(c_1332,plain,
    ( v1_funct_2(X0_46,k2_zfmisc_1(sK0,sK0),sK0) != iProver_top
    | v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1) != iProver_top
    | r2_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,X0_46,sK5)) != iProver_top
    | r2_binop_1(sK1,sK3,sK5) = iProver_top
    | m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) != iProver_top
    | m1_subset_1(sK3,sK1) != iProver_top
    | m1_subset_1(sK2,sK0) != iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK0) = iProver_top
    | v1_funct_1(X0_46) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1331])).

cnf(c_1334,plain,
    ( v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1) != iProver_top
    | v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0) != iProver_top
    | r2_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5)) != iProver_top
    | r2_binop_1(sK1,sK3,sK5) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) != iProver_top
    | m1_subset_1(sK3,sK1) != iProver_top
    | m1_subset_1(sK2,sK0) != iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK0) = iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1332])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,X3)
    | m1_subset_1(k1_domain_1(X3,X1,X2,X0),k2_zfmisc_1(X3,X1))
    | v1_xboole_0(X3)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_280,plain,
    ( ~ m1_subset_1(X0_46,X0_45)
    | ~ m1_subset_1(X1_46,X1_45)
    | m1_subset_1(k1_domain_1(X1_45,X0_45,X1_46,X0_46),k2_zfmisc_1(X1_45,X0_45))
    | v1_xboole_0(X1_45)
    | v1_xboole_0(X0_45) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_420,plain,
    ( ~ m1_subset_1(X0_46,X0_45)
    | m1_subset_1(k1_domain_1(X0_45,sK1,X0_46,sK3),k2_zfmisc_1(X0_45,sK1))
    | ~ m1_subset_1(sK3,sK1)
    | v1_xboole_0(X0_45)
    | v1_xboole_0(sK1) ),
    inference(instantiation,[status(thm)],[c_280])).

cnf(c_683,plain,
    ( m1_subset_1(k1_domain_1(sK0,sK1,sK2,sK3),k2_zfmisc_1(sK0,sK1))
    | ~ m1_subset_1(sK3,sK1)
    | ~ m1_subset_1(sK2,sK0)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0) ),
    inference(instantiation,[status(thm)],[c_420])).

cnf(c_684,plain,
    ( m1_subset_1(k1_domain_1(sK0,sK1,sK2,sK3),k2_zfmisc_1(sK0,sK1)) = iProver_top
    | m1_subset_1(sK3,sK1) != iProver_top
    | m1_subset_1(sK2,sK0) != iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_683])).

cnf(c_485,plain,
    ( ~ v1_funct_2(X0_46,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ r1_binop_1(sK0,sK2,X0_46)
    | ~ r2_binop_1(sK0,sK2,X0_46)
    | r3_binop_1(sK0,sK2,X0_46)
    | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ m1_subset_1(sK2,sK0)
    | ~ v1_funct_1(X0_46) ),
    inference(instantiation,[status(thm)],[c_283])).

cnf(c_486,plain,
    ( v1_funct_2(X0_46,k2_zfmisc_1(sK0,sK0),sK0) != iProver_top
    | r1_binop_1(sK0,sK2,X0_46) != iProver_top
    | r2_binop_1(sK0,sK2,X0_46) != iProver_top
    | r3_binop_1(sK0,sK2,X0_46) = iProver_top
    | m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) != iProver_top
    | m1_subset_1(sK2,sK0) != iProver_top
    | v1_funct_1(X0_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_485])).

cnf(c_488,plain,
    ( v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0) != iProver_top
    | r1_binop_1(sK0,sK2,sK4) != iProver_top
    | r2_binop_1(sK0,sK2,sK4) != iProver_top
    | r3_binop_1(sK0,sK2,sK4) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) != iProver_top
    | m1_subset_1(sK2,sK0) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_486])).

cnf(c_465,plain,
    ( ~ v1_funct_2(X0_46,k2_zfmisc_1(sK0,sK0),sK0)
    | r2_binop_1(sK0,sK2,X0_46)
    | ~ r3_binop_1(sK0,sK2,X0_46)
    | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ m1_subset_1(sK2,sK0)
    | ~ v1_funct_1(X0_46) ),
    inference(instantiation,[status(thm)],[c_282])).

cnf(c_466,plain,
    ( v1_funct_2(X0_46,k2_zfmisc_1(sK0,sK0),sK0) != iProver_top
    | r2_binop_1(sK0,sK2,X0_46) = iProver_top
    | r3_binop_1(sK0,sK2,X0_46) != iProver_top
    | m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) != iProver_top
    | m1_subset_1(sK2,sK0) != iProver_top
    | v1_funct_1(X0_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_465])).

cnf(c_468,plain,
    ( v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0) != iProver_top
    | r2_binop_1(sK0,sK2,sK4) = iProver_top
    | r3_binop_1(sK0,sK2,sK4) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) != iProver_top
    | m1_subset_1(sK2,sK0) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_466])).

cnf(c_445,plain,
    ( ~ v1_funct_2(X0_46,k2_zfmisc_1(sK0,sK0),sK0)
    | r1_binop_1(sK0,sK2,X0_46)
    | ~ r3_binop_1(sK0,sK2,X0_46)
    | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ m1_subset_1(sK2,sK0)
    | ~ v1_funct_1(X0_46) ),
    inference(instantiation,[status(thm)],[c_281])).

cnf(c_446,plain,
    ( v1_funct_2(X0_46,k2_zfmisc_1(sK0,sK0),sK0) != iProver_top
    | r1_binop_1(sK0,sK2,X0_46) = iProver_top
    | r3_binop_1(sK0,sK2,X0_46) != iProver_top
    | m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) != iProver_top
    | m1_subset_1(sK2,sK0) != iProver_top
    | v1_funct_1(X0_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_445])).

cnf(c_448,plain,
    ( v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0) != iProver_top
    | r1_binop_1(sK0,sK2,sK4) = iProver_top
    | r3_binop_1(sK0,sK2,sK4) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) != iProver_top
    | m1_subset_1(sK2,sK0) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_446])).

cnf(c_13,negated_conjecture,
    ( ~ r3_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5))
    | ~ r3_binop_1(sK1,sK3,sK5)
    | ~ r3_binop_1(sK0,sK2,sK4) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_38,plain,
    ( r3_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5)) != iProver_top
    | r3_binop_1(sK1,sK3,sK5) != iProver_top
    | r3_binop_1(sK0,sK2,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_14,negated_conjecture,
    ( r3_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5))
    | r3_binop_1(sK1,sK3,sK5) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_37,plain,
    ( r3_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5)) = iProver_top
    | r3_binop_1(sK1,sK3,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_15,negated_conjecture,
    ( r3_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5))
    | r3_binop_1(sK0,sK2,sK4) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_36,plain,
    ( r3_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5)) = iProver_top
    | r3_binop_1(sK0,sK2,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_35,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_17,negated_conjecture,
    ( v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_34,plain,
    ( v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_18,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_33,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_32,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_20,negated_conjecture,
    ( v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_31,plain,
    ( v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_21,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_30,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_29,plain,
    ( m1_subset_1(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_28,plain,
    ( m1_subset_1(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_24,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_27,plain,
    ( v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_25,negated_conjecture,
    ( ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_26,plain,
    ( v1_xboole_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1810,c_1764,c_1742,c_1740,c_1624,c_1616,c_1588,c_1584,c_1580,c_1576,c_1573,c_1545,c_1481,c_1379,c_1334,c_684,c_488,c_468,c_448,c_38,c_37,c_36,c_35,c_34,c_33,c_32,c_31,c_30,c_29,c_28,c_27,c_26])).


%------------------------------------------------------------------------------
