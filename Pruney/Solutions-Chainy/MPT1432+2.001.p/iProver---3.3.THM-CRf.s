%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:18:57 EST 2020

% Result     : Theorem 2.00s
% Output     : CNFRefutation 2.00s
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
            & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
            & v1_funct_1(X2) )
         => ( r3_binop_1(X0,X1,X2)
          <=> ( r2_binop_1(X0,X1,X2)
              & r1_binop_1(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r3_binop_1(X0,X1,X2)
          <=> ( r2_binop_1(X0,X1,X2)
              & r1_binop_1(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
          | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
          | ~ v1_funct_1(X2) )
      | ~ m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r3_binop_1(X0,X1,X2)
          <=> ( r2_binop_1(X0,X1,X2)
              & r1_binop_1(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
          | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
          | ~ v1_funct_1(X2) )
      | ~ m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f10])).

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
    inference(nnf_transformation,[],[f11])).

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

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r2_binop_1(X0,X1,X2)
      | ~ r3_binop_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_binop_1(X0,X1,X2)
      | ~ r3_binop_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f38,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X1)
        & m1_subset_1(X2,X0)
        & ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k1_domain_1(X0,X1,X2,X3),k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k1_domain_1(X0,X1,X2,X3),k2_zfmisc_1(X0,X1))
      | ~ m1_subset_1(X3,X1)
      | ~ m1_subset_1(X2,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f9,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k1_domain_1(X0,X1,X2,X3),k2_zfmisc_1(X0,X1))
      | ~ m1_subset_1(X3,X1)
      | ~ m1_subset_1(X2,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k1_domain_1(X0,X1,X2,X3),k2_zfmisc_1(X0,X1))
      | ~ m1_subset_1(X3,X1)
      | ~ m1_subset_1(X2,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f9])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | v1_xboole_0(X3)
    | v1_xboole_0(X1) ),
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
    | ~ v1_funct_1(X0_46)
    | ~ v1_funct_1(X1_46)
    | v1_xboole_0(X1_45)
    | v1_xboole_0(X0_45) ),
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
    | ~ v1_funct_1(X1_46)
    | ~ v1_funct_1(X0_46)
    | v1_xboole_0(X0_45)
    | v1_xboole_0(sK1) ),
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
    | ~ v1_funct_1(X0_46)
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(X0_45)
    | v1_xboole_0(sK1) ),
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
    | ~ v1_funct_1(X0_46)
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0) ),
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
    | v1_funct_1(X0_46) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
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
    | v1_funct_1(sK5) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
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
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | v1_xboole_0(X3)
    | v1_xboole_0(X1) ),
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
    | ~ v1_funct_1(X0_46)
    | ~ v1_funct_1(X1_46)
    | v1_xboole_0(X1_45)
    | v1_xboole_0(X0_45) ),
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
    | ~ v1_funct_1(X1_46)
    | ~ v1_funct_1(X0_46)
    | v1_xboole_0(X0_45)
    | v1_xboole_0(sK1) ),
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
    | ~ v1_funct_1(X0_46)
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(X0_45)
    | v1_xboole_0(sK1) ),
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
    | ~ v1_funct_1(X0_46)
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0) ),
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
    | v1_funct_1(X0_46) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
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
    | v1_funct_1(sK5) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1762])).

cnf(c_2,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | r2_binop_1(X1,X2,X0)
    | ~ r3_binop_1(X1,X2,X0)
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_281,plain,
    ( ~ v1_funct_2(X0_46,k2_zfmisc_1(X0_45,X0_45),X0_45)
    | r2_binop_1(X0_45,X1_46,X0_46)
    | ~ r3_binop_1(X0_45,X1_46,X0_46)
    | ~ m1_subset_1(X1_46,X0_45)
    | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0_45,X0_45),X0_45)))
    | ~ v1_funct_1(X0_46) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_460,plain,
    ( ~ v1_funct_2(X0_46,k2_zfmisc_1(sK1,sK1),sK1)
    | r2_binop_1(sK1,sK3,X0_46)
    | ~ r3_binop_1(sK1,sK3,X0_46)
    | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ m1_subset_1(sK3,sK1)
    | ~ v1_funct_1(X0_46) ),
    inference(instantiation,[status(thm)],[c_281])).

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

cnf(c_3,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | r1_binop_1(X1,X2,X0)
    | ~ r3_binop_1(X1,X2,X0)
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_280,plain,
    ( ~ v1_funct_2(X0_46,k2_zfmisc_1(X0_45,X0_45),X0_45)
    | r1_binop_1(X0_45,X1_46,X0_46)
    | ~ r3_binop_1(X0_45,X1_46,X0_46)
    | ~ m1_subset_1(X1_46,X0_45)
    | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0_45,X0_45),X0_45)))
    | ~ v1_funct_1(X0_46) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_440,plain,
    ( ~ v1_funct_2(X0_46,k2_zfmisc_1(sK1,sK1),sK1)
    | r1_binop_1(sK1,sK3,X0_46)
    | ~ r3_binop_1(sK1,sK3,X0_46)
    | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ m1_subset_1(sK3,sK1)
    | ~ v1_funct_1(X0_46) ),
    inference(instantiation,[status(thm)],[c_280])).

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

cnf(c_1,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ r1_binop_1(X1,X2,X0)
    | ~ r2_binop_1(X1,X2,X0)
    | r3_binop_1(X1,X2,X0)
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_282,plain,
    ( ~ v1_funct_2(X0_46,k2_zfmisc_1(X0_45,X0_45),X0_45)
    | ~ r1_binop_1(X0_45,X1_46,X0_46)
    | ~ r2_binop_1(X0_45,X1_46,X0_46)
    | r3_binop_1(X0_45,X1_46,X0_46)
    | ~ m1_subset_1(X1_46,X0_45)
    | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0_45,X0_45),X0_45)))
    | ~ v1_funct_1(X0_46) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_480,plain,
    ( ~ v1_funct_2(X0_46,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ r1_binop_1(sK1,sK3,X0_46)
    | ~ r2_binop_1(sK1,sK3,X0_46)
    | r3_binop_1(sK1,sK3,X0_46)
    | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ m1_subset_1(sK3,sK1)
    | ~ v1_funct_1(X0_46) ),
    inference(instantiation,[status(thm)],[c_282])).

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

cnf(c_1055,plain,
    ( ~ v1_funct_2(X0_46,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ r1_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),X0_46)
    | ~ r2_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),X0_46)
    | r3_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),X0_46)
    | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))))
    | ~ m1_subset_1(k1_domain_1(sK0,sK1,sK2,sK3),k2_zfmisc_1(sK0,sK1))
    | ~ v1_funct_1(X0_46) ),
    inference(instantiation,[status(thm)],[c_282])).

cnf(c_1615,plain,
    ( ~ v1_funct_2(k6_filter_1(sK0,sK1,sK4,sK5),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ r1_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5))
    | ~ r2_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5))
    | r3_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5))
    | ~ m1_subset_1(k6_filter_1(sK0,sK1,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))))
    | ~ m1_subset_1(k1_domain_1(sK0,sK1,sK2,sK3),k2_zfmisc_1(sK0,sK1))
    | ~ v1_funct_1(k6_filter_1(sK0,sK1,sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_1055])).

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

cnf(c_1057,plain,
    ( ~ v1_funct_2(X0_46,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | r1_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),X0_46)
    | ~ r3_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),X0_46)
    | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))))
    | ~ m1_subset_1(k1_domain_1(sK0,sK1,sK2,sK3),k2_zfmisc_1(sK0,sK1))
    | ~ v1_funct_1(X0_46) ),
    inference(instantiation,[status(thm)],[c_280])).

cnf(c_1575,plain,
    ( ~ v1_funct_2(k6_filter_1(sK0,sK1,sK4,sK5),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | r1_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5))
    | ~ r3_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5))
    | ~ m1_subset_1(k6_filter_1(sK0,sK1,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))))
    | ~ m1_subset_1(k1_domain_1(sK0,sK1,sK2,sK3),k2_zfmisc_1(sK0,sK1))
    | ~ v1_funct_1(k6_filter_1(sK0,sK1,sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_1057])).

cnf(c_1576,plain,
    ( v1_funct_2(k6_filter_1(sK0,sK1,sK4,sK5),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)) != iProver_top
    | r1_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5)) = iProver_top
    | r3_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5)) != iProver_top
    | m1_subset_1(k6_filter_1(sK0,sK1,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)))) != iProver_top
    | m1_subset_1(k1_domain_1(sK0,sK1,sK2,sK3),k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_funct_1(k6_filter_1(sK0,sK1,sK4,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1575])).

cnf(c_1056,plain,
    ( ~ v1_funct_2(X0_46,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | r2_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),X0_46)
    | ~ r3_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),X0_46)
    | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))))
    | ~ m1_subset_1(k1_domain_1(sK0,sK1,sK2,sK3),k2_zfmisc_1(sK0,sK1))
    | ~ v1_funct_1(X0_46) ),
    inference(instantiation,[status(thm)],[c_281])).

cnf(c_1572,plain,
    ( ~ v1_funct_2(k6_filter_1(sK0,sK1,sK4,sK5),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | r2_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5))
    | ~ r3_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5))
    | ~ m1_subset_1(k6_filter_1(sK0,sK1,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))))
    | ~ m1_subset_1(k1_domain_1(sK0,sK1,sK2,sK3),k2_zfmisc_1(sK0,sK1))
    | ~ v1_funct_1(k6_filter_1(sK0,sK1,sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_1056])).

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
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | v1_xboole_0(X3)
    | v1_xboole_0(X1) ),
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
    | ~ v1_funct_1(X0_46)
    | ~ v1_funct_1(X1_46)
    | v1_xboole_0(X1_45)
    | v1_xboole_0(X0_45) ),
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
    | ~ v1_funct_1(X1_46)
    | ~ v1_funct_1(X0_46)
    | v1_xboole_0(X0_45)
    | v1_xboole_0(sK1) ),
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
    | ~ v1_funct_1(X0_46)
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(X0_45)
    | v1_xboole_0(sK1) ),
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
    | ~ v1_funct_1(X0_46)
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0) ),
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
    | v1_funct_1(X0_46) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
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
    | v1_funct_1(sK5) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
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
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | v1_xboole_0(X3)
    | v1_xboole_0(X1) ),
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
    | ~ v1_funct_1(X0_46)
    | ~ v1_funct_1(X1_46)
    | v1_xboole_0(X1_45)
    | v1_xboole_0(X0_45) ),
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
    | ~ v1_funct_1(X1_46)
    | ~ v1_funct_1(X0_46)
    | v1_xboole_0(X0_45)
    | v1_xboole_0(sK1) ),
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
    | ~ v1_funct_1(X0_46)
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(X0_45)
    | v1_xboole_0(sK1) ),
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
    | ~ v1_funct_1(X0_46)
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0) ),
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
    | v1_funct_1(X0_46) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
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
    | v1_funct_1(sK5) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
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
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | v1_xboole_0(X3)
    | v1_xboole_0(X1) ),
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
    | ~ v1_funct_1(X0_46)
    | ~ v1_funct_1(X1_46)
    | v1_xboole_0(X1_45)
    | v1_xboole_0(X0_45) ),
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
    | ~ v1_funct_1(X1_46)
    | ~ v1_funct_1(X0_46)
    | v1_xboole_0(X0_45)
    | v1_xboole_0(sK1) ),
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
    | ~ v1_funct_1(X0_46)
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(X0_45)
    | v1_xboole_0(sK1) ),
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
    | ~ v1_funct_1(X0_46)
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0) ),
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
    | v1_funct_1(X0_46) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
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
    | v1_funct_1(sK5) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
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
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | v1_xboole_0(X3)
    | v1_xboole_0(X1) ),
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
    | ~ v1_funct_1(X0_46)
    | ~ v1_funct_1(X1_46)
    | v1_xboole_0(X1_45)
    | v1_xboole_0(X0_45) ),
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
    | ~ v1_funct_1(X1_46)
    | ~ v1_funct_1(X0_46)
    | v1_xboole_0(X0_45)
    | v1_xboole_0(sK1) ),
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
    | ~ v1_funct_1(X0_46)
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(X0_45)
    | v1_xboole_0(sK1) ),
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
    | ~ v1_funct_1(X0_46)
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0) ),
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
    | v1_funct_1(X0_46) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
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
    | v1_funct_1(sK5) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1332])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,X3)
    | m1_subset_1(k1_domain_1(X3,X1,X2,X0),k2_zfmisc_1(X3,X1))
    | v1_xboole_0(X3)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_283,plain,
    ( ~ m1_subset_1(X0_46,X0_45)
    | ~ m1_subset_1(X1_46,X1_45)
    | m1_subset_1(k1_domain_1(X1_45,X0_45,X1_46,X0_46),k2_zfmisc_1(X1_45,X0_45))
    | v1_xboole_0(X1_45)
    | v1_xboole_0(X0_45) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_420,plain,
    ( ~ m1_subset_1(X0_46,X0_45)
    | m1_subset_1(k1_domain_1(X0_45,sK1,X0_46,sK3),k2_zfmisc_1(X0_45,sK1))
    | ~ m1_subset_1(sK3,sK1)
    | v1_xboole_0(X0_45)
    | v1_xboole_0(sK1) ),
    inference(instantiation,[status(thm)],[c_283])).

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
    inference(instantiation,[status(thm)],[c_282])).

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
    inference(instantiation,[status(thm)],[c_281])).

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
    inference(instantiation,[status(thm)],[c_280])).

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
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:30:57 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 2.00/0.96  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.00/0.96  
% 2.00/0.96  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.00/0.96  
% 2.00/0.96  ------  iProver source info
% 2.00/0.96  
% 2.00/0.96  git: date: 2020-06-30 10:37:57 +0100
% 2.00/0.96  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.00/0.96  git: non_committed_changes: false
% 2.00/0.96  git: last_make_outside_of_git: false
% 2.00/0.96  
% 2.00/0.96  ------ 
% 2.00/0.96  
% 2.00/0.96  ------ Input Options
% 2.00/0.96  
% 2.00/0.96  --out_options                           all
% 2.00/0.96  --tptp_safe_out                         true
% 2.00/0.96  --problem_path                          ""
% 2.00/0.96  --include_path                          ""
% 2.00/0.96  --clausifier                            res/vclausify_rel
% 2.00/0.96  --clausifier_options                    --mode clausify
% 2.00/0.96  --stdin                                 false
% 2.00/0.96  --stats_out                             all
% 2.00/0.96  
% 2.00/0.96  ------ General Options
% 2.00/0.96  
% 2.00/0.96  --fof                                   false
% 2.00/0.96  --time_out_real                         305.
% 2.00/0.96  --time_out_virtual                      -1.
% 2.00/0.96  --symbol_type_check                     false
% 2.00/0.96  --clausify_out                          false
% 2.00/0.96  --sig_cnt_out                           false
% 2.00/0.96  --trig_cnt_out                          false
% 2.00/0.96  --trig_cnt_out_tolerance                1.
% 2.00/0.96  --trig_cnt_out_sk_spl                   false
% 2.00/0.96  --abstr_cl_out                          false
% 2.00/0.96  
% 2.00/0.96  ------ Global Options
% 2.00/0.96  
% 2.00/0.96  --schedule                              default
% 2.00/0.96  --add_important_lit                     false
% 2.00/0.96  --prop_solver_per_cl                    1000
% 2.00/0.96  --min_unsat_core                        false
% 2.00/0.96  --soft_assumptions                      false
% 2.00/0.96  --soft_lemma_size                       3
% 2.00/0.96  --prop_impl_unit_size                   0
% 2.00/0.96  --prop_impl_unit                        []
% 2.00/0.96  --share_sel_clauses                     true
% 2.00/0.96  --reset_solvers                         false
% 2.00/0.96  --bc_imp_inh                            [conj_cone]
% 2.00/0.96  --conj_cone_tolerance                   3.
% 2.00/0.96  --extra_neg_conj                        none
% 2.00/0.96  --large_theory_mode                     true
% 2.00/0.96  --prolific_symb_bound                   200
% 2.00/0.96  --lt_threshold                          2000
% 2.00/0.96  --clause_weak_htbl                      true
% 2.00/0.96  --gc_record_bc_elim                     false
% 2.00/0.96  
% 2.00/0.96  ------ Preprocessing Options
% 2.00/0.96  
% 2.00/0.96  --preprocessing_flag                    true
% 2.00/0.96  --time_out_prep_mult                    0.1
% 2.00/0.96  --splitting_mode                        input
% 2.00/0.96  --splitting_grd                         true
% 2.00/0.96  --splitting_cvd                         false
% 2.00/0.96  --splitting_cvd_svl                     false
% 2.00/0.96  --splitting_nvd                         32
% 2.00/0.96  --sub_typing                            true
% 2.00/0.96  --prep_gs_sim                           true
% 2.00/0.96  --prep_unflatten                        true
% 2.00/0.96  --prep_res_sim                          true
% 2.00/0.96  --prep_upred                            true
% 2.00/0.96  --prep_sem_filter                       exhaustive
% 2.00/0.96  --prep_sem_filter_out                   false
% 2.00/0.96  --pred_elim                             true
% 2.00/0.96  --res_sim_input                         true
% 2.00/0.96  --eq_ax_congr_red                       true
% 2.00/0.96  --pure_diseq_elim                       true
% 2.00/0.96  --brand_transform                       false
% 2.00/0.96  --non_eq_to_eq                          false
% 2.00/0.96  --prep_def_merge                        true
% 2.00/0.96  --prep_def_merge_prop_impl              false
% 2.00/0.96  --prep_def_merge_mbd                    true
% 2.00/0.96  --prep_def_merge_tr_red                 false
% 2.00/0.96  --prep_def_merge_tr_cl                  false
% 2.00/0.96  --smt_preprocessing                     true
% 2.00/0.96  --smt_ac_axioms                         fast
% 2.00/0.96  --preprocessed_out                      false
% 2.00/0.96  --preprocessed_stats                    false
% 2.00/0.96  
% 2.00/0.96  ------ Abstraction refinement Options
% 2.00/0.96  
% 2.00/0.96  --abstr_ref                             []
% 2.00/0.96  --abstr_ref_prep                        false
% 2.00/0.96  --abstr_ref_until_sat                   false
% 2.00/0.96  --abstr_ref_sig_restrict                funpre
% 2.00/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 2.00/0.96  --abstr_ref_under                       []
% 2.00/0.96  
% 2.00/0.96  ------ SAT Options
% 2.00/0.96  
% 2.00/0.96  --sat_mode                              false
% 2.00/0.96  --sat_fm_restart_options                ""
% 2.00/0.96  --sat_gr_def                            false
% 2.00/0.96  --sat_epr_types                         true
% 2.00/0.96  --sat_non_cyclic_types                  false
% 2.00/0.96  --sat_finite_models                     false
% 2.00/0.96  --sat_fm_lemmas                         false
% 2.00/0.96  --sat_fm_prep                           false
% 2.00/0.96  --sat_fm_uc_incr                        true
% 2.00/0.96  --sat_out_model                         small
% 2.00/0.96  --sat_out_clauses                       false
% 2.00/0.96  
% 2.00/0.96  ------ QBF Options
% 2.00/0.96  
% 2.00/0.96  --qbf_mode                              false
% 2.00/0.96  --qbf_elim_univ                         false
% 2.00/0.96  --qbf_dom_inst                          none
% 2.00/0.96  --qbf_dom_pre_inst                      false
% 2.00/0.96  --qbf_sk_in                             false
% 2.00/0.96  --qbf_pred_elim                         true
% 2.00/0.96  --qbf_split                             512
% 2.00/0.96  
% 2.00/0.96  ------ BMC1 Options
% 2.00/0.96  
% 2.00/0.96  --bmc1_incremental                      false
% 2.00/0.96  --bmc1_axioms                           reachable_all
% 2.00/0.96  --bmc1_min_bound                        0
% 2.00/0.96  --bmc1_max_bound                        -1
% 2.00/0.96  --bmc1_max_bound_default                -1
% 2.00/0.96  --bmc1_symbol_reachability              true
% 2.00/0.96  --bmc1_property_lemmas                  false
% 2.00/0.96  --bmc1_k_induction                      false
% 2.00/0.96  --bmc1_non_equiv_states                 false
% 2.00/0.96  --bmc1_deadlock                         false
% 2.00/0.96  --bmc1_ucm                              false
% 2.00/0.96  --bmc1_add_unsat_core                   none
% 2.00/0.96  --bmc1_unsat_core_children              false
% 2.00/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 2.00/0.96  --bmc1_out_stat                         full
% 2.00/0.96  --bmc1_ground_init                      false
% 2.00/0.96  --bmc1_pre_inst_next_state              false
% 2.00/0.96  --bmc1_pre_inst_state                   false
% 2.00/0.96  --bmc1_pre_inst_reach_state             false
% 2.00/0.96  --bmc1_out_unsat_core                   false
% 2.00/0.96  --bmc1_aig_witness_out                  false
% 2.00/0.96  --bmc1_verbose                          false
% 2.00/0.96  --bmc1_dump_clauses_tptp                false
% 2.00/0.96  --bmc1_dump_unsat_core_tptp             false
% 2.00/0.96  --bmc1_dump_file                        -
% 2.00/0.96  --bmc1_ucm_expand_uc_limit              128
% 2.00/0.96  --bmc1_ucm_n_expand_iterations          6
% 2.00/0.96  --bmc1_ucm_extend_mode                  1
% 2.00/0.96  --bmc1_ucm_init_mode                    2
% 2.00/0.96  --bmc1_ucm_cone_mode                    none
% 2.00/0.96  --bmc1_ucm_reduced_relation_type        0
% 2.00/0.96  --bmc1_ucm_relax_model                  4
% 2.00/0.96  --bmc1_ucm_full_tr_after_sat            true
% 2.00/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 2.00/0.96  --bmc1_ucm_layered_model                none
% 2.00/0.96  --bmc1_ucm_max_lemma_size               10
% 2.00/0.96  
% 2.00/0.96  ------ AIG Options
% 2.00/0.96  
% 2.00/0.96  --aig_mode                              false
% 2.00/0.96  
% 2.00/0.96  ------ Instantiation Options
% 2.00/0.96  
% 2.00/0.96  --instantiation_flag                    true
% 2.00/0.96  --inst_sos_flag                         false
% 2.00/0.96  --inst_sos_phase                        true
% 2.00/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.00/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.00/0.96  --inst_lit_sel_side                     num_symb
% 2.00/0.96  --inst_solver_per_active                1400
% 2.00/0.96  --inst_solver_calls_frac                1.
% 2.00/0.96  --inst_passive_queue_type               priority_queues
% 2.00/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.00/0.96  --inst_passive_queues_freq              [25;2]
% 2.00/0.96  --inst_dismatching                      true
% 2.00/0.96  --inst_eager_unprocessed_to_passive     true
% 2.00/0.96  --inst_prop_sim_given                   true
% 2.00/0.96  --inst_prop_sim_new                     false
% 2.00/0.96  --inst_subs_new                         false
% 2.00/0.96  --inst_eq_res_simp                      false
% 2.00/0.96  --inst_subs_given                       false
% 2.00/0.96  --inst_orphan_elimination               true
% 2.00/0.96  --inst_learning_loop_flag               true
% 2.00/0.96  --inst_learning_start                   3000
% 2.00/0.96  --inst_learning_factor                  2
% 2.00/0.96  --inst_start_prop_sim_after_learn       3
% 2.00/0.96  --inst_sel_renew                        solver
% 2.00/0.96  --inst_lit_activity_flag                true
% 2.00/0.96  --inst_restr_to_given                   false
% 2.00/0.96  --inst_activity_threshold               500
% 2.00/0.96  --inst_out_proof                        true
% 2.00/0.96  
% 2.00/0.96  ------ Resolution Options
% 2.00/0.96  
% 2.00/0.96  --resolution_flag                       true
% 2.00/0.96  --res_lit_sel                           adaptive
% 2.00/0.96  --res_lit_sel_side                      none
% 2.00/0.96  --res_ordering                          kbo
% 2.00/0.96  --res_to_prop_solver                    active
% 2.00/0.96  --res_prop_simpl_new                    false
% 2.00/0.96  --res_prop_simpl_given                  true
% 2.00/0.96  --res_passive_queue_type                priority_queues
% 2.00/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.00/0.96  --res_passive_queues_freq               [15;5]
% 2.00/0.96  --res_forward_subs                      full
% 2.00/0.96  --res_backward_subs                     full
% 2.00/0.96  --res_forward_subs_resolution           true
% 2.00/0.96  --res_backward_subs_resolution          true
% 2.00/0.96  --res_orphan_elimination                true
% 2.00/0.96  --res_time_limit                        2.
% 2.00/0.96  --res_out_proof                         true
% 2.00/0.96  
% 2.00/0.96  ------ Superposition Options
% 2.00/0.96  
% 2.00/0.96  --superposition_flag                    true
% 2.00/0.96  --sup_passive_queue_type                priority_queues
% 2.00/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.00/0.96  --sup_passive_queues_freq               [8;1;4]
% 2.00/0.96  --demod_completeness_check              fast
% 2.00/0.96  --demod_use_ground                      true
% 2.00/0.96  --sup_to_prop_solver                    passive
% 2.00/0.96  --sup_prop_simpl_new                    true
% 2.00/0.96  --sup_prop_simpl_given                  true
% 2.00/0.96  --sup_fun_splitting                     false
% 2.00/0.96  --sup_smt_interval                      50000
% 2.00/0.96  
% 2.00/0.96  ------ Superposition Simplification Setup
% 2.00/0.96  
% 2.00/0.96  --sup_indices_passive                   []
% 2.00/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.00/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.00/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.00/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 2.00/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.00/0.96  --sup_full_bw                           [BwDemod]
% 2.00/0.96  --sup_immed_triv                        [TrivRules]
% 2.00/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.00/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.00/0.96  --sup_immed_bw_main                     []
% 2.00/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.00/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 2.00/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.00/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.00/0.96  
% 2.00/0.96  ------ Combination Options
% 2.00/0.96  
% 2.00/0.96  --comb_res_mult                         3
% 2.00/0.96  --comb_sup_mult                         2
% 2.00/0.96  --comb_inst_mult                        10
% 2.00/0.96  
% 2.00/0.96  ------ Debug Options
% 2.00/0.96  
% 2.00/0.96  --dbg_backtrace                         false
% 2.00/0.96  --dbg_dump_prop_clauses                 false
% 2.00/0.96  --dbg_dump_prop_clauses_file            -
% 2.00/0.96  --dbg_out_stat                          false
% 2.00/0.96  ------ Parsing...
% 2.00/0.96  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.00/0.96  
% 2.00/0.96  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 2.00/0.96  
% 2.00/0.96  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.00/0.96  ------ Proving...
% 2.00/0.96  ------ Problem Properties 
% 2.00/0.96  
% 2.00/0.96  
% 2.00/0.96  clauses                                 26
% 2.00/0.96  conjectures                             13
% 2.00/0.96  EPR                                     6
% 2.00/0.96  Horn                                    17
% 2.00/0.96  unary                                   10
% 2.00/0.96  binary                                  2
% 2.00/0.96  lits                                    136
% 2.00/0.96  lits eq                                 0
% 2.00/0.96  fd_pure                                 0
% 2.00/0.96  fd_pseudo                               0
% 2.00/0.96  fd_cond                                 0
% 2.00/0.96  fd_pseudo_cond                          0
% 2.00/0.96  AC symbols                              0
% 2.00/0.96  
% 2.00/0.96  ------ Schedule dynamic 5 is on 
% 2.00/0.96  
% 2.00/0.96  ------ no equalities: superposition off 
% 2.00/0.96  
% 2.00/0.96  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.00/0.96  
% 2.00/0.96  
% 2.00/0.96  ------ 
% 2.00/0.96  Current options:
% 2.00/0.96  ------ 
% 2.00/0.96  
% 2.00/0.96  ------ Input Options
% 2.00/0.96  
% 2.00/0.96  --out_options                           all
% 2.00/0.96  --tptp_safe_out                         true
% 2.00/0.96  --problem_path                          ""
% 2.00/0.96  --include_path                          ""
% 2.00/0.96  --clausifier                            res/vclausify_rel
% 2.00/0.96  --clausifier_options                    --mode clausify
% 2.00/0.96  --stdin                                 false
% 2.00/0.96  --stats_out                             all
% 2.00/0.96  
% 2.00/0.96  ------ General Options
% 2.00/0.96  
% 2.00/0.96  --fof                                   false
% 2.00/0.96  --time_out_real                         305.
% 2.00/0.96  --time_out_virtual                      -1.
% 2.00/0.96  --symbol_type_check                     false
% 2.00/0.96  --clausify_out                          false
% 2.00/0.96  --sig_cnt_out                           false
% 2.00/0.96  --trig_cnt_out                          false
% 2.00/0.96  --trig_cnt_out_tolerance                1.
% 2.00/0.96  --trig_cnt_out_sk_spl                   false
% 2.00/0.96  --abstr_cl_out                          false
% 2.00/0.96  
% 2.00/0.96  ------ Global Options
% 2.00/0.96  
% 2.00/0.96  --schedule                              default
% 2.00/0.96  --add_important_lit                     false
% 2.00/0.96  --prop_solver_per_cl                    1000
% 2.00/0.96  --min_unsat_core                        false
% 2.00/0.96  --soft_assumptions                      false
% 2.00/0.96  --soft_lemma_size                       3
% 2.00/0.96  --prop_impl_unit_size                   0
% 2.00/0.96  --prop_impl_unit                        []
% 2.00/0.96  --share_sel_clauses                     true
% 2.00/0.96  --reset_solvers                         false
% 2.00/0.96  --bc_imp_inh                            [conj_cone]
% 2.00/0.96  --conj_cone_tolerance                   3.
% 2.00/0.96  --extra_neg_conj                        none
% 2.00/0.96  --large_theory_mode                     true
% 2.00/0.96  --prolific_symb_bound                   200
% 2.00/0.96  --lt_threshold                          2000
% 2.00/0.96  --clause_weak_htbl                      true
% 2.00/0.96  --gc_record_bc_elim                     false
% 2.00/0.96  
% 2.00/0.96  ------ Preprocessing Options
% 2.00/0.96  
% 2.00/0.96  --preprocessing_flag                    true
% 2.00/0.96  --time_out_prep_mult                    0.1
% 2.00/0.96  --splitting_mode                        input
% 2.00/0.96  --splitting_grd                         true
% 2.00/0.96  --splitting_cvd                         false
% 2.00/0.96  --splitting_cvd_svl                     false
% 2.00/0.96  --splitting_nvd                         32
% 2.00/0.96  --sub_typing                            true
% 2.00/0.96  --prep_gs_sim                           true
% 2.00/0.96  --prep_unflatten                        true
% 2.00/0.96  --prep_res_sim                          true
% 2.00/0.96  --prep_upred                            true
% 2.00/0.96  --prep_sem_filter                       exhaustive
% 2.00/0.96  --prep_sem_filter_out                   false
% 2.00/0.96  --pred_elim                             true
% 2.00/0.96  --res_sim_input                         true
% 2.00/0.96  --eq_ax_congr_red                       true
% 2.00/0.96  --pure_diseq_elim                       true
% 2.00/0.96  --brand_transform                       false
% 2.00/0.96  --non_eq_to_eq                          false
% 2.00/0.96  --prep_def_merge                        true
% 2.00/0.96  --prep_def_merge_prop_impl              false
% 2.00/0.96  --prep_def_merge_mbd                    true
% 2.00/0.96  --prep_def_merge_tr_red                 false
% 2.00/0.96  --prep_def_merge_tr_cl                  false
% 2.00/0.96  --smt_preprocessing                     true
% 2.00/0.96  --smt_ac_axioms                         fast
% 2.00/0.96  --preprocessed_out                      false
% 2.00/0.96  --preprocessed_stats                    false
% 2.00/0.96  
% 2.00/0.96  ------ Abstraction refinement Options
% 2.00/0.96  
% 2.00/0.96  --abstr_ref                             []
% 2.00/0.96  --abstr_ref_prep                        false
% 2.00/0.96  --abstr_ref_until_sat                   false
% 2.00/0.96  --abstr_ref_sig_restrict                funpre
% 2.00/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 2.00/0.96  --abstr_ref_under                       []
% 2.00/0.96  
% 2.00/0.96  ------ SAT Options
% 2.00/0.96  
% 2.00/0.96  --sat_mode                              false
% 2.00/0.96  --sat_fm_restart_options                ""
% 2.00/0.96  --sat_gr_def                            false
% 2.00/0.96  --sat_epr_types                         true
% 2.00/0.96  --sat_non_cyclic_types                  false
% 2.00/0.96  --sat_finite_models                     false
% 2.00/0.96  --sat_fm_lemmas                         false
% 2.00/0.96  --sat_fm_prep                           false
% 2.00/0.96  --sat_fm_uc_incr                        true
% 2.00/0.96  --sat_out_model                         small
% 2.00/0.96  --sat_out_clauses                       false
% 2.00/0.96  
% 2.00/0.96  ------ QBF Options
% 2.00/0.96  
% 2.00/0.96  --qbf_mode                              false
% 2.00/0.96  --qbf_elim_univ                         false
% 2.00/0.96  --qbf_dom_inst                          none
% 2.00/0.96  --qbf_dom_pre_inst                      false
% 2.00/0.96  --qbf_sk_in                             false
% 2.00/0.96  --qbf_pred_elim                         true
% 2.00/0.96  --qbf_split                             512
% 2.00/0.96  
% 2.00/0.96  ------ BMC1 Options
% 2.00/0.96  
% 2.00/0.96  --bmc1_incremental                      false
% 2.00/0.96  --bmc1_axioms                           reachable_all
% 2.00/0.96  --bmc1_min_bound                        0
% 2.00/0.96  --bmc1_max_bound                        -1
% 2.00/0.96  --bmc1_max_bound_default                -1
% 2.00/0.96  --bmc1_symbol_reachability              true
% 2.00/0.96  --bmc1_property_lemmas                  false
% 2.00/0.96  --bmc1_k_induction                      false
% 2.00/0.96  --bmc1_non_equiv_states                 false
% 2.00/0.96  --bmc1_deadlock                         false
% 2.00/0.96  --bmc1_ucm                              false
% 2.00/0.96  --bmc1_add_unsat_core                   none
% 2.00/0.96  --bmc1_unsat_core_children              false
% 2.00/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 2.00/0.96  --bmc1_out_stat                         full
% 2.00/0.96  --bmc1_ground_init                      false
% 2.00/0.96  --bmc1_pre_inst_next_state              false
% 2.00/0.96  --bmc1_pre_inst_state                   false
% 2.00/0.96  --bmc1_pre_inst_reach_state             false
% 2.00/0.96  --bmc1_out_unsat_core                   false
% 2.00/0.96  --bmc1_aig_witness_out                  false
% 2.00/0.96  --bmc1_verbose                          false
% 2.00/0.96  --bmc1_dump_clauses_tptp                false
% 2.00/0.96  --bmc1_dump_unsat_core_tptp             false
% 2.00/0.96  --bmc1_dump_file                        -
% 2.00/0.96  --bmc1_ucm_expand_uc_limit              128
% 2.00/0.96  --bmc1_ucm_n_expand_iterations          6
% 2.00/0.96  --bmc1_ucm_extend_mode                  1
% 2.00/0.96  --bmc1_ucm_init_mode                    2
% 2.00/0.96  --bmc1_ucm_cone_mode                    none
% 2.00/0.96  --bmc1_ucm_reduced_relation_type        0
% 2.00/0.96  --bmc1_ucm_relax_model                  4
% 2.00/0.96  --bmc1_ucm_full_tr_after_sat            true
% 2.00/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 2.00/0.96  --bmc1_ucm_layered_model                none
% 2.00/0.96  --bmc1_ucm_max_lemma_size               10
% 2.00/0.96  
% 2.00/0.96  ------ AIG Options
% 2.00/0.96  
% 2.00/0.96  --aig_mode                              false
% 2.00/0.96  
% 2.00/0.96  ------ Instantiation Options
% 2.00/0.96  
% 2.00/0.96  --instantiation_flag                    true
% 2.00/0.96  --inst_sos_flag                         false
% 2.00/0.96  --inst_sos_phase                        true
% 2.00/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.00/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.00/0.96  --inst_lit_sel_side                     none
% 2.00/0.96  --inst_solver_per_active                1400
% 2.00/0.96  --inst_solver_calls_frac                1.
% 2.00/0.96  --inst_passive_queue_type               priority_queues
% 2.00/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.00/0.96  --inst_passive_queues_freq              [25;2]
% 2.00/0.96  --inst_dismatching                      true
% 2.00/0.96  --inst_eager_unprocessed_to_passive     true
% 2.00/0.96  --inst_prop_sim_given                   true
% 2.00/0.96  --inst_prop_sim_new                     false
% 2.00/0.96  --inst_subs_new                         false
% 2.00/0.96  --inst_eq_res_simp                      false
% 2.00/0.96  --inst_subs_given                       false
% 2.00/0.96  --inst_orphan_elimination               true
% 2.00/0.96  --inst_learning_loop_flag               true
% 2.00/0.96  --inst_learning_start                   3000
% 2.00/0.96  --inst_learning_factor                  2
% 2.00/0.96  --inst_start_prop_sim_after_learn       3
% 2.00/0.96  --inst_sel_renew                        solver
% 2.00/0.96  --inst_lit_activity_flag                true
% 2.00/0.96  --inst_restr_to_given                   false
% 2.00/0.96  --inst_activity_threshold               500
% 2.00/0.96  --inst_out_proof                        true
% 2.00/0.96  
% 2.00/0.96  ------ Resolution Options
% 2.00/0.96  
% 2.00/0.96  --resolution_flag                       false
% 2.00/0.96  --res_lit_sel                           adaptive
% 2.00/0.96  --res_lit_sel_side                      none
% 2.00/0.96  --res_ordering                          kbo
% 2.00/0.96  --res_to_prop_solver                    active
% 2.00/0.96  --res_prop_simpl_new                    false
% 2.00/0.96  --res_prop_simpl_given                  true
% 2.00/0.96  --res_passive_queue_type                priority_queues
% 2.00/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.00/0.96  --res_passive_queues_freq               [15;5]
% 2.00/0.96  --res_forward_subs                      full
% 2.00/0.96  --res_backward_subs                     full
% 2.00/0.96  --res_forward_subs_resolution           true
% 2.00/0.96  --res_backward_subs_resolution          true
% 2.00/0.96  --res_orphan_elimination                true
% 2.00/0.96  --res_time_limit                        2.
% 2.00/0.96  --res_out_proof                         true
% 2.00/0.96  
% 2.00/0.96  ------ Superposition Options
% 2.00/0.96  
% 2.00/0.96  --superposition_flag                    false
% 2.00/0.96  --sup_passive_queue_type                priority_queues
% 2.00/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.00/0.96  --sup_passive_queues_freq               [8;1;4]
% 2.00/0.96  --demod_completeness_check              fast
% 2.00/0.96  --demod_use_ground                      true
% 2.00/0.96  --sup_to_prop_solver                    passive
% 2.00/0.96  --sup_prop_simpl_new                    true
% 2.00/0.96  --sup_prop_simpl_given                  true
% 2.00/0.96  --sup_fun_splitting                     false
% 2.00/0.96  --sup_smt_interval                      50000
% 2.00/0.96  
% 2.00/0.96  ------ Superposition Simplification Setup
% 2.00/0.96  
% 2.00/0.96  --sup_indices_passive                   []
% 2.00/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.00/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.00/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.00/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 2.00/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.00/0.96  --sup_full_bw                           [BwDemod]
% 2.00/0.96  --sup_immed_triv                        [TrivRules]
% 2.00/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.00/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.00/0.96  --sup_immed_bw_main                     []
% 2.00/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.00/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 2.00/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.00/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.00/0.96  
% 2.00/0.96  ------ Combination Options
% 2.00/0.96  
% 2.00/0.96  --comb_res_mult                         3
% 2.00/0.96  --comb_sup_mult                         2
% 2.00/0.96  --comb_inst_mult                        10
% 2.00/0.96  
% 2.00/0.96  ------ Debug Options
% 2.00/0.96  
% 2.00/0.96  --dbg_backtrace                         false
% 2.00/0.96  --dbg_dump_prop_clauses                 false
% 2.00/0.96  --dbg_dump_prop_clauses_file            -
% 2.00/0.96  --dbg_out_stat                          false
% 2.00/0.96  
% 2.00/0.96  
% 2.00/0.96  
% 2.00/0.96  
% 2.00/0.96  ------ Proving...
% 2.00/0.96  
% 2.00/0.96  
% 2.00/0.96  % SZS status Theorem for theBenchmark.p
% 2.00/0.96  
% 2.00/0.96  % SZS output start CNFRefutation for theBenchmark.p
% 2.00/0.96  
% 2.00/0.96  fof(f4,axiom,(
% 2.00/0.96    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : (m1_subset_1(X3,X1) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) & v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1) & v1_funct_1(X5)) => ((r1_binop_1(X1,X3,X5) & r1_binop_1(X0,X2,X4)) <=> r1_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5)))))))))),
% 2.00/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.00/0.96  
% 2.00/0.96  fof(f14,plain,(
% 2.00/0.96    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (((r1_binop_1(X1,X3,X5) & r1_binop_1(X0,X2,X4)) <=> r1_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) | ~v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X4))) | ~m1_subset_1(X3,X1)) | ~m1_subset_1(X2,X0)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.00/0.96    inference(ennf_transformation,[],[f4])).
% 2.00/0.96  
% 2.00/0.96  fof(f15,plain,(
% 2.00/0.96    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (((r1_binop_1(X1,X3,X5) & r1_binop_1(X0,X2,X4)) <=> r1_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) | ~v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,X1)) | ~m1_subset_1(X2,X0)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.00/0.96    inference(flattening,[],[f14])).
% 2.00/0.96  
% 2.00/0.96  fof(f22,plain,(
% 2.00/0.96    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((((r1_binop_1(X1,X3,X5) & r1_binop_1(X0,X2,X4)) | ~r1_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5))) & (r1_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5)) | (~r1_binop_1(X1,X3,X5) | ~r1_binop_1(X0,X2,X4)))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) | ~v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,X1)) | ~m1_subset_1(X2,X0)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.00/0.96    inference(nnf_transformation,[],[f15])).
% 2.00/0.96  
% 2.00/0.96  fof(f23,plain,(
% 2.00/0.96    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((((r1_binop_1(X1,X3,X5) & r1_binop_1(X0,X2,X4)) | ~r1_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5))) & (r1_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5)) | ~r1_binop_1(X1,X3,X5) | ~r1_binop_1(X0,X2,X4))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) | ~v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,X1)) | ~m1_subset_1(X2,X0)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.00/0.96    inference(flattening,[],[f22])).
% 2.00/0.96  
% 2.00/0.96  fof(f42,plain,(
% 2.00/0.96    ( ! [X4,X2,X0,X5,X3,X1] : (r1_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5)) | ~r1_binop_1(X1,X3,X5) | ~r1_binop_1(X0,X2,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) | ~v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X4) | ~m1_subset_1(X3,X1) | ~m1_subset_1(X2,X0) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.00/0.96    inference(cnf_transformation,[],[f23])).
% 2.00/0.96  
% 2.00/0.96  fof(f5,axiom,(
% 2.00/0.96    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : (m1_subset_1(X3,X1) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) & v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1) & v1_funct_1(X5)) => ((r2_binop_1(X1,X3,X5) & r2_binop_1(X0,X2,X4)) <=> r2_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5)))))))))),
% 2.00/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.00/0.96  
% 2.00/0.96  fof(f16,plain,(
% 2.00/0.96    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (((r2_binop_1(X1,X3,X5) & r2_binop_1(X0,X2,X4)) <=> r2_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) | ~v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X4))) | ~m1_subset_1(X3,X1)) | ~m1_subset_1(X2,X0)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.00/0.96    inference(ennf_transformation,[],[f5])).
% 2.00/0.96  
% 2.00/0.96  fof(f17,plain,(
% 2.00/0.96    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (((r2_binop_1(X1,X3,X5) & r2_binop_1(X0,X2,X4)) <=> r2_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) | ~v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,X1)) | ~m1_subset_1(X2,X0)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.00/0.96    inference(flattening,[],[f16])).
% 2.00/0.96  
% 2.00/0.96  fof(f24,plain,(
% 2.00/0.96    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((((r2_binop_1(X1,X3,X5) & r2_binop_1(X0,X2,X4)) | ~r2_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5))) & (r2_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5)) | (~r2_binop_1(X1,X3,X5) | ~r2_binop_1(X0,X2,X4)))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) | ~v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,X1)) | ~m1_subset_1(X2,X0)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.00/0.96    inference(nnf_transformation,[],[f17])).
% 2.00/0.96  
% 2.00/0.96  fof(f25,plain,(
% 2.00/0.96    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((((r2_binop_1(X1,X3,X5) & r2_binop_1(X0,X2,X4)) | ~r2_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5))) & (r2_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5)) | ~r2_binop_1(X1,X3,X5) | ~r2_binop_1(X0,X2,X4))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) | ~v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,X1)) | ~m1_subset_1(X2,X0)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.00/0.96    inference(flattening,[],[f24])).
% 2.00/0.96  
% 2.00/0.96  fof(f45,plain,(
% 2.00/0.96    ( ! [X4,X2,X0,X5,X3,X1] : (r2_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5)) | ~r2_binop_1(X1,X3,X5) | ~r2_binop_1(X0,X2,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) | ~v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X4) | ~m1_subset_1(X3,X1) | ~m1_subset_1(X2,X0) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.00/0.96    inference(cnf_transformation,[],[f25])).
% 2.00/0.96  
% 2.00/0.96  fof(f2,axiom,(
% 2.00/0.96    ! [X0,X1] : (m1_subset_1(X1,X0) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) & v1_funct_1(X2)) => (r3_binop_1(X0,X1,X2) <=> (r2_binop_1(X0,X1,X2) & r1_binop_1(X0,X1,X2)))))),
% 2.00/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.00/0.96  
% 2.00/0.96  fof(f10,plain,(
% 2.00/0.96    ! [X0,X1] : (! [X2] : ((r3_binop_1(X0,X1,X2) <=> (r2_binop_1(X0,X1,X2) & r1_binop_1(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X1,X0))),
% 2.00/0.96    inference(ennf_transformation,[],[f2])).
% 2.00/0.96  
% 2.00/0.96  fof(f11,plain,(
% 2.00/0.96    ! [X0,X1] : (! [X2] : ((r3_binop_1(X0,X1,X2) <=> (r2_binop_1(X0,X1,X2) & r1_binop_1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2)) | ~m1_subset_1(X1,X0))),
% 2.00/0.96    inference(flattening,[],[f10])).
% 2.00/0.96  
% 2.00/0.96  fof(f20,plain,(
% 2.00/0.96    ! [X0,X1] : (! [X2] : (((r3_binop_1(X0,X1,X2) | (~r2_binop_1(X0,X1,X2) | ~r1_binop_1(X0,X1,X2))) & ((r2_binop_1(X0,X1,X2) & r1_binop_1(X0,X1,X2)) | ~r3_binop_1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2)) | ~m1_subset_1(X1,X0))),
% 2.00/0.96    inference(nnf_transformation,[],[f11])).
% 2.00/0.96  
% 2.00/0.96  fof(f21,plain,(
% 2.00/0.96    ! [X0,X1] : (! [X2] : (((r3_binop_1(X0,X1,X2) | ~r2_binop_1(X0,X1,X2) | ~r1_binop_1(X0,X1,X2)) & ((r2_binop_1(X0,X1,X2) & r1_binop_1(X0,X1,X2)) | ~r3_binop_1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2)) | ~m1_subset_1(X1,X0))),
% 2.00/0.96    inference(flattening,[],[f20])).
% 2.00/0.96  
% 2.00/0.96  fof(f37,plain,(
% 2.00/0.96    ( ! [X2,X0,X1] : (r2_binop_1(X0,X1,X2) | ~r3_binop_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2) | ~m1_subset_1(X1,X0)) )),
% 2.00/0.97    inference(cnf_transformation,[],[f21])).
% 2.00/0.97  
% 2.00/0.97  fof(f36,plain,(
% 2.00/0.97    ( ! [X2,X0,X1] : (r1_binop_1(X0,X1,X2) | ~r3_binop_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2) | ~m1_subset_1(X1,X0)) )),
% 2.00/0.97    inference(cnf_transformation,[],[f21])).
% 2.00/0.97  
% 2.00/0.97  fof(f38,plain,(
% 2.00/0.97    ( ! [X2,X0,X1] : (r3_binop_1(X0,X1,X2) | ~r2_binop_1(X0,X1,X2) | ~r1_binop_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2) | ~m1_subset_1(X1,X0)) )),
% 2.00/0.97    inference(cnf_transformation,[],[f21])).
% 2.00/0.97  
% 2.00/0.97  fof(f3,axiom,(
% 2.00/0.97    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) & v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) & v1_funct_1(X2)) => (m1_subset_1(k6_filter_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)),k2_zfmisc_1(X0,X1)))) & v1_funct_2(k6_filter_1(X0,X1,X2,X3),k2_zfmisc_1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)),k2_zfmisc_1(X0,X1)) & v1_funct_1(k6_filter_1(X0,X1,X2,X3))))),
% 2.00/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.00/0.97  
% 2.00/0.97  fof(f12,plain,(
% 2.00/0.97    ! [X0,X1,X2,X3] : ((m1_subset_1(k6_filter_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)),k2_zfmisc_1(X0,X1)))) & v1_funct_2(k6_filter_1(X0,X1,X2,X3),k2_zfmisc_1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)),k2_zfmisc_1(X0,X1)) & v1_funct_1(k6_filter_1(X0,X1,X2,X3))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) | ~v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2)))),
% 2.00/0.97    inference(ennf_transformation,[],[f3])).
% 2.00/0.97  
% 2.00/0.97  fof(f13,plain,(
% 2.00/0.97    ! [X0,X1,X2,X3] : ((m1_subset_1(k6_filter_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)),k2_zfmisc_1(X0,X1)))) & v1_funct_2(k6_filter_1(X0,X1,X2,X3),k2_zfmisc_1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)),k2_zfmisc_1(X0,X1)) & v1_funct_1(k6_filter_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) | ~v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2))),
% 2.00/0.97    inference(flattening,[],[f12])).
% 2.00/0.97  
% 2.00/0.97  fof(f41,plain,(
% 2.00/0.97    ( ! [X2,X0,X3,X1] : (m1_subset_1(k6_filter_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)),k2_zfmisc_1(X0,X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) | ~v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2)) )),
% 2.00/0.97    inference(cnf_transformation,[],[f13])).
% 2.00/0.97  
% 2.00/0.97  fof(f40,plain,(
% 2.00/0.97    ( ! [X2,X0,X3,X1] : (v1_funct_2(k6_filter_1(X0,X1,X2,X3),k2_zfmisc_1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)),k2_zfmisc_1(X0,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) | ~v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2)) )),
% 2.00/0.97    inference(cnf_transformation,[],[f13])).
% 2.00/0.97  
% 2.00/0.97  fof(f39,plain,(
% 2.00/0.97    ( ! [X2,X0,X3,X1] : (v1_funct_1(k6_filter_1(X0,X1,X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) | ~v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2)) )),
% 2.00/0.97    inference(cnf_transformation,[],[f13])).
% 2.00/0.97  
% 2.00/0.97  fof(f44,plain,(
% 2.00/0.97    ( ! [X4,X2,X0,X5,X3,X1] : (r1_binop_1(X1,X3,X5) | ~r1_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) | ~v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X4) | ~m1_subset_1(X3,X1) | ~m1_subset_1(X2,X0) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.00/0.97    inference(cnf_transformation,[],[f23])).
% 2.00/0.97  
% 2.00/0.97  fof(f43,plain,(
% 2.00/0.97    ( ! [X4,X2,X0,X5,X3,X1] : (r1_binop_1(X0,X2,X4) | ~r1_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) | ~v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X4) | ~m1_subset_1(X3,X1) | ~m1_subset_1(X2,X0) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.00/0.97    inference(cnf_transformation,[],[f23])).
% 2.00/0.97  
% 2.00/0.97  fof(f46,plain,(
% 2.00/0.97    ( ! [X4,X2,X0,X5,X3,X1] : (r2_binop_1(X0,X2,X4) | ~r2_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) | ~v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X4) | ~m1_subset_1(X3,X1) | ~m1_subset_1(X2,X0) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.00/0.97    inference(cnf_transformation,[],[f25])).
% 2.00/0.97  
% 2.00/0.97  fof(f47,plain,(
% 2.00/0.97    ( ! [X4,X2,X0,X5,X3,X1] : (r2_binop_1(X1,X3,X5) | ~r2_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) | ~v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X4) | ~m1_subset_1(X3,X1) | ~m1_subset_1(X2,X0) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.00/0.97    inference(cnf_transformation,[],[f25])).
% 2.00/0.97  
% 2.00/0.97  fof(f1,axiom,(
% 2.00/0.97    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X1) & m1_subset_1(X2,X0) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => m1_subset_1(k1_domain_1(X0,X1,X2,X3),k2_zfmisc_1(X0,X1)))),
% 2.00/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.00/0.97  
% 2.00/0.97  fof(f8,plain,(
% 2.00/0.97    ! [X0,X1,X2,X3] : (m1_subset_1(k1_domain_1(X0,X1,X2,X3),k2_zfmisc_1(X0,X1)) | (~m1_subset_1(X3,X1) | ~m1_subset_1(X2,X0) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 2.00/0.97    inference(ennf_transformation,[],[f1])).
% 2.00/0.97  
% 2.00/0.97  fof(f9,plain,(
% 2.00/0.97    ! [X0,X1,X2,X3] : (m1_subset_1(k1_domain_1(X0,X1,X2,X3),k2_zfmisc_1(X0,X1)) | ~m1_subset_1(X3,X1) | ~m1_subset_1(X2,X0) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 2.00/0.97    inference(flattening,[],[f8])).
% 2.00/0.97  
% 2.00/0.97  fof(f35,plain,(
% 2.00/0.97    ( ! [X2,X0,X3,X1] : (m1_subset_1(k1_domain_1(X0,X1,X2,X3),k2_zfmisc_1(X0,X1)) | ~m1_subset_1(X3,X1) | ~m1_subset_1(X2,X0) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.00/0.97    inference(cnf_transformation,[],[f9])).
% 2.00/0.97  
% 2.00/0.97  fof(f6,conjecture,(
% 2.00/0.97    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : (m1_subset_1(X3,X1) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) & v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1) & v1_funct_1(X5)) => ((r3_binop_1(X1,X3,X5) & r3_binop_1(X0,X2,X4)) <=> r3_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5)))))))))),
% 2.00/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.00/0.97  
% 2.00/0.97  fof(f7,negated_conjecture,(
% 2.00/0.97    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : (m1_subset_1(X3,X1) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) & v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1) & v1_funct_1(X5)) => ((r3_binop_1(X1,X3,X5) & r3_binop_1(X0,X2,X4)) <=> r3_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5)))))))))),
% 2.00/0.97    inference(negated_conjecture,[],[f6])).
% 2.00/0.97  
% 2.00/0.97  fof(f18,plain,(
% 2.00/0.97    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((r3_binop_1(X1,X3,X5) & r3_binop_1(X0,X2,X4)) <~> r3_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) & v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0) & v1_funct_1(X4))) & m1_subset_1(X3,X1)) & m1_subset_1(X2,X0)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 2.00/0.97    inference(ennf_transformation,[],[f7])).
% 2.00/0.97  
% 2.00/0.97  fof(f19,plain,(
% 2.00/0.97    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((r3_binop_1(X1,X3,X5) & r3_binop_1(X0,X2,X4)) <~> r3_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) & v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0) & v1_funct_1(X4)) & m1_subset_1(X3,X1)) & m1_subset_1(X2,X0)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 2.00/0.97    inference(flattening,[],[f18])).
% 2.00/0.97  
% 2.00/0.97  fof(f26,plain,(
% 2.00/0.97    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((~r3_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5)) | (~r3_binop_1(X1,X3,X5) | ~r3_binop_1(X0,X2,X4))) & (r3_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5)) | (r3_binop_1(X1,X3,X5) & r3_binop_1(X0,X2,X4)))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) & v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0) & v1_funct_1(X4)) & m1_subset_1(X3,X1)) & m1_subset_1(X2,X0)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 2.00/0.97    inference(nnf_transformation,[],[f19])).
% 2.00/0.97  
% 2.00/0.97  fof(f27,plain,(
% 2.00/0.97    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r3_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5)) | ~r3_binop_1(X1,X3,X5) | ~r3_binop_1(X0,X2,X4)) & (r3_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5)) | (r3_binop_1(X1,X3,X5) & r3_binop_1(X0,X2,X4))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) & v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0) & v1_funct_1(X4)) & m1_subset_1(X3,X1)) & m1_subset_1(X2,X0)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 2.00/0.97    inference(flattening,[],[f26])).
% 2.00/0.97  
% 2.00/0.97  fof(f33,plain,(
% 2.00/0.97    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((~r3_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5)) | ~r3_binop_1(X1,X3,X5) | ~r3_binop_1(X0,X2,X4)) & (r3_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5)) | (r3_binop_1(X1,X3,X5) & r3_binop_1(X0,X2,X4))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1) & v1_funct_1(X5)) => ((~r3_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,sK5)) | ~r3_binop_1(X1,X3,sK5) | ~r3_binop_1(X0,X2,X4)) & (r3_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,sK5)) | (r3_binop_1(X1,X3,sK5) & r3_binop_1(X0,X2,X4))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) & v1_funct_2(sK5,k2_zfmisc_1(X1,X1),X1) & v1_funct_1(sK5))) )),
% 2.00/0.97    introduced(choice_axiom,[])).
% 2.00/0.97  
% 2.00/0.97  fof(f32,plain,(
% 2.00/0.97    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((~r3_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5)) | ~r3_binop_1(X1,X3,X5) | ~r3_binop_1(X0,X2,X4)) & (r3_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5)) | (r3_binop_1(X1,X3,X5) & r3_binop_1(X0,X2,X4))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) & v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0) & v1_funct_1(X4)) => (? [X5] : ((~r3_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,sK4,X5)) | ~r3_binop_1(X1,X3,X5) | ~r3_binop_1(X0,X2,sK4)) & (r3_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,sK4,X5)) | (r3_binop_1(X1,X3,X5) & r3_binop_1(X0,X2,sK4))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1) & v1_funct_1(X5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) & v1_funct_2(sK4,k2_zfmisc_1(X0,X0),X0) & v1_funct_1(sK4))) )),
% 2.00/0.97    introduced(choice_axiom,[])).
% 2.00/0.97  
% 2.00/0.97  fof(f31,plain,(
% 2.00/0.97    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((~r3_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5)) | ~r3_binop_1(X1,X3,X5) | ~r3_binop_1(X0,X2,X4)) & (r3_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5)) | (r3_binop_1(X1,X3,X5) & r3_binop_1(X0,X2,X4))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) & v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0) & v1_funct_1(X4)) & m1_subset_1(X3,X1)) => (? [X4] : (? [X5] : ((~r3_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,sK3),k6_filter_1(X0,X1,X4,X5)) | ~r3_binop_1(X1,sK3,X5) | ~r3_binop_1(X0,X2,X4)) & (r3_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,sK3),k6_filter_1(X0,X1,X4,X5)) | (r3_binop_1(X1,sK3,X5) & r3_binop_1(X0,X2,X4))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) & v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0) & v1_funct_1(X4)) & m1_subset_1(sK3,X1))) )),
% 2.00/0.97    introduced(choice_axiom,[])).
% 2.00/0.97  
% 2.00/0.97  fof(f30,plain,(
% 2.00/0.97    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r3_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5)) | ~r3_binop_1(X1,X3,X5) | ~r3_binop_1(X0,X2,X4)) & (r3_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5)) | (r3_binop_1(X1,X3,X5) & r3_binop_1(X0,X2,X4))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) & v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0) & v1_funct_1(X4)) & m1_subset_1(X3,X1)) & m1_subset_1(X2,X0)) => (? [X3] : (? [X4] : (? [X5] : ((~r3_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,sK2,X3),k6_filter_1(X0,X1,X4,X5)) | ~r3_binop_1(X1,X3,X5) | ~r3_binop_1(X0,sK2,X4)) & (r3_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,sK2,X3),k6_filter_1(X0,X1,X4,X5)) | (r3_binop_1(X1,X3,X5) & r3_binop_1(X0,sK2,X4))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) & v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0) & v1_funct_1(X4)) & m1_subset_1(X3,X1)) & m1_subset_1(sK2,X0))) )),
% 2.00/0.97    introduced(choice_axiom,[])).
% 2.00/0.97  
% 2.00/0.97  fof(f29,plain,(
% 2.00/0.97    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r3_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5)) | ~r3_binop_1(X1,X3,X5) | ~r3_binop_1(X0,X2,X4)) & (r3_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5)) | (r3_binop_1(X1,X3,X5) & r3_binop_1(X0,X2,X4))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) & v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0) & v1_funct_1(X4)) & m1_subset_1(X3,X1)) & m1_subset_1(X2,X0)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r3_binop_1(k2_zfmisc_1(X0,sK1),k1_domain_1(X0,sK1,X2,X3),k6_filter_1(X0,sK1,X4,X5)) | ~r3_binop_1(sK1,X3,X5) | ~r3_binop_1(X0,X2,X4)) & (r3_binop_1(k2_zfmisc_1(X0,sK1),k1_domain_1(X0,sK1,X2,X3),k6_filter_1(X0,sK1,X4,X5)) | (r3_binop_1(sK1,X3,X5) & r3_binop_1(X0,X2,X4))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) & v1_funct_2(X5,k2_zfmisc_1(sK1,sK1),sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) & v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0) & v1_funct_1(X4)) & m1_subset_1(X3,sK1)) & m1_subset_1(X2,X0)) & ~v1_xboole_0(sK1))) )),
% 2.00/0.97    introduced(choice_axiom,[])).
% 2.00/0.97  
% 2.00/0.97  fof(f28,plain,(
% 2.00/0.97    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r3_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5)) | ~r3_binop_1(X1,X3,X5) | ~r3_binop_1(X0,X2,X4)) & (r3_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5)) | (r3_binop_1(X1,X3,X5) & r3_binop_1(X0,X2,X4))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) & v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0) & v1_funct_1(X4)) & m1_subset_1(X3,X1)) & m1_subset_1(X2,X0)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r3_binop_1(k2_zfmisc_1(sK0,X1),k1_domain_1(sK0,X1,X2,X3),k6_filter_1(sK0,X1,X4,X5)) | ~r3_binop_1(X1,X3,X5) | ~r3_binop_1(sK0,X2,X4)) & (r3_binop_1(k2_zfmisc_1(sK0,X1),k1_domain_1(sK0,X1,X2,X3),k6_filter_1(sK0,X1,X4,X5)) | (r3_binop_1(X1,X3,X5) & r3_binop_1(sK0,X2,X4))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) & v1_funct_2(X4,k2_zfmisc_1(sK0,sK0),sK0) & v1_funct_1(X4)) & m1_subset_1(X3,X1)) & m1_subset_1(X2,sK0)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 2.00/0.97    introduced(choice_axiom,[])).
% 2.00/0.97  
% 2.00/0.97  fof(f34,plain,(
% 2.00/0.97    ((((((~r3_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5)) | ~r3_binop_1(sK1,sK3,sK5) | ~r3_binop_1(sK0,sK2,sK4)) & (r3_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5)) | (r3_binop_1(sK1,sK3,sK5) & r3_binop_1(sK0,sK2,sK4))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) & v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) & v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0) & v1_funct_1(sK4)) & m1_subset_1(sK3,sK1)) & m1_subset_1(sK2,sK0)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 2.00/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f27,f33,f32,f31,f30,f29,f28])).
% 2.00/0.97  
% 2.00/0.97  fof(f60,plain,(
% 2.00/0.97    ~r3_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5)) | ~r3_binop_1(sK1,sK3,sK5) | ~r3_binop_1(sK0,sK2,sK4)),
% 2.00/0.97    inference(cnf_transformation,[],[f34])).
% 2.00/0.97  
% 2.00/0.97  fof(f59,plain,(
% 2.00/0.97    r3_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5)) | r3_binop_1(sK1,sK3,sK5)),
% 2.00/0.97    inference(cnf_transformation,[],[f34])).
% 2.00/0.97  
% 2.00/0.97  fof(f58,plain,(
% 2.00/0.97    r3_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5)) | r3_binop_1(sK0,sK2,sK4)),
% 2.00/0.97    inference(cnf_transformation,[],[f34])).
% 2.00/0.97  
% 2.00/0.97  fof(f57,plain,(
% 2.00/0.97    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))),
% 2.00/0.97    inference(cnf_transformation,[],[f34])).
% 2.00/0.97  
% 2.00/0.97  fof(f56,plain,(
% 2.00/0.97    v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)),
% 2.00/0.97    inference(cnf_transformation,[],[f34])).
% 2.00/0.97  
% 2.00/0.97  fof(f55,plain,(
% 2.00/0.97    v1_funct_1(sK5)),
% 2.00/0.97    inference(cnf_transformation,[],[f34])).
% 2.00/0.97  
% 2.00/0.97  fof(f54,plain,(
% 2.00/0.97    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))),
% 2.00/0.97    inference(cnf_transformation,[],[f34])).
% 2.00/0.97  
% 2.00/0.97  fof(f53,plain,(
% 2.00/0.97    v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)),
% 2.00/0.97    inference(cnf_transformation,[],[f34])).
% 2.00/0.97  
% 2.00/0.97  fof(f52,plain,(
% 2.00/0.97    v1_funct_1(sK4)),
% 2.00/0.97    inference(cnf_transformation,[],[f34])).
% 2.00/0.97  
% 2.00/0.97  fof(f51,plain,(
% 2.00/0.97    m1_subset_1(sK3,sK1)),
% 2.00/0.97    inference(cnf_transformation,[],[f34])).
% 2.00/0.97  
% 2.00/0.97  fof(f50,plain,(
% 2.00/0.97    m1_subset_1(sK2,sK0)),
% 2.00/0.97    inference(cnf_transformation,[],[f34])).
% 2.00/0.97  
% 2.00/0.97  fof(f49,plain,(
% 2.00/0.97    ~v1_xboole_0(sK1)),
% 2.00/0.97    inference(cnf_transformation,[],[f34])).
% 2.00/0.97  
% 2.00/0.97  fof(f48,plain,(
% 2.00/0.97    ~v1_xboole_0(sK0)),
% 2.00/0.97    inference(cnf_transformation,[],[f34])).
% 2.00/0.97  
% 2.00/0.97  cnf(c_9,plain,
% 2.00/0.97      ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
% 2.00/0.97      | ~ v1_funct_2(X2,k2_zfmisc_1(X3,X3),X3)
% 2.00/0.97      | ~ r1_binop_1(X1,X4,X0)
% 2.00/0.97      | ~ r1_binop_1(X3,X5,X2)
% 2.00/0.97      | r1_binop_1(k2_zfmisc_1(X3,X1),k1_domain_1(X3,X1,X5,X4),k6_filter_1(X3,X1,X2,X0))
% 2.00/0.97      | ~ m1_subset_1(X4,X1)
% 2.00/0.97      | ~ m1_subset_1(X5,X3)
% 2.00/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
% 2.00/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X3,X3),X3)))
% 2.00/0.97      | ~ v1_funct_1(X0)
% 2.00/0.97      | ~ v1_funct_1(X2)
% 2.00/0.97      | v1_xboole_0(X3)
% 2.00/0.97      | v1_xboole_0(X1) ),
% 2.00/0.97      inference(cnf_transformation,[],[f42]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_274,plain,
% 2.00/0.97      ( ~ v1_funct_2(X0_46,k2_zfmisc_1(X0_45,X0_45),X0_45)
% 2.00/0.97      | ~ v1_funct_2(X1_46,k2_zfmisc_1(X1_45,X1_45),X1_45)
% 2.00/0.97      | ~ r1_binop_1(X0_45,X2_46,X0_46)
% 2.00/0.97      | ~ r1_binop_1(X1_45,X3_46,X1_46)
% 2.00/0.97      | r1_binop_1(k2_zfmisc_1(X1_45,X0_45),k1_domain_1(X1_45,X0_45,X3_46,X2_46),k6_filter_1(X1_45,X0_45,X1_46,X0_46))
% 2.00/0.97      | ~ m1_subset_1(X2_46,X0_45)
% 2.00/0.97      | ~ m1_subset_1(X3_46,X1_45)
% 2.00/0.97      | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0_45,X0_45),X0_45)))
% 2.00/0.97      | ~ m1_subset_1(X1_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1_45,X1_45),X1_45)))
% 2.00/0.97      | ~ v1_funct_1(X0_46)
% 2.00/0.97      | ~ v1_funct_1(X1_46)
% 2.00/0.97      | v1_xboole_0(X1_45)
% 2.00/0.97      | v1_xboole_0(X0_45) ),
% 2.00/0.97      inference(subtyping,[status(esa)],[c_9]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_826,plain,
% 2.00/0.97      ( ~ v1_funct_2(X0_46,k2_zfmisc_1(X0_45,X0_45),X0_45)
% 2.00/0.97      | ~ v1_funct_2(X1_46,k2_zfmisc_1(sK1,sK1),sK1)
% 2.00/0.97      | ~ r1_binop_1(X0_45,X2_46,X0_46)
% 2.00/0.97      | r1_binop_1(k2_zfmisc_1(X0_45,sK1),k1_domain_1(X0_45,sK1,X2_46,sK3),k6_filter_1(X0_45,sK1,X0_46,X1_46))
% 2.00/0.97      | ~ r1_binop_1(sK1,sK3,X1_46)
% 2.00/0.97      | ~ m1_subset_1(X2_46,X0_45)
% 2.00/0.97      | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0_45,X0_45),X0_45)))
% 2.00/0.97      | ~ m1_subset_1(X1_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
% 2.00/0.97      | ~ m1_subset_1(sK3,sK1)
% 2.00/0.97      | ~ v1_funct_1(X1_46)
% 2.00/0.97      | ~ v1_funct_1(X0_46)
% 2.00/0.97      | v1_xboole_0(X0_45)
% 2.00/0.97      | v1_xboole_0(sK1) ),
% 2.00/0.97      inference(instantiation,[status(thm)],[c_274]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_1626,plain,
% 2.00/0.97      ( ~ v1_funct_2(X0_46,k2_zfmisc_1(X0_45,X0_45),X0_45)
% 2.00/0.97      | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
% 2.00/0.97      | ~ r1_binop_1(X0_45,X1_46,X0_46)
% 2.00/0.97      | r1_binop_1(k2_zfmisc_1(X0_45,sK1),k1_domain_1(X0_45,sK1,X1_46,sK3),k6_filter_1(X0_45,sK1,X0_46,sK5))
% 2.00/0.97      | ~ r1_binop_1(sK1,sK3,sK5)
% 2.00/0.97      | ~ m1_subset_1(X1_46,X0_45)
% 2.00/0.97      | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0_45,X0_45),X0_45)))
% 2.00/0.97      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
% 2.00/0.97      | ~ m1_subset_1(sK3,sK1)
% 2.00/0.97      | ~ v1_funct_1(X0_46)
% 2.00/0.97      | ~ v1_funct_1(sK5)
% 2.00/0.97      | v1_xboole_0(X0_45)
% 2.00/0.97      | v1_xboole_0(sK1) ),
% 2.00/0.97      inference(instantiation,[status(thm)],[c_826]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_1807,plain,
% 2.00/0.97      ( ~ v1_funct_2(X0_46,k2_zfmisc_1(sK0,sK0),sK0)
% 2.00/0.97      | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
% 2.00/0.97      | r1_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,X0_46,sK5))
% 2.00/0.97      | ~ r1_binop_1(sK1,sK3,sK5)
% 2.00/0.97      | ~ r1_binop_1(sK0,sK2,X0_46)
% 2.00/0.97      | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
% 2.00/0.97      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
% 2.00/0.97      | ~ m1_subset_1(sK3,sK1)
% 2.00/0.97      | ~ m1_subset_1(sK2,sK0)
% 2.00/0.97      | ~ v1_funct_1(X0_46)
% 2.00/0.97      | ~ v1_funct_1(sK5)
% 2.00/0.97      | v1_xboole_0(sK1)
% 2.00/0.97      | v1_xboole_0(sK0) ),
% 2.00/0.97      inference(instantiation,[status(thm)],[c_1626]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_1808,plain,
% 2.00/0.97      ( v1_funct_2(X0_46,k2_zfmisc_1(sK0,sK0),sK0) != iProver_top
% 2.00/0.97      | v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1) != iProver_top
% 2.00/0.97      | r1_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,X0_46,sK5)) = iProver_top
% 2.00/0.97      | r1_binop_1(sK1,sK3,sK5) != iProver_top
% 2.00/0.97      | r1_binop_1(sK0,sK2,X0_46) != iProver_top
% 2.00/0.97      | m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) != iProver_top
% 2.00/0.97      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) != iProver_top
% 2.00/0.97      | m1_subset_1(sK3,sK1) != iProver_top
% 2.00/0.97      | m1_subset_1(sK2,sK0) != iProver_top
% 2.00/0.97      | v1_funct_1(X0_46) != iProver_top
% 2.00/0.97      | v1_funct_1(sK5) != iProver_top
% 2.00/0.97      | v1_xboole_0(sK1) = iProver_top
% 2.00/0.97      | v1_xboole_0(sK0) = iProver_top ),
% 2.00/0.97      inference(predicate_to_equality,[status(thm)],[c_1807]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_1810,plain,
% 2.00/0.97      ( v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1) != iProver_top
% 2.00/0.97      | v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0) != iProver_top
% 2.00/0.97      | r1_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5)) = iProver_top
% 2.00/0.97      | r1_binop_1(sK1,sK3,sK5) != iProver_top
% 2.00/0.97      | r1_binop_1(sK0,sK2,sK4) != iProver_top
% 2.00/0.97      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) != iProver_top
% 2.00/0.97      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) != iProver_top
% 2.00/0.97      | m1_subset_1(sK3,sK1) != iProver_top
% 2.00/0.97      | m1_subset_1(sK2,sK0) != iProver_top
% 2.00/0.97      | v1_funct_1(sK5) != iProver_top
% 2.00/0.97      | v1_funct_1(sK4) != iProver_top
% 2.00/0.97      | v1_xboole_0(sK1) = iProver_top
% 2.00/0.97      | v1_xboole_0(sK0) = iProver_top ),
% 2.00/0.97      inference(instantiation,[status(thm)],[c_1808]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_12,plain,
% 2.00/0.97      ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
% 2.00/0.97      | ~ v1_funct_2(X2,k2_zfmisc_1(X3,X3),X3)
% 2.00/0.97      | ~ r2_binop_1(X1,X4,X0)
% 2.00/0.97      | ~ r2_binop_1(X3,X5,X2)
% 2.00/0.97      | r2_binop_1(k2_zfmisc_1(X3,X1),k1_domain_1(X3,X1,X5,X4),k6_filter_1(X3,X1,X2,X0))
% 2.00/0.97      | ~ m1_subset_1(X4,X1)
% 2.00/0.97      | ~ m1_subset_1(X5,X3)
% 2.00/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
% 2.00/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X3,X3),X3)))
% 2.00/0.97      | ~ v1_funct_1(X0)
% 2.00/0.97      | ~ v1_funct_1(X2)
% 2.00/0.97      | v1_xboole_0(X3)
% 2.00/0.97      | v1_xboole_0(X1) ),
% 2.00/0.97      inference(cnf_transformation,[],[f45]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_271,plain,
% 2.00/0.97      ( ~ v1_funct_2(X0_46,k2_zfmisc_1(X0_45,X0_45),X0_45)
% 2.00/0.97      | ~ v1_funct_2(X1_46,k2_zfmisc_1(X1_45,X1_45),X1_45)
% 2.00/0.97      | ~ r2_binop_1(X0_45,X2_46,X0_46)
% 2.00/0.97      | ~ r2_binop_1(X1_45,X3_46,X1_46)
% 2.00/0.97      | r2_binop_1(k2_zfmisc_1(X1_45,X0_45),k1_domain_1(X1_45,X0_45,X3_46,X2_46),k6_filter_1(X1_45,X0_45,X1_46,X0_46))
% 2.00/0.97      | ~ m1_subset_1(X2_46,X0_45)
% 2.00/0.97      | ~ m1_subset_1(X3_46,X1_45)
% 2.00/0.97      | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0_45,X0_45),X0_45)))
% 2.00/0.97      | ~ m1_subset_1(X1_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1_45,X1_45),X1_45)))
% 2.00/0.97      | ~ v1_funct_1(X0_46)
% 2.00/0.97      | ~ v1_funct_1(X1_46)
% 2.00/0.97      | v1_xboole_0(X1_45)
% 2.00/0.97      | v1_xboole_0(X0_45) ),
% 2.00/0.97      inference(subtyping,[status(esa)],[c_12]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_801,plain,
% 2.00/0.97      ( ~ v1_funct_2(X0_46,k2_zfmisc_1(X0_45,X0_45),X0_45)
% 2.00/0.97      | ~ v1_funct_2(X1_46,k2_zfmisc_1(sK1,sK1),sK1)
% 2.00/0.97      | ~ r2_binop_1(X0_45,X2_46,X0_46)
% 2.00/0.97      | r2_binop_1(k2_zfmisc_1(X0_45,sK1),k1_domain_1(X0_45,sK1,X2_46,sK3),k6_filter_1(X0_45,sK1,X0_46,X1_46))
% 2.00/0.97      | ~ r2_binop_1(sK1,sK3,X1_46)
% 2.00/0.97      | ~ m1_subset_1(X2_46,X0_45)
% 2.00/0.97      | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0_45,X0_45),X0_45)))
% 2.00/0.97      | ~ m1_subset_1(X1_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
% 2.00/0.97      | ~ m1_subset_1(sK3,sK1)
% 2.00/0.97      | ~ v1_funct_1(X1_46)
% 2.00/0.97      | ~ v1_funct_1(X0_46)
% 2.00/0.97      | v1_xboole_0(X0_45)
% 2.00/0.97      | v1_xboole_0(sK1) ),
% 2.00/0.97      inference(instantiation,[status(thm)],[c_271]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_1618,plain,
% 2.00/0.97      ( ~ v1_funct_2(X0_46,k2_zfmisc_1(X0_45,X0_45),X0_45)
% 2.00/0.97      | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
% 2.00/0.97      | ~ r2_binop_1(X0_45,X1_46,X0_46)
% 2.00/0.97      | r2_binop_1(k2_zfmisc_1(X0_45,sK1),k1_domain_1(X0_45,sK1,X1_46,sK3),k6_filter_1(X0_45,sK1,X0_46,sK5))
% 2.00/0.97      | ~ r2_binop_1(sK1,sK3,sK5)
% 2.00/0.97      | ~ m1_subset_1(X1_46,X0_45)
% 2.00/0.97      | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0_45,X0_45),X0_45)))
% 2.00/0.97      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
% 2.00/0.97      | ~ m1_subset_1(sK3,sK1)
% 2.00/0.97      | ~ v1_funct_1(X0_46)
% 2.00/0.97      | ~ v1_funct_1(sK5)
% 2.00/0.97      | v1_xboole_0(X0_45)
% 2.00/0.97      | v1_xboole_0(sK1) ),
% 2.00/0.97      inference(instantiation,[status(thm)],[c_801]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_1761,plain,
% 2.00/0.97      ( ~ v1_funct_2(X0_46,k2_zfmisc_1(sK0,sK0),sK0)
% 2.00/0.97      | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
% 2.00/0.97      | r2_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,X0_46,sK5))
% 2.00/0.97      | ~ r2_binop_1(sK1,sK3,sK5)
% 2.00/0.97      | ~ r2_binop_1(sK0,sK2,X0_46)
% 2.00/0.97      | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
% 2.00/0.97      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
% 2.00/0.97      | ~ m1_subset_1(sK3,sK1)
% 2.00/0.97      | ~ m1_subset_1(sK2,sK0)
% 2.00/0.97      | ~ v1_funct_1(X0_46)
% 2.00/0.97      | ~ v1_funct_1(sK5)
% 2.00/0.97      | v1_xboole_0(sK1)
% 2.00/0.97      | v1_xboole_0(sK0) ),
% 2.00/0.97      inference(instantiation,[status(thm)],[c_1618]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_1762,plain,
% 2.00/0.97      ( v1_funct_2(X0_46,k2_zfmisc_1(sK0,sK0),sK0) != iProver_top
% 2.00/0.97      | v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1) != iProver_top
% 2.00/0.97      | r2_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,X0_46,sK5)) = iProver_top
% 2.00/0.97      | r2_binop_1(sK1,sK3,sK5) != iProver_top
% 2.00/0.97      | r2_binop_1(sK0,sK2,X0_46) != iProver_top
% 2.00/0.97      | m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) != iProver_top
% 2.00/0.97      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) != iProver_top
% 2.00/0.97      | m1_subset_1(sK3,sK1) != iProver_top
% 2.00/0.97      | m1_subset_1(sK2,sK0) != iProver_top
% 2.00/0.97      | v1_funct_1(X0_46) != iProver_top
% 2.00/0.97      | v1_funct_1(sK5) != iProver_top
% 2.00/0.97      | v1_xboole_0(sK1) = iProver_top
% 2.00/0.97      | v1_xboole_0(sK0) = iProver_top ),
% 2.00/0.97      inference(predicate_to_equality,[status(thm)],[c_1761]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_1764,plain,
% 2.00/0.97      ( v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1) != iProver_top
% 2.00/0.97      | v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0) != iProver_top
% 2.00/0.97      | r2_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5)) = iProver_top
% 2.00/0.97      | r2_binop_1(sK1,sK3,sK5) != iProver_top
% 2.00/0.97      | r2_binop_1(sK0,sK2,sK4) != iProver_top
% 2.00/0.97      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) != iProver_top
% 2.00/0.97      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) != iProver_top
% 2.00/0.97      | m1_subset_1(sK3,sK1) != iProver_top
% 2.00/0.97      | m1_subset_1(sK2,sK0) != iProver_top
% 2.00/0.97      | v1_funct_1(sK5) != iProver_top
% 2.00/0.97      | v1_funct_1(sK4) != iProver_top
% 2.00/0.97      | v1_xboole_0(sK1) = iProver_top
% 2.00/0.97      | v1_xboole_0(sK0) = iProver_top ),
% 2.00/0.97      inference(instantiation,[status(thm)],[c_1762]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_2,plain,
% 2.00/0.97      ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
% 2.00/0.97      | r2_binop_1(X1,X2,X0)
% 2.00/0.97      | ~ r3_binop_1(X1,X2,X0)
% 2.00/0.97      | ~ m1_subset_1(X2,X1)
% 2.00/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
% 2.00/0.97      | ~ v1_funct_1(X0) ),
% 2.00/0.97      inference(cnf_transformation,[],[f37]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_281,plain,
% 2.00/0.97      ( ~ v1_funct_2(X0_46,k2_zfmisc_1(X0_45,X0_45),X0_45)
% 2.00/0.97      | r2_binop_1(X0_45,X1_46,X0_46)
% 2.00/0.97      | ~ r3_binop_1(X0_45,X1_46,X0_46)
% 2.00/0.97      | ~ m1_subset_1(X1_46,X0_45)
% 2.00/0.97      | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0_45,X0_45),X0_45)))
% 2.00/0.97      | ~ v1_funct_1(X0_46) ),
% 2.00/0.97      inference(subtyping,[status(esa)],[c_2]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_460,plain,
% 2.00/0.97      ( ~ v1_funct_2(X0_46,k2_zfmisc_1(sK1,sK1),sK1)
% 2.00/0.97      | r2_binop_1(sK1,sK3,X0_46)
% 2.00/0.97      | ~ r3_binop_1(sK1,sK3,X0_46)
% 2.00/0.97      | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
% 2.00/0.97      | ~ m1_subset_1(sK3,sK1)
% 2.00/0.97      | ~ v1_funct_1(X0_46) ),
% 2.00/0.97      inference(instantiation,[status(thm)],[c_281]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_1738,plain,
% 2.00/0.97      ( ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
% 2.00/0.97      | r2_binop_1(sK1,sK3,sK5)
% 2.00/0.97      | ~ r3_binop_1(sK1,sK3,sK5)
% 2.00/0.97      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
% 2.00/0.97      | ~ m1_subset_1(sK3,sK1)
% 2.00/0.97      | ~ v1_funct_1(sK5) ),
% 2.00/0.97      inference(instantiation,[status(thm)],[c_460]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_1742,plain,
% 2.00/0.97      ( v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1) != iProver_top
% 2.00/0.97      | r2_binop_1(sK1,sK3,sK5) = iProver_top
% 2.00/0.97      | r3_binop_1(sK1,sK3,sK5) != iProver_top
% 2.00/0.97      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) != iProver_top
% 2.00/0.97      | m1_subset_1(sK3,sK1) != iProver_top
% 2.00/0.97      | v1_funct_1(sK5) != iProver_top ),
% 2.00/0.97      inference(predicate_to_equality,[status(thm)],[c_1738]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_3,plain,
% 2.00/0.97      ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
% 2.00/0.97      | r1_binop_1(X1,X2,X0)
% 2.00/0.97      | ~ r3_binop_1(X1,X2,X0)
% 2.00/0.97      | ~ m1_subset_1(X2,X1)
% 2.00/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
% 2.00/0.97      | ~ v1_funct_1(X0) ),
% 2.00/0.97      inference(cnf_transformation,[],[f36]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_280,plain,
% 2.00/0.97      ( ~ v1_funct_2(X0_46,k2_zfmisc_1(X0_45,X0_45),X0_45)
% 2.00/0.97      | r1_binop_1(X0_45,X1_46,X0_46)
% 2.00/0.97      | ~ r3_binop_1(X0_45,X1_46,X0_46)
% 2.00/0.97      | ~ m1_subset_1(X1_46,X0_45)
% 2.00/0.97      | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0_45,X0_45),X0_45)))
% 2.00/0.97      | ~ v1_funct_1(X0_46) ),
% 2.00/0.97      inference(subtyping,[status(esa)],[c_3]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_440,plain,
% 2.00/0.97      ( ~ v1_funct_2(X0_46,k2_zfmisc_1(sK1,sK1),sK1)
% 2.00/0.97      | r1_binop_1(sK1,sK3,X0_46)
% 2.00/0.97      | ~ r3_binop_1(sK1,sK3,X0_46)
% 2.00/0.97      | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
% 2.00/0.97      | ~ m1_subset_1(sK3,sK1)
% 2.00/0.97      | ~ v1_funct_1(X0_46) ),
% 2.00/0.97      inference(instantiation,[status(thm)],[c_280]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_1739,plain,
% 2.00/0.97      ( ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
% 2.00/0.97      | r1_binop_1(sK1,sK3,sK5)
% 2.00/0.97      | ~ r3_binop_1(sK1,sK3,sK5)
% 2.00/0.97      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
% 2.00/0.97      | ~ m1_subset_1(sK3,sK1)
% 2.00/0.97      | ~ v1_funct_1(sK5) ),
% 2.00/0.97      inference(instantiation,[status(thm)],[c_440]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_1740,plain,
% 2.00/0.97      ( v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1) != iProver_top
% 2.00/0.97      | r1_binop_1(sK1,sK3,sK5) = iProver_top
% 2.00/0.97      | r3_binop_1(sK1,sK3,sK5) != iProver_top
% 2.00/0.97      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) != iProver_top
% 2.00/0.97      | m1_subset_1(sK3,sK1) != iProver_top
% 2.00/0.97      | v1_funct_1(sK5) != iProver_top ),
% 2.00/0.97      inference(predicate_to_equality,[status(thm)],[c_1739]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_1,plain,
% 2.00/0.97      ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
% 2.00/0.97      | ~ r1_binop_1(X1,X2,X0)
% 2.00/0.97      | ~ r2_binop_1(X1,X2,X0)
% 2.00/0.97      | r3_binop_1(X1,X2,X0)
% 2.00/0.97      | ~ m1_subset_1(X2,X1)
% 2.00/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
% 2.00/0.97      | ~ v1_funct_1(X0) ),
% 2.00/0.97      inference(cnf_transformation,[],[f38]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_282,plain,
% 2.00/0.97      ( ~ v1_funct_2(X0_46,k2_zfmisc_1(X0_45,X0_45),X0_45)
% 2.00/0.97      | ~ r1_binop_1(X0_45,X1_46,X0_46)
% 2.00/0.97      | ~ r2_binop_1(X0_45,X1_46,X0_46)
% 2.00/0.97      | r3_binop_1(X0_45,X1_46,X0_46)
% 2.00/0.97      | ~ m1_subset_1(X1_46,X0_45)
% 2.00/0.97      | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0_45,X0_45),X0_45)))
% 2.00/0.97      | ~ v1_funct_1(X0_46) ),
% 2.00/0.97      inference(subtyping,[status(esa)],[c_1]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_480,plain,
% 2.00/0.97      ( ~ v1_funct_2(X0_46,k2_zfmisc_1(sK1,sK1),sK1)
% 2.00/0.97      | ~ r1_binop_1(sK1,sK3,X0_46)
% 2.00/0.97      | ~ r2_binop_1(sK1,sK3,X0_46)
% 2.00/0.97      | r3_binop_1(sK1,sK3,X0_46)
% 2.00/0.97      | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
% 2.00/0.97      | ~ m1_subset_1(sK3,sK1)
% 2.00/0.97      | ~ v1_funct_1(X0_46) ),
% 2.00/0.97      inference(instantiation,[status(thm)],[c_282]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_1623,plain,
% 2.00/0.97      ( ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
% 2.00/0.97      | ~ r1_binop_1(sK1,sK3,sK5)
% 2.00/0.97      | ~ r2_binop_1(sK1,sK3,sK5)
% 2.00/0.97      | r3_binop_1(sK1,sK3,sK5)
% 2.00/0.97      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
% 2.00/0.97      | ~ m1_subset_1(sK3,sK1)
% 2.00/0.97      | ~ v1_funct_1(sK5) ),
% 2.00/0.97      inference(instantiation,[status(thm)],[c_480]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_1624,plain,
% 2.00/0.97      ( v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1) != iProver_top
% 2.00/0.97      | r1_binop_1(sK1,sK3,sK5) != iProver_top
% 2.00/0.97      | r2_binop_1(sK1,sK3,sK5) != iProver_top
% 2.00/0.97      | r3_binop_1(sK1,sK3,sK5) = iProver_top
% 2.00/0.97      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) != iProver_top
% 2.00/0.97      | m1_subset_1(sK3,sK1) != iProver_top
% 2.00/0.97      | v1_funct_1(sK5) != iProver_top ),
% 2.00/0.97      inference(predicate_to_equality,[status(thm)],[c_1623]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_1055,plain,
% 2.00/0.97      ( ~ v1_funct_2(X0_46,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
% 2.00/0.97      | ~ r1_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),X0_46)
% 2.00/0.97      | ~ r2_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),X0_46)
% 2.00/0.97      | r3_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),X0_46)
% 2.00/0.97      | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))))
% 2.00/0.97      | ~ m1_subset_1(k1_domain_1(sK0,sK1,sK2,sK3),k2_zfmisc_1(sK0,sK1))
% 2.00/0.97      | ~ v1_funct_1(X0_46) ),
% 2.00/0.97      inference(instantiation,[status(thm)],[c_282]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_1615,plain,
% 2.00/0.97      ( ~ v1_funct_2(k6_filter_1(sK0,sK1,sK4,sK5),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
% 2.00/0.97      | ~ r1_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5))
% 2.00/0.97      | ~ r2_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5))
% 2.00/0.97      | r3_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5))
% 2.00/0.97      | ~ m1_subset_1(k6_filter_1(sK0,sK1,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))))
% 2.00/0.97      | ~ m1_subset_1(k1_domain_1(sK0,sK1,sK2,sK3),k2_zfmisc_1(sK0,sK1))
% 2.00/0.97      | ~ v1_funct_1(k6_filter_1(sK0,sK1,sK4,sK5)) ),
% 2.00/0.97      inference(instantiation,[status(thm)],[c_1055]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_1616,plain,
% 2.00/0.97      ( v1_funct_2(k6_filter_1(sK0,sK1,sK4,sK5),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)) != iProver_top
% 2.00/0.97      | r1_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5)) != iProver_top
% 2.00/0.97      | r2_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5)) != iProver_top
% 2.00/0.97      | r3_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5)) = iProver_top
% 2.00/0.97      | m1_subset_1(k6_filter_1(sK0,sK1,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)))) != iProver_top
% 2.00/0.97      | m1_subset_1(k1_domain_1(sK0,sK1,sK2,sK3),k2_zfmisc_1(sK0,sK1)) != iProver_top
% 2.00/0.97      | v1_funct_1(k6_filter_1(sK0,sK1,sK4,sK5)) != iProver_top ),
% 2.00/0.97      inference(predicate_to_equality,[status(thm)],[c_1615]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_4,plain,
% 2.00/0.97      ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
% 2.00/0.97      | ~ v1_funct_2(X2,k2_zfmisc_1(X3,X3),X3)
% 2.00/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
% 2.00/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X3,X3),X3)))
% 2.00/0.97      | m1_subset_1(k6_filter_1(X1,X3,X0,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3)),k2_zfmisc_1(X1,X3))))
% 2.00/0.97      | ~ v1_funct_1(X0)
% 2.00/0.97      | ~ v1_funct_1(X2) ),
% 2.00/0.97      inference(cnf_transformation,[],[f41]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_279,plain,
% 2.00/0.97      ( ~ v1_funct_2(X0_46,k2_zfmisc_1(X0_45,X0_45),X0_45)
% 2.00/0.97      | ~ v1_funct_2(X1_46,k2_zfmisc_1(X1_45,X1_45),X1_45)
% 2.00/0.97      | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0_45,X0_45),X0_45)))
% 2.00/0.97      | ~ m1_subset_1(X1_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1_45,X1_45),X1_45)))
% 2.00/0.97      | m1_subset_1(k6_filter_1(X0_45,X1_45,X0_46,X1_46),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0_45,X1_45),k2_zfmisc_1(X0_45,X1_45)),k2_zfmisc_1(X0_45,X1_45))))
% 2.00/0.97      | ~ v1_funct_1(X0_46)
% 2.00/0.97      | ~ v1_funct_1(X1_46) ),
% 2.00/0.97      inference(subtyping,[status(esa)],[c_4]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_1587,plain,
% 2.00/0.97      ( ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
% 2.00/0.97      | ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
% 2.00/0.97      | m1_subset_1(k6_filter_1(sK0,sK1,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))))
% 2.00/0.97      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
% 2.00/0.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
% 2.00/0.97      | ~ v1_funct_1(sK5)
% 2.00/0.97      | ~ v1_funct_1(sK4) ),
% 2.00/0.97      inference(instantiation,[status(thm)],[c_279]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_1588,plain,
% 2.00/0.97      ( v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1) != iProver_top
% 2.00/0.97      | v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0) != iProver_top
% 2.00/0.97      | m1_subset_1(k6_filter_1(sK0,sK1,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)))) = iProver_top
% 2.00/0.97      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) != iProver_top
% 2.00/0.97      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) != iProver_top
% 2.00/0.97      | v1_funct_1(sK5) != iProver_top
% 2.00/0.97      | v1_funct_1(sK4) != iProver_top ),
% 2.00/0.97      inference(predicate_to_equality,[status(thm)],[c_1587]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_5,plain,
% 2.00/0.97      ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
% 2.00/0.97      | ~ v1_funct_2(X2,k2_zfmisc_1(X3,X3),X3)
% 2.00/0.97      | v1_funct_2(k6_filter_1(X1,X3,X0,X2),k2_zfmisc_1(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3)),k2_zfmisc_1(X1,X3))
% 2.00/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
% 2.00/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X3,X3),X3)))
% 2.00/0.97      | ~ v1_funct_1(X0)
% 2.00/0.97      | ~ v1_funct_1(X2) ),
% 2.00/0.97      inference(cnf_transformation,[],[f40]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_278,plain,
% 2.00/0.97      ( ~ v1_funct_2(X0_46,k2_zfmisc_1(X0_45,X0_45),X0_45)
% 2.00/0.97      | ~ v1_funct_2(X1_46,k2_zfmisc_1(X1_45,X1_45),X1_45)
% 2.00/0.97      | v1_funct_2(k6_filter_1(X0_45,X1_45,X0_46,X1_46),k2_zfmisc_1(k2_zfmisc_1(X0_45,X1_45),k2_zfmisc_1(X0_45,X1_45)),k2_zfmisc_1(X0_45,X1_45))
% 2.00/0.97      | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0_45,X0_45),X0_45)))
% 2.00/0.97      | ~ m1_subset_1(X1_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1_45,X1_45),X1_45)))
% 2.00/0.97      | ~ v1_funct_1(X0_46)
% 2.00/0.97      | ~ v1_funct_1(X1_46) ),
% 2.00/0.97      inference(subtyping,[status(esa)],[c_5]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_1583,plain,
% 2.00/0.97      ( v1_funct_2(k6_filter_1(sK0,sK1,sK4,sK5),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
% 2.00/0.97      | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
% 2.00/0.97      | ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
% 2.00/0.97      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
% 2.00/0.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
% 2.00/0.97      | ~ v1_funct_1(sK5)
% 2.00/0.97      | ~ v1_funct_1(sK4) ),
% 2.00/0.97      inference(instantiation,[status(thm)],[c_278]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_1584,plain,
% 2.00/0.97      ( v1_funct_2(k6_filter_1(sK0,sK1,sK4,sK5),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)) = iProver_top
% 2.00/0.97      | v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1) != iProver_top
% 2.00/0.97      | v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0) != iProver_top
% 2.00/0.97      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) != iProver_top
% 2.00/0.97      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) != iProver_top
% 2.00/0.97      | v1_funct_1(sK5) != iProver_top
% 2.00/0.97      | v1_funct_1(sK4) != iProver_top ),
% 2.00/0.97      inference(predicate_to_equality,[status(thm)],[c_1583]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_6,plain,
% 2.00/0.97      ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
% 2.00/0.97      | ~ v1_funct_2(X2,k2_zfmisc_1(X3,X3),X3)
% 2.00/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
% 2.00/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X3,X3),X3)))
% 2.00/0.97      | ~ v1_funct_1(X0)
% 2.00/0.97      | ~ v1_funct_1(X2)
% 2.00/0.97      | v1_funct_1(k6_filter_1(X1,X3,X0,X2)) ),
% 2.00/0.97      inference(cnf_transformation,[],[f39]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_277,plain,
% 2.00/0.97      ( ~ v1_funct_2(X0_46,k2_zfmisc_1(X0_45,X0_45),X0_45)
% 2.00/0.97      | ~ v1_funct_2(X1_46,k2_zfmisc_1(X1_45,X1_45),X1_45)
% 2.00/0.97      | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0_45,X0_45),X0_45)))
% 2.00/0.97      | ~ m1_subset_1(X1_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1_45,X1_45),X1_45)))
% 2.00/0.97      | ~ v1_funct_1(X0_46)
% 2.00/0.97      | ~ v1_funct_1(X1_46)
% 2.00/0.97      | v1_funct_1(k6_filter_1(X0_45,X1_45,X0_46,X1_46)) ),
% 2.00/0.97      inference(subtyping,[status(esa)],[c_6]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_1579,plain,
% 2.00/0.97      ( ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
% 2.00/0.97      | ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
% 2.00/0.97      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
% 2.00/0.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
% 2.00/0.97      | v1_funct_1(k6_filter_1(sK0,sK1,sK4,sK5))
% 2.00/0.97      | ~ v1_funct_1(sK5)
% 2.00/0.97      | ~ v1_funct_1(sK4) ),
% 2.00/0.97      inference(instantiation,[status(thm)],[c_277]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_1580,plain,
% 2.00/0.97      ( v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1) != iProver_top
% 2.00/0.97      | v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0) != iProver_top
% 2.00/0.97      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) != iProver_top
% 2.00/0.97      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) != iProver_top
% 2.00/0.97      | v1_funct_1(k6_filter_1(sK0,sK1,sK4,sK5)) = iProver_top
% 2.00/0.97      | v1_funct_1(sK5) != iProver_top
% 2.00/0.97      | v1_funct_1(sK4) != iProver_top ),
% 2.00/0.97      inference(predicate_to_equality,[status(thm)],[c_1579]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_1057,plain,
% 2.00/0.97      ( ~ v1_funct_2(X0_46,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
% 2.00/0.97      | r1_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),X0_46)
% 2.00/0.97      | ~ r3_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),X0_46)
% 2.00/0.97      | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))))
% 2.00/0.97      | ~ m1_subset_1(k1_domain_1(sK0,sK1,sK2,sK3),k2_zfmisc_1(sK0,sK1))
% 2.00/0.97      | ~ v1_funct_1(X0_46) ),
% 2.00/0.97      inference(instantiation,[status(thm)],[c_280]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_1575,plain,
% 2.00/0.97      ( ~ v1_funct_2(k6_filter_1(sK0,sK1,sK4,sK5),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
% 2.00/0.97      | r1_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5))
% 2.00/0.97      | ~ r3_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5))
% 2.00/0.97      | ~ m1_subset_1(k6_filter_1(sK0,sK1,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))))
% 2.00/0.97      | ~ m1_subset_1(k1_domain_1(sK0,sK1,sK2,sK3),k2_zfmisc_1(sK0,sK1))
% 2.00/0.97      | ~ v1_funct_1(k6_filter_1(sK0,sK1,sK4,sK5)) ),
% 2.00/0.97      inference(instantiation,[status(thm)],[c_1057]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_1576,plain,
% 2.00/0.97      ( v1_funct_2(k6_filter_1(sK0,sK1,sK4,sK5),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)) != iProver_top
% 2.00/0.97      | r1_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5)) = iProver_top
% 2.00/0.97      | r3_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5)) != iProver_top
% 2.00/0.97      | m1_subset_1(k6_filter_1(sK0,sK1,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)))) != iProver_top
% 2.00/0.97      | m1_subset_1(k1_domain_1(sK0,sK1,sK2,sK3),k2_zfmisc_1(sK0,sK1)) != iProver_top
% 2.00/0.97      | v1_funct_1(k6_filter_1(sK0,sK1,sK4,sK5)) != iProver_top ),
% 2.00/0.97      inference(predicate_to_equality,[status(thm)],[c_1575]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_1056,plain,
% 2.00/0.97      ( ~ v1_funct_2(X0_46,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
% 2.00/0.97      | r2_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),X0_46)
% 2.00/0.97      | ~ r3_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),X0_46)
% 2.00/0.97      | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))))
% 2.00/0.97      | ~ m1_subset_1(k1_domain_1(sK0,sK1,sK2,sK3),k2_zfmisc_1(sK0,sK1))
% 2.00/0.97      | ~ v1_funct_1(X0_46) ),
% 2.00/0.97      inference(instantiation,[status(thm)],[c_281]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_1572,plain,
% 2.00/0.97      ( ~ v1_funct_2(k6_filter_1(sK0,sK1,sK4,sK5),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
% 2.00/0.97      | r2_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5))
% 2.00/0.97      | ~ r3_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5))
% 2.00/0.97      | ~ m1_subset_1(k6_filter_1(sK0,sK1,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))))
% 2.00/0.97      | ~ m1_subset_1(k1_domain_1(sK0,sK1,sK2,sK3),k2_zfmisc_1(sK0,sK1))
% 2.00/0.97      | ~ v1_funct_1(k6_filter_1(sK0,sK1,sK4,sK5)) ),
% 2.00/0.97      inference(instantiation,[status(thm)],[c_1056]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_1573,plain,
% 2.00/0.97      ( v1_funct_2(k6_filter_1(sK0,sK1,sK4,sK5),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)) != iProver_top
% 2.00/0.97      | r2_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5)) = iProver_top
% 2.00/0.97      | r3_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5)) != iProver_top
% 2.00/0.97      | m1_subset_1(k6_filter_1(sK0,sK1,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)))) != iProver_top
% 2.00/0.97      | m1_subset_1(k1_domain_1(sK0,sK1,sK2,sK3),k2_zfmisc_1(sK0,sK1)) != iProver_top
% 2.00/0.97      | v1_funct_1(k6_filter_1(sK0,sK1,sK4,sK5)) != iProver_top ),
% 2.00/0.97      inference(predicate_to_equality,[status(thm)],[c_1572]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_7,plain,
% 2.00/0.97      ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
% 2.00/0.97      | ~ v1_funct_2(X2,k2_zfmisc_1(X3,X3),X3)
% 2.00/0.97      | r1_binop_1(X1,X4,X0)
% 2.00/0.97      | ~ r1_binop_1(k2_zfmisc_1(X3,X1),k1_domain_1(X3,X1,X5,X4),k6_filter_1(X3,X1,X2,X0))
% 2.00/0.97      | ~ m1_subset_1(X4,X1)
% 2.00/0.97      | ~ m1_subset_1(X5,X3)
% 2.00/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
% 2.00/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X3,X3),X3)))
% 2.00/0.97      | ~ v1_funct_1(X0)
% 2.00/0.97      | ~ v1_funct_1(X2)
% 2.00/0.97      | v1_xboole_0(X3)
% 2.00/0.97      | v1_xboole_0(X1) ),
% 2.00/0.97      inference(cnf_transformation,[],[f44]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_276,plain,
% 2.00/0.97      ( ~ v1_funct_2(X0_46,k2_zfmisc_1(X0_45,X0_45),X0_45)
% 2.00/0.97      | ~ v1_funct_2(X1_46,k2_zfmisc_1(X1_45,X1_45),X1_45)
% 2.00/0.97      | r1_binop_1(X0_45,X2_46,X0_46)
% 2.00/0.97      | ~ r1_binop_1(k2_zfmisc_1(X1_45,X0_45),k1_domain_1(X1_45,X0_45,X3_46,X2_46),k6_filter_1(X1_45,X0_45,X1_46,X0_46))
% 2.00/0.97      | ~ m1_subset_1(X2_46,X0_45)
% 2.00/0.97      | ~ m1_subset_1(X3_46,X1_45)
% 2.00/0.97      | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0_45,X0_45),X0_45)))
% 2.00/0.97      | ~ m1_subset_1(X1_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1_45,X1_45),X1_45)))
% 2.00/0.97      | ~ v1_funct_1(X0_46)
% 2.00/0.97      | ~ v1_funct_1(X1_46)
% 2.00/0.97      | v1_xboole_0(X1_45)
% 2.00/0.97      | v1_xboole_0(X0_45) ),
% 2.00/0.97      inference(subtyping,[status(esa)],[c_7]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_625,plain,
% 2.00/0.97      ( ~ v1_funct_2(X0_46,k2_zfmisc_1(X0_45,X0_45),X0_45)
% 2.00/0.97      | ~ v1_funct_2(X1_46,k2_zfmisc_1(sK1,sK1),sK1)
% 2.00/0.97      | ~ r1_binop_1(k2_zfmisc_1(X0_45,sK1),k1_domain_1(X0_45,sK1,X2_46,sK3),k6_filter_1(X0_45,sK1,X0_46,X1_46))
% 2.00/0.97      | r1_binop_1(sK1,sK3,X1_46)
% 2.00/0.97      | ~ m1_subset_1(X2_46,X0_45)
% 2.00/0.97      | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0_45,X0_45),X0_45)))
% 2.00/0.97      | ~ m1_subset_1(X1_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
% 2.00/0.97      | ~ m1_subset_1(sK3,sK1)
% 2.00/0.97      | ~ v1_funct_1(X1_46)
% 2.00/0.97      | ~ v1_funct_1(X0_46)
% 2.00/0.97      | v1_xboole_0(X0_45)
% 2.00/0.97      | v1_xboole_0(sK1) ),
% 2.00/0.97      inference(instantiation,[status(thm)],[c_276]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_1406,plain,
% 2.00/0.97      ( ~ v1_funct_2(X0_46,k2_zfmisc_1(X0_45,X0_45),X0_45)
% 2.00/0.97      | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
% 2.00/0.97      | ~ r1_binop_1(k2_zfmisc_1(X0_45,sK1),k1_domain_1(X0_45,sK1,X1_46,sK3),k6_filter_1(X0_45,sK1,X0_46,sK5))
% 2.00/0.97      | r1_binop_1(sK1,sK3,sK5)
% 2.00/0.97      | ~ m1_subset_1(X1_46,X0_45)
% 2.00/0.97      | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0_45,X0_45),X0_45)))
% 2.00/0.97      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
% 2.00/0.97      | ~ m1_subset_1(sK3,sK1)
% 2.00/0.97      | ~ v1_funct_1(X0_46)
% 2.00/0.97      | ~ v1_funct_1(sK5)
% 2.00/0.97      | v1_xboole_0(X0_45)
% 2.00/0.97      | v1_xboole_0(sK1) ),
% 2.00/0.97      inference(instantiation,[status(thm)],[c_625]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_1542,plain,
% 2.00/0.97      ( ~ v1_funct_2(X0_46,k2_zfmisc_1(sK0,sK0),sK0)
% 2.00/0.97      | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
% 2.00/0.97      | ~ r1_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,X0_46,sK5))
% 2.00/0.97      | r1_binop_1(sK1,sK3,sK5)
% 2.00/0.97      | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
% 2.00/0.97      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
% 2.00/0.97      | ~ m1_subset_1(sK3,sK1)
% 2.00/0.97      | ~ m1_subset_1(sK2,sK0)
% 2.00/0.97      | ~ v1_funct_1(X0_46)
% 2.00/0.97      | ~ v1_funct_1(sK5)
% 2.00/0.97      | v1_xboole_0(sK1)
% 2.00/0.97      | v1_xboole_0(sK0) ),
% 2.00/0.97      inference(instantiation,[status(thm)],[c_1406]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_1543,plain,
% 2.00/0.97      ( v1_funct_2(X0_46,k2_zfmisc_1(sK0,sK0),sK0) != iProver_top
% 2.00/0.97      | v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1) != iProver_top
% 2.00/0.97      | r1_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,X0_46,sK5)) != iProver_top
% 2.00/0.97      | r1_binop_1(sK1,sK3,sK5) = iProver_top
% 2.00/0.97      | m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) != iProver_top
% 2.00/0.97      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) != iProver_top
% 2.00/0.97      | m1_subset_1(sK3,sK1) != iProver_top
% 2.00/0.97      | m1_subset_1(sK2,sK0) != iProver_top
% 2.00/0.97      | v1_funct_1(X0_46) != iProver_top
% 2.00/0.97      | v1_funct_1(sK5) != iProver_top
% 2.00/0.97      | v1_xboole_0(sK1) = iProver_top
% 2.00/0.97      | v1_xboole_0(sK0) = iProver_top ),
% 2.00/0.97      inference(predicate_to_equality,[status(thm)],[c_1542]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_1545,plain,
% 2.00/0.97      ( v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1) != iProver_top
% 2.00/0.97      | v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0) != iProver_top
% 2.00/0.97      | r1_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5)) != iProver_top
% 2.00/0.97      | r1_binop_1(sK1,sK3,sK5) = iProver_top
% 2.00/0.97      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) != iProver_top
% 2.00/0.97      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) != iProver_top
% 2.00/0.97      | m1_subset_1(sK3,sK1) != iProver_top
% 2.00/0.97      | m1_subset_1(sK2,sK0) != iProver_top
% 2.00/0.97      | v1_funct_1(sK5) != iProver_top
% 2.00/0.97      | v1_funct_1(sK4) != iProver_top
% 2.00/0.97      | v1_xboole_0(sK1) = iProver_top
% 2.00/0.97      | v1_xboole_0(sK0) = iProver_top ),
% 2.00/0.97      inference(instantiation,[status(thm)],[c_1543]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_8,plain,
% 2.00/0.97      ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
% 2.00/0.97      | ~ v1_funct_2(X2,k2_zfmisc_1(X3,X3),X3)
% 2.00/0.97      | r1_binop_1(X3,X4,X2)
% 2.00/0.97      | ~ r1_binop_1(k2_zfmisc_1(X3,X1),k1_domain_1(X3,X1,X4,X5),k6_filter_1(X3,X1,X2,X0))
% 2.00/0.97      | ~ m1_subset_1(X5,X1)
% 2.00/0.97      | ~ m1_subset_1(X4,X3)
% 2.00/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
% 2.00/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X3,X3),X3)))
% 2.00/0.97      | ~ v1_funct_1(X0)
% 2.00/0.97      | ~ v1_funct_1(X2)
% 2.00/0.97      | v1_xboole_0(X3)
% 2.00/0.97      | v1_xboole_0(X1) ),
% 2.00/0.97      inference(cnf_transformation,[],[f43]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_275,plain,
% 2.00/0.97      ( ~ v1_funct_2(X0_46,k2_zfmisc_1(X0_45,X0_45),X0_45)
% 2.00/0.97      | ~ v1_funct_2(X1_46,k2_zfmisc_1(X1_45,X1_45),X1_45)
% 2.00/0.97      | r1_binop_1(X1_45,X2_46,X1_46)
% 2.00/0.97      | ~ r1_binop_1(k2_zfmisc_1(X1_45,X0_45),k1_domain_1(X1_45,X0_45,X2_46,X3_46),k6_filter_1(X1_45,X0_45,X1_46,X0_46))
% 2.00/0.97      | ~ m1_subset_1(X3_46,X0_45)
% 2.00/0.97      | ~ m1_subset_1(X2_46,X1_45)
% 2.00/0.97      | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0_45,X0_45),X0_45)))
% 2.00/0.97      | ~ m1_subset_1(X1_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1_45,X1_45),X1_45)))
% 2.00/0.97      | ~ v1_funct_1(X0_46)
% 2.00/0.97      | ~ v1_funct_1(X1_46)
% 2.00/0.97      | v1_xboole_0(X1_45)
% 2.00/0.97      | v1_xboole_0(X0_45) ),
% 2.00/0.97      inference(subtyping,[status(esa)],[c_8]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_600,plain,
% 2.00/0.97      ( ~ v1_funct_2(X0_46,k2_zfmisc_1(X0_45,X0_45),X0_45)
% 2.00/0.97      | ~ v1_funct_2(X1_46,k2_zfmisc_1(sK1,sK1),sK1)
% 2.00/0.97      | r1_binop_1(X0_45,X2_46,X0_46)
% 2.00/0.97      | ~ r1_binop_1(k2_zfmisc_1(X0_45,sK1),k1_domain_1(X0_45,sK1,X2_46,sK3),k6_filter_1(X0_45,sK1,X0_46,X1_46))
% 2.00/0.97      | ~ m1_subset_1(X2_46,X0_45)
% 2.00/0.97      | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0_45,X0_45),X0_45)))
% 2.00/0.97      | ~ m1_subset_1(X1_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
% 2.00/0.97      | ~ m1_subset_1(sK3,sK1)
% 2.00/0.97      | ~ v1_funct_1(X1_46)
% 2.00/0.97      | ~ v1_funct_1(X0_46)
% 2.00/0.97      | v1_xboole_0(X0_45)
% 2.00/0.97      | v1_xboole_0(sK1) ),
% 2.00/0.97      inference(instantiation,[status(thm)],[c_275]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_1266,plain,
% 2.00/0.97      ( ~ v1_funct_2(X0_46,k2_zfmisc_1(X0_45,X0_45),X0_45)
% 2.00/0.97      | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
% 2.00/0.97      | r1_binop_1(X0_45,X1_46,X0_46)
% 2.00/0.97      | ~ r1_binop_1(k2_zfmisc_1(X0_45,sK1),k1_domain_1(X0_45,sK1,X1_46,sK3),k6_filter_1(X0_45,sK1,X0_46,sK5))
% 2.00/0.97      | ~ m1_subset_1(X1_46,X0_45)
% 2.00/0.97      | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0_45,X0_45),X0_45)))
% 2.00/0.97      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
% 2.00/0.97      | ~ m1_subset_1(sK3,sK1)
% 2.00/0.97      | ~ v1_funct_1(X0_46)
% 2.00/0.97      | ~ v1_funct_1(sK5)
% 2.00/0.97      | v1_xboole_0(X0_45)
% 2.00/0.97      | v1_xboole_0(sK1) ),
% 2.00/0.97      inference(instantiation,[status(thm)],[c_600]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_1478,plain,
% 2.00/0.97      ( ~ v1_funct_2(X0_46,k2_zfmisc_1(sK0,sK0),sK0)
% 2.00/0.97      | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
% 2.00/0.97      | ~ r1_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,X0_46,sK5))
% 2.00/0.97      | r1_binop_1(sK0,sK2,X0_46)
% 2.00/0.97      | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
% 2.00/0.97      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
% 2.00/0.97      | ~ m1_subset_1(sK3,sK1)
% 2.00/0.97      | ~ m1_subset_1(sK2,sK0)
% 2.00/0.97      | ~ v1_funct_1(X0_46)
% 2.00/0.97      | ~ v1_funct_1(sK5)
% 2.00/0.97      | v1_xboole_0(sK1)
% 2.00/0.97      | v1_xboole_0(sK0) ),
% 2.00/0.97      inference(instantiation,[status(thm)],[c_1266]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_1479,plain,
% 2.00/0.97      ( v1_funct_2(X0_46,k2_zfmisc_1(sK0,sK0),sK0) != iProver_top
% 2.00/0.97      | v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1) != iProver_top
% 2.00/0.97      | r1_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,X0_46,sK5)) != iProver_top
% 2.00/0.97      | r1_binop_1(sK0,sK2,X0_46) = iProver_top
% 2.00/0.97      | m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) != iProver_top
% 2.00/0.97      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) != iProver_top
% 2.00/0.97      | m1_subset_1(sK3,sK1) != iProver_top
% 2.00/0.97      | m1_subset_1(sK2,sK0) != iProver_top
% 2.00/0.97      | v1_funct_1(X0_46) != iProver_top
% 2.00/0.97      | v1_funct_1(sK5) != iProver_top
% 2.00/0.97      | v1_xboole_0(sK1) = iProver_top
% 2.00/0.97      | v1_xboole_0(sK0) = iProver_top ),
% 2.00/0.97      inference(predicate_to_equality,[status(thm)],[c_1478]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_1481,plain,
% 2.00/0.97      ( v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1) != iProver_top
% 2.00/0.97      | v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0) != iProver_top
% 2.00/0.97      | r1_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5)) != iProver_top
% 2.00/0.97      | r1_binop_1(sK0,sK2,sK4) = iProver_top
% 2.00/0.97      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) != iProver_top
% 2.00/0.97      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) != iProver_top
% 2.00/0.97      | m1_subset_1(sK3,sK1) != iProver_top
% 2.00/0.97      | m1_subset_1(sK2,sK0) != iProver_top
% 2.00/0.97      | v1_funct_1(sK5) != iProver_top
% 2.00/0.97      | v1_funct_1(sK4) != iProver_top
% 2.00/0.97      | v1_xboole_0(sK1) = iProver_top
% 2.00/0.97      | v1_xboole_0(sK0) = iProver_top ),
% 2.00/0.97      inference(instantiation,[status(thm)],[c_1479]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_11,plain,
% 2.00/0.97      ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
% 2.00/0.97      | ~ v1_funct_2(X2,k2_zfmisc_1(X3,X3),X3)
% 2.00/0.97      | r2_binop_1(X3,X4,X2)
% 2.00/0.97      | ~ r2_binop_1(k2_zfmisc_1(X3,X1),k1_domain_1(X3,X1,X4,X5),k6_filter_1(X3,X1,X2,X0))
% 2.00/0.97      | ~ m1_subset_1(X5,X1)
% 2.00/0.97      | ~ m1_subset_1(X4,X3)
% 2.00/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
% 2.00/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X3,X3),X3)))
% 2.00/0.97      | ~ v1_funct_1(X0)
% 2.00/0.97      | ~ v1_funct_1(X2)
% 2.00/0.97      | v1_xboole_0(X3)
% 2.00/0.97      | v1_xboole_0(X1) ),
% 2.00/0.97      inference(cnf_transformation,[],[f46]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_272,plain,
% 2.00/0.97      ( ~ v1_funct_2(X0_46,k2_zfmisc_1(X0_45,X0_45),X0_45)
% 2.00/0.97      | ~ v1_funct_2(X1_46,k2_zfmisc_1(X1_45,X1_45),X1_45)
% 2.00/0.97      | r2_binop_1(X1_45,X2_46,X1_46)
% 2.00/0.97      | ~ r2_binop_1(k2_zfmisc_1(X1_45,X0_45),k1_domain_1(X1_45,X0_45,X2_46,X3_46),k6_filter_1(X1_45,X0_45,X1_46,X0_46))
% 2.00/0.97      | ~ m1_subset_1(X3_46,X0_45)
% 2.00/0.97      | ~ m1_subset_1(X2_46,X1_45)
% 2.00/0.97      | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0_45,X0_45),X0_45)))
% 2.00/0.97      | ~ m1_subset_1(X1_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1_45,X1_45),X1_45)))
% 2.00/0.97      | ~ v1_funct_1(X0_46)
% 2.00/0.97      | ~ v1_funct_1(X1_46)
% 2.00/0.97      | v1_xboole_0(X1_45)
% 2.00/0.97      | v1_xboole_0(X0_45) ),
% 2.00/0.97      inference(subtyping,[status(esa)],[c_11]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_520,plain,
% 2.00/0.97      ( ~ v1_funct_2(X0_46,k2_zfmisc_1(X0_45,X0_45),X0_45)
% 2.00/0.97      | ~ v1_funct_2(X1_46,k2_zfmisc_1(sK1,sK1),sK1)
% 2.00/0.97      | r2_binop_1(X0_45,X2_46,X0_46)
% 2.00/0.97      | ~ r2_binop_1(k2_zfmisc_1(X0_45,sK1),k1_domain_1(X0_45,sK1,X2_46,sK3),k6_filter_1(X0_45,sK1,X0_46,X1_46))
% 2.00/0.97      | ~ m1_subset_1(X2_46,X0_45)
% 2.00/0.97      | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0_45,X0_45),X0_45)))
% 2.00/0.97      | ~ m1_subset_1(X1_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
% 2.00/0.97      | ~ m1_subset_1(sK3,sK1)
% 2.00/0.97      | ~ v1_funct_1(X1_46)
% 2.00/0.97      | ~ v1_funct_1(X0_46)
% 2.00/0.97      | v1_xboole_0(X0_45)
% 2.00/0.97      | v1_xboole_0(sK1) ),
% 2.00/0.97      inference(instantiation,[status(thm)],[c_272]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_738,plain,
% 2.00/0.97      ( ~ v1_funct_2(X0_46,k2_zfmisc_1(X0_45,X0_45),X0_45)
% 2.00/0.97      | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
% 2.00/0.97      | r2_binop_1(X0_45,X1_46,X0_46)
% 2.00/0.97      | ~ r2_binop_1(k2_zfmisc_1(X0_45,sK1),k1_domain_1(X0_45,sK1,X1_46,sK3),k6_filter_1(X0_45,sK1,X0_46,sK5))
% 2.00/0.97      | ~ m1_subset_1(X1_46,X0_45)
% 2.00/0.97      | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0_45,X0_45),X0_45)))
% 2.00/0.97      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
% 2.00/0.97      | ~ m1_subset_1(sK3,sK1)
% 2.00/0.97      | ~ v1_funct_1(X0_46)
% 2.00/0.97      | ~ v1_funct_1(sK5)
% 2.00/0.97      | v1_xboole_0(X0_45)
% 2.00/0.97      | v1_xboole_0(sK1) ),
% 2.00/0.97      inference(instantiation,[status(thm)],[c_520]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_1376,plain,
% 2.00/0.97      ( ~ v1_funct_2(X0_46,k2_zfmisc_1(sK0,sK0),sK0)
% 2.00/0.97      | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
% 2.00/0.97      | ~ r2_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,X0_46,sK5))
% 2.00/0.97      | r2_binop_1(sK0,sK2,X0_46)
% 2.00/0.97      | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
% 2.00/0.97      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
% 2.00/0.97      | ~ m1_subset_1(sK3,sK1)
% 2.00/0.97      | ~ m1_subset_1(sK2,sK0)
% 2.00/0.97      | ~ v1_funct_1(X0_46)
% 2.00/0.97      | ~ v1_funct_1(sK5)
% 2.00/0.97      | v1_xboole_0(sK1)
% 2.00/0.97      | v1_xboole_0(sK0) ),
% 2.00/0.97      inference(instantiation,[status(thm)],[c_738]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_1377,plain,
% 2.00/0.97      ( v1_funct_2(X0_46,k2_zfmisc_1(sK0,sK0),sK0) != iProver_top
% 2.00/0.97      | v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1) != iProver_top
% 2.00/0.97      | r2_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,X0_46,sK5)) != iProver_top
% 2.00/0.97      | r2_binop_1(sK0,sK2,X0_46) = iProver_top
% 2.00/0.97      | m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) != iProver_top
% 2.00/0.97      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) != iProver_top
% 2.00/0.97      | m1_subset_1(sK3,sK1) != iProver_top
% 2.00/0.97      | m1_subset_1(sK2,sK0) != iProver_top
% 2.00/0.97      | v1_funct_1(X0_46) != iProver_top
% 2.00/0.97      | v1_funct_1(sK5) != iProver_top
% 2.00/0.97      | v1_xboole_0(sK1) = iProver_top
% 2.00/0.97      | v1_xboole_0(sK0) = iProver_top ),
% 2.00/0.97      inference(predicate_to_equality,[status(thm)],[c_1376]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_1379,plain,
% 2.00/0.97      ( v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1) != iProver_top
% 2.00/0.97      | v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0) != iProver_top
% 2.00/0.97      | r2_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5)) != iProver_top
% 2.00/0.97      | r2_binop_1(sK0,sK2,sK4) = iProver_top
% 2.00/0.97      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) != iProver_top
% 2.00/0.97      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) != iProver_top
% 2.00/0.97      | m1_subset_1(sK3,sK1) != iProver_top
% 2.00/0.97      | m1_subset_1(sK2,sK0) != iProver_top
% 2.00/0.97      | v1_funct_1(sK5) != iProver_top
% 2.00/0.97      | v1_funct_1(sK4) != iProver_top
% 2.00/0.97      | v1_xboole_0(sK1) = iProver_top
% 2.00/0.97      | v1_xboole_0(sK0) = iProver_top ),
% 2.00/0.97      inference(instantiation,[status(thm)],[c_1377]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_10,plain,
% 2.00/0.97      ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
% 2.00/0.97      | ~ v1_funct_2(X2,k2_zfmisc_1(X3,X3),X3)
% 2.00/0.97      | r2_binop_1(X1,X4,X0)
% 2.00/0.97      | ~ r2_binop_1(k2_zfmisc_1(X3,X1),k1_domain_1(X3,X1,X5,X4),k6_filter_1(X3,X1,X2,X0))
% 2.00/0.97      | ~ m1_subset_1(X4,X1)
% 2.00/0.97      | ~ m1_subset_1(X5,X3)
% 2.00/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
% 2.00/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X3,X3),X3)))
% 2.00/0.97      | ~ v1_funct_1(X0)
% 2.00/0.97      | ~ v1_funct_1(X2)
% 2.00/0.97      | v1_xboole_0(X3)
% 2.00/0.97      | v1_xboole_0(X1) ),
% 2.00/0.97      inference(cnf_transformation,[],[f47]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_273,plain,
% 2.00/0.97      ( ~ v1_funct_2(X0_46,k2_zfmisc_1(X0_45,X0_45),X0_45)
% 2.00/0.97      | ~ v1_funct_2(X1_46,k2_zfmisc_1(X1_45,X1_45),X1_45)
% 2.00/0.97      | r2_binop_1(X0_45,X2_46,X0_46)
% 2.00/0.97      | ~ r2_binop_1(k2_zfmisc_1(X1_45,X0_45),k1_domain_1(X1_45,X0_45,X3_46,X2_46),k6_filter_1(X1_45,X0_45,X1_46,X0_46))
% 2.00/0.97      | ~ m1_subset_1(X2_46,X0_45)
% 2.00/0.97      | ~ m1_subset_1(X3_46,X1_45)
% 2.00/0.97      | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0_45,X0_45),X0_45)))
% 2.00/0.97      | ~ m1_subset_1(X1_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1_45,X1_45),X1_45)))
% 2.00/0.97      | ~ v1_funct_1(X0_46)
% 2.00/0.97      | ~ v1_funct_1(X1_46)
% 2.00/0.97      | v1_xboole_0(X1_45)
% 2.00/0.97      | v1_xboole_0(X0_45) ),
% 2.00/0.97      inference(subtyping,[status(esa)],[c_10]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_545,plain,
% 2.00/0.97      ( ~ v1_funct_2(X0_46,k2_zfmisc_1(X0_45,X0_45),X0_45)
% 2.00/0.97      | ~ v1_funct_2(X1_46,k2_zfmisc_1(sK1,sK1),sK1)
% 2.00/0.97      | ~ r2_binop_1(k2_zfmisc_1(X0_45,sK1),k1_domain_1(X0_45,sK1,X2_46,sK3),k6_filter_1(X0_45,sK1,X0_46,X1_46))
% 2.00/0.97      | r2_binop_1(sK1,sK3,X1_46)
% 2.00/0.97      | ~ m1_subset_1(X2_46,X0_45)
% 2.00/0.97      | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0_45,X0_45),X0_45)))
% 2.00/0.97      | ~ m1_subset_1(X1_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
% 2.00/0.97      | ~ m1_subset_1(sK3,sK1)
% 2.00/0.97      | ~ v1_funct_1(X1_46)
% 2.00/0.97      | ~ v1_funct_1(X0_46)
% 2.00/0.97      | v1_xboole_0(X0_45)
% 2.00/0.97      | v1_xboole_0(sK1) ),
% 2.00/0.97      inference(instantiation,[status(thm)],[c_273]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_708,plain,
% 2.00/0.97      ( ~ v1_funct_2(X0_46,k2_zfmisc_1(X0_45,X0_45),X0_45)
% 2.00/0.97      | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
% 2.00/0.97      | ~ r2_binop_1(k2_zfmisc_1(X0_45,sK1),k1_domain_1(X0_45,sK1,X1_46,sK3),k6_filter_1(X0_45,sK1,X0_46,sK5))
% 2.00/0.97      | r2_binop_1(sK1,sK3,sK5)
% 2.00/0.97      | ~ m1_subset_1(X1_46,X0_45)
% 2.00/0.97      | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0_45,X0_45),X0_45)))
% 2.00/0.97      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
% 2.00/0.97      | ~ m1_subset_1(sK3,sK1)
% 2.00/0.97      | ~ v1_funct_1(X0_46)
% 2.00/0.97      | ~ v1_funct_1(sK5)
% 2.00/0.97      | v1_xboole_0(X0_45)
% 2.00/0.97      | v1_xboole_0(sK1) ),
% 2.00/0.97      inference(instantiation,[status(thm)],[c_545]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_1331,plain,
% 2.00/0.97      ( ~ v1_funct_2(X0_46,k2_zfmisc_1(sK0,sK0),sK0)
% 2.00/0.97      | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
% 2.00/0.97      | ~ r2_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,X0_46,sK5))
% 2.00/0.97      | r2_binop_1(sK1,sK3,sK5)
% 2.00/0.97      | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
% 2.00/0.97      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
% 2.00/0.97      | ~ m1_subset_1(sK3,sK1)
% 2.00/0.97      | ~ m1_subset_1(sK2,sK0)
% 2.00/0.97      | ~ v1_funct_1(X0_46)
% 2.00/0.97      | ~ v1_funct_1(sK5)
% 2.00/0.97      | v1_xboole_0(sK1)
% 2.00/0.97      | v1_xboole_0(sK0) ),
% 2.00/0.97      inference(instantiation,[status(thm)],[c_708]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_1332,plain,
% 2.00/0.97      ( v1_funct_2(X0_46,k2_zfmisc_1(sK0,sK0),sK0) != iProver_top
% 2.00/0.97      | v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1) != iProver_top
% 2.00/0.97      | r2_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,X0_46,sK5)) != iProver_top
% 2.00/0.97      | r2_binop_1(sK1,sK3,sK5) = iProver_top
% 2.00/0.97      | m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) != iProver_top
% 2.00/0.97      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) != iProver_top
% 2.00/0.97      | m1_subset_1(sK3,sK1) != iProver_top
% 2.00/0.97      | m1_subset_1(sK2,sK0) != iProver_top
% 2.00/0.97      | v1_funct_1(X0_46) != iProver_top
% 2.00/0.97      | v1_funct_1(sK5) != iProver_top
% 2.00/0.97      | v1_xboole_0(sK1) = iProver_top
% 2.00/0.97      | v1_xboole_0(sK0) = iProver_top ),
% 2.00/0.97      inference(predicate_to_equality,[status(thm)],[c_1331]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_1334,plain,
% 2.00/0.97      ( v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1) != iProver_top
% 2.00/0.97      | v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0) != iProver_top
% 2.00/0.97      | r2_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5)) != iProver_top
% 2.00/0.97      | r2_binop_1(sK1,sK3,sK5) = iProver_top
% 2.00/0.97      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) != iProver_top
% 2.00/0.97      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) != iProver_top
% 2.00/0.97      | m1_subset_1(sK3,sK1) != iProver_top
% 2.00/0.97      | m1_subset_1(sK2,sK0) != iProver_top
% 2.00/0.97      | v1_funct_1(sK5) != iProver_top
% 2.00/0.97      | v1_funct_1(sK4) != iProver_top
% 2.00/0.97      | v1_xboole_0(sK1) = iProver_top
% 2.00/0.97      | v1_xboole_0(sK0) = iProver_top ),
% 2.00/0.97      inference(instantiation,[status(thm)],[c_1332]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_0,plain,
% 2.00/0.97      ( ~ m1_subset_1(X0,X1)
% 2.00/0.97      | ~ m1_subset_1(X2,X3)
% 2.00/0.97      | m1_subset_1(k1_domain_1(X3,X1,X2,X0),k2_zfmisc_1(X3,X1))
% 2.00/0.97      | v1_xboole_0(X3)
% 2.00/0.97      | v1_xboole_0(X1) ),
% 2.00/0.97      inference(cnf_transformation,[],[f35]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_283,plain,
% 2.00/0.97      ( ~ m1_subset_1(X0_46,X0_45)
% 2.00/0.97      | ~ m1_subset_1(X1_46,X1_45)
% 2.00/0.97      | m1_subset_1(k1_domain_1(X1_45,X0_45,X1_46,X0_46),k2_zfmisc_1(X1_45,X0_45))
% 2.00/0.97      | v1_xboole_0(X1_45)
% 2.00/0.97      | v1_xboole_0(X0_45) ),
% 2.00/0.97      inference(subtyping,[status(esa)],[c_0]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_420,plain,
% 2.00/0.97      ( ~ m1_subset_1(X0_46,X0_45)
% 2.00/0.97      | m1_subset_1(k1_domain_1(X0_45,sK1,X0_46,sK3),k2_zfmisc_1(X0_45,sK1))
% 2.00/0.97      | ~ m1_subset_1(sK3,sK1)
% 2.00/0.97      | v1_xboole_0(X0_45)
% 2.00/0.97      | v1_xboole_0(sK1) ),
% 2.00/0.97      inference(instantiation,[status(thm)],[c_283]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_683,plain,
% 2.00/0.97      ( m1_subset_1(k1_domain_1(sK0,sK1,sK2,sK3),k2_zfmisc_1(sK0,sK1))
% 2.00/0.97      | ~ m1_subset_1(sK3,sK1)
% 2.00/0.97      | ~ m1_subset_1(sK2,sK0)
% 2.00/0.97      | v1_xboole_0(sK1)
% 2.00/0.97      | v1_xboole_0(sK0) ),
% 2.00/0.97      inference(instantiation,[status(thm)],[c_420]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_684,plain,
% 2.00/0.97      ( m1_subset_1(k1_domain_1(sK0,sK1,sK2,sK3),k2_zfmisc_1(sK0,sK1)) = iProver_top
% 2.00/0.97      | m1_subset_1(sK3,sK1) != iProver_top
% 2.00/0.97      | m1_subset_1(sK2,sK0) != iProver_top
% 2.00/0.97      | v1_xboole_0(sK1) = iProver_top
% 2.00/0.97      | v1_xboole_0(sK0) = iProver_top ),
% 2.00/0.97      inference(predicate_to_equality,[status(thm)],[c_683]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_485,plain,
% 2.00/0.97      ( ~ v1_funct_2(X0_46,k2_zfmisc_1(sK0,sK0),sK0)
% 2.00/0.97      | ~ r1_binop_1(sK0,sK2,X0_46)
% 2.00/0.97      | ~ r2_binop_1(sK0,sK2,X0_46)
% 2.00/0.97      | r3_binop_1(sK0,sK2,X0_46)
% 2.00/0.97      | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
% 2.00/0.97      | ~ m1_subset_1(sK2,sK0)
% 2.00/0.97      | ~ v1_funct_1(X0_46) ),
% 2.00/0.97      inference(instantiation,[status(thm)],[c_282]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_486,plain,
% 2.00/0.97      ( v1_funct_2(X0_46,k2_zfmisc_1(sK0,sK0),sK0) != iProver_top
% 2.00/0.97      | r1_binop_1(sK0,sK2,X0_46) != iProver_top
% 2.00/0.97      | r2_binop_1(sK0,sK2,X0_46) != iProver_top
% 2.00/0.97      | r3_binop_1(sK0,sK2,X0_46) = iProver_top
% 2.00/0.97      | m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) != iProver_top
% 2.00/0.97      | m1_subset_1(sK2,sK0) != iProver_top
% 2.00/0.97      | v1_funct_1(X0_46) != iProver_top ),
% 2.00/0.97      inference(predicate_to_equality,[status(thm)],[c_485]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_488,plain,
% 2.00/0.97      ( v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0) != iProver_top
% 2.00/0.97      | r1_binop_1(sK0,sK2,sK4) != iProver_top
% 2.00/0.97      | r2_binop_1(sK0,sK2,sK4) != iProver_top
% 2.00/0.97      | r3_binop_1(sK0,sK2,sK4) = iProver_top
% 2.00/0.97      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) != iProver_top
% 2.00/0.97      | m1_subset_1(sK2,sK0) != iProver_top
% 2.00/0.97      | v1_funct_1(sK4) != iProver_top ),
% 2.00/0.97      inference(instantiation,[status(thm)],[c_486]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_465,plain,
% 2.00/0.97      ( ~ v1_funct_2(X0_46,k2_zfmisc_1(sK0,sK0),sK0)
% 2.00/0.97      | r2_binop_1(sK0,sK2,X0_46)
% 2.00/0.97      | ~ r3_binop_1(sK0,sK2,X0_46)
% 2.00/0.97      | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
% 2.00/0.97      | ~ m1_subset_1(sK2,sK0)
% 2.00/0.97      | ~ v1_funct_1(X0_46) ),
% 2.00/0.97      inference(instantiation,[status(thm)],[c_281]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_466,plain,
% 2.00/0.97      ( v1_funct_2(X0_46,k2_zfmisc_1(sK0,sK0),sK0) != iProver_top
% 2.00/0.97      | r2_binop_1(sK0,sK2,X0_46) = iProver_top
% 2.00/0.97      | r3_binop_1(sK0,sK2,X0_46) != iProver_top
% 2.00/0.97      | m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) != iProver_top
% 2.00/0.97      | m1_subset_1(sK2,sK0) != iProver_top
% 2.00/0.97      | v1_funct_1(X0_46) != iProver_top ),
% 2.00/0.97      inference(predicate_to_equality,[status(thm)],[c_465]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_468,plain,
% 2.00/0.97      ( v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0) != iProver_top
% 2.00/0.97      | r2_binop_1(sK0,sK2,sK4) = iProver_top
% 2.00/0.97      | r3_binop_1(sK0,sK2,sK4) != iProver_top
% 2.00/0.97      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) != iProver_top
% 2.00/0.97      | m1_subset_1(sK2,sK0) != iProver_top
% 2.00/0.97      | v1_funct_1(sK4) != iProver_top ),
% 2.00/0.97      inference(instantiation,[status(thm)],[c_466]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_445,plain,
% 2.00/0.97      ( ~ v1_funct_2(X0_46,k2_zfmisc_1(sK0,sK0),sK0)
% 2.00/0.97      | r1_binop_1(sK0,sK2,X0_46)
% 2.00/0.97      | ~ r3_binop_1(sK0,sK2,X0_46)
% 2.00/0.97      | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
% 2.00/0.97      | ~ m1_subset_1(sK2,sK0)
% 2.00/0.97      | ~ v1_funct_1(X0_46) ),
% 2.00/0.97      inference(instantiation,[status(thm)],[c_280]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_446,plain,
% 2.00/0.97      ( v1_funct_2(X0_46,k2_zfmisc_1(sK0,sK0),sK0) != iProver_top
% 2.00/0.97      | r1_binop_1(sK0,sK2,X0_46) = iProver_top
% 2.00/0.97      | r3_binop_1(sK0,sK2,X0_46) != iProver_top
% 2.00/0.97      | m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) != iProver_top
% 2.00/0.97      | m1_subset_1(sK2,sK0) != iProver_top
% 2.00/0.97      | v1_funct_1(X0_46) != iProver_top ),
% 2.00/0.97      inference(predicate_to_equality,[status(thm)],[c_445]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_448,plain,
% 2.00/0.97      ( v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0) != iProver_top
% 2.00/0.97      | r1_binop_1(sK0,sK2,sK4) = iProver_top
% 2.00/0.97      | r3_binop_1(sK0,sK2,sK4) != iProver_top
% 2.00/0.97      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) != iProver_top
% 2.00/0.97      | m1_subset_1(sK2,sK0) != iProver_top
% 2.00/0.97      | v1_funct_1(sK4) != iProver_top ),
% 2.00/0.97      inference(instantiation,[status(thm)],[c_446]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_13,negated_conjecture,
% 2.00/0.97      ( ~ r3_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5))
% 2.00/0.97      | ~ r3_binop_1(sK1,sK3,sK5)
% 2.00/0.97      | ~ r3_binop_1(sK0,sK2,sK4) ),
% 2.00/0.97      inference(cnf_transformation,[],[f60]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_38,plain,
% 2.00/0.97      ( r3_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5)) != iProver_top
% 2.00/0.97      | r3_binop_1(sK1,sK3,sK5) != iProver_top
% 2.00/0.97      | r3_binop_1(sK0,sK2,sK4) != iProver_top ),
% 2.00/0.97      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_14,negated_conjecture,
% 2.00/0.97      ( r3_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5))
% 2.00/0.97      | r3_binop_1(sK1,sK3,sK5) ),
% 2.00/0.97      inference(cnf_transformation,[],[f59]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_37,plain,
% 2.00/0.97      ( r3_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5)) = iProver_top
% 2.00/0.97      | r3_binop_1(sK1,sK3,sK5) = iProver_top ),
% 2.00/0.97      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_15,negated_conjecture,
% 2.00/0.97      ( r3_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5))
% 2.00/0.97      | r3_binop_1(sK0,sK2,sK4) ),
% 2.00/0.97      inference(cnf_transformation,[],[f58]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_36,plain,
% 2.00/0.97      ( r3_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5)) = iProver_top
% 2.00/0.97      | r3_binop_1(sK0,sK2,sK4) = iProver_top ),
% 2.00/0.97      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_16,negated_conjecture,
% 2.00/0.97      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) ),
% 2.00/0.97      inference(cnf_transformation,[],[f57]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_35,plain,
% 2.00/0.97      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) = iProver_top ),
% 2.00/0.97      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_17,negated_conjecture,
% 2.00/0.97      ( v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1) ),
% 2.00/0.97      inference(cnf_transformation,[],[f56]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_34,plain,
% 2.00/0.97      ( v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1) = iProver_top ),
% 2.00/0.97      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_18,negated_conjecture,
% 2.00/0.97      ( v1_funct_1(sK5) ),
% 2.00/0.97      inference(cnf_transformation,[],[f55]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_33,plain,
% 2.00/0.97      ( v1_funct_1(sK5) = iProver_top ),
% 2.00/0.97      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_19,negated_conjecture,
% 2.00/0.97      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) ),
% 2.00/0.97      inference(cnf_transformation,[],[f54]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_32,plain,
% 2.00/0.97      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) = iProver_top ),
% 2.00/0.97      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_20,negated_conjecture,
% 2.00/0.97      ( v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0) ),
% 2.00/0.97      inference(cnf_transformation,[],[f53]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_31,plain,
% 2.00/0.97      ( v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0) = iProver_top ),
% 2.00/0.97      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_21,negated_conjecture,
% 2.00/0.97      ( v1_funct_1(sK4) ),
% 2.00/0.97      inference(cnf_transformation,[],[f52]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_30,plain,
% 2.00/0.97      ( v1_funct_1(sK4) = iProver_top ),
% 2.00/0.97      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_22,negated_conjecture,
% 2.00/0.97      ( m1_subset_1(sK3,sK1) ),
% 2.00/0.97      inference(cnf_transformation,[],[f51]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_29,plain,
% 2.00/0.97      ( m1_subset_1(sK3,sK1) = iProver_top ),
% 2.00/0.97      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_23,negated_conjecture,
% 2.00/0.97      ( m1_subset_1(sK2,sK0) ),
% 2.00/0.97      inference(cnf_transformation,[],[f50]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_28,plain,
% 2.00/0.97      ( m1_subset_1(sK2,sK0) = iProver_top ),
% 2.00/0.97      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_24,negated_conjecture,
% 2.00/0.97      ( ~ v1_xboole_0(sK1) ),
% 2.00/0.97      inference(cnf_transformation,[],[f49]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_27,plain,
% 2.00/0.97      ( v1_xboole_0(sK1) != iProver_top ),
% 2.00/0.97      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_25,negated_conjecture,
% 2.00/0.97      ( ~ v1_xboole_0(sK0) ),
% 2.00/0.97      inference(cnf_transformation,[],[f48]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(c_26,plain,
% 2.00/0.97      ( v1_xboole_0(sK0) != iProver_top ),
% 2.00/0.97      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.00/0.97  
% 2.00/0.97  cnf(contradiction,plain,
% 2.00/0.97      ( $false ),
% 2.00/0.97      inference(minisat,
% 2.00/0.97                [status(thm)],
% 2.00/0.97                [c_1810,c_1764,c_1742,c_1740,c_1624,c_1616,c_1588,c_1584,
% 2.00/0.97                 c_1580,c_1576,c_1573,c_1545,c_1481,c_1379,c_1334,c_684,
% 2.00/0.97                 c_488,c_468,c_448,c_38,c_37,c_36,c_35,c_34,c_33,c_32,
% 2.00/0.97                 c_31,c_30,c_29,c_28,c_27,c_26]) ).
% 2.00/0.97  
% 2.00/0.97  
% 2.00/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 2.00/0.97  
% 2.00/0.97  ------                               Statistics
% 2.00/0.97  
% 2.00/0.97  ------ General
% 2.00/0.97  
% 2.00/0.97  abstr_ref_over_cycles:                  0
% 2.00/0.97  abstr_ref_under_cycles:                 0
% 2.00/0.97  gc_basic_clause_elim:                   0
% 2.00/0.97  forced_gc_time:                         0
% 2.00/0.97  parsing_time:                           0.008
% 2.00/0.97  unif_index_cands_time:                  0.
% 2.00/0.97  unif_index_add_time:                    0.
% 2.00/0.97  orderings_time:                         0.
% 2.00/0.97  out_proof_time:                         0.015
% 2.00/0.97  total_time:                             0.158
% 2.00/0.97  num_of_symbols:                         50
% 2.00/0.97  num_of_terms:                           2591
% 2.00/0.97  
% 2.00/0.97  ------ Preprocessing
% 2.00/0.97  
% 2.00/0.97  num_of_splits:                          0
% 2.00/0.97  num_of_split_atoms:                     0
% 2.00/0.97  num_of_reused_defs:                     0
% 2.00/0.97  num_eq_ax_congr_red:                    0
% 2.00/0.97  num_of_sem_filtered_clauses:            0
% 2.00/0.97  num_of_subtypes:                        2
% 2.00/0.97  monotx_restored_types:                  0
% 2.00/0.97  sat_num_of_epr_types:                   0
% 2.00/0.97  sat_num_of_non_cyclic_types:            0
% 2.00/0.97  sat_guarded_non_collapsed_types:        0
% 2.00/0.97  num_pure_diseq_elim:                    0
% 2.00/0.97  simp_replaced_by:                       0
% 2.00/0.97  res_preprocessed:                       26
% 2.00/0.97  prep_upred:                             0
% 2.00/0.97  prep_unflattend:                        0
% 2.00/0.97  smt_new_axioms:                         0
% 2.00/0.97  pred_elim_cands:                        7
% 2.00/0.97  pred_elim:                              0
% 2.00/0.97  pred_elim_cl:                           0
% 2.00/0.97  pred_elim_cycles:                       1
% 2.00/0.97  merged_defs:                            0
% 2.00/0.97  merged_defs_ncl:                        0
% 2.00/0.97  bin_hyper_res:                          0
% 2.00/0.97  prep_cycles:                            1
% 2.00/0.97  pred_elim_time:                         0.
% 2.00/0.97  splitting_time:                         0.
% 2.00/0.97  sem_filter_time:                        0.
% 2.00/0.97  monotx_time:                            0.
% 2.00/0.97  subtype_inf_time:                       0.
% 2.00/0.97  
% 2.00/0.97  ------ Problem properties
% 2.00/0.97  
% 2.00/0.97  clauses:                                26
% 2.00/0.97  conjectures:                            13
% 2.00/0.97  epr:                                    6
% 2.00/0.97  horn:                                   17
% 2.00/0.97  ground:                                 13
% 2.00/0.97  unary:                                  10
% 2.00/0.97  binary:                                 2
% 2.00/0.97  lits:                                   136
% 2.00/0.97  lits_eq:                                0
% 2.00/0.97  fd_pure:                                0
% 2.00/0.97  fd_pseudo:                              0
% 2.00/0.97  fd_cond:                                0
% 2.00/0.97  fd_pseudo_cond:                         0
% 2.00/0.97  ac_symbols:                             0
% 2.00/0.97  
% 2.00/0.97  ------ Propositional Solver
% 2.00/0.97  
% 2.00/0.97  prop_solver_calls:                      18
% 2.00/0.97  prop_fast_solver_calls:                 272
% 2.00/0.97  smt_solver_calls:                       0
% 2.00/0.97  smt_fast_solver_calls:                  0
% 2.00/0.97  prop_num_of_clauses:                    1140
% 2.00/0.97  prop_preprocess_simplified:             2222
% 2.00/0.97  prop_fo_subsumed:                       0
% 2.00/0.97  prop_solver_time:                       0.
% 2.00/0.97  smt_solver_time:                        0.
% 2.00/0.97  smt_fast_solver_time:                   0.
% 2.00/0.97  prop_fast_solver_time:                  0.
% 2.00/0.97  prop_unsat_core_time:                   0.
% 2.00/0.97  
% 2.00/0.97  ------ QBF
% 2.00/0.97  
% 2.00/0.97  qbf_q_res:                              0
% 2.00/0.97  qbf_num_tautologies:                    0
% 2.00/0.97  qbf_prep_cycles:                        0
% 2.00/0.97  
% 2.00/0.97  ------ BMC1
% 2.00/0.97  
% 2.00/0.97  bmc1_current_bound:                     -1
% 2.00/0.97  bmc1_last_solved_bound:                 -1
% 2.00/0.97  bmc1_unsat_core_size:                   -1
% 2.00/0.97  bmc1_unsat_core_parents_size:           -1
% 2.00/0.97  bmc1_merge_next_fun:                    0
% 2.00/0.97  bmc1_unsat_core_clauses_time:           0.
% 2.00/0.97  
% 2.00/0.97  ------ Instantiation
% 2.00/0.97  
% 2.00/0.97  inst_num_of_clauses:                    304
% 2.00/0.97  inst_num_in_passive:                    13
% 2.00/0.97  inst_num_in_active:                     288
% 2.00/0.97  inst_num_in_unprocessed:                2
% 2.00/0.97  inst_num_of_loops:                      319
% 2.00/0.97  inst_num_of_learning_restarts:          0
% 2.00/0.97  inst_num_moves_active_passive:          23
% 2.00/0.97  inst_lit_activity:                      0
% 2.00/0.97  inst_lit_activity_moves:                0
% 2.00/0.97  inst_num_tautologies:                   0
% 2.00/0.97  inst_num_prop_implied:                  0
% 2.00/0.97  inst_num_existing_simplified:           0
% 2.00/0.97  inst_num_eq_res_simplified:             0
% 2.00/0.97  inst_num_child_elim:                    0
% 2.00/0.97  inst_num_of_dismatching_blockings:      28
% 2.00/0.97  inst_num_of_non_proper_insts:           231
% 2.00/0.97  inst_num_of_duplicates:                 0
% 2.00/0.97  inst_inst_num_from_inst_to_res:         0
% 2.00/0.97  inst_dismatching_checking_time:         0.
% 2.00/0.97  
% 2.00/0.97  ------ Resolution
% 2.00/0.97  
% 2.00/0.97  res_num_of_clauses:                     0
% 2.00/0.97  res_num_in_passive:                     0
% 2.00/0.97  res_num_in_active:                      0
% 2.00/0.97  res_num_of_loops:                       27
% 2.00/0.97  res_forward_subset_subsumed:            0
% 2.00/0.97  res_backward_subset_subsumed:           0
% 2.00/0.97  res_forward_subsumed:                   0
% 2.00/0.97  res_backward_subsumed:                  0
% 2.00/0.97  res_forward_subsumption_resolution:     0
% 2.00/0.97  res_backward_subsumption_resolution:    0
% 2.00/0.97  res_clause_to_clause_subsumption:       0
% 2.00/0.97  res_orphan_elimination:                 0
% 2.00/0.97  res_tautology_del:                      0
% 2.00/0.97  res_num_eq_res_simplified:              0
% 2.00/0.97  res_num_sel_changes:                    0
% 2.00/0.97  res_moves_from_active_to_pass:          0
% 2.00/0.97  
% 2.00/0.97  ------ Superposition
% 2.00/0.97  
% 2.00/0.97  sup_time_total:                         0.
% 2.00/0.97  sup_time_generating:                    0.
% 2.00/0.97  sup_time_sim_full:                      0.
% 2.00/0.97  sup_time_sim_immed:                     0.
% 2.00/0.97  
% 2.00/0.97  sup_num_of_clauses:                     0
% 2.00/0.97  sup_num_in_active:                      0
% 2.00/0.97  sup_num_in_passive:                     0
% 2.00/0.97  sup_num_of_loops:                       0
% 2.00/0.97  sup_fw_superposition:                   0
% 2.00/0.97  sup_bw_superposition:                   0
% 2.00/0.97  sup_immediate_simplified:               0
% 2.00/0.97  sup_given_eliminated:                   0
% 2.00/0.97  comparisons_done:                       0
% 2.00/0.97  comparisons_avoided:                    0
% 2.00/0.97  
% 2.00/0.97  ------ Simplifications
% 2.00/0.97  
% 2.00/0.97  
% 2.00/0.97  sim_fw_subset_subsumed:                 0
% 2.00/0.97  sim_bw_subset_subsumed:                 0
% 2.00/0.97  sim_fw_subsumed:                        0
% 2.00/0.97  sim_bw_subsumed:                        0
% 2.00/0.97  sim_fw_subsumption_res:                 0
% 2.00/0.97  sim_bw_subsumption_res:                 0
% 2.00/0.97  sim_tautology_del:                      0
% 2.00/0.97  sim_eq_tautology_del:                   0
% 2.00/0.97  sim_eq_res_simp:                        0
% 2.00/0.97  sim_fw_demodulated:                     0
% 2.00/0.97  sim_bw_demodulated:                     0
% 2.00/0.97  sim_light_normalised:                   0
% 2.00/0.97  sim_joinable_taut:                      0
% 2.00/0.97  sim_joinable_simp:                      0
% 2.00/0.97  sim_ac_normalised:                      0
% 2.00/0.97  sim_smt_subsumption:                    0
% 2.00/0.97  
%------------------------------------------------------------------------------
