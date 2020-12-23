%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1166+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:01 EST 2020

% Result     : Theorem 47.36s
% Output     : CNFRefutation 47.36s
% Verified   : 
% Statistics : Number of formulae       :  163 (1044 expanded)
%              Number of clauses        :   86 ( 208 expanded)
%              Number of leaves         :   17 ( 344 expanded)
%              Depth                    :   31
%              Number of atoms          :  899 (7645 expanded)
%              Number of equality atoms :  354 (1523 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal clause size      :   21 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1868,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( k1_xboole_0 = X1
                 => ( m1_orders_2(X2,X0,X1)
                  <=> k1_xboole_0 = X2 ) )
                & ( k1_xboole_0 != X1
                 => ( m1_orders_2(X2,X0,X1)
                  <=> ? [X3] :
                        ( k3_orders_2(X0,X1,X3) = X2
                        & r2_hidden(X3,X1)
                        & m1_subset_1(X3,u1_struct_0(X0)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4086,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_orders_2(X2,X0,X1)
                  <=> k1_xboole_0 = X2 )
                  | k1_xboole_0 != X1 )
                & ( ( m1_orders_2(X2,X0,X1)
                  <=> ? [X3] :
                        ( k3_orders_2(X0,X1,X3) = X2
                        & r2_hidden(X3,X1)
                        & m1_subset_1(X3,u1_struct_0(X0)) ) )
                  | k1_xboole_0 = X1 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1868])).

fof(f4087,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_orders_2(X2,X0,X1)
                  <=> k1_xboole_0 = X2 )
                  | k1_xboole_0 != X1 )
                & ( ( m1_orders_2(X2,X0,X1)
                  <=> ? [X3] :
                        ( k3_orders_2(X0,X1,X3) = X2
                        & r2_hidden(X3,X1)
                        & m1_subset_1(X3,u1_struct_0(X0)) ) )
                  | k1_xboole_0 = X1 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f4086])).

fof(f5858,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( ( m1_orders_2(X2,X0,X1)
                      | k1_xboole_0 != X2 )
                    & ( k1_xboole_0 = X2
                      | ~ m1_orders_2(X2,X0,X1) ) )
                  | k1_xboole_0 != X1 )
                & ( ( ( m1_orders_2(X2,X0,X1)
                      | ! [X3] :
                          ( k3_orders_2(X0,X1,X3) != X2
                          | ~ r2_hidden(X3,X1)
                          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
                    & ( ? [X3] :
                          ( k3_orders_2(X0,X1,X3) = X2
                          & r2_hidden(X3,X1)
                          & m1_subset_1(X3,u1_struct_0(X0)) )
                      | ~ m1_orders_2(X2,X0,X1) ) )
                  | k1_xboole_0 = X1 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f4087])).

fof(f5859,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( ( m1_orders_2(X2,X0,X1)
                      | k1_xboole_0 != X2 )
                    & ( k1_xboole_0 = X2
                      | ~ m1_orders_2(X2,X0,X1) ) )
                  | k1_xboole_0 != X1 )
                & ( ( ( m1_orders_2(X2,X0,X1)
                      | ! [X3] :
                          ( k3_orders_2(X0,X1,X3) != X2
                          | ~ r2_hidden(X3,X1)
                          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
                    & ( ? [X4] :
                          ( k3_orders_2(X0,X1,X4) = X2
                          & r2_hidden(X4,X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ m1_orders_2(X2,X0,X1) ) )
                  | k1_xboole_0 = X1 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f5858])).

fof(f5860,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k3_orders_2(X0,X1,X4) = X2
          & r2_hidden(X4,X1)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( k3_orders_2(X0,X1,sK691(X0,X1,X2)) = X2
        & r2_hidden(sK691(X0,X1,X2),X1)
        & m1_subset_1(sK691(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f5861,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( ( m1_orders_2(X2,X0,X1)
                      | k1_xboole_0 != X2 )
                    & ( k1_xboole_0 = X2
                      | ~ m1_orders_2(X2,X0,X1) ) )
                  | k1_xboole_0 != X1 )
                & ( ( ( m1_orders_2(X2,X0,X1)
                      | ! [X3] :
                          ( k3_orders_2(X0,X1,X3) != X2
                          | ~ r2_hidden(X3,X1)
                          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
                    & ( ( k3_orders_2(X0,X1,sK691(X0,X1,X2)) = X2
                        & r2_hidden(sK691(X0,X1,X2),X1)
                        & m1_subset_1(sK691(X0,X1,X2),u1_struct_0(X0)) )
                      | ~ m1_orders_2(X2,X0,X1) ) )
                  | k1_xboole_0 = X1 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK691])],[f5859,f5860])).

fof(f9573,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK691(X0,X1,X2),X1)
      | ~ m1_orders_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f5861])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5917,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f1559,axiom,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8858,plain,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    inference(cnf_transformation,[],[f1559])).

fof(f11556,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK691(X0,X1,X2),X1)
      | ~ m1_orders_2(X2,X0,X1)
      | o_0_0_xboole_0 = X1
      | ~ m1_subset_1(X2,k9_setfam_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f9573,f5917,f8858,f8858])).

fof(f1881,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_orders_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4106,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_orders_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1881])).

fof(f4107,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_orders_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f4106])).

fof(f9598,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_orders_2(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4107])).

fof(f11563,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k9_setfam_1(u1_struct_0(X0)))
      | ~ m1_orders_2(X2,X0,X1)
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f9598,f8858,f8858])).

fof(f9572,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK691(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_orders_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f5861])).

fof(f11557,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK691(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_orders_2(X2,X0,X1)
      | o_0_0_xboole_0 = X1
      | ~ m1_subset_1(X2,k9_setfam_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f9572,f5917,f8858,f8858])).

fof(f1926,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ~ ( m1_orders_2(X2,X0,X1)
                  & m1_orders_2(X1,X0,X2)
                  & k1_xboole_0 != X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1927,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ~ ( m1_orders_2(X2,X0,X1)
                    & m1_orders_2(X1,X0,X2)
                    & k1_xboole_0 != X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f1926])).

fof(f4192,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( m1_orders_2(X2,X0,X1)
              & m1_orders_2(X1,X0,X2)
              & k1_xboole_0 != X1
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1927])).

fof(f4193,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( m1_orders_2(X2,X0,X1)
              & m1_orders_2(X1,X0,X2)
              & k1_xboole_0 != X1
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f4192])).

fof(f5906,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( m1_orders_2(X2,X0,X1)
          & m1_orders_2(X1,X0,X2)
          & k1_xboole_0 != X1
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( m1_orders_2(sK705,X0,X1)
        & m1_orders_2(X1,X0,sK705)
        & k1_xboole_0 != X1
        & m1_subset_1(sK705,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f5905,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( m1_orders_2(X2,X0,X1)
              & m1_orders_2(X1,X0,X2)
              & k1_xboole_0 != X1
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( m1_orders_2(X2,X0,sK704)
            & m1_orders_2(sK704,X0,X2)
            & k1_xboole_0 != sK704
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK704,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f5904,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( m1_orders_2(X2,X0,X1)
                & m1_orders_2(X1,X0,X2)
                & k1_xboole_0 != X1
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( m1_orders_2(X2,sK703,X1)
              & m1_orders_2(X1,sK703,X2)
              & k1_xboole_0 != X1
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK703))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK703))) )
      & l1_orders_2(sK703)
      & v5_orders_2(sK703)
      & v4_orders_2(sK703)
      & v3_orders_2(sK703)
      & ~ v2_struct_0(sK703) ) ),
    introduced(choice_axiom,[])).

fof(f5907,plain,
    ( m1_orders_2(sK705,sK703,sK704)
    & m1_orders_2(sK704,sK703,sK705)
    & k1_xboole_0 != sK704
    & m1_subset_1(sK705,k1_zfmisc_1(u1_struct_0(sK703)))
    & m1_subset_1(sK704,k1_zfmisc_1(u1_struct_0(sK703)))
    & l1_orders_2(sK703)
    & v5_orders_2(sK703)
    & v4_orders_2(sK703)
    & v3_orders_2(sK703)
    & ~ v2_struct_0(sK703) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK703,sK704,sK705])],[f4193,f5906,f5905,f5904])).

fof(f9695,plain,(
    m1_orders_2(sK705,sK703,sK704) ),
    inference(cnf_transformation,[],[f5907])).

fof(f9691,plain,(
    m1_subset_1(sK704,k1_zfmisc_1(u1_struct_0(sK703))) ),
    inference(cnf_transformation,[],[f5907])).

fof(f11609,plain,(
    m1_subset_1(sK704,k9_setfam_1(u1_struct_0(sK703))) ),
    inference(definition_unfolding,[],[f9691,f8858])).

fof(f9574,plain,(
    ! [X2,X0,X1] :
      ( k3_orders_2(X0,X1,sK691(X0,X1,X2)) = X2
      | ~ m1_orders_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f5861])).

fof(f11555,plain,(
    ! [X2,X0,X1] :
      ( k3_orders_2(X0,X1,sK691(X0,X1,X2)) = X2
      | ~ m1_orders_2(X2,X0,X1)
      | o_0_0_xboole_0 = X1
      | ~ m1_subset_1(X2,k9_setfam_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f9574,f5917,f8858,f8858])).

fof(f9686,plain,(
    ~ v2_struct_0(sK703) ),
    inference(cnf_transformation,[],[f5907])).

fof(f9687,plain,(
    v3_orders_2(sK703) ),
    inference(cnf_transformation,[],[f5907])).

fof(f9688,plain,(
    v4_orders_2(sK703) ),
    inference(cnf_transformation,[],[f5907])).

fof(f9689,plain,(
    v5_orders_2(sK703) ),
    inference(cnf_transformation,[],[f5907])).

fof(f9690,plain,(
    l1_orders_2(sK703) ),
    inference(cnf_transformation,[],[f5907])).

fof(f1919,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                  <=> ( r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4178,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                  <=> ( r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1919])).

fof(f4179,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                  <=> ( r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f4178])).

fof(f5902,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                      | ~ r2_hidden(X1,X3)
                      | ~ r2_orders_2(X0,X1,X2) )
                    & ( ( r2_hidden(X1,X3)
                        & r2_orders_2(X0,X1,X2) )
                      | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2)) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f4179])).

fof(f5903,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                      | ~ r2_hidden(X1,X3)
                      | ~ r2_orders_2(X0,X1,X2) )
                    & ( ( r2_hidden(X1,X3)
                        & r2_orders_2(X0,X1,X2) )
                      | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2)) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f5902])).

fof(f9677,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f5903])).

fof(f11598,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2))
      | ~ m1_subset_1(X3,k9_setfam_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f9677,f8858])).

fof(f9693,plain,(
    k1_xboole_0 != sK704 ),
    inference(cnf_transformation,[],[f5907])).

fof(f11607,plain,(
    o_0_0_xboole_0 != sK704 ),
    inference(definition_unfolding,[],[f9693,f5917])).

fof(f1371,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5311,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) )
      & ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f1371])).

fof(f5312,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) )
      & ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f5311])).

fof(f8313,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f5312])).

fof(f1283,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8121,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f1283])).

fof(f1281,axiom,(
    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8119,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f1281])).

fof(f9710,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f8121,f8119])).

fof(f10790,plain,(
    ! [X2,X0,X3,X1] :
      ( o_0_0_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)
      | o_0_0_xboole_0 = X3
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f8313,f5917,f9710,f5917,f5917,f5917,f5917])).

fof(f8314,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f5312])).

fof(f10789,plain,(
    ! [X2,X0,X3,X1] :
      ( o_0_0_xboole_0 != X0
      | o_0_0_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ) ),
    inference(definition_unfolding,[],[f8314,f5917,f5917,f9710])).

fof(f11896,plain,(
    ! [X2,X3,X1] : o_0_0_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,X1),X2),X3) ),
    inference(equality_resolution,[],[f10789])).

fof(f9692,plain,(
    m1_subset_1(sK705,k1_zfmisc_1(u1_struct_0(sK703))) ),
    inference(cnf_transformation,[],[f5907])).

fof(f11608,plain,(
    m1_subset_1(sK705,k9_setfam_1(u1_struct_0(sK703))) ),
    inference(definition_unfolding,[],[f9692,f8858])).

fof(f9694,plain,(
    m1_orders_2(sK704,sK703,sK705) ),
    inference(cnf_transformation,[],[f5907])).

fof(f1921,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ~ r2_hidden(X1,k3_orders_2(X0,X2,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4182,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ r2_hidden(X1,k3_orders_2(X0,X2,X1))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1921])).

fof(f4183,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ r2_hidden(X1,k3_orders_2(X0,X2,X1))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f4182])).

fof(f9680,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k3_orders_2(X0,X2,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4183])).

fof(f11601,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k3_orders_2(X0,X2,X1))
      | ~ m1_subset_1(X2,k9_setfam_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f9680,f8858])).

fof(f1924,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_orders_2(X2,X0,X1)
             => r1_tarski(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4188,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X2,X1)
              | ~ m1_orders_2(X2,X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1924])).

fof(f4189,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X2,X1)
              | ~ m1_orders_2(X2,X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f4188])).

fof(f9683,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X1)
      | ~ m1_orders_2(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4189])).

fof(f11604,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X1)
      | ~ m1_orders_2(X2,X0,X1)
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f9683,f8858])).

fof(f101,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2031,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f101])).

fof(f6056,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f2031])).

fof(f9802,plain,(
    ! [X0] :
      ( o_0_0_xboole_0 = X0
      | ~ r1_tarski(X0,o_0_0_xboole_0) ) ),
    inference(definition_unfolding,[],[f6056,f5917,f5917])).

cnf(c_3639,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k9_setfam_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(X1)))
    | r2_hidden(sK691(X1,X2,X0),X2)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1)
    | v2_struct_0(X1)
    | o_0_0_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f11556])).

cnf(c_3661,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k9_setfam_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k9_setfam_1(u1_struct_0(X1)))
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f11563])).

cnf(c_34790,plain,
    ( ~ m1_subset_1(X2,k9_setfam_1(u1_struct_0(X1)))
    | ~ m1_orders_2(X0,X1,X2)
    | r2_hidden(sK691(X1,X2,X0),X2)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1)
    | v2_struct_0(X1)
    | o_0_0_xboole_0 = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3639,c_3661])).

cnf(c_34791,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k9_setfam_1(u1_struct_0(X1)))
    | r2_hidden(sK691(X1,X2,X0),X2)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1)
    | v2_struct_0(X1)
    | o_0_0_xboole_0 = X2 ),
    inference(renaming,[status(thm)],[c_34790])).

cnf(c_110095,plain,
    ( o_0_0_xboole_0 = X0
    | m1_orders_2(X1,X2,X0) != iProver_top
    | m1_subset_1(X0,k9_setfam_1(u1_struct_0(X2))) != iProver_top
    | r2_hidden(sK691(X2,X0,X1),X0) = iProver_top
    | v4_orders_2(X2) != iProver_top
    | v5_orders_2(X2) != iProver_top
    | l1_orders_2(X2) != iProver_top
    | v3_orders_2(X2) != iProver_top
    | v2_struct_0(X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34791])).

cnf(c_3640,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k9_setfam_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(X1)))
    | m1_subset_1(sK691(X1,X2,X0),u1_struct_0(X1))
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1)
    | v2_struct_0(X1)
    | o_0_0_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f11557])).

cnf(c_34835,plain,
    ( ~ m1_subset_1(X2,k9_setfam_1(u1_struct_0(X1)))
    | ~ m1_orders_2(X0,X1,X2)
    | m1_subset_1(sK691(X1,X2,X0),u1_struct_0(X1))
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1)
    | v2_struct_0(X1)
    | o_0_0_xboole_0 = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3640,c_3661])).

cnf(c_34836,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k9_setfam_1(u1_struct_0(X1)))
    | m1_subset_1(sK691(X1,X2,X0),u1_struct_0(X1))
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1)
    | v2_struct_0(X1)
    | o_0_0_xboole_0 = X2 ),
    inference(renaming,[status(thm)],[c_34835])).

cnf(c_110094,plain,
    ( o_0_0_xboole_0 = X0
    | m1_orders_2(X1,X2,X0) != iProver_top
    | m1_subset_1(X0,k9_setfam_1(u1_struct_0(X2))) != iProver_top
    | m1_subset_1(sK691(X2,X0,X1),u1_struct_0(X2)) = iProver_top
    | v4_orders_2(X2) != iProver_top
    | v5_orders_2(X2) != iProver_top
    | l1_orders_2(X2) != iProver_top
    | v3_orders_2(X2) != iProver_top
    | v2_struct_0(X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34836])).

cnf(c_3749,negated_conjecture,
    ( m1_orders_2(sK705,sK703,sK704) ),
    inference(cnf_transformation,[],[f9695])).

cnf(c_110208,plain,
    ( m1_orders_2(sK705,sK703,sK704) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3749])).

cnf(c_3753,negated_conjecture,
    ( m1_subset_1(sK704,k9_setfam_1(u1_struct_0(sK703))) ),
    inference(cnf_transformation,[],[f11609])).

cnf(c_110205,plain,
    ( m1_subset_1(sK704,k9_setfam_1(u1_struct_0(sK703))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3753])).

cnf(c_3638,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k9_setfam_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(X1)))
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1)
    | v2_struct_0(X1)
    | k3_orders_2(X1,X2,sK691(X1,X2,X0)) = X0
    | o_0_0_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f11555])).

cnf(c_34962,plain,
    ( ~ m1_subset_1(X2,k9_setfam_1(u1_struct_0(X1)))
    | ~ m1_orders_2(X0,X1,X2)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1)
    | v2_struct_0(X1)
    | k3_orders_2(X1,X2,sK691(X1,X2,X0)) = X0
    | o_0_0_xboole_0 = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3638,c_3661])).

cnf(c_34963,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k9_setfam_1(u1_struct_0(X1)))
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1)
    | v2_struct_0(X1)
    | k3_orders_2(X1,X2,sK691(X1,X2,X0)) = X0
    | o_0_0_xboole_0 = X2 ),
    inference(renaming,[status(thm)],[c_34962])).

cnf(c_110093,plain,
    ( k3_orders_2(X0,X1,sK691(X0,X1,X2)) = X2
    | o_0_0_xboole_0 = X1
    | m1_orders_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0))) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top
    | v3_orders_2(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34963])).

cnf(c_145176,plain,
    ( k3_orders_2(sK703,sK704,sK691(sK703,sK704,X0)) = X0
    | sK704 = o_0_0_xboole_0
    | m1_orders_2(X0,sK703,sK704) != iProver_top
    | v4_orders_2(sK703) != iProver_top
    | v5_orders_2(sK703) != iProver_top
    | l1_orders_2(sK703) != iProver_top
    | v3_orders_2(sK703) != iProver_top
    | v2_struct_0(sK703) = iProver_top ),
    inference(superposition,[status(thm)],[c_110205,c_110093])).

cnf(c_3758,negated_conjecture,
    ( ~ v2_struct_0(sK703) ),
    inference(cnf_transformation,[],[f9686])).

cnf(c_3763,plain,
    ( v2_struct_0(sK703) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3758])).

cnf(c_3757,negated_conjecture,
    ( v3_orders_2(sK703) ),
    inference(cnf_transformation,[],[f9687])).

cnf(c_3764,plain,
    ( v3_orders_2(sK703) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3757])).

cnf(c_3756,negated_conjecture,
    ( v4_orders_2(sK703) ),
    inference(cnf_transformation,[],[f9688])).

cnf(c_3765,plain,
    ( v4_orders_2(sK703) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3756])).

cnf(c_3755,negated_conjecture,
    ( v5_orders_2(sK703) ),
    inference(cnf_transformation,[],[f9689])).

cnf(c_3766,plain,
    ( v5_orders_2(sK703) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3755])).

cnf(c_3754,negated_conjecture,
    ( l1_orders_2(sK703) ),
    inference(cnf_transformation,[],[f9690])).

cnf(c_3767,plain,
    ( l1_orders_2(sK703) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3754])).

cnf(c_145199,plain,
    ( m1_orders_2(X0,sK703,sK704) != iProver_top
    | sK704 = o_0_0_xboole_0
    | k3_orders_2(sK703,sK704,sK691(sK703,sK704,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_145176,c_3763,c_3764,c_3765,c_3766,c_3767])).

cnf(c_145200,plain,
    ( k3_orders_2(sK703,sK704,sK691(sK703,sK704,X0)) = X0
    | sK704 = o_0_0_xboole_0
    | m1_orders_2(X0,sK703,sK704) != iProver_top ),
    inference(renaming,[status(thm)],[c_145199])).

cnf(c_145208,plain,
    ( k3_orders_2(sK703,sK704,sK691(sK703,sK704,sK705)) = sK705
    | sK704 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_110208,c_145200])).

cnf(c_3740,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,k9_setfam_1(u1_struct_0(X1)))
    | r2_hidden(X2,X3)
    | ~ r2_hidden(X2,k3_orders_2(X1,X3,X0))
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f11598])).

cnf(c_110216,plain,
    ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X3,k9_setfam_1(u1_struct_0(X1))) != iProver_top
    | r2_hidden(X2,X3) = iProver_top
    | r2_hidden(X2,k3_orders_2(X1,X3,X0)) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v5_orders_2(X1) != iProver_top
    | l1_orders_2(X1) != iProver_top
    | v3_orders_2(X1) != iProver_top
    | v2_struct_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3740])).

cnf(c_150513,plain,
    ( sK704 = o_0_0_xboole_0
    | m1_subset_1(X0,u1_struct_0(sK703)) != iProver_top
    | m1_subset_1(sK691(sK703,sK704,sK705),u1_struct_0(sK703)) != iProver_top
    | m1_subset_1(sK704,k9_setfam_1(u1_struct_0(sK703))) != iProver_top
    | r2_hidden(X0,sK704) = iProver_top
    | r2_hidden(X0,sK705) != iProver_top
    | v4_orders_2(sK703) != iProver_top
    | v5_orders_2(sK703) != iProver_top
    | l1_orders_2(sK703) != iProver_top
    | v3_orders_2(sK703) != iProver_top
    | v2_struct_0(sK703) = iProver_top ),
    inference(superposition,[status(thm)],[c_145208,c_110216])).

cnf(c_3768,plain,
    ( m1_subset_1(sK704,k9_setfam_1(u1_struct_0(sK703))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3753])).

cnf(c_3751,negated_conjecture,
    ( o_0_0_xboole_0 != sK704 ),
    inference(cnf_transformation,[],[f11607])).

cnf(c_2384,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) != o_0_0_xboole_0
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = X2
    | o_0_0_xboole_0 = X1
    | o_0_0_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f10790])).

cnf(c_7426,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0),o_0_0_xboole_0) != o_0_0_xboole_0
    | o_0_0_xboole_0 = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2384])).

cnf(c_2383,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,X0),X1),X2) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f11896])).

cnf(c_7427,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0),o_0_0_xboole_0) = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2383])).

cnf(c_54623,plain,
    ( X0 != X1
    | X2 != X1
    | X0 = X2 ),
    theory(equality)).

cnf(c_150702,plain,
    ( sK704 != X0
    | o_0_0_xboole_0 != X0
    | o_0_0_xboole_0 = sK704 ),
    inference(instantiation,[status(thm)],[c_54623])).

cnf(c_150703,plain,
    ( sK704 != o_0_0_xboole_0
    | o_0_0_xboole_0 = sK704
    | o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_150702])).

cnf(c_150731,plain,
    ( r2_hidden(X0,sK705) != iProver_top
    | r2_hidden(X0,sK704) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK703)) != iProver_top
    | m1_subset_1(sK691(sK703,sK704,sK705),u1_struct_0(sK703)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_150513,c_3763,c_3764,c_3765,c_3766,c_3767,c_3768,c_3751,c_7426,c_7427,c_150703])).

cnf(c_150732,plain,
    ( m1_subset_1(X0,u1_struct_0(sK703)) != iProver_top
    | m1_subset_1(sK691(sK703,sK704,sK705),u1_struct_0(sK703)) != iProver_top
    | r2_hidden(X0,sK704) = iProver_top
    | r2_hidden(X0,sK705) != iProver_top ),
    inference(renaming,[status(thm)],[c_150731])).

cnf(c_150741,plain,
    ( sK704 = o_0_0_xboole_0
    | m1_orders_2(sK705,sK703,sK704) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK703)) != iProver_top
    | m1_subset_1(sK704,k9_setfam_1(u1_struct_0(sK703))) != iProver_top
    | r2_hidden(X0,sK704) = iProver_top
    | r2_hidden(X0,sK705) != iProver_top
    | v4_orders_2(sK703) != iProver_top
    | v5_orders_2(sK703) != iProver_top
    | l1_orders_2(sK703) != iProver_top
    | v3_orders_2(sK703) != iProver_top
    | v2_struct_0(sK703) = iProver_top ),
    inference(superposition,[status(thm)],[c_110094,c_150732])).

cnf(c_3771,plain,
    ( m1_orders_2(sK705,sK703,sK704) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3749])).

cnf(c_150866,plain,
    ( r2_hidden(X0,sK705) != iProver_top
    | r2_hidden(X0,sK704) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK703)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_150741,c_3763,c_3764,c_3765,c_3766,c_3767,c_3768,c_3751,c_3771,c_7426,c_7427,c_150703])).

cnf(c_150867,plain,
    ( m1_subset_1(X0,u1_struct_0(sK703)) != iProver_top
    | r2_hidden(X0,sK704) = iProver_top
    | r2_hidden(X0,sK705) != iProver_top ),
    inference(renaming,[status(thm)],[c_150866])).

cnf(c_150875,plain,
    ( o_0_0_xboole_0 = X0
    | m1_orders_2(X1,sK703,X0) != iProver_top
    | m1_subset_1(X0,k9_setfam_1(u1_struct_0(sK703))) != iProver_top
    | r2_hidden(sK691(sK703,X0,X1),sK704) = iProver_top
    | r2_hidden(sK691(sK703,X0,X1),sK705) != iProver_top
    | v4_orders_2(sK703) != iProver_top
    | v5_orders_2(sK703) != iProver_top
    | l1_orders_2(sK703) != iProver_top
    | v3_orders_2(sK703) != iProver_top
    | v2_struct_0(sK703) = iProver_top ),
    inference(superposition,[status(thm)],[c_110094,c_150867])).

cnf(c_150929,plain,
    ( r2_hidden(sK691(sK703,X0,X1),sK705) != iProver_top
    | r2_hidden(sK691(sK703,X0,X1),sK704) = iProver_top
    | m1_subset_1(X0,k9_setfam_1(u1_struct_0(sK703))) != iProver_top
    | m1_orders_2(X1,sK703,X0) != iProver_top
    | o_0_0_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_150875,c_3763,c_3764,c_3765,c_3766,c_3767])).

cnf(c_150930,plain,
    ( o_0_0_xboole_0 = X0
    | m1_orders_2(X1,sK703,X0) != iProver_top
    | m1_subset_1(X0,k9_setfam_1(u1_struct_0(sK703))) != iProver_top
    | r2_hidden(sK691(sK703,X0,X1),sK704) = iProver_top
    | r2_hidden(sK691(sK703,X0,X1),sK705) != iProver_top ),
    inference(renaming,[status(thm)],[c_150929])).

cnf(c_150938,plain,
    ( sK705 = o_0_0_xboole_0
    | m1_orders_2(X0,sK703,sK705) != iProver_top
    | m1_subset_1(sK705,k9_setfam_1(u1_struct_0(sK703))) != iProver_top
    | r2_hidden(sK691(sK703,sK705,X0),sK704) = iProver_top
    | v4_orders_2(sK703) != iProver_top
    | v5_orders_2(sK703) != iProver_top
    | l1_orders_2(sK703) != iProver_top
    | v3_orders_2(sK703) != iProver_top
    | v2_struct_0(sK703) = iProver_top ),
    inference(superposition,[status(thm)],[c_110095,c_150930])).

cnf(c_3752,negated_conjecture,
    ( m1_subset_1(sK705,k9_setfam_1(u1_struct_0(sK703))) ),
    inference(cnf_transformation,[],[f11608])).

cnf(c_3769,plain,
    ( m1_subset_1(sK705,k9_setfam_1(u1_struct_0(sK703))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3752])).

cnf(c_151023,plain,
    ( r2_hidden(sK691(sK703,sK705,X0),sK704) = iProver_top
    | sK705 = o_0_0_xboole_0
    | m1_orders_2(X0,sK703,sK705) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_150938,c_3763,c_3764,c_3765,c_3766,c_3767,c_3769])).

cnf(c_151024,plain,
    ( sK705 = o_0_0_xboole_0
    | m1_orders_2(X0,sK703,sK705) != iProver_top
    | r2_hidden(sK691(sK703,sK705,X0),sK704) = iProver_top ),
    inference(renaming,[status(thm)],[c_151023])).

cnf(c_3750,negated_conjecture,
    ( m1_orders_2(sK704,sK703,sK705) ),
    inference(cnf_transformation,[],[f9694])).

cnf(c_110207,plain,
    ( m1_orders_2(sK704,sK703,sK705) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3750])).

cnf(c_110206,plain,
    ( m1_subset_1(sK705,k9_setfam_1(u1_struct_0(sK703))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3752])).

cnf(c_145194,plain,
    ( k3_orders_2(sK703,sK705,sK691(sK703,sK705,X0)) = X0
    | sK705 = o_0_0_xboole_0
    | m1_orders_2(X0,sK703,sK705) != iProver_top
    | v4_orders_2(sK703) != iProver_top
    | v5_orders_2(sK703) != iProver_top
    | l1_orders_2(sK703) != iProver_top
    | v3_orders_2(sK703) != iProver_top
    | v2_struct_0(sK703) = iProver_top ),
    inference(superposition,[status(thm)],[c_110206,c_110093])).

cnf(c_145224,plain,
    ( m1_orders_2(X0,sK703,sK705) != iProver_top
    | sK705 = o_0_0_xboole_0
    | k3_orders_2(sK703,sK705,sK691(sK703,sK705,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_145194,c_3763,c_3764,c_3765,c_3766,c_3767])).

cnf(c_145225,plain,
    ( k3_orders_2(sK703,sK705,sK691(sK703,sK705,X0)) = X0
    | sK705 = o_0_0_xboole_0
    | m1_orders_2(X0,sK703,sK705) != iProver_top ),
    inference(renaming,[status(thm)],[c_145224])).

cnf(c_145233,plain,
    ( k3_orders_2(sK703,sK705,sK691(sK703,sK705,sK704)) = sK704
    | sK705 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_110207,c_145225])).

cnf(c_3743,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k9_setfam_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,k3_orders_2(X1,X2,X0))
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f11601])).

cnf(c_110213,plain,
    ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X2,k9_setfam_1(u1_struct_0(X1))) != iProver_top
    | r2_hidden(X0,k3_orders_2(X1,X2,X0)) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v5_orders_2(X1) != iProver_top
    | l1_orders_2(X1) != iProver_top
    | v3_orders_2(X1) != iProver_top
    | v2_struct_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3743])).

cnf(c_147836,plain,
    ( sK705 = o_0_0_xboole_0
    | m1_subset_1(sK691(sK703,sK705,sK704),u1_struct_0(sK703)) != iProver_top
    | m1_subset_1(sK705,k9_setfam_1(u1_struct_0(sK703))) != iProver_top
    | r2_hidden(sK691(sK703,sK705,sK704),sK704) != iProver_top
    | v4_orders_2(sK703) != iProver_top
    | v5_orders_2(sK703) != iProver_top
    | l1_orders_2(sK703) != iProver_top
    | v3_orders_2(sK703) != iProver_top
    | v2_struct_0(sK703) = iProver_top ),
    inference(superposition,[status(thm)],[c_145233,c_110213])).

cnf(c_148367,plain,
    ( r2_hidden(sK691(sK703,sK705,sK704),sK704) != iProver_top
    | sK705 = o_0_0_xboole_0
    | m1_subset_1(sK691(sK703,sK705,sK704),u1_struct_0(sK703)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_147836,c_3763,c_3764,c_3765,c_3766,c_3767,c_3769])).

cnf(c_148368,plain,
    ( sK705 = o_0_0_xboole_0
    | m1_subset_1(sK691(sK703,sK705,sK704),u1_struct_0(sK703)) != iProver_top
    | r2_hidden(sK691(sK703,sK705,sK704),sK704) != iProver_top ),
    inference(renaming,[status(thm)],[c_148367])).

cnf(c_148374,plain,
    ( sK705 = o_0_0_xboole_0
    | m1_orders_2(sK704,sK703,sK705) != iProver_top
    | m1_subset_1(sK705,k9_setfam_1(u1_struct_0(sK703))) != iProver_top
    | r2_hidden(sK691(sK703,sK705,sK704),sK704) != iProver_top
    | v4_orders_2(sK703) != iProver_top
    | v5_orders_2(sK703) != iProver_top
    | l1_orders_2(sK703) != iProver_top
    | v3_orders_2(sK703) != iProver_top
    | v2_struct_0(sK703) = iProver_top ),
    inference(superposition,[status(thm)],[c_110094,c_148368])).

cnf(c_3770,plain,
    ( m1_orders_2(sK704,sK703,sK705) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3750])).

cnf(c_148571,plain,
    ( r2_hidden(sK691(sK703,sK705,sK704),sK704) != iProver_top
    | sK705 = o_0_0_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_148374,c_3763,c_3764,c_3765,c_3766,c_3767,c_3769,c_3770])).

cnf(c_148572,plain,
    ( sK705 = o_0_0_xboole_0
    | r2_hidden(sK691(sK703,sK705,sK704),sK704) != iProver_top ),
    inference(renaming,[status(thm)],[c_148571])).

cnf(c_151032,plain,
    ( sK705 = o_0_0_xboole_0
    | m1_orders_2(sK704,sK703,sK705) != iProver_top ),
    inference(superposition,[status(thm)],[c_151024,c_148572])).

cnf(c_151160,plain,
    ( sK705 = o_0_0_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_151032,c_3770])).

cnf(c_3746,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k9_setfam_1(u1_struct_0(X1)))
    | r1_tarski(X0,X2)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f11604])).

cnf(c_110210,plain,
    ( m1_orders_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X2,k9_setfam_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(X0,X2) = iProver_top
    | v4_orders_2(X1) != iProver_top
    | v5_orders_2(X1) != iProver_top
    | l1_orders_2(X1) != iProver_top
    | v3_orders_2(X1) != iProver_top
    | v2_struct_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3746])).

cnf(c_146075,plain,
    ( m1_orders_2(X0,sK703,sK705) != iProver_top
    | r1_tarski(X0,sK705) = iProver_top
    | v4_orders_2(sK703) != iProver_top
    | v5_orders_2(sK703) != iProver_top
    | l1_orders_2(sK703) != iProver_top
    | v3_orders_2(sK703) != iProver_top
    | v2_struct_0(sK703) = iProver_top ),
    inference(superposition,[status(thm)],[c_110206,c_110210])).

cnf(c_146351,plain,
    ( r1_tarski(X0,sK705) = iProver_top
    | m1_orders_2(X0,sK703,sK705) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_146075,c_3763,c_3764,c_3765,c_3766,c_3767])).

cnf(c_146352,plain,
    ( m1_orders_2(X0,sK703,sK705) != iProver_top
    | r1_tarski(X0,sK705) = iProver_top ),
    inference(renaming,[status(thm)],[c_146351])).

cnf(c_146359,plain,
    ( r1_tarski(sK704,sK705) = iProver_top ),
    inference(superposition,[status(thm)],[c_110207,c_146352])).

cnf(c_151182,plain,
    ( r1_tarski(sK704,o_0_0_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_151160,c_146359])).

cnf(c_146,plain,
    ( ~ r1_tarski(X0,o_0_0_xboole_0)
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f9802])).

cnf(c_145164,plain,
    ( ~ r1_tarski(sK704,o_0_0_xboole_0)
    | o_0_0_xboole_0 = sK704 ),
    inference(instantiation,[status(thm)],[c_146])).

cnf(c_145165,plain,
    ( o_0_0_xboole_0 = sK704
    | r1_tarski(sK704,o_0_0_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_145164])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_151182,c_145165,c_3751])).

%------------------------------------------------------------------------------
