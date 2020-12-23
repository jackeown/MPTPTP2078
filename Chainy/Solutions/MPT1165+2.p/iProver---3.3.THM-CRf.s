%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1165+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:01 EST 2020

% Result     : Theorem 47.35s
% Output     : CNFRefutation 47.35s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 872 expanded)
%              Number of clauses        :   53 ( 181 expanded)
%              Number of leaves         :    9 ( 249 expanded)
%              Depth                    :   28
%              Number of atoms          :  624 (6738 expanded)
%              Number of equality atoms :  192 (1693 expanded)
%              Maximal formula depth    :   15 (   7 average)
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

fof(f4085,plain,(
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
    inference(flattening,[],[f4085])).

fof(f5855,plain,(
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
    inference(nnf_transformation,[],[f4086])).

fof(f5856,plain,(
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
    inference(rectify,[],[f5855])).

fof(f5857,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k3_orders_2(X0,X1,X4) = X2
          & r2_hidden(X4,X1)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( k3_orders_2(X0,X1,sK691(X0,X1,X2)) = X2
        & r2_hidden(sK691(X0,X1,X2),X1)
        & m1_subset_1(sK691(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK691])],[f5856,f5857])).

fof(f9573,plain,(
    ! [X2,X0,X1] :
      ( m1_orders_2(X2,X0,X1)
      | k1_xboole_0 != X2
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f5858])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5913,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f1559,axiom,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8854,plain,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    inference(cnf_transformation,[],[f1559])).

fof(f11546,plain,(
    ! [X2,X0,X1] :
      ( m1_orders_2(X2,X0,X1)
      | o_0_0_xboole_0 != X2
      | o_0_0_xboole_0 != X1
      | ~ m1_subset_1(X2,k9_setfam_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f9573,f5913,f5913,f8854,f8854])).

fof(f12019,plain,(
    ! [X0,X1] :
      ( m1_orders_2(o_0_0_xboole_0,X0,X1)
      | o_0_0_xboole_0 != X1
      | ~ m1_subset_1(o_0_0_xboole_0,k9_setfam_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f11546])).

fof(f12020,plain,(
    ! [X0] :
      ( m1_orders_2(o_0_0_xboole_0,X0,o_0_0_xboole_0)
      | ~ m1_subset_1(o_0_0_xboole_0,k9_setfam_1(u1_struct_0(X0)))
      | ~ m1_subset_1(o_0_0_xboole_0,k9_setfam_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f12019])).

fof(f1925,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ~ ( k1_xboole_0 = X1
                & ~ m1_orders_2(X1,X0,X1) )
            & ~ ( m1_orders_2(X1,X0,X1)
                & k1_xboole_0 != X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1926,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ~ ( k1_xboole_0 = X1
                  & ~ m1_orders_2(X1,X0,X1) )
              & ~ ( m1_orders_2(X1,X0,X1)
                  & k1_xboole_0 != X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f1925])).

fof(f4189,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( k1_xboole_0 = X1
              & ~ m1_orders_2(X1,X0,X1) )
            | ( m1_orders_2(X1,X0,X1)
              & k1_xboole_0 != X1 ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1926])).

fof(f4190,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( k1_xboole_0 = X1
              & ~ m1_orders_2(X1,X0,X1) )
            | ( m1_orders_2(X1,X0,X1)
              & k1_xboole_0 != X1 ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f4189])).

fof(f5902,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ( k1_xboole_0 = X1
              & ~ m1_orders_2(X1,X0,X1) )
            | ( m1_orders_2(X1,X0,X1)
              & k1_xboole_0 != X1 ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ( k1_xboole_0 = sK704
            & ~ m1_orders_2(sK704,X0,sK704) )
          | ( m1_orders_2(sK704,X0,sK704)
            & k1_xboole_0 != sK704 ) )
        & m1_subset_1(sK704,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f5901,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ( k1_xboole_0 = X1
                & ~ m1_orders_2(X1,X0,X1) )
              | ( m1_orders_2(X1,X0,X1)
                & k1_xboole_0 != X1 ) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ( k1_xboole_0 = X1
              & ~ m1_orders_2(X1,sK703,X1) )
            | ( m1_orders_2(X1,sK703,X1)
              & k1_xboole_0 != X1 ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK703))) )
      & l1_orders_2(sK703)
      & v5_orders_2(sK703)
      & v4_orders_2(sK703)
      & v3_orders_2(sK703)
      & ~ v2_struct_0(sK703) ) ),
    introduced(choice_axiom,[])).

fof(f5903,plain,
    ( ( ( k1_xboole_0 = sK704
        & ~ m1_orders_2(sK704,sK703,sK704) )
      | ( m1_orders_2(sK704,sK703,sK704)
        & k1_xboole_0 != sK704 ) )
    & m1_subset_1(sK704,k1_zfmisc_1(u1_struct_0(sK703)))
    & l1_orders_2(sK703)
    & v5_orders_2(sK703)
    & v4_orders_2(sK703)
    & v3_orders_2(sK703)
    & ~ v2_struct_0(sK703) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK703,sK704])],[f4190,f5902,f5901])).

fof(f9689,plain,
    ( k1_xboole_0 = sK704
    | m1_orders_2(sK704,sK703,sK704) ),
    inference(cnf_transformation,[],[f5903])).

fof(f11599,plain,
    ( o_0_0_xboole_0 = sK704
    | m1_orders_2(sK704,sK703,sK704) ),
    inference(definition_unfolding,[],[f9689,f5913])).

fof(f9569,plain,(
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
    inference(cnf_transformation,[],[f5858])).

fof(f11550,plain,(
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
    inference(definition_unfolding,[],[f9569,f5913,f8854,f8854])).

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

fof(f4105,plain,(
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
    inference(flattening,[],[f4105])).

fof(f9594,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_orders_2(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4106])).

fof(f11557,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k9_setfam_1(u1_struct_0(X0)))
      | ~ m1_orders_2(X2,X0,X1)
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f9594,f8854,f8854])).

fof(f9568,plain,(
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
    inference(cnf_transformation,[],[f5858])).

fof(f11551,plain,(
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
    inference(definition_unfolding,[],[f9568,f5913,f8854,f8854])).

fof(f9685,plain,(
    m1_subset_1(sK704,k1_zfmisc_1(u1_struct_0(sK703))) ),
    inference(cnf_transformation,[],[f5903])).

fof(f11602,plain,(
    m1_subset_1(sK704,k9_setfam_1(u1_struct_0(sK703))) ),
    inference(definition_unfolding,[],[f9685,f8854])).

fof(f9570,plain,(
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
    inference(cnf_transformation,[],[f5858])).

fof(f11549,plain,(
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
    inference(definition_unfolding,[],[f9570,f5913,f8854,f8854])).

fof(f9680,plain,(
    ~ v2_struct_0(sK703) ),
    inference(cnf_transformation,[],[f5903])).

fof(f9681,plain,(
    v3_orders_2(sK703) ),
    inference(cnf_transformation,[],[f5903])).

fof(f9682,plain,(
    v4_orders_2(sK703) ),
    inference(cnf_transformation,[],[f5903])).

fof(f9683,plain,(
    v5_orders_2(sK703) ),
    inference(cnf_transformation,[],[f5903])).

fof(f9684,plain,(
    l1_orders_2(sK703) ),
    inference(cnf_transformation,[],[f5903])).

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

fof(f4181,plain,(
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
    inference(flattening,[],[f4181])).

fof(f9676,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k3_orders_2(X0,X2,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4182])).

fof(f11595,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k3_orders_2(X0,X2,X1))
      | ~ m1_subset_1(X2,k9_setfam_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f9676,f8854])).

fof(f9686,plain,
    ( ~ m1_orders_2(sK704,sK703,sK704)
    | k1_xboole_0 != sK704 ),
    inference(cnf_transformation,[],[f5903])).

fof(f11601,plain,
    ( ~ m1_orders_2(sK704,sK703,sK704)
    | o_0_0_xboole_0 != sK704 ),
    inference(definition_unfolding,[],[f9686,f5913])).

cnf(c_3635,plain,
    ( m1_orders_2(o_0_0_xboole_0,X0,o_0_0_xboole_0)
    | ~ m1_subset_1(o_0_0_xboole_0,k9_setfam_1(u1_struct_0(X0)))
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v3_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f12020])).

cnf(c_150868,plain,
    ( m1_orders_2(o_0_0_xboole_0,sK703,o_0_0_xboole_0)
    | ~ m1_subset_1(o_0_0_xboole_0,k9_setfam_1(u1_struct_0(sK703)))
    | ~ v4_orders_2(sK703)
    | ~ v5_orders_2(sK703)
    | ~ l1_orders_2(sK703)
    | ~ v3_orders_2(sK703)
    | v2_struct_0(sK703) ),
    inference(instantiation,[status(thm)],[c_3635])).

cnf(c_3747,negated_conjecture,
    ( m1_orders_2(sK704,sK703,sK704)
    | o_0_0_xboole_0 = sK704 ),
    inference(cnf_transformation,[],[f11599])).

cnf(c_110193,plain,
    ( o_0_0_xboole_0 = sK704
    | m1_orders_2(sK704,sK703,sK704) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3747])).

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
    inference(cnf_transformation,[],[f11550])).

cnf(c_3661,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k9_setfam_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k9_setfam_1(u1_struct_0(X1)))
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f11557])).

cnf(c_34789,plain,
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

cnf(c_34790,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k9_setfam_1(u1_struct_0(X1)))
    | r2_hidden(sK691(X1,X2,X0),X2)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1)
    | v2_struct_0(X1)
    | o_0_0_xboole_0 = X2 ),
    inference(renaming,[status(thm)],[c_34789])).

cnf(c_110081,plain,
    ( o_0_0_xboole_0 = X0
    | m1_orders_2(X1,X2,X0) != iProver_top
    | m1_subset_1(X0,k9_setfam_1(u1_struct_0(X2))) != iProver_top
    | r2_hidden(sK691(X2,X0,X1),X0) = iProver_top
    | v4_orders_2(X2) != iProver_top
    | v5_orders_2(X2) != iProver_top
    | l1_orders_2(X2) != iProver_top
    | v3_orders_2(X2) != iProver_top
    | v2_struct_0(X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34790])).

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
    inference(cnf_transformation,[],[f11551])).

cnf(c_34834,plain,
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

cnf(c_34835,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k9_setfam_1(u1_struct_0(X1)))
    | m1_subset_1(sK691(X1,X2,X0),u1_struct_0(X1))
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1)
    | v2_struct_0(X1)
    | o_0_0_xboole_0 = X2 ),
    inference(renaming,[status(thm)],[c_34834])).

cnf(c_110080,plain,
    ( o_0_0_xboole_0 = X0
    | m1_orders_2(X1,X2,X0) != iProver_top
    | m1_subset_1(X0,k9_setfam_1(u1_struct_0(X2))) != iProver_top
    | m1_subset_1(sK691(X2,X0,X1),u1_struct_0(X2)) = iProver_top
    | v4_orders_2(X2) != iProver_top
    | v5_orders_2(X2) != iProver_top
    | l1_orders_2(X2) != iProver_top
    | v3_orders_2(X2) != iProver_top
    | v2_struct_0(X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34835])).

cnf(c_3751,negated_conjecture,
    ( m1_subset_1(sK704,k9_setfam_1(u1_struct_0(sK703))) ),
    inference(cnf_transformation,[],[f11602])).

cnf(c_110191,plain,
    ( m1_subset_1(sK704,k9_setfam_1(u1_struct_0(sK703))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3751])).

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
    inference(cnf_transformation,[],[f11549])).

cnf(c_34961,plain,
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

cnf(c_34962,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k9_setfam_1(u1_struct_0(X1)))
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1)
    | v2_struct_0(X1)
    | k3_orders_2(X1,X2,sK691(X1,X2,X0)) = X0
    | o_0_0_xboole_0 = X2 ),
    inference(renaming,[status(thm)],[c_34961])).

cnf(c_110079,plain,
    ( k3_orders_2(X0,X1,sK691(X0,X1,X2)) = X2
    | o_0_0_xboole_0 = X1
    | m1_orders_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0))) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top
    | v3_orders_2(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34962])).

cnf(c_145110,plain,
    ( k3_orders_2(sK703,sK704,sK691(sK703,sK704,X0)) = X0
    | sK704 = o_0_0_xboole_0
    | m1_orders_2(X0,sK703,sK704) != iProver_top
    | v4_orders_2(sK703) != iProver_top
    | v5_orders_2(sK703) != iProver_top
    | l1_orders_2(sK703) != iProver_top
    | v3_orders_2(sK703) != iProver_top
    | v2_struct_0(sK703) = iProver_top ),
    inference(superposition,[status(thm)],[c_110191,c_110079])).

cnf(c_3756,negated_conjecture,
    ( ~ v2_struct_0(sK703) ),
    inference(cnf_transformation,[],[f9680])).

cnf(c_3761,plain,
    ( v2_struct_0(sK703) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3756])).

cnf(c_3755,negated_conjecture,
    ( v3_orders_2(sK703) ),
    inference(cnf_transformation,[],[f9681])).

cnf(c_3762,plain,
    ( v3_orders_2(sK703) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3755])).

cnf(c_3754,negated_conjecture,
    ( v4_orders_2(sK703) ),
    inference(cnf_transformation,[],[f9682])).

cnf(c_3763,plain,
    ( v4_orders_2(sK703) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3754])).

cnf(c_3753,negated_conjecture,
    ( v5_orders_2(sK703) ),
    inference(cnf_transformation,[],[f9683])).

cnf(c_3764,plain,
    ( v5_orders_2(sK703) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3753])).

cnf(c_3752,negated_conjecture,
    ( l1_orders_2(sK703) ),
    inference(cnf_transformation,[],[f9684])).

cnf(c_3765,plain,
    ( l1_orders_2(sK703) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3752])).

cnf(c_145143,plain,
    ( m1_orders_2(X0,sK703,sK704) != iProver_top
    | sK704 = o_0_0_xboole_0
    | k3_orders_2(sK703,sK704,sK691(sK703,sK704,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_145110,c_3761,c_3762,c_3763,c_3764,c_3765])).

cnf(c_145144,plain,
    ( k3_orders_2(sK703,sK704,sK691(sK703,sK704,X0)) = X0
    | sK704 = o_0_0_xboole_0
    | m1_orders_2(X0,sK703,sK704) != iProver_top ),
    inference(renaming,[status(thm)],[c_145143])).

cnf(c_145152,plain,
    ( k3_orders_2(sK703,sK704,sK691(sK703,sK704,sK704)) = sK704
    | sK704 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_110193,c_145144])).

cnf(c_3743,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k9_setfam_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,k3_orders_2(X1,X2,X0))
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f11595])).

cnf(c_110197,plain,
    ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X2,k9_setfam_1(u1_struct_0(X1))) != iProver_top
    | r2_hidden(X0,k3_orders_2(X1,X2,X0)) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v5_orders_2(X1) != iProver_top
    | l1_orders_2(X1) != iProver_top
    | v3_orders_2(X1) != iProver_top
    | v2_struct_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3743])).

cnf(c_146902,plain,
    ( sK704 = o_0_0_xboole_0
    | m1_subset_1(sK691(sK703,sK704,sK704),u1_struct_0(sK703)) != iProver_top
    | m1_subset_1(sK704,k9_setfam_1(u1_struct_0(sK703))) != iProver_top
    | r2_hidden(sK691(sK703,sK704,sK704),sK704) != iProver_top
    | v4_orders_2(sK703) != iProver_top
    | v5_orders_2(sK703) != iProver_top
    | l1_orders_2(sK703) != iProver_top
    | v3_orders_2(sK703) != iProver_top
    | v2_struct_0(sK703) = iProver_top ),
    inference(superposition,[status(thm)],[c_145152,c_110197])).

cnf(c_3766,plain,
    ( m1_subset_1(sK704,k9_setfam_1(u1_struct_0(sK703))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3751])).

cnf(c_146933,plain,
    ( r2_hidden(sK691(sK703,sK704,sK704),sK704) != iProver_top
    | sK704 = o_0_0_xboole_0
    | m1_subset_1(sK691(sK703,sK704,sK704),u1_struct_0(sK703)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_146902,c_3761,c_3762,c_3763,c_3764,c_3765,c_3766])).

cnf(c_146934,plain,
    ( sK704 = o_0_0_xboole_0
    | m1_subset_1(sK691(sK703,sK704,sK704),u1_struct_0(sK703)) != iProver_top
    | r2_hidden(sK691(sK703,sK704,sK704),sK704) != iProver_top ),
    inference(renaming,[status(thm)],[c_146933])).

cnf(c_146940,plain,
    ( sK704 = o_0_0_xboole_0
    | m1_orders_2(sK704,sK703,sK704) != iProver_top
    | m1_subset_1(sK704,k9_setfam_1(u1_struct_0(sK703))) != iProver_top
    | r2_hidden(sK691(sK703,sK704,sK704),sK704) != iProver_top
    | v4_orders_2(sK703) != iProver_top
    | v5_orders_2(sK703) != iProver_top
    | l1_orders_2(sK703) != iProver_top
    | v3_orders_2(sK703) != iProver_top
    | v2_struct_0(sK703) = iProver_top ),
    inference(superposition,[status(thm)],[c_110080,c_146934])).

cnf(c_146974,plain,
    ( r2_hidden(sK691(sK703,sK704,sK704),sK704) != iProver_top
    | sK704 = o_0_0_xboole_0
    | m1_orders_2(sK704,sK703,sK704) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_146940,c_3761,c_3762,c_3763,c_3764,c_3765,c_3766])).

cnf(c_146975,plain,
    ( sK704 = o_0_0_xboole_0
    | m1_orders_2(sK704,sK703,sK704) != iProver_top
    | r2_hidden(sK691(sK703,sK704,sK704),sK704) != iProver_top ),
    inference(renaming,[status(thm)],[c_146974])).

cnf(c_146981,plain,
    ( sK704 = o_0_0_xboole_0
    | m1_orders_2(sK704,sK703,sK704) != iProver_top
    | m1_subset_1(sK704,k9_setfam_1(u1_struct_0(sK703))) != iProver_top
    | v4_orders_2(sK703) != iProver_top
    | v5_orders_2(sK703) != iProver_top
    | l1_orders_2(sK703) != iProver_top
    | v3_orders_2(sK703) != iProver_top
    | v2_struct_0(sK703) = iProver_top ),
    inference(superposition,[status(thm)],[c_110081,c_146975])).

cnf(c_146984,plain,
    ( sK704 = o_0_0_xboole_0
    | m1_orders_2(sK704,sK703,sK704) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_146981,c_3761,c_3762,c_3763,c_3764,c_3765,c_3766])).

cnf(c_146990,plain,
    ( sK704 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_110193,c_146984])).

cnf(c_3750,negated_conjecture,
    ( ~ m1_orders_2(sK704,sK703,sK704)
    | o_0_0_xboole_0 != sK704 ),
    inference(cnf_transformation,[],[f11601])).

cnf(c_110192,plain,
    ( o_0_0_xboole_0 != sK704
    | m1_orders_2(sK704,sK703,sK704) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3750])).

cnf(c_147232,plain,
    ( o_0_0_xboole_0 != o_0_0_xboole_0
    | m1_orders_2(o_0_0_xboole_0,sK703,o_0_0_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_146990,c_110192])).

cnf(c_147236,plain,
    ( m1_orders_2(o_0_0_xboole_0,sK703,o_0_0_xboole_0) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_147232])).

cnf(c_147245,plain,
    ( ~ m1_orders_2(o_0_0_xboole_0,sK703,o_0_0_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_147236])).

cnf(c_147233,plain,
    ( m1_subset_1(o_0_0_xboole_0,k9_setfam_1(u1_struct_0(sK703))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_146990,c_110191])).

cnf(c_147244,plain,
    ( m1_subset_1(o_0_0_xboole_0,k9_setfam_1(u1_struct_0(sK703))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_147233])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_150868,c_147245,c_147244,c_3752,c_3753,c_3754,c_3755,c_3756])).

%------------------------------------------------------------------------------
