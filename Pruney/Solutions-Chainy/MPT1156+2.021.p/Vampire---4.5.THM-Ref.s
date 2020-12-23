%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:00 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 735 expanded)
%              Number of leaves         :   15 ( 227 expanded)
%              Depth                    :   33
%              Number of atoms          :  499 (4716 expanded)
%              Number of equality atoms :   71 ( 105 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f179,plain,(
    $false ),
    inference(subsumption_resolution,[],[f178,f43])).

fof(f43,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( r2_hidden(sK2,k2_orders_2(sK1,k6_domain_1(u1_struct_0(sK1),sK2)))
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l1_orders_2(sK1)
    & v5_orders_2(sK1)
    & v4_orders_2(sK1)
    & v3_orders_2(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f14,f31,f30])).

fof(f30,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( r2_hidden(X1,k2_orders_2(sK1,k6_domain_1(u1_struct_0(sK1),X1)))
          & m1_subset_1(X1,u1_struct_0(sK1)) )
      & l1_orders_2(sK1)
      & v5_orders_2(sK1)
      & v4_orders_2(sK1)
      & v3_orders_2(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X1] :
        ( r2_hidden(X1,k2_orders_2(sK1,k6_domain_1(u1_struct_0(sK1),X1)))
        & m1_subset_1(X1,u1_struct_0(sK1)) )
   => ( r2_hidden(sK2,k2_orders_2(sK1,k6_domain_1(u1_struct_0(sK1),sK2)))
      & m1_subset_1(sK2,u1_struct_0(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ~ r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ~ r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_orders_2)).

fof(f178,plain,(
    v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f177,f44])).

fof(f44,plain,(
    v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f177,plain,
    ( ~ v3_orders_2(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f176,f47])).

fof(f47,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f176,plain,
    ( ~ l1_orders_2(sK1)
    | ~ v3_orders_2(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f175,f48])).

fof(f48,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f32])).

fof(f175,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ v3_orders_2(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f169,f149])).

fof(f149,plain,(
    ~ m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(forward_demodulation,[],[f148,f145])).

fof(f145,plain,(
    k6_domain_1(u1_struct_0(sK1),sK2) = k2_tarski(sK2,sK2) ),
    inference(subsumption_resolution,[],[f144,f43])).

fof(f144,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK2) = k2_tarski(sK2,sK2)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f143,f44])).

fof(f143,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK2) = k2_tarski(sK2,sK2)
    | ~ v3_orders_2(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f142,f47])).

fof(f142,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK2) = k2_tarski(sK2,sK2)
    | ~ l1_orders_2(sK1)
    | ~ v3_orders_2(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f139,f48])).

fof(f139,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK2) = k2_tarski(sK2,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ v3_orders_2(sK1)
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f136,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_orders_2(X0,X1,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_orders_2)).

fof(f136,plain,
    ( ~ r1_orders_2(sK1,sK2,sK2)
    | k6_domain_1(u1_struct_0(sK1),sK2) = k2_tarski(sK2,sK2) ),
    inference(subsumption_resolution,[],[f132,f86])).

fof(f86,plain,(
    sP0(sK2,sK2,sK1) ),
    inference(resolution,[],[f85,f48])).

fof(f85,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | sP0(sK2,X0,sK1) ) ),
    inference(resolution,[],[f84,f48])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | sP0(X0,X1,sK1) ) ),
    inference(subsumption_resolution,[],[f83,f44])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | sP0(X0,X1,sK1)
      | ~ v3_orders_2(sK1) ) ),
    inference(resolution,[],[f64,f47])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | sP0(X2,X1,X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( sP0(X2,X1,X0)
                & ( r1_orders_2(X0,X2,X1)
                  | r1_orders_2(X0,X1,X2)
                  | ! [X3] :
                      ( ~ r2_hidden(X2,X3)
                      | ~ r2_hidden(X1,X3)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                      | ~ v6_orders_2(X3,X0) ) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( sP0(X2,X1,X0)
                & ( r1_orders_2(X0,X2,X1)
                  | r1_orders_2(X0,X1,X2)
                  | ! [X4] :
                      ( ~ r2_hidden(X2,X4)
                      | ~ r2_hidden(X1,X4)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                      | ~ v6_orders_2(X4,X0) ) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(definition_folding,[],[f22,f28])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X2,X3)
          & r2_hidden(X1,X3)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
          & v6_orders_2(X3,X0) )
      | ( ~ r1_orders_2(X0,X2,X1)
        & ~ r1_orders_2(X0,X1,X2) )
      | ~ sP0(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ? [X3] :
                      ( r2_hidden(X2,X3)
                      & r2_hidden(X1,X3)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                      & v6_orders_2(X3,X0) )
                  | ( ~ r1_orders_2(X0,X2,X1)
                    & ~ r1_orders_2(X0,X1,X2) ) )
                & ( r1_orders_2(X0,X2,X1)
                  | r1_orders_2(X0,X1,X2)
                  | ! [X4] :
                      ( ~ r2_hidden(X2,X4)
                      | ~ r2_hidden(X1,X4)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                      | ~ v6_orders_2(X4,X0) ) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ? [X3] :
                      ( r2_hidden(X2,X3)
                      & r2_hidden(X1,X3)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                      & v6_orders_2(X3,X0) )
                  | ( ~ r1_orders_2(X0,X2,X1)
                    & ~ r1_orders_2(X0,X1,X2) ) )
                & ( r1_orders_2(X0,X2,X1)
                  | r1_orders_2(X0,X1,X2)
                  | ! [X4] :
                      ( ~ r2_hidden(X2,X4)
                      | ~ r2_hidden(X1,X4)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                      | ~ v6_orders_2(X4,X0) ) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ~ ( ! [X3] :
                        ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                          & v6_orders_2(X3,X0) )
                       => ~ ( r2_hidden(X2,X3)
                            & r2_hidden(X1,X3) ) )
                    & ( r1_orders_2(X0,X2,X1)
                      | r1_orders_2(X0,X1,X2) ) )
                & ~ ( ~ r1_orders_2(X0,X2,X1)
                    & ~ r1_orders_2(X0,X1,X2)
                    & ? [X4] :
                        ( r2_hidden(X2,X4)
                        & r2_hidden(X1,X4)
                        & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                        & v6_orders_2(X4,X0) ) ) ) ) ) ) ),
    inference(rectify,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ~ ( ! [X3] :
                        ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                          & v6_orders_2(X3,X0) )
                       => ~ ( r2_hidden(X2,X3)
                            & r2_hidden(X1,X3) ) )
                    & ( r1_orders_2(X0,X2,X1)
                      | r1_orders_2(X0,X1,X2) ) )
                & ~ ( ~ r1_orders_2(X0,X2,X1)
                    & ~ r1_orders_2(X0,X1,X2)
                    & ? [X3] :
                        ( r2_hidden(X2,X3)
                        & r2_hidden(X1,X3)
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                        & v6_orders_2(X3,X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_orders_2)).

fof(f132,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK2) = k2_tarski(sK2,sK2)
    | ~ r1_orders_2(sK1,sK2,sK2)
    | ~ sP0(sK2,sK2,sK1) ),
    inference(resolution,[],[f131,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,sK3(X0,X1,X2))
      | ~ r1_orders_2(X2,X0,X1)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,sK3(X0,X1,X2))
        & r2_hidden(X1,sK3(X0,X1,X2))
        & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2)))
        & v6_orders_2(sK3(X0,X1,X2),X2) )
      | ( ~ r1_orders_2(X2,X0,X1)
        & ~ r1_orders_2(X2,X1,X0) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f34,f35])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X0,X3)
          & r2_hidden(X1,X3)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
          & v6_orders_2(X3,X2) )
     => ( r2_hidden(X0,sK3(X0,X1,X2))
        & r2_hidden(X1,sK3(X0,X1,X2))
        & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2)))
        & v6_orders_2(sK3(X0,X1,X2),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ? [X3] :
          ( r2_hidden(X0,X3)
          & r2_hidden(X1,X3)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
          & v6_orders_2(X3,X2) )
      | ( ~ r1_orders_2(X2,X0,X1)
        & ~ r1_orders_2(X2,X1,X0) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X2,X3)
          & r2_hidden(X1,X3)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
          & v6_orders_2(X3,X0) )
      | ( ~ r1_orders_2(X0,X2,X1)
        & ~ r1_orders_2(X0,X1,X2) )
      | ~ sP0(X2,X1,X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f131,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK3(sK2,sK2,sK1))
      | k6_domain_1(u1_struct_0(sK1),sK2) = k2_tarski(sK2,sK2) ) ),
    inference(resolution,[],[f127,f48])).

fof(f127,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK1))
      | k2_tarski(X4,X4) = k6_domain_1(u1_struct_0(sK1),X4)
      | ~ r2_hidden(X5,sK3(sK2,sK2,sK1)) ) ),
    inference(resolution,[],[f82,f93])).

fof(f93,plain,(
    m1_subset_1(sK3(sK2,sK2,sK1),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f92,f43])).

fof(f92,plain,
    ( m1_subset_1(sK3(sK2,sK2,sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f91,f44])).

fof(f91,plain,
    ( m1_subset_1(sK3(sK2,sK2,sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v3_orders_2(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f90,f47])).

fof(f90,plain,
    ( m1_subset_1(sK3(sK2,sK2,sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_orders_2(sK1)
    | ~ v3_orders_2(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f89,f48])).

fof(f89,plain,
    ( m1_subset_1(sK3(sK2,sK2,sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ v3_orders_2(sK1)
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f87,f52])).

fof(f87,plain,
    ( ~ r1_orders_2(sK1,sK2,sK2)
    | m1_subset_1(sK3(sK2,sK2,sK1),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(resolution,[],[f86,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r1_orders_2(X2,X0,X1)
      | m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | k2_tarski(X0,X0) = k6_domain_1(X1,X0)
      | ~ m1_subset_1(X0,X1)
      | ~ r2_hidden(X3,X2) ) ),
    inference(resolution,[],[f74,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f74,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k2_tarski(X1,X1) ) ),
    inference(definition_unfolding,[],[f65,f50])).

fof(f50,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f65,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f148,plain,(
    ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f146,f76])).

fof(f76,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_tarski(X0,X4)) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK4(X0,X1,X2) != X1
              & sK4(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( sK4(X0,X1,X2) = X1
            | sK4(X0,X1,X2) = X0
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f40,f41])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK4(X0,X1,X2) != X1
            & sK4(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( sK4(X0,X1,X2) = X1
          | sK4(X0,X1,X2) = X0
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f39])).

% (19716)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

% (19728)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f146,plain,
    ( ~ r2_hidden(sK2,k2_tarski(sK2,sK2))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(backward_demodulation,[],[f120,f145])).

fof(f120,plain,
    ( ~ r2_hidden(sK2,k6_domain_1(u1_struct_0(sK1),sK2))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(resolution,[],[f113,f49])).

fof(f49,plain,(
    r2_hidden(sK2,k2_orders_2(sK1,k6_domain_1(u1_struct_0(sK1),sK2))) ),
    inference(cnf_transformation,[],[f32])).

fof(f113,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k2_orders_2(sK1,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ r2_hidden(X0,X1) ) ),
    inference(subsumption_resolution,[],[f112,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f112,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ r2_hidden(X0,k2_orders_2(sK1,X1)) ) ),
    inference(subsumption_resolution,[],[f111,f43])).

fof(f111,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ r2_hidden(X0,k2_orders_2(sK1,X1))
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f110,f44])).

fof(f110,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ r2_hidden(X0,k2_orders_2(sK1,X1))
      | ~ v3_orders_2(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f109,f45])).

fof(f45,plain,(
    v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ r2_hidden(X0,k2_orders_2(sK1,X1))
      | ~ v4_orders_2(sK1)
      | ~ v3_orders_2(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f108,f47])).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ l1_orders_2(sK1)
      | ~ r2_hidden(X0,k2_orders_2(sK1,X1))
      | ~ v4_orders_2(sK1)
      | ~ v3_orders_2(sK1)
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f51,f46])).

fof(f46,plain,(
    v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r2_hidden(X1,k2_orders_2(X0,X2))
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ r2_hidden(X1,k2_orders_2(X0,X2))
              | ~ r2_hidden(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ r2_hidden(X1,k2_orders_2(X0,X2))
              | ~ r2_hidden(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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
             => ~ ( r2_hidden(X1,k2_orders_2(X0,X2))
                  & r2_hidden(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_orders_2)).

fof(f169,plain,
    ( m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ v3_orders_2(sK1)
    | v2_struct_0(sK1) ),
    inference(superposition,[],[f54,f145])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_orders_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:41:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.50  % (19706)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.51  % (19699)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.51  % (19722)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.51  % (19707)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.51  % (19704)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.51  % (19714)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.52  % (19709)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.52  % (19715)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.52  % (19709)Refutation not found, incomplete strategy% (19709)------------------------------
% 0.22/0.52  % (19709)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (19709)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (19709)Memory used [KB]: 10746
% 0.22/0.52  % (19709)Time elapsed: 0.106 s
% 0.22/0.52  % (19709)------------------------------
% 0.22/0.52  % (19709)------------------------------
% 0.22/0.52  % (19710)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.52  % (19713)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.52  % (19700)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.52  % (19723)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.52  % (19705)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (19721)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.53  % (19711)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.53  % (19720)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.53  % (19721)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % (19700)Refutation not found, incomplete strategy% (19700)------------------------------
% 0.22/0.53  % (19700)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (19712)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.53  % (19701)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.53  % (19700)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (19700)Memory used [KB]: 1663
% 0.22/0.53  % (19700)Time elapsed: 0.107 s
% 0.22/0.53  % (19700)------------------------------
% 0.22/0.53  % (19700)------------------------------
% 0.22/0.53  % (19724)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.53  % (19703)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.54  % (19702)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f179,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(subsumption_resolution,[],[f178,f43])).
% 0.22/0.54  fof(f43,plain,(
% 0.22/0.54    ~v2_struct_0(sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f32])).
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    (r2_hidden(sK2,k2_orders_2(sK1,k6_domain_1(u1_struct_0(sK1),sK2))) & m1_subset_1(sK2,u1_struct_0(sK1))) & l1_orders_2(sK1) & v5_orders_2(sK1) & v4_orders_2(sK1) & v3_orders_2(sK1) & ~v2_struct_0(sK1)),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f14,f31,f30])).
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : (r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (r2_hidden(X1,k2_orders_2(sK1,k6_domain_1(u1_struct_0(sK1),X1))) & m1_subset_1(X1,u1_struct_0(sK1))) & l1_orders_2(sK1) & v5_orders_2(sK1) & v4_orders_2(sK1) & v3_orders_2(sK1) & ~v2_struct_0(sK1))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    ? [X1] : (r2_hidden(X1,k2_orders_2(sK1,k6_domain_1(u1_struct_0(sK1),X1))) & m1_subset_1(X1,u1_struct_0(sK1))) => (r2_hidden(sK2,k2_orders_2(sK1,k6_domain_1(u1_struct_0(sK1),sK2))) & m1_subset_1(sK2,u1_struct_0(sK1)))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f14,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : (r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.22/0.54    inference(flattening,[],[f13])).
% 0.22/0.54  fof(f13,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : (r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f11])).
% 0.22/0.54  fof(f11,negated_conjecture,(
% 0.22/0.54    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))))),
% 0.22/0.54    inference(negated_conjecture,[],[f10])).
% 0.22/0.54  fof(f10,conjecture,(
% 0.22/0.54    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_orders_2)).
% 0.22/0.54  fof(f178,plain,(
% 0.22/0.54    v2_struct_0(sK1)),
% 0.22/0.54    inference(subsumption_resolution,[],[f177,f44])).
% 0.22/0.54  fof(f44,plain,(
% 0.22/0.54    v3_orders_2(sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f32])).
% 0.22/0.54  fof(f177,plain,(
% 0.22/0.54    ~v3_orders_2(sK1) | v2_struct_0(sK1)),
% 0.22/0.54    inference(subsumption_resolution,[],[f176,f47])).
% 0.22/0.54  fof(f47,plain,(
% 0.22/0.54    l1_orders_2(sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f32])).
% 0.22/0.54  fof(f176,plain,(
% 0.22/0.54    ~l1_orders_2(sK1) | ~v3_orders_2(sK1) | v2_struct_0(sK1)),
% 0.22/0.54    inference(subsumption_resolution,[],[f175,f48])).
% 0.22/0.54  fof(f48,plain,(
% 0.22/0.54    m1_subset_1(sK2,u1_struct_0(sK1))),
% 0.22/0.54    inference(cnf_transformation,[],[f32])).
% 0.22/0.54  fof(f175,plain,(
% 0.22/0.54    ~m1_subset_1(sK2,u1_struct_0(sK1)) | ~l1_orders_2(sK1) | ~v3_orders_2(sK1) | v2_struct_0(sK1)),
% 0.22/0.54    inference(subsumption_resolution,[],[f169,f149])).
% 0.22/0.54  fof(f149,plain,(
% 0.22/0.54    ~m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.22/0.54    inference(forward_demodulation,[],[f148,f145])).
% 0.22/0.54  fof(f145,plain,(
% 0.22/0.54    k6_domain_1(u1_struct_0(sK1),sK2) = k2_tarski(sK2,sK2)),
% 0.22/0.54    inference(subsumption_resolution,[],[f144,f43])).
% 0.22/0.54  fof(f144,plain,(
% 0.22/0.54    k6_domain_1(u1_struct_0(sK1),sK2) = k2_tarski(sK2,sK2) | v2_struct_0(sK1)),
% 0.22/0.54    inference(subsumption_resolution,[],[f143,f44])).
% 0.22/0.54  fof(f143,plain,(
% 0.22/0.54    k6_domain_1(u1_struct_0(sK1),sK2) = k2_tarski(sK2,sK2) | ~v3_orders_2(sK1) | v2_struct_0(sK1)),
% 0.22/0.54    inference(subsumption_resolution,[],[f142,f47])).
% 0.22/0.54  fof(f142,plain,(
% 0.22/0.54    k6_domain_1(u1_struct_0(sK1),sK2) = k2_tarski(sK2,sK2) | ~l1_orders_2(sK1) | ~v3_orders_2(sK1) | v2_struct_0(sK1)),
% 0.22/0.54    inference(subsumption_resolution,[],[f139,f48])).
% 0.22/0.54  fof(f139,plain,(
% 0.22/0.54    k6_domain_1(u1_struct_0(sK1),sK2) = k2_tarski(sK2,sK2) | ~m1_subset_1(sK2,u1_struct_0(sK1)) | ~l1_orders_2(sK1) | ~v3_orders_2(sK1) | v2_struct_0(sK1)),
% 0.22/0.54    inference(resolution,[],[f136,f52])).
% 0.22/0.54  fof(f52,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f18])).
% 0.22/0.54  fof(f18,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.54    inference(flattening,[],[f17])).
% 0.22/0.54  fof(f17,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f6])).
% 0.22/0.54  fof(f6,axiom,(
% 0.22/0.54    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r1_orders_2(X0,X1,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_orders_2)).
% 0.22/0.54  fof(f136,plain,(
% 0.22/0.54    ~r1_orders_2(sK1,sK2,sK2) | k6_domain_1(u1_struct_0(sK1),sK2) = k2_tarski(sK2,sK2)),
% 0.22/0.54    inference(subsumption_resolution,[],[f132,f86])).
% 0.22/0.54  fof(f86,plain,(
% 0.22/0.54    sP0(sK2,sK2,sK1)),
% 0.22/0.54    inference(resolution,[],[f85,f48])).
% 0.22/0.54  fof(f85,plain,(
% 0.22/0.54    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | sP0(sK2,X0,sK1)) )),
% 0.22/0.54    inference(resolution,[],[f84,f48])).
% 0.22/0.54  fof(f84,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_subset_1(X1,u1_struct_0(sK1)) | sP0(X0,X1,sK1)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f83,f44])).
% 0.22/0.54  fof(f83,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_subset_1(X1,u1_struct_0(sK1)) | sP0(X0,X1,sK1) | ~v3_orders_2(sK1)) )),
% 0.22/0.54    inference(resolution,[],[f64,f47])).
% 0.22/0.54  fof(f64,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | sP0(X2,X1,X0) | ~v3_orders_2(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f37])).
% 0.22/0.54  fof(f37,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : ((sP0(X2,X1,X0) & (r1_orders_2(X0,X2,X1) | r1_orders_2(X0,X1,X2) | ! [X3] : (~r2_hidden(X2,X3) | ~r2_hidden(X1,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X3,X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_orders_2(X0))),
% 0.22/0.54    inference(rectify,[],[f29])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : ((sP0(X2,X1,X0) & (r1_orders_2(X0,X2,X1) | r1_orders_2(X0,X1,X2) | ! [X4] : (~r2_hidden(X2,X4) | ~r2_hidden(X1,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X4,X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_orders_2(X0))),
% 0.22/0.54    inference(definition_folding,[],[f22,f28])).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    ! [X2,X1,X0] : (? [X3] : (r2_hidden(X2,X3) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X3,X0)) | (~r1_orders_2(X0,X2,X1) & ~r1_orders_2(X0,X1,X2)) | ~sP0(X2,X1,X0))),
% 0.22/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : (((? [X3] : (r2_hidden(X2,X3) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X3,X0)) | (~r1_orders_2(X0,X2,X1) & ~r1_orders_2(X0,X1,X2))) & (r1_orders_2(X0,X2,X1) | r1_orders_2(X0,X1,X2) | ! [X4] : (~r2_hidden(X2,X4) | ~r2_hidden(X1,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X4,X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_orders_2(X0))),
% 0.22/0.54    inference(flattening,[],[f21])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : (((? [X3] : ((r2_hidden(X2,X3) & r2_hidden(X1,X3)) & (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X3,X0))) | (~r1_orders_2(X0,X2,X1) & ~r1_orders_2(X0,X1,X2))) & (r1_orders_2(X0,X2,X1) | r1_orders_2(X0,X1,X2) | ! [X4] : (~r2_hidden(X2,X4) | ~r2_hidden(X1,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X4,X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v3_orders_2(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f12])).
% 0.22/0.54  fof(f12,plain,(
% 0.22/0.54    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (~(! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X3,X0)) => ~(r2_hidden(X2,X3) & r2_hidden(X1,X3))) & (r1_orders_2(X0,X2,X1) | r1_orders_2(X0,X1,X2))) & ~(~r1_orders_2(X0,X2,X1) & ~r1_orders_2(X0,X1,X2) & ? [X4] : (r2_hidden(X2,X4) & r2_hidden(X1,X4) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X4,X0)))))))),
% 0.22/0.54    inference(rectify,[],[f8])).
% 0.22/0.54  fof(f8,axiom,(
% 0.22/0.54    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (~(! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X3,X0)) => ~(r2_hidden(X2,X3) & r2_hidden(X1,X3))) & (r1_orders_2(X0,X2,X1) | r1_orders_2(X0,X1,X2))) & ~(~r1_orders_2(X0,X2,X1) & ~r1_orders_2(X0,X1,X2) & ? [X3] : (r2_hidden(X2,X3) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X3,X0)))))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_orders_2)).
% 0.22/0.54  fof(f132,plain,(
% 0.22/0.54    k6_domain_1(u1_struct_0(sK1),sK2) = k2_tarski(sK2,sK2) | ~r1_orders_2(sK1,sK2,sK2) | ~sP0(sK2,sK2,sK1)),
% 0.22/0.54    inference(resolution,[],[f131,f60])).
% 0.22/0.54  fof(f60,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (r2_hidden(X1,sK3(X0,X1,X2)) | ~r1_orders_2(X2,X0,X1) | ~sP0(X0,X1,X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f36])).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((r2_hidden(X0,sK3(X0,X1,X2)) & r2_hidden(X1,sK3(X0,X1,X2)) & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) & v6_orders_2(sK3(X0,X1,X2),X2)) | (~r1_orders_2(X2,X0,X1) & ~r1_orders_2(X2,X1,X0)) | ~sP0(X0,X1,X2))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f34,f35])).
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    ! [X2,X1,X0] : (? [X3] : (r2_hidden(X0,X3) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) & v6_orders_2(X3,X2)) => (r2_hidden(X0,sK3(X0,X1,X2)) & r2_hidden(X1,sK3(X0,X1,X2)) & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) & v6_orders_2(sK3(X0,X1,X2),X2)))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f34,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (? [X3] : (r2_hidden(X0,X3) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) & v6_orders_2(X3,X2)) | (~r1_orders_2(X2,X0,X1) & ~r1_orders_2(X2,X1,X0)) | ~sP0(X0,X1,X2))),
% 0.22/0.54    inference(rectify,[],[f33])).
% 0.22/0.54  fof(f33,plain,(
% 0.22/0.54    ! [X2,X1,X0] : (? [X3] : (r2_hidden(X2,X3) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X3,X0)) | (~r1_orders_2(X0,X2,X1) & ~r1_orders_2(X0,X1,X2)) | ~sP0(X2,X1,X0))),
% 0.22/0.54    inference(nnf_transformation,[],[f28])).
% 0.22/0.54  fof(f131,plain,(
% 0.22/0.54    ( ! [X2] : (~r2_hidden(X2,sK3(sK2,sK2,sK1)) | k6_domain_1(u1_struct_0(sK1),sK2) = k2_tarski(sK2,sK2)) )),
% 0.22/0.54    inference(resolution,[],[f127,f48])).
% 0.22/0.54  fof(f127,plain,(
% 0.22/0.54    ( ! [X4,X5] : (~m1_subset_1(X4,u1_struct_0(sK1)) | k2_tarski(X4,X4) = k6_domain_1(u1_struct_0(sK1),X4) | ~r2_hidden(X5,sK3(sK2,sK2,sK1))) )),
% 0.22/0.54    inference(resolution,[],[f82,f93])).
% 0.22/0.54  fof(f93,plain,(
% 0.22/0.54    m1_subset_1(sK3(sK2,sK2,sK1),k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.22/0.54    inference(subsumption_resolution,[],[f92,f43])).
% 0.22/0.54  fof(f92,plain,(
% 0.22/0.54    m1_subset_1(sK3(sK2,sK2,sK1),k1_zfmisc_1(u1_struct_0(sK1))) | v2_struct_0(sK1)),
% 0.22/0.54    inference(subsumption_resolution,[],[f91,f44])).
% 0.22/0.54  fof(f91,plain,(
% 0.22/0.54    m1_subset_1(sK3(sK2,sK2,sK1),k1_zfmisc_1(u1_struct_0(sK1))) | ~v3_orders_2(sK1) | v2_struct_0(sK1)),
% 0.22/0.54    inference(subsumption_resolution,[],[f90,f47])).
% 0.22/0.54  fof(f90,plain,(
% 0.22/0.54    m1_subset_1(sK3(sK2,sK2,sK1),k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_orders_2(sK1) | ~v3_orders_2(sK1) | v2_struct_0(sK1)),
% 0.22/0.54    inference(subsumption_resolution,[],[f89,f48])).
% 0.22/0.54  fof(f89,plain,(
% 0.22/0.54    m1_subset_1(sK3(sK2,sK2,sK1),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(sK2,u1_struct_0(sK1)) | ~l1_orders_2(sK1) | ~v3_orders_2(sK1) | v2_struct_0(sK1)),
% 0.22/0.54    inference(resolution,[],[f87,f52])).
% 0.22/0.54  fof(f87,plain,(
% 0.22/0.54    ~r1_orders_2(sK1,sK2,sK2) | m1_subset_1(sK3(sK2,sK2,sK1),k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.22/0.54    inference(resolution,[],[f86,f58])).
% 0.22/0.54  fof(f58,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | ~r1_orders_2(X2,X0,X1) | m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2)))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f36])).
% 0.22/0.54  fof(f82,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X1)) | k2_tarski(X0,X0) = k6_domain_1(X1,X0) | ~m1_subset_1(X0,X1) | ~r2_hidden(X3,X2)) )),
% 0.22/0.54    inference(resolution,[],[f74,f73])).
% 0.22/0.54  fof(f73,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f27])).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f4])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.22/0.54  fof(f74,plain,(
% 0.22/0.54    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k2_tarski(X1,X1)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f65,f50])).
% 0.22/0.54  fof(f50,plain,(
% 0.22/0.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.54  fof(f65,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f24])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.22/0.54    inference(flattening,[],[f23])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f5])).
% 0.22/0.54  fof(f5,axiom,(
% 0.22/0.54    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.22/0.54  fof(f148,plain,(
% 0.22/0.54    ~m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.22/0.54    inference(subsumption_resolution,[],[f146,f76])).
% 0.22/0.54  fof(f76,plain,(
% 0.22/0.54    ( ! [X4,X0] : (r2_hidden(X4,k2_tarski(X0,X4))) )),
% 0.22/0.54    inference(equality_resolution,[],[f75])).
% 0.22/0.54  fof(f75,plain,(
% 0.22/0.54    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k2_tarski(X0,X4) != X2) )),
% 0.22/0.54    inference(equality_resolution,[],[f69])).
% 0.22/0.54  fof(f69,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 0.22/0.54    inference(cnf_transformation,[],[f42])).
% 0.22/0.54  fof(f42,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f40,f41])).
% 0.22/0.54  fof(f41,plain,(
% 0.22/0.54    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2))))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f40,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 0.22/0.54    inference(rectify,[],[f39])).
% 0.22/0.54  % (19716)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.54  fof(f39,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 0.22/0.54    inference(flattening,[],[f38])).
% 0.22/0.54  fof(f38,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 0.22/0.54    inference(nnf_transformation,[],[f1])).
% 0.22/0.54  % (19728)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 0.22/0.54  fof(f146,plain,(
% 0.22/0.54    ~r2_hidden(sK2,k2_tarski(sK2,sK2)) | ~m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.22/0.54    inference(backward_demodulation,[],[f120,f145])).
% 0.22/0.54  fof(f120,plain,(
% 0.22/0.54    ~r2_hidden(sK2,k6_domain_1(u1_struct_0(sK1),sK2)) | ~m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.22/0.54    inference(resolution,[],[f113,f49])).
% 0.22/0.54  fof(f49,plain,(
% 0.22/0.54    r2_hidden(sK2,k2_orders_2(sK1,k6_domain_1(u1_struct_0(sK1),sK2)))),
% 0.22/0.54    inference(cnf_transformation,[],[f32])).
% 0.22/0.54  fof(f113,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r2_hidden(X0,k2_orders_2(sK1,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | ~r2_hidden(X0,X1)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f112,f66])).
% 0.22/0.54  fof(f66,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f26])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.54    inference(flattening,[],[f25])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.22/0.54    inference(ennf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 0.22/0.54  fof(f112,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~r2_hidden(X0,k2_orders_2(sK1,X1))) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f111,f43])).
% 0.22/0.54  fof(f111,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~r2_hidden(X0,k2_orders_2(sK1,X1)) | v2_struct_0(sK1)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f110,f44])).
% 0.22/0.54  fof(f110,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~r2_hidden(X0,k2_orders_2(sK1,X1)) | ~v3_orders_2(sK1) | v2_struct_0(sK1)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f109,f45])).
% 0.22/0.54  fof(f45,plain,(
% 0.22/0.54    v4_orders_2(sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f32])).
% 0.22/0.54  fof(f109,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~r2_hidden(X0,k2_orders_2(sK1,X1)) | ~v4_orders_2(sK1) | ~v3_orders_2(sK1) | v2_struct_0(sK1)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f108,f47])).
% 0.22/0.54  fof(f108,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~l1_orders_2(sK1) | ~r2_hidden(X0,k2_orders_2(sK1,X1)) | ~v4_orders_2(sK1) | ~v3_orders_2(sK1) | v2_struct_0(sK1)) )),
% 0.22/0.54    inference(resolution,[],[f51,f46])).
% 0.22/0.54  fof(f46,plain,(
% 0.22/0.54    v5_orders_2(sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f32])).
% 0.22/0.54  fof(f51,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~v5_orders_2(X0) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~r2_hidden(X1,k2_orders_2(X0,X2)) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f16])).
% 0.22/0.54  fof(f16,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : (~r2_hidden(X1,k2_orders_2(X0,X2)) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.54    inference(flattening,[],[f15])).
% 0.22/0.54  fof(f15,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : ((~r2_hidden(X1,k2_orders_2(X0,X2)) | ~r2_hidden(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f9])).
% 0.22/0.54  fof(f9,axiom,(
% 0.22/0.54    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(r2_hidden(X1,k2_orders_2(X0,X2)) & r2_hidden(X1,X2)))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_orders_2)).
% 0.22/0.54  fof(f169,plain,(
% 0.22/0.54    m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(sK2,u1_struct_0(sK1)) | ~l1_orders_2(sK1) | ~v3_orders_2(sK1) | v2_struct_0(sK1)),
% 0.22/0.54    inference(superposition,[],[f54,f145])).
% 0.22/0.54  fof(f54,plain,(
% 0.22/0.54    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f20])).
% 0.22/0.54  fof(f20,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : ((m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.54    inference(flattening,[],[f19])).
% 0.22/0.54  fof(f19,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : ((m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f7])).
% 0.22/0.54  fof(f7,axiom,(
% 0.22/0.54    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_orders_2)).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (19721)------------------------------
% 0.22/0.54  % (19721)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (19721)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (19721)Memory used [KB]: 6396
% 0.22/0.54  % (19721)Time elapsed: 0.086 s
% 0.22/0.54  % (19721)------------------------------
% 0.22/0.54  % (19721)------------------------------
% 0.22/0.54  % (19728)Refutation not found, incomplete strategy% (19728)------------------------------
% 0.22/0.54  % (19728)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (19725)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (19698)Success in time 0.18 s
%------------------------------------------------------------------------------
