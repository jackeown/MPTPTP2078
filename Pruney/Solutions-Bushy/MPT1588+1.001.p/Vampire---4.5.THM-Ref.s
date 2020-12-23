%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1588+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:10 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 181 expanded)
%              Number of leaves         :    8 (  37 expanded)
%              Depth                    :   19
%              Number of atoms          :  287 (1419 expanded)
%              Number of equality atoms :   10 ( 102 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f197,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f101,f120,f179,f196])).

fof(f196,plain,(
    spl5_8 ),
    inference(avatar_contradiction_clause,[],[f195])).

fof(f195,plain,
    ( $false
    | spl5_8 ),
    inference(subsumption_resolution,[],[f194,f14])).

fof(f14,plain,(
    m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( k1_yellow_0(X0,k7_domain_1(u1_struct_0(X1),X2,X3)) != k1_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3))
                    | ~ r1_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3)) )
                  & r2_hidden(k1_yellow_0(X0,k7_domain_1(u1_struct_0(X1),X2,X3)),u1_struct_0(X1))
                  & r1_yellow_0(X0,k7_domain_1(u1_struct_0(X1),X2,X3))
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & m1_yellow_0(X1,X0)
          & v4_yellow_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( k1_yellow_0(X0,k7_domain_1(u1_struct_0(X1),X2,X3)) != k1_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3))
                    | ~ r1_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3)) )
                  & r2_hidden(k1_yellow_0(X0,k7_domain_1(u1_struct_0(X1),X2,X3)),u1_struct_0(X1))
                  & r1_yellow_0(X0,k7_domain_1(u1_struct_0(X1),X2,X3))
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & m1_yellow_0(X1,X0)
          & v4_yellow_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v4_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_yellow_0(X1,X0)
              & v4_yellow_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X1))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X1))
                   => ( ( r2_hidden(k1_yellow_0(X0,k7_domain_1(u1_struct_0(X1),X2,X3)),u1_struct_0(X1))
                        & r1_yellow_0(X0,k7_domain_1(u1_struct_0(X1),X2,X3)) )
                     => ( k1_yellow_0(X0,k7_domain_1(u1_struct_0(X1),X2,X3)) = k1_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3))
                        & r1_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3)) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_yellow_0(X1,X0)
            & v4_yellow_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                 => ( ( r2_hidden(k1_yellow_0(X0,k7_domain_1(u1_struct_0(X1),X2,X3)),u1_struct_0(X1))
                      & r1_yellow_0(X0,k7_domain_1(u1_struct_0(X1),X2,X3)) )
                   => ( k1_yellow_0(X0,k7_domain_1(u1_struct_0(X1),X2,X3)) = k1_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3))
                      & r1_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_yellow_0)).

fof(f194,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | spl5_8 ),
    inference(subsumption_resolution,[],[f193,f17])).

fof(f17,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f193,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | spl5_8 ),
    inference(subsumption_resolution,[],[f185,f78])).

fof(f78,plain,(
    ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(resolution,[],[f16,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(f16,plain,(
    r2_hidden(k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f185,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | spl5_8 ),
    inference(resolution,[],[f178,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | ~ m1_subset_1(X2,X0)
      | m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,X0)
        & m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_domain_1)).

fof(f178,plain,
    ( ~ m1_subset_1(k7_domain_1(u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | spl5_8 ),
    inference(avatar_component_clause,[],[f176])).

fof(f176,plain,
    ( spl5_8
  <=> m1_subset_1(k7_domain_1(u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f179,plain,
    ( spl5_2
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f85,f176,f98])).

fof(f98,plain,
    ( spl5_2
  <=> r1_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f85,plain,
    ( ~ m1_subset_1(k7_domain_1(u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) ),
    inference(subsumption_resolution,[],[f84,f15])).

fof(f15,plain,(
    r1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) ),
    inference(cnf_transformation,[],[f7])).

fof(f84,plain,
    ( ~ m1_subset_1(k7_domain_1(u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3))
    | r1_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) ),
    inference(subsumption_resolution,[],[f83,f20])).

fof(f20,plain,(
    m1_yellow_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f83,plain,
    ( ~ m1_yellow_0(sK1,sK0)
    | ~ m1_subset_1(k7_domain_1(u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3))
    | r1_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) ),
    inference(subsumption_resolution,[],[f82,f19])).

fof(f19,plain,(
    v4_yellow_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f82,plain,
    ( ~ v4_yellow_0(sK1,sK0)
    | ~ m1_yellow_0(sK1,sK0)
    | ~ m1_subset_1(k7_domain_1(u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3))
    | r1_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) ),
    inference(subsumption_resolution,[],[f81,f18])).

fof(f18,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f81,plain,
    ( v2_struct_0(sK1)
    | ~ v4_yellow_0(sK1,sK0)
    | ~ m1_yellow_0(sK1,sK0)
    | ~ m1_subset_1(k7_domain_1(u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3))
    | r1_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) ),
    inference(subsumption_resolution,[],[f80,f23])).

fof(f23,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f80,plain,
    ( ~ l1_orders_2(sK0)
    | v2_struct_0(sK1)
    | ~ v4_yellow_0(sK1,sK0)
    | ~ m1_yellow_0(sK1,sK0)
    | ~ m1_subset_1(k7_domain_1(u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3))
    | r1_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) ),
    inference(subsumption_resolution,[],[f79,f22])).

fof(f22,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f79,plain,
    ( ~ v4_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK1)
    | ~ v4_yellow_0(sK1,sK0)
    | ~ m1_yellow_0(sK1,sK0)
    | ~ m1_subset_1(k7_domain_1(u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3))
    | r1_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) ),
    inference(subsumption_resolution,[],[f76,f21])).

fof(f21,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f76,plain,
    ( v2_struct_0(sK0)
    | ~ v4_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK1)
    | ~ v4_yellow_0(sK1,sK0)
    | ~ m1_yellow_0(sK1,sK0)
    | ~ m1_subset_1(k7_domain_1(u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3))
    | r1_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) ),
    inference(resolution,[],[f16,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v4_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X1)
      | ~ v4_yellow_0(X1,X0)
      | ~ m1_yellow_0(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r1_yellow_0(X0,X2)
      | ~ r2_hidden(k1_yellow_0(X0,X2),u1_struct_0(X1))
      | r1_yellow_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2)
                & r1_yellow_0(X1,X2) )
              | ~ r2_hidden(k1_yellow_0(X0,X2),u1_struct_0(X1))
              | ~ r1_yellow_0(X0,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_yellow_0(X1,X0)
          | ~ v4_yellow_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2)
                & r1_yellow_0(X1,X2) )
              | ~ r2_hidden(k1_yellow_0(X0,X2),u1_struct_0(X1))
              | ~ r1_yellow_0(X0,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_yellow_0(X1,X0)
          | ~ v4_yellow_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_yellow_0(X1,X0)
            & v4_yellow_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( r2_hidden(k1_yellow_0(X0,X2),u1_struct_0(X1))
                  & r1_yellow_0(X0,X2) )
               => ( k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2)
                  & r1_yellow_0(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_yellow_0)).

fof(f120,plain,(
    spl5_1 ),
    inference(avatar_contradiction_clause,[],[f119])).

fof(f119,plain,
    ( $false
    | spl5_1 ),
    inference(subsumption_resolution,[],[f118,f14])).

fof(f118,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | spl5_1 ),
    inference(subsumption_resolution,[],[f117,f17])).

fof(f117,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | spl5_1 ),
    inference(subsumption_resolution,[],[f115,f78])).

fof(f115,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | spl5_1 ),
    inference(resolution,[],[f113,f27])).

fof(f113,plain,
    ( ~ m1_subset_1(k7_domain_1(u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | spl5_1 ),
    inference(subsumption_resolution,[],[f112,f16])).

fof(f112,plain,
    ( ~ m1_subset_1(k7_domain_1(u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)),u1_struct_0(sK1))
    | spl5_1 ),
    inference(subsumption_resolution,[],[f111,f15])).

fof(f111,plain,
    ( ~ m1_subset_1(k7_domain_1(u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3))
    | ~ r2_hidden(k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)),u1_struct_0(sK1))
    | spl5_1 ),
    inference(subsumption_resolution,[],[f110,f20])).

fof(f110,plain,
    ( ~ m1_yellow_0(sK1,sK0)
    | ~ m1_subset_1(k7_domain_1(u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3))
    | ~ r2_hidden(k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)),u1_struct_0(sK1))
    | spl5_1 ),
    inference(subsumption_resolution,[],[f109,f19])).

fof(f109,plain,
    ( ~ v4_yellow_0(sK1,sK0)
    | ~ m1_yellow_0(sK1,sK0)
    | ~ m1_subset_1(k7_domain_1(u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3))
    | ~ r2_hidden(k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)),u1_struct_0(sK1))
    | spl5_1 ),
    inference(subsumption_resolution,[],[f108,f18])).

fof(f108,plain,
    ( v2_struct_0(sK1)
    | ~ v4_yellow_0(sK1,sK0)
    | ~ m1_yellow_0(sK1,sK0)
    | ~ m1_subset_1(k7_domain_1(u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3))
    | ~ r2_hidden(k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)),u1_struct_0(sK1))
    | spl5_1 ),
    inference(subsumption_resolution,[],[f107,f23])).

fof(f107,plain,
    ( ~ l1_orders_2(sK0)
    | v2_struct_0(sK1)
    | ~ v4_yellow_0(sK1,sK0)
    | ~ m1_yellow_0(sK1,sK0)
    | ~ m1_subset_1(k7_domain_1(u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3))
    | ~ r2_hidden(k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)),u1_struct_0(sK1))
    | spl5_1 ),
    inference(subsumption_resolution,[],[f106,f22])).

fof(f106,plain,
    ( ~ v4_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK1)
    | ~ v4_yellow_0(sK1,sK0)
    | ~ m1_yellow_0(sK1,sK0)
    | ~ m1_subset_1(k7_domain_1(u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3))
    | ~ r2_hidden(k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)),u1_struct_0(sK1))
    | spl5_1 ),
    inference(subsumption_resolution,[],[f103,f21])).

fof(f103,plain,
    ( v2_struct_0(sK0)
    | ~ v4_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK1)
    | ~ v4_yellow_0(sK1,sK0)
    | ~ m1_yellow_0(sK1,sK0)
    | ~ m1_subset_1(k7_domain_1(u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3))
    | ~ r2_hidden(k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)),u1_struct_0(sK1))
    | spl5_1 ),
    inference(resolution,[],[f96,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v4_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X1)
      | ~ v4_yellow_0(X1,X0)
      | ~ m1_yellow_0(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r1_yellow_0(X0,X2)
      | ~ r2_hidden(k1_yellow_0(X0,X2),u1_struct_0(X1))
      | sQ4_eqProxy(k1_yellow_0(X0,X2),k1_yellow_0(X1,X2)) ) ),
    inference(equality_proxy_replacement,[],[f25,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( sQ4_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ4_eqProxy])])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v4_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X1)
      | ~ v4_yellow_0(X1,X0)
      | ~ m1_yellow_0(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r1_yellow_0(X0,X2)
      | ~ r2_hidden(k1_yellow_0(X0,X2),u1_struct_0(X1))
      | k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f96,plain,
    ( ~ sQ4_eqProxy(k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)),k1_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,sK3)))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl5_1
  <=> sQ4_eqProxy(k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)),k1_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f101,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f29,f98,f94])).

fof(f29,plain,
    ( ~ r1_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,sK3))
    | ~ sQ4_eqProxy(k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)),k1_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,sK3))) ),
    inference(equality_proxy_replacement,[],[f13,f28])).

fof(f13,plain,
    ( ~ r1_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,sK3))
    | k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) != k1_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) ),
    inference(cnf_transformation,[],[f7])).

%------------------------------------------------------------------------------
