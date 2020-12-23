%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:15 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   84 (1362 expanded)
%              Number of leaves         :   15 ( 627 expanded)
%              Depth                    :   15
%              Number of atoms          :  546 (12305 expanded)
%              Number of equality atoms :   48 (3150 expanded)
%              Maximal formula depth    :   18 (   8 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f164,plain,(
    $false ),
    inference(subsumption_resolution,[],[f162,f158])).

fof(f158,plain,(
    r3_orders_2(sK0,sK1,sK4(k3_orders_2(sK0,sK3,sK1))) ),
    inference(unit_resulting_resolution,[],[f142,f138,f50,f121])).

fof(f121,plain,(
    ! [X0,X1] :
      ( ~ m2_orders_2(X1,sK0,sK2)
      | ~ r2_hidden(X0,X1)
      | r3_orders_2(sK0,sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f120,f43])).

fof(f43,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( k1_xboole_0 != k3_orders_2(sK0,sK3,sK1)
    & sK1 = k1_funct_1(sK2,u1_struct_0(sK0))
    & m2_orders_2(sK3,sK0,sK2)
    & m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f34,f33,f32,f31])).

fof(f31,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( k1_xboole_0 != k3_orders_2(X0,X3,X1)
                    & k1_funct_1(X2,u1_struct_0(X0)) = X1
                    & m2_orders_2(X3,X0,X2) )
                & m1_orders_1(X2,k1_orders_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k1_xboole_0 != k3_orders_2(sK0,X3,X1)
                  & k1_funct_1(X2,u1_struct_0(sK0)) = X1
                  & m2_orders_2(X3,sK0,X2) )
              & m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( k1_xboole_0 != k3_orders_2(sK0,X3,X1)
                & k1_funct_1(X2,u1_struct_0(sK0)) = X1
                & m2_orders_2(X3,sK0,X2) )
            & m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ? [X3] :
              ( k1_xboole_0 != k3_orders_2(sK0,X3,sK1)
              & k1_funct_1(X2,u1_struct_0(sK0)) = sK1
              & m2_orders_2(X3,sK0,X2) )
          & m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( k1_xboole_0 != k3_orders_2(sK0,X3,sK1)
            & k1_funct_1(X2,u1_struct_0(sK0)) = sK1
            & m2_orders_2(X3,sK0,X2) )
        & m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0))) )
   => ( ? [X3] :
          ( k1_xboole_0 != k3_orders_2(sK0,X3,sK1)
          & sK1 = k1_funct_1(sK2,u1_struct_0(sK0))
          & m2_orders_2(X3,sK0,sK2) )
      & m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X3] :
        ( k1_xboole_0 != k3_orders_2(sK0,X3,sK1)
        & sK1 = k1_funct_1(sK2,u1_struct_0(sK0))
        & m2_orders_2(X3,sK0,sK2) )
   => ( k1_xboole_0 != k3_orders_2(sK0,sK3,sK1)
      & sK1 = k1_funct_1(sK2,u1_struct_0(sK0))
      & m2_orders_2(sK3,sK0,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k1_xboole_0 != k3_orders_2(X0,X3,X1)
                  & k1_funct_1(X2,u1_struct_0(X0)) = X1
                  & m2_orders_2(X3,X0,X2) )
              & m1_orders_1(X2,k1_orders_1(u1_struct_0(X0))) )
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
          ( ? [X2] :
              ( ? [X3] :
                  ( k1_xboole_0 != k3_orders_2(X0,X3,X1)
                  & k1_funct_1(X2,u1_struct_0(X0)) = X1
                  & m2_orders_2(X3,X0,X2) )
              & m1_orders_1(X2,k1_orders_1(u1_struct_0(X0))) )
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
           => ! [X2] :
                ( m1_orders_1(X2,k1_orders_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m2_orders_2(X3,X0,X2)
                   => ( k1_funct_1(X2,u1_struct_0(X0)) = X1
                     => k1_xboole_0 = k3_orders_2(X0,X3,X1) ) ) ) ) ) ),
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
         => ! [X2] :
              ( m1_orders_1(X2,k1_orders_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m2_orders_2(X3,X0,X2)
                 => ( k1_funct_1(X2,u1_struct_0(X0)) = X1
                   => k1_xboole_0 = k3_orders_2(X0,X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_orders_2)).

fof(f120,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m2_orders_2(X1,sK0,sK2)
      | r3_orders_2(sK0,sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f119,f44])).

fof(f44,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f119,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m2_orders_2(X1,sK0,sK2)
      | r3_orders_2(sK0,sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f118,f45])).

fof(f45,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f118,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m2_orders_2(X1,sK0,sK2)
      | r3_orders_2(sK0,sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f117,f46])).

fof(f46,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f117,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m2_orders_2(X1,sK0,sK2)
      | r3_orders_2(sK0,sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f116,f47])).

fof(f47,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f116,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m2_orders_2(X1,sK0,sK2)
      | r3_orders_2(sK0,sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f115,f49])).

fof(f49,plain,(
    m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f35])).

fof(f115,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m2_orders_2(X1,sK0,sK2)
      | ~ m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK0)))
      | r3_orders_2(sK0,sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f114,f48])).

fof(f48,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f35])).

fof(f114,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | ~ r2_hidden(X0,X1)
      | ~ m2_orders_2(X1,sK0,sK2)
      | ~ m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK0)))
      | r3_orders_2(sK0,sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f71,f51])).

fof(f51,plain,(
    sK1 = k1_funct_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f35])).

fof(f71,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ m1_subset_1(k1_funct_1(X3,u1_struct_0(X0)),u1_struct_0(X0))
      | ~ r2_hidden(X1,X4)
      | ~ m2_orders_2(X4,X0,X3)
      | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X0)))
      | r3_orders_2(X0,k1_funct_1(X3,u1_struct_0(X0)),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r3_orders_2(X0,X2,X1)
      | k1_funct_1(X3,u1_struct_0(X0)) != X2
      | ~ r2_hidden(X1,X4)
      | ~ m2_orders_2(X4,X0,X3)
      | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r3_orders_2(X0,X2,X1)
                      | k1_funct_1(X3,u1_struct_0(X0)) != X2
                      | ~ r2_hidden(X1,X4)
                      | ~ m2_orders_2(X4,X0,X3) )
                  | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r3_orders_2(X0,X2,X1)
                      | k1_funct_1(X3,u1_struct_0(X0)) != X2
                      | ~ r2_hidden(X1,X4)
                      | ~ m2_orders_2(X4,X0,X3) )
                  | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
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
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_orders_1(X3,k1_orders_1(u1_struct_0(X0)))
                 => ! [X4] :
                      ( m2_orders_2(X4,X0,X3)
                     => ( ( k1_funct_1(X3,u1_struct_0(X0)) = X2
                          & r2_hidden(X1,X4) )
                       => r3_orders_2(X0,X2,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_orders_2)).

fof(f50,plain,(
    m2_orders_2(sK3,sK0,sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f138,plain,(
    m1_subset_1(sK4(k3_orders_2(sK0,sK3,sK1)),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f122,f111,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f111,plain,(
    m1_subset_1(k3_orders_2(sK0,sK3,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f43,f44,f45,f46,f47,f48,f110,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_orders_2)).

% (9162)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
fof(f110,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f43,f44,f45,f46,f47,f50,f49,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m2_orders_2(X2,X0,X1) )
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m2_orders_2(X2,X0,X1) )
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m2_orders_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m2_orders_2(X2,X0,X1)
         => ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_orders_2)).

fof(f122,plain,(
    r2_hidden(sK4(k3_orders_2(sK0,sK3,sK1)),k3_orders_2(sK0,sK3,sK1)) ),
    inference(unit_resulting_resolution,[],[f52,f62])).

fof(f62,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ( ! [X2,X3] :
            ( k4_tarski(X2,X3) != sK4(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK4(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f40])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] :
            ( k4_tarski(X2,X3) != sK4(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK4(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3] :
                  ~ ( k4_tarski(X2,X3) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

fof(f52,plain,(
    k1_xboole_0 != k3_orders_2(sK0,sK3,sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f142,plain,(
    r2_hidden(sK4(k3_orders_2(sK0,sK3,sK1)),sK3) ),
    inference(unit_resulting_resolution,[],[f43,f44,f45,f46,f47,f48,f110,f122,f138,f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v5_orders_2(X0)
      | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_hidden(X1,X3)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

% (9167)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_orders_2)).

fof(f162,plain,(
    ~ r3_orders_2(sK0,sK1,sK4(k3_orders_2(sK0,sK3,sK1))) ),
    inference(unit_resulting_resolution,[],[f43,f44,f47,f48,f138,f154,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_orders_2(X0)
      | ~ r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_orders_2(X0,X1,X2)
          | ~ r1_orders_2(X0,X1,X2) )
        & ( r1_orders_2(X0,X1,X2)
          | ~ r3_orders_2(X0,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

% (9157)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
fof(f154,plain,(
    ~ r1_orders_2(sK0,sK1,sK4(k3_orders_2(sK0,sK3,sK1))) ),
    inference(unit_resulting_resolution,[],[f45,f46,f47,f109,f48,f48,f138,f141,f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v5_orders_2(X0)
      | ~ r2_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_orders_2(X0,X1,X3)
      | ~ v4_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_orders_2(X0,X1,X3)
                  | ( ( ~ r2_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X2) )
                    & ( ~ r1_orders_2(X0,X2,X3)
                      | ~ r2_orders_2(X0,X1,X2) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_orders_2(X0,X1,X3)
                  | ( ( ~ r2_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X2) )
                    & ( ~ r1_orders_2(X0,X2,X3)
                      | ~ r2_orders_2(X0,X1,X2) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( ( r2_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X2) )
                      | ( r1_orders_2(X0,X2,X3)
                        & r2_orders_2(X0,X1,X2) ) )
                   => r2_orders_2(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_orders_2)).

fof(f141,plain,(
    r2_orders_2(sK0,sK4(k3_orders_2(sK0,sK3,sK1)),sK1) ),
    inference(unit_resulting_resolution,[],[f43,f44,f45,f46,f47,f48,f110,f122,f138,f57])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v5_orders_2(X0)
      | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_orders_2(X0,X1,X2)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f109,plain,(
    ~ r2_orders_2(sK0,sK1,sK1) ),
    inference(unit_resulting_resolution,[],[f47,f48,f72])).

fof(f72,plain,(
    ! [X2,X0] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_orders_2(X0,X2,X2) ) ),
    inference(duplicate_literal_removal,[],[f70])).

fof(f70,plain,(
    ! [X2,X0] :
      ( ~ r2_orders_2(X0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( X1 != X2
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_orders_2(X0,X1,X2)
                  | X1 = X2
                  | ~ r1_orders_2(X0,X1,X2) )
                & ( ( X1 != X2
                    & r1_orders_2(X0,X1,X2) )
                  | ~ r2_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_orders_2(X0,X1,X2)
                  | X1 = X2
                  | ~ r1_orders_2(X0,X1,X2) )
                & ( ( X1 != X2
                    & r1_orders_2(X0,X1,X2) )
                  | ~ r2_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_orders_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:08:24 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.44  % (9173)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.45  % (9168)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.46  % (9160)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.47  % (9168)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f164,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(subsumption_resolution,[],[f162,f158])).
% 0.21/0.47  fof(f158,plain,(
% 0.21/0.47    r3_orders_2(sK0,sK1,sK4(k3_orders_2(sK0,sK3,sK1)))),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f142,f138,f50,f121])).
% 0.21/0.47  fof(f121,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m2_orders_2(X1,sK0,sK2) | ~r2_hidden(X0,X1) | r3_orders_2(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f120,f43])).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    ~v2_struct_0(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f35])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    (((k1_xboole_0 != k3_orders_2(sK0,sK3,sK1) & sK1 = k1_funct_1(sK2,u1_struct_0(sK0)) & m2_orders_2(sK3,sK0,sK2)) & m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f34,f33,f32,f31])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (k1_xboole_0 != k3_orders_2(X0,X3,X1) & k1_funct_1(X2,u1_struct_0(X0)) = X1 & m2_orders_2(X3,X0,X2)) & m1_orders_1(X2,k1_orders_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (k1_xboole_0 != k3_orders_2(sK0,X3,X1) & k1_funct_1(X2,u1_struct_0(sK0)) = X1 & m2_orders_2(X3,sK0,X2)) & m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0)))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ? [X1] : (? [X2] : (? [X3] : (k1_xboole_0 != k3_orders_2(sK0,X3,X1) & k1_funct_1(X2,u1_struct_0(sK0)) = X1 & m2_orders_2(X3,sK0,X2)) & m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0)))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (? [X3] : (k1_xboole_0 != k3_orders_2(sK0,X3,sK1) & k1_funct_1(X2,u1_struct_0(sK0)) = sK1 & m2_orders_2(X3,sK0,X2)) & m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    ? [X2] : (? [X3] : (k1_xboole_0 != k3_orders_2(sK0,X3,sK1) & k1_funct_1(X2,u1_struct_0(sK0)) = sK1 & m2_orders_2(X3,sK0,X2)) & m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0)))) => (? [X3] : (k1_xboole_0 != k3_orders_2(sK0,X3,sK1) & sK1 = k1_funct_1(sK2,u1_struct_0(sK0)) & m2_orders_2(X3,sK0,sK2)) & m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK0))))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    ? [X3] : (k1_xboole_0 != k3_orders_2(sK0,X3,sK1) & sK1 = k1_funct_1(sK2,u1_struct_0(sK0)) & m2_orders_2(X3,sK0,sK2)) => (k1_xboole_0 != k3_orders_2(sK0,sK3,sK1) & sK1 = k1_funct_1(sK2,u1_struct_0(sK0)) & m2_orders_2(sK3,sK0,sK2))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (k1_xboole_0 != k3_orders_2(X0,X3,X1) & k1_funct_1(X2,u1_struct_0(X0)) = X1 & m2_orders_2(X3,X0,X2)) & m1_orders_1(X2,k1_orders_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((k1_xboole_0 != k3_orders_2(X0,X3,X1) & k1_funct_1(X2,u1_struct_0(X0)) = X1) & m2_orders_2(X3,X0,X2)) & m1_orders_1(X2,k1_orders_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,negated_conjecture,(
% 0.21/0.47    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_orders_1(X2,k1_orders_1(u1_struct_0(X0))) => ! [X3] : (m2_orders_2(X3,X0,X2) => (k1_funct_1(X2,u1_struct_0(X0)) = X1 => k1_xboole_0 = k3_orders_2(X0,X3,X1))))))),
% 0.21/0.47    inference(negated_conjecture,[],[f10])).
% 0.21/0.47  fof(f10,conjecture,(
% 0.21/0.47    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_orders_1(X2,k1_orders_1(u1_struct_0(X0))) => ! [X3] : (m2_orders_2(X3,X0,X2) => (k1_funct_1(X2,u1_struct_0(X0)) = X1 => k1_xboole_0 = k3_orders_2(X0,X3,X1))))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_orders_2)).
% 0.21/0.47  fof(f120,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~m2_orders_2(X1,sK0,sK2) | r3_orders_2(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f119,f44])).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    v3_orders_2(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f35])).
% 0.21/0.47  fof(f119,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~m2_orders_2(X1,sK0,sK2) | r3_orders_2(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f118,f45])).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    v4_orders_2(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f35])).
% 0.21/0.47  fof(f118,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~m2_orders_2(X1,sK0,sK2) | r3_orders_2(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f117,f46])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    v5_orders_2(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f35])).
% 0.21/0.47  fof(f117,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~m2_orders_2(X1,sK0,sK2) | r3_orders_2(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f116,f47])).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    l1_orders_2(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f35])).
% 0.21/0.47  fof(f116,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~m2_orders_2(X1,sK0,sK2) | r3_orders_2(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f115,f49])).
% 0.21/0.47  fof(f49,plain,(
% 0.21/0.47    m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK0)))),
% 0.21/0.47    inference(cnf_transformation,[],[f35])).
% 0.21/0.47  fof(f115,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~m2_orders_2(X1,sK0,sK2) | ~m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK0))) | r3_orders_2(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f114,f48])).
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.47    inference(cnf_transformation,[],[f35])).
% 0.21/0.47  fof(f114,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_subset_1(sK1,u1_struct_0(sK0)) | ~r2_hidden(X0,X1) | ~m2_orders_2(X1,sK0,sK2) | ~m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK0))) | r3_orders_2(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.47    inference(superposition,[],[f71,f51])).
% 0.21/0.47  fof(f51,plain,(
% 0.21/0.47    sK1 = k1_funct_1(sK2,u1_struct_0(sK0))),
% 0.21/0.47    inference(cnf_transformation,[],[f35])).
% 0.21/0.47  fof(f71,plain,(
% 0.21/0.47    ( ! [X4,X0,X3,X1] : (~m1_subset_1(k1_funct_1(X3,u1_struct_0(X0)),u1_struct_0(X0)) | ~r2_hidden(X1,X4) | ~m2_orders_2(X4,X0,X3) | ~m1_orders_1(X3,k1_orders_1(u1_struct_0(X0))) | r3_orders_2(X0,k1_funct_1(X3,u1_struct_0(X0)),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(equality_resolution,[],[f56])).
% 0.21/0.47  fof(f56,plain,(
% 0.21/0.47    ( ! [X4,X2,X0,X3,X1] : (r3_orders_2(X0,X2,X1) | k1_funct_1(X3,u1_struct_0(X0)) != X2 | ~r2_hidden(X1,X4) | ~m2_orders_2(X4,X0,X3) | ~m1_orders_1(X3,k1_orders_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r3_orders_2(X0,X2,X1) | k1_funct_1(X3,u1_struct_0(X0)) != X2 | ~r2_hidden(X1,X4) | ~m2_orders_2(X4,X0,X3)) | ~m1_orders_1(X3,k1_orders_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((r3_orders_2(X0,X2,X1) | (k1_funct_1(X3,u1_struct_0(X0)) != X2 | ~r2_hidden(X1,X4))) | ~m2_orders_2(X4,X0,X3)) | ~m1_orders_1(X3,k1_orders_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,axiom,(
% 0.21/0.47    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_orders_1(X3,k1_orders_1(u1_struct_0(X0))) => ! [X4] : (m2_orders_2(X4,X0,X3) => ((k1_funct_1(X3,u1_struct_0(X0)) = X2 & r2_hidden(X1,X4)) => r3_orders_2(X0,X2,X1)))))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_orders_2)).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    m2_orders_2(sK3,sK0,sK2)),
% 0.21/0.47    inference(cnf_transformation,[],[f35])).
% 0.21/0.47  fof(f138,plain,(
% 0.21/0.47    m1_subset_1(sK4(k3_orders_2(sK0,sK3,sK1)),u1_struct_0(sK0))),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f122,f111,f69])).
% 0.21/0.47  fof(f69,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f30])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.47    inference(flattening,[],[f29])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.21/0.47    inference(ennf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 0.21/0.47  fof(f111,plain,(
% 0.21/0.47    m1_subset_1(k3_orders_2(sK0,sK3,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f43,f44,f45,f46,f47,f48,f110,f66])).
% 0.21/0.47  fof(f66,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f26])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_orders_2)).
% 0.21/0.47  % (9162)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.47  fof(f110,plain,(
% 0.21/0.47    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f43,f44,f45,f46,f47,f50,f49,f65])).
% 0.21/0.47  fof(f65,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~v5_orders_2(X0) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f24])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f23])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1)) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_orders_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.47    inference(pure_predicate_removal,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_orders_2(X2,X0,X1) => (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_orders_2)).
% 0.21/0.47  fof(f122,plain,(
% 0.21/0.47    r2_hidden(sK4(k3_orders_2(sK0,sK3,sK1)),k3_orders_2(sK0,sK3,sK1))),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f52,f62])).
% 0.21/0.47  fof(f62,plain,(
% 0.21/0.47    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f41])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    ! [X0] : ((! [X2,X3] : (k4_tarski(X2,X3) != sK4(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK4(X0),X0)) | k1_xboole_0 = X0)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f40])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X3,X2] : (k4_tarski(X2,X3) != sK4(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK4(X0),X0)))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0] : ~(! [X1] : ~(! [X2,X3] : ~(k4_tarski(X2,X3) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).
% 0.21/0.47  fof(f52,plain,(
% 0.21/0.47    k1_xboole_0 != k3_orders_2(sK0,sK3,sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f35])).
% 0.21/0.47  fof(f142,plain,(
% 0.21/0.47    r2_hidden(sK4(k3_orders_2(sK0,sK3,sK1)),sK3)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f43,f44,f45,f46,f47,f48,f110,f122,f138,f58])).
% 0.21/0.47  fof(f58,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (~v5_orders_2(X0) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | r2_hidden(X1,X3) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f39])).
% 0.21/0.48  % (9167)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2)) & ((r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f38])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((r2_hidden(X1,k3_orders_2(X0,X3,X2)) | (~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2))) & ((r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(nnf_transformation,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)))))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_orders_2)).
% 0.21/0.48  fof(f162,plain,(
% 0.21/0.48    ~r3_orders_2(sK0,sK1,sK4(k3_orders_2(sK0,sK3,sK1)))),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f43,f44,f47,f48,f138,f154,f67])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~v3_orders_2(X0) | ~r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_orders_2(X0,X1,X2) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f42])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(nnf_transformation,[],[f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).
% 0.21/0.48  % (9157)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.48  fof(f154,plain,(
% 0.21/0.48    ~r1_orders_2(sK0,sK1,sK4(k3_orders_2(sK0,sK3,sK1)))),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f45,f46,f47,f109,f48,f48,f138,f141,f61])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (~v5_orders_2(X0) | ~r2_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | r2_orders_2(X0,X1,X3) | ~v4_orders_2(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_orders_2(X0,X1,X3) | ((~r2_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X2)) & (~r1_orders_2(X0,X2,X3) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0))),
% 0.21/0.48    inference(flattening,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_orders_2(X0,X1,X3) | ((~r2_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X2)) & (~r1_orders_2(X0,X2,X3) | ~r2_orders_2(X0,X1,X2)))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (((r2_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X2)) | (r1_orders_2(X0,X2,X3) & r2_orders_2(X0,X1,X2))) => r2_orders_2(X0,X1,X3))))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_orders_2)).
% 0.21/0.48  fof(f141,plain,(
% 0.21/0.48    r2_orders_2(sK0,sK4(k3_orders_2(sK0,sK3,sK1)),sK1)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f43,f44,f45,f46,f47,f48,f110,f122,f138,f57])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (~v5_orders_2(X0) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | r2_orders_2(X0,X1,X2) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f39])).
% 0.21/0.48  fof(f109,plain,(
% 0.21/0.48    ~r2_orders_2(sK0,sK1,sK1)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f47,f48,f72])).
% 0.21/0.48  fof(f72,plain,(
% 0.21/0.48    ( ! [X2,X0] : (~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_orders_2(X0,X2,X2)) )),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f70])).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    ( ! [X2,X0] : (~r2_orders_2(X0,X2,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.48    inference(equality_resolution,[],[f54])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (X1 != X2 | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f37])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | X1 = X2 | ~r1_orders_2(X0,X1,X2)) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.48    inference(flattening,[],[f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | (X1 = X2 | ~r1_orders_2(X0,X1,X2))) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.48    inference(nnf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : ((r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_orders_2)).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (9168)------------------------------
% 0.21/0.48  % (9168)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (9168)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (9168)Memory used [KB]: 6268
% 0.21/0.48  % (9168)Time elapsed: 0.082 s
% 0.21/0.48  % (9152)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.48  % (9168)------------------------------
% 0.21/0.48  % (9168)------------------------------
% 0.21/0.48  % (9151)Success in time 0.131 s
%------------------------------------------------------------------------------
