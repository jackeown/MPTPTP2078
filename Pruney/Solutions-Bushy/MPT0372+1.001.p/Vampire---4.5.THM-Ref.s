%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0372+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:51 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 195 expanded)
%              Number of leaves         :    8 (  60 expanded)
%              Depth                    :   18
%              Number of atoms          :  245 (1224 expanded)
%              Number of equality atoms :   21 ( 161 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f157,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f135,f141,f156])).

fof(f156,plain,(
    ~ spl5_2 ),
    inference(avatar_contradiction_clause,[],[f155])).

fof(f155,plain,
    ( $false
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f154,f37])).

fof(f37,plain,(
    ~ sQ4_eqProxy(k3_subset_1(sK0,sK2),sK1) ),
    inference(resolution,[],[f35,f25])).

fof(f25,plain,(
    ~ sQ4_eqProxy(sK1,k3_subset_1(sK0,sK2)) ),
    inference(equality_proxy_replacement,[],[f20,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( sQ4_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ4_eqProxy])])).

fof(f20,plain,(
    sK1 != k3_subset_1(sK0,sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( sK1 != k3_subset_1(sK0,sK2)
    & ! [X3] :
        ( ( ( ~ r2_hidden(X3,sK2)
            | ~ r2_hidden(X3,sK1) )
          & ( r2_hidden(X3,sK2)
            | r2_hidden(X3,sK1) ) )
        | ~ m1_subset_1(X3,sK0) )
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f10,f9])).

fof(f9,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( k3_subset_1(X0,X2) != X1
            & ! [X3] :
                ( ( ( ~ r2_hidden(X3,X2)
                    | ~ r2_hidden(X3,X1) )
                  & ( r2_hidden(X3,X2)
                    | r2_hidden(X3,X1) ) )
                | ~ m1_subset_1(X3,X0) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( sK1 != k3_subset_1(sK0,X2)
          & ! [X3] :
              ( ( ( ~ r2_hidden(X3,X2)
                  | ~ r2_hidden(X3,sK1) )
                & ( r2_hidden(X3,X2)
                  | r2_hidden(X3,sK1) ) )
              | ~ m1_subset_1(X3,sK0) )
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,
    ( ? [X2] :
        ( sK1 != k3_subset_1(sK0,X2)
        & ! [X3] :
            ( ( ( ~ r2_hidden(X3,X2)
                | ~ r2_hidden(X3,sK1) )
              & ( r2_hidden(X3,X2)
                | r2_hidden(X3,sK1) ) )
            | ~ m1_subset_1(X3,sK0) )
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( sK1 != k3_subset_1(sK0,sK2)
      & ! [X3] :
          ( ( ( ~ r2_hidden(X3,sK2)
              | ~ r2_hidden(X3,sK1) )
            & ( r2_hidden(X3,sK2)
              | r2_hidden(X3,sK1) ) )
          | ~ m1_subset_1(X3,sK0) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & ! [X3] :
              ( ( ( ~ r2_hidden(X3,X2)
                  | ~ r2_hidden(X3,X1) )
                & ( r2_hidden(X3,X2)
                  | r2_hidden(X3,X1) ) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f4])).

fof(f4,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( ! [X3] :
                  ( m1_subset_1(X3,X0)
                 => ~ ( r2_hidden(X3,X1)
                    <=> r2_hidden(X3,X2) ) )
             => k3_subset_1(X0,X2) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ~ ( r2_hidden(X3,X1)
                  <=> r2_hidden(X3,X2) ) )
           => k3_subset_1(X0,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_subset_1)).

fof(f35,plain,(
    ! [X0,X1] :
      ( sQ4_eqProxy(X1,X0)
      | ~ sQ4_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f24])).

fof(f154,plain,
    ( sQ4_eqProxy(k3_subset_1(sK0,sK2),sK1)
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f153,f17])).

fof(f17,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f153,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | sQ4_eqProxy(k3_subset_1(sK0,sK2),sK1)
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f149,f119])).

fof(f119,plain,
    ( r2_hidden(sK3(sK0,sK1,sK2),sK2)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl5_2
  <=> r2_hidden(sK3(sK0,sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f149,plain,
    ( ~ r2_hidden(sK3(sK0,sK1,sK2),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | sQ4_eqProxy(k3_subset_1(sK0,sK2),sK1)
    | ~ spl5_2 ),
    inference(resolution,[],[f119,f92])).

fof(f92,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3(sK0,sK1,X0),sK2)
      | ~ r2_hidden(sK3(sK0,sK1,X0),X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | sQ4_eqProxy(k3_subset_1(sK0,X0),sK1) ) ),
    inference(subsumption_resolution,[],[f91,f16])).

fof(f16,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f91,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | ~ r2_hidden(sK3(sK0,sK1,X0),X0)
      | ~ r2_hidden(sK3(sK0,sK1,X0),sK2)
      | sQ4_eqProxy(k3_subset_1(sK0,X0),sK1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    inference(duplicate_literal_removal,[],[f90])).

fof(f90,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | ~ r2_hidden(sK3(sK0,sK1,X0),X0)
      | ~ r2_hidden(sK3(sK0,sK1,X0),sK2)
      | sQ4_eqProxy(k3_subset_1(sK0,X0),sK1)
      | sQ4_eqProxy(k3_subset_1(sK0,X0),sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f71,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK3(X0,X1,X2),X0)
      | sQ4_eqProxy(k3_subset_1(X0,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(equality_proxy_replacement,[],[f21,f24])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( k3_subset_1(X0,X2) = X1
      | m1_subset_1(sK3(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k3_subset_1(X0,X2) = X1
          | ( ( r2_hidden(sK3(X0,X1,X2),X2)
              | ~ r2_hidden(sK3(X0,X1,X2),X1) )
            & ( ~ r2_hidden(sK3(X0,X1,X2),X2)
              | r2_hidden(sK3(X0,X1,X2),X1) )
            & m1_subset_1(sK3(X0,X1,X2),X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f13,f14])).

fof(f14,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X2)
            | ~ r2_hidden(X3,X1) )
          & ( ~ r2_hidden(X3,X2)
            | r2_hidden(X3,X1) )
          & m1_subset_1(X3,X0) )
     => ( ( r2_hidden(sK3(X0,X1,X2),X2)
          | ~ r2_hidden(sK3(X0,X1,X2),X1) )
        & ( ~ r2_hidden(sK3(X0,X1,X2),X2)
          | r2_hidden(sK3(X0,X1,X2),X1) )
        & m1_subset_1(sK3(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k3_subset_1(X0,X2) = X1
          | ? [X3] :
              ( ( r2_hidden(X3,X2)
                | ~ r2_hidden(X3,X1) )
              & ( ~ r2_hidden(X3,X2)
                | r2_hidden(X3,X1) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k3_subset_1(X0,X2) = X1
          | ? [X3] :
              ( ( r2_hidden(X3,X2)
                | ~ r2_hidden(X3,X1) )
              & ( ~ r2_hidden(X3,X2)
                | r2_hidden(X3,X1) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k3_subset_1(X0,X2) = X1
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> ~ r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k3_subset_1(X0,X2) = X1
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> ~ r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                <=> ~ r2_hidden(X3,X2) ) )
           => k3_subset_1(X0,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_subset_1)).

fof(f71,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3(sK0,sK1,X0),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | ~ r2_hidden(sK3(sK0,sK1,X0),X0)
      | ~ r2_hidden(sK3(sK0,sK1,X0),sK2)
      | sQ4_eqProxy(k3_subset_1(sK0,X0),sK1) ) ),
    inference(resolution,[],[f54,f16])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
      | sQ4_eqProxy(k3_subset_1(X0,X1),sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(sK3(X0,sK1,X1),X1)
      | ~ r2_hidden(sK3(X0,sK1,X1),sK2)
      | ~ m1_subset_1(sK3(X0,sK1,X1),sK0) ) ),
    inference(resolution,[],[f27,f19])).

fof(f19,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK1)
      | ~ r2_hidden(X3,sK2)
      | ~ m1_subset_1(X3,sK0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X2)
      | sQ4_eqProxy(k3_subset_1(X0,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(equality_proxy_replacement,[],[f22,f24])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( k3_subset_1(X0,X2) = X1
      | ~ r2_hidden(sK3(X0,X1,X2),X2)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

% (3919)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f141,plain,
    ( ~ spl5_1
    | spl5_2 ),
    inference(avatar_contradiction_clause,[],[f139])).

fof(f139,plain,
    ( $false
    | ~ spl5_1
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f16,f17,f37,f120,f115,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X2)
      | sQ4_eqProxy(k3_subset_1(X0,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(equality_proxy_replacement,[],[f23,f24])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( k3_subset_1(X0,X2) = X1
      | r2_hidden(sK3(X0,X1,X2),X2)
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f115,plain,
    ( r2_hidden(sK3(sK0,sK1,sK2),sK1)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl5_1
  <=> r2_hidden(sK3(sK0,sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f120,plain,
    ( ~ r2_hidden(sK3(sK0,sK1,sK2),sK2)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f118])).

fof(f135,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_contradiction_clause,[],[f134])).

fof(f134,plain,
    ( $false
    | spl5_1
    | spl5_2 ),
    inference(subsumption_resolution,[],[f133,f16])).

fof(f133,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | spl5_1
    | spl5_2 ),
    inference(subsumption_resolution,[],[f132,f17])).

fof(f132,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | spl5_1
    | spl5_2 ),
    inference(subsumption_resolution,[],[f130,f37])).

fof(f130,plain,
    ( sQ4_eqProxy(k3_subset_1(sK0,sK2),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | spl5_1
    | spl5_2 ),
    inference(resolution,[],[f128,f28])).

fof(f128,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1,sK2),sK0)
    | spl5_1
    | spl5_2 ),
    inference(subsumption_resolution,[],[f127,f116])).

fof(f116,plain,
    ( ~ r2_hidden(sK3(sK0,sK1,sK2),sK1)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f114])).

fof(f127,plain,
    ( r2_hidden(sK3(sK0,sK1,sK2),sK1)
    | ~ m1_subset_1(sK3(sK0,sK1,sK2),sK0)
    | spl5_2 ),
    inference(resolution,[],[f120,f18])).

fof(f18,plain,(
    ! [X3] :
      ( r2_hidden(X3,sK2)
      | r2_hidden(X3,sK1)
      | ~ m1_subset_1(X3,sK0) ) ),
    inference(cnf_transformation,[],[f11])).

%------------------------------------------------------------------------------
