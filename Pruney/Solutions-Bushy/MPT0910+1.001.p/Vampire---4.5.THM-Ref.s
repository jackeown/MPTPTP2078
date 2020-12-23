%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0910+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:52 EST 2020

% Result     : Theorem 0.13s
% Output     : Refutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 117 expanded)
%              Number of leaves         :   10 (  38 expanded)
%              Depth                    :   14
%              Number of atoms          :  193 ( 780 expanded)
%              Number of equality atoms :   61 ( 406 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f83,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f64,f70,f76,f82])).

fof(f82,plain,(
    spl6_3 ),
    inference(avatar_contradiction_clause,[],[f81])).

fof(f81,plain,
    ( $false
    | spl6_3 ),
    inference(subsumption_resolution,[],[f78,f15])).

fof(f15,plain,(
    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( sK3 != k6_mcart_1(sK0,sK1,sK2,sK4)
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & ! [X5] :
        ( ! [X6] :
            ( ! [X7] :
                ( sK3 = X6
                | k3_mcart_1(X5,X6,X7) != sK4
                | ~ m1_subset_1(X7,sK2) )
            | ~ m1_subset_1(X6,sK1) )
        | ~ m1_subset_1(X5,sK0) )
    & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f8,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( k6_mcart_1(X0,X1,X2,X4) != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & ! [X5] :
            ( ! [X6] :
                ( ! [X7] :
                    ( X3 = X6
                    | k3_mcart_1(X5,X6,X7) != X4
                    | ~ m1_subset_1(X7,X2) )
                | ~ m1_subset_1(X6,X1) )
            | ~ m1_subset_1(X5,X0) )
        & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) )
   => ( sK3 != k6_mcart_1(sK0,sK1,sK2,sK4)
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( sK3 = X6
                  | k3_mcart_1(X5,X6,X7) != sK4
                  | ~ m1_subset_1(X7,sK2) )
              | ~ m1_subset_1(X6,sK1) )
          | ~ m1_subset_1(X5,sK0) )
      & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k6_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X6
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k6_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X6
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
       => ( ! [X5] :
              ( m1_subset_1(X5,X0)
             => ! [X6] :
                  ( m1_subset_1(X6,X1)
                 => ! [X7] :
                      ( m1_subset_1(X7,X2)
                     => ( k3_mcart_1(X5,X6,X7) = X4
                       => X3 = X6 ) ) ) )
         => ( k6_mcart_1(X0,X1,X2,X4) = X3
            | k1_xboole_0 = X2
            | k1_xboole_0 = X1
            | k1_xboole_0 = X0 ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
     => ( ! [X5] :
            ( m1_subset_1(X5,X0)
           => ! [X6] :
                ( m1_subset_1(X6,X1)
               => ! [X7] :
                    ( m1_subset_1(X7,X2)
                   => ( k3_mcart_1(X5,X6,X7) = X4
                     => X3 = X6 ) ) ) )
       => ( k6_mcart_1(X0,X1,X2,X4) = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_mcart_1)).

fof(f78,plain,
    ( ~ m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))
    | spl6_3 ),
    inference(resolution,[],[f63,f23])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_mcart_1)).

fof(f63,plain,
    ( ~ m1_subset_1(k7_mcart_1(sK0,sK1,sK2,sK4),sK2)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl6_3
  <=> m1_subset_1(k7_mcart_1(sK0,sK1,sK2,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f76,plain,(
    spl6_2 ),
    inference(avatar_contradiction_clause,[],[f75])).

fof(f75,plain,
    ( $false
    | spl6_2 ),
    inference(subsumption_resolution,[],[f72,f15])).

fof(f72,plain,
    ( ~ m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))
    | spl6_2 ),
    inference(resolution,[],[f59,f24])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_mcart_1)).

fof(f59,plain,
    ( ~ m1_subset_1(k6_mcart_1(sK0,sK1,sK2,sK4),sK1)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl6_2
  <=> m1_subset_1(k6_mcart_1(sK0,sK1,sK2,sK4),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f70,plain,(
    spl6_1 ),
    inference(avatar_contradiction_clause,[],[f69])).

fof(f69,plain,
    ( $false
    | spl6_1 ),
    inference(subsumption_resolution,[],[f66,f15])).

fof(f66,plain,
    ( ~ m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))
    | spl6_1 ),
    inference(resolution,[],[f55,f22])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_mcart_1)).

fof(f55,plain,
    ( ~ m1_subset_1(k5_mcart_1(sK0,sK1,sK2,sK4),sK0)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl6_1
  <=> m1_subset_1(k5_mcart_1(sK0,sK1,sK2,sK4),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f64,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f51,f61,f57,f53])).

fof(f51,plain,
    ( ~ m1_subset_1(k7_mcart_1(sK0,sK1,sK2,sK4),sK2)
    | ~ m1_subset_1(k6_mcart_1(sK0,sK1,sK2,sK4),sK1)
    | ~ m1_subset_1(k5_mcart_1(sK0,sK1,sK2,sK4),sK0) ),
    inference(subsumption_resolution,[],[f50,f26])).

fof(f26,plain,(
    ~ sQ5_eqProxy(sK3,k6_mcart_1(sK0,sK1,sK2,sK4)) ),
    inference(equality_proxy_replacement,[],[f20,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( sQ5_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ5_eqProxy])])).

fof(f20,plain,(
    sK3 != k6_mcart_1(sK0,sK1,sK2,sK4) ),
    inference(cnf_transformation,[],[f14])).

fof(f50,plain,
    ( sQ5_eqProxy(sK3,k6_mcart_1(sK0,sK1,sK2,sK4))
    | ~ m1_subset_1(k7_mcart_1(sK0,sK1,sK2,sK4),sK2)
    | ~ m1_subset_1(k6_mcart_1(sK0,sK1,sK2,sK4),sK1)
    | ~ m1_subset_1(k5_mcart_1(sK0,sK1,sK2,sK4),sK0) ),
    inference(subsumption_resolution,[],[f49,f29])).

fof(f29,plain,(
    ~ sQ5_eqProxy(k1_xboole_0,sK0) ),
    inference(equality_proxy_replacement,[],[f17,f25])).

fof(f17,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f14])).

fof(f49,plain,
    ( sQ5_eqProxy(k1_xboole_0,sK0)
    | sQ5_eqProxy(sK3,k6_mcart_1(sK0,sK1,sK2,sK4))
    | ~ m1_subset_1(k7_mcart_1(sK0,sK1,sK2,sK4),sK2)
    | ~ m1_subset_1(k6_mcart_1(sK0,sK1,sK2,sK4),sK1)
    | ~ m1_subset_1(k5_mcart_1(sK0,sK1,sK2,sK4),sK0) ),
    inference(subsumption_resolution,[],[f48,f28])).

fof(f28,plain,(
    ~ sQ5_eqProxy(k1_xboole_0,sK1) ),
    inference(equality_proxy_replacement,[],[f18,f25])).

fof(f18,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f14])).

fof(f48,plain,
    ( sQ5_eqProxy(k1_xboole_0,sK1)
    | sQ5_eqProxy(k1_xboole_0,sK0)
    | sQ5_eqProxy(sK3,k6_mcart_1(sK0,sK1,sK2,sK4))
    | ~ m1_subset_1(k7_mcart_1(sK0,sK1,sK2,sK4),sK2)
    | ~ m1_subset_1(k6_mcart_1(sK0,sK1,sK2,sK4),sK1)
    | ~ m1_subset_1(k5_mcart_1(sK0,sK1,sK2,sK4),sK0) ),
    inference(subsumption_resolution,[],[f46,f27])).

% (23751)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
fof(f27,plain,(
    ~ sQ5_eqProxy(k1_xboole_0,sK2) ),
    inference(equality_proxy_replacement,[],[f19,f25])).

fof(f19,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f14])).

fof(f46,plain,
    ( sQ5_eqProxy(k1_xboole_0,sK2)
    | sQ5_eqProxy(k1_xboole_0,sK1)
    | sQ5_eqProxy(k1_xboole_0,sK0)
    | sQ5_eqProxy(sK3,k6_mcart_1(sK0,sK1,sK2,sK4))
    | ~ m1_subset_1(k7_mcart_1(sK0,sK1,sK2,sK4),sK2)
    | ~ m1_subset_1(k6_mcart_1(sK0,sK1,sK2,sK4),sK1)
    | ~ m1_subset_1(k5_mcart_1(sK0,sK1,sK2,sK4),sK0) ),
    inference(resolution,[],[f43,f15])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK4,k3_zfmisc_1(X0,X1,X2))
      | sQ5_eqProxy(k1_xboole_0,X2)
      | sQ5_eqProxy(k1_xboole_0,X1)
      | sQ5_eqProxy(k1_xboole_0,X0)
      | sQ5_eqProxy(sK3,k6_mcart_1(X0,X1,X2,sK4))
      | ~ m1_subset_1(k7_mcart_1(X0,X1,X2,sK4),sK2)
      | ~ m1_subset_1(k6_mcart_1(X0,X1,X2,sK4),sK1)
      | ~ m1_subset_1(k5_mcart_1(X0,X1,X2,sK4),sK0) ) ),
    inference(resolution,[],[f31,f30])).

fof(f30,plain,(
    ! [X6,X7,X5] :
      ( ~ sQ5_eqProxy(k3_mcart_1(X5,X6,X7),sK4)
      | sQ5_eqProxy(sK3,X6)
      | ~ m1_subset_1(X7,sK2)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X5,sK0) ) ),
    inference(equality_proxy_replacement,[],[f16,f25,f25])).

fof(f16,plain,(
    ! [X6,X7,X5] :
      ( sK3 = X6
      | k3_mcart_1(X5,X6,X7) != sK4
      | ~ m1_subset_1(X7,sK2)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X5,sK0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( sQ5_eqProxy(k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)),X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | sQ5_eqProxy(k1_xboole_0,X2)
      | sQ5_eqProxy(k1_xboole_0,X1)
      | sQ5_eqProxy(k1_xboole_0,X0) ) ),
    inference(equality_proxy_replacement,[],[f21,f25,f25,f25,f25])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_mcart_1)).

%------------------------------------------------------------------------------
