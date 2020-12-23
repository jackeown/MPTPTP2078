%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:22 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 140 expanded)
%              Number of leaves         :   17 (  62 expanded)
%              Depth                    :    7
%              Number of atoms          :  206 ( 480 expanded)
%              Number of equality atoms :  124 ( 330 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f106,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f32,f37,f42,f47,f52,f65,f72,f77,f90,f95,f99,f102,f105])).

fof(f105,plain,
    ( spl7_3
    | spl7_1
    | spl7_2
    | spl7_8
    | ~ spl7_4
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f104,f92,f44,f62,f34,f29,f39])).

fof(f39,plain,
    ( spl7_3
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f29,plain,
    ( spl7_1
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f34,plain,
    ( spl7_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f62,plain,
    ( spl7_8
  <=> sK4 = k5_mcart_1(sK0,sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f44,plain,
    ( spl7_4
  <=> m1_subset_1(sK3,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f92,plain,
    ( spl7_13
  <=> sK4 = k1_mcart_1(k1_mcart_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f104,plain,
    ( sK4 = k5_mcart_1(sK0,sK1,sK2,sK3)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | ~ spl7_4
    | ~ spl7_13 ),
    inference(forward_demodulation,[],[f103,f94])).

fof(f94,plain,
    ( sK4 = k1_mcart_1(k1_mcart_1(sK3))
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f92])).

fof(f103,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | k5_mcart_1(sK0,sK1,sK2,sK3) = k1_mcart_1(k1_mcart_1(sK3))
    | ~ spl7_4 ),
    inference(resolution,[],[f27,f46])).

fof(f46,plain,
    ( m1_subset_1(sK3,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f44])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0
      | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) ),
    inference(definition_unfolding,[],[f20,f19])).

fof(f19,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f20,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
            & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
            & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
                & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
                & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).

fof(f102,plain,
    ( spl7_3
    | spl7_1
    | spl7_2
    | spl7_7
    | ~ spl7_4
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f101,f87,f44,f58,f34,f29,f39])).

fof(f58,plain,
    ( spl7_7
  <=> sK5 = k6_mcart_1(sK0,sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f87,plain,
    ( spl7_12
  <=> sK5 = k2_mcart_1(k1_mcart_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f101,plain,
    ( sK5 = k6_mcart_1(sK0,sK1,sK2,sK3)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | ~ spl7_4
    | ~ spl7_12 ),
    inference(forward_demodulation,[],[f100,f89])).

fof(f89,plain,
    ( sK5 = k2_mcart_1(k1_mcart_1(sK3))
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f87])).

fof(f100,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k1_mcart_1(sK3))
    | ~ spl7_4 ),
    inference(resolution,[],[f26,f46])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0
      | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) ) ),
    inference(definition_unfolding,[],[f21,f19])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f99,plain,
    ( spl7_3
    | spl7_1
    | spl7_2
    | spl7_6
    | ~ spl7_4
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f98,f69,f44,f54,f34,f29,f39])).

fof(f54,plain,
    ( spl7_6
  <=> sK6 = k7_mcart_1(sK0,sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f69,plain,
    ( spl7_9
  <=> sK6 = k2_mcart_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f98,plain,
    ( sK6 = k7_mcart_1(sK0,sK1,sK2,sK3)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | ~ spl7_4
    | ~ spl7_9 ),
    inference(forward_demodulation,[],[f97,f71])).

fof(f71,plain,
    ( sK6 = k2_mcart_1(sK3)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f69])).

fof(f97,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | k7_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(sK3)
    | ~ spl7_4 ),
    inference(resolution,[],[f25,f46])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0
      | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) ) ),
    inference(definition_unfolding,[],[f22,f19])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f95,plain,
    ( spl7_13
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f80,f74,f92])).

fof(f74,plain,
    ( spl7_10
  <=> k4_tarski(sK4,sK5) = k1_mcart_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f80,plain,
    ( sK4 = k1_mcart_1(k1_mcart_1(sK3))
    | ~ spl7_10 ),
    inference(superposition,[],[f16,f76])).

fof(f76,plain,
    ( k4_tarski(sK4,sK5) = k1_mcart_1(sK3)
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f74])).

fof(f16,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f90,plain,
    ( spl7_12
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f79,f74,f87])).

fof(f79,plain,
    ( sK5 = k2_mcart_1(k1_mcart_1(sK3))
    | ~ spl7_10 ),
    inference(superposition,[],[f17,f76])).

fof(f17,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f4])).

fof(f77,plain,
    ( spl7_10
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f67,f49,f74])).

fof(f49,plain,
    ( spl7_5
  <=> sK3 = k4_tarski(k4_tarski(sK4,sK5),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f67,plain,
    ( k4_tarski(sK4,sK5) = k1_mcart_1(sK3)
    | ~ spl7_5 ),
    inference(superposition,[],[f16,f51])).

fof(f51,plain,
    ( sK3 = k4_tarski(k4_tarski(sK4,sK5),sK6)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f49])).

fof(f72,plain,
    ( spl7_9
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f66,f49,f69])).

fof(f66,plain,
    ( sK6 = k2_mcart_1(sK3)
    | ~ spl7_5 ),
    inference(superposition,[],[f17,f51])).

fof(f65,plain,
    ( ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f10,f62,f58,f54])).

fof(f10,plain,
    ( sK4 != k5_mcart_1(sK0,sK1,sK2,sK3)
    | sK5 != k6_mcart_1(sK0,sK1,sK2,sK3)
    | sK6 != k7_mcart_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4,X5,X6] :
          ( ( k7_mcart_1(X0,X1,X2,X3) != X6
            | k6_mcart_1(X0,X1,X2,X3) != X5
            | k5_mcart_1(X0,X1,X2,X3) != X4 )
          & k3_mcart_1(X4,X5,X6) = X3 )
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4,X5,X6] :
          ( ( k7_mcart_1(X0,X1,X2,X3) != X6
            | k6_mcart_1(X0,X1,X2,X3) != X5
            | k5_mcart_1(X0,X1,X2,X3) != X4 )
          & k3_mcart_1(X4,X5,X6) = X3 )
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
       => ~ ( ? [X4,X5,X6] :
                ( ~ ( k7_mcart_1(X0,X1,X2,X3) = X6
                    & k6_mcart_1(X0,X1,X2,X3) = X5
                    & k5_mcart_1(X0,X1,X2,X3) = X4 )
                & k3_mcart_1(X4,X5,X6) = X3 )
            & k1_xboole_0 != X2
            & k1_xboole_0 != X1
            & k1_xboole_0 != X0 ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => ~ ( ? [X4,X5,X6] :
              ( ~ ( k7_mcart_1(X0,X1,X2,X3) = X6
                  & k6_mcart_1(X0,X1,X2,X3) = X5
                  & k5_mcart_1(X0,X1,X2,X3) = X4 )
              & k3_mcart_1(X4,X5,X6) = X3 )
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_mcart_1)).

fof(f52,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f24,f49])).

fof(f24,plain,(
    sK3 = k4_tarski(k4_tarski(sK4,sK5),sK6) ),
    inference(definition_unfolding,[],[f11,f18])).

fof(f18,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f11,plain,(
    sK3 = k3_mcart_1(sK4,sK5,sK6) ),
    inference(cnf_transformation,[],[f8])).

fof(f47,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f23,f44])).

fof(f23,plain,(
    m1_subset_1(sK3,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f12,f19])).

fof(f12,plain,(
    m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f42,plain,(
    ~ spl7_3 ),
    inference(avatar_split_clause,[],[f13,f39])).

fof(f13,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f8])).

fof(f37,plain,(
    ~ spl7_2 ),
    inference(avatar_split_clause,[],[f14,f34])).

fof(f14,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f8])).

fof(f32,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f15,f29])).

fof(f15,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n020.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 12:50:37 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.51  % (6163)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.52  % (6151)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (6152)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.52  % (6156)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.52  % (6163)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f106,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(avatar_sat_refutation,[],[f32,f37,f42,f47,f52,f65,f72,f77,f90,f95,f99,f102,f105])).
% 0.22/0.52  fof(f105,plain,(
% 0.22/0.52    spl7_3 | spl7_1 | spl7_2 | spl7_8 | ~spl7_4 | ~spl7_13),
% 0.22/0.52    inference(avatar_split_clause,[],[f104,f92,f44,f62,f34,f29,f39])).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    spl7_3 <=> k1_xboole_0 = sK0),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    spl7_1 <=> k1_xboole_0 = sK2),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.22/0.52  fof(f34,plain,(
% 0.22/0.52    spl7_2 <=> k1_xboole_0 = sK1),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.22/0.52  fof(f62,plain,(
% 0.22/0.52    spl7_8 <=> sK4 = k5_mcart_1(sK0,sK1,sK2,sK3)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.22/0.52  fof(f44,plain,(
% 0.22/0.52    spl7_4 <=> m1_subset_1(sK3,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.22/0.52  fof(f92,plain,(
% 0.22/0.52    spl7_13 <=> sK4 = k1_mcart_1(k1_mcart_1(sK3))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.22/0.52  fof(f104,plain,(
% 0.22/0.52    sK4 = k5_mcart_1(sK0,sK1,sK2,sK3) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK0 | (~spl7_4 | ~spl7_13)),
% 0.22/0.52    inference(forward_demodulation,[],[f103,f94])).
% 0.22/0.52  fof(f94,plain,(
% 0.22/0.52    sK4 = k1_mcart_1(k1_mcart_1(sK3)) | ~spl7_13),
% 0.22/0.52    inference(avatar_component_clause,[],[f92])).
% 0.22/0.52  fof(f103,plain,(
% 0.22/0.52    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK0 | k5_mcart_1(sK0,sK1,sK2,sK3) = k1_mcart_1(k1_mcart_1(sK3)) | ~spl7_4),
% 0.22/0.52    inference(resolution,[],[f27,f46])).
% 0.22/0.52  fof(f46,plain,(
% 0.22/0.52    m1_subset_1(sK3,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~spl7_4),
% 0.22/0.52    inference(avatar_component_clause,[],[f44])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X0 | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) )),
% 0.22/0.52    inference(definition_unfolding,[],[f20,f19])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f9])).
% 0.22/0.52  fof(f9,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.22/0.52    inference(ennf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).
% 0.22/0.52  fof(f102,plain,(
% 0.22/0.52    spl7_3 | spl7_1 | spl7_2 | spl7_7 | ~spl7_4 | ~spl7_12),
% 0.22/0.52    inference(avatar_split_clause,[],[f101,f87,f44,f58,f34,f29,f39])).
% 0.22/0.52  fof(f58,plain,(
% 0.22/0.52    spl7_7 <=> sK5 = k6_mcart_1(sK0,sK1,sK2,sK3)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.22/0.52  fof(f87,plain,(
% 0.22/0.52    spl7_12 <=> sK5 = k2_mcart_1(k1_mcart_1(sK3))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.22/0.52  fof(f101,plain,(
% 0.22/0.52    sK5 = k6_mcart_1(sK0,sK1,sK2,sK3) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK0 | (~spl7_4 | ~spl7_12)),
% 0.22/0.52    inference(forward_demodulation,[],[f100,f89])).
% 0.22/0.52  fof(f89,plain,(
% 0.22/0.52    sK5 = k2_mcart_1(k1_mcart_1(sK3)) | ~spl7_12),
% 0.22/0.52    inference(avatar_component_clause,[],[f87])).
% 0.22/0.52  fof(f100,plain,(
% 0.22/0.52    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK0 | k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k1_mcart_1(sK3)) | ~spl7_4),
% 0.22/0.52    inference(resolution,[],[f26,f46])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X0 | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))) )),
% 0.22/0.52    inference(definition_unfolding,[],[f21,f19])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f9])).
% 0.22/0.52  fof(f99,plain,(
% 0.22/0.52    spl7_3 | spl7_1 | spl7_2 | spl7_6 | ~spl7_4 | ~spl7_9),
% 0.22/0.52    inference(avatar_split_clause,[],[f98,f69,f44,f54,f34,f29,f39])).
% 0.22/0.52  fof(f54,plain,(
% 0.22/0.52    spl7_6 <=> sK6 = k7_mcart_1(sK0,sK1,sK2,sK3)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.22/0.52  fof(f69,plain,(
% 0.22/0.52    spl7_9 <=> sK6 = k2_mcart_1(sK3)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.22/0.52  fof(f98,plain,(
% 0.22/0.52    sK6 = k7_mcart_1(sK0,sK1,sK2,sK3) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK0 | (~spl7_4 | ~spl7_9)),
% 0.22/0.52    inference(forward_demodulation,[],[f97,f71])).
% 0.22/0.52  fof(f71,plain,(
% 0.22/0.52    sK6 = k2_mcart_1(sK3) | ~spl7_9),
% 0.22/0.52    inference(avatar_component_clause,[],[f69])).
% 0.22/0.52  fof(f97,plain,(
% 0.22/0.52    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK0 | k7_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(sK3) | ~spl7_4),
% 0.22/0.52    inference(resolution,[],[f25,f46])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X0 | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)) )),
% 0.22/0.52    inference(definition_unfolding,[],[f22,f19])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f9])).
% 0.22/0.52  fof(f95,plain,(
% 0.22/0.52    spl7_13 | ~spl7_10),
% 0.22/0.52    inference(avatar_split_clause,[],[f80,f74,f92])).
% 0.22/0.52  fof(f74,plain,(
% 0.22/0.52    spl7_10 <=> k4_tarski(sK4,sK5) = k1_mcart_1(sK3)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.22/0.52  fof(f80,plain,(
% 0.22/0.52    sK4 = k1_mcart_1(k1_mcart_1(sK3)) | ~spl7_10),
% 0.22/0.52    inference(superposition,[],[f16,f76])).
% 0.22/0.52  fof(f76,plain,(
% 0.22/0.52    k4_tarski(sK4,sK5) = k1_mcart_1(sK3) | ~spl7_10),
% 0.22/0.52    inference(avatar_component_clause,[],[f74])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).
% 0.22/0.52  fof(f90,plain,(
% 0.22/0.52    spl7_12 | ~spl7_10),
% 0.22/0.52    inference(avatar_split_clause,[],[f79,f74,f87])).
% 0.22/0.52  fof(f79,plain,(
% 0.22/0.52    sK5 = k2_mcart_1(k1_mcart_1(sK3)) | ~spl7_10),
% 0.22/0.52    inference(superposition,[],[f17,f76])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 0.22/0.52    inference(cnf_transformation,[],[f4])).
% 0.22/0.52  fof(f77,plain,(
% 0.22/0.52    spl7_10 | ~spl7_5),
% 0.22/0.52    inference(avatar_split_clause,[],[f67,f49,f74])).
% 0.22/0.52  fof(f49,plain,(
% 0.22/0.52    spl7_5 <=> sK3 = k4_tarski(k4_tarski(sK4,sK5),sK6)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.22/0.52  fof(f67,plain,(
% 0.22/0.52    k4_tarski(sK4,sK5) = k1_mcart_1(sK3) | ~spl7_5),
% 0.22/0.52    inference(superposition,[],[f16,f51])).
% 0.22/0.53  fof(f51,plain,(
% 0.22/0.53    sK3 = k4_tarski(k4_tarski(sK4,sK5),sK6) | ~spl7_5),
% 0.22/0.53    inference(avatar_component_clause,[],[f49])).
% 0.22/0.53  fof(f72,plain,(
% 0.22/0.53    spl7_9 | ~spl7_5),
% 0.22/0.53    inference(avatar_split_clause,[],[f66,f49,f69])).
% 0.22/0.53  fof(f66,plain,(
% 0.22/0.53    sK6 = k2_mcart_1(sK3) | ~spl7_5),
% 0.22/0.53    inference(superposition,[],[f17,f51])).
% 0.22/0.53  fof(f65,plain,(
% 0.22/0.53    ~spl7_6 | ~spl7_7 | ~spl7_8),
% 0.22/0.53    inference(avatar_split_clause,[],[f10,f62,f58,f54])).
% 0.22/0.53  fof(f10,plain,(
% 0.22/0.53    sK4 != k5_mcart_1(sK0,sK1,sK2,sK3) | sK5 != k6_mcart_1(sK0,sK1,sK2,sK3) | sK6 != k7_mcart_1(sK0,sK1,sK2,sK3)),
% 0.22/0.53    inference(cnf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,plain,(
% 0.22/0.53    ? [X0,X1,X2,X3] : (? [X4,X5,X6] : ((k7_mcart_1(X0,X1,X2,X3) != X6 | k6_mcart_1(X0,X1,X2,X3) != X5 | k5_mcart_1(X0,X1,X2,X3) != X4) & k3_mcart_1(X4,X5,X6) = X3) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 0.22/0.53    inference(flattening,[],[f7])).
% 0.22/0.53  fof(f7,plain,(
% 0.22/0.53    ? [X0,X1,X2,X3] : ((? [X4,X5,X6] : ((k7_mcart_1(X0,X1,X2,X3) != X6 | k6_mcart_1(X0,X1,X2,X3) != X5 | k5_mcart_1(X0,X1,X2,X3) != X4) & k3_mcart_1(X4,X5,X6) = X3) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 0.22/0.53    inference(ennf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,negated_conjecture,(
% 0.22/0.53    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => ~(? [X4,X5,X6] : (~(k7_mcart_1(X0,X1,X2,X3) = X6 & k6_mcart_1(X0,X1,X2,X3) = X5 & k5_mcart_1(X0,X1,X2,X3) = X4) & k3_mcart_1(X4,X5,X6) = X3) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0))),
% 0.22/0.53    inference(negated_conjecture,[],[f5])).
% 0.22/0.53  fof(f5,conjecture,(
% 0.22/0.53    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => ~(? [X4,X5,X6] : (~(k7_mcart_1(X0,X1,X2,X3) = X6 & k6_mcart_1(X0,X1,X2,X3) = X5 & k5_mcart_1(X0,X1,X2,X3) = X4) & k3_mcart_1(X4,X5,X6) = X3) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_mcart_1)).
% 0.22/0.53  fof(f52,plain,(
% 0.22/0.53    spl7_5),
% 0.22/0.53    inference(avatar_split_clause,[],[f24,f49])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    sK3 = k4_tarski(k4_tarski(sK4,sK5),sK6)),
% 0.22/0.53    inference(definition_unfolding,[],[f11,f18])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).
% 0.22/0.53  fof(f11,plain,(
% 0.22/0.53    sK3 = k3_mcart_1(sK4,sK5,sK6)),
% 0.22/0.53    inference(cnf_transformation,[],[f8])).
% 0.22/0.53  fof(f47,plain,(
% 0.22/0.53    spl7_4),
% 0.22/0.53    inference(avatar_split_clause,[],[f23,f44])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    m1_subset_1(sK3,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 0.22/0.53    inference(definition_unfolding,[],[f12,f19])).
% 0.22/0.53  fof(f12,plain,(
% 0.22/0.53    m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))),
% 0.22/0.53    inference(cnf_transformation,[],[f8])).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    ~spl7_3),
% 0.22/0.53    inference(avatar_split_clause,[],[f13,f39])).
% 0.22/0.53  fof(f13,plain,(
% 0.22/0.53    k1_xboole_0 != sK0),
% 0.22/0.53    inference(cnf_transformation,[],[f8])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    ~spl7_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f14,f34])).
% 0.22/0.53  fof(f14,plain,(
% 0.22/0.53    k1_xboole_0 != sK1),
% 0.22/0.53    inference(cnf_transformation,[],[f8])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    ~spl7_1),
% 0.22/0.53    inference(avatar_split_clause,[],[f15,f29])).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    k1_xboole_0 != sK2),
% 0.22/0.53    inference(cnf_transformation,[],[f8])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (6163)------------------------------
% 0.22/0.53  % (6163)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (6163)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (6163)Memory used [KB]: 10746
% 0.22/0.53  % (6163)Time elapsed: 0.114 s
% 0.22/0.53  % (6163)------------------------------
% 0.22/0.53  % (6163)------------------------------
% 0.22/0.53  % (6160)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.53  % (6146)Success in time 0.165 s
%------------------------------------------------------------------------------
