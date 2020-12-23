%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:22 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 110 expanded)
%              Number of leaves         :   11 (  43 expanded)
%              Depth                    :    8
%              Number of atoms          :  202 ( 452 expanded)
%              Number of equality atoms :  125 ( 318 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f73,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f29,f34,f39,f44,f49,f65,f67,f69,f72])).

fof(f72,plain,
    ( spl7_1
    | spl7_2
    | spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_6 ),
    inference(avatar_contradiction_clause,[],[f70])).

fof(f70,plain,
    ( $false
    | spl7_1
    | spl7_2
    | spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_6 ),
    inference(unit_resulting_resolution,[],[f33,f28,f38,f56,f48,f52])).

fof(f52,plain,
    ( ! [X6,X8,X7] :
        ( ~ m1_subset_1(sK3,k2_zfmisc_1(k2_zfmisc_1(X6,X7),X8))
        | k1_xboole_0 = X7
        | k1_xboole_0 = X8
        | k1_xboole_0 = X6
        | sK6 = k7_mcart_1(X6,X7,X8,sK3) )
    | ~ spl7_4 ),
    inference(superposition,[],[f22,f43])).

fof(f43,plain,
    ( sK3 = k3_mcart_1(sK4,sK5,sK6)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl7_4
  <=> sK3 = k3_mcart_1(sK4,sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f22,plain,(
    ! [X6,X4,X2,X0,X5,X1] :
      ( ~ m1_subset_1(k3_mcart_1(X4,X5,X6),k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0
      | k7_mcart_1(X0,X1,X2,k3_mcart_1(X4,X5,X6)) = X6 ) ),
    inference(equality_resolution,[],[f19])).

fof(f19,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k3_mcart_1(X4,X5,X6) != X3
      | k7_mcart_1(X0,X1,X2,X3) = X6 ) ),
    inference(definition_unfolding,[],[f17,f14])).

fof(f14,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f17,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k3_mcart_1(X4,X5,X6) != X3
      | k7_mcart_1(X0,X1,X2,X3) = X6 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4,X5,X6] :
              ( ( k7_mcart_1(X0,X1,X2,X3) = X6
                & k6_mcart_1(X0,X1,X2,X3) = X5
                & k5_mcart_1(X0,X1,X2,X3) = X4 )
              | k3_mcart_1(X4,X5,X6) != X3 )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ~ ( ? [X3] :
            ( ? [X4,X5,X6] :
                ( ~ ( k7_mcart_1(X0,X1,X2,X3) = X6
                    & k6_mcart_1(X0,X1,X2,X3) = X5
                    & k5_mcart_1(X0,X1,X2,X3) = X4 )
                & k3_mcart_1(X4,X5,X6) = X3 )
            & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_mcart_1)).

fof(f48,plain,
    ( m1_subset_1(sK3,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl7_5
  <=> m1_subset_1(sK3,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f56,plain,
    ( sK6 != k7_mcart_1(sK0,sK1,sK2,sK3)
    | spl7_6 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl7_6
  <=> sK6 = k7_mcart_1(sK0,sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f38,plain,
    ( k1_xboole_0 != sK2
    | spl7_3 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl7_3
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f28,plain,
    ( k1_xboole_0 != sK0
    | spl7_1 ),
    inference(avatar_component_clause,[],[f26])).

fof(f26,plain,
    ( spl7_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f33,plain,
    ( k1_xboole_0 != sK1
    | spl7_2 ),
    inference(avatar_component_clause,[],[f31])).

fof(f31,plain,
    ( spl7_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f69,plain,
    ( spl7_7
    | spl7_1
    | spl7_3
    | spl7_2
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f68,f46,f41,f31,f36,f26,f58])).

fof(f58,plain,
    ( spl7_7
  <=> sK5 = k6_mcart_1(sK0,sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f68,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | sK5 = k6_mcart_1(sK0,sK1,sK2,sK3)
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(resolution,[],[f51,f48])).

fof(f51,plain,
    ( ! [X4,X5,X3] :
        ( ~ m1_subset_1(sK3,k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5))
        | k1_xboole_0 = X4
        | k1_xboole_0 = X5
        | k1_xboole_0 = X3
        | sK5 = k6_mcart_1(X3,X4,X5,sK3) )
    | ~ spl7_4 ),
    inference(superposition,[],[f23,f43])).

fof(f23,plain,(
    ! [X6,X4,X2,X0,X5,X1] :
      ( ~ m1_subset_1(k3_mcart_1(X4,X5,X6),k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0
      | k6_mcart_1(X0,X1,X2,k3_mcart_1(X4,X5,X6)) = X5 ) ),
    inference(equality_resolution,[],[f20])).

fof(f20,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k3_mcart_1(X4,X5,X6) != X3
      | k6_mcart_1(X0,X1,X2,X3) = X5 ) ),
    inference(definition_unfolding,[],[f16,f14])).

fof(f16,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k3_mcart_1(X4,X5,X6) != X3
      | k6_mcart_1(X0,X1,X2,X3) = X5 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f67,plain,
    ( spl7_8
    | spl7_1
    | spl7_3
    | spl7_2
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f66,f46,f41,f31,f36,f26,f62])).

fof(f62,plain,
    ( spl7_8
  <=> sK4 = k5_mcart_1(sK0,sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f66,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | sK4 = k5_mcart_1(sK0,sK1,sK2,sK3)
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(resolution,[],[f50,f48])).

fof(f50,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
        | k1_xboole_0 = X1
        | k1_xboole_0 = X2
        | k1_xboole_0 = X0
        | sK4 = k5_mcart_1(X0,X1,X2,sK3) )
    | ~ spl7_4 ),
    inference(superposition,[],[f24,f43])).

fof(f24,plain,(
    ! [X6,X4,X2,X0,X5,X1] :
      ( ~ m1_subset_1(k3_mcart_1(X4,X5,X6),k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0
      | k5_mcart_1(X0,X1,X2,k3_mcart_1(X4,X5,X6)) = X4 ) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k3_mcart_1(X4,X5,X6) != X3
      | k5_mcart_1(X0,X1,X2,X3) = X4 ) ),
    inference(definition_unfolding,[],[f15,f14])).

fof(f15,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k3_mcart_1(X4,X5,X6) != X3
      | k5_mcart_1(X0,X1,X2,X3) = X4 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f65,plain,
    ( ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f8,f62,f58,f54])).

fof(f8,plain,
    ( sK4 != k5_mcart_1(sK0,sK1,sK2,sK3)
    | sK5 != k6_mcart_1(sK0,sK1,sK2,sK3)
    | sK6 != k7_mcart_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
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
    inference(flattening,[],[f5])).

fof(f5,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
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
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_mcart_1)).

fof(f49,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f18,f46])).

fof(f18,plain,(
    m1_subset_1(sK3,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f10,f14])).

fof(f10,plain,(
    m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f44,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f9,f41])).

fof(f9,plain,(
    sK3 = k3_mcart_1(sK4,sK5,sK6) ),
    inference(cnf_transformation,[],[f6])).

fof(f39,plain,(
    ~ spl7_3 ),
    inference(avatar_split_clause,[],[f13,f36])).

fof(f13,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f6])).

fof(f34,plain,(
    ~ spl7_2 ),
    inference(avatar_split_clause,[],[f12,f31])).

fof(f12,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f6])).

fof(f29,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f11,f26])).

fof(f11,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f6])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:55:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.52  % (2790)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (2782)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (2774)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.53  % (2790)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f73,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f29,f34,f39,f44,f49,f65,f67,f69,f72])).
% 0.21/0.53  fof(f72,plain,(
% 0.21/0.53    spl7_1 | spl7_2 | spl7_3 | ~spl7_4 | ~spl7_5 | spl7_6),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f70])).
% 0.21/0.53  fof(f70,plain,(
% 0.21/0.53    $false | (spl7_1 | spl7_2 | spl7_3 | ~spl7_4 | ~spl7_5 | spl7_6)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f33,f28,f38,f56,f48,f52])).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    ( ! [X6,X8,X7] : (~m1_subset_1(sK3,k2_zfmisc_1(k2_zfmisc_1(X6,X7),X8)) | k1_xboole_0 = X7 | k1_xboole_0 = X8 | k1_xboole_0 = X6 | sK6 = k7_mcart_1(X6,X7,X8,sK3)) ) | ~spl7_4),
% 0.21/0.53    inference(superposition,[],[f22,f43])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    sK3 = k3_mcart_1(sK4,sK5,sK6) | ~spl7_4),
% 0.21/0.53    inference(avatar_component_clause,[],[f41])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    spl7_4 <=> sK3 = k3_mcart_1(sK4,sK5,sK6)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ( ! [X6,X4,X2,X0,X5,X1] : (~m1_subset_1(k3_mcart_1(X4,X5,X6),k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X0 | k7_mcart_1(X0,X1,X2,k3_mcart_1(X4,X5,X6)) = X6) )),
% 0.21/0.53    inference(equality_resolution,[],[f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k3_mcart_1(X4,X5,X6) != X3 | k7_mcart_1(X0,X1,X2,X3) = X6) )),
% 0.21/0.53    inference(definition_unfolding,[],[f17,f14])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k3_mcart_1(X4,X5,X6) != X3 | k7_mcart_1(X0,X1,X2,X3) = X6) )),
% 0.21/0.53    inference(cnf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (! [X3] : (! [X4,X5,X6] : ((k7_mcart_1(X0,X1,X2,X3) = X6 & k6_mcart_1(X0,X1,X2,X3) = X5 & k5_mcart_1(X0,X1,X2,X3) = X4) | k3_mcart_1(X4,X5,X6) != X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.53    inference(ennf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : ~(? [X3] : (? [X4,X5,X6] : (~(k7_mcart_1(X0,X1,X2,X3) = X6 & k6_mcart_1(X0,X1,X2,X3) = X5 & k5_mcart_1(X0,X1,X2,X3) = X4) & k3_mcart_1(X4,X5,X6) = X3) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_mcart_1)).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    m1_subset_1(sK3,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~spl7_5),
% 0.21/0.53    inference(avatar_component_clause,[],[f46])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    spl7_5 <=> m1_subset_1(sK3,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    sK6 != k7_mcart_1(sK0,sK1,sK2,sK3) | spl7_6),
% 0.21/0.53    inference(avatar_component_clause,[],[f54])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    spl7_6 <=> sK6 = k7_mcart_1(sK0,sK1,sK2,sK3)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    k1_xboole_0 != sK2 | spl7_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f36])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    spl7_3 <=> k1_xboole_0 = sK2),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    k1_xboole_0 != sK0 | spl7_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    spl7_1 <=> k1_xboole_0 = sK0),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    k1_xboole_0 != sK1 | spl7_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    spl7_2 <=> k1_xboole_0 = sK1),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.21/0.53  fof(f69,plain,(
% 0.21/0.53    spl7_7 | spl7_1 | spl7_3 | spl7_2 | ~spl7_4 | ~spl7_5),
% 0.21/0.53    inference(avatar_split_clause,[],[f68,f46,f41,f31,f36,f26,f58])).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    spl7_7 <=> sK5 = k6_mcart_1(sK0,sK1,sK2,sK3)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.21/0.53  fof(f68,plain,(
% 0.21/0.53    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK0 | sK5 = k6_mcart_1(sK0,sK1,sK2,sK3) | (~spl7_4 | ~spl7_5)),
% 0.21/0.53    inference(resolution,[],[f51,f48])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    ( ! [X4,X5,X3] : (~m1_subset_1(sK3,k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5)) | k1_xboole_0 = X4 | k1_xboole_0 = X5 | k1_xboole_0 = X3 | sK5 = k6_mcart_1(X3,X4,X5,sK3)) ) | ~spl7_4),
% 0.21/0.53    inference(superposition,[],[f23,f43])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ( ! [X6,X4,X2,X0,X5,X1] : (~m1_subset_1(k3_mcart_1(X4,X5,X6),k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X0 | k6_mcart_1(X0,X1,X2,k3_mcart_1(X4,X5,X6)) = X5) )),
% 0.21/0.53    inference(equality_resolution,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k3_mcart_1(X4,X5,X6) != X3 | k6_mcart_1(X0,X1,X2,X3) = X5) )),
% 0.21/0.53    inference(definition_unfolding,[],[f16,f14])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k3_mcart_1(X4,X5,X6) != X3 | k6_mcart_1(X0,X1,X2,X3) = X5) )),
% 0.21/0.53    inference(cnf_transformation,[],[f7])).
% 0.21/0.53  fof(f67,plain,(
% 0.21/0.53    spl7_8 | spl7_1 | spl7_3 | spl7_2 | ~spl7_4 | ~spl7_5),
% 0.21/0.53    inference(avatar_split_clause,[],[f66,f46,f41,f31,f36,f26,f62])).
% 0.21/0.53  fof(f62,plain,(
% 0.21/0.53    spl7_8 <=> sK4 = k5_mcart_1(sK0,sK1,sK2,sK3)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.21/0.53  fof(f66,plain,(
% 0.21/0.53    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK0 | sK4 = k5_mcart_1(sK0,sK1,sK2,sK3) | (~spl7_4 | ~spl7_5)),
% 0.21/0.53    inference(resolution,[],[f50,f48])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(sK3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X0 | sK4 = k5_mcart_1(X0,X1,X2,sK3)) ) | ~spl7_4),
% 0.21/0.53    inference(superposition,[],[f24,f43])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ( ! [X6,X4,X2,X0,X5,X1] : (~m1_subset_1(k3_mcart_1(X4,X5,X6),k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X0 | k5_mcart_1(X0,X1,X2,k3_mcart_1(X4,X5,X6)) = X4) )),
% 0.21/0.53    inference(equality_resolution,[],[f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k3_mcart_1(X4,X5,X6) != X3 | k5_mcart_1(X0,X1,X2,X3) = X4) )),
% 0.21/0.53    inference(definition_unfolding,[],[f15,f14])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k3_mcart_1(X4,X5,X6) != X3 | k5_mcart_1(X0,X1,X2,X3) = X4) )),
% 0.21/0.53    inference(cnf_transformation,[],[f7])).
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    ~spl7_6 | ~spl7_7 | ~spl7_8),
% 0.21/0.53    inference(avatar_split_clause,[],[f8,f62,f58,f54])).
% 0.21/0.53  fof(f8,plain,(
% 0.21/0.53    sK4 != k5_mcart_1(sK0,sK1,sK2,sK3) | sK5 != k6_mcart_1(sK0,sK1,sK2,sK3) | sK6 != k7_mcart_1(sK0,sK1,sK2,sK3)),
% 0.21/0.53    inference(cnf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,plain,(
% 0.21/0.53    ? [X0,X1,X2,X3] : (? [X4,X5,X6] : ((k7_mcart_1(X0,X1,X2,X3) != X6 | k6_mcart_1(X0,X1,X2,X3) != X5 | k5_mcart_1(X0,X1,X2,X3) != X4) & k3_mcart_1(X4,X5,X6) = X3) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 0.21/0.53    inference(flattening,[],[f5])).
% 0.21/0.53  fof(f5,plain,(
% 0.21/0.53    ? [X0,X1,X2,X3] : ((? [X4,X5,X6] : ((k7_mcart_1(X0,X1,X2,X3) != X6 | k6_mcart_1(X0,X1,X2,X3) != X5 | k5_mcart_1(X0,X1,X2,X3) != X4) & k3_mcart_1(X4,X5,X6) = X3) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 0.21/0.53    inference(ennf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,negated_conjecture,(
% 0.21/0.53    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => ~(? [X4,X5,X6] : (~(k7_mcart_1(X0,X1,X2,X3) = X6 & k6_mcart_1(X0,X1,X2,X3) = X5 & k5_mcart_1(X0,X1,X2,X3) = X4) & k3_mcart_1(X4,X5,X6) = X3) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0))),
% 0.21/0.53    inference(negated_conjecture,[],[f3])).
% 0.21/0.53  fof(f3,conjecture,(
% 0.21/0.53    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => ~(? [X4,X5,X6] : (~(k7_mcart_1(X0,X1,X2,X3) = X6 & k6_mcart_1(X0,X1,X2,X3) = X5 & k5_mcart_1(X0,X1,X2,X3) = X4) & k3_mcart_1(X4,X5,X6) = X3) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_mcart_1)).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    spl7_5),
% 0.21/0.53    inference(avatar_split_clause,[],[f18,f46])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    m1_subset_1(sK3,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 0.21/0.53    inference(definition_unfolding,[],[f10,f14])).
% 0.21/0.53  fof(f10,plain,(
% 0.21/0.53    m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))),
% 0.21/0.53    inference(cnf_transformation,[],[f6])).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    spl7_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f9,f41])).
% 0.21/0.53  fof(f9,plain,(
% 0.21/0.53    sK3 = k3_mcart_1(sK4,sK5,sK6)),
% 0.21/0.53    inference(cnf_transformation,[],[f6])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ~spl7_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f13,f36])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    k1_xboole_0 != sK2),
% 0.21/0.53    inference(cnf_transformation,[],[f6])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ~spl7_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f12,f31])).
% 0.21/0.53  fof(f12,plain,(
% 0.21/0.53    k1_xboole_0 != sK1),
% 0.21/0.53    inference(cnf_transformation,[],[f6])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ~spl7_1),
% 0.21/0.53    inference(avatar_split_clause,[],[f11,f26])).
% 0.21/0.53  fof(f11,plain,(
% 0.21/0.53    k1_xboole_0 != sK0),
% 0.21/0.53    inference(cnf_transformation,[],[f6])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (2790)------------------------------
% 0.21/0.53  % (2790)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (2790)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (2790)Memory used [KB]: 10746
% 0.21/0.53  % (2790)Time elapsed: 0.091 s
% 0.21/0.53  % (2790)------------------------------
% 0.21/0.53  % (2790)------------------------------
% 0.21/0.53  % (2759)Success in time 0.172 s
%------------------------------------------------------------------------------
