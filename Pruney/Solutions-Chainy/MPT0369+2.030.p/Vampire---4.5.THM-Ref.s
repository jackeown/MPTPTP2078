%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:27 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   57 (  85 expanded)
%              Number of leaves         :   13 (  29 expanded)
%              Depth                    :    7
%              Number of atoms          :  139 ( 245 expanded)
%              Number of equality atoms :   17 (  35 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f129,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f35,f39,f43,f49,f64,f69,f115,f124,f128])).

fof(f128,plain,
    ( spl5_3
    | ~ spl5_5 ),
    inference(avatar_contradiction_clause,[],[f127])).

fof(f127,plain,
    ( $false
    | spl5_3
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f125,f42])).

fof(f42,plain,
    ( k1_xboole_0 != sK0
    | spl5_3 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl5_3
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f125,plain,
    ( k1_xboole_0 = sK0
    | ~ spl5_5 ),
    inference(resolution,[],[f123,f29])).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f123,plain,
    ( v1_xboole_0(sK0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl5_5
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f124,plain,
    ( spl5_5
    | spl5_9
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f45,f33,f71,f54])).

fof(f71,plain,
    ( spl5_9
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f33,plain,
    ( spl5_1
  <=> m1_subset_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f45,plain,
    ( r2_hidden(sK2,sK0)
    | v1_xboole_0(sK0)
    | ~ spl5_1 ),
    inference(resolution,[],[f34,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f34,plain,
    ( m1_subset_1(sK2,sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f33])).

fof(f115,plain,
    ( spl5_2
    | spl5_8
    | ~ spl5_9 ),
    inference(avatar_contradiction_clause,[],[f114])).

fof(f114,plain,
    ( $false
    | spl5_2
    | spl5_8
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f110,f38])).

fof(f38,plain,
    ( ~ r2_hidden(sK2,sK1)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f37])).

fof(f37,plain,
    ( spl5_2
  <=> r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f110,plain,
    ( r2_hidden(sK2,sK1)
    | spl5_8
    | ~ spl5_9 ),
    inference(resolution,[],[f104,f68])).

fof(f68,plain,
    ( ~ r2_hidden(sK2,k4_xboole_0(sK0,sK1))
    | spl5_8 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl5_8
  <=> r2_hidden(sK2,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f104,plain,
    ( ! [X2] :
        ( r2_hidden(sK2,k4_xboole_0(sK0,X2))
        | r2_hidden(sK2,X2) )
    | ~ spl5_9 ),
    inference(resolution,[],[f75,f31])).

fof(f31,plain,(
    ! [X0,X3,X1] :
      ( ~ sP4(X3,X1,X0)
      | r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP4(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f75,plain,
    ( ! [X0] :
        ( sP4(sK2,X0,sK0)
        | r2_hidden(sK2,X0) )
    | ~ spl5_9 ),
    inference(resolution,[],[f72,f18])).

fof(f18,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | sP4(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f72,plain,
    ( r2_hidden(sK2,sK0)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f71])).

fof(f69,plain,
    ( ~ spl5_8
    | ~ spl5_4
    | spl5_7 ),
    inference(avatar_split_clause,[],[f65,f62,f47,f67])).

fof(f47,plain,
    ( spl5_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f62,plain,
    ( spl5_7
  <=> r2_hidden(sK2,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f65,plain,
    ( ~ r2_hidden(sK2,k4_xboole_0(sK0,sK1))
    | ~ spl5_4
    | spl5_7 ),
    inference(forward_demodulation,[],[f63,f50])).

fof(f50,plain,
    ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)
    | ~ spl5_4 ),
    inference(resolution,[],[f48,f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f48,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f47])).

fof(f63,plain,
    ( ~ r2_hidden(sK2,k3_subset_1(sK0,sK1))
    | spl5_7 ),
    inference(avatar_component_clause,[],[f62])).

fof(f64,plain,(
    ~ spl5_7 ),
    inference(avatar_split_clause,[],[f14,f62])).

fof(f14,plain,(
    ~ r2_hidden(sK2,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(X2,k3_subset_1(X0,X1))
              & ~ r2_hidden(X2,X1)
              & m1_subset_1(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
      & k1_xboole_0 != X0 ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(X2,k3_subset_1(X0,X1))
              & ~ r2_hidden(X2,X1)
              & m1_subset_1(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( k1_xboole_0 != X0
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(X0))
           => ! [X2] :
                ( m1_subset_1(X2,X0)
               => ( ~ r2_hidden(X2,X1)
                 => r2_hidden(X2,k3_subset_1(X0,X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ! [X2] :
              ( m1_subset_1(X2,X0)
             => ( ~ r2_hidden(X2,X1)
               => r2_hidden(X2,k3_subset_1(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_subset_1)).

fof(f49,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f15,f47])).

fof(f15,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f43,plain,(
    ~ spl5_3 ),
    inference(avatar_split_clause,[],[f16,f41])).

fof(f16,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f8])).

fof(f39,plain,(
    ~ spl5_2 ),
    inference(avatar_split_clause,[],[f13,f37])).

fof(f13,plain,(
    ~ r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f35,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f12,f33])).

fof(f12,plain,(
    m1_subset_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:51:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.42  % (2384)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.47  % (2379)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.47  % (2379)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f129,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f35,f39,f43,f49,f64,f69,f115,f124,f128])).
% 0.21/0.47  fof(f128,plain,(
% 0.21/0.47    spl5_3 | ~spl5_5),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f127])).
% 0.21/0.47  fof(f127,plain,(
% 0.21/0.47    $false | (spl5_3 | ~spl5_5)),
% 0.21/0.47    inference(subsumption_resolution,[],[f125,f42])).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    k1_xboole_0 != sK0 | spl5_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f41])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    spl5_3 <=> k1_xboole_0 = sK0),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.47  fof(f125,plain,(
% 0.21/0.47    k1_xboole_0 = sK0 | ~spl5_5),
% 0.21/0.47    inference(resolution,[],[f123,f29])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.47  fof(f123,plain,(
% 0.21/0.47    v1_xboole_0(sK0) | ~spl5_5),
% 0.21/0.47    inference(avatar_component_clause,[],[f54])).
% 0.21/0.47  fof(f54,plain,(
% 0.21/0.47    spl5_5 <=> v1_xboole_0(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.47  fof(f124,plain,(
% 0.21/0.47    spl5_5 | spl5_9 | ~spl5_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f45,f33,f71,f54])).
% 0.21/0.47  fof(f71,plain,(
% 0.21/0.47    spl5_9 <=> r2_hidden(sK2,sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    spl5_1 <=> m1_subset_1(sK2,sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    r2_hidden(sK2,sK0) | v1_xboole_0(sK0) | ~spl5_1),
% 0.21/0.47    inference(resolution,[],[f34,f28])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    m1_subset_1(sK2,sK0) | ~spl5_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f33])).
% 0.21/0.47  fof(f115,plain,(
% 0.21/0.47    spl5_2 | spl5_8 | ~spl5_9),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f114])).
% 0.21/0.47  fof(f114,plain,(
% 0.21/0.47    $false | (spl5_2 | spl5_8 | ~spl5_9)),
% 0.21/0.47    inference(subsumption_resolution,[],[f110,f38])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    ~r2_hidden(sK2,sK1) | spl5_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f37])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    spl5_2 <=> r2_hidden(sK2,sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.47  fof(f110,plain,(
% 0.21/0.47    r2_hidden(sK2,sK1) | (spl5_8 | ~spl5_9)),
% 0.21/0.47    inference(resolution,[],[f104,f68])).
% 0.21/0.47  fof(f68,plain,(
% 0.21/0.47    ~r2_hidden(sK2,k4_xboole_0(sK0,sK1)) | spl5_8),
% 0.21/0.47    inference(avatar_component_clause,[],[f67])).
% 0.21/0.47  fof(f67,plain,(
% 0.21/0.47    spl5_8 <=> r2_hidden(sK2,k4_xboole_0(sK0,sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.47  fof(f104,plain,(
% 0.21/0.47    ( ! [X2] : (r2_hidden(sK2,k4_xboole_0(sK0,X2)) | r2_hidden(sK2,X2)) ) | ~spl5_9),
% 0.21/0.47    inference(resolution,[],[f75,f31])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    ( ! [X0,X3,X1] : (~sP4(X3,X1,X0) | r2_hidden(X3,k4_xboole_0(X0,X1))) )),
% 0.21/0.47    inference(equality_resolution,[],[f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (~sP4(X3,X1,X0) | r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.21/0.47    inference(cnf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.21/0.47  fof(f75,plain,(
% 0.21/0.47    ( ! [X0] : (sP4(sK2,X0,sK0) | r2_hidden(sK2,X0)) ) | ~spl5_9),
% 0.21/0.47    inference(resolution,[],[f72,f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | sP4(X3,X1,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f1])).
% 0.21/0.47  fof(f72,plain,(
% 0.21/0.47    r2_hidden(sK2,sK0) | ~spl5_9),
% 0.21/0.47    inference(avatar_component_clause,[],[f71])).
% 0.21/0.47  fof(f69,plain,(
% 0.21/0.47    ~spl5_8 | ~spl5_4 | spl5_7),
% 0.21/0.47    inference(avatar_split_clause,[],[f65,f62,f47,f67])).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    spl5_4 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.47  fof(f62,plain,(
% 0.21/0.47    spl5_7 <=> r2_hidden(sK2,k3_subset_1(sK0,sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.47  fof(f65,plain,(
% 0.21/0.47    ~r2_hidden(sK2,k4_xboole_0(sK0,sK1)) | (~spl5_4 | spl5_7)),
% 0.21/0.47    inference(forward_demodulation,[],[f63,f50])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) | ~spl5_4),
% 0.21/0.47    inference(resolution,[],[f48,f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,plain,(
% 0.21/0.47    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl5_4),
% 0.21/0.47    inference(avatar_component_clause,[],[f47])).
% 0.21/0.47  fof(f63,plain,(
% 0.21/0.47    ~r2_hidden(sK2,k3_subset_1(sK0,sK1)) | spl5_7),
% 0.21/0.47    inference(avatar_component_clause,[],[f62])).
% 0.21/0.47  fof(f64,plain,(
% 0.21/0.47    ~spl5_7),
% 0.21/0.47    inference(avatar_split_clause,[],[f14,f62])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ~r2_hidden(sK2,k3_subset_1(sK0,sK1))),
% 0.21/0.47    inference(cnf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : (~r2_hidden(X2,k3_subset_1(X0,X1)) & ~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) & k1_xboole_0 != X0)),
% 0.21/0.47    inference(flattening,[],[f7])).
% 0.21/0.47  fof(f7,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : ((~r2_hidden(X2,k3_subset_1(X0,X1)) & ~r2_hidden(X2,X1)) & m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) & k1_xboole_0 != X0)),
% 0.21/0.47    inference(ennf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,negated_conjecture,(
% 0.21/0.47    ~! [X0] : (k1_xboole_0 != X0 => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,X0) => (~r2_hidden(X2,X1) => r2_hidden(X2,k3_subset_1(X0,X1))))))),
% 0.21/0.47    inference(negated_conjecture,[],[f5])).
% 0.21/0.47  fof(f5,conjecture,(
% 0.21/0.47    ! [X0] : (k1_xboole_0 != X0 => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,X0) => (~r2_hidden(X2,X1) => r2_hidden(X2,k3_subset_1(X0,X1))))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_subset_1)).
% 0.21/0.47  fof(f49,plain,(
% 0.21/0.47    spl5_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f15,f47])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.47    inference(cnf_transformation,[],[f8])).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    ~spl5_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f16,f41])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    k1_xboole_0 != sK0),
% 0.21/0.47    inference(cnf_transformation,[],[f8])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    ~spl5_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f13,f37])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ~r2_hidden(sK2,sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f8])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    spl5_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f12,f33])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    m1_subset_1(sK2,sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f8])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (2379)------------------------------
% 0.21/0.47  % (2379)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (2379)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (2379)Memory used [KB]: 6140
% 0.21/0.47  % (2379)Time elapsed: 0.057 s
% 0.21/0.47  % (2379)------------------------------
% 0.21/0.47  % (2379)------------------------------
% 0.21/0.47  % (2378)Success in time 0.118 s
%------------------------------------------------------------------------------
