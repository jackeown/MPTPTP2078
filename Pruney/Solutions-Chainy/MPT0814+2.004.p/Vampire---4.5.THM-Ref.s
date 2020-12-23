%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:10 EST 2020

% Result     : Theorem 1.71s
% Output     : Refutation 1.71s
% Verified   : 
% Statistics : Number of formulae       :   62 (  97 expanded)
%              Number of leaves         :   12 (  31 expanded)
%              Depth                    :   14
%              Number of atoms          :  179 ( 283 expanded)
%              Number of equality atoms :   15 (  29 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f172,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f92,f98,f103,f117,f132,f171])).

fof(f171,plain,
    ( ~ spl7_1
    | ~ spl7_8 ),
    inference(avatar_contradiction_clause,[],[f170])).

fof(f170,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_8 ),
    inference(trivial_inequality_removal,[],[f169])).

fof(f169,plain,
    ( sK0 != sK0
    | ~ spl7_1
    | ~ spl7_8 ),
    inference(resolution,[],[f168,f91])).

fof(f91,plain,
    ( r2_hidden(sK0,sK3)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl7_1
  <=> r2_hidden(sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f168,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK3)
        | sK0 != X0 )
    | ~ spl7_8 ),
    inference(duplicate_literal_removal,[],[f167])).

fof(f167,plain,
    ( ! [X0] :
        ( sK0 != X0
        | ~ r2_hidden(X0,sK3)
        | ~ r2_hidden(X0,sK3) )
    | ~ spl7_8 ),
    inference(resolution,[],[f166,f142])).

fof(f142,plain,
    ( ! [X0] :
        ( r2_hidden(sK5(X0),sK1)
        | ~ r2_hidden(X0,sK3) )
    | ~ spl7_8 ),
    inference(duplicate_literal_removal,[],[f140])).

fof(f140,plain,
    ( ! [X0] :
        ( r2_hidden(sK5(X0),sK1)
        | ~ r2_hidden(X0,sK3)
        | ~ r2_hidden(X0,sK3) )
    | ~ spl7_8 ),
    inference(resolution,[],[f136,f131])).

fof(f131,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_zfmisc_1(sK1,sK2))
        | ~ r2_hidden(X0,sK3) )
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl7_8
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK3)
        | r2_hidden(X0,k2_zfmisc_1(sK1,sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f136,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
        | r2_hidden(sK5(X0),sK1)
        | ~ r2_hidden(X0,sK3) )
    | ~ spl7_8 ),
    inference(superposition,[],[f134,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(sK5(X0),sK6(X0)) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ? [X3,X4] : k4_tarski(X3,X4) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ~ ( ! [X3,X4] : k4_tarski(X3,X4) != X0
        & r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l139_zfmisc_1)).

fof(f134,plain,
    ( ! [X2,X1] :
        ( ~ r2_hidden(k4_tarski(X1,X2),sK3)
        | r2_hidden(X1,sK1) )
    | ~ spl7_8 ),
    inference(resolution,[],[f131,f64])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_zfmisc_1)).

fof(f166,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5(X0),sK1)
        | sK0 != X0
        | ~ r2_hidden(X0,sK3) )
    | ~ spl7_8 ),
    inference(duplicate_literal_removal,[],[f165])).

fof(f165,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5(X0),sK1)
        | sK0 != X0
        | ~ r2_hidden(X0,sK3)
        | ~ r2_hidden(X0,sK3) )
    | ~ spl7_8 ),
    inference(resolution,[],[f137,f154])).

fof(f154,plain,
    ( ! [X0] :
        ( r2_hidden(sK6(X0),sK2)
        | ~ r2_hidden(X0,sK3) )
    | ~ spl7_8 ),
    inference(duplicate_literal_removal,[],[f152])).

fof(f152,plain,
    ( ! [X0] :
        ( r2_hidden(sK6(X0),sK2)
        | ~ r2_hidden(X0,sK3)
        | ~ r2_hidden(X0,sK3) )
    | ~ spl7_8 ),
    inference(resolution,[],[f139,f131])).

fof(f139,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
        | r2_hidden(sK6(X0),sK2)
        | ~ r2_hidden(X0,sK3) )
    | ~ spl7_8 ),
    inference(superposition,[],[f135,f62])).

fof(f135,plain,
    ( ! [X4,X3] :
        ( ~ r2_hidden(k4_tarski(X3,X4),sK3)
        | r2_hidden(X4,sK2) )
    | ~ spl7_8 ),
    inference(resolution,[],[f131,f65])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f137,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK6(X0),sK2)
        | ~ r2_hidden(sK5(X0),sK1)
        | sK0 != X0
        | ~ r2_hidden(X0,sK3) )
    | ~ spl7_8 ),
    inference(resolution,[],[f118,f131])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | ~ r2_hidden(sK5(X0),sK1)
      | ~ r2_hidden(sK6(X0),sK2)
      | sK0 != X0 ) ),
    inference(superposition,[],[f35,f62])).

fof(f35,plain,(
    ! [X4,X5] :
      ( k4_tarski(X4,X5) != sK0
      | ~ r2_hidden(X4,sK1)
      | ~ r2_hidden(X5,sK2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4,X5] :
          ( ~ r2_hidden(X5,X2)
          | ~ r2_hidden(X4,X1)
          | k4_tarski(X4,X5) != X0 )
      & r2_hidden(X0,X3)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4,X5] :
          ( ~ r2_hidden(X5,X2)
          | ~ r2_hidden(X4,X1)
          | k4_tarski(X4,X5) != X0 )
      & r2_hidden(X0,X3)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
       => ~ ( ! [X4,X5] :
                ~ ( r2_hidden(X5,X2)
                  & r2_hidden(X4,X1)
                  & k4_tarski(X4,X5) = X0 )
            & r2_hidden(X0,X3) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ~ ( ! [X4,X5] :
              ~ ( r2_hidden(X5,X2)
                & r2_hidden(X4,X1)
                & k4_tarski(X4,X5) = X0 )
          & r2_hidden(X0,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_relset_1)).

fof(f132,plain,
    ( spl7_5
    | spl7_8
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f119,f100,f130,f114])).

fof(f114,plain,
    ( spl7_5
  <=> v1_xboole_0(k2_zfmisc_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f100,plain,
    ( spl7_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f119,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK3)
        | v1_xboole_0(k2_zfmisc_1(sK1,sK2))
        | r2_hidden(X0,k2_zfmisc_1(sK1,sK2)) )
    | ~ spl7_3 ),
    inference(resolution,[],[f104,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f104,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,k2_zfmisc_1(sK1,sK2))
        | ~ r2_hidden(X0,sK3) )
    | ~ spl7_3 ),
    inference(resolution,[],[f102,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f102,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f100])).

fof(f117,plain,
    ( spl7_2
    | ~ spl7_5
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f106,f100,f114,f95])).

fof(f95,plain,
    ( spl7_2
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f106,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK1,sK2))
    | v1_xboole_0(sK3)
    | ~ spl7_3 ),
    inference(resolution,[],[f102,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f103,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f36,f100])).

fof(f36,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f25])).

fof(f98,plain,
    ( ~ spl7_2
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f93,f89,f95])).

fof(f93,plain,
    ( ~ v1_xboole_0(sK3)
    | ~ spl7_1 ),
    inference(resolution,[],[f91,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

fof(f92,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f37,f89])).

fof(f37,plain,(
    r2_hidden(sK0,sK3) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:15:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.55  % (14894)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.56  % (14893)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.50/0.58  % (14902)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.50/0.58  % (14910)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.50/0.58  % (14901)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.50/0.58  % (14909)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.71/0.59  % (14909)Refutation found. Thanks to Tanya!
% 1.71/0.59  % SZS status Theorem for theBenchmark
% 1.71/0.59  % SZS output start Proof for theBenchmark
% 1.71/0.59  fof(f172,plain,(
% 1.71/0.59    $false),
% 1.71/0.59    inference(avatar_sat_refutation,[],[f92,f98,f103,f117,f132,f171])).
% 1.71/0.59  fof(f171,plain,(
% 1.71/0.59    ~spl7_1 | ~spl7_8),
% 1.71/0.59    inference(avatar_contradiction_clause,[],[f170])).
% 1.71/0.59  fof(f170,plain,(
% 1.71/0.59    $false | (~spl7_1 | ~spl7_8)),
% 1.71/0.59    inference(trivial_inequality_removal,[],[f169])).
% 1.71/0.59  fof(f169,plain,(
% 1.71/0.59    sK0 != sK0 | (~spl7_1 | ~spl7_8)),
% 1.71/0.59    inference(resolution,[],[f168,f91])).
% 1.71/0.59  fof(f91,plain,(
% 1.71/0.59    r2_hidden(sK0,sK3) | ~spl7_1),
% 1.71/0.59    inference(avatar_component_clause,[],[f89])).
% 1.71/0.59  fof(f89,plain,(
% 1.71/0.59    spl7_1 <=> r2_hidden(sK0,sK3)),
% 1.71/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.71/0.59  fof(f168,plain,(
% 1.71/0.59    ( ! [X0] : (~r2_hidden(X0,sK3) | sK0 != X0) ) | ~spl7_8),
% 1.71/0.59    inference(duplicate_literal_removal,[],[f167])).
% 1.71/0.59  fof(f167,plain,(
% 1.71/0.59    ( ! [X0] : (sK0 != X0 | ~r2_hidden(X0,sK3) | ~r2_hidden(X0,sK3)) ) | ~spl7_8),
% 1.71/0.59    inference(resolution,[],[f166,f142])).
% 1.71/0.59  fof(f142,plain,(
% 1.71/0.59    ( ! [X0] : (r2_hidden(sK5(X0),sK1) | ~r2_hidden(X0,sK3)) ) | ~spl7_8),
% 1.71/0.59    inference(duplicate_literal_removal,[],[f140])).
% 1.71/0.59  fof(f140,plain,(
% 1.71/0.59    ( ! [X0] : (r2_hidden(sK5(X0),sK1) | ~r2_hidden(X0,sK3) | ~r2_hidden(X0,sK3)) ) | ~spl7_8),
% 1.71/0.59    inference(resolution,[],[f136,f131])).
% 1.71/0.59  fof(f131,plain,(
% 1.71/0.59    ( ! [X0] : (r2_hidden(X0,k2_zfmisc_1(sK1,sK2)) | ~r2_hidden(X0,sK3)) ) | ~spl7_8),
% 1.71/0.59    inference(avatar_component_clause,[],[f130])).
% 1.71/0.59  fof(f130,plain,(
% 1.71/0.59    spl7_8 <=> ! [X0] : (~r2_hidden(X0,sK3) | r2_hidden(X0,k2_zfmisc_1(sK1,sK2)))),
% 1.71/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 1.71/0.59  fof(f136,plain,(
% 1.71/0.59    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(sK5(X0),sK1) | ~r2_hidden(X0,sK3)) ) | ~spl7_8),
% 1.71/0.59    inference(superposition,[],[f134,f62])).
% 1.71/0.59  fof(f62,plain,(
% 1.71/0.59    ( ! [X2,X0,X1] : (k4_tarski(sK5(X0),sK6(X0)) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 1.71/0.59    inference(cnf_transformation,[],[f34])).
% 1.71/0.59  fof(f34,plain,(
% 1.71/0.59    ! [X0,X1,X2] : (? [X3,X4] : k4_tarski(X3,X4) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 1.71/0.59    inference(ennf_transformation,[],[f14])).
% 1.71/0.59  fof(f14,axiom,(
% 1.71/0.59    ! [X0,X1,X2] : ~(! [X3,X4] : k4_tarski(X3,X4) != X0 & r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 1.71/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l139_zfmisc_1)).
% 1.71/0.59  fof(f134,plain,(
% 1.71/0.59    ( ! [X2,X1] : (~r2_hidden(k4_tarski(X1,X2),sK3) | r2_hidden(X1,sK1)) ) | ~spl7_8),
% 1.71/0.59    inference(resolution,[],[f131,f64])).
% 1.71/0.59  fof(f64,plain,(
% 1.71/0.59    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 1.71/0.59    inference(cnf_transformation,[],[f16])).
% 1.71/0.59  fof(f16,axiom,(
% 1.71/0.59    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 1.71/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_zfmisc_1)).
% 1.71/0.59  fof(f166,plain,(
% 1.71/0.59    ( ! [X0] : (~r2_hidden(sK5(X0),sK1) | sK0 != X0 | ~r2_hidden(X0,sK3)) ) | ~spl7_8),
% 1.71/0.59    inference(duplicate_literal_removal,[],[f165])).
% 1.71/0.59  fof(f165,plain,(
% 1.71/0.59    ( ! [X0] : (~r2_hidden(sK5(X0),sK1) | sK0 != X0 | ~r2_hidden(X0,sK3) | ~r2_hidden(X0,sK3)) ) | ~spl7_8),
% 1.71/0.59    inference(resolution,[],[f137,f154])).
% 1.71/0.59  fof(f154,plain,(
% 1.71/0.59    ( ! [X0] : (r2_hidden(sK6(X0),sK2) | ~r2_hidden(X0,sK3)) ) | ~spl7_8),
% 1.71/0.59    inference(duplicate_literal_removal,[],[f152])).
% 1.71/0.59  fof(f152,plain,(
% 1.71/0.59    ( ! [X0] : (r2_hidden(sK6(X0),sK2) | ~r2_hidden(X0,sK3) | ~r2_hidden(X0,sK3)) ) | ~spl7_8),
% 1.71/0.59    inference(resolution,[],[f139,f131])).
% 1.71/0.59  fof(f139,plain,(
% 1.71/0.59    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(sK6(X0),sK2) | ~r2_hidden(X0,sK3)) ) | ~spl7_8),
% 1.71/0.59    inference(superposition,[],[f135,f62])).
% 1.71/0.59  fof(f135,plain,(
% 1.71/0.59    ( ! [X4,X3] : (~r2_hidden(k4_tarski(X3,X4),sK3) | r2_hidden(X4,sK2)) ) | ~spl7_8),
% 1.71/0.59    inference(resolution,[],[f131,f65])).
% 1.71/0.59  fof(f65,plain,(
% 1.71/0.59    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 1.71/0.59    inference(cnf_transformation,[],[f16])).
% 1.71/0.59  fof(f137,plain,(
% 1.71/0.59    ( ! [X0] : (~r2_hidden(sK6(X0),sK2) | ~r2_hidden(sK5(X0),sK1) | sK0 != X0 | ~r2_hidden(X0,sK3)) ) | ~spl7_8),
% 1.71/0.59    inference(resolution,[],[f118,f131])).
% 1.71/0.59  fof(f118,plain,(
% 1.71/0.59    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | ~r2_hidden(sK5(X0),sK1) | ~r2_hidden(sK6(X0),sK2) | sK0 != X0) )),
% 1.71/0.59    inference(superposition,[],[f35,f62])).
% 1.71/0.59  fof(f35,plain,(
% 1.71/0.59    ( ! [X4,X5] : (k4_tarski(X4,X5) != sK0 | ~r2_hidden(X4,sK1) | ~r2_hidden(X5,sK2)) )),
% 1.71/0.59    inference(cnf_transformation,[],[f25])).
% 1.71/0.59  fof(f25,plain,(
% 1.71/0.59    ? [X0,X1,X2,X3] : (! [X4,X5] : (~r2_hidden(X5,X2) | ~r2_hidden(X4,X1) | k4_tarski(X4,X5) != X0) & r2_hidden(X0,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 1.71/0.59    inference(flattening,[],[f24])).
% 1.71/0.59  fof(f24,plain,(
% 1.71/0.59    ? [X0,X1,X2,X3] : ((! [X4,X5] : (~r2_hidden(X5,X2) | ~r2_hidden(X4,X1) | k4_tarski(X4,X5) != X0) & r2_hidden(X0,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 1.71/0.59    inference(ennf_transformation,[],[f23])).
% 1.71/0.59  fof(f23,negated_conjecture,(
% 1.71/0.59    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) => ~(! [X4,X5] : ~(r2_hidden(X5,X2) & r2_hidden(X4,X1) & k4_tarski(X4,X5) = X0) & r2_hidden(X0,X3)))),
% 1.71/0.59    inference(negated_conjecture,[],[f22])).
% 1.71/0.59  fof(f22,conjecture,(
% 1.71/0.59    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) => ~(! [X4,X5] : ~(r2_hidden(X5,X2) & r2_hidden(X4,X1) & k4_tarski(X4,X5) = X0) & r2_hidden(X0,X3)))),
% 1.71/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_relset_1)).
% 1.71/0.59  fof(f132,plain,(
% 1.71/0.59    spl7_5 | spl7_8 | ~spl7_3),
% 1.71/0.59    inference(avatar_split_clause,[],[f119,f100,f130,f114])).
% 1.71/0.59  fof(f114,plain,(
% 1.71/0.59    spl7_5 <=> v1_xboole_0(k2_zfmisc_1(sK1,sK2))),
% 1.71/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 1.71/0.59  fof(f100,plain,(
% 1.71/0.59    spl7_3 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.71/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 1.71/0.59  fof(f119,plain,(
% 1.71/0.59    ( ! [X0] : (~r2_hidden(X0,sK3) | v1_xboole_0(k2_zfmisc_1(sK1,sK2)) | r2_hidden(X0,k2_zfmisc_1(sK1,sK2))) ) | ~spl7_3),
% 1.71/0.59    inference(resolution,[],[f104,f45])).
% 1.71/0.59  fof(f45,plain,(
% 1.71/0.59    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 1.71/0.59    inference(cnf_transformation,[],[f29])).
% 1.71/0.59  fof(f29,plain,(
% 1.71/0.59    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.71/0.59    inference(flattening,[],[f28])).
% 1.71/0.59  fof(f28,plain,(
% 1.71/0.59    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.71/0.59    inference(ennf_transformation,[],[f19])).
% 1.71/0.59  fof(f19,axiom,(
% 1.71/0.59    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.71/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 1.71/0.59  fof(f104,plain,(
% 1.71/0.59    ( ! [X0] : (m1_subset_1(X0,k2_zfmisc_1(sK1,sK2)) | ~r2_hidden(X0,sK3)) ) | ~spl7_3),
% 1.71/0.59    inference(resolution,[],[f102,f51])).
% 1.71/0.59  fof(f51,plain,(
% 1.71/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1) | m1_subset_1(X0,X2)) )),
% 1.71/0.59    inference(cnf_transformation,[],[f32])).
% 1.71/0.59  fof(f32,plain,(
% 1.71/0.59    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.71/0.59    inference(flattening,[],[f31])).
% 1.71/0.59  fof(f31,plain,(
% 1.71/0.59    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 1.71/0.59    inference(ennf_transformation,[],[f21])).
% 1.71/0.59  fof(f21,axiom,(
% 1.71/0.59    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 1.71/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 1.71/0.59  fof(f102,plain,(
% 1.71/0.59    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl7_3),
% 1.71/0.59    inference(avatar_component_clause,[],[f100])).
% 1.71/0.59  fof(f117,plain,(
% 1.71/0.59    spl7_2 | ~spl7_5 | ~spl7_3),
% 1.71/0.59    inference(avatar_split_clause,[],[f106,f100,f114,f95])).
% 1.71/0.60  fof(f95,plain,(
% 1.71/0.60    spl7_2 <=> v1_xboole_0(sK3)),
% 1.71/0.60    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 1.71/0.60  fof(f106,plain,(
% 1.71/0.60    ~v1_xboole_0(k2_zfmisc_1(sK1,sK2)) | v1_xboole_0(sK3) | ~spl7_3),
% 1.71/0.60    inference(resolution,[],[f102,f38])).
% 1.71/0.60  fof(f38,plain,(
% 1.71/0.60    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0) | v1_xboole_0(X1)) )),
% 1.71/0.60    inference(cnf_transformation,[],[f26])).
% 1.71/0.60  fof(f26,plain,(
% 1.71/0.60    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 1.71/0.60    inference(ennf_transformation,[],[f17])).
% 1.71/0.60  fof(f17,axiom,(
% 1.71/0.60    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 1.71/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).
% 1.71/0.60  fof(f103,plain,(
% 1.71/0.60    spl7_3),
% 1.71/0.60    inference(avatar_split_clause,[],[f36,f100])).
% 1.71/0.60  fof(f36,plain,(
% 1.71/0.60    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.71/0.60    inference(cnf_transformation,[],[f25])).
% 1.71/0.60  fof(f98,plain,(
% 1.71/0.60    ~spl7_2 | ~spl7_1),
% 1.71/0.60    inference(avatar_split_clause,[],[f93,f89,f95])).
% 1.71/0.60  fof(f93,plain,(
% 1.71/0.60    ~v1_xboole_0(sK3) | ~spl7_1),
% 1.71/0.60    inference(resolution,[],[f91,f48])).
% 1.71/0.60  fof(f48,plain,(
% 1.71/0.60    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~v1_xboole_0(X1)) )),
% 1.71/0.60    inference(cnf_transformation,[],[f30])).
% 1.71/0.60  fof(f30,plain,(
% 1.71/0.60    ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1))),
% 1.71/0.60    inference(ennf_transformation,[],[f5])).
% 1.71/0.60  fof(f5,axiom,(
% 1.71/0.60    ! [X0,X1] : ~(v1_xboole_0(X1) & r2_hidden(X0,X1))),
% 1.71/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).
% 1.71/0.60  fof(f92,plain,(
% 1.71/0.60    spl7_1),
% 1.71/0.60    inference(avatar_split_clause,[],[f37,f89])).
% 1.71/0.60  fof(f37,plain,(
% 1.71/0.60    r2_hidden(sK0,sK3)),
% 1.71/0.60    inference(cnf_transformation,[],[f25])).
% 1.71/0.60  % SZS output end Proof for theBenchmark
% 1.71/0.60  % (14909)------------------------------
% 1.71/0.60  % (14909)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.71/0.60  % (14909)Termination reason: Refutation
% 1.71/0.60  
% 1.71/0.60  % (14909)Memory used [KB]: 10746
% 1.71/0.60  % (14909)Time elapsed: 0.146 s
% 1.71/0.60  % (14909)------------------------------
% 1.71/0.60  % (14909)------------------------------
% 1.71/0.60  % (14906)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.71/0.60  % (14890)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.71/0.60  % (14898)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.71/0.60  % (14886)Success in time 0.232 s
%------------------------------------------------------------------------------
