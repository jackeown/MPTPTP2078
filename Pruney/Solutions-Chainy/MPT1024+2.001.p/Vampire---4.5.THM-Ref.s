%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:12 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 236 expanded)
%              Number of leaves         :   32 ( 104 expanded)
%              Depth                    :    9
%              Number of atoms          :  380 ( 728 expanded)
%              Number of equality atoms :   74 ( 143 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f322,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f69,f73,f77,f89,f93,f98,f118,f130,f134,f146,f159,f166,f185,f189,f194,f198,f215,f245,f271,f301,f320,f321])).

fof(f321,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | k1_relat_1(sK3) != k1_relset_1(sK0,sK1,sK3)
    | k1_xboole_0 != sK0
    | r2_hidden(sK6(sK4,sK2,sK3),sK0)
    | ~ r2_hidden(sK6(sK4,sK2,sK3),k1_relat_1(sK3)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f320,plain,
    ( spl7_37
    | ~ spl7_30
    | ~ spl7_35 ),
    inference(avatar_split_clause,[],[f315,f299,f269,f318])).

fof(f318,plain,
    ( spl7_37
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_37])])).

fof(f269,plain,
    ( spl7_30
  <=> v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).

fof(f299,plain,
    ( spl7_35
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).

fof(f315,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl7_30
    | ~ spl7_35 ),
    inference(subsumption_resolution,[],[f307,f270])).

fof(f270,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl7_30 ),
    inference(avatar_component_clause,[],[f269])).

fof(f307,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl7_35 ),
    inference(resolution,[],[f300,f61])).

fof(f61,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f300,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl7_35 ),
    inference(avatar_component_clause,[],[f299])).

fof(f301,plain,
    ( spl7_35
    | ~ spl7_3
    | ~ spl7_17
    | ~ spl7_26 ),
    inference(avatar_split_clause,[],[f264,f213,f164,f75,f299])).

fof(f75,plain,
    ( spl7_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f164,plain,
    ( spl7_17
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f213,plain,
    ( spl7_26
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f264,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl7_3
    | ~ spl7_17
    | ~ spl7_26 ),
    inference(forward_demodulation,[],[f254,f165])).

fof(f165,plain,
    ( k1_xboole_0 = sK1
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f164])).

fof(f254,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl7_3
    | ~ spl7_26 ),
    inference(superposition,[],[f76,f214])).

fof(f214,plain,
    ( k1_xboole_0 = sK0
    | ~ spl7_26 ),
    inference(avatar_component_clause,[],[f213])).

fof(f76,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f75])).

fof(f271,plain,
    ( spl7_30
    | ~ spl7_2
    | ~ spl7_17
    | ~ spl7_26 ),
    inference(avatar_split_clause,[],[f263,f213,f164,f71,f269])).

fof(f71,plain,
    ( spl7_2
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f263,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl7_2
    | ~ spl7_17
    | ~ spl7_26 ),
    inference(forward_demodulation,[],[f253,f165])).

fof(f253,plain,
    ( v1_funct_2(sK3,k1_xboole_0,sK1)
    | ~ spl7_2
    | ~ spl7_26 ),
    inference(superposition,[],[f72,f214])).

fof(f72,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f71])).

fof(f245,plain,
    ( spl7_15
    | ~ spl7_25 ),
    inference(avatar_contradiction_clause,[],[f244])).

fof(f244,plain,
    ( $false
    | spl7_15
    | ~ spl7_25 ),
    inference(subsumption_resolution,[],[f232,f59])).

fof(f59,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f232,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl7_15
    | ~ spl7_25 ),
    inference(superposition,[],[f158,f211])).

fof(f211,plain,
    ( k1_xboole_0 = sK3
    | ~ spl7_25 ),
    inference(avatar_component_clause,[],[f210])).

fof(f210,plain,
    ( spl7_25
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f158,plain,
    ( ~ v1_xboole_0(sK3)
    | spl7_15 ),
    inference(avatar_component_clause,[],[f157])).

fof(f157,plain,
    ( spl7_15
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f215,plain,
    ( spl7_25
    | spl7_26
    | ~ spl7_21
    | ~ spl7_24 ),
    inference(avatar_split_clause,[],[f207,f196,f183,f213,f210])).

fof(f183,plain,
    ( spl7_21
  <=> v1_funct_2(sK3,sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f196,plain,
    ( spl7_24
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f207,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK3
    | ~ spl7_21
    | ~ spl7_24 ),
    inference(subsumption_resolution,[],[f200,f184])).

fof(f184,plain,
    ( v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ spl7_21 ),
    inference(avatar_component_clause,[],[f183])).

fof(f200,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK3
    | ~ v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ spl7_24 ),
    inference(resolution,[],[f197,f63])).

fof(f63,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X1
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f197,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f196])).

fof(f198,plain,
    ( spl7_24
    | ~ spl7_3
    | ~ spl7_17 ),
    inference(avatar_split_clause,[],[f173,f164,f75,f196])).

fof(f173,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl7_3
    | ~ spl7_17 ),
    inference(superposition,[],[f76,f165])).

fof(f194,plain,
    ( sK0 != k1_relset_1(sK0,sK1,sK3)
    | k1_relat_1(sK3) != k1_relset_1(sK0,sK1,sK3)
    | r2_hidden(sK6(sK4,sK2,sK3),sK0)
    | ~ r2_hidden(sK6(sK4,sK2,sK3),k1_relat_1(sK3)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f189,plain,
    ( ~ spl7_22
    | ~ spl7_1
    | ~ spl7_4
    | ~ spl7_9
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f155,f144,f116,f87,f67,f187])).

fof(f187,plain,
    ( spl7_22
  <=> r2_hidden(sK6(sK4,sK2,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f67,plain,
    ( spl7_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f87,plain,
    ( spl7_4
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f116,plain,
    ( spl7_9
  <=> r2_hidden(sK6(sK4,sK2,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f144,plain,
    ( spl7_14
  <=> r2_hidden(k4_tarski(sK6(sK4,sK2,sK3),sK4),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f155,plain,
    ( ~ r2_hidden(sK6(sK4,sK2,sK3),sK0)
    | ~ spl7_1
    | ~ spl7_4
    | ~ spl7_9
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f120,f154])).

% (8164)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
fof(f154,plain,
    ( sK4 = k1_funct_1(sK3,sK6(sK4,sK2,sK3))
    | ~ spl7_1
    | ~ spl7_4
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f153,f88])).

fof(f88,plain,
    ( v1_relat_1(sK3)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f87])).

fof(f153,plain,
    ( sK4 = k1_funct_1(sK3,sK6(sK4,sK2,sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl7_1
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f149,f68])).

fof(f68,plain,
    ( v1_funct_1(sK3)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f67])).

fof(f149,plain,
    ( ~ v1_funct_1(sK3)
    | sK4 = k1_funct_1(sK3,sK6(sK4,sK2,sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl7_14 ),
    inference(resolution,[],[f145,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | k1_funct_1(X2,X0) = X1
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

% (8161)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% (8156)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% (8167)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% (8157)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% (8169)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% (8168)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% (8169)Refutation not found, incomplete strategy% (8169)------------------------------
% (8169)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (8169)Termination reason: Refutation not found, incomplete strategy

% (8169)Memory used [KB]: 10618
% (8169)Time elapsed: 0.091 s
% (8169)------------------------------
% (8169)------------------------------
% (8165)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
fof(f145,plain,
    ( r2_hidden(k4_tarski(sK6(sK4,sK2,sK3),sK4),sK3)
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f144])).

fof(f120,plain,
    ( ~ r2_hidden(sK6(sK4,sK2,sK3),sK0)
    | sK4 != k1_funct_1(sK3,sK6(sK4,sK2,sK3))
    | ~ spl7_9 ),
    inference(resolution,[],[f117,f32])).

fof(f32,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,sK2)
      | ~ r2_hidden(X5,sK0)
      | sK4 != k1_funct_1(sK3,X5) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ~ ( k1_funct_1(X3,X5) = X4
                    & r2_hidden(X5,X2)
                    & r2_hidden(X5,X0) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ~ ( ! [X5] :
                ~ ( k1_funct_1(X3,X5) = X4
                  & r2_hidden(X5,X2)
                  & r2_hidden(X5,X0) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t115_funct_2)).

fof(f117,plain,
    ( r2_hidden(sK6(sK4,sK2,sK3),sK2)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f116])).

fof(f185,plain,
    ( spl7_21
    | ~ spl7_2
    | ~ spl7_17 ),
    inference(avatar_split_clause,[],[f174,f164,f71,f183])).

fof(f174,plain,
    ( v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ spl7_2
    | ~ spl7_17 ),
    inference(superposition,[],[f72,f165])).

fof(f166,plain,
    ( spl7_16
    | spl7_17
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f84,f75,f71,f164,f161])).

fof(f161,plain,
    ( spl7_16
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f84,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f80,f72])).

fof(f80,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ spl7_3 ),
    inference(resolution,[],[f76,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f159,plain,
    ( ~ spl7_15
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f150,f144,f157])).

fof(f150,plain,
    ( ~ v1_xboole_0(sK3)
    | ~ spl7_14 ),
    inference(resolution,[],[f145,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f146,plain,
    ( spl7_14
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f104,f96,f87,f144])).

fof(f96,plain,
    ( spl7_6
  <=> r2_hidden(sK4,k9_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f104,plain,
    ( r2_hidden(k4_tarski(sK6(sK4,sK2,sK3),sK4),sK3)
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f100,f88])).

fof(f100,plain,
    ( r2_hidden(k4_tarski(sK6(sK4,sK2,sK3),sK4),sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl7_6 ),
    inference(resolution,[],[f97,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(k4_tarski(sK6(X0,X1,X2),X0),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

fof(f97,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f96])).

fof(f134,plain,
    ( spl7_12
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f103,f96,f87,f132])).

fof(f132,plain,
    ( spl7_12
  <=> r2_hidden(sK6(sK4,sK2,sK3),k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f103,plain,
    ( r2_hidden(sK6(sK4,sK2,sK3),k1_relat_1(sK3))
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f99,f88])).

fof(f99,plain,
    ( r2_hidden(sK6(sK4,sK2,sK3),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl7_6 ),
    inference(resolution,[],[f97,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(sK6(X0,X1,X2),k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f130,plain,
    ( spl7_11
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f78,f75,f128])).

fof(f128,plain,
    ( spl7_11
  <=> k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f78,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)
    | ~ spl7_3 ),
    inference(resolution,[],[f76,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f118,plain,
    ( spl7_9
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f105,f96,f87,f116])).

fof(f105,plain,
    ( r2_hidden(sK6(sK4,sK2,sK3),sK2)
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f101,f88])).

fof(f101,plain,
    ( r2_hidden(sK6(sK4,sK2,sK3),sK2)
    | ~ v1_relat_1(sK3)
    | ~ spl7_6 ),
    inference(resolution,[],[f97,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(sK6(X0,X1,X2),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f98,plain,
    ( spl7_6
    | ~ spl7_3
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f94,f91,f75,f96])).

fof(f91,plain,
    ( spl7_5
  <=> r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f94,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl7_3
    | ~ spl7_5 ),
    inference(forward_demodulation,[],[f92,f82])).

fof(f82,plain,
    ( ! [X0] : k7_relset_1(sK0,sK1,sK3,X0) = k9_relat_1(sK3,X0)
    | ~ spl7_3 ),
    inference(resolution,[],[f76,f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f92,plain,
    ( r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f91])).

fof(f93,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f33,f91])).

fof(f33,plain,(
    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f19])).

fof(f89,plain,
    ( spl7_4
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f81,f75,f87])).

fof(f81,plain,
    ( v1_relat_1(sK3)
    | ~ spl7_3 ),
    inference(resolution,[],[f76,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f77,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f36,f75])).

fof(f36,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f19])).

fof(f73,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f35,f71])).

fof(f35,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f69,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f34,f67])).

fof(f34,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:28:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (8155)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.46  % (8152)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.47  % (8163)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.47  % (8149)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.48  % (8154)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.48  % (8151)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.48  % (8153)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.48  % (8158)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.49  % (8149)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f322,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f69,f73,f77,f89,f93,f98,f118,f130,f134,f146,f159,f166,f185,f189,f194,f198,f215,f245,f271,f301,f320,f321])).
% 0.21/0.49  fof(f321,plain,(
% 0.21/0.49    k1_xboole_0 != sK1 | k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | k1_relat_1(sK3) != k1_relset_1(sK0,sK1,sK3) | k1_xboole_0 != sK0 | r2_hidden(sK6(sK4,sK2,sK3),sK0) | ~r2_hidden(sK6(sK4,sK2,sK3),k1_relat_1(sK3))),
% 0.21/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.49  fof(f320,plain,(
% 0.21/0.49    spl7_37 | ~spl7_30 | ~spl7_35),
% 0.21/0.49    inference(avatar_split_clause,[],[f315,f299,f269,f318])).
% 0.21/0.49  fof(f318,plain,(
% 0.21/0.49    spl7_37 <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_37])])).
% 0.21/0.49  fof(f269,plain,(
% 0.21/0.49    spl7_30 <=> v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).
% 0.21/0.49  fof(f299,plain,(
% 0.21/0.49    spl7_35 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).
% 0.21/0.49  fof(f315,plain,(
% 0.21/0.49    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | (~spl7_30 | ~spl7_35)),
% 0.21/0.49    inference(subsumption_resolution,[],[f307,f270])).
% 0.21/0.49  fof(f270,plain,(
% 0.21/0.49    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | ~spl7_30),
% 0.21/0.49    inference(avatar_component_clause,[],[f269])).
% 0.21/0.49  fof(f307,plain,(
% 0.21/0.49    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | ~v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | ~spl7_35),
% 0.21/0.49    inference(resolution,[],[f300,f61])).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1)) )),
% 0.21/0.49    inference(equality_resolution,[],[f50])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(flattening,[],[f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.49  fof(f300,plain,(
% 0.21/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl7_35),
% 0.21/0.49    inference(avatar_component_clause,[],[f299])).
% 0.21/0.49  fof(f301,plain,(
% 0.21/0.49    spl7_35 | ~spl7_3 | ~spl7_17 | ~spl7_26),
% 0.21/0.49    inference(avatar_split_clause,[],[f264,f213,f164,f75,f299])).
% 0.21/0.49  fof(f75,plain,(
% 0.21/0.49    spl7_3 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.21/0.49  fof(f164,plain,(
% 0.21/0.49    spl7_17 <=> k1_xboole_0 = sK1),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 0.21/0.49  fof(f213,plain,(
% 0.21/0.49    spl7_26 <=> k1_xboole_0 = sK0),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).
% 0.21/0.49  fof(f264,plain,(
% 0.21/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl7_3 | ~spl7_17 | ~spl7_26)),
% 0.21/0.49    inference(forward_demodulation,[],[f254,f165])).
% 0.21/0.49  fof(f165,plain,(
% 0.21/0.49    k1_xboole_0 = sK1 | ~spl7_17),
% 0.21/0.49    inference(avatar_component_clause,[],[f164])).
% 0.21/0.49  fof(f254,plain,(
% 0.21/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | (~spl7_3 | ~spl7_26)),
% 0.21/0.49    inference(superposition,[],[f76,f214])).
% 0.21/0.49  fof(f214,plain,(
% 0.21/0.49    k1_xboole_0 = sK0 | ~spl7_26),
% 0.21/0.49    inference(avatar_component_clause,[],[f213])).
% 0.21/0.49  fof(f76,plain,(
% 0.21/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl7_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f75])).
% 0.21/0.49  fof(f271,plain,(
% 0.21/0.49    spl7_30 | ~spl7_2 | ~spl7_17 | ~spl7_26),
% 0.21/0.49    inference(avatar_split_clause,[],[f263,f213,f164,f71,f269])).
% 0.21/0.49  fof(f71,plain,(
% 0.21/0.49    spl7_2 <=> v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.21/0.49  fof(f263,plain,(
% 0.21/0.49    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | (~spl7_2 | ~spl7_17 | ~spl7_26)),
% 0.21/0.49    inference(forward_demodulation,[],[f253,f165])).
% 0.21/0.49  fof(f253,plain,(
% 0.21/0.49    v1_funct_2(sK3,k1_xboole_0,sK1) | (~spl7_2 | ~spl7_26)),
% 0.21/0.49    inference(superposition,[],[f72,f214])).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    v1_funct_2(sK3,sK0,sK1) | ~spl7_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f71])).
% 0.21/0.49  fof(f245,plain,(
% 0.21/0.49    spl7_15 | ~spl7_25),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f244])).
% 0.21/0.49  fof(f244,plain,(
% 0.21/0.49    $false | (spl7_15 | ~spl7_25)),
% 0.21/0.49    inference(subsumption_resolution,[],[f232,f59])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    v1_xboole_0(k1_xboole_0)),
% 0.21/0.49    inference(cnf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    v1_xboole_0(k1_xboole_0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.49  fof(f232,plain,(
% 0.21/0.49    ~v1_xboole_0(k1_xboole_0) | (spl7_15 | ~spl7_25)),
% 0.21/0.49    inference(superposition,[],[f158,f211])).
% 0.21/0.49  fof(f211,plain,(
% 0.21/0.49    k1_xboole_0 = sK3 | ~spl7_25),
% 0.21/0.49    inference(avatar_component_clause,[],[f210])).
% 0.21/0.49  fof(f210,plain,(
% 0.21/0.49    spl7_25 <=> k1_xboole_0 = sK3),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).
% 0.21/0.49  fof(f158,plain,(
% 0.21/0.49    ~v1_xboole_0(sK3) | spl7_15),
% 0.21/0.49    inference(avatar_component_clause,[],[f157])).
% 0.21/0.49  fof(f157,plain,(
% 0.21/0.49    spl7_15 <=> v1_xboole_0(sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 0.21/0.49  fof(f215,plain,(
% 0.21/0.49    spl7_25 | spl7_26 | ~spl7_21 | ~spl7_24),
% 0.21/0.49    inference(avatar_split_clause,[],[f207,f196,f183,f213,f210])).
% 0.21/0.49  fof(f183,plain,(
% 0.21/0.49    spl7_21 <=> v1_funct_2(sK3,sK0,k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).
% 0.21/0.49  fof(f196,plain,(
% 0.21/0.49    spl7_24 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).
% 0.21/0.49  fof(f207,plain,(
% 0.21/0.49    k1_xboole_0 = sK0 | k1_xboole_0 = sK3 | (~spl7_21 | ~spl7_24)),
% 0.21/0.49    inference(subsumption_resolution,[],[f200,f184])).
% 0.21/0.49  fof(f184,plain,(
% 0.21/0.49    v1_funct_2(sK3,sK0,k1_xboole_0) | ~spl7_21),
% 0.21/0.49    inference(avatar_component_clause,[],[f183])).
% 0.21/0.49  fof(f200,plain,(
% 0.21/0.49    k1_xboole_0 = sK0 | k1_xboole_0 = sK3 | ~v1_funct_2(sK3,sK0,k1_xboole_0) | ~spl7_24),
% 0.21/0.49    inference(resolution,[],[f197,f63])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0)) )),
% 0.21/0.49    inference(equality_resolution,[],[f48])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X1 | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f28])).
% 0.21/0.49  fof(f197,plain,(
% 0.21/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl7_24),
% 0.21/0.49    inference(avatar_component_clause,[],[f196])).
% 0.21/0.49  fof(f198,plain,(
% 0.21/0.49    spl7_24 | ~spl7_3 | ~spl7_17),
% 0.21/0.49    inference(avatar_split_clause,[],[f173,f164,f75,f196])).
% 0.21/0.49  fof(f173,plain,(
% 0.21/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | (~spl7_3 | ~spl7_17)),
% 0.21/0.49    inference(superposition,[],[f76,f165])).
% 0.21/0.49  fof(f194,plain,(
% 0.21/0.49    sK0 != k1_relset_1(sK0,sK1,sK3) | k1_relat_1(sK3) != k1_relset_1(sK0,sK1,sK3) | r2_hidden(sK6(sK4,sK2,sK3),sK0) | ~r2_hidden(sK6(sK4,sK2,sK3),k1_relat_1(sK3))),
% 0.21/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.49  fof(f189,plain,(
% 0.21/0.49    ~spl7_22 | ~spl7_1 | ~spl7_4 | ~spl7_9 | ~spl7_14),
% 0.21/0.49    inference(avatar_split_clause,[],[f155,f144,f116,f87,f67,f187])).
% 0.21/0.49  fof(f187,plain,(
% 0.21/0.49    spl7_22 <=> r2_hidden(sK6(sK4,sK2,sK3),sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    spl7_1 <=> v1_funct_1(sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.49  fof(f87,plain,(
% 0.21/0.49    spl7_4 <=> v1_relat_1(sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.21/0.49  fof(f116,plain,(
% 0.21/0.49    spl7_9 <=> r2_hidden(sK6(sK4,sK2,sK3),sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.21/0.49  fof(f144,plain,(
% 0.21/0.49    spl7_14 <=> r2_hidden(k4_tarski(sK6(sK4,sK2,sK3),sK4),sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 0.21/0.49  fof(f155,plain,(
% 0.21/0.49    ~r2_hidden(sK6(sK4,sK2,sK3),sK0) | (~spl7_1 | ~spl7_4 | ~spl7_9 | ~spl7_14)),
% 0.21/0.49    inference(subsumption_resolution,[],[f120,f154])).
% 0.21/0.49  % (8164)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.49  fof(f154,plain,(
% 0.21/0.49    sK4 = k1_funct_1(sK3,sK6(sK4,sK2,sK3)) | (~spl7_1 | ~spl7_4 | ~spl7_14)),
% 0.21/0.49    inference(subsumption_resolution,[],[f153,f88])).
% 0.21/0.49  fof(f88,plain,(
% 0.21/0.49    v1_relat_1(sK3) | ~spl7_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f87])).
% 0.21/0.49  fof(f153,plain,(
% 0.21/0.49    sK4 = k1_funct_1(sK3,sK6(sK4,sK2,sK3)) | ~v1_relat_1(sK3) | (~spl7_1 | ~spl7_14)),
% 0.21/0.49    inference(subsumption_resolution,[],[f149,f68])).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    v1_funct_1(sK3) | ~spl7_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f67])).
% 0.21/0.49  fof(f149,plain,(
% 0.21/0.49    ~v1_funct_1(sK3) | sK4 = k1_funct_1(sK3,sK6(sK4,sK2,sK3)) | ~v1_relat_1(sK3) | ~spl7_14),
% 0.21/0.49    inference(resolution,[],[f145,f39])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | k1_funct_1(X2,X0) = X1 | ~v1_relat_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.49    inference(flattening,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.49    inference(ennf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).
% 0.21/0.49  % (8161)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (8156)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.49  % (8167)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.49  % (8157)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.50  % (8169)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.50  % (8168)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.50  % (8169)Refutation not found, incomplete strategy% (8169)------------------------------
% 0.21/0.50  % (8169)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (8169)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (8169)Memory used [KB]: 10618
% 0.21/0.50  % (8169)Time elapsed: 0.091 s
% 0.21/0.50  % (8169)------------------------------
% 0.21/0.50  % (8169)------------------------------
% 0.21/0.50  % (8165)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.50  fof(f145,plain,(
% 0.21/0.50    r2_hidden(k4_tarski(sK6(sK4,sK2,sK3),sK4),sK3) | ~spl7_14),
% 0.21/0.50    inference(avatar_component_clause,[],[f144])).
% 0.21/0.50  fof(f120,plain,(
% 0.21/0.50    ~r2_hidden(sK6(sK4,sK2,sK3),sK0) | sK4 != k1_funct_1(sK3,sK6(sK4,sK2,sK3)) | ~spl7_9),
% 0.21/0.50    inference(resolution,[],[f117,f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ( ! [X5] : (~r2_hidden(X5,sK2) | ~r2_hidden(X5,sK0) | sK4 != k1_funct_1(sK3,X5)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.21/0.50    inference(flattening,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.21/0.50    inference(ennf_transformation,[],[f17])).
% 0.21/0.50  fof(f17,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.21/0.50    inference(negated_conjecture,[],[f16])).
% 0.21/0.50  fof(f16,conjecture,(
% 0.21/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t115_funct_2)).
% 0.21/0.50  fof(f117,plain,(
% 0.21/0.50    r2_hidden(sK6(sK4,sK2,sK3),sK2) | ~spl7_9),
% 0.21/0.50    inference(avatar_component_clause,[],[f116])).
% 0.21/0.50  fof(f185,plain,(
% 0.21/0.50    spl7_21 | ~spl7_2 | ~spl7_17),
% 0.21/0.50    inference(avatar_split_clause,[],[f174,f164,f71,f183])).
% 0.21/0.50  fof(f174,plain,(
% 0.21/0.50    v1_funct_2(sK3,sK0,k1_xboole_0) | (~spl7_2 | ~spl7_17)),
% 0.21/0.50    inference(superposition,[],[f72,f165])).
% 0.21/0.50  fof(f166,plain,(
% 0.21/0.50    spl7_16 | spl7_17 | ~spl7_2 | ~spl7_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f84,f75,f71,f164,f161])).
% 0.21/0.50  fof(f161,plain,(
% 0.21/0.50    spl7_16 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 0.21/0.50  fof(f84,plain,(
% 0.21/0.50    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | (~spl7_2 | ~spl7_3)),
% 0.21/0.50    inference(subsumption_resolution,[],[f80,f72])).
% 0.21/0.50  fof(f80,plain,(
% 0.21/0.50    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~v1_funct_2(sK3,sK0,sK1) | ~spl7_3),
% 0.21/0.50    inference(resolution,[],[f76,f52])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f28])).
% 0.21/0.50  fof(f159,plain,(
% 0.21/0.50    ~spl7_15 | ~spl7_14),
% 0.21/0.50    inference(avatar_split_clause,[],[f150,f144,f157])).
% 0.21/0.50  fof(f150,plain,(
% 0.21/0.50    ~v1_xboole_0(sK3) | ~spl7_14),
% 0.21/0.50    inference(resolution,[],[f145,f43])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.50  fof(f146,plain,(
% 0.21/0.50    spl7_14 | ~spl7_4 | ~spl7_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f104,f96,f87,f144])).
% 0.21/0.50  fof(f96,plain,(
% 0.21/0.50    spl7_6 <=> r2_hidden(sK4,k9_relat_1(sK3,sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.21/0.50  fof(f104,plain,(
% 0.21/0.50    r2_hidden(k4_tarski(sK6(sK4,sK2,sK3),sK4),sK3) | (~spl7_4 | ~spl7_6)),
% 0.21/0.50    inference(subsumption_resolution,[],[f100,f88])).
% 0.21/0.50  fof(f100,plain,(
% 0.21/0.50    r2_hidden(k4_tarski(sK6(sK4,sK2,sK3),sK4),sK3) | ~v1_relat_1(sK3) | ~spl7_6),
% 0.21/0.50    inference(resolution,[],[f97,f56])).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(k4_tarski(sK6(X0,X1,X2),X0),X2) | ~v1_relat_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.21/0.50    inference(ennf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).
% 0.21/0.50  fof(f97,plain,(
% 0.21/0.50    r2_hidden(sK4,k9_relat_1(sK3,sK2)) | ~spl7_6),
% 0.21/0.50    inference(avatar_component_clause,[],[f96])).
% 0.21/0.50  fof(f134,plain,(
% 0.21/0.50    spl7_12 | ~spl7_4 | ~spl7_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f103,f96,f87,f132])).
% 0.21/0.50  fof(f132,plain,(
% 0.21/0.50    spl7_12 <=> r2_hidden(sK6(sK4,sK2,sK3),k1_relat_1(sK3))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.21/0.50  fof(f103,plain,(
% 0.21/0.50    r2_hidden(sK6(sK4,sK2,sK3),k1_relat_1(sK3)) | (~spl7_4 | ~spl7_6)),
% 0.21/0.50    inference(subsumption_resolution,[],[f99,f88])).
% 0.21/0.50  fof(f99,plain,(
% 0.21/0.50    r2_hidden(sK6(sK4,sK2,sK3),k1_relat_1(sK3)) | ~v1_relat_1(sK3) | ~spl7_6),
% 0.21/0.50    inference(resolution,[],[f97,f55])).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(sK6(X0,X1,X2),k1_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f31])).
% 0.21/0.50  fof(f130,plain,(
% 0.21/0.50    spl7_11 | ~spl7_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f78,f75,f128])).
% 0.21/0.50  fof(f128,plain,(
% 0.21/0.50    spl7_11 <=> k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.21/0.50  fof(f78,plain,(
% 0.21/0.50    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) | ~spl7_3),
% 0.21/0.50    inference(resolution,[],[f76,f54])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relat_1(X2) = k1_relset_1(X0,X1,X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.50  fof(f118,plain,(
% 0.21/0.50    spl7_9 | ~spl7_4 | ~spl7_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f105,f96,f87,f116])).
% 0.21/0.50  fof(f105,plain,(
% 0.21/0.50    r2_hidden(sK6(sK4,sK2,sK3),sK2) | (~spl7_4 | ~spl7_6)),
% 0.21/0.50    inference(subsumption_resolution,[],[f101,f88])).
% 0.21/0.50  fof(f101,plain,(
% 0.21/0.50    r2_hidden(sK6(sK4,sK2,sK3),sK2) | ~v1_relat_1(sK3) | ~spl7_6),
% 0.21/0.50    inference(resolution,[],[f97,f57])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(sK6(X0,X1,X2),X1) | ~v1_relat_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f31])).
% 0.21/0.50  fof(f98,plain,(
% 0.21/0.50    spl7_6 | ~spl7_3 | ~spl7_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f94,f91,f75,f96])).
% 0.21/0.50  fof(f91,plain,(
% 0.21/0.50    spl7_5 <=> r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.21/0.50  fof(f94,plain,(
% 0.21/0.50    r2_hidden(sK4,k9_relat_1(sK3,sK2)) | (~spl7_3 | ~spl7_5)),
% 0.21/0.50    inference(forward_demodulation,[],[f92,f82])).
% 0.21/0.50  fof(f82,plain,(
% 0.21/0.50    ( ! [X0] : (k7_relset_1(sK0,sK1,sK3,X0) = k9_relat_1(sK3,X0)) ) | ~spl7_3),
% 0.21/0.50    inference(resolution,[],[f76,f44])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.21/0.50  fof(f92,plain,(
% 0.21/0.50    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) | ~spl7_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f91])).
% 0.21/0.50  fof(f93,plain,(
% 0.21/0.50    spl7_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f33,f91])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f89,plain,(
% 0.21/0.50    spl7_4 | ~spl7_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f81,f75,f87])).
% 0.21/0.50  fof(f81,plain,(
% 0.21/0.50    v1_relat_1(sK3) | ~spl7_3),
% 0.21/0.50    inference(resolution,[],[f76,f45])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.50  fof(f77,plain,(
% 0.21/0.50    spl7_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f36,f75])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f73,plain,(
% 0.21/0.50    spl7_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f35,f71])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f69,plain,(
% 0.21/0.50    spl7_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f34,f67])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    v1_funct_1(sK3)),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (8149)------------------------------
% 0.21/0.50  % (8149)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (8149)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (8149)Memory used [KB]: 6268
% 0.21/0.50  % (8149)Time elapsed: 0.078 s
% 0.21/0.50  % (8149)------------------------------
% 0.21/0.50  % (8149)------------------------------
% 0.21/0.50  % (8148)Success in time 0.154 s
%------------------------------------------------------------------------------
