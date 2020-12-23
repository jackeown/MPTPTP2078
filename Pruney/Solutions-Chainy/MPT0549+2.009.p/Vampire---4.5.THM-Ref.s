%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:36 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 266 expanded)
%              Number of leaves         :   30 ( 102 expanded)
%              Depth                    :   11
%              Number of atoms          :  396 ( 813 expanded)
%              Number of equality atoms :   83 ( 143 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (1841)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% (1838)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% (1855)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% (1854)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% (1858)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
fof(f958,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f68,f71,f75,f79,f83,f589,f612,f614,f627,f643,f646,f658,f662,f671,f675,f921,f938,f957])).

fof(f957,plain,
    ( spl4_63
    | ~ spl4_1
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f664,f73,f63,f610])).

fof(f610,plain,
    ( spl4_63
  <=> k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_63])])).

fof(f63,plain,
    ( spl4_1
  <=> k1_xboole_0 = k9_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f73,plain,
    ( spl4_3
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f664,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ spl4_1
    | ~ spl4_3 ),
    inference(trivial_inequality_removal,[],[f663])).

fof(f663,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ spl4_1
    | ~ spl4_3 ),
    inference(superposition,[],[f459,f69])).

fof(f69,plain,
    ( k1_xboole_0 = k9_relat_1(sK1,sK0)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f459,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k9_relat_1(sK1,X0)
        | k1_xboole_0 = k7_relat_1(sK1,X0) )
    | ~ spl4_3 ),
    inference(resolution,[],[f97,f74])).

fof(f74,plain,
    ( v1_relat_1(sK1)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f73])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k7_relat_1(X0,X1)
      | k1_xboole_0 != k9_relat_1(X0,X1) ) ),
    inference(global_subsumption,[],[f51,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k9_relat_1(X0,X1)
      | k1_xboole_0 = k7_relat_1(X0,X1)
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f45,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f45,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f51,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f938,plain,(
    ~ spl4_73 ),
    inference(avatar_contradiction_clause,[],[f936])).

fof(f936,plain,
    ( $false
    | ~ spl4_73 ),
    inference(resolution,[],[f916,f84])).

fof(f84,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f47,f60])).

fof(f60,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f47,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f916,plain,
    ( r2_hidden(sK3(k1_relat_1(sK1),sK0),k1_xboole_0)
    | ~ spl4_73 ),
    inference(avatar_component_clause,[],[f915])).

fof(f915,plain,
    ( spl4_73
  <=> r2_hidden(sK3(k1_relat_1(sK1),sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_73])])).

fof(f921,plain,
    ( ~ spl4_68
    | spl4_73
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_63
    | ~ spl4_66
    | ~ spl4_69 ),
    inference(avatar_split_clause,[],[f919,f673,f656,f610,f81,f73,f915,f669])).

fof(f669,plain,
    ( spl4_68
  <=> r2_hidden(sK3(sK0,k1_relat_1(sK1)),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_68])])).

fof(f81,plain,
    ( spl4_5
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f656,plain,
    ( spl4_66
  <=> r2_hidden(sK3(k1_relat_1(sK1),sK0),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_66])])).

fof(f673,plain,
    ( spl4_69
  <=> r2_hidden(sK3(sK0,k1_relat_1(sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_69])])).

fof(f919,plain,
    ( r2_hidden(sK3(k1_relat_1(sK1),sK0),k1_xboole_0)
    | ~ r2_hidden(sK3(sK0,k1_relat_1(sK1)),k1_relat_1(sK1))
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_63
    | ~ spl4_66
    | ~ spl4_69 ),
    inference(forward_demodulation,[],[f918,f82])).

fof(f82,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f81])).

fof(f918,plain,
    ( r2_hidden(sK3(k1_relat_1(sK1),sK0),k1_relat_1(k1_xboole_0))
    | ~ r2_hidden(sK3(sK0,k1_relat_1(sK1)),k1_relat_1(sK1))
    | ~ spl4_3
    | ~ spl4_63
    | ~ spl4_66
    | ~ spl4_69 ),
    inference(forward_demodulation,[],[f897,f611])).

fof(f611,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ spl4_63 ),
    inference(avatar_component_clause,[],[f610])).

fof(f897,plain,
    ( r2_hidden(sK3(k1_relat_1(sK1),sK0),k1_relat_1(k7_relat_1(sK1,sK0)))
    | ~ r2_hidden(sK3(sK0,k1_relat_1(sK1)),k1_relat_1(sK1))
    | ~ spl4_3
    | ~ spl4_66
    | ~ spl4_69 ),
    inference(resolution,[],[f699,f707])).

fof(f707,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(X0,sK0),sK0)
        | ~ r2_hidden(sK3(sK0,k1_relat_1(sK1)),X0) )
    | ~ spl4_69 ),
    inference(resolution,[],[f698,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f698,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(X0,sK0)
        | ~ r2_hidden(sK3(sK0,k1_relat_1(sK1)),X0) )
    | ~ spl4_69 ),
    inference(resolution,[],[f674,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f674,plain,
    ( r2_hidden(sK3(sK0,k1_relat_1(sK1)),sK0)
    | ~ spl4_69 ),
    inference(avatar_component_clause,[],[f673])).

fof(f699,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(k1_relat_1(sK1),sK0),X0)
        | r2_hidden(sK3(k1_relat_1(sK1),sK0),k1_relat_1(k7_relat_1(sK1,X0))) )
    | ~ spl4_3
    | ~ spl4_66 ),
    inference(resolution,[],[f657,f197])).

fof(f197,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k1_relat_1(sK1))
        | ~ r2_hidden(X0,X1)
        | r2_hidden(X0,k1_relat_1(k7_relat_1(sK1,X1))) )
    | ~ spl4_3 ),
    inference(resolution,[],[f59,f74])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(X0,X1)
      | r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).

fof(f657,plain,
    ( r2_hidden(sK3(k1_relat_1(sK1),sK0),k1_relat_1(sK1))
    | ~ spl4_66 ),
    inference(avatar_component_clause,[],[f656])).

fof(f675,plain,
    ( spl4_69
    | spl4_67 ),
    inference(avatar_split_clause,[],[f666,f660,f673])).

fof(f660,plain,
    ( spl4_67
  <=> r1_xboole_0(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_67])])).

fof(f666,plain,
    ( r2_hidden(sK3(sK0,k1_relat_1(sK1)),sK0)
    | spl4_67 ),
    inference(resolution,[],[f661,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f661,plain,
    ( ~ r1_xboole_0(sK0,k1_relat_1(sK1))
    | spl4_67 ),
    inference(avatar_component_clause,[],[f660])).

fof(f671,plain,
    ( spl4_68
    | spl4_67 ),
    inference(avatar_split_clause,[],[f665,f660,f669])).

fof(f665,plain,
    ( r2_hidden(sK3(sK0,k1_relat_1(sK1)),k1_relat_1(sK1))
    | spl4_67 ),
    inference(resolution,[],[f661,f49])).

fof(f662,plain,
    ( ~ spl4_67
    | spl4_2 ),
    inference(avatar_split_clause,[],[f650,f66,f660])).

fof(f66,plain,
    ( spl4_2
  <=> r1_xboole_0(k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f650,plain,
    ( ~ r1_xboole_0(sK0,k1_relat_1(sK1))
    | spl4_2 ),
    inference(resolution,[],[f67,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f67,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f658,plain,
    ( spl4_66
    | spl4_2 ),
    inference(avatar_split_clause,[],[f649,f66,f656])).

fof(f649,plain,
    ( r2_hidden(sK3(k1_relat_1(sK1),sK0),k1_relat_1(sK1))
    | spl4_2 ),
    inference(resolution,[],[f67,f48])).

fof(f646,plain,
    ( spl4_58
    | ~ spl4_64 ),
    inference(avatar_split_clause,[],[f645,f641,f584])).

fof(f584,plain,
    ( spl4_58
  <=> k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_58])])).

fof(f641,plain,
    ( spl4_64
  <=> v1_xboole_0(k1_relat_1(k7_relat_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_64])])).

fof(f645,plain,
    ( k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl4_64 ),
    inference(resolution,[],[f642,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f642,plain,
    ( v1_xboole_0(k1_relat_1(k7_relat_1(sK1,sK0)))
    | ~ spl4_64 ),
    inference(avatar_component_clause,[],[f641])).

fof(f643,plain,
    ( spl4_64
    | ~ spl4_59 ),
    inference(avatar_split_clause,[],[f636,f587,f641])).

fof(f587,plain,
    ( spl4_59
  <=> ! [X1] : ~ r2_hidden(sK2(k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(k7_relat_1(sK1,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_59])])).

fof(f636,plain,
    ( v1_xboole_0(k1_relat_1(k7_relat_1(sK1,sK0)))
    | ~ spl4_59 ),
    inference(resolution,[],[f588,f46])).

fof(f46,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK2(X0),X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f30])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ? [X1] : r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
     => v1_xboole_0(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f588,plain,
    ( ! [X1] : ~ r2_hidden(sK2(k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(k7_relat_1(sK1,X1)))
    | ~ spl4_59 ),
    inference(avatar_component_clause,[],[f587])).

fof(f627,plain,
    ( ~ spl4_3
    | spl4_1
    | ~ spl4_4
    | ~ spl4_63 ),
    inference(avatar_split_clause,[],[f626,f610,f77,f63,f73])).

fof(f77,plain,
    ( spl4_4
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f626,plain,
    ( k1_xboole_0 = k9_relat_1(sK1,sK0)
    | ~ v1_relat_1(sK1)
    | ~ spl4_4
    | ~ spl4_63 ),
    inference(forward_demodulation,[],[f622,f78])).

fof(f78,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f77])).

fof(f622,plain,
    ( k2_relat_1(k1_xboole_0) = k9_relat_1(sK1,sK0)
    | ~ v1_relat_1(sK1)
    | ~ spl4_63 ),
    inference(superposition,[],[f52,f611])).

fof(f614,plain,
    ( ~ spl4_3
    | spl4_62 ),
    inference(avatar_split_clause,[],[f613,f607,f73])).

fof(f607,plain,
    ( spl4_62
  <=> v1_relat_1(k7_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_62])])).

fof(f613,plain,
    ( ~ v1_relat_1(sK1)
    | spl4_62 ),
    inference(resolution,[],[f608,f51])).

fof(f608,plain,
    ( ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | spl4_62 ),
    inference(avatar_component_clause,[],[f607])).

fof(f612,plain,
    ( ~ spl4_62
    | spl4_63
    | ~ spl4_58 ),
    inference(avatar_split_clause,[],[f605,f584,f610,f607])).

fof(f605,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl4_58 ),
    inference(trivial_inequality_removal,[],[f604])).

fof(f604,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl4_58 ),
    inference(superposition,[],[f44,f585])).

fof(f585,plain,
    ( k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl4_58 ),
    inference(avatar_component_clause,[],[f584])).

fof(f44,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f589,plain,
    ( spl4_58
    | spl4_59
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f574,f73,f66,f587,f584])).

fof(f574,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK2(k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(k7_relat_1(sK1,X1)))
        | k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0)) )
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(resolution,[],[f564,f112])).

fof(f112,plain,
    ( ! [X0] :
        ( r2_hidden(sK2(k1_relat_1(k7_relat_1(sK1,X0))),X0)
        | k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,X0)) )
    | ~ spl4_3 ),
    inference(resolution,[],[f110,f43])).

fof(f110,plain,
    ( ! [X0] :
        ( v1_xboole_0(k1_relat_1(k7_relat_1(sK1,X0)))
        | r2_hidden(sK2(k1_relat_1(k7_relat_1(sK1,X0))),X0) )
    | ~ spl4_3 ),
    inference(resolution,[],[f108,f46])).

fof(f108,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k1_relat_1(k7_relat_1(sK1,X1)))
        | r2_hidden(X0,X1) )
    | ~ spl4_3 ),
    inference(resolution,[],[f57,f74])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f564,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,sK0)
        | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(sK1,X1))) )
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(resolution,[],[f339,f70])).

fof(f70,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f339,plain,
    ( ! [X6,X8,X7] :
        ( ~ r1_xboole_0(k1_relat_1(sK1),X8)
        | ~ r2_hidden(X6,X8)
        | ~ r2_hidden(X6,k1_relat_1(k7_relat_1(sK1,X7))) )
    | ~ spl4_3 ),
    inference(resolution,[],[f162,f53])).

% (1858)Refutation not found, incomplete strategy% (1858)------------------------------
% (1858)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (1858)Termination reason: Refutation not found, incomplete strategy
fof(f162,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_xboole_0(X2,k1_relat_1(sK1))
        | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(sK1,X1)))
        | ~ r2_hidden(X0,X2) )
    | ~ spl4_3 ),
    inference(resolution,[],[f155,f50])).

% (1858)Memory used [KB]: 10618
fof(f155,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,k1_relat_1(sK1))
        | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(sK1,X1))) )
    | ~ spl4_3 ),
    inference(resolution,[],[f58,f74])).

% (1858)Time elapsed: 0.139 s
% (1858)------------------------------
% (1858)------------------------------
fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | r2_hidden(X0,k1_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f83,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f41,f81])).

fof(f41,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f79,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f42,f77])).

fof(f42,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f75,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f38,f73])).

fof(f38,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
      | k1_xboole_0 != k9_relat_1(sK1,sK0) )
    & ( r1_xboole_0(k1_relat_1(sK1),sK0)
      | k1_xboole_0 = k9_relat_1(sK1,sK0) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f28])).

fof(f28,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k9_relat_1(X1,X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 = k9_relat_1(X1,X0) )
        & v1_relat_1(X1) )
   => ( ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
        | k1_xboole_0 != k9_relat_1(sK1,sK0) )
      & ( r1_xboole_0(k1_relat_1(sK1),sK0)
        | k1_xboole_0 = k9_relat_1(sK1,sK0) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k9_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k9_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k9_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k9_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k9_relat_1(X1,X0)
      <~> r1_xboole_0(k1_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k9_relat_1(X1,X0)
        <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

fof(f71,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f39,f66,f63])).

fof(f39,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 = k9_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f68,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f40,f66,f63])).

fof(f40,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 != k9_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:47:33 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.47  % (1836)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.47  % (1844)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.49  % (1852)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.50  % (1842)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.51  % (1853)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.52  % (1840)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.52  % (1845)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.53  % (1842)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  % (1841)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.53  % (1838)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.53  % (1855)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.54  % (1854)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.54  % (1858)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.54  fof(f958,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(avatar_sat_refutation,[],[f68,f71,f75,f79,f83,f589,f612,f614,f627,f643,f646,f658,f662,f671,f675,f921,f938,f957])).
% 0.21/0.54  fof(f957,plain,(
% 0.21/0.54    spl4_63 | ~spl4_1 | ~spl4_3),
% 0.21/0.54    inference(avatar_split_clause,[],[f664,f73,f63,f610])).
% 0.21/0.54  fof(f610,plain,(
% 0.21/0.54    spl4_63 <=> k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_63])])).
% 0.21/0.54  fof(f63,plain,(
% 0.21/0.54    spl4_1 <=> k1_xboole_0 = k9_relat_1(sK1,sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.54  fof(f73,plain,(
% 0.21/0.54    spl4_3 <=> v1_relat_1(sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.54  fof(f664,plain,(
% 0.21/0.54    k1_xboole_0 = k7_relat_1(sK1,sK0) | (~spl4_1 | ~spl4_3)),
% 0.21/0.54    inference(trivial_inequality_removal,[],[f663])).
% 0.21/0.54  fof(f663,plain,(
% 0.21/0.54    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k7_relat_1(sK1,sK0) | (~spl4_1 | ~spl4_3)),
% 0.21/0.54    inference(superposition,[],[f459,f69])).
% 0.21/0.54  fof(f69,plain,(
% 0.21/0.54    k1_xboole_0 = k9_relat_1(sK1,sK0) | ~spl4_1),
% 0.21/0.54    inference(avatar_component_clause,[],[f63])).
% 0.21/0.54  fof(f459,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 != k9_relat_1(sK1,X0) | k1_xboole_0 = k7_relat_1(sK1,X0)) ) | ~spl4_3),
% 0.21/0.54    inference(resolution,[],[f97,f74])).
% 0.21/0.54  fof(f74,plain,(
% 0.21/0.54    v1_relat_1(sK1) | ~spl4_3),
% 0.21/0.54    inference(avatar_component_clause,[],[f73])).
% 0.21/0.54  fof(f97,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v1_relat_1(X0) | k1_xboole_0 = k7_relat_1(X0,X1) | k1_xboole_0 != k9_relat_1(X0,X1)) )),
% 0.21/0.54    inference(global_subsumption,[],[f51,f96])).
% 0.21/0.54  fof(f96,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_xboole_0 != k9_relat_1(X0,X1) | k1_xboole_0 = k7_relat_1(X0,X1) | ~v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(superposition,[],[f45,f52])).
% 0.21/0.54  fof(f52,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f23])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,axiom,(
% 0.21/0.54    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.21/0.54  fof(f45,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f19])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(flattening,[],[f18])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f10])).
% 0.21/0.54  fof(f10,axiom,(
% 0.21/0.54    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 0.21/0.54  fof(f51,plain,(
% 0.21/0.54    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f22])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.21/0.54  fof(f938,plain,(
% 0.21/0.54    ~spl4_73),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f936])).
% 0.21/0.54  fof(f936,plain,(
% 0.21/0.54    $false | ~spl4_73),
% 0.21/0.54    inference(resolution,[],[f916,f84])).
% 0.21/0.54  fof(f84,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.54    inference(superposition,[],[f47,f60])).
% 0.21/0.54  fof(f60,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.54    inference(equality_resolution,[],[f56])).
% 0.21/0.54  fof(f56,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f35])).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.54    inference(flattening,[],[f34])).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.54    inference(nnf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.54  fof(f47,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 0.21/0.54  fof(f916,plain,(
% 0.21/0.54    r2_hidden(sK3(k1_relat_1(sK1),sK0),k1_xboole_0) | ~spl4_73),
% 0.21/0.54    inference(avatar_component_clause,[],[f915])).
% 0.21/0.54  fof(f915,plain,(
% 0.21/0.54    spl4_73 <=> r2_hidden(sK3(k1_relat_1(sK1),sK0),k1_xboole_0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_73])])).
% 0.21/0.54  fof(f921,plain,(
% 0.21/0.54    ~spl4_68 | spl4_73 | ~spl4_3 | ~spl4_5 | ~spl4_63 | ~spl4_66 | ~spl4_69),
% 0.21/0.54    inference(avatar_split_clause,[],[f919,f673,f656,f610,f81,f73,f915,f669])).
% 0.21/0.54  fof(f669,plain,(
% 0.21/0.54    spl4_68 <=> r2_hidden(sK3(sK0,k1_relat_1(sK1)),k1_relat_1(sK1))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_68])])).
% 0.21/0.54  fof(f81,plain,(
% 0.21/0.54    spl4_5 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.54  fof(f656,plain,(
% 0.21/0.54    spl4_66 <=> r2_hidden(sK3(k1_relat_1(sK1),sK0),k1_relat_1(sK1))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_66])])).
% 0.21/0.54  fof(f673,plain,(
% 0.21/0.54    spl4_69 <=> r2_hidden(sK3(sK0,k1_relat_1(sK1)),sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_69])])).
% 0.21/0.54  fof(f919,plain,(
% 0.21/0.54    r2_hidden(sK3(k1_relat_1(sK1),sK0),k1_xboole_0) | ~r2_hidden(sK3(sK0,k1_relat_1(sK1)),k1_relat_1(sK1)) | (~spl4_3 | ~spl4_5 | ~spl4_63 | ~spl4_66 | ~spl4_69)),
% 0.21/0.54    inference(forward_demodulation,[],[f918,f82])).
% 0.21/0.54  fof(f82,plain,(
% 0.21/0.54    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl4_5),
% 0.21/0.54    inference(avatar_component_clause,[],[f81])).
% 0.21/0.54  fof(f918,plain,(
% 0.21/0.54    r2_hidden(sK3(k1_relat_1(sK1),sK0),k1_relat_1(k1_xboole_0)) | ~r2_hidden(sK3(sK0,k1_relat_1(sK1)),k1_relat_1(sK1)) | (~spl4_3 | ~spl4_63 | ~spl4_66 | ~spl4_69)),
% 0.21/0.54    inference(forward_demodulation,[],[f897,f611])).
% 0.21/0.54  fof(f611,plain,(
% 0.21/0.54    k1_xboole_0 = k7_relat_1(sK1,sK0) | ~spl4_63),
% 0.21/0.54    inference(avatar_component_clause,[],[f610])).
% 0.21/0.54  fof(f897,plain,(
% 0.21/0.54    r2_hidden(sK3(k1_relat_1(sK1),sK0),k1_relat_1(k7_relat_1(sK1,sK0))) | ~r2_hidden(sK3(sK0,k1_relat_1(sK1)),k1_relat_1(sK1)) | (~spl4_3 | ~spl4_66 | ~spl4_69)),
% 0.21/0.54    inference(resolution,[],[f699,f707])).
% 0.21/0.54  fof(f707,plain,(
% 0.21/0.54    ( ! [X0] : (r2_hidden(sK3(X0,sK0),sK0) | ~r2_hidden(sK3(sK0,k1_relat_1(sK1)),X0)) ) | ~spl4_69),
% 0.21/0.54    inference(resolution,[],[f698,f49])).
% 0.21/0.54  fof(f49,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK3(X0,X1),X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f33])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f32])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.54    inference(ennf_transformation,[],[f14])).
% 0.21/0.54  fof(f14,plain,(
% 0.21/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.54    inference(rectify,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.21/0.54  fof(f698,plain,(
% 0.21/0.54    ( ! [X0] : (~r1_xboole_0(X0,sK0) | ~r2_hidden(sK3(sK0,k1_relat_1(sK1)),X0)) ) | ~spl4_69),
% 0.21/0.54    inference(resolution,[],[f674,f50])).
% 0.21/0.54  fof(f50,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f33])).
% 0.21/0.54  fof(f674,plain,(
% 0.21/0.54    r2_hidden(sK3(sK0,k1_relat_1(sK1)),sK0) | ~spl4_69),
% 0.21/0.54    inference(avatar_component_clause,[],[f673])).
% 0.21/0.54  fof(f699,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(sK3(k1_relat_1(sK1),sK0),X0) | r2_hidden(sK3(k1_relat_1(sK1),sK0),k1_relat_1(k7_relat_1(sK1,X0)))) ) | (~spl4_3 | ~spl4_66)),
% 0.21/0.54    inference(resolution,[],[f657,f197])).
% 0.21/0.54  fof(f197,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r2_hidden(X0,k1_relat_1(sK1)) | ~r2_hidden(X0,X1) | r2_hidden(X0,k1_relat_1(k7_relat_1(sK1,X1)))) ) | ~spl4_3),
% 0.21/0.54    inference(resolution,[],[f59,f74])).
% 0.21/0.54  fof(f59,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1) | r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f37])).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1)) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 0.21/0.54    inference(flattening,[],[f36])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | (~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1))) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 0.21/0.54    inference(nnf_transformation,[],[f25])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))) | ~v1_relat_1(X2))),
% 0.21/0.54    inference(ennf_transformation,[],[f11])).
% 0.21/0.54  fof(f11,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).
% 0.21/0.54  fof(f657,plain,(
% 0.21/0.54    r2_hidden(sK3(k1_relat_1(sK1),sK0),k1_relat_1(sK1)) | ~spl4_66),
% 0.21/0.54    inference(avatar_component_clause,[],[f656])).
% 0.21/0.54  fof(f675,plain,(
% 0.21/0.54    spl4_69 | spl4_67),
% 0.21/0.54    inference(avatar_split_clause,[],[f666,f660,f673])).
% 0.21/0.54  fof(f660,plain,(
% 0.21/0.54    spl4_67 <=> r1_xboole_0(sK0,k1_relat_1(sK1))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_67])])).
% 0.21/0.54  fof(f666,plain,(
% 0.21/0.54    r2_hidden(sK3(sK0,k1_relat_1(sK1)),sK0) | spl4_67),
% 0.21/0.54    inference(resolution,[],[f661,f48])).
% 0.21/0.54  fof(f48,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK3(X0,X1),X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f33])).
% 0.21/0.54  fof(f661,plain,(
% 0.21/0.54    ~r1_xboole_0(sK0,k1_relat_1(sK1)) | spl4_67),
% 0.21/0.54    inference(avatar_component_clause,[],[f660])).
% 0.21/0.54  fof(f671,plain,(
% 0.21/0.54    spl4_68 | spl4_67),
% 0.21/0.54    inference(avatar_split_clause,[],[f665,f660,f669])).
% 0.21/0.54  fof(f665,plain,(
% 0.21/0.54    r2_hidden(sK3(sK0,k1_relat_1(sK1)),k1_relat_1(sK1)) | spl4_67),
% 0.21/0.54    inference(resolution,[],[f661,f49])).
% 0.21/0.54  fof(f662,plain,(
% 0.21/0.54    ~spl4_67 | spl4_2),
% 0.21/0.54    inference(avatar_split_clause,[],[f650,f66,f660])).
% 0.21/0.54  fof(f66,plain,(
% 0.21/0.54    spl4_2 <=> r1_xboole_0(k1_relat_1(sK1),sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.54  fof(f650,plain,(
% 0.21/0.54    ~r1_xboole_0(sK0,k1_relat_1(sK1)) | spl4_2),
% 0.21/0.54    inference(resolution,[],[f67,f53])).
% 0.21/0.54  fof(f53,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f24])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.21/0.54  fof(f67,plain,(
% 0.21/0.54    ~r1_xboole_0(k1_relat_1(sK1),sK0) | spl4_2),
% 0.21/0.54    inference(avatar_component_clause,[],[f66])).
% 0.21/0.54  fof(f658,plain,(
% 0.21/0.54    spl4_66 | spl4_2),
% 0.21/0.54    inference(avatar_split_clause,[],[f649,f66,f656])).
% 0.21/0.54  fof(f649,plain,(
% 0.21/0.54    r2_hidden(sK3(k1_relat_1(sK1),sK0),k1_relat_1(sK1)) | spl4_2),
% 0.21/0.54    inference(resolution,[],[f67,f48])).
% 0.21/0.54  fof(f646,plain,(
% 0.21/0.54    spl4_58 | ~spl4_64),
% 0.21/0.54    inference(avatar_split_clause,[],[f645,f641,f584])).
% 0.21/0.54  fof(f584,plain,(
% 0.21/0.54    spl4_58 <=> k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_58])])).
% 0.21/0.54  fof(f641,plain,(
% 0.21/0.54    spl4_64 <=> v1_xboole_0(k1_relat_1(k7_relat_1(sK1,sK0)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_64])])).
% 0.21/0.54  fof(f645,plain,(
% 0.21/0.54    k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0)) | ~spl4_64),
% 0.21/0.54    inference(resolution,[],[f642,f43])).
% 0.21/0.54  fof(f43,plain,(
% 0.21/0.54    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f17])).
% 0.21/0.54  fof(f17,plain,(
% 0.21/0.54    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.54  fof(f642,plain,(
% 0.21/0.54    v1_xboole_0(k1_relat_1(k7_relat_1(sK1,sK0))) | ~spl4_64),
% 0.21/0.54    inference(avatar_component_clause,[],[f641])).
% 0.21/0.54  fof(f643,plain,(
% 0.21/0.54    spl4_64 | ~spl4_59),
% 0.21/0.54    inference(avatar_split_clause,[],[f636,f587,f641])).
% 0.21/0.54  fof(f587,plain,(
% 0.21/0.54    spl4_59 <=> ! [X1] : ~r2_hidden(sK2(k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(k7_relat_1(sK1,X1)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_59])])).
% 0.21/0.54  fof(f636,plain,(
% 0.21/0.54    v1_xboole_0(k1_relat_1(k7_relat_1(sK1,sK0))) | ~spl4_59),
% 0.21/0.54    inference(resolution,[],[f588,f46])).
% 0.21/0.54  fof(f46,plain,(
% 0.21/0.54    ( ! [X0] : (r2_hidden(sK2(X0),X0) | v1_xboole_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f31])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK2(X0),X0))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f30])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ! [X0] : (v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f15])).
% 0.21/0.54  fof(f15,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) => v1_xboole_0(X0))),
% 0.21/0.54    inference(unused_predicate_definition_removal,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.54  fof(f588,plain,(
% 0.21/0.54    ( ! [X1] : (~r2_hidden(sK2(k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(k7_relat_1(sK1,X1)))) ) | ~spl4_59),
% 0.21/0.54    inference(avatar_component_clause,[],[f587])).
% 0.21/0.54  fof(f627,plain,(
% 0.21/0.54    ~spl4_3 | spl4_1 | ~spl4_4 | ~spl4_63),
% 0.21/0.54    inference(avatar_split_clause,[],[f626,f610,f77,f63,f73])).
% 0.21/0.54  fof(f77,plain,(
% 0.21/0.54    spl4_4 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.54  fof(f626,plain,(
% 0.21/0.54    k1_xboole_0 = k9_relat_1(sK1,sK0) | ~v1_relat_1(sK1) | (~spl4_4 | ~spl4_63)),
% 0.21/0.54    inference(forward_demodulation,[],[f622,f78])).
% 0.21/0.54  fof(f78,plain,(
% 0.21/0.54    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl4_4),
% 0.21/0.54    inference(avatar_component_clause,[],[f77])).
% 0.21/0.54  fof(f622,plain,(
% 0.21/0.54    k2_relat_1(k1_xboole_0) = k9_relat_1(sK1,sK0) | ~v1_relat_1(sK1) | ~spl4_63),
% 0.21/0.54    inference(superposition,[],[f52,f611])).
% 0.21/0.54  fof(f614,plain,(
% 0.21/0.54    ~spl4_3 | spl4_62),
% 0.21/0.54    inference(avatar_split_clause,[],[f613,f607,f73])).
% 0.21/0.54  fof(f607,plain,(
% 0.21/0.54    spl4_62 <=> v1_relat_1(k7_relat_1(sK1,sK0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_62])])).
% 0.21/0.54  fof(f613,plain,(
% 0.21/0.54    ~v1_relat_1(sK1) | spl4_62),
% 0.21/0.54    inference(resolution,[],[f608,f51])).
% 0.21/0.54  fof(f608,plain,(
% 0.21/0.54    ~v1_relat_1(k7_relat_1(sK1,sK0)) | spl4_62),
% 0.21/0.54    inference(avatar_component_clause,[],[f607])).
% 0.21/0.54  fof(f612,plain,(
% 0.21/0.54    ~spl4_62 | spl4_63 | ~spl4_58),
% 0.21/0.54    inference(avatar_split_clause,[],[f605,f584,f610,f607])).
% 0.21/0.54  fof(f605,plain,(
% 0.21/0.54    k1_xboole_0 = k7_relat_1(sK1,sK0) | ~v1_relat_1(k7_relat_1(sK1,sK0)) | ~spl4_58),
% 0.21/0.54    inference(trivial_inequality_removal,[],[f604])).
% 0.21/0.54  fof(f604,plain,(
% 0.21/0.54    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k7_relat_1(sK1,sK0) | ~v1_relat_1(k7_relat_1(sK1,sK0)) | ~spl4_58),
% 0.21/0.54    inference(superposition,[],[f44,f585])).
% 0.21/0.54  fof(f585,plain,(
% 0.21/0.54    k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0)) | ~spl4_58),
% 0.21/0.54    inference(avatar_component_clause,[],[f584])).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f19])).
% 0.21/0.54  fof(f589,plain,(
% 0.21/0.54    spl4_58 | spl4_59 | ~spl4_2 | ~spl4_3),
% 0.21/0.54    inference(avatar_split_clause,[],[f574,f73,f66,f587,f584])).
% 0.21/0.54  fof(f574,plain,(
% 0.21/0.54    ( ! [X1] : (~r2_hidden(sK2(k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(k7_relat_1(sK1,X1))) | k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0))) ) | (~spl4_2 | ~spl4_3)),
% 0.21/0.54    inference(resolution,[],[f564,f112])).
% 0.21/0.54  fof(f112,plain,(
% 0.21/0.54    ( ! [X0] : (r2_hidden(sK2(k1_relat_1(k7_relat_1(sK1,X0))),X0) | k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,X0))) ) | ~spl4_3),
% 0.21/0.54    inference(resolution,[],[f110,f43])).
% 0.21/0.54  fof(f110,plain,(
% 0.21/0.54    ( ! [X0] : (v1_xboole_0(k1_relat_1(k7_relat_1(sK1,X0))) | r2_hidden(sK2(k1_relat_1(k7_relat_1(sK1,X0))),X0)) ) | ~spl4_3),
% 0.21/0.54    inference(resolution,[],[f108,f46])).
% 0.21/0.54  fof(f108,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r2_hidden(X0,k1_relat_1(k7_relat_1(sK1,X1))) | r2_hidden(X0,X1)) ) | ~spl4_3),
% 0.21/0.54    inference(resolution,[],[f57,f74])).
% 0.21/0.54  fof(f57,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | r2_hidden(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f37])).
% 0.21/0.54  fof(f564,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r2_hidden(X0,sK0) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(sK1,X1)))) ) | (~spl4_2 | ~spl4_3)),
% 0.21/0.54    inference(resolution,[],[f339,f70])).
% 0.21/0.54  fof(f70,plain,(
% 0.21/0.54    r1_xboole_0(k1_relat_1(sK1),sK0) | ~spl4_2),
% 0.21/0.54    inference(avatar_component_clause,[],[f66])).
% 0.21/0.54  fof(f339,plain,(
% 0.21/0.54    ( ! [X6,X8,X7] : (~r1_xboole_0(k1_relat_1(sK1),X8) | ~r2_hidden(X6,X8) | ~r2_hidden(X6,k1_relat_1(k7_relat_1(sK1,X7)))) ) | ~spl4_3),
% 0.21/0.54    inference(resolution,[],[f162,f53])).
% 0.21/0.54  % (1858)Refutation not found, incomplete strategy% (1858)------------------------------
% 0.21/0.54  % (1858)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (1858)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  fof(f162,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r1_xboole_0(X2,k1_relat_1(sK1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(sK1,X1))) | ~r2_hidden(X0,X2)) ) | ~spl4_3),
% 0.21/0.54    inference(resolution,[],[f155,f50])).
% 0.21/0.54  
% 0.21/0.54  % (1858)Memory used [KB]: 10618
% 0.21/0.54  fof(f155,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r2_hidden(X0,k1_relat_1(sK1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(sK1,X1)))) ) | ~spl4_3),
% 0.21/0.54    inference(resolution,[],[f58,f74])).
% 0.21/0.54  % (1858)Time elapsed: 0.139 s
% 0.21/0.54  % (1858)------------------------------
% 0.21/0.54  % (1858)------------------------------
% 0.21/0.54  fof(f58,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | r2_hidden(X0,k1_relat_1(X2))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f37])).
% 0.21/0.54  fof(f83,plain,(
% 0.21/0.54    spl4_5),
% 0.21/0.54    inference(avatar_split_clause,[],[f41,f81])).
% 0.21/0.54  fof(f41,plain,(
% 0.21/0.54    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.54    inference(cnf_transformation,[],[f9])).
% 0.21/0.54  fof(f9,axiom,(
% 0.21/0.54    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.54  fof(f79,plain,(
% 0.21/0.54    spl4_4),
% 0.21/0.54    inference(avatar_split_clause,[],[f42,f77])).
% 0.21/0.54  fof(f42,plain,(
% 0.21/0.54    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.54    inference(cnf_transformation,[],[f9])).
% 0.21/0.54  fof(f75,plain,(
% 0.21/0.54    spl4_3),
% 0.21/0.54    inference(avatar_split_clause,[],[f38,f73])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    v1_relat_1(sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f29])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    (~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k9_relat_1(sK1,sK0)) & (r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k9_relat_1(sK1,sK0)) & v1_relat_1(sK1)),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f28])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ? [X0,X1] : ((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k9_relat_1(X1,X0)) & v1_relat_1(X1)) => ((~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k9_relat_1(sK1,sK0)) & (r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k9_relat_1(sK1,sK0)) & v1_relat_1(sK1))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    ? [X0,X1] : ((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k9_relat_1(X1,X0)) & v1_relat_1(X1))),
% 0.21/0.54    inference(flattening,[],[f26])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ? [X0,X1] : (((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k9_relat_1(X1,X0))) & v1_relat_1(X1))),
% 0.21/0.54    inference(nnf_transformation,[],[f16])).
% 0.21/0.54  fof(f16,plain,(
% 0.21/0.54    ? [X0,X1] : ((k1_xboole_0 = k9_relat_1(X1,X0) <~> r1_xboole_0(k1_relat_1(X1),X0)) & v1_relat_1(X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f13])).
% 0.21/0.54  fof(f13,negated_conjecture,(
% 0.21/0.54    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.21/0.54    inference(negated_conjecture,[],[f12])).
% 0.21/0.54  fof(f12,conjecture,(
% 0.21/0.54    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).
% 0.21/0.54  fof(f71,plain,(
% 0.21/0.54    spl4_1 | spl4_2),
% 0.21/0.54    inference(avatar_split_clause,[],[f39,f66,f63])).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k9_relat_1(sK1,sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f29])).
% 0.21/0.54  fof(f68,plain,(
% 0.21/0.54    ~spl4_1 | ~spl4_2),
% 0.21/0.54    inference(avatar_split_clause,[],[f40,f66,f63])).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    ~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k9_relat_1(sK1,sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f29])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (1842)------------------------------
% 0.21/0.54  % (1842)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (1842)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (1842)Memory used [KB]: 11129
% 0.21/0.54  % (1842)Time elapsed: 0.092 s
% 0.21/0.54  % (1842)------------------------------
% 0.21/0.54  % (1842)------------------------------
% 0.21/0.54  % (1856)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.54  % (1828)Success in time 0.185 s
%------------------------------------------------------------------------------
