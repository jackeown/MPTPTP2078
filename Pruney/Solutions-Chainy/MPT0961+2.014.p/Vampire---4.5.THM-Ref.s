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
% DateTime   : Thu Dec  3 13:00:12 EST 2020

% Result     : Theorem 1.37s
% Output     : Refutation 1.37s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 176 expanded)
%              Number of leaves         :   12 (  51 expanded)
%              Depth                    :   10
%              Number of atoms          :  189 ( 585 expanded)
%              Number of equality atoms :   46 ( 158 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f248,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f109,f136,f140,f222,f247])).

fof(f247,plain,(
    spl4_4 ),
    inference(avatar_contradiction_clause,[],[f242])).

fof(f242,plain,
    ( $false
    | spl4_4 ),
    inference(unit_resulting_resolution,[],[f113,f230,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f230,plain,
    ( r2_hidden(sK2(k1_relat_1(sK0),k1_relat_1(sK0)),k1_relat_1(sK0))
    | spl4_4 ),
    inference(unit_resulting_resolution,[],[f113,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f113,plain,
    ( ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0))
    | spl4_4 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl4_4
  <=> r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f222,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_contradiction_clause,[],[f216])).

fof(f216,plain,
    ( $false
    | ~ spl4_1
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f198,f42,f202,f78])).

fof(f78,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f202,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl4_1
    | spl4_2 ),
    inference(forward_demodulation,[],[f177,f55])).

fof(f55,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f177,plain,
    ( k1_relat_1(k1_xboole_0) = k1_relset_1(k1_relat_1(k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | ~ spl4_1
    | spl4_2 ),
    inference(backward_demodulation,[],[f154,f156])).

fof(f156,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_1
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f40,f145,f54])).

fof(f54,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f145,plain,
    ( k1_xboole_0 = k2_relat_1(sK0)
    | ~ spl4_1
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f104,f99,f142,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f142,plain,
    ( k1_relat_1(sK0) = k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0)
    | ~ spl4_1 ),
    inference(unit_resulting_resolution,[],[f99,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f99,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl4_1
  <=> m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f104,plain,
    ( ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl4_2
  <=> v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f40,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        | ~ v1_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        | ~ v1_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
          & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
          & v1_funct_1(X0) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(f154,plain,
    ( k1_relat_1(sK0) = k1_relset_1(k1_relat_1(sK0),k1_xboole_0,sK0)
    | ~ spl4_1
    | spl4_2 ),
    inference(backward_demodulation,[],[f142,f145])).

fof(f42,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f198,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl4_1
    | spl4_2 ),
    inference(forward_demodulation,[],[f174,f55])).

fof(f174,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl4_1
    | spl4_2 ),
    inference(backward_demodulation,[],[f151,f156])).

fof(f151,plain,
    ( ~ v1_funct_2(sK0,k1_relat_1(sK0),k1_xboole_0)
    | ~ spl4_1
    | spl4_2 ),
    inference(backward_demodulation,[],[f104,f145])).

fof(f140,plain,(
    spl4_3 ),
    inference(avatar_contradiction_clause,[],[f137])).

fof(f137,plain,
    ( $false
    | spl4_3 ),
    inference(unit_resulting_resolution,[],[f41,f108])).

fof(f108,plain,
    ( ~ v1_funct_1(sK0)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl4_3
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f41,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f136,plain,
    ( spl4_1
    | ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f131])).

fof(f131,plain,
    ( $false
    | spl4_1
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f121,f124,f68])).

fof(f124,plain,
    ( r2_hidden(sK2(k2_relat_1(sK0),k2_relat_1(sK0)),k2_relat_1(sK0))
    | spl4_1
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f121,f67])).

fof(f121,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))
    | spl4_1
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f40,f100,f114,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(f114,plain,
    ( r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f112])).

fof(f100,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f98])).

fof(f109,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f39,f106,f102,f98])).

fof(f39,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
    | ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n009.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:59:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.50  % (5036)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.20/0.52  % (5052)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.20/0.52  % (5046)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.20/0.52  % (5044)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.20/0.52  % (5054)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.20/0.54  % (5038)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.37/0.54  % (5043)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.37/0.54  % (5057)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.37/0.54  % (5031)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.37/0.54  % (5031)Refutation not found, incomplete strategy% (5031)------------------------------
% 1.37/0.54  % (5031)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.54  % (5031)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.54  
% 1.37/0.54  % (5031)Memory used [KB]: 1663
% 1.37/0.54  % (5031)Time elapsed: 0.123 s
% 1.37/0.54  % (5031)------------------------------
% 1.37/0.54  % (5031)------------------------------
% 1.37/0.54  % (5033)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.37/0.54  % (5034)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.37/0.54  % (5033)Refutation not found, incomplete strategy% (5033)------------------------------
% 1.37/0.54  % (5033)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.54  % (5033)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.54  
% 1.37/0.54  % (5033)Memory used [KB]: 10746
% 1.37/0.54  % (5033)Time elapsed: 0.123 s
% 1.37/0.54  % (5033)------------------------------
% 1.37/0.54  % (5033)------------------------------
% 1.37/0.55  % (5039)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.37/0.55  % (5042)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.37/0.55  % (5042)Refutation not found, incomplete strategy% (5042)------------------------------
% 1.37/0.55  % (5042)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.55  % (5042)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.55  
% 1.37/0.55  % (5042)Memory used [KB]: 10746
% 1.37/0.55  % (5042)Time elapsed: 0.132 s
% 1.37/0.55  % (5042)------------------------------
% 1.37/0.55  % (5042)------------------------------
% 1.37/0.55  % (5032)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.37/0.55  % (5059)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.37/0.55  % (5050)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.37/0.55  % (5039)Refutation not found, incomplete strategy% (5039)------------------------------
% 1.37/0.55  % (5039)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.55  % (5039)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.55  
% 1.37/0.55  % (5039)Memory used [KB]: 10746
% 1.37/0.55  % (5039)Time elapsed: 0.136 s
% 1.37/0.55  % (5039)------------------------------
% 1.37/0.55  % (5039)------------------------------
% 1.37/0.56  % (5049)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.37/0.56  % (5035)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.37/0.56  % (5058)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.37/0.56  % (5035)Refutation found. Thanks to Tanya!
% 1.37/0.56  % SZS status Theorem for theBenchmark
% 1.37/0.56  % (5041)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.37/0.56  % (5047)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.37/0.56  % (5055)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.37/0.56  % (5051)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.37/0.57  % (5053)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.37/0.57  % (5037)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.37/0.57  % (5048)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.37/0.57  % SZS output start Proof for theBenchmark
% 1.37/0.57  fof(f248,plain,(
% 1.37/0.57    $false),
% 1.37/0.57    inference(avatar_sat_refutation,[],[f109,f136,f140,f222,f247])).
% 1.37/0.57  fof(f247,plain,(
% 1.37/0.57    spl4_4),
% 1.37/0.57    inference(avatar_contradiction_clause,[],[f242])).
% 1.37/0.57  fof(f242,plain,(
% 1.37/0.57    $false | spl4_4),
% 1.37/0.57    inference(unit_resulting_resolution,[],[f113,f230,f68])).
% 1.37/0.57  fof(f68,plain,(
% 1.37/0.57    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.37/0.57    inference(cnf_transformation,[],[f33])).
% 1.37/0.57  fof(f33,plain,(
% 1.37/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.37/0.57    inference(ennf_transformation,[],[f2])).
% 1.37/0.57  fof(f2,axiom,(
% 1.37/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.37/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.37/0.57  fof(f230,plain,(
% 1.37/0.57    r2_hidden(sK2(k1_relat_1(sK0),k1_relat_1(sK0)),k1_relat_1(sK0)) | spl4_4),
% 1.37/0.57    inference(unit_resulting_resolution,[],[f113,f67])).
% 1.37/0.57  fof(f67,plain,(
% 1.37/0.57    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK2(X0,X1),X0)) )),
% 1.37/0.57    inference(cnf_transformation,[],[f33])).
% 1.37/0.57  fof(f113,plain,(
% 1.37/0.57    ~r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) | spl4_4),
% 1.37/0.57    inference(avatar_component_clause,[],[f112])).
% 1.37/0.57  fof(f112,plain,(
% 1.37/0.57    spl4_4 <=> r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0))),
% 1.37/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.37/0.57  fof(f222,plain,(
% 1.37/0.57    ~spl4_1 | spl4_2),
% 1.37/0.57    inference(avatar_contradiction_clause,[],[f216])).
% 1.37/0.57  fof(f216,plain,(
% 1.37/0.57    $false | (~spl4_1 | spl4_2)),
% 1.37/0.57    inference(unit_resulting_resolution,[],[f198,f42,f202,f78])).
% 1.37/0.57  fof(f78,plain,(
% 1.37/0.57    ( ! [X2,X1] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | v1_funct_2(X2,k1_xboole_0,X1)) )),
% 1.37/0.57    inference(equality_resolution,[],[f48])).
% 1.37/0.57  fof(f48,plain,(
% 1.37/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 1.37/0.57    inference(cnf_transformation,[],[f24])).
% 1.37/0.57  fof(f24,plain,(
% 1.37/0.57    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.37/0.57    inference(flattening,[],[f23])).
% 1.37/0.57  fof(f23,plain,(
% 1.37/0.57    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.37/0.57    inference(ennf_transformation,[],[f17])).
% 1.37/0.57  fof(f17,axiom,(
% 1.37/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.37/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.37/0.57  fof(f202,plain,(
% 1.37/0.57    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl4_1 | spl4_2)),
% 1.37/0.57    inference(forward_demodulation,[],[f177,f55])).
% 1.37/0.57  fof(f55,plain,(
% 1.37/0.57    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.37/0.57    inference(cnf_transformation,[],[f11])).
% 1.37/0.57  fof(f11,axiom,(
% 1.37/0.57    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.37/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 1.37/0.57  fof(f177,plain,(
% 1.37/0.57    k1_relat_1(k1_xboole_0) = k1_relset_1(k1_relat_1(k1_xboole_0),k1_xboole_0,k1_xboole_0) | (~spl4_1 | spl4_2)),
% 1.37/0.57    inference(backward_demodulation,[],[f154,f156])).
% 1.37/0.57  fof(f156,plain,(
% 1.37/0.57    k1_xboole_0 = sK0 | (~spl4_1 | spl4_2)),
% 1.37/0.57    inference(unit_resulting_resolution,[],[f40,f145,f54])).
% 1.37/0.57  fof(f54,plain,(
% 1.37/0.57    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 = X0) )),
% 1.37/0.57    inference(cnf_transformation,[],[f28])).
% 1.37/0.57  fof(f28,plain,(
% 1.37/0.57    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.37/0.57    inference(flattening,[],[f27])).
% 1.37/0.57  fof(f27,plain,(
% 1.37/0.57    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.37/0.57    inference(ennf_transformation,[],[f12])).
% 1.37/0.57  fof(f12,axiom,(
% 1.37/0.57    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 1.37/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 1.37/0.57  fof(f145,plain,(
% 1.37/0.57    k1_xboole_0 = k2_relat_1(sK0) | (~spl4_1 | spl4_2)),
% 1.37/0.57    inference(unit_resulting_resolution,[],[f104,f99,f142,f50])).
% 1.37/0.57  fof(f50,plain,(
% 1.37/0.57    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_2(X2,X0,X1)) )),
% 1.37/0.57    inference(cnf_transformation,[],[f24])).
% 1.37/0.57  fof(f142,plain,(
% 1.37/0.57    k1_relat_1(sK0) = k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0) | ~spl4_1),
% 1.37/0.57    inference(unit_resulting_resolution,[],[f99,f57])).
% 1.37/0.57  fof(f57,plain,(
% 1.37/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.37/0.57    inference(cnf_transformation,[],[f29])).
% 1.37/0.57  fof(f29,plain,(
% 1.37/0.57    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.37/0.57    inference(ennf_transformation,[],[f15])).
% 1.37/0.57  fof(f15,axiom,(
% 1.37/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.37/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.37/0.57  fof(f99,plain,(
% 1.37/0.57    m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | ~spl4_1),
% 1.37/0.57    inference(avatar_component_clause,[],[f98])).
% 1.37/0.57  fof(f98,plain,(
% 1.37/0.57    spl4_1 <=> m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))),
% 1.37/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.37/0.57  fof(f104,plain,(
% 1.37/0.57    ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | spl4_2),
% 1.37/0.57    inference(avatar_component_clause,[],[f102])).
% 1.37/0.57  fof(f102,plain,(
% 1.37/0.57    spl4_2 <=> v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))),
% 1.37/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.37/0.57  fof(f40,plain,(
% 1.37/0.57    v1_relat_1(sK0)),
% 1.37/0.57    inference(cnf_transformation,[],[f22])).
% 1.37/0.57  fof(f22,plain,(
% 1.37/0.57    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 1.37/0.57    inference(flattening,[],[f21])).
% 1.37/0.57  fof(f21,plain,(
% 1.37/0.57    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 1.37/0.57    inference(ennf_transformation,[],[f20])).
% 1.37/0.57  fof(f20,negated_conjecture,(
% 1.37/0.57    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 1.37/0.57    inference(negated_conjecture,[],[f19])).
% 1.37/0.57  fof(f19,conjecture,(
% 1.37/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 1.37/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).
% 1.37/0.57  fof(f154,plain,(
% 1.37/0.57    k1_relat_1(sK0) = k1_relset_1(k1_relat_1(sK0),k1_xboole_0,sK0) | (~spl4_1 | spl4_2)),
% 1.37/0.57    inference(backward_demodulation,[],[f142,f145])).
% 1.37/0.57  fof(f42,plain,(
% 1.37/0.57    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.37/0.57    inference(cnf_transformation,[],[f5])).
% 1.37/0.57  fof(f5,axiom,(
% 1.37/0.57    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.37/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 1.37/0.57  fof(f198,plain,(
% 1.37/0.57    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl4_1 | spl4_2)),
% 1.37/0.57    inference(forward_demodulation,[],[f174,f55])).
% 1.37/0.57  fof(f174,plain,(
% 1.37/0.57    ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | (~spl4_1 | spl4_2)),
% 1.37/0.57    inference(backward_demodulation,[],[f151,f156])).
% 1.37/0.57  fof(f151,plain,(
% 1.37/0.57    ~v1_funct_2(sK0,k1_relat_1(sK0),k1_xboole_0) | (~spl4_1 | spl4_2)),
% 1.37/0.57    inference(backward_demodulation,[],[f104,f145])).
% 1.37/0.57  fof(f140,plain,(
% 1.37/0.57    spl4_3),
% 1.37/0.57    inference(avatar_contradiction_clause,[],[f137])).
% 1.37/0.57  fof(f137,plain,(
% 1.37/0.57    $false | spl4_3),
% 1.37/0.57    inference(unit_resulting_resolution,[],[f41,f108])).
% 1.37/0.57  fof(f108,plain,(
% 1.37/0.57    ~v1_funct_1(sK0) | spl4_3),
% 1.37/0.57    inference(avatar_component_clause,[],[f106])).
% 1.37/0.57  fof(f106,plain,(
% 1.37/0.57    spl4_3 <=> v1_funct_1(sK0)),
% 1.37/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.37/0.57  fof(f41,plain,(
% 1.37/0.57    v1_funct_1(sK0)),
% 1.37/0.57    inference(cnf_transformation,[],[f22])).
% 1.37/0.57  fof(f136,plain,(
% 1.37/0.57    spl4_1 | ~spl4_4),
% 1.37/0.57    inference(avatar_contradiction_clause,[],[f131])).
% 1.37/0.57  fof(f131,plain,(
% 1.37/0.57    $false | (spl4_1 | ~spl4_4)),
% 1.37/0.57    inference(unit_resulting_resolution,[],[f121,f124,f68])).
% 1.37/0.57  fof(f124,plain,(
% 1.37/0.57    r2_hidden(sK2(k2_relat_1(sK0),k2_relat_1(sK0)),k2_relat_1(sK0)) | (spl4_1 | ~spl4_4)),
% 1.37/0.57    inference(unit_resulting_resolution,[],[f121,f67])).
% 1.37/0.57  fof(f121,plain,(
% 1.37/0.57    ~r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) | (spl4_1 | ~spl4_4)),
% 1.37/0.57    inference(unit_resulting_resolution,[],[f40,f100,f114,f52])).
% 1.37/0.57  fof(f52,plain,(
% 1.37/0.57    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(k1_relat_1(X2),X0) | ~r1_tarski(k2_relat_1(X2),X1) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.37/0.57    inference(cnf_transformation,[],[f26])).
% 1.37/0.57  fof(f26,plain,(
% 1.37/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 1.37/0.57    inference(flattening,[],[f25])).
% 1.37/0.57  fof(f25,plain,(
% 1.37/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 1.37/0.57    inference(ennf_transformation,[],[f16])).
% 1.37/0.57  fof(f16,axiom,(
% 1.37/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.37/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).
% 1.37/0.57  fof(f114,plain,(
% 1.37/0.57    r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) | ~spl4_4),
% 1.37/0.57    inference(avatar_component_clause,[],[f112])).
% 1.37/0.57  fof(f100,plain,(
% 1.37/0.57    ~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | spl4_1),
% 1.37/0.57    inference(avatar_component_clause,[],[f98])).
% 1.37/0.57  fof(f109,plain,(
% 1.37/0.57    ~spl4_1 | ~spl4_2 | ~spl4_3),
% 1.37/0.57    inference(avatar_split_clause,[],[f39,f106,f102,f98])).
% 1.37/0.57  fof(f39,plain,(
% 1.37/0.57    ~v1_funct_1(sK0) | ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | ~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))),
% 1.37/0.57    inference(cnf_transformation,[],[f22])).
% 1.37/0.57  % SZS output end Proof for theBenchmark
% 1.37/0.57  % (5035)------------------------------
% 1.37/0.57  % (5035)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.57  % (5035)Termination reason: Refutation
% 1.37/0.57  
% 1.37/0.57  % (5035)Memory used [KB]: 6268
% 1.37/0.57  % (5035)Time elapsed: 0.140 s
% 1.37/0.57  % (5035)------------------------------
% 1.37/0.57  % (5035)------------------------------
% 1.37/0.57  % (5030)Success in time 0.204 s
%------------------------------------------------------------------------------
