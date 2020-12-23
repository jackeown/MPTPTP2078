%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:03 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.22s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 130 expanded)
%              Number of leaves         :   18 (  48 expanded)
%              Depth                    :    9
%              Number of atoms          :  217 ( 398 expanded)
%              Number of equality atoms :   31 (  62 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f225,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f48,f53,f57,f72,f100,f105,f140,f151,f176,f217,f224])).

fof(f224,plain,
    ( ~ spl8_17
    | ~ spl8_20 ),
    inference(avatar_contradiction_clause,[],[f223])).

fof(f223,plain,
    ( $false
    | ~ spl8_17
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f220,f154])).

fof(f154,plain,
    ( sK0 = k1_funct_1(sK3,sK6(sK3,sK1,sK0))
    | ~ spl8_17 ),
    inference(resolution,[],[f150,f27])).

fof(f27,plain,(
    ! [X0,X3,X1] :
      ( ~ sP5(X3,X1,X0)
      | k1_funct_1(X0,sK6(X0,X1,X3)) = X3 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_funct_1)).

fof(f150,plain,
    ( sP5(sK0,sK1,sK3)
    | ~ spl8_17 ),
    inference(avatar_component_clause,[],[f149])).

fof(f149,plain,
    ( spl8_17
  <=> sP5(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f220,plain,
    ( sK0 != k1_funct_1(sK3,sK6(sK3,sK1,sK0))
    | ~ spl8_20 ),
    inference(resolution,[],[f216,f19])).

fof(f19,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,sK1)
      | sK0 != k1_funct_1(sK3,X4) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X0
          | ~ m1_subset_1(X4,X1) )
      & r2_hidden(X0,k2_relset_1(X1,X2,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X0
          | ~ m1_subset_1(X4,X1) )
      & r2_hidden(X0,k2_relset_1(X1,X2,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_1(X3) )
       => ~ ( ! [X4] :
                ( m1_subset_1(X4,X1)
               => k1_funct_1(X3,X4) != X0 )
            & r2_hidden(X0,k2_relset_1(X1,X2,X3)) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
       => ~ ( ! [X4] :
                ( m1_subset_1(X4,X1)
               => k1_funct_1(X3,X4) != X0 )
            & r2_hidden(X0,k2_relset_1(X1,X2,X3)) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(X3,X1,X2)
        & v1_funct_1(X3) )
     => ~ ( ! [X4] :
              ( m1_subset_1(X4,X1)
             => k1_funct_1(X3,X4) != X0 )
          & r2_hidden(X0,k2_relset_1(X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t190_funct_2)).

fof(f216,plain,
    ( m1_subset_1(sK6(sK3,sK1,sK0),sK1)
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f215])).

fof(f215,plain,
    ( spl8_20
  <=> m1_subset_1(sK6(sK3,sK1,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f217,plain,
    ( spl8_20
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f188,f174,f215])).

fof(f174,plain,
    ( spl8_18
  <=> r2_hidden(sK6(sK3,sK1,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f188,plain,
    ( m1_subset_1(sK6(sK3,sK1,sK0),sK1)
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f187,f186])).

fof(f186,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl8_18 ),
    inference(resolution,[],[f175,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f175,plain,
    ( r2_hidden(sK6(sK3,sK1,sK0),sK1)
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f174])).

fof(f187,plain,
    ( v1_xboole_0(sK1)
    | m1_subset_1(sK6(sK3,sK1,sK0),sK1)
    | ~ spl8_18 ),
    inference(resolution,[],[f175,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0)
      | m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f176,plain,
    ( spl8_18
    | ~ spl8_17 ),
    inference(avatar_split_clause,[],[f153,f149,f174])).

fof(f153,plain,
    ( r2_hidden(sK6(sK3,sK1,sK0),sK1)
    | ~ spl8_17 ),
    inference(resolution,[],[f150,f26])).

% (28141)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
fof(f26,plain,(
    ! [X0,X3,X1] :
      ( ~ sP5(X3,X1,X0)
      | r2_hidden(sK6(X0,X1,X3),X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f151,plain,
    ( spl8_17
    | ~ spl8_1
    | ~ spl8_4
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f147,f138,f70,f46,f149])).

fof(f46,plain,
    ( spl8_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f70,plain,
    ( spl8_4
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f138,plain,
    ( spl8_16
  <=> r2_hidden(sK0,k9_relat_1(sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f147,plain,
    ( sP5(sK0,sK1,sK3)
    | ~ spl8_1
    | ~ spl8_4
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f146,f71])).

fof(f71,plain,
    ( v1_relat_1(sK3)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f70])).

fof(f146,plain,
    ( sP5(sK0,sK1,sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl8_1
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f143,f47])).

fof(f47,plain,
    ( v1_funct_1(sK3)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f46])).

fof(f143,plain,
    ( ~ v1_funct_1(sK3)
    | sP5(sK0,sK1,sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl8_16 ),
    inference(resolution,[],[f139,f42])).

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | sP5(X3,X1,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | sP5(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f139,plain,
    ( r2_hidden(sK0,k9_relat_1(sK3,sK1))
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f138])).

fof(f140,plain,
    ( spl8_16
    | ~ spl8_3
    | ~ spl8_11 ),
    inference(avatar_split_clause,[],[f111,f103,f55,f138])).

fof(f55,plain,
    ( spl8_3
  <=> r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f103,plain,
    ( spl8_11
  <=> k2_relset_1(sK1,sK2,sK3) = k9_relat_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f111,plain,
    ( r2_hidden(sK0,k9_relat_1(sK3,sK1))
    | ~ spl8_3
    | ~ spl8_11 ),
    inference(superposition,[],[f56,f104])).

fof(f104,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k9_relat_1(sK3,sK1)
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f103])).

fof(f56,plain,
    ( r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3))
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f55])).

fof(f105,plain,
    ( spl8_11
    | ~ spl8_2
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f101,f98,f51,f103])).

fof(f51,plain,
    ( spl8_2
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f98,plain,
    ( spl8_10
  <=> k2_relset_1(sK1,sK2,sK3) = k7_relset_1(sK1,sK2,sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f101,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k9_relat_1(sK3,sK1)
    | ~ spl8_2
    | ~ spl8_10 ),
    inference(forward_demodulation,[],[f99,f60])).

fof(f60,plain,
    ( ! [X0] : k9_relat_1(sK3,X0) = k7_relset_1(sK1,sK2,sK3,X0)
    | ~ spl8_2 ),
    inference(resolution,[],[f52,f23])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f52,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f51])).

fof(f99,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k7_relset_1(sK1,sK2,sK3,sK1)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f98])).

fof(f100,plain,
    ( spl8_10
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f58,f51,f98])).

fof(f58,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k7_relset_1(sK1,sK2,sK3,sK1)
    | ~ spl8_2 ),
    inference(resolution,[],[f52,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

fof(f72,plain,
    ( spl8_4
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f64,f51,f70])).

fof(f64,plain,
    ( v1_relat_1(sK3)
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f61,f41])).

fof(f41,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f61,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK2))
    | v1_relat_1(sK3)
    | ~ spl8_2 ),
    inference(resolution,[],[f52,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f57,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f22,f55])).

fof(f22,plain,(
    r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f12])).

fof(f53,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f21,f51])).

fof(f21,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f12])).

fof(f48,plain,(
    spl8_1 ),
    inference(avatar_split_clause,[],[f20,f46])).

fof(f20,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:47:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.47  % (28138)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.47  % (28131)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.49  % (28124)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.49  % (28127)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.49  % (28132)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.49  % (28135)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.50  % (28124)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % (28130)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.50  % (28134)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.50  % (28129)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.50  % (28125)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (28134)Refutation not found, incomplete strategy% (28134)------------------------------
% 0.20/0.51  % (28134)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (28134)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (28134)Memory used [KB]: 6012
% 0.20/0.51  % (28134)Time elapsed: 0.066 s
% 0.20/0.51  % (28134)------------------------------
% 0.20/0.51  % (28134)------------------------------
% 0.20/0.51  % (28142)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.51  % (28137)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.51  % (28128)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.51  % (28126)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.51  % (28133)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.51  % (28143)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.51  % (28140)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 1.22/0.51  % SZS output start Proof for theBenchmark
% 1.22/0.51  fof(f225,plain,(
% 1.22/0.51    $false),
% 1.22/0.51    inference(avatar_sat_refutation,[],[f48,f53,f57,f72,f100,f105,f140,f151,f176,f217,f224])).
% 1.22/0.51  fof(f224,plain,(
% 1.22/0.51    ~spl8_17 | ~spl8_20),
% 1.22/0.51    inference(avatar_contradiction_clause,[],[f223])).
% 1.22/0.51  fof(f223,plain,(
% 1.22/0.51    $false | (~spl8_17 | ~spl8_20)),
% 1.22/0.51    inference(subsumption_resolution,[],[f220,f154])).
% 1.22/0.51  fof(f154,plain,(
% 1.22/0.51    sK0 = k1_funct_1(sK3,sK6(sK3,sK1,sK0)) | ~spl8_17),
% 1.22/0.51    inference(resolution,[],[f150,f27])).
% 1.22/0.51  fof(f27,plain,(
% 1.22/0.51    ( ! [X0,X3,X1] : (~sP5(X3,X1,X0) | k1_funct_1(X0,sK6(X0,X1,X3)) = X3) )),
% 1.22/0.51    inference(cnf_transformation,[],[f15])).
% 1.22/0.52  fof(f15,plain,(
% 1.22/0.52    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.22/0.52    inference(flattening,[],[f14])).
% 1.22/0.52  fof(f14,plain,(
% 1.22/0.52    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.22/0.52    inference(ennf_transformation,[],[f5])).
% 1.22/0.52  fof(f5,axiom,(
% 1.22/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))))),
% 1.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_funct_1)).
% 1.22/0.52  fof(f150,plain,(
% 1.22/0.52    sP5(sK0,sK1,sK3) | ~spl8_17),
% 1.22/0.52    inference(avatar_component_clause,[],[f149])).
% 1.22/0.52  fof(f149,plain,(
% 1.22/0.52    spl8_17 <=> sP5(sK0,sK1,sK3)),
% 1.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 1.22/0.52  fof(f220,plain,(
% 1.22/0.52    sK0 != k1_funct_1(sK3,sK6(sK3,sK1,sK0)) | ~spl8_20),
% 1.22/0.52    inference(resolution,[],[f216,f19])).
% 1.22/0.52  fof(f19,plain,(
% 1.22/0.52    ( ! [X4] : (~m1_subset_1(X4,sK1) | sK0 != k1_funct_1(sK3,X4)) )),
% 1.22/0.52    inference(cnf_transformation,[],[f12])).
% 1.22/0.52  fof(f12,plain,(
% 1.22/0.52    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X3))),
% 1.22/0.52    inference(flattening,[],[f11])).
% 1.22/0.52  fof(f11,plain,(
% 1.22/0.52    ? [X0,X1,X2,X3] : ((! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X3)))),
% 1.22/0.52    inference(ennf_transformation,[],[f10])).
% 1.22/0.52  fof(f10,plain,(
% 1.22/0.52    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X3)) => ~(! [X4] : (m1_subset_1(X4,X1) => k1_funct_1(X3,X4) != X0) & r2_hidden(X0,k2_relset_1(X1,X2,X3))))),
% 1.22/0.52    inference(pure_predicate_removal,[],[f9])).
% 1.22/0.52  fof(f9,negated_conjecture,(
% 1.22/0.52    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ~(! [X4] : (m1_subset_1(X4,X1) => k1_funct_1(X3,X4) != X0) & r2_hidden(X0,k2_relset_1(X1,X2,X3))))),
% 1.22/0.52    inference(negated_conjecture,[],[f8])).
% 1.22/0.52  fof(f8,conjecture,(
% 1.22/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ~(! [X4] : (m1_subset_1(X4,X1) => k1_funct_1(X3,X4) != X0) & r2_hidden(X0,k2_relset_1(X1,X2,X3))))),
% 1.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t190_funct_2)).
% 1.22/0.52  fof(f216,plain,(
% 1.22/0.52    m1_subset_1(sK6(sK3,sK1,sK0),sK1) | ~spl8_20),
% 1.22/0.52    inference(avatar_component_clause,[],[f215])).
% 1.22/0.52  fof(f215,plain,(
% 1.22/0.52    spl8_20 <=> m1_subset_1(sK6(sK3,sK1,sK0),sK1)),
% 1.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).
% 1.22/0.52  fof(f217,plain,(
% 1.22/0.52    spl8_20 | ~spl8_18),
% 1.22/0.52    inference(avatar_split_clause,[],[f188,f174,f215])).
% 1.22/0.52  fof(f174,plain,(
% 1.22/0.52    spl8_18 <=> r2_hidden(sK6(sK3,sK1,sK0),sK1)),
% 1.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).
% 1.22/0.52  fof(f188,plain,(
% 1.22/0.52    m1_subset_1(sK6(sK3,sK1,sK0),sK1) | ~spl8_18),
% 1.22/0.52    inference(subsumption_resolution,[],[f187,f186])).
% 1.22/0.52  fof(f186,plain,(
% 1.22/0.52    ~v1_xboole_0(sK1) | ~spl8_18),
% 1.22/0.52    inference(resolution,[],[f175,f37])).
% 1.22/0.52  fof(f37,plain,(
% 1.22/0.52    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 1.22/0.52    inference(cnf_transformation,[],[f1])).
% 1.22/0.52  fof(f1,axiom,(
% 1.22/0.52    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.22/0.52  fof(f175,plain,(
% 1.22/0.52    r2_hidden(sK6(sK3,sK1,sK0),sK1) | ~spl8_18),
% 1.22/0.52    inference(avatar_component_clause,[],[f174])).
% 1.22/0.52  fof(f187,plain,(
% 1.22/0.52    v1_xboole_0(sK1) | m1_subset_1(sK6(sK3,sK1,sK0),sK1) | ~spl8_18),
% 1.22/0.52    inference(resolution,[],[f175,f34])).
% 1.22/0.52  fof(f34,plain,(
% 1.22/0.52    ( ! [X0,X1] : (~r2_hidden(X1,X0) | v1_xboole_0(X0) | m1_subset_1(X1,X0)) )),
% 1.22/0.52    inference(cnf_transformation,[],[f16])).
% 1.22/0.52  fof(f16,plain,(
% 1.22/0.52    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.22/0.52    inference(ennf_transformation,[],[f2])).
% 1.22/0.52  fof(f2,axiom,(
% 1.22/0.52    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 1.22/0.52  fof(f176,plain,(
% 1.22/0.52    spl8_18 | ~spl8_17),
% 1.22/0.52    inference(avatar_split_clause,[],[f153,f149,f174])).
% 1.22/0.52  fof(f153,plain,(
% 1.22/0.52    r2_hidden(sK6(sK3,sK1,sK0),sK1) | ~spl8_17),
% 1.22/0.52    inference(resolution,[],[f150,f26])).
% 1.22/0.52  % (28141)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 1.22/0.52  fof(f26,plain,(
% 1.22/0.52    ( ! [X0,X3,X1] : (~sP5(X3,X1,X0) | r2_hidden(sK6(X0,X1,X3),X1)) )),
% 1.22/0.52    inference(cnf_transformation,[],[f15])).
% 1.22/0.52  fof(f151,plain,(
% 1.22/0.52    spl8_17 | ~spl8_1 | ~spl8_4 | ~spl8_16),
% 1.22/0.52    inference(avatar_split_clause,[],[f147,f138,f70,f46,f149])).
% 1.22/0.52  fof(f46,plain,(
% 1.22/0.52    spl8_1 <=> v1_funct_1(sK3)),
% 1.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 1.22/0.52  fof(f70,plain,(
% 1.22/0.52    spl8_4 <=> v1_relat_1(sK3)),
% 1.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 1.22/0.52  fof(f138,plain,(
% 1.22/0.52    spl8_16 <=> r2_hidden(sK0,k9_relat_1(sK3,sK1))),
% 1.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).
% 1.22/0.52  fof(f147,plain,(
% 1.22/0.52    sP5(sK0,sK1,sK3) | (~spl8_1 | ~spl8_4 | ~spl8_16)),
% 1.22/0.52    inference(subsumption_resolution,[],[f146,f71])).
% 1.22/0.52  fof(f71,plain,(
% 1.22/0.52    v1_relat_1(sK3) | ~spl8_4),
% 1.22/0.52    inference(avatar_component_clause,[],[f70])).
% 1.22/0.52  fof(f146,plain,(
% 1.22/0.52    sP5(sK0,sK1,sK3) | ~v1_relat_1(sK3) | (~spl8_1 | ~spl8_16)),
% 1.22/0.52    inference(subsumption_resolution,[],[f143,f47])).
% 1.22/0.52  fof(f47,plain,(
% 1.22/0.52    v1_funct_1(sK3) | ~spl8_1),
% 1.22/0.52    inference(avatar_component_clause,[],[f46])).
% 1.22/0.52  fof(f143,plain,(
% 1.22/0.52    ~v1_funct_1(sK3) | sP5(sK0,sK1,sK3) | ~v1_relat_1(sK3) | ~spl8_16),
% 1.22/0.52    inference(resolution,[],[f139,f42])).
% 1.22/0.52  fof(f42,plain,(
% 1.22/0.52    ( ! [X0,X3,X1] : (~r2_hidden(X3,k9_relat_1(X0,X1)) | ~v1_funct_1(X0) | sP5(X3,X1,X0) | ~v1_relat_1(X0)) )),
% 1.22/0.52    inference(equality_resolution,[],[f29])).
% 1.22/0.52  fof(f29,plain,(
% 1.22/0.52    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | sP5(X3,X1,X0) | ~r2_hidden(X3,X2) | k9_relat_1(X0,X1) != X2) )),
% 1.22/0.52    inference(cnf_transformation,[],[f15])).
% 1.22/0.52  fof(f139,plain,(
% 1.22/0.52    r2_hidden(sK0,k9_relat_1(sK3,sK1)) | ~spl8_16),
% 1.22/0.52    inference(avatar_component_clause,[],[f138])).
% 1.22/0.52  fof(f140,plain,(
% 1.22/0.52    spl8_16 | ~spl8_3 | ~spl8_11),
% 1.22/0.52    inference(avatar_split_clause,[],[f111,f103,f55,f138])).
% 1.22/0.52  fof(f55,plain,(
% 1.22/0.52    spl8_3 <=> r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3))),
% 1.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 1.22/0.52  fof(f103,plain,(
% 1.22/0.52    spl8_11 <=> k2_relset_1(sK1,sK2,sK3) = k9_relat_1(sK3,sK1)),
% 1.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 1.22/0.52  fof(f111,plain,(
% 1.22/0.52    r2_hidden(sK0,k9_relat_1(sK3,sK1)) | (~spl8_3 | ~spl8_11)),
% 1.22/0.52    inference(superposition,[],[f56,f104])).
% 1.22/0.52  fof(f104,plain,(
% 1.22/0.52    k2_relset_1(sK1,sK2,sK3) = k9_relat_1(sK3,sK1) | ~spl8_11),
% 1.22/0.52    inference(avatar_component_clause,[],[f103])).
% 1.22/0.52  fof(f56,plain,(
% 1.22/0.52    r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3)) | ~spl8_3),
% 1.22/0.52    inference(avatar_component_clause,[],[f55])).
% 1.22/0.52  fof(f105,plain,(
% 1.22/0.52    spl8_11 | ~spl8_2 | ~spl8_10),
% 1.22/0.52    inference(avatar_split_clause,[],[f101,f98,f51,f103])).
% 1.22/0.52  fof(f51,plain,(
% 1.22/0.52    spl8_2 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 1.22/0.52  fof(f98,plain,(
% 1.22/0.52    spl8_10 <=> k2_relset_1(sK1,sK2,sK3) = k7_relset_1(sK1,sK2,sK3,sK1)),
% 1.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 1.22/0.52  fof(f101,plain,(
% 1.22/0.52    k2_relset_1(sK1,sK2,sK3) = k9_relat_1(sK3,sK1) | (~spl8_2 | ~spl8_10)),
% 1.22/0.52    inference(forward_demodulation,[],[f99,f60])).
% 1.22/0.52  fof(f60,plain,(
% 1.22/0.52    ( ! [X0] : (k9_relat_1(sK3,X0) = k7_relset_1(sK1,sK2,sK3,X0)) ) | ~spl8_2),
% 1.22/0.52    inference(resolution,[],[f52,f23])).
% 1.22/0.52  fof(f23,plain,(
% 1.22/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 1.22/0.52    inference(cnf_transformation,[],[f13])).
% 1.22/0.52  fof(f13,plain,(
% 1.22/0.52    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.22/0.52    inference(ennf_transformation,[],[f6])).
% 1.22/0.52  fof(f6,axiom,(
% 1.22/0.52    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 1.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 1.22/0.52  fof(f52,plain,(
% 1.22/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl8_2),
% 1.22/0.52    inference(avatar_component_clause,[],[f51])).
% 1.22/0.52  fof(f99,plain,(
% 1.22/0.52    k2_relset_1(sK1,sK2,sK3) = k7_relset_1(sK1,sK2,sK3,sK1) | ~spl8_10),
% 1.22/0.52    inference(avatar_component_clause,[],[f98])).
% 1.22/0.52  fof(f100,plain,(
% 1.22/0.52    spl8_10 | ~spl8_2),
% 1.22/0.52    inference(avatar_split_clause,[],[f58,f51,f98])).
% 1.22/0.52  fof(f58,plain,(
% 1.22/0.52    k2_relset_1(sK1,sK2,sK3) = k7_relset_1(sK1,sK2,sK3,sK1) | ~spl8_2),
% 1.22/0.52    inference(resolution,[],[f52,f38])).
% 1.22/0.52  fof(f38,plain,(
% 1.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)) )),
% 1.22/0.52    inference(cnf_transformation,[],[f17])).
% 1.22/0.52  fof(f17,plain,(
% 1.22/0.52    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.22/0.52    inference(ennf_transformation,[],[f7])).
% 1.22/0.52  fof(f7,axiom,(
% 1.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)))),
% 1.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).
% 1.22/0.52  fof(f72,plain,(
% 1.22/0.52    spl8_4 | ~spl8_2),
% 1.22/0.52    inference(avatar_split_clause,[],[f64,f51,f70])).
% 1.22/0.52  fof(f64,plain,(
% 1.22/0.52    v1_relat_1(sK3) | ~spl8_2),
% 1.22/0.52    inference(subsumption_resolution,[],[f61,f41])).
% 1.22/0.52  fof(f41,plain,(
% 1.22/0.52    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.22/0.52    inference(cnf_transformation,[],[f4])).
% 1.22/0.52  fof(f4,axiom,(
% 1.22/0.52    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.22/0.52  fof(f61,plain,(
% 1.22/0.52    ~v1_relat_1(k2_zfmisc_1(sK1,sK2)) | v1_relat_1(sK3) | ~spl8_2),
% 1.22/0.52    inference(resolution,[],[f52,f40])).
% 1.22/0.52  fof(f40,plain,(
% 1.22/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 1.22/0.52    inference(cnf_transformation,[],[f18])).
% 1.22/0.52  fof(f18,plain,(
% 1.22/0.52    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.22/0.52    inference(ennf_transformation,[],[f3])).
% 1.22/0.52  fof(f3,axiom,(
% 1.22/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.22/0.52  fof(f57,plain,(
% 1.22/0.52    spl8_3),
% 1.22/0.52    inference(avatar_split_clause,[],[f22,f55])).
% 1.22/0.52  fof(f22,plain,(
% 1.22/0.52    r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3))),
% 1.22/0.52    inference(cnf_transformation,[],[f12])).
% 1.22/0.52  fof(f53,plain,(
% 1.22/0.52    spl8_2),
% 1.22/0.52    inference(avatar_split_clause,[],[f21,f51])).
% 1.22/0.52  fof(f21,plain,(
% 1.22/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.22/0.52    inference(cnf_transformation,[],[f12])).
% 1.22/0.52  fof(f48,plain,(
% 1.22/0.52    spl8_1),
% 1.22/0.52    inference(avatar_split_clause,[],[f20,f46])).
% 1.22/0.52  fof(f20,plain,(
% 1.22/0.52    v1_funct_1(sK3)),
% 1.22/0.52    inference(cnf_transformation,[],[f12])).
% 1.22/0.52  % SZS output end Proof for theBenchmark
% 1.22/0.52  % (28124)------------------------------
% 1.22/0.52  % (28124)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.52  % (28124)Termination reason: Refutation
% 1.22/0.52  
% 1.22/0.52  % (28124)Memory used [KB]: 6268
% 1.22/0.52  % (28124)Time elapsed: 0.065 s
% 1.22/0.52  % (28124)------------------------------
% 1.22/0.52  % (28124)------------------------------
% 1.22/0.52  % (28136)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.22/0.52  % (28123)Success in time 0.155 s
%------------------------------------------------------------------------------
