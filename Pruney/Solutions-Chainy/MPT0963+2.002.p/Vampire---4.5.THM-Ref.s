%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:28 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 189 expanded)
%              Number of leaves         :   13 (  52 expanded)
%              Depth                    :   10
%              Number of atoms          :  233 ( 775 expanded)
%              Number of equality atoms :   17 (  76 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f210,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f93,f101,f105,f111,f131,f168,f202,f209])).

fof(f209,plain,(
    spl10_3 ),
    inference(avatar_contradiction_clause,[],[f206])).

% (18452)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
fof(f206,plain,
    ( $false
    | spl10_3 ),
    inference(unit_resulting_resolution,[],[f23,f92])).

fof(f92,plain,
    ( ~ v1_funct_1(sK2)
    | spl10_3 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl10_3
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f23,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2) )
      & ! [X3] :
          ( r2_hidden(k1_funct_1(X2,X3),X1)
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2) )
      & ! [X3] :
          ( r2_hidden(k1_funct_1(X2,X3),X1)
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( ! [X3] :
                ( r2_hidden(X3,X0)
               => r2_hidden(k1_funct_1(X2,X3),X1) )
            & k1_relat_1(X2) = X0 )
         => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X2,X0,X1)
            & v1_funct_1(X2) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( ! [X3] :
              ( r2_hidden(X3,X0)
             => r2_hidden(k1_funct_1(X2,X3),X1) )
          & k1_relat_1(X2) = X0 )
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_funct_2)).

fof(f202,plain,
    ( spl10_2
    | ~ spl10_5
    | ~ spl10_6 ),
    inference(avatar_contradiction_clause,[],[f196])).

fof(f196,plain,
    ( $false
    | spl10_2
    | ~ spl10_5
    | ~ spl10_6 ),
    inference(unit_resulting_resolution,[],[f174,f188,f48])).

fof(f48,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(sK7(X0,X2),X2),X0)
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK7(X0,X2),X2),X0)
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f188,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK7(sK2,sK9(k2_relat_1(sK2),sK1)),X0),sK2)
    | spl10_2
    | ~ spl10_5
    | ~ spl10_6 ),
    inference(unit_resulting_resolution,[],[f182,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,sK0)
      | ~ r2_hidden(k4_tarski(X0,X1),sK2) ) ),
    inference(superposition,[],[f47,f24])).

fof(f24,plain,(
    sK0 = k1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f47,plain,(
    ! [X2,X0,X3] :
      ( r2_hidden(X2,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X2,X3),X0) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f182,plain,
    ( ~ r2_hidden(sK7(sK2,sK9(k2_relat_1(sK2),sK1)),sK0)
    | spl10_2
    | ~ spl10_5
    | ~ spl10_6 ),
    inference(unit_resulting_resolution,[],[f175,f174,f123])).

fof(f123,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK7(sK2,X1),sK0)
        | r2_hidden(X1,sK1)
        | ~ r2_hidden(X1,k2_relat_1(sK2)) )
    | ~ spl10_6 ),
    inference(superposition,[],[f20,f114])).

fof(f114,plain,
    ( ! [X2] :
        ( k1_funct_1(sK2,sK7(sK2,X2)) = X2
        | ~ r2_hidden(X2,k2_relat_1(sK2)) )
    | ~ spl10_6 ),
    inference(resolution,[],[f110,f48])).

fof(f110,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(k4_tarski(X2,X3),sK2)
        | k1_funct_1(sK2,X2) = X3 )
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl10_6
  <=> ! [X3,X2] :
        ( k1_funct_1(sK2,X2) = X3
        | ~ r2_hidden(k4_tarski(X2,X3),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f20,plain,(
    ! [X3] :
      ( r2_hidden(k1_funct_1(sK2,X3),sK1)
      | ~ r2_hidden(X3,sK0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f175,plain,
    ( ~ r2_hidden(sK9(k2_relat_1(sK2),sK1),sK1)
    | spl10_2
    | ~ spl10_5 ),
    inference(unit_resulting_resolution,[],[f172,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK9(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f172,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK1)
    | spl10_2
    | ~ spl10_5 ),
    inference(unit_resulting_resolution,[],[f88,f100])).

fof(f100,plain,
    ( ! [X5] :
        ( v1_funct_2(sK2,sK0,X5)
        | ~ r1_tarski(k2_relat_1(sK2),X5) )
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl10_5
  <=> ! [X5] :
        ( v1_funct_2(sK2,sK0,X5)
        | ~ r1_tarski(k2_relat_1(sK2),X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f88,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | spl10_2 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl10_2
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f174,plain,
    ( r2_hidden(sK9(k2_relat_1(sK2),sK1),k2_relat_1(sK2))
    | spl10_2
    | ~ spl10_5 ),
    inference(unit_resulting_resolution,[],[f172,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK9(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f168,plain,
    ( spl10_1
    | ~ spl10_6
    | ~ spl10_8 ),
    inference(avatar_contradiction_clause,[],[f162])).

fof(f162,plain,
    ( $false
    | spl10_1
    | ~ spl10_6
    | ~ spl10_8 ),
    inference(unit_resulting_resolution,[],[f136,f148,f48])).

fof(f148,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK7(sK2,sK9(k2_relat_1(sK2),sK1)),X0),sK2)
    | spl10_1
    | ~ spl10_6
    | ~ spl10_8 ),
    inference(unit_resulting_resolution,[],[f146,f78])).

fof(f146,plain,
    ( ~ r2_hidden(sK7(sK2,sK9(k2_relat_1(sK2),sK1)),sK0)
    | spl10_1
    | ~ spl10_6
    | ~ spl10_8 ),
    inference(unit_resulting_resolution,[],[f137,f136,f123])).

fof(f137,plain,
    ( ~ r2_hidden(sK9(k2_relat_1(sK2),sK1),sK1)
    | spl10_1
    | ~ spl10_8 ),
    inference(unit_resulting_resolution,[],[f134,f41])).

fof(f134,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK1)
    | spl10_1
    | ~ spl10_8 ),
    inference(unit_resulting_resolution,[],[f84,f130])).

fof(f130,plain,
    ( ! [X6] :
        ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X6)))
        | ~ r1_tarski(k2_relat_1(sK2),X6) )
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl10_8
  <=> ! [X6] :
        ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X6)))
        | ~ r1_tarski(k2_relat_1(sK2),X6) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f84,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl10_1 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl10_1
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f136,plain,
    ( r2_hidden(sK9(k2_relat_1(sK2),sK1),k2_relat_1(sK2))
    | spl10_1
    | ~ spl10_8 ),
    inference(unit_resulting_resolution,[],[f134,f40])).

fof(f131,plain,
    ( ~ spl10_4
    | spl10_8 ),
    inference(avatar_split_clause,[],[f77,f129,f95])).

fof(f95,plain,
    ( spl10_4
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f77,plain,(
    ! [X6] :
      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X6)))
      | ~ v1_relat_1(sK2)
      | ~ r1_tarski(k2_relat_1(sK2),X6) ) ),
    inference(forward_demodulation,[],[f70,f24])).

fof(f70,plain,(
    ! [X6] :
      ( ~ v1_relat_1(sK2)
      | ~ r1_tarski(k2_relat_1(sK2),X6)
      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X6))) ) ),
    inference(resolution,[],[f23,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

fof(f111,plain,
    ( spl10_6
    | ~ spl10_4 ),
    inference(avatar_split_clause,[],[f67,f95,f109])).

fof(f67,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(sK2)
      | k1_funct_1(sK2,X2) = X3
      | ~ r2_hidden(k4_tarski(X2,X3),sK2) ) ),
    inference(resolution,[],[f23,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(f105,plain,(
    spl10_4 ),
    inference(avatar_contradiction_clause,[],[f102])).

fof(f102,plain,
    ( $false
    | spl10_4 ),
    inference(unit_resulting_resolution,[],[f22,f97])).

fof(f97,plain,
    ( ~ v1_relat_1(sK2)
    | spl10_4 ),
    inference(avatar_component_clause,[],[f95])).

fof(f22,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f101,plain,
    ( ~ spl10_4
    | spl10_5 ),
    inference(avatar_split_clause,[],[f76,f99,f95])).

fof(f76,plain,(
    ! [X5] :
      ( v1_funct_2(sK2,sK0,X5)
      | ~ v1_relat_1(sK2)
      | ~ r1_tarski(k2_relat_1(sK2),X5) ) ),
    inference(forward_demodulation,[],[f69,f24])).

fof(f69,plain,(
    ! [X5] :
      ( ~ v1_relat_1(sK2)
      | ~ r1_tarski(k2_relat_1(sK2),X5)
      | v1_funct_2(sK2,k1_relat_1(sK2),X5) ) ),
    inference(resolution,[],[f23,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | v1_funct_2(X1,k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f93,plain,
    ( ~ spl10_1
    | ~ spl10_2
    | ~ spl10_3 ),
    inference(avatar_split_clause,[],[f21,f90,f86,f82])).

fof(f21,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:58:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.53  % (18447)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (18443)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (18439)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (18432)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.55  % (18455)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.55  % (18459)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.55  % (18437)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.55  % (18451)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.56  % (18458)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.56  % (18436)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.56  % (18436)Refutation found. Thanks to Tanya!
% 0.21/0.56  % SZS status Theorem for theBenchmark
% 0.21/0.56  % SZS output start Proof for theBenchmark
% 0.21/0.56  fof(f210,plain,(
% 0.21/0.56    $false),
% 0.21/0.56    inference(avatar_sat_refutation,[],[f93,f101,f105,f111,f131,f168,f202,f209])).
% 0.21/0.56  fof(f209,plain,(
% 0.21/0.56    spl10_3),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f206])).
% 0.21/0.56  % (18452)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.56  fof(f206,plain,(
% 0.21/0.56    $false | spl10_3),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f23,f92])).
% 0.21/0.56  fof(f92,plain,(
% 0.21/0.56    ~v1_funct_1(sK2) | spl10_3),
% 0.21/0.56    inference(avatar_component_clause,[],[f90])).
% 0.21/0.56  fof(f90,plain,(
% 0.21/0.56    spl10_3 <=> v1_funct_1(sK2)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 0.21/0.56  fof(f23,plain,(
% 0.21/0.56    v1_funct_1(sK2)),
% 0.21/0.56    inference(cnf_transformation,[],[f12])).
% 0.21/0.56  fof(f12,plain,(
% 0.21/0.56    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & ! [X3] : (r2_hidden(k1_funct_1(X2,X3),X1) | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.21/0.56    inference(flattening,[],[f11])).
% 0.21/0.56  fof(f11,plain,(
% 0.21/0.56    ? [X0,X1,X2] : (((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & (! [X3] : (r2_hidden(k1_funct_1(X2,X3),X1) | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0)) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.21/0.56    inference(ennf_transformation,[],[f10])).
% 0.21/0.56  fof(f10,negated_conjecture,(
% 0.21/0.56    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,X0) => r2_hidden(k1_funct_1(X2,X3),X1)) & k1_relat_1(X2) = X0) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 0.21/0.56    inference(negated_conjecture,[],[f9])).
% 0.21/0.56  fof(f9,conjecture,(
% 0.21/0.56    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,X0) => r2_hidden(k1_funct_1(X2,X3),X1)) & k1_relat_1(X2) = X0) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_funct_2)).
% 0.21/0.56  fof(f202,plain,(
% 0.21/0.56    spl10_2 | ~spl10_5 | ~spl10_6),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f196])).
% 0.21/0.56  fof(f196,plain,(
% 0.21/0.56    $false | (spl10_2 | ~spl10_5 | ~spl10_6)),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f174,f188,f48])).
% 0.21/0.56  fof(f48,plain,(
% 0.21/0.56    ( ! [X2,X0] : (r2_hidden(k4_tarski(sK7(X0,X2),X2),X0) | ~r2_hidden(X2,k2_relat_1(X0))) )),
% 0.21/0.56    inference(equality_resolution,[],[f36])).
% 0.21/0.56  fof(f36,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK7(X0,X2),X2),X0) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.21/0.56    inference(cnf_transformation,[],[f4])).
% 0.21/0.56  fof(f4,axiom,(
% 0.21/0.56    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).
% 0.21/0.56  fof(f188,plain,(
% 0.21/0.56    ( ! [X0] : (~r2_hidden(k4_tarski(sK7(sK2,sK9(k2_relat_1(sK2),sK1)),X0),sK2)) ) | (spl10_2 | ~spl10_5 | ~spl10_6)),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f182,f78])).
% 0.21/0.56  fof(f78,plain,(
% 0.21/0.56    ( ! [X0,X1] : (r2_hidden(X0,sK0) | ~r2_hidden(k4_tarski(X0,X1),sK2)) )),
% 0.21/0.56    inference(superposition,[],[f47,f24])).
% 0.21/0.56  fof(f24,plain,(
% 0.21/0.56    sK0 = k1_relat_1(sK2)),
% 0.21/0.56    inference(cnf_transformation,[],[f12])).
% 0.21/0.56  fof(f47,plain,(
% 0.21/0.56    ( ! [X2,X0,X3] : (r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(k4_tarski(X2,X3),X0)) )),
% 0.21/0.56    inference(equality_resolution,[],[f31])).
% 0.21/0.56  fof(f31,plain,(
% 0.21/0.56    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1) | k1_relat_1(X0) != X1) )),
% 0.21/0.56    inference(cnf_transformation,[],[f3])).
% 0.21/0.56  fof(f3,axiom,(
% 0.21/0.56    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 0.21/0.56  fof(f182,plain,(
% 0.21/0.56    ~r2_hidden(sK7(sK2,sK9(k2_relat_1(sK2),sK1)),sK0) | (spl10_2 | ~spl10_5 | ~spl10_6)),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f175,f174,f123])).
% 0.21/0.56  fof(f123,plain,(
% 0.21/0.56    ( ! [X1] : (~r2_hidden(sK7(sK2,X1),sK0) | r2_hidden(X1,sK1) | ~r2_hidden(X1,k2_relat_1(sK2))) ) | ~spl10_6),
% 0.21/0.56    inference(superposition,[],[f20,f114])).
% 0.21/0.56  fof(f114,plain,(
% 0.21/0.56    ( ! [X2] : (k1_funct_1(sK2,sK7(sK2,X2)) = X2 | ~r2_hidden(X2,k2_relat_1(sK2))) ) | ~spl10_6),
% 0.21/0.56    inference(resolution,[],[f110,f48])).
% 0.21/0.56  fof(f110,plain,(
% 0.21/0.56    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),sK2) | k1_funct_1(sK2,X2) = X3) ) | ~spl10_6),
% 0.21/0.56    inference(avatar_component_clause,[],[f109])).
% 0.21/0.56  fof(f109,plain,(
% 0.21/0.56    spl10_6 <=> ! [X3,X2] : (k1_funct_1(sK2,X2) = X3 | ~r2_hidden(k4_tarski(X2,X3),sK2))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).
% 0.21/0.56  fof(f20,plain,(
% 0.21/0.56    ( ! [X3] : (r2_hidden(k1_funct_1(sK2,X3),sK1) | ~r2_hidden(X3,sK0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f12])).
% 0.21/0.56  fof(f175,plain,(
% 0.21/0.56    ~r2_hidden(sK9(k2_relat_1(sK2),sK1),sK1) | (spl10_2 | ~spl10_5)),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f172,f41])).
% 0.21/0.56  fof(f41,plain,(
% 0.21/0.56    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK9(X0,X1),X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f19])).
% 0.21/0.56  fof(f19,plain,(
% 0.21/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f1])).
% 0.21/0.56  fof(f1,axiom,(
% 0.21/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.56  fof(f172,plain,(
% 0.21/0.56    ~r1_tarski(k2_relat_1(sK2),sK1) | (spl10_2 | ~spl10_5)),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f88,f100])).
% 0.21/0.56  fof(f100,plain,(
% 0.21/0.56    ( ! [X5] : (v1_funct_2(sK2,sK0,X5) | ~r1_tarski(k2_relat_1(sK2),X5)) ) | ~spl10_5),
% 0.21/0.56    inference(avatar_component_clause,[],[f99])).
% 0.21/0.56  fof(f99,plain,(
% 0.21/0.56    spl10_5 <=> ! [X5] : (v1_funct_2(sK2,sK0,X5) | ~r1_tarski(k2_relat_1(sK2),X5))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 0.21/0.56  fof(f88,plain,(
% 0.21/0.56    ~v1_funct_2(sK2,sK0,sK1) | spl10_2),
% 0.21/0.56    inference(avatar_component_clause,[],[f86])).
% 0.21/0.56  fof(f86,plain,(
% 0.21/0.56    spl10_2 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 0.21/0.56  fof(f174,plain,(
% 0.21/0.56    r2_hidden(sK9(k2_relat_1(sK2),sK1),k2_relat_1(sK2)) | (spl10_2 | ~spl10_5)),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f172,f40])).
% 0.21/0.56  fof(f40,plain,(
% 0.21/0.56    ( ! [X0,X1] : (r2_hidden(sK9(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f19])).
% 0.21/0.56  fof(f168,plain,(
% 0.21/0.56    spl10_1 | ~spl10_6 | ~spl10_8),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f162])).
% 0.21/0.56  fof(f162,plain,(
% 0.21/0.56    $false | (spl10_1 | ~spl10_6 | ~spl10_8)),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f136,f148,f48])).
% 0.21/0.56  fof(f148,plain,(
% 0.21/0.56    ( ! [X0] : (~r2_hidden(k4_tarski(sK7(sK2,sK9(k2_relat_1(sK2),sK1)),X0),sK2)) ) | (spl10_1 | ~spl10_6 | ~spl10_8)),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f146,f78])).
% 0.21/0.56  fof(f146,plain,(
% 0.21/0.56    ~r2_hidden(sK7(sK2,sK9(k2_relat_1(sK2),sK1)),sK0) | (spl10_1 | ~spl10_6 | ~spl10_8)),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f137,f136,f123])).
% 0.21/0.56  fof(f137,plain,(
% 0.21/0.56    ~r2_hidden(sK9(k2_relat_1(sK2),sK1),sK1) | (spl10_1 | ~spl10_8)),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f134,f41])).
% 0.21/0.56  fof(f134,plain,(
% 0.21/0.56    ~r1_tarski(k2_relat_1(sK2),sK1) | (spl10_1 | ~spl10_8)),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f84,f130])).
% 0.21/0.56  fof(f130,plain,(
% 0.21/0.56    ( ! [X6] : (m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X6))) | ~r1_tarski(k2_relat_1(sK2),X6)) ) | ~spl10_8),
% 0.21/0.56    inference(avatar_component_clause,[],[f129])).
% 0.21/0.56  fof(f129,plain,(
% 0.21/0.56    spl10_8 <=> ! [X6] : (m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X6))) | ~r1_tarski(k2_relat_1(sK2),X6))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).
% 0.21/0.56  fof(f84,plain,(
% 0.21/0.56    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl10_1),
% 0.21/0.56    inference(avatar_component_clause,[],[f82])).
% 0.21/0.56  fof(f82,plain,(
% 0.21/0.56    spl10_1 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 0.21/0.56  fof(f136,plain,(
% 0.21/0.56    r2_hidden(sK9(k2_relat_1(sK2),sK1),k2_relat_1(sK2)) | (spl10_1 | ~spl10_8)),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f134,f40])).
% 0.21/0.56  fof(f131,plain,(
% 0.21/0.56    ~spl10_4 | spl10_8),
% 0.21/0.56    inference(avatar_split_clause,[],[f77,f129,f95])).
% 0.21/0.56  fof(f95,plain,(
% 0.21/0.56    spl10_4 <=> v1_relat_1(sK2)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 0.21/0.56  fof(f77,plain,(
% 0.21/0.56    ( ! [X6] : (m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X6))) | ~v1_relat_1(sK2) | ~r1_tarski(k2_relat_1(sK2),X6)) )),
% 0.21/0.56    inference(forward_demodulation,[],[f70,f24])).
% 0.21/0.56  fof(f70,plain,(
% 0.21/0.56    ( ! [X6] : (~v1_relat_1(sK2) | ~r1_tarski(k2_relat_1(sK2),X6) | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X6)))) )),
% 0.21/0.56    inference(resolution,[],[f23,f27])).
% 0.21/0.56  fof(f27,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f16])).
% 0.21/0.56  fof(f16,plain,(
% 0.21/0.56    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.56    inference(flattening,[],[f15])).
% 0.21/0.56  fof(f15,plain,(
% 0.21/0.56    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.56    inference(ennf_transformation,[],[f8])).
% 0.21/0.56  fof(f8,axiom,(
% 0.21/0.56    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).
% 0.21/0.56  fof(f111,plain,(
% 0.21/0.56    spl10_6 | ~spl10_4),
% 0.21/0.56    inference(avatar_split_clause,[],[f67,f95,f109])).
% 0.21/0.56  fof(f67,plain,(
% 0.21/0.56    ( ! [X2,X3] : (~v1_relat_1(sK2) | k1_funct_1(sK2,X2) = X3 | ~r2_hidden(k4_tarski(X2,X3),sK2)) )),
% 0.21/0.56    inference(resolution,[],[f23,f29])).
% 0.21/0.56  fof(f29,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_relat_1(X2) | k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f18])).
% 0.21/0.56  fof(f18,plain,(
% 0.21/0.56    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.56    inference(flattening,[],[f17])).
% 0.21/0.56  fof(f17,plain,(
% 0.21/0.56    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.56    inference(ennf_transformation,[],[f6])).
% 0.21/0.56  fof(f6,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).
% 0.21/0.56  fof(f105,plain,(
% 0.21/0.56    spl10_4),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f102])).
% 0.21/0.56  fof(f102,plain,(
% 0.21/0.56    $false | spl10_4),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f22,f97])).
% 0.21/0.56  fof(f97,plain,(
% 0.21/0.56    ~v1_relat_1(sK2) | spl10_4),
% 0.21/0.56    inference(avatar_component_clause,[],[f95])).
% 0.21/0.56  fof(f22,plain,(
% 0.21/0.56    v1_relat_1(sK2)),
% 0.21/0.56    inference(cnf_transformation,[],[f12])).
% 0.21/0.56  fof(f101,plain,(
% 0.21/0.56    ~spl10_4 | spl10_5),
% 0.21/0.56    inference(avatar_split_clause,[],[f76,f99,f95])).
% 0.21/0.56  fof(f76,plain,(
% 0.21/0.56    ( ! [X5] : (v1_funct_2(sK2,sK0,X5) | ~v1_relat_1(sK2) | ~r1_tarski(k2_relat_1(sK2),X5)) )),
% 0.21/0.56    inference(forward_demodulation,[],[f69,f24])).
% 0.21/0.56  fof(f69,plain,(
% 0.21/0.56    ( ! [X5] : (~v1_relat_1(sK2) | ~r1_tarski(k2_relat_1(sK2),X5) | v1_funct_2(sK2,k1_relat_1(sK2),X5)) )),
% 0.21/0.56    inference(resolution,[],[f23,f26])).
% 0.21/0.56  fof(f26,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | v1_funct_2(X1,k1_relat_1(X1),X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f16])).
% 0.21/0.56  fof(f93,plain,(
% 0.21/0.56    ~spl10_1 | ~spl10_2 | ~spl10_3),
% 0.21/0.56    inference(avatar_split_clause,[],[f21,f90,f86,f82])).
% 0.21/0.56  fof(f21,plain,(
% 0.21/0.56    ~v1_funct_1(sK2) | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.56    inference(cnf_transformation,[],[f12])).
% 0.21/0.56  % SZS output end Proof for theBenchmark
% 0.21/0.56  % (18436)------------------------------
% 0.21/0.56  % (18436)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (18436)Termination reason: Refutation
% 0.21/0.56  
% 0.21/0.56  % (18436)Memory used [KB]: 6268
% 0.21/0.56  % (18436)Time elapsed: 0.152 s
% 0.21/0.56  % (18436)------------------------------
% 0.21/0.56  % (18436)------------------------------
% 0.21/0.56  % (18431)Success in time 0.196 s
%------------------------------------------------------------------------------
