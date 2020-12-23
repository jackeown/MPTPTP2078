%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:29 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 140 expanded)
%              Number of leaves         :   18 (  57 expanded)
%              Depth                    :   10
%              Number of atoms          :  227 ( 354 expanded)
%              Number of equality atoms :   30 (  62 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f134,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f35,f48,f53,f65,f72,f78,f90,f99,f105,f113,f114,f128,f132])).

fof(f132,plain,
    ( ~ spl8_7
    | ~ spl8_8
    | ~ spl8_12 ),
    inference(avatar_contradiction_clause,[],[f131])).

fof(f131,plain,
    ( $false
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f129,f121])).

fof(f121,plain,
    ( ! [X4] : ~ r2_hidden(k4_tarski(X4,sK3),sK2)
    | ~ spl8_7
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f116,f76])).

fof(f76,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl8_8
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f116,plain,
    ( ! [X4] :
        ( sK1 != k2_relat_1(sK2)
        | ~ r2_hidden(k4_tarski(X4,sK3),sK2) )
    | ~ spl8_7 ),
    inference(forward_demodulation,[],[f15,f71])).

fof(f71,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl8_7
  <=> k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f15,plain,(
    ! [X4] :
      ( sK1 != k2_relset_1(sK0,sK1,sK2)
      | ~ r2_hidden(k4_tarski(X4,sK3),sK2) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X4,X3),X2)
            | ~ r2_hidden(X3,X1) )
      <~> k2_relset_1(X0,X1,X2) = X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( ! [X3] :
              ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),X2)
                & r2_hidden(X3,X1) )
        <=> k2_relset_1(X0,X1,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),X2)
              & r2_hidden(X3,X1) )
      <=> k2_relset_1(X0,X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_relset_1)).

fof(f129,plain,
    ( r2_hidden(k4_tarski(sK7(sK2,sK3),sK3),sK2)
    | ~ spl8_12 ),
    inference(resolution,[],[f127,f19])).

fof(f19,plain,(
    ! [X2,X0] :
      ( ~ sP6(X2,X0)
      | r2_hidden(k4_tarski(sK7(X0,X2),X2),X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f127,plain,
    ( sP6(sK3,sK2)
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl8_12
  <=> sP6(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f128,plain,
    ( spl8_12
    | ~ spl8_2
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f123,f75,f41,f125])).

fof(f41,plain,
    ( spl8_2
  <=> r2_hidden(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f123,plain,
    ( sP6(sK3,sK2)
    | ~ spl8_2
    | ~ spl8_8 ),
    inference(resolution,[],[f120,f43])).

fof(f43,plain,
    ( r2_hidden(sK3,sK1)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f41])).

fof(f120,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK1)
        | sP6(X1,sK2) )
    | ~ spl8_8 ),
    inference(superposition,[],[f29,f76])).

fof(f29,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k2_relat_1(X0))
      | sP6(X2,X0) ) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( sP6(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f114,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | k2_relset_1(sK0,sK1,sK2) != k2_relat_1(sK2)
    | sK1 = k2_relat_1(sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f113,plain,
    ( ~ spl8_4
    | ~ spl8_6
    | ~ spl8_10
    | spl8_11 ),
    inference(avatar_contradiction_clause,[],[f112])).

fof(f112,plain,
    ( $false
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_10
    | spl8_11 ),
    inference(subsumption_resolution,[],[f110,f104])).

fof(f104,plain,
    ( ~ r2_hidden(sK5(sK2,sK1),sK1)
    | spl8_11 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl8_11
  <=> r2_hidden(sK5(sK2,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f110,plain,
    ( r2_hidden(sK5(sK2,sK1),sK1)
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_10 ),
    inference(resolution,[],[f98,f79])).

fof(f79,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK2))
        | r2_hidden(X0,sK1) )
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(resolution,[],[f54,f64])).

fof(f64,plain,
    ( v5_relat_1(sK2,sK1)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl8_6
  <=> v5_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f54,plain,
    ( ! [X0,X1] :
        ( ~ v5_relat_1(sK2,X0)
        | ~ r2_hidden(X1,k2_relat_1(sK2))
        | r2_hidden(X1,X0) )
    | ~ spl8_4 ),
    inference(resolution,[],[f52,f18])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ r2_hidden(X2,k2_relat_1(X1))
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,k2_relat_1(X1)) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,k2_relat_1(X1)) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k2_relat_1(X1))
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t202_relat_1)).

fof(f52,plain,
    ( v1_relat_1(sK2)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl8_4
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f98,plain,
    ( r2_hidden(sK5(sK2,sK1),k2_relat_1(sK2))
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl8_10
  <=> r2_hidden(sK5(sK2,sK1),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f105,plain,
    ( ~ spl8_11
    | spl8_8
    | ~ spl8_9 ),
    inference(avatar_split_clause,[],[f94,f87,f75,f102])).

fof(f87,plain,
    ( spl8_9
  <=> sP6(sK5(sK2,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f94,plain,
    ( ~ r2_hidden(sK5(sK2,sK1),sK1)
    | spl8_8
    | ~ spl8_9 ),
    inference(subsumption_resolution,[],[f91,f77])).

fof(f77,plain,
    ( sK1 != k2_relat_1(sK2)
    | spl8_8 ),
    inference(avatar_component_clause,[],[f75])).

fof(f91,plain,
    ( ~ r2_hidden(sK5(sK2,sK1),sK1)
    | sK1 = k2_relat_1(sK2)
    | ~ spl8_9 ),
    inference(resolution,[],[f89,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ sP6(sK5(X0,X1),X0)
      | ~ r2_hidden(sK5(X0,X1),X1)
      | k2_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f89,plain,
    ( sP6(sK5(sK2,sK1),sK2)
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f87])).

fof(f99,plain,
    ( spl8_10
    | ~ spl8_9 ),
    inference(avatar_split_clause,[],[f93,f87,f96])).

fof(f93,plain,
    ( r2_hidden(sK5(sK2,sK1),k2_relat_1(sK2))
    | ~ spl8_9 ),
    inference(resolution,[],[f89,f30])).

fof(f30,plain,(
    ! [X2,X0] :
      ( ~ sP6(X2,X0)
      | r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( ~ sP6(X2,X0)
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f90,plain,
    ( spl8_9
    | spl8_3
    | spl8_8 ),
    inference(avatar_split_clause,[],[f85,f75,f45,f87])).

fof(f45,plain,
    ( spl8_3
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f85,plain,
    ( sP6(sK5(sK2,sK1),sK2)
    | spl8_3
    | spl8_8 ),
    inference(subsumption_resolution,[],[f83,f77])).

fof(f83,plain,
    ( sP6(sK5(sK2,sK1),sK2)
    | sK1 = k2_relat_1(sK2)
    | spl8_3 ),
    inference(factoring,[],[f67])).

% (16992)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
fof(f67,plain,
    ( ! [X0] :
        ( sP6(sK5(X0,sK1),sK2)
        | sP6(sK5(X0,sK1),X0)
        | k2_relat_1(X0) = sK1 )
    | spl8_3 ),
    inference(resolution,[],[f66,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X1)
      | sP6(sK5(X0,X1),X0)
      | k2_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f66,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | sP6(X0,sK2) )
    | spl8_3 ),
    inference(resolution,[],[f60,f20])).

fof(f20,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | sP6(X2,X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f60,plain,
    ( ! [X3] :
        ( r2_hidden(k4_tarski(sK4(X3),X3),sK2)
        | ~ r2_hidden(X3,sK1) )
    | spl8_3 ),
    inference(subsumption_resolution,[],[f16,f47])).

fof(f47,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | spl8_3 ),
    inference(avatar_component_clause,[],[f45])).

fof(f16,plain,(
    ! [X3] :
      ( sK1 = k2_relset_1(sK0,sK1,sK2)
      | ~ r2_hidden(X3,sK1)
      | r2_hidden(k4_tarski(sK4(X3),X3),sK2) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f78,plain,
    ( ~ spl8_8
    | spl8_3
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f73,f69,f45,f75])).

fof(f73,plain,
    ( sK1 != k2_relat_1(sK2)
    | spl8_3
    | ~ spl8_7 ),
    inference(superposition,[],[f47,f71])).

fof(f72,plain,
    ( spl8_7
    | ~ spl8_1 ),
    inference(avatar_split_clause,[],[f38,f32,f69])).

fof(f32,plain,
    ( spl8_1
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f38,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)
    | ~ spl8_1 ),
    inference(resolution,[],[f34,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f34,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f65,plain,
    ( spl8_6
    | ~ spl8_1 ),
    inference(avatar_split_clause,[],[f37,f32,f62])).

fof(f37,plain,
    ( v5_relat_1(sK2,sK1)
    | ~ spl8_1 ),
    inference(resolution,[],[f34,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f53,plain,
    ( spl8_4
    | ~ spl8_1 ),
    inference(avatar_split_clause,[],[f39,f32,f50])).

fof(f39,plain,
    ( v1_relat_1(sK2)
    | ~ spl8_1 ),
    inference(resolution,[],[f34,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f48,plain,
    ( spl8_2
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f14,f45,f41])).

fof(f14,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | r2_hidden(sK3,sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f35,plain,(
    spl8_1 ),
    inference(avatar_split_clause,[],[f17,f32])).

fof(f17,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:29:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.42  % (16997)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.47  % (16987)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.48  % (16998)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.48  % (16986)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.49  % (16994)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  % (16996)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.49  % (16989)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.49  % (16985)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.49  % (16990)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.49  % (16995)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.49  % (16988)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.49  % (16985)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f134,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(avatar_sat_refutation,[],[f35,f48,f53,f65,f72,f78,f90,f99,f105,f113,f114,f128,f132])).
% 0.20/0.49  fof(f132,plain,(
% 0.20/0.49    ~spl8_7 | ~spl8_8 | ~spl8_12),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f131])).
% 0.20/0.49  fof(f131,plain,(
% 0.20/0.49    $false | (~spl8_7 | ~spl8_8 | ~spl8_12)),
% 0.20/0.49    inference(subsumption_resolution,[],[f129,f121])).
% 0.20/0.49  fof(f121,plain,(
% 0.20/0.49    ( ! [X4] : (~r2_hidden(k4_tarski(X4,sK3),sK2)) ) | (~spl8_7 | ~spl8_8)),
% 0.20/0.49    inference(subsumption_resolution,[],[f116,f76])).
% 0.20/0.49  fof(f76,plain,(
% 0.20/0.49    sK1 = k2_relat_1(sK2) | ~spl8_8),
% 0.20/0.49    inference(avatar_component_clause,[],[f75])).
% 0.20/0.49  fof(f75,plain,(
% 0.20/0.49    spl8_8 <=> sK1 = k2_relat_1(sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.20/0.49  fof(f116,plain,(
% 0.20/0.49    ( ! [X4] : (sK1 != k2_relat_1(sK2) | ~r2_hidden(k4_tarski(X4,sK3),sK2)) ) | ~spl8_7),
% 0.20/0.49    inference(forward_demodulation,[],[f15,f71])).
% 0.20/0.49  fof(f71,plain,(
% 0.20/0.49    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) | ~spl8_7),
% 0.20/0.49    inference(avatar_component_clause,[],[f69])).
% 0.20/0.49  fof(f69,plain,(
% 0.20/0.49    spl8_7 <=> k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ( ! [X4] : (sK1 != k2_relset_1(sK0,sK1,sK2) | ~r2_hidden(k4_tarski(X4,sK3),sK2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f8])).
% 0.20/0.49  fof(f8,plain,(
% 0.20/0.49    ? [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X4,X3),X2) | ~r2_hidden(X3,X1)) <~> k2_relset_1(X0,X1,X2) = X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(ennf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,negated_conjecture,(
% 0.20/0.49    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X4,X3),X2) & r2_hidden(X3,X1)) <=> k2_relset_1(X0,X1,X2) = X1))),
% 0.20/0.49    inference(negated_conjecture,[],[f6])).
% 0.20/0.49  fof(f6,conjecture,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X4,X3),X2) & r2_hidden(X3,X1)) <=> k2_relset_1(X0,X1,X2) = X1))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_relset_1)).
% 0.20/0.49  fof(f129,plain,(
% 0.20/0.49    r2_hidden(k4_tarski(sK7(sK2,sK3),sK3),sK2) | ~spl8_12),
% 0.20/0.49    inference(resolution,[],[f127,f19])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ( ! [X2,X0] : (~sP6(X2,X0) | r2_hidden(k4_tarski(sK7(X0,X2),X2),X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).
% 0.20/0.49  fof(f127,plain,(
% 0.20/0.49    sP6(sK3,sK2) | ~spl8_12),
% 0.20/0.49    inference(avatar_component_clause,[],[f125])).
% 0.20/0.49  fof(f125,plain,(
% 0.20/0.49    spl8_12 <=> sP6(sK3,sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 0.20/0.49  fof(f128,plain,(
% 0.20/0.49    spl8_12 | ~spl8_2 | ~spl8_8),
% 0.20/0.49    inference(avatar_split_clause,[],[f123,f75,f41,f125])).
% 0.20/0.49  fof(f41,plain,(
% 0.20/0.49    spl8_2 <=> r2_hidden(sK3,sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.20/0.49  fof(f123,plain,(
% 0.20/0.49    sP6(sK3,sK2) | (~spl8_2 | ~spl8_8)),
% 0.20/0.49    inference(resolution,[],[f120,f43])).
% 0.20/0.49  fof(f43,plain,(
% 0.20/0.49    r2_hidden(sK3,sK1) | ~spl8_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f41])).
% 0.20/0.49  fof(f120,plain,(
% 0.20/0.49    ( ! [X1] : (~r2_hidden(X1,sK1) | sP6(X1,sK2)) ) | ~spl8_8),
% 0.20/0.49    inference(superposition,[],[f29,f76])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    ( ! [X2,X0] : (~r2_hidden(X2,k2_relat_1(X0)) | sP6(X2,X0)) )),
% 0.20/0.49    inference(equality_resolution,[],[f22])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (sP6(X2,X0) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.20/0.49    inference(cnf_transformation,[],[f1])).
% 0.20/0.49  fof(f114,plain,(
% 0.20/0.49    sK1 != k2_relset_1(sK0,sK1,sK2) | k2_relset_1(sK0,sK1,sK2) != k2_relat_1(sK2) | sK1 = k2_relat_1(sK2)),
% 0.20/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.49  fof(f113,plain,(
% 0.20/0.49    ~spl8_4 | ~spl8_6 | ~spl8_10 | spl8_11),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f112])).
% 0.20/0.49  fof(f112,plain,(
% 0.20/0.49    $false | (~spl8_4 | ~spl8_6 | ~spl8_10 | spl8_11)),
% 0.20/0.49    inference(subsumption_resolution,[],[f110,f104])).
% 0.20/0.49  fof(f104,plain,(
% 0.20/0.49    ~r2_hidden(sK5(sK2,sK1),sK1) | spl8_11),
% 0.20/0.49    inference(avatar_component_clause,[],[f102])).
% 0.20/0.49  fof(f102,plain,(
% 0.20/0.49    spl8_11 <=> r2_hidden(sK5(sK2,sK1),sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 0.20/0.49  fof(f110,plain,(
% 0.20/0.49    r2_hidden(sK5(sK2,sK1),sK1) | (~spl8_4 | ~spl8_6 | ~spl8_10)),
% 0.20/0.49    inference(resolution,[],[f98,f79])).
% 0.20/0.49  fof(f79,plain,(
% 0.20/0.49    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK2)) | r2_hidden(X0,sK1)) ) | (~spl8_4 | ~spl8_6)),
% 0.20/0.49    inference(resolution,[],[f54,f64])).
% 0.20/0.49  fof(f64,plain,(
% 0.20/0.49    v5_relat_1(sK2,sK1) | ~spl8_6),
% 0.20/0.49    inference(avatar_component_clause,[],[f62])).
% 0.20/0.49  fof(f62,plain,(
% 0.20/0.49    spl8_6 <=> v5_relat_1(sK2,sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.20/0.49  fof(f54,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v5_relat_1(sK2,X0) | ~r2_hidden(X1,k2_relat_1(sK2)) | r2_hidden(X1,X0)) ) | ~spl8_4),
% 0.20/0.49    inference(resolution,[],[f52,f18])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | ~v5_relat_1(X1,X0) | ~r2_hidden(X2,k2_relat_1(X1)) | r2_hidden(X2,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f10])).
% 0.20/0.49  fof(f10,plain,(
% 0.20/0.49    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,k2_relat_1(X1))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.49    inference(flattening,[],[f9])).
% 0.20/0.49  fof(f9,plain,(
% 0.20/0.49    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,k2_relat_1(X1))) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.20/0.49    inference(ennf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k2_relat_1(X1)) => r2_hidden(X2,X0)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t202_relat_1)).
% 0.20/0.49  fof(f52,plain,(
% 0.20/0.49    v1_relat_1(sK2) | ~spl8_4),
% 0.20/0.49    inference(avatar_component_clause,[],[f50])).
% 0.20/0.49  fof(f50,plain,(
% 0.20/0.49    spl8_4 <=> v1_relat_1(sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.20/0.49  fof(f98,plain,(
% 0.20/0.49    r2_hidden(sK5(sK2,sK1),k2_relat_1(sK2)) | ~spl8_10),
% 0.20/0.49    inference(avatar_component_clause,[],[f96])).
% 0.20/0.49  fof(f96,plain,(
% 0.20/0.49    spl8_10 <=> r2_hidden(sK5(sK2,sK1),k2_relat_1(sK2))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.20/0.49  fof(f105,plain,(
% 0.20/0.49    ~spl8_11 | spl8_8 | ~spl8_9),
% 0.20/0.49    inference(avatar_split_clause,[],[f94,f87,f75,f102])).
% 0.20/0.49  fof(f87,plain,(
% 0.20/0.49    spl8_9 <=> sP6(sK5(sK2,sK1),sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.20/0.49  fof(f94,plain,(
% 0.20/0.49    ~r2_hidden(sK5(sK2,sK1),sK1) | (spl8_8 | ~spl8_9)),
% 0.20/0.49    inference(subsumption_resolution,[],[f91,f77])).
% 0.20/0.49  fof(f77,plain,(
% 0.20/0.49    sK1 != k2_relat_1(sK2) | spl8_8),
% 0.20/0.49    inference(avatar_component_clause,[],[f75])).
% 0.20/0.49  fof(f91,plain,(
% 0.20/0.49    ~r2_hidden(sK5(sK2,sK1),sK1) | sK1 = k2_relat_1(sK2) | ~spl8_9),
% 0.20/0.49    inference(resolution,[],[f89,f24])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~sP6(sK5(X0,X1),X0) | ~r2_hidden(sK5(X0,X1),X1) | k2_relat_1(X0) = X1) )),
% 0.20/0.49    inference(cnf_transformation,[],[f1])).
% 0.20/0.49  fof(f89,plain,(
% 0.20/0.49    sP6(sK5(sK2,sK1),sK2) | ~spl8_9),
% 0.20/0.49    inference(avatar_component_clause,[],[f87])).
% 0.20/0.49  fof(f99,plain,(
% 0.20/0.49    spl8_10 | ~spl8_9),
% 0.20/0.49    inference(avatar_split_clause,[],[f93,f87,f96])).
% 0.20/0.49  fof(f93,plain,(
% 0.20/0.49    r2_hidden(sK5(sK2,sK1),k2_relat_1(sK2)) | ~spl8_9),
% 0.20/0.49    inference(resolution,[],[f89,f30])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    ( ! [X2,X0] : (~sP6(X2,X0) | r2_hidden(X2,k2_relat_1(X0))) )),
% 0.20/0.49    inference(equality_resolution,[],[f21])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~sP6(X2,X0) | r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.20/0.49    inference(cnf_transformation,[],[f1])).
% 0.20/0.49  fof(f90,plain,(
% 0.20/0.49    spl8_9 | spl8_3 | spl8_8),
% 0.20/0.49    inference(avatar_split_clause,[],[f85,f75,f45,f87])).
% 0.20/0.49  fof(f45,plain,(
% 0.20/0.49    spl8_3 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.20/0.49  fof(f85,plain,(
% 0.20/0.49    sP6(sK5(sK2,sK1),sK2) | (spl8_3 | spl8_8)),
% 0.20/0.49    inference(subsumption_resolution,[],[f83,f77])).
% 0.20/0.49  fof(f83,plain,(
% 0.20/0.49    sP6(sK5(sK2,sK1),sK2) | sK1 = k2_relat_1(sK2) | spl8_3),
% 0.20/0.49    inference(factoring,[],[f67])).
% 0.20/0.49  % (16992)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.49  fof(f67,plain,(
% 0.20/0.49    ( ! [X0] : (sP6(sK5(X0,sK1),sK2) | sP6(sK5(X0,sK1),X0) | k2_relat_1(X0) = sK1) ) | spl8_3),
% 0.20/0.49    inference(resolution,[],[f66,f23])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X1) | sP6(sK5(X0,X1),X0) | k2_relat_1(X0) = X1) )),
% 0.20/0.49    inference(cnf_transformation,[],[f1])).
% 0.20/0.49  fof(f66,plain,(
% 0.20/0.49    ( ! [X0] : (~r2_hidden(X0,sK1) | sP6(X0,sK2)) ) | spl8_3),
% 0.20/0.49    inference(resolution,[],[f60,f20])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ( ! [X2,X0,X3] : (~r2_hidden(k4_tarski(X3,X2),X0) | sP6(X2,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f1])).
% 0.20/0.49  fof(f60,plain,(
% 0.20/0.49    ( ! [X3] : (r2_hidden(k4_tarski(sK4(X3),X3),sK2) | ~r2_hidden(X3,sK1)) ) | spl8_3),
% 0.20/0.49    inference(subsumption_resolution,[],[f16,f47])).
% 0.20/0.49  fof(f47,plain,(
% 0.20/0.49    sK1 != k2_relset_1(sK0,sK1,sK2) | spl8_3),
% 0.20/0.49    inference(avatar_component_clause,[],[f45])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ( ! [X3] : (sK1 = k2_relset_1(sK0,sK1,sK2) | ~r2_hidden(X3,sK1) | r2_hidden(k4_tarski(sK4(X3),X3),sK2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f8])).
% 0.20/0.49  fof(f78,plain,(
% 0.20/0.49    ~spl8_8 | spl8_3 | ~spl8_7),
% 0.20/0.49    inference(avatar_split_clause,[],[f73,f69,f45,f75])).
% 0.20/0.49  fof(f73,plain,(
% 0.20/0.49    sK1 != k2_relat_1(sK2) | (spl8_3 | ~spl8_7)),
% 0.20/0.49    inference(superposition,[],[f47,f71])).
% 0.20/0.49  fof(f72,plain,(
% 0.20/0.49    spl8_7 | ~spl8_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f38,f32,f69])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    spl8_1 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) | ~spl8_1),
% 0.20/0.49    inference(resolution,[],[f34,f26])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f12])).
% 0.20/0.49  fof(f12,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(ennf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl8_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f32])).
% 0.20/0.49  fof(f65,plain,(
% 0.20/0.49    spl8_6 | ~spl8_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f37,f32,f62])).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    v5_relat_1(sK2,sK1) | ~spl8_1),
% 0.20/0.49    inference(resolution,[],[f34,f28])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f13])).
% 0.20/0.49  fof(f13,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(ennf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.49  fof(f53,plain,(
% 0.20/0.49    spl8_4 | ~spl8_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f39,f32,f50])).
% 0.20/0.49  fof(f39,plain,(
% 0.20/0.49    v1_relat_1(sK2) | ~spl8_1),
% 0.20/0.49    inference(resolution,[],[f34,f25])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f11])).
% 0.20/0.49  fof(f11,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(ennf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.49  fof(f48,plain,(
% 0.20/0.49    spl8_2 | ~spl8_3),
% 0.20/0.49    inference(avatar_split_clause,[],[f14,f45,f41])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    sK1 != k2_relset_1(sK0,sK1,sK2) | r2_hidden(sK3,sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f8])).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    spl8_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f17,f32])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.49    inference(cnf_transformation,[],[f8])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (16985)------------------------------
% 0.20/0.49  % (16985)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (16985)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (16985)Memory used [KB]: 10618
% 0.20/0.49  % (16985)Time elapsed: 0.085 s
% 0.20/0.49  % (16985)------------------------------
% 0.20/0.49  % (16985)------------------------------
% 0.20/0.49  % (16982)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.49  % (16983)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (16981)Success in time 0.14 s
%------------------------------------------------------------------------------
