%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:04 EST 2020

% Result     : Theorem 1.03s
% Output     : Refutation 1.03s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 356 expanded)
%              Number of leaves         :   15 (  95 expanded)
%              Depth                    :   16
%              Number of atoms          :  228 (1015 expanded)
%              Number of equality atoms :   60 ( 200 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f287,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f87,f92,f149,f156,f286])).

% (11304)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
fof(f286,plain,
    ( spl4_2
    | ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f282])).

fof(f282,plain,
    ( $false
    | spl4_2
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f41,f272,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f272,plain,
    ( r2_hidden(sK2,o_0_0_xboole_0)
    | spl4_2
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f207,f269])).

fof(f269,plain,
    ( o_0_0_xboole_0 = k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)
    | spl4_2
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f225,f268])).

fof(f268,plain,
    ( o_0_0_xboole_0 = k1_relat_1(sK2)
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f212,f257])).

fof(f257,plain,
    ( o_0_0_xboole_0 = k1_relset_1(o_0_0_xboole_0,o_0_0_xboole_0,sK2)
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f208,f209,f55])).

fof(f55,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,X1)))
      | o_0_0_xboole_0 = k1_relset_1(o_0_0_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,o_0_0_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | o_0_0_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(definition_unfolding,[],[f45,f48])).

fof(f48,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_xboole_0)).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f209,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f159,f198])).

fof(f198,plain,
    ( o_0_0_xboole_0 = sK0
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f41,f173,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | X0 = X1
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

fof(f173,plain,
    ( v1_xboole_0(sK0)
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f41,f160,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | v1_xboole_0(X0)
      | v1_xboole_0(k1_funct_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k1_funct_2(X0,X1))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k1_funct_2(X0,X1))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => v1_xboole_0(k1_funct_2(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_2)).

fof(f160,plain,
    ( ~ v1_xboole_0(k1_funct_2(sK0,o_0_0_xboole_0))
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f65,f148])).

fof(f148,plain,
    ( o_0_0_xboole_0 = sK1
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f146])).

% (11279)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% (11287)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
fof(f146,plain,
    ( spl4_4
  <=> o_0_0_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f65,plain,(
    ~ v1_xboole_0(k1_funct_2(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f28,f37])).

fof(f28,plain,(
    r2_hidden(sK2,k1_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_tarski(k2_relat_1(X2),X1)
        | k1_relat_1(X2) != X0 )
      & r2_hidden(X2,k1_funct_2(X0,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_tarski(k2_relat_1(X2),X1)
        | k1_relat_1(X2) != X0 )
      & r2_hidden(X2,k1_funct_2(X0,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(X2,k1_funct_2(X0,X1))
         => ( r1_tarski(k2_relat_1(X2),X1)
            & k1_relat_1(X2) = X0 ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X2,k1_funct_2(X0,X1))
       => ( r1_tarski(k2_relat_1(X2),X1)
          & k1_relat_1(X2) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_funct_2)).

fof(f159,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,o_0_0_xboole_0)))
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f64,f148])).

fof(f64,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f28,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_funct_2(X0,X1))
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
     => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_2)).

fof(f208,plain,
    ( v1_funct_2(sK2,o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f158,f198])).

fof(f158,plain,
    ( v1_funct_2(sK2,sK0,o_0_0_xboole_0)
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f63,f148])).

fof(f63,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f28,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_funct_2(X0,X1))
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f212,plain,
    ( k1_relat_1(sK2) = k1_relset_1(o_0_0_xboole_0,o_0_0_xboole_0,sK2)
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f163,f198])).

fof(f163,plain,
    ( k1_relat_1(sK2) = k1_relset_1(sK0,o_0_0_xboole_0,sK2)
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f72,f148])).

fof(f72,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f64,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f225,plain,
    ( o_0_0_xboole_0 = k1_funct_2(k1_relat_1(sK2),o_0_0_xboole_0)
    | spl4_2
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f200,f116])).

fof(f116,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | o_0_0_xboole_0 = k1_funct_2(X0,o_0_0_xboole_0) ) ),
    inference(resolution,[],[f107,f109])).

fof(f109,plain,(
    ! [X2] :
      ( ~ v1_xboole_0(X2)
      | o_0_0_xboole_0 = X2 ) ),
    inference(forward_demodulation,[],[f102,f98])).

fof(f98,plain,(
    o_0_0_xboole_0 = k1_funct_2(k1_funct_2(sK0,sK1),o_0_0_xboole_0) ),
    inference(unit_resulting_resolution,[],[f41,f68,f31])).

fof(f68,plain,(
    v1_xboole_0(k1_funct_2(k1_funct_2(sK0,sK1),o_0_0_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f41,f65,f38])).

fof(f102,plain,(
    ! [X2] :
      ( k1_funct_2(k1_funct_2(sK0,sK1),o_0_0_xboole_0) = X2
      | ~ v1_xboole_0(X2) ) ),
    inference(resolution,[],[f68,f31])).

fof(f107,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_funct_2(X0,o_0_0_xboole_0))
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f100,f98])).

fof(f100,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | v1_xboole_0(k1_funct_2(X0,k1_funct_2(k1_funct_2(sK0,sK1),o_0_0_xboole_0))) ) ),
    inference(resolution,[],[f68,f38])).

fof(f200,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK2))
    | spl4_2
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f86,f173,f31])).

fof(f86,plain,
    ( sK0 != k1_relat_1(sK2)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl4_2
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f207,plain,
    ( r2_hidden(sK2,k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f157,f198])).

fof(f157,plain,
    ( r2_hidden(sK2,k1_funct_2(sK0,o_0_0_xboole_0))
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f28,f148])).

fof(f41,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(f156,plain,(
    spl4_3 ),
    inference(avatar_contradiction_clause,[],[f152])).

fof(f152,plain,
    ( $false
    | spl4_3 ),
    inference(unit_resulting_resolution,[],[f28,f144,f34])).

fof(f144,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl4_3
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f149,plain,
    ( ~ spl4_3
    | spl4_4
    | spl4_2 ),
    inference(avatar_split_clause,[],[f78,f84,f146,f142])).

fof(f78,plain,
    ( sK0 = k1_relat_1(sK2)
    | o_0_0_xboole_0 = sK1
    | ~ v1_funct_2(sK2,sK0,sK1) ),
    inference(forward_demodulation,[],[f74,f72])).

fof(f74,plain,
    ( o_0_0_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ v1_funct_2(sK2,sK0,sK1) ),
    inference(resolution,[],[f64,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | o_0_0_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(definition_unfolding,[],[f47,f48])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f92,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f91])).

fof(f91,plain,
    ( $false
    | spl4_1 ),
    inference(unit_resulting_resolution,[],[f26,f71,f82,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f82,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl4_1
  <=> r1_tarski(k2_relat_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f71,plain,(
    v5_relat_1(sK2,sK1) ),
    inference(unit_resulting_resolution,[],[f64,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f26,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f87,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f25,f84,f80])).

fof(f25,plain,
    ( sK0 != k1_relat_1(sK2)
    | ~ r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:25:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.37  ipcrm: permission denied for id (794230786)
% 0.13/0.38  ipcrm: permission denied for id (794263555)
% 0.13/0.38  ipcrm: permission denied for id (794296324)
% 0.13/0.38  ipcrm: permission denied for id (794329093)
% 0.13/0.38  ipcrm: permission denied for id (794361862)
% 0.13/0.38  ipcrm: permission denied for id (794492938)
% 0.13/0.39  ipcrm: permission denied for id (794558476)
% 0.13/0.39  ipcrm: permission denied for id (794624014)
% 0.13/0.39  ipcrm: permission denied for id (794656783)
% 0.13/0.39  ipcrm: permission denied for id (794722321)
% 0.13/0.39  ipcrm: permission denied for id (794755090)
% 0.13/0.40  ipcrm: permission denied for id (794853397)
% 0.13/0.40  ipcrm: permission denied for id (794886167)
% 0.13/0.40  ipcrm: permission denied for id (794984474)
% 0.13/0.41  ipcrm: permission denied for id (795017243)
% 0.21/0.41  ipcrm: permission denied for id (795181088)
% 0.21/0.41  ipcrm: permission denied for id (795213857)
% 0.21/0.41  ipcrm: permission denied for id (795246626)
% 0.21/0.42  ipcrm: permission denied for id (795312164)
% 0.21/0.42  ipcrm: permission denied for id (795508778)
% 0.21/0.43  ipcrm: permission denied for id (795541547)
% 0.21/0.43  ipcrm: permission denied for id (795574316)
% 0.21/0.43  ipcrm: permission denied for id (795607085)
% 0.21/0.43  ipcrm: permission denied for id (795639854)
% 0.21/0.43  ipcrm: permission denied for id (795672623)
% 0.21/0.44  ipcrm: permission denied for id (795803699)
% 0.21/0.44  ipcrm: permission denied for id (795836468)
% 0.21/0.44  ipcrm: permission denied for id (795869237)
% 0.21/0.44  ipcrm: permission denied for id (796033082)
% 0.21/0.45  ipcrm: permission denied for id (796098620)
% 0.21/0.45  ipcrm: permission denied for id (796131389)
% 0.21/0.45  ipcrm: permission denied for id (796164158)
% 0.21/0.45  ipcrm: permission denied for id (796196927)
% 0.21/0.45  ipcrm: permission denied for id (796229696)
% 0.21/0.45  ipcrm: permission denied for id (796262465)
% 0.21/0.46  ipcrm: permission denied for id (796295234)
% 0.21/0.46  ipcrm: permission denied for id (796360772)
% 0.21/0.46  ipcrm: permission denied for id (796393541)
% 0.21/0.46  ipcrm: permission denied for id (796557385)
% 0.21/0.47  ipcrm: permission denied for id (796590154)
% 0.21/0.47  ipcrm: permission denied for id (796655692)
% 0.21/0.47  ipcrm: permission denied for id (796721230)
% 0.21/0.47  ipcrm: permission denied for id (796753999)
% 0.21/0.47  ipcrm: permission denied for id (796819537)
% 0.21/0.48  ipcrm: permission denied for id (796852306)
% 0.21/0.48  ipcrm: permission denied for id (796885075)
% 0.21/0.48  ipcrm: permission denied for id (797048920)
% 0.21/0.49  ipcrm: permission denied for id (797147227)
% 0.21/0.49  ipcrm: permission denied for id (797179996)
% 0.21/0.49  ipcrm: permission denied for id (797245534)
% 0.21/0.49  ipcrm: permission denied for id (797311072)
% 0.21/0.50  ipcrm: permission denied for id (797343841)
% 0.21/0.50  ipcrm: permission denied for id (797409380)
% 0.21/0.51  ipcrm: permission denied for id (797605994)
% 0.21/0.51  ipcrm: permission denied for id (797638763)
% 0.21/0.51  ipcrm: permission denied for id (797671532)
% 0.21/0.51  ipcrm: permission denied for id (797704301)
% 0.21/0.51  ipcrm: permission denied for id (797737070)
% 0.21/0.51  ipcrm: permission denied for id (797769839)
% 0.21/0.52  ipcrm: permission denied for id (797835377)
% 0.21/0.52  ipcrm: permission denied for id (797868146)
% 0.21/0.52  ipcrm: permission denied for id (797933684)
% 0.21/0.52  ipcrm: permission denied for id (797966453)
% 0.21/0.52  ipcrm: permission denied for id (797999222)
% 0.21/0.52  ipcrm: permission denied for id (798031991)
% 0.21/0.53  ipcrm: permission denied for id (798097529)
% 0.21/0.53  ipcrm: permission denied for id (798195836)
% 0.21/0.53  ipcrm: permission denied for id (798294143)
% 1.03/0.66  % (11280)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.03/0.68  % (11288)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.03/0.68  % (11280)Refutation found. Thanks to Tanya!
% 1.03/0.68  % SZS status Theorem for theBenchmark
% 1.03/0.68  % (11295)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.03/0.68  % SZS output start Proof for theBenchmark
% 1.03/0.68  fof(f287,plain,(
% 1.03/0.68    $false),
% 1.03/0.68    inference(avatar_sat_refutation,[],[f87,f92,f149,f156,f286])).
% 1.03/0.68  % (11304)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.03/0.68  fof(f286,plain,(
% 1.03/0.68    spl4_2 | ~spl4_4),
% 1.03/0.68    inference(avatar_contradiction_clause,[],[f282])).
% 1.03/0.68  fof(f282,plain,(
% 1.03/0.68    $false | (spl4_2 | ~spl4_4)),
% 1.03/0.68    inference(unit_resulting_resolution,[],[f41,f272,f37])).
% 1.03/0.68  fof(f37,plain,(
% 1.03/0.68    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~r2_hidden(X1,X0)) )),
% 1.03/0.68    inference(cnf_transformation,[],[f1])).
% 1.03/0.68  fof(f1,axiom,(
% 1.03/0.68    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.03/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.03/0.68  fof(f272,plain,(
% 1.03/0.68    r2_hidden(sK2,o_0_0_xboole_0) | (spl4_2 | ~spl4_4)),
% 1.03/0.68    inference(backward_demodulation,[],[f207,f269])).
% 1.03/0.68  fof(f269,plain,(
% 1.03/0.68    o_0_0_xboole_0 = k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0) | (spl4_2 | ~spl4_4)),
% 1.03/0.68    inference(backward_demodulation,[],[f225,f268])).
% 1.03/0.68  fof(f268,plain,(
% 1.03/0.68    o_0_0_xboole_0 = k1_relat_1(sK2) | ~spl4_4),
% 1.03/0.68    inference(backward_demodulation,[],[f212,f257])).
% 1.03/0.68  fof(f257,plain,(
% 1.03/0.68    o_0_0_xboole_0 = k1_relset_1(o_0_0_xboole_0,o_0_0_xboole_0,sK2) | ~spl4_4),
% 1.03/0.68    inference(unit_resulting_resolution,[],[f208,f209,f55])).
% 1.03/0.68  fof(f55,plain,(
% 1.03/0.68    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,X1))) | o_0_0_xboole_0 = k1_relset_1(o_0_0_xboole_0,X1,X2) | ~v1_funct_2(X2,o_0_0_xboole_0,X1)) )),
% 1.03/0.68    inference(equality_resolution,[],[f51])).
% 1.03/0.68  fof(f51,plain,(
% 1.03/0.68    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | o_0_0_xboole_0 != X0 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 1.03/0.68    inference(definition_unfolding,[],[f45,f48])).
% 1.03/0.68  fof(f48,plain,(
% 1.03/0.68    k1_xboole_0 = o_0_0_xboole_0),
% 1.03/0.68    inference(cnf_transformation,[],[f2])).
% 1.03/0.68  fof(f2,axiom,(
% 1.03/0.68    k1_xboole_0 = o_0_0_xboole_0),
% 1.03/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_xboole_0)).
% 1.03/0.68  fof(f45,plain,(
% 1.03/0.68    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 1.03/0.68    inference(cnf_transformation,[],[f24])).
% 1.03/0.68  fof(f24,plain,(
% 1.03/0.68    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.03/0.68    inference(flattening,[],[f23])).
% 1.03/0.68  fof(f23,plain,(
% 1.03/0.68    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.03/0.68    inference(ennf_transformation,[],[f8])).
% 1.03/0.68  fof(f8,axiom,(
% 1.03/0.68    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.03/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.03/0.68  fof(f209,plain,(
% 1.03/0.68    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))) | ~spl4_4),
% 1.03/0.68    inference(backward_demodulation,[],[f159,f198])).
% 1.03/0.68  fof(f198,plain,(
% 1.03/0.68    o_0_0_xboole_0 = sK0 | ~spl4_4),
% 1.03/0.68    inference(unit_resulting_resolution,[],[f41,f173,f31])).
% 1.03/0.68  fof(f31,plain,(
% 1.03/0.68    ( ! [X0,X1] : (~v1_xboole_0(X0) | X0 = X1 | ~v1_xboole_0(X1)) )),
% 1.03/0.68    inference(cnf_transformation,[],[f17])).
% 1.03/0.68  fof(f17,plain,(
% 1.03/0.68    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 1.03/0.68    inference(ennf_transformation,[],[f4])).
% 1.03/0.68  fof(f4,axiom,(
% 1.03/0.68    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 1.03/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).
% 1.03/0.68  fof(f173,plain,(
% 1.03/0.68    v1_xboole_0(sK0) | ~spl4_4),
% 1.03/0.68    inference(unit_resulting_resolution,[],[f41,f160,f38])).
% 1.03/0.68  fof(f38,plain,(
% 1.03/0.68    ( ! [X0,X1] : (~v1_xboole_0(X1) | v1_xboole_0(X0) | v1_xboole_0(k1_funct_2(X0,X1))) )),
% 1.03/0.68    inference(cnf_transformation,[],[f21])).
% 1.03/0.68  fof(f21,plain,(
% 1.03/0.68    ! [X0,X1] : (v1_xboole_0(k1_funct_2(X0,X1)) | ~v1_xboole_0(X1) | v1_xboole_0(X0))),
% 1.03/0.68    inference(flattening,[],[f20])).
% 1.03/0.68  fof(f20,plain,(
% 1.03/0.68    ! [X0,X1] : (v1_xboole_0(k1_funct_2(X0,X1)) | (~v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 1.03/0.68    inference(ennf_transformation,[],[f9])).
% 1.03/0.68  fof(f9,axiom,(
% 1.03/0.68    ! [X0,X1] : ((v1_xboole_0(X1) & ~v1_xboole_0(X0)) => v1_xboole_0(k1_funct_2(X0,X1)))),
% 1.03/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_2)).
% 1.03/0.68  fof(f160,plain,(
% 1.03/0.68    ~v1_xboole_0(k1_funct_2(sK0,o_0_0_xboole_0)) | ~spl4_4),
% 1.03/0.68    inference(backward_demodulation,[],[f65,f148])).
% 1.03/0.68  fof(f148,plain,(
% 1.03/0.68    o_0_0_xboole_0 = sK1 | ~spl4_4),
% 1.03/0.68    inference(avatar_component_clause,[],[f146])).
% 1.03/0.68  % (11279)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.03/0.69  % (11287)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.03/0.69  fof(f146,plain,(
% 1.03/0.69    spl4_4 <=> o_0_0_xboole_0 = sK1),
% 1.03/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.03/0.69  fof(f65,plain,(
% 1.03/0.69    ~v1_xboole_0(k1_funct_2(sK0,sK1))),
% 1.03/0.69    inference(unit_resulting_resolution,[],[f28,f37])).
% 1.03/0.69  fof(f28,plain,(
% 1.03/0.69    r2_hidden(sK2,k1_funct_2(sK0,sK1))),
% 1.03/0.69    inference(cnf_transformation,[],[f15])).
% 1.03/0.69  fof(f15,plain,(
% 1.03/0.69    ? [X0,X1,X2] : ((~r1_tarski(k2_relat_1(X2),X1) | k1_relat_1(X2) != X0) & r2_hidden(X2,k1_funct_2(X0,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.03/0.69    inference(flattening,[],[f14])).
% 1.03/0.69  fof(f14,plain,(
% 1.03/0.69    ? [X0,X1,X2] : (((~r1_tarski(k2_relat_1(X2),X1) | k1_relat_1(X2) != X0) & r2_hidden(X2,k1_funct_2(X0,X1))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 1.03/0.69    inference(ennf_transformation,[],[f13])).
% 1.03/0.69  fof(f13,negated_conjecture,(
% 1.03/0.69    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X2,k1_funct_2(X0,X1)) => (r1_tarski(k2_relat_1(X2),X1) & k1_relat_1(X2) = X0)))),
% 1.03/0.69    inference(negated_conjecture,[],[f12])).
% 1.03/0.69  fof(f12,conjecture,(
% 1.03/0.69    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X2,k1_funct_2(X0,X1)) => (r1_tarski(k2_relat_1(X2),X1) & k1_relat_1(X2) = X0)))),
% 1.03/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_funct_2)).
% 1.03/0.69  fof(f159,plain,(
% 1.03/0.69    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,o_0_0_xboole_0))) | ~spl4_4),
% 1.03/0.69    inference(backward_demodulation,[],[f64,f148])).
% 1.03/0.69  fof(f64,plain,(
% 1.03/0.69    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.03/0.69    inference(unit_resulting_resolution,[],[f28,f35])).
% 1.03/0.69  fof(f35,plain,(
% 1.03/0.69    ( ! [X2,X0,X1] : (~r2_hidden(X2,k1_funct_2(X0,X1)) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.03/0.69    inference(cnf_transformation,[],[f19])).
% 1.03/0.69  fof(f19,plain,(
% 1.03/0.69    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~r2_hidden(X2,k1_funct_2(X0,X1)))),
% 1.03/0.69    inference(ennf_transformation,[],[f10])).
% 1.03/0.69  fof(f10,axiom,(
% 1.03/0.69    ! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.03/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_2)).
% 1.03/0.69  fof(f208,plain,(
% 1.03/0.69    v1_funct_2(sK2,o_0_0_xboole_0,o_0_0_xboole_0) | ~spl4_4),
% 1.03/0.69    inference(backward_demodulation,[],[f158,f198])).
% 1.03/0.69  fof(f158,plain,(
% 1.03/0.69    v1_funct_2(sK2,sK0,o_0_0_xboole_0) | ~spl4_4),
% 1.03/0.69    inference(backward_demodulation,[],[f63,f148])).
% 1.03/0.69  fof(f63,plain,(
% 1.03/0.69    v1_funct_2(sK2,sK0,sK1)),
% 1.03/0.69    inference(unit_resulting_resolution,[],[f28,f34])).
% 1.03/0.69  fof(f34,plain,(
% 1.03/0.69    ( ! [X2,X0,X1] : (~r2_hidden(X2,k1_funct_2(X0,X1)) | v1_funct_2(X2,X0,X1)) )),
% 1.03/0.69    inference(cnf_transformation,[],[f19])).
% 1.03/0.69  fof(f212,plain,(
% 1.03/0.69    k1_relat_1(sK2) = k1_relset_1(o_0_0_xboole_0,o_0_0_xboole_0,sK2) | ~spl4_4),
% 1.03/0.69    inference(backward_demodulation,[],[f163,f198])).
% 1.03/0.69  fof(f163,plain,(
% 1.03/0.69    k1_relat_1(sK2) = k1_relset_1(sK0,o_0_0_xboole_0,sK2) | ~spl4_4),
% 1.03/0.69    inference(backward_demodulation,[],[f72,f148])).
% 1.03/0.69  fof(f72,plain,(
% 1.03/0.69    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)),
% 1.03/0.69    inference(unit_resulting_resolution,[],[f64,f32])).
% 1.03/0.69  fof(f32,plain,(
% 1.03/0.69    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.03/0.69    inference(cnf_transformation,[],[f18])).
% 1.03/0.69  fof(f18,plain,(
% 1.03/0.69    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.03/0.69    inference(ennf_transformation,[],[f7])).
% 1.03/0.69  fof(f7,axiom,(
% 1.03/0.69    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.03/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.03/0.69  fof(f225,plain,(
% 1.03/0.69    o_0_0_xboole_0 = k1_funct_2(k1_relat_1(sK2),o_0_0_xboole_0) | (spl4_2 | ~spl4_4)),
% 1.03/0.69    inference(unit_resulting_resolution,[],[f200,f116])).
% 1.03/0.69  fof(f116,plain,(
% 1.03/0.69    ( ! [X0] : (v1_xboole_0(X0) | o_0_0_xboole_0 = k1_funct_2(X0,o_0_0_xboole_0)) )),
% 1.03/0.69    inference(resolution,[],[f107,f109])).
% 1.03/0.69  fof(f109,plain,(
% 1.03/0.69    ( ! [X2] : (~v1_xboole_0(X2) | o_0_0_xboole_0 = X2) )),
% 1.03/0.69    inference(forward_demodulation,[],[f102,f98])).
% 1.03/0.69  fof(f98,plain,(
% 1.03/0.69    o_0_0_xboole_0 = k1_funct_2(k1_funct_2(sK0,sK1),o_0_0_xboole_0)),
% 1.03/0.69    inference(unit_resulting_resolution,[],[f41,f68,f31])).
% 1.03/0.69  fof(f68,plain,(
% 1.03/0.69    v1_xboole_0(k1_funct_2(k1_funct_2(sK0,sK1),o_0_0_xboole_0))),
% 1.03/0.69    inference(unit_resulting_resolution,[],[f41,f65,f38])).
% 1.03/0.69  fof(f102,plain,(
% 1.03/0.69    ( ! [X2] : (k1_funct_2(k1_funct_2(sK0,sK1),o_0_0_xboole_0) = X2 | ~v1_xboole_0(X2)) )),
% 1.03/0.69    inference(resolution,[],[f68,f31])).
% 1.03/0.69  fof(f107,plain,(
% 1.03/0.69    ( ! [X0] : (v1_xboole_0(k1_funct_2(X0,o_0_0_xboole_0)) | v1_xboole_0(X0)) )),
% 1.03/0.69    inference(forward_demodulation,[],[f100,f98])).
% 1.03/0.69  fof(f100,plain,(
% 1.03/0.69    ( ! [X0] : (v1_xboole_0(X0) | v1_xboole_0(k1_funct_2(X0,k1_funct_2(k1_funct_2(sK0,sK1),o_0_0_xboole_0)))) )),
% 1.03/0.69    inference(resolution,[],[f68,f38])).
% 1.03/0.69  fof(f200,plain,(
% 1.03/0.69    ~v1_xboole_0(k1_relat_1(sK2)) | (spl4_2 | ~spl4_4)),
% 1.03/0.69    inference(unit_resulting_resolution,[],[f86,f173,f31])).
% 1.03/0.69  fof(f86,plain,(
% 1.03/0.69    sK0 != k1_relat_1(sK2) | spl4_2),
% 1.03/0.69    inference(avatar_component_clause,[],[f84])).
% 1.03/0.69  fof(f84,plain,(
% 1.03/0.69    spl4_2 <=> sK0 = k1_relat_1(sK2)),
% 1.03/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.03/0.69  fof(f207,plain,(
% 1.03/0.69    r2_hidden(sK2,k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)) | ~spl4_4),
% 1.03/0.69    inference(backward_demodulation,[],[f157,f198])).
% 1.03/0.69  fof(f157,plain,(
% 1.03/0.69    r2_hidden(sK2,k1_funct_2(sK0,o_0_0_xboole_0)) | ~spl4_4),
% 1.03/0.69    inference(backward_demodulation,[],[f28,f148])).
% 1.03/0.69  fof(f41,plain,(
% 1.03/0.69    v1_xboole_0(o_0_0_xboole_0)),
% 1.03/0.69    inference(cnf_transformation,[],[f3])).
% 1.03/0.69  fof(f3,axiom,(
% 1.03/0.69    v1_xboole_0(o_0_0_xboole_0)),
% 1.03/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).
% 1.03/0.69  fof(f156,plain,(
% 1.03/0.69    spl4_3),
% 1.03/0.69    inference(avatar_contradiction_clause,[],[f152])).
% 1.03/0.69  fof(f152,plain,(
% 1.03/0.69    $false | spl4_3),
% 1.03/0.69    inference(unit_resulting_resolution,[],[f28,f144,f34])).
% 1.03/0.69  fof(f144,plain,(
% 1.03/0.69    ~v1_funct_2(sK2,sK0,sK1) | spl4_3),
% 1.03/0.69    inference(avatar_component_clause,[],[f142])).
% 1.03/0.69  fof(f142,plain,(
% 1.03/0.69    spl4_3 <=> v1_funct_2(sK2,sK0,sK1)),
% 1.03/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.03/0.69  fof(f149,plain,(
% 1.03/0.69    ~spl4_3 | spl4_4 | spl4_2),
% 1.03/0.69    inference(avatar_split_clause,[],[f78,f84,f146,f142])).
% 1.03/0.69  fof(f78,plain,(
% 1.03/0.69    sK0 = k1_relat_1(sK2) | o_0_0_xboole_0 = sK1 | ~v1_funct_2(sK2,sK0,sK1)),
% 1.03/0.69    inference(forward_demodulation,[],[f74,f72])).
% 1.03/0.69  fof(f74,plain,(
% 1.03/0.69    o_0_0_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~v1_funct_2(sK2,sK0,sK1)),
% 1.03/0.69    inference(resolution,[],[f64,f49])).
% 1.03/0.69  fof(f49,plain,(
% 1.03/0.69    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | o_0_0_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 1.03/0.69    inference(definition_unfolding,[],[f47,f48])).
% 1.03/0.69  fof(f47,plain,(
% 1.03/0.69    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 1.03/0.69    inference(cnf_transformation,[],[f24])).
% 1.03/0.69  fof(f92,plain,(
% 1.03/0.69    spl4_1),
% 1.03/0.69    inference(avatar_contradiction_clause,[],[f91])).
% 1.03/0.69  fof(f91,plain,(
% 1.03/0.69    $false | spl4_1),
% 1.03/0.69    inference(unit_resulting_resolution,[],[f26,f71,f82,f30])).
% 1.03/0.69  fof(f30,plain,(
% 1.03/0.69    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0)) )),
% 1.03/0.69    inference(cnf_transformation,[],[f16])).
% 1.03/0.69  fof(f16,plain,(
% 1.03/0.69    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.03/0.69    inference(ennf_transformation,[],[f5])).
% 1.03/0.69  fof(f5,axiom,(
% 1.03/0.69    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.03/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 1.03/0.69  fof(f82,plain,(
% 1.03/0.69    ~r1_tarski(k2_relat_1(sK2),sK1) | spl4_1),
% 1.03/0.69    inference(avatar_component_clause,[],[f80])).
% 1.03/0.69  fof(f80,plain,(
% 1.03/0.69    spl4_1 <=> r1_tarski(k2_relat_1(sK2),sK1)),
% 1.03/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.03/0.69  fof(f71,plain,(
% 1.03/0.69    v5_relat_1(sK2,sK1)),
% 1.03/0.69    inference(unit_resulting_resolution,[],[f64,f40])).
% 1.03/0.69  fof(f40,plain,(
% 1.03/0.69    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.03/0.69    inference(cnf_transformation,[],[f22])).
% 1.03/0.69  fof(f22,plain,(
% 1.03/0.69    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.03/0.69    inference(ennf_transformation,[],[f6])).
% 1.03/0.69  fof(f6,axiom,(
% 1.03/0.69    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.03/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.03/0.69  fof(f26,plain,(
% 1.03/0.69    v1_relat_1(sK2)),
% 1.03/0.69    inference(cnf_transformation,[],[f15])).
% 1.03/0.69  fof(f87,plain,(
% 1.03/0.69    ~spl4_1 | ~spl4_2),
% 1.03/0.69    inference(avatar_split_clause,[],[f25,f84,f80])).
% 1.03/0.69  fof(f25,plain,(
% 1.03/0.69    sK0 != k1_relat_1(sK2) | ~r1_tarski(k2_relat_1(sK2),sK1)),
% 1.03/0.69    inference(cnf_transformation,[],[f15])).
% 1.03/0.69  % SZS output end Proof for theBenchmark
% 1.03/0.69  % (11280)------------------------------
% 1.03/0.69  % (11280)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.03/0.69  % (11280)Termination reason: Refutation
% 1.03/0.69  
% 1.03/0.69  % (11280)Memory used [KB]: 6268
% 1.03/0.69  % (11280)Time elapsed: 0.108 s
% 1.03/0.69  % (11280)------------------------------
% 1.03/0.69  % (11280)------------------------------
% 1.03/0.70  % (11046)Success in time 0.329 s
%------------------------------------------------------------------------------
