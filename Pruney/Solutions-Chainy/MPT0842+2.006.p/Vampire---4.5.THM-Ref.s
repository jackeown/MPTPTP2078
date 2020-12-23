%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:57 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 191 expanded)
%              Number of leaves         :   24 (  83 expanded)
%              Depth                    :    7
%              Number of atoms          :  294 ( 548 expanded)
%              Number of equality atoms :   11 (  17 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (7916)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f238,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f62,f74,f79,f84,f101,f109,f113,f145,f157,f170,f185,f187,f206,f218,f230,f237])).

% (7906)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
fof(f237,plain,
    ( spl10_23
    | ~ spl10_26 ),
    inference(avatar_contradiction_clause,[],[f236])).

fof(f236,plain,
    ( $false
    | spl10_23
    | ~ spl10_26 ),
    inference(subsumption_resolution,[],[f235,f217])).

fof(f217,plain,
    ( ~ m1_subset_1(sK6(sK4,sK1,sK3),sK2)
    | spl10_23 ),
    inference(avatar_component_clause,[],[f216])).

fof(f216,plain,
    ( spl10_23
  <=> m1_subset_1(sK6(sK4,sK1,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_23])])).

fof(f235,plain,
    ( m1_subset_1(sK6(sK4,sK1,sK3),sK2)
    | ~ spl10_26 ),
    inference(resolution,[],[f229,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f229,plain,
    ( r2_hidden(sK6(sK4,sK1,sK3),sK2)
    | ~ spl10_26 ),
    inference(avatar_component_clause,[],[f228])).

fof(f228,plain,
    ( spl10_26
  <=> r2_hidden(sK6(sK4,sK1,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_26])])).

fof(f230,plain,
    ( spl10_26
    | ~ spl10_12
    | ~ spl10_20 ),
    inference(avatar_split_clause,[],[f226,f168,f111,f228])).

fof(f111,plain,
    ( spl10_12
  <=> m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f168,plain,
    ( spl10_20
  <=> r2_hidden(sK6(sK4,sK1,sK3),k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_20])])).

fof(f226,plain,
    ( r2_hidden(sK6(sK4,sK1,sK3),sK2)
    | ~ spl10_12
    | ~ spl10_20 ),
    inference(resolution,[],[f136,f169])).

fof(f169,plain,
    ( r2_hidden(sK6(sK4,sK1,sK3),k2_relat_1(sK3))
    | ~ spl10_20 ),
    inference(avatar_component_clause,[],[f168])).

fof(f136,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK3))
        | r2_hidden(X0,sK2) )
    | ~ spl10_12 ),
    inference(resolution,[],[f112,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f112,plain,
    ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2))
    | ~ spl10_12 ),
    inference(avatar_component_clause,[],[f111])).

fof(f218,plain,
    ( ~ spl10_23
    | ~ spl10_11
    | ~ spl10_17
    | ~ spl10_22 ),
    inference(avatar_split_clause,[],[f212,f204,f155,f107,f216])).

fof(f107,plain,
    ( spl10_11
  <=> ! [X5] :
        ( ~ m1_subset_1(X5,sK2)
        | ~ r2_hidden(X5,sK1)
        | ~ r2_hidden(k4_tarski(sK4,X5),sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).

fof(f155,plain,
    ( spl10_17
  <=> r2_hidden(sK6(sK4,sK1,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).

fof(f204,plain,
    ( spl10_22
  <=> r2_hidden(k4_tarski(sK4,sK6(sK4,sK1,sK3)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).

fof(f212,plain,
    ( ~ m1_subset_1(sK6(sK4,sK1,sK3),sK2)
    | ~ spl10_11
    | ~ spl10_17
    | ~ spl10_22 ),
    inference(subsumption_resolution,[],[f207,f156])).

fof(f156,plain,
    ( r2_hidden(sK6(sK4,sK1,sK3),sK1)
    | ~ spl10_17 ),
    inference(avatar_component_clause,[],[f155])).

fof(f207,plain,
    ( ~ r2_hidden(sK6(sK4,sK1,sK3),sK1)
    | ~ m1_subset_1(sK6(sK4,sK1,sK3),sK2)
    | ~ spl10_11
    | ~ spl10_22 ),
    inference(resolution,[],[f205,f108])).

fof(f108,plain,
    ( ! [X5] :
        ( ~ r2_hidden(k4_tarski(sK4,X5),sK3)
        | ~ r2_hidden(X5,sK1)
        | ~ m1_subset_1(X5,sK2) )
    | ~ spl10_11 ),
    inference(avatar_component_clause,[],[f107])).

fof(f205,plain,
    ( r2_hidden(k4_tarski(sK4,sK6(sK4,sK1,sK3)),sK3)
    | ~ spl10_22 ),
    inference(avatar_component_clause,[],[f204])).

fof(f206,plain,
    ( spl10_22
    | ~ spl10_3
    | ~ spl10_8 ),
    inference(avatar_split_clause,[],[f195,f82,f60,f204])).

fof(f60,plain,
    ( spl10_3
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f82,plain,
    ( spl10_8
  <=> r2_hidden(sK4,k10_relat_1(sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f195,plain,
    ( r2_hidden(k4_tarski(sK4,sK6(sK4,sK1,sK3)),sK3)
    | ~ spl10_3
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f192,f61])).

fof(f61,plain,
    ( v1_relat_1(sK3)
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f60])).

fof(f192,plain,
    ( r2_hidden(k4_tarski(sK4,sK6(sK4,sK1,sK3)),sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl10_8 ),
    inference(resolution,[],[f83,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | r2_hidden(k4_tarski(X0,sK6(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

fof(f83,plain,
    ( r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f82])).

fof(f187,plain,
    ( spl10_9
    | ~ spl10_7
    | ~ spl10_10 ),
    inference(avatar_split_clause,[],[f186,f99,f77,f95])).

fof(f95,plain,
    ( spl10_9
  <=> sP8(sK4,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f77,plain,
    ( spl10_7
  <=> r2_hidden(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f99,plain,
    ( spl10_10
  <=> r2_hidden(k4_tarski(sK4,sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f186,plain,
    ( sP8(sK4,sK1,sK3)
    | ~ spl10_7
    | ~ spl10_10 ),
    inference(resolution,[],[f179,f78])).

fof(f78,plain,
    ( r2_hidden(sK5,sK1)
    | ~ spl10_7 ),
    inference(avatar_component_clause,[],[f77])).

fof(f179,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5,X0)
        | sP8(sK4,X0,sK3) )
    | ~ spl10_10 ),
    inference(resolution,[],[f100,f31])).

fof(f31,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X4),X0)
      | ~ r2_hidden(X4,X1)
      | sP8(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_1)).

fof(f100,plain,
    ( r2_hidden(k4_tarski(sK4,sK5),sK3)
    | ~ spl10_10 ),
    inference(avatar_component_clause,[],[f99])).

fof(f185,plain,
    ( ~ spl10_8
    | ~ spl10_2
    | spl10_4 ),
    inference(avatar_split_clause,[],[f119,f64,f51,f82])).

fof(f51,plain,
    ( spl10_2
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f64,plain,
    ( spl10_4
  <=> r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f119,plain,
    ( ~ r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | ~ spl10_2
    | spl10_4 ),
    inference(forward_demodulation,[],[f105,f57])).

fof(f57,plain,
    ( ! [X0] : k8_relset_1(sK0,sK2,sK3,X0) = k10_relat_1(sK3,X0)
    | ~ spl10_2 ),
    inference(resolution,[],[f52,f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f52,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f51])).

fof(f105,plain,
    ( ~ r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))
    | spl10_4 ),
    inference(avatar_component_clause,[],[f64])).

fof(f170,plain,
    ( spl10_20
    | ~ spl10_3
    | ~ spl10_8 ),
    inference(avatar_split_clause,[],[f151,f82,f60,f168])).

fof(f151,plain,
    ( r2_hidden(sK6(sK4,sK1,sK3),k2_relat_1(sK3))
    | ~ spl10_3
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f147,f61])).

fof(f147,plain,
    ( r2_hidden(sK6(sK4,sK1,sK3),k2_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl10_8 ),
    inference(resolution,[],[f83,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | r2_hidden(sK6(X0,X1,X2),k2_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f157,plain,
    ( spl10_17
    | ~ spl10_3
    | ~ spl10_8 ),
    inference(avatar_split_clause,[],[f153,f82,f60,f155])).

fof(f153,plain,
    ( r2_hidden(sK6(sK4,sK1,sK3),sK1)
    | ~ spl10_3
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f149,f61])).

fof(f149,plain,
    ( r2_hidden(sK6(sK4,sK1,sK3),sK1)
    | ~ v1_relat_1(sK3)
    | ~ spl10_8 ),
    inference(resolution,[],[f83,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | r2_hidden(sK6(X0,X1,X2),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f145,plain,
    ( spl10_8
    | ~ spl10_3
    | ~ spl10_9 ),
    inference(avatar_split_clause,[],[f118,f95,f60,f82])).

fof(f118,plain,
    ( r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | ~ spl10_3
    | ~ spl10_9 ),
    inference(subsumption_resolution,[],[f104,f61])).

fof(f104,plain,
    ( ~ v1_relat_1(sK3)
    | r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | ~ spl10_9 ),
    inference(resolution,[],[f96,f45])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( ~ sP8(X3,X1,X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(X3,k10_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ sP8(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f96,plain,
    ( sP8(sK4,sK1,sK3)
    | ~ spl10_9 ),
    inference(avatar_component_clause,[],[f95])).

fof(f113,plain,
    ( spl10_12
    | ~ spl10_2
    | ~ spl10_6 ),
    inference(avatar_split_clause,[],[f75,f72,f51,f111])).

fof(f72,plain,
    ( spl10_6
  <=> m1_subset_1(k2_relset_1(sK0,sK2,sK3),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f75,plain,
    ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2))
    | ~ spl10_2
    | ~ spl10_6 ),
    inference(forward_demodulation,[],[f73,f55])).

fof(f55,plain,
    ( k2_relset_1(sK0,sK2,sK3) = k2_relat_1(sK3)
    | ~ spl10_2 ),
    inference(resolution,[],[f52,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f73,plain,
    ( m1_subset_1(k2_relset_1(sK0,sK2,sK3),k1_zfmisc_1(sK2))
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f72])).

fof(f109,plain,
    ( ~ spl10_4
    | spl10_11 ),
    inference(avatar_split_clause,[],[f21,f107,f64])).

fof(f21,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,sK2)
      | ~ r2_hidden(k4_tarski(sK4,X5),sK3)
      | ~ r2_hidden(X5,sK1)
      | ~ r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))
          <~> ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X4,X5),X3)
                & m1_subset_1(X5,X2) ) )
          & m1_subset_1(X4,X0) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
       => ! [X4] :
            ( m1_subset_1(X4,X0)
           => ( r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))
            <=> ? [X5] :
                  ( r2_hidden(X5,X1)
                  & r2_hidden(k4_tarski(X4,X5),X3)
                  & m1_subset_1(X5,X2) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( ~ v1_xboole_0(X2)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                   => ! [X4] :
                        ( m1_subset_1(X4,X0)
                       => ( r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))
                        <=> ? [X5] :
                              ( r2_hidden(X5,X1)
                              & r2_hidden(k4_tarski(X4,X5),X3)
                              & m1_subset_1(X5,X2) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ~ v1_xboole_0(X2)
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                 => ! [X4] :
                      ( m1_subset_1(X4,X0)
                     => ( r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))
                      <=> ? [X5] :
                            ( r2_hidden(X5,X1)
                            & r2_hidden(k4_tarski(X4,X5),X3)
                            & m1_subset_1(X5,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_relset_1)).

fof(f101,plain,
    ( spl10_4
    | spl10_10 ),
    inference(avatar_split_clause,[],[f23,f99,f64])).

fof(f23,plain,
    ( r2_hidden(k4_tarski(sK4,sK5),sK3)
    | r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f84,plain,
    ( spl10_8
    | ~ spl10_2
    | ~ spl10_4 ),
    inference(avatar_split_clause,[],[f80,f64,f51,f82])).

fof(f80,plain,
    ( r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | ~ spl10_2
    | ~ spl10_4 ),
    inference(forward_demodulation,[],[f65,f57])).

fof(f65,plain,
    ( r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f64])).

fof(f79,plain,
    ( spl10_4
    | spl10_7 ),
    inference(avatar_split_clause,[],[f24,f77,f64])).

fof(f24,plain,
    ( r2_hidden(sK5,sK1)
    | r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f74,plain,
    ( spl10_6
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f54,f51,f72])).

fof(f54,plain,
    ( m1_subset_1(k2_relset_1(sK0,sK2,sK3),k1_zfmisc_1(sK2))
    | ~ spl10_2 ),
    inference(resolution,[],[f52,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f62,plain,
    ( spl10_3
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f56,f51,f60])).

fof(f56,plain,
    ( v1_relat_1(sK3)
    | ~ spl10_2 ),
    inference(resolution,[],[f52,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f53,plain,(
    spl10_2 ),
    inference(avatar_split_clause,[],[f26,f51])).

fof(f26,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:56:14 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (7921)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.47  % (7914)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.48  % (7908)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.49  % (7909)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (7917)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.50  % (7904)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (7913)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.50  % (7922)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.51  % (7904)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  % (7916)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  fof(f238,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f53,f62,f74,f79,f84,f101,f109,f113,f145,f157,f170,f185,f187,f206,f218,f230,f237])).
% 0.21/0.51  % (7906)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.51  fof(f237,plain,(
% 0.21/0.51    spl10_23 | ~spl10_26),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f236])).
% 0.21/0.51  fof(f236,plain,(
% 0.21/0.51    $false | (spl10_23 | ~spl10_26)),
% 0.21/0.51    inference(subsumption_resolution,[],[f235,f217])).
% 0.21/0.51  fof(f217,plain,(
% 0.21/0.51    ~m1_subset_1(sK6(sK4,sK1,sK3),sK2) | spl10_23),
% 0.21/0.51    inference(avatar_component_clause,[],[f216])).
% 0.21/0.51  fof(f216,plain,(
% 0.21/0.51    spl10_23 <=> m1_subset_1(sK6(sK4,sK1,sK3),sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_23])])).
% 0.21/0.51  fof(f235,plain,(
% 0.21/0.51    m1_subset_1(sK6(sK4,sK1,sK3),sK2) | ~spl10_26),
% 0.21/0.51    inference(resolution,[],[f229,f39])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 0.21/0.51  fof(f229,plain,(
% 0.21/0.51    r2_hidden(sK6(sK4,sK1,sK3),sK2) | ~spl10_26),
% 0.21/0.51    inference(avatar_component_clause,[],[f228])).
% 0.21/0.51  fof(f228,plain,(
% 0.21/0.51    spl10_26 <=> r2_hidden(sK6(sK4,sK1,sK3),sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_26])])).
% 0.21/0.51  fof(f230,plain,(
% 0.21/0.51    spl10_26 | ~spl10_12 | ~spl10_20),
% 0.21/0.51    inference(avatar_split_clause,[],[f226,f168,f111,f228])).
% 0.21/0.51  fof(f111,plain,(
% 0.21/0.51    spl10_12 <=> m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).
% 0.21/0.51  fof(f168,plain,(
% 0.21/0.51    spl10_20 <=> r2_hidden(sK6(sK4,sK1,sK3),k2_relat_1(sK3))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_20])])).
% 0.21/0.51  fof(f226,plain,(
% 0.21/0.51    r2_hidden(sK6(sK4,sK1,sK3),sK2) | (~spl10_12 | ~spl10_20)),
% 0.21/0.51    inference(resolution,[],[f136,f169])).
% 0.21/0.51  fof(f169,plain,(
% 0.21/0.51    r2_hidden(sK6(sK4,sK1,sK3),k2_relat_1(sK3)) | ~spl10_20),
% 0.21/0.51    inference(avatar_component_clause,[],[f168])).
% 0.21/0.51  fof(f136,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK3)) | r2_hidden(X0,sK2)) ) | ~spl10_12),
% 0.21/0.51    inference(resolution,[],[f112,f38])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 0.21/0.51  fof(f112,plain,(
% 0.21/0.51    m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2)) | ~spl10_12),
% 0.21/0.51    inference(avatar_component_clause,[],[f111])).
% 0.21/0.51  fof(f218,plain,(
% 0.21/0.51    ~spl10_23 | ~spl10_11 | ~spl10_17 | ~spl10_22),
% 0.21/0.51    inference(avatar_split_clause,[],[f212,f204,f155,f107,f216])).
% 0.21/0.51  fof(f107,plain,(
% 0.21/0.51    spl10_11 <=> ! [X5] : (~m1_subset_1(X5,sK2) | ~r2_hidden(X5,sK1) | ~r2_hidden(k4_tarski(sK4,X5),sK3))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).
% 0.21/0.51  fof(f155,plain,(
% 0.21/0.51    spl10_17 <=> r2_hidden(sK6(sK4,sK1,sK3),sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).
% 0.21/0.51  fof(f204,plain,(
% 0.21/0.51    spl10_22 <=> r2_hidden(k4_tarski(sK4,sK6(sK4,sK1,sK3)),sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).
% 0.21/0.51  fof(f212,plain,(
% 0.21/0.51    ~m1_subset_1(sK6(sK4,sK1,sK3),sK2) | (~spl10_11 | ~spl10_17 | ~spl10_22)),
% 0.21/0.51    inference(subsumption_resolution,[],[f207,f156])).
% 0.21/0.51  fof(f156,plain,(
% 0.21/0.51    r2_hidden(sK6(sK4,sK1,sK3),sK1) | ~spl10_17),
% 0.21/0.51    inference(avatar_component_clause,[],[f155])).
% 0.21/0.51  fof(f207,plain,(
% 0.21/0.51    ~r2_hidden(sK6(sK4,sK1,sK3),sK1) | ~m1_subset_1(sK6(sK4,sK1,sK3),sK2) | (~spl10_11 | ~spl10_22)),
% 0.21/0.51    inference(resolution,[],[f205,f108])).
% 0.21/0.51  fof(f108,plain,(
% 0.21/0.51    ( ! [X5] : (~r2_hidden(k4_tarski(sK4,X5),sK3) | ~r2_hidden(X5,sK1) | ~m1_subset_1(X5,sK2)) ) | ~spl10_11),
% 0.21/0.51    inference(avatar_component_clause,[],[f107])).
% 0.21/0.51  fof(f205,plain,(
% 0.21/0.51    r2_hidden(k4_tarski(sK4,sK6(sK4,sK1,sK3)),sK3) | ~spl10_22),
% 0.21/0.51    inference(avatar_component_clause,[],[f204])).
% 0.21/0.51  fof(f206,plain,(
% 0.21/0.51    spl10_22 | ~spl10_3 | ~spl10_8),
% 0.21/0.51    inference(avatar_split_clause,[],[f195,f82,f60,f204])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    spl10_3 <=> v1_relat_1(sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 0.21/0.51  fof(f82,plain,(
% 0.21/0.51    spl10_8 <=> r2_hidden(sK4,k10_relat_1(sK3,sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).
% 0.21/0.51  fof(f195,plain,(
% 0.21/0.51    r2_hidden(k4_tarski(sK4,sK6(sK4,sK1,sK3)),sK3) | (~spl10_3 | ~spl10_8)),
% 0.21/0.51    inference(subsumption_resolution,[],[f192,f61])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    v1_relat_1(sK3) | ~spl10_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f60])).
% 0.21/0.51  fof(f192,plain,(
% 0.21/0.51    r2_hidden(k4_tarski(sK4,sK6(sK4,sK1,sK3)),sK3) | ~v1_relat_1(sK3) | ~spl10_8),
% 0.21/0.51    inference(resolution,[],[f83,f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X0,k10_relat_1(X2,X1)) | r2_hidden(k4_tarski(X0,sK6(X0,X1,X2)),X2) | ~v1_relat_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).
% 0.21/0.51  fof(f83,plain,(
% 0.21/0.51    r2_hidden(sK4,k10_relat_1(sK3,sK1)) | ~spl10_8),
% 0.21/0.51    inference(avatar_component_clause,[],[f82])).
% 0.21/0.51  fof(f187,plain,(
% 0.21/0.51    spl10_9 | ~spl10_7 | ~spl10_10),
% 0.21/0.51    inference(avatar_split_clause,[],[f186,f99,f77,f95])).
% 0.21/0.51  fof(f95,plain,(
% 0.21/0.51    spl10_9 <=> sP8(sK4,sK1,sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).
% 0.21/0.51  fof(f77,plain,(
% 0.21/0.51    spl10_7 <=> r2_hidden(sK5,sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).
% 0.21/0.51  fof(f99,plain,(
% 0.21/0.51    spl10_10 <=> r2_hidden(k4_tarski(sK4,sK5),sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).
% 0.21/0.51  fof(f186,plain,(
% 0.21/0.51    sP8(sK4,sK1,sK3) | (~spl10_7 | ~spl10_10)),
% 0.21/0.51    inference(resolution,[],[f179,f78])).
% 0.21/0.51  fof(f78,plain,(
% 0.21/0.51    r2_hidden(sK5,sK1) | ~spl10_7),
% 0.21/0.51    inference(avatar_component_clause,[],[f77])).
% 0.21/0.51  fof(f179,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(sK5,X0) | sP8(sK4,X0,sK3)) ) | ~spl10_10),
% 0.21/0.51    inference(resolution,[],[f100,f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ( ! [X4,X0,X3,X1] : (~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X4,X1) | sP8(X3,X1,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_1)).
% 0.21/0.51  fof(f100,plain,(
% 0.21/0.51    r2_hidden(k4_tarski(sK4,sK5),sK3) | ~spl10_10),
% 0.21/0.51    inference(avatar_component_clause,[],[f99])).
% 0.21/0.51  fof(f185,plain,(
% 0.21/0.51    ~spl10_8 | ~spl10_2 | spl10_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f119,f64,f51,f82])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    spl10_2 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    spl10_4 <=> r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 0.21/0.51  fof(f119,plain,(
% 0.21/0.51    ~r2_hidden(sK4,k10_relat_1(sK3,sK1)) | (~spl10_2 | spl10_4)),
% 0.21/0.51    inference(forward_demodulation,[],[f105,f57])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    ( ! [X0] : (k8_relset_1(sK0,sK2,sK3,X0) = k10_relat_1(sK3,X0)) ) | ~spl10_2),
% 0.21/0.51    inference(resolution,[],[f52,f40])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~spl10_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f51])).
% 0.21/0.51  fof(f105,plain,(
% 0.21/0.51    ~r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) | spl10_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f64])).
% 0.21/0.51  fof(f170,plain,(
% 0.21/0.51    spl10_20 | ~spl10_3 | ~spl10_8),
% 0.21/0.51    inference(avatar_split_clause,[],[f151,f82,f60,f168])).
% 0.21/0.51  fof(f151,plain,(
% 0.21/0.51    r2_hidden(sK6(sK4,sK1,sK3),k2_relat_1(sK3)) | (~spl10_3 | ~spl10_8)),
% 0.21/0.51    inference(subsumption_resolution,[],[f147,f61])).
% 0.21/0.51  fof(f147,plain,(
% 0.21/0.51    r2_hidden(sK6(sK4,sK1,sK3),k2_relat_1(sK3)) | ~v1_relat_1(sK3) | ~spl10_8),
% 0.21/0.51    inference(resolution,[],[f83,f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X0,k10_relat_1(X2,X1)) | r2_hidden(sK6(X0,X1,X2),k2_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f13])).
% 0.21/0.51  fof(f157,plain,(
% 0.21/0.51    spl10_17 | ~spl10_3 | ~spl10_8),
% 0.21/0.51    inference(avatar_split_clause,[],[f153,f82,f60,f155])).
% 0.21/0.51  fof(f153,plain,(
% 0.21/0.51    r2_hidden(sK6(sK4,sK1,sK3),sK1) | (~spl10_3 | ~spl10_8)),
% 0.21/0.51    inference(subsumption_resolution,[],[f149,f61])).
% 0.21/0.51  fof(f149,plain,(
% 0.21/0.51    r2_hidden(sK6(sK4,sK1,sK3),sK1) | ~v1_relat_1(sK3) | ~spl10_8),
% 0.21/0.51    inference(resolution,[],[f83,f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X0,k10_relat_1(X2,X1)) | r2_hidden(sK6(X0,X1,X2),X1) | ~v1_relat_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f13])).
% 0.21/0.51  fof(f145,plain,(
% 0.21/0.51    spl10_8 | ~spl10_3 | ~spl10_9),
% 0.21/0.51    inference(avatar_split_clause,[],[f118,f95,f60,f82])).
% 0.21/0.51  fof(f118,plain,(
% 0.21/0.51    r2_hidden(sK4,k10_relat_1(sK3,sK1)) | (~spl10_3 | ~spl10_9)),
% 0.21/0.51    inference(subsumption_resolution,[],[f104,f61])).
% 0.21/0.51  fof(f104,plain,(
% 0.21/0.51    ~v1_relat_1(sK3) | r2_hidden(sK4,k10_relat_1(sK3,sK1)) | ~spl10_9),
% 0.21/0.51    inference(resolution,[],[f96,f45])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    ( ! [X0,X3,X1] : (~sP8(X3,X1,X0) | ~v1_relat_1(X0) | r2_hidden(X3,k10_relat_1(X0,X1))) )),
% 0.21/0.51    inference(equality_resolution,[],[f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~sP8(X3,X1,X0) | r2_hidden(X3,X2) | k10_relat_1(X0,X1) != X2) )),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f96,plain,(
% 0.21/0.51    sP8(sK4,sK1,sK3) | ~spl10_9),
% 0.21/0.51    inference(avatar_component_clause,[],[f95])).
% 0.21/0.51  fof(f113,plain,(
% 0.21/0.51    spl10_12 | ~spl10_2 | ~spl10_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f75,f72,f51,f111])).
% 0.21/0.51  fof(f72,plain,(
% 0.21/0.51    spl10_6 <=> m1_subset_1(k2_relset_1(sK0,sK2,sK3),k1_zfmisc_1(sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).
% 0.21/0.51  fof(f75,plain,(
% 0.21/0.51    m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2)) | (~spl10_2 | ~spl10_6)),
% 0.21/0.51    inference(forward_demodulation,[],[f73,f55])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    k2_relset_1(sK0,sK2,sK3) = k2_relat_1(sK3) | ~spl10_2),
% 0.21/0.51    inference(resolution,[],[f52,f42])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relat_1(X2) = k2_relset_1(X0,X1,X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    m1_subset_1(k2_relset_1(sK0,sK2,sK3),k1_zfmisc_1(sK2)) | ~spl10_6),
% 0.21/0.51    inference(avatar_component_clause,[],[f72])).
% 0.21/0.51  fof(f109,plain,(
% 0.21/0.51    ~spl10_4 | spl10_11),
% 0.21/0.51    inference(avatar_split_clause,[],[f21,f107,f64])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ( ! [X5] : (~m1_subset_1(X5,sK2) | ~r2_hidden(k4_tarski(sK4,X5),sK3) | ~r2_hidden(X5,sK1) | ~r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ? [X0,X1,X2,X3] : (? [X4] : ((r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) <~> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.21/0.51    inference(ennf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2)))))),
% 0.21/0.51    inference(pure_predicate_removal,[],[f10])).
% 0.21/0.51  fof(f10,negated_conjecture,(
% 0.21/0.51    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2))))))))),
% 0.21/0.51    inference(negated_conjecture,[],[f9])).
% 0.21/0.51  fof(f9,conjecture,(
% 0.21/0.51    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2))))))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_relset_1)).
% 0.21/0.51  fof(f101,plain,(
% 0.21/0.51    spl10_4 | spl10_10),
% 0.21/0.51    inference(avatar_split_clause,[],[f23,f99,f64])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    r2_hidden(k4_tarski(sK4,sK5),sK3) | r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f84,plain,(
% 0.21/0.51    spl10_8 | ~spl10_2 | ~spl10_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f80,f64,f51,f82])).
% 0.21/0.51  fof(f80,plain,(
% 0.21/0.51    r2_hidden(sK4,k10_relat_1(sK3,sK1)) | (~spl10_2 | ~spl10_4)),
% 0.21/0.51    inference(forward_demodulation,[],[f65,f57])).
% 0.21/0.51  fof(f65,plain,(
% 0.21/0.51    r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) | ~spl10_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f64])).
% 0.21/0.51  fof(f79,plain,(
% 0.21/0.51    spl10_4 | spl10_7),
% 0.21/0.51    inference(avatar_split_clause,[],[f24,f77,f64])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    r2_hidden(sK5,sK1) | r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f74,plain,(
% 0.21/0.51    spl10_6 | ~spl10_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f54,f51,f72])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    m1_subset_1(k2_relset_1(sK0,sK2,sK3),k1_zfmisc_1(sK2)) | ~spl10_2),
% 0.21/0.51    inference(resolution,[],[f52,f43])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 0.21/0.51  fof(f62,plain,(
% 0.21/0.51    spl10_3 | ~spl10_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f56,f51,f60])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    v1_relat_1(sK3) | ~spl10_2),
% 0.21/0.51    inference(resolution,[],[f52,f41])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    spl10_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f26,f51])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (7904)------------------------------
% 0.21/0.51  % (7904)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (7904)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (7904)Memory used [KB]: 6268
% 0.21/0.51  % (7904)Time elapsed: 0.085 s
% 0.21/0.51  % (7904)------------------------------
% 0.21/0.51  % (7904)------------------------------
% 0.21/0.51  % (7903)Success in time 0.143 s
%------------------------------------------------------------------------------
