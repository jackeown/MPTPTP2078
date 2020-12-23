%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:29 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 130 expanded)
%              Number of leaves         :   21 (  61 expanded)
%              Depth                    :    5
%              Number of atoms          :  225 ( 366 expanded)
%              Number of equality atoms :    8 (  14 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f207,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f41,f52,f57,f61,f65,f69,f73,f81,f100,f114,f124,f128,f164,f173,f185,f197,f206])).

fof(f206,plain,
    ( ~ spl8_3
    | ~ spl8_24
    | ~ spl8_25
    | spl8_29 ),
    inference(avatar_contradiction_clause,[],[f204])).

fof(f204,plain,
    ( $false
    | ~ spl8_3
    | ~ spl8_24
    | ~ spl8_25
    | spl8_29 ),
    inference(unit_resulting_resolution,[],[f40,f163,f196,f172])).

fof(f172,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
        | ~ r2_hidden(k4_tarski(X0,X2),X3)
        | r2_hidden(X0,X1) )
    | ~ spl8_25 ),
    inference(avatar_component_clause,[],[f171])).

fof(f171,plain,
    ( spl8_25
  <=> ! [X1,X3,X0,X2,X4] :
        ( r2_hidden(X0,X1)
        | ~ r2_hidden(k4_tarski(X0,X2),X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X4))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f196,plain,
    ( ~ r2_hidden(sK6(sK2,sK3),sK1)
    | spl8_29 ),
    inference(avatar_component_clause,[],[f195])).

fof(f195,plain,
    ( spl8_29
  <=> r2_hidden(sK6(sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).

fof(f163,plain,
    ( r2_hidden(k4_tarski(sK6(sK2,sK3),sK3),sK2)
    | ~ spl8_24 ),
    inference(avatar_component_clause,[],[f162])).

fof(f162,plain,
    ( spl8_24
  <=> r2_hidden(k4_tarski(sK6(sK2,sK3),sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f40,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl8_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f197,plain,
    ( ~ spl8_29
    | ~ spl8_8
    | spl8_27 ),
    inference(avatar_split_clause,[],[f192,f183,f59,f195])).

fof(f59,plain,
    ( spl8_8
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,X1)
        | m1_subset_1(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f183,plain,
    ( spl8_27
  <=> m1_subset_1(sK6(sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).

fof(f192,plain,
    ( ~ r2_hidden(sK6(sK2,sK3),sK1)
    | ~ spl8_8
    | spl8_27 ),
    inference(resolution,[],[f184,f60])).

fof(f60,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(X0,X1)
        | ~ r2_hidden(X0,X1) )
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f59])).

fof(f184,plain,
    ( ~ m1_subset_1(sK6(sK2,sK3),sK1)
    | spl8_27 ),
    inference(avatar_component_clause,[],[f183])).

fof(f185,plain,
    ( ~ spl8_27
    | ~ spl8_7
    | ~ spl8_24 ),
    inference(avatar_split_clause,[],[f169,f162,f55,f183])).

fof(f55,plain,
    ( spl8_7
  <=> ! [X4] :
        ( ~ m1_subset_1(X4,sK1)
        | ~ r2_hidden(k4_tarski(X4,sK3),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f169,plain,
    ( ~ m1_subset_1(sK6(sK2,sK3),sK1)
    | ~ spl8_7
    | ~ spl8_24 ),
    inference(resolution,[],[f163,f56])).

fof(f56,plain,
    ( ! [X4] :
        ( ~ r2_hidden(k4_tarski(X4,sK3),sK2)
        | ~ m1_subset_1(X4,sK1) )
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f55])).

fof(f173,plain,
    ( spl8_25
    | ~ spl8_10
    | ~ spl8_11 ),
    inference(avatar_split_clause,[],[f87,f71,f67,f171])).

fof(f67,plain,
    ( spl8_10
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ r2_hidden(X2,X1)
        | r2_hidden(X2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f71,plain,
    ( spl8_11
  <=> ! [X1,X3,X0,X2] :
        ( r2_hidden(X0,X2)
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f87,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( r2_hidden(X0,X1)
        | ~ r2_hidden(k4_tarski(X0,X2),X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X4))) )
    | ~ spl8_10
    | ~ spl8_11 ),
    inference(resolution,[],[f72,f68])).

fof(f68,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(X2,X0)
        | ~ r2_hidden(X2,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f67])).

fof(f72,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | r2_hidden(X0,X2) )
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f71])).

fof(f164,plain,
    ( spl8_24
    | ~ spl8_13
    | ~ spl8_19 ),
    inference(avatar_split_clause,[],[f137,f112,f79,f162])).

fof(f79,plain,
    ( spl8_13
  <=> ! [X0,X2] :
        ( r2_hidden(k4_tarski(sK6(X0,X2),X2),X0)
        | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f112,plain,
    ( spl8_19
  <=> r2_hidden(sK3,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f137,plain,
    ( r2_hidden(k4_tarski(sK6(sK2,sK3),sK3),sK2)
    | ~ spl8_13
    | ~ spl8_19 ),
    inference(resolution,[],[f127,f80])).

fof(f80,plain,
    ( ! [X2,X0] :
        ( ~ r2_hidden(X2,k2_relat_1(X0))
        | r2_hidden(k4_tarski(sK6(X0,X2),X2),X0) )
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f79])).

fof(f127,plain,
    ( r2_hidden(sK3,k2_relat_1(sK2))
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f112])).

fof(f128,plain,
    ( spl8_19
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f126,f98,f43,f39,f112])).

fof(f43,plain,
    ( spl8_4
  <=> r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f98,plain,
    ( spl8_16
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f126,plain,
    ( r2_hidden(sK3,k2_relat_1(sK2))
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f125,f40])).

fof(f125,plain,
    ( r2_hidden(sK3,k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl8_4
    | ~ spl8_16 ),
    inference(superposition,[],[f44,f99])).

fof(f99,plain,
    ( ! [X2,X0,X1] :
        ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f98])).

fof(f44,plain,
    ( r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2))
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f43])).

fof(f124,plain,
    ( ~ spl8_6
    | ~ spl8_9
    | spl8_19 ),
    inference(avatar_contradiction_clause,[],[f121])).

fof(f121,plain,
    ( $false
    | ~ spl8_6
    | ~ spl8_9
    | spl8_19 ),
    inference(unit_resulting_resolution,[],[f51,f113,f64])).

fof(f64,plain,
    ( ! [X2,X0,X3] :
        ( r2_hidden(X2,k2_relat_1(X0))
        | ~ r2_hidden(k4_tarski(X3,X2),X0) )
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl8_9
  <=> ! [X3,X0,X2] :
        ( ~ r2_hidden(k4_tarski(X3,X2),X0)
        | r2_hidden(X2,k2_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f113,plain,
    ( ~ r2_hidden(sK3,k2_relat_1(sK2))
    | spl8_19 ),
    inference(avatar_component_clause,[],[f112])).

fof(f51,plain,
    ( r2_hidden(k4_tarski(sK4,sK3),sK2)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl8_6
  <=> r2_hidden(k4_tarski(sK4,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f114,plain,
    ( ~ spl8_19
    | ~ spl8_3
    | spl8_4
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f110,f98,f43,f39,f112])).

fof(f110,plain,
    ( ~ r2_hidden(sK3,k2_relat_1(sK2))
    | ~ spl8_3
    | spl8_4
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f109,f40])).

fof(f109,plain,
    ( ~ r2_hidden(sK3,k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl8_4
    | ~ spl8_16 ),
    inference(superposition,[],[f53,f99])).

fof(f53,plain,
    ( ~ r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2))
    | spl8_4 ),
    inference(avatar_component_clause,[],[f43])).

fof(f100,plain,(
    spl8_16 ),
    inference(avatar_split_clause,[],[f24,f98])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f81,plain,(
    spl8_13 ),
    inference(avatar_split_clause,[],[f28,f79])).

fof(f28,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(sK6(X0,X2),X2),X0)
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK6(X0,X2),X2),X0)
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f73,plain,(
    spl8_11 ),
    inference(avatar_split_clause,[],[f25,f71])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f69,plain,(
    spl8_10 ),
    inference(avatar_split_clause,[],[f19,f67])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f65,plain,(
    spl8_9 ),
    inference(avatar_split_clause,[],[f29,f63])).

fof(f29,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f20])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f61,plain,(
    spl8_8 ),
    inference(avatar_split_clause,[],[f18,f59])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f57,plain,
    ( ~ spl8_4
    | spl8_7 ),
    inference(avatar_split_clause,[],[f12,f55,f43])).

fof(f12,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,sK1)
      | ~ r2_hidden(k4_tarski(X4,sK3),sK2)
      | ~ r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( r2_hidden(X3,k2_relset_1(X1,X0,X2))
                <~> ? [X4] :
                      ( r2_hidden(k4_tarski(X4,X3),X2)
                      & m1_subset_1(X4,X1) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
               => ! [X3] :
                    ( r2_hidden(X3,k2_relset_1(X1,X0,X2))
                  <=> ? [X4] :
                        ( r2_hidden(k4_tarski(X4,X3),X2)
                        & m1_subset_1(X4,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
             => ! [X3] :
                  ( r2_hidden(X3,k2_relset_1(X1,X0,X2))
                <=> ? [X4] :
                      ( r2_hidden(k4_tarski(X4,X3),X2)
                      & m1_subset_1(X4,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_relset_1)).

fof(f52,plain,
    ( spl8_4
    | spl8_6 ),
    inference(avatar_split_clause,[],[f14,f50,f43])).

fof(f14,plain,
    ( r2_hidden(k4_tarski(sK4,sK3),sK2)
    | r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f41,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f15,f39])).

fof(f15,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n013.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:04:24 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (4511)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.48  % (4519)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.48  % (4511)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f207,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f41,f52,f57,f61,f65,f69,f73,f81,f100,f114,f124,f128,f164,f173,f185,f197,f206])).
% 0.21/0.49  fof(f206,plain,(
% 0.21/0.49    ~spl8_3 | ~spl8_24 | ~spl8_25 | spl8_29),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f204])).
% 0.21/0.49  fof(f204,plain,(
% 0.21/0.49    $false | (~spl8_3 | ~spl8_24 | ~spl8_25 | spl8_29)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f40,f163,f196,f172])).
% 0.21/0.49  fof(f172,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X4))) | ~r2_hidden(k4_tarski(X0,X2),X3) | r2_hidden(X0,X1)) ) | ~spl8_25),
% 0.21/0.49    inference(avatar_component_clause,[],[f171])).
% 0.21/0.49  fof(f171,plain,(
% 0.21/0.49    spl8_25 <=> ! [X1,X3,X0,X2,X4] : (r2_hidden(X0,X1) | ~r2_hidden(k4_tarski(X0,X2),X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X4))))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).
% 0.21/0.49  fof(f196,plain,(
% 0.21/0.49    ~r2_hidden(sK6(sK2,sK3),sK1) | spl8_29),
% 0.21/0.49    inference(avatar_component_clause,[],[f195])).
% 0.21/0.49  fof(f195,plain,(
% 0.21/0.49    spl8_29 <=> r2_hidden(sK6(sK2,sK3),sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).
% 0.21/0.49  fof(f163,plain,(
% 0.21/0.49    r2_hidden(k4_tarski(sK6(sK2,sK3),sK3),sK2) | ~spl8_24),
% 0.21/0.49    inference(avatar_component_clause,[],[f162])).
% 0.21/0.49  fof(f162,plain,(
% 0.21/0.49    spl8_24 <=> r2_hidden(k4_tarski(sK6(sK2,sK3),sK3),sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl8_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f39])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    spl8_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.21/0.49  fof(f197,plain,(
% 0.21/0.49    ~spl8_29 | ~spl8_8 | spl8_27),
% 0.21/0.49    inference(avatar_split_clause,[],[f192,f183,f59,f195])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    spl8_8 <=> ! [X1,X0] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.21/0.49  fof(f183,plain,(
% 0.21/0.49    spl8_27 <=> m1_subset_1(sK6(sK2,sK3),sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).
% 0.21/0.49  fof(f192,plain,(
% 0.21/0.49    ~r2_hidden(sK6(sK2,sK3),sK1) | (~spl8_8 | spl8_27)),
% 0.21/0.49    inference(resolution,[],[f184,f60])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) ) | ~spl8_8),
% 0.21/0.49    inference(avatar_component_clause,[],[f59])).
% 0.21/0.49  fof(f184,plain,(
% 0.21/0.49    ~m1_subset_1(sK6(sK2,sK3),sK1) | spl8_27),
% 0.21/0.49    inference(avatar_component_clause,[],[f183])).
% 0.21/0.49  fof(f185,plain,(
% 0.21/0.49    ~spl8_27 | ~spl8_7 | ~spl8_24),
% 0.21/0.49    inference(avatar_split_clause,[],[f169,f162,f55,f183])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    spl8_7 <=> ! [X4] : (~m1_subset_1(X4,sK1) | ~r2_hidden(k4_tarski(X4,sK3),sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.21/0.49  fof(f169,plain,(
% 0.21/0.49    ~m1_subset_1(sK6(sK2,sK3),sK1) | (~spl8_7 | ~spl8_24)),
% 0.21/0.49    inference(resolution,[],[f163,f56])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    ( ! [X4] : (~r2_hidden(k4_tarski(X4,sK3),sK2) | ~m1_subset_1(X4,sK1)) ) | ~spl8_7),
% 0.21/0.49    inference(avatar_component_clause,[],[f55])).
% 0.21/0.49  fof(f173,plain,(
% 0.21/0.49    spl8_25 | ~spl8_10 | ~spl8_11),
% 0.21/0.49    inference(avatar_split_clause,[],[f87,f71,f67,f171])).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    spl8_10 <=> ! [X1,X0,X2] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.21/0.49  fof(f71,plain,(
% 0.21/0.49    spl8_11 <=> ! [X1,X3,X0,X2] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 0.21/0.49  fof(f87,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(X0,X1) | ~r2_hidden(k4_tarski(X0,X2),X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X4)))) ) | (~spl8_10 | ~spl8_11)),
% 0.21/0.49    inference(resolution,[],[f72,f68])).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl8_10),
% 0.21/0.49    inference(avatar_component_clause,[],[f67])).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) ) | ~spl8_11),
% 0.21/0.49    inference(avatar_component_clause,[],[f71])).
% 0.21/0.49  fof(f164,plain,(
% 0.21/0.49    spl8_24 | ~spl8_13 | ~spl8_19),
% 0.21/0.49    inference(avatar_split_clause,[],[f137,f112,f79,f162])).
% 0.21/0.49  fof(f79,plain,(
% 0.21/0.49    spl8_13 <=> ! [X0,X2] : (r2_hidden(k4_tarski(sK6(X0,X2),X2),X0) | ~r2_hidden(X2,k2_relat_1(X0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 0.21/0.49  fof(f112,plain,(
% 0.21/0.49    spl8_19 <=> r2_hidden(sK3,k2_relat_1(sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).
% 0.21/0.49  fof(f137,plain,(
% 0.21/0.49    r2_hidden(k4_tarski(sK6(sK2,sK3),sK3),sK2) | (~spl8_13 | ~spl8_19)),
% 0.21/0.49    inference(resolution,[],[f127,f80])).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    ( ! [X2,X0] : (~r2_hidden(X2,k2_relat_1(X0)) | r2_hidden(k4_tarski(sK6(X0,X2),X2),X0)) ) | ~spl8_13),
% 0.21/0.49    inference(avatar_component_clause,[],[f79])).
% 0.21/0.49  fof(f127,plain,(
% 0.21/0.49    r2_hidden(sK3,k2_relat_1(sK2)) | ~spl8_19),
% 0.21/0.49    inference(avatar_component_clause,[],[f112])).
% 0.21/0.49  fof(f128,plain,(
% 0.21/0.49    spl8_19 | ~spl8_3 | ~spl8_4 | ~spl8_16),
% 0.21/0.49    inference(avatar_split_clause,[],[f126,f98,f43,f39,f112])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    spl8_4 <=> r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.21/0.49  fof(f98,plain,(
% 0.21/0.49    spl8_16 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).
% 0.21/0.49  fof(f126,plain,(
% 0.21/0.49    r2_hidden(sK3,k2_relat_1(sK2)) | (~spl8_3 | ~spl8_4 | ~spl8_16)),
% 0.21/0.49    inference(subsumption_resolution,[],[f125,f40])).
% 0.21/0.49  fof(f125,plain,(
% 0.21/0.49    r2_hidden(sK3,k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | (~spl8_4 | ~spl8_16)),
% 0.21/0.49    inference(superposition,[],[f44,f99])).
% 0.21/0.49  fof(f99,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl8_16),
% 0.21/0.49    inference(avatar_component_clause,[],[f98])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2)) | ~spl8_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f43])).
% 0.21/0.49  fof(f124,plain,(
% 0.21/0.49    ~spl8_6 | ~spl8_9 | spl8_19),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f121])).
% 0.21/0.49  fof(f121,plain,(
% 0.21/0.49    $false | (~spl8_6 | ~spl8_9 | spl8_19)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f51,f113,f64])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    ( ! [X2,X0,X3] : (r2_hidden(X2,k2_relat_1(X0)) | ~r2_hidden(k4_tarski(X3,X2),X0)) ) | ~spl8_9),
% 0.21/0.49    inference(avatar_component_clause,[],[f63])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    spl8_9 <=> ! [X3,X0,X2] : (~r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,k2_relat_1(X0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.21/0.49  fof(f113,plain,(
% 0.21/0.49    ~r2_hidden(sK3,k2_relat_1(sK2)) | spl8_19),
% 0.21/0.49    inference(avatar_component_clause,[],[f112])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    r2_hidden(k4_tarski(sK4,sK3),sK2) | ~spl8_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f50])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    spl8_6 <=> r2_hidden(k4_tarski(sK4,sK3),sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.21/0.49  fof(f114,plain,(
% 0.21/0.49    ~spl8_19 | ~spl8_3 | spl8_4 | ~spl8_16),
% 0.21/0.49    inference(avatar_split_clause,[],[f110,f98,f43,f39,f112])).
% 0.21/0.49  fof(f110,plain,(
% 0.21/0.49    ~r2_hidden(sK3,k2_relat_1(sK2)) | (~spl8_3 | spl8_4 | ~spl8_16)),
% 0.21/0.49    inference(subsumption_resolution,[],[f109,f40])).
% 0.21/0.49  fof(f109,plain,(
% 0.21/0.49    ~r2_hidden(sK3,k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | (spl8_4 | ~spl8_16)),
% 0.21/0.49    inference(superposition,[],[f53,f99])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    ~r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2)) | spl8_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f43])).
% 0.21/0.49  fof(f100,plain,(
% 0.21/0.49    spl8_16),
% 0.21/0.49    inference(avatar_split_clause,[],[f24,f98])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.49  fof(f81,plain,(
% 0.21/0.49    spl8_13),
% 0.21/0.49    inference(avatar_split_clause,[],[f28,f79])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ( ! [X2,X0] : (r2_hidden(k4_tarski(sK6(X0,X2),X2),X0) | ~r2_hidden(X2,k2_relat_1(X0))) )),
% 0.21/0.49    inference(equality_resolution,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK6(X0,X2),X2),X0) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    spl8_11),
% 0.21/0.49    inference(avatar_split_clause,[],[f25,f71])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    spl8_10),
% 0.21/0.49    inference(avatar_split_clause,[],[f19,f67])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    spl8_9),
% 0.21/0.49    inference(avatar_split_clause,[],[f29,f63])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ( ! [X2,X0,X3] : (~r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,k2_relat_1(X0))) )),
% 0.21/0.49    inference(equality_resolution,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f4])).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    spl8_8),
% 0.21/0.49    inference(avatar_split_clause,[],[f18,f59])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    ~spl8_4 | spl8_7),
% 0.21/0.49    inference(avatar_split_clause,[],[f12,f55,f43])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ( ! [X4] : (~m1_subset_1(X4,sK1) | ~r2_hidden(k4_tarski(X4,sK3),sK2) | ~r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (r2_hidden(X3,k2_relset_1(X1,X0,X2)) <~> ? [X4] : (r2_hidden(k4_tarski(X4,X3),X2) & m1_subset_1(X4,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,negated_conjecture,(
% 0.21/0.49    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ! [X3] : (r2_hidden(X3,k2_relset_1(X1,X0,X2)) <=> ? [X4] : (r2_hidden(k4_tarski(X4,X3),X2) & m1_subset_1(X4,X1))))))),
% 0.21/0.49    inference(negated_conjecture,[],[f6])).
% 0.21/0.49  fof(f6,conjecture,(
% 0.21/0.49    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ! [X3] : (r2_hidden(X3,k2_relset_1(X1,X0,X2)) <=> ? [X4] : (r2_hidden(k4_tarski(X4,X3),X2) & m1_subset_1(X4,X1))))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_relset_1)).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    spl8_4 | spl8_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f14,f50,f43])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    r2_hidden(k4_tarski(sK4,sK3),sK2) | r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2))),
% 0.21/0.49    inference(cnf_transformation,[],[f8])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    spl8_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f15,f39])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.49    inference(cnf_transformation,[],[f8])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (4511)------------------------------
% 0.21/0.49  % (4511)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (4511)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (4511)Memory used [KB]: 10746
% 0.21/0.49  % (4511)Time elapsed: 0.068 s
% 0.21/0.49  % (4511)------------------------------
% 0.21/0.49  % (4511)------------------------------
% 0.21/0.49  % (4504)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.49  % (4505)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.49  % (4506)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.49  % (4499)Success in time 0.128 s
%------------------------------------------------------------------------------
