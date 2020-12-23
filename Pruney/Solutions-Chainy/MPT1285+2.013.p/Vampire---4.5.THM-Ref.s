%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:07 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.41s
% Verified   : 
% Statistics : Number of formulae       :  251 ( 532 expanded)
%              Number of leaves         :   56 ( 243 expanded)
%              Depth                    :   10
%              Number of atoms          :  933 (2682 expanded)
%              Number of equality atoms :   62 ( 114 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f541,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f73,f78,f83,f88,f93,f102,f110,f120,f126,f130,f141,f150,f158,f162,f173,f177,f189,f195,f204,f212,f234,f239,f251,f269,f313,f317,f339,f358,f360,f373,f385,f393,f404,f418,f419,f431,f450,f501,f510,f523,f529,f540])).

fof(f540,plain,
    ( spl8_7
    | ~ spl8_49 ),
    inference(avatar_contradiction_clause,[],[f539])).

fof(f539,plain,
    ( $false
    | spl8_7
    | ~ spl8_49 ),
    inference(subsumption_resolution,[],[f538,f383])).

fof(f383,plain,
    ( v6_tops_1(sK3,sK1)
    | ~ spl8_49 ),
    inference(avatar_component_clause,[],[f382])).

fof(f382,plain,
    ( spl8_49
  <=> v6_tops_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_49])])).

fof(f538,plain,
    ( ~ v6_tops_1(sK3,sK1)
    | spl8_7 ),
    inference(subsumption_resolution,[],[f41,f100])).

fof(f100,plain,
    ( ~ v6_tops_1(sK2,sK0)
    | spl8_7 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl8_7
  <=> v6_tops_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f41,plain,
    ( v6_tops_1(sK2,sK0)
    | ~ v6_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ( ( ( ~ v4_tops_1(sK2,sK0)
          | ~ v3_pre_topc(sK2,sK0) )
        & v6_tops_1(sK2,sK0) )
      | ( ~ v6_tops_1(sK3,sK1)
        & v4_tops_1(sK3,sK1)
        & v3_pre_topc(sK3,sK1) ) )
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f27,f26,f25,f24])).

fof(f24,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ( ( ~ v4_tops_1(X2,X0)
                          | ~ v3_pre_topc(X2,X0) )
                        & v6_tops_1(X2,X0) )
                      | ( ~ v6_tops_1(X3,X1)
                        & v4_tops_1(X3,X1)
                        & v3_pre_topc(X3,X1) ) )
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & l1_pre_topc(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( ~ v4_tops_1(X2,sK0)
                        | ~ v3_pre_topc(X2,sK0) )
                      & v6_tops_1(X2,sK0) )
                    | ( ~ v6_tops_1(X3,X1)
                      & v4_tops_1(X3,X1)
                      & v3_pre_topc(X3,X1) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ( ( ~ v4_tops_1(X2,sK0)
                      | ~ v3_pre_topc(X2,sK0) )
                    & v6_tops_1(X2,sK0) )
                  | ( ~ v6_tops_1(X3,X1)
                    & v4_tops_1(X3,X1)
                    & v3_pre_topc(X3,X1) ) )
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & l1_pre_topc(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ( ( ~ v4_tops_1(X2,sK0)
                    | ~ v3_pre_topc(X2,sK0) )
                  & v6_tops_1(X2,sK0) )
                | ( ~ v6_tops_1(X3,sK1)
                  & v4_tops_1(X3,sK1)
                  & v3_pre_topc(X3,sK1) ) )
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ( ( ~ v4_tops_1(X2,sK0)
                  | ~ v3_pre_topc(X2,sK0) )
                & v6_tops_1(X2,sK0) )
              | ( ~ v6_tops_1(X3,sK1)
                & v4_tops_1(X3,sK1)
                & v3_pre_topc(X3,sK1) ) )
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X3] :
          ( ( ( ( ~ v4_tops_1(sK2,sK0)
                | ~ v3_pre_topc(sK2,sK0) )
              & v6_tops_1(sK2,sK0) )
            | ( ~ v6_tops_1(X3,sK1)
              & v4_tops_1(X3,sK1)
              & v3_pre_topc(X3,sK1) ) )
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X3] :
        ( ( ( ( ~ v4_tops_1(sK2,sK0)
              | ~ v3_pre_topc(sK2,sK0) )
            & v6_tops_1(sK2,sK0) )
          | ( ~ v6_tops_1(X3,sK1)
            & v4_tops_1(X3,sK1)
            & v3_pre_topc(X3,sK1) ) )
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
   => ( ( ( ( ~ v4_tops_1(sK2,sK0)
            | ~ v3_pre_topc(sK2,sK0) )
          & v6_tops_1(sK2,sK0) )
        | ( ~ v6_tops_1(sK3,sK1)
          & v4_tops_1(sK3,sK1)
          & v3_pre_topc(sK3,sK1) ) )
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( ~ v4_tops_1(X2,X0)
                        | ~ v3_pre_topc(X2,X0) )
                      & v6_tops_1(X2,X0) )
                    | ( ~ v6_tops_1(X3,X1)
                      & v4_tops_1(X3,X1)
                      & v3_pre_topc(X3,X1) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( ~ v4_tops_1(X2,X0)
                        | ~ v3_pre_topc(X2,X0) )
                      & v6_tops_1(X2,X0) )
                    | ( ~ v6_tops_1(X3,X1)
                      & v4_tops_1(X3,X1)
                      & v3_pre_topc(X3,X1) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( ( v6_tops_1(X2,X0)
                       => ( v4_tops_1(X2,X0)
                          & v3_pre_topc(X2,X0) ) )
                      & ( ( v4_tops_1(X3,X1)
                          & v3_pre_topc(X3,X1) )
                       => v6_tops_1(X3,X1) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( v6_tops_1(X2,X0)
                     => ( v4_tops_1(X2,X0)
                        & v3_pre_topc(X2,X0) ) )
                    & ( ( v4_tops_1(X3,X1)
                        & v3_pre_topc(X3,X1) )
                     => v6_tops_1(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_tops_1)).

% (23636)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% (23641)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% (23634)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% (23642)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% (23648)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% (23643)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% (23623)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
fof(f529,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | ~ spl8_11
    | ~ spl8_12 ),
    inference(avatar_contradiction_clause,[],[f528])).

fof(f528,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_11
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f527,f77])).

fof(f77,plain,
    ( l1_pre_topc(sK0)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl8_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f527,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl8_1
    | ~ spl8_11
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f525,f125])).

fof(f125,plain,
    ( sP6(sK0)
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl8_12
  <=> sP6(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f525,plain,
    ( ~ sP6(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl8_1
    | ~ spl8_11 ),
    inference(resolution,[],[f119,f72])).

fof(f72,plain,
    ( v2_pre_topc(sK0)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f70])).

% (23645)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
fof(f70,plain,
    ( spl8_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f119,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(X0)
        | ~ sP6(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl8_11
  <=> ! [X0] :
        ( ~ l1_pre_topc(X0)
        | ~ sP6(X0)
        | ~ v2_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f523,plain,
    ( ~ spl8_3
    | ~ spl8_5
    | spl8_49
    | ~ spl8_54 ),
    inference(avatar_contradiction_clause,[],[f522])).

fof(f522,plain,
    ( $false
    | ~ spl8_3
    | ~ spl8_5
    | spl8_49
    | ~ spl8_54 ),
    inference(subsumption_resolution,[],[f521,f82])).

fof(f82,plain,
    ( l1_pre_topc(sK1)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl8_3
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f521,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ spl8_5
    | spl8_49
    | ~ spl8_54 ),
    inference(subsumption_resolution,[],[f520,f92])).

fof(f92,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl8_5
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f520,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | spl8_49
    | ~ spl8_54 ),
    inference(subsumption_resolution,[],[f518,f384])).

fof(f384,plain,
    ( ~ v6_tops_1(sK3,sK1)
    | spl8_49 ),
    inference(avatar_component_clause,[],[f382])).

fof(f518,plain,
    ( v6_tops_1(sK3,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | ~ spl8_54 ),
    inference(trivial_inequality_removal,[],[f516])).

fof(f516,plain,
    ( sK3 != sK3
    | v6_tops_1(sK3,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | ~ spl8_54 ),
    inference(superposition,[],[f47,f445])).

fof(f445,plain,
    ( sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3))
    | ~ spl8_54 ),
    inference(avatar_component_clause,[],[f443])).

fof(f443,plain,
    ( spl8_54
  <=> sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_54])])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1
      | v6_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v6_tops_1(X1,X0)
              | k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1 )
            & ( k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1
              | ~ v6_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v6_tops_1(X1,X0)
          <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v6_tops_1(X1,X0)
          <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_tops_1)).

fof(f510,plain,
    ( ~ spl8_5
    | ~ spl8_21
    | spl8_55
    | ~ spl8_63 ),
    inference(avatar_contradiction_clause,[],[f509])).

fof(f509,plain,
    ( $false
    | ~ spl8_5
    | ~ spl8_21
    | spl8_55
    | ~ spl8_63 ),
    inference(subsumption_resolution,[],[f508,f92])).

fof(f508,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl8_21
    | spl8_55
    | ~ spl8_63 ),
    inference(subsumption_resolution,[],[f506,f449])).

fof(f449,plain,
    ( ~ r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3)))
    | spl8_55 ),
    inference(avatar_component_clause,[],[f447])).

fof(f447,plain,
    ( spl8_55
  <=> r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_55])])).

fof(f506,plain,
    ( r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl8_21
    | ~ spl8_63 ),
    inference(resolution,[],[f500,f188])).

fof(f188,plain,
    ( r1_tarski(sK3,k2_pre_topc(sK1,sK3))
    | ~ spl8_21 ),
    inference(avatar_component_clause,[],[f186])).

fof(f186,plain,
    ( spl8_21
  <=> r1_tarski(sK3,k2_pre_topc(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f500,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK3,k2_pre_topc(sK1,X0))
        | r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,X0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) )
    | ~ spl8_63 ),
    inference(avatar_component_clause,[],[f499])).

fof(f499,plain,
    ( spl8_63
  <=> ! [X0] :
        ( ~ r1_tarski(sK3,k2_pre_topc(sK1,X0))
        | r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,X0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_63])])).

fof(f501,plain,
    ( spl8_63
    | ~ spl8_3
    | ~ spl8_53 ),
    inference(avatar_split_clause,[],[f441,f429,f80,f499])).

fof(f429,plain,
    ( spl8_53
  <=> ! [X0] :
        ( r1_tarski(sK3,k1_tops_1(sK1,X0))
        | ~ r1_tarski(sK3,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_53])])).

fof(f441,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK3,k2_pre_topc(sK1,X0))
        | r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,X0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) )
    | ~ spl8_3
    | ~ spl8_53 ),
    inference(subsumption_resolution,[],[f438,f82])).

fof(f438,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK3,k2_pre_topc(sK1,X0))
        | r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,X0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_pre_topc(sK1) )
    | ~ spl8_53 ),
    inference(resolution,[],[f430,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f430,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ r1_tarski(sK3,X0)
        | r1_tarski(sK3,k1_tops_1(sK1,X0)) )
    | ~ spl8_53 ),
    inference(avatar_component_clause,[],[f429])).

fof(f450,plain,
    ( spl8_54
    | ~ spl8_55
    | ~ spl8_51 ),
    inference(avatar_split_clause,[],[f422,f415,f447,f443])).

fof(f415,plain,
    ( spl8_51
  <=> r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_51])])).

fof(f422,plain,
    ( ~ r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3)))
    | sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3))
    | ~ spl8_51 ),
    inference(resolution,[],[f417,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f417,plain,
    ( r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3)
    | ~ spl8_51 ),
    inference(avatar_component_clause,[],[f415])).

fof(f431,plain,
    ( spl8_53
    | ~ spl8_24
    | ~ spl8_42 ),
    inference(avatar_split_clause,[],[f400,f315,f209,f429])).

fof(f209,plain,
    ( spl8_24
  <=> sK3 = k1_tops_1(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f315,plain,
    ( spl8_42
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ r1_tarski(sK3,X0)
        | r1_tarski(k1_tops_1(sK1,sK3),k1_tops_1(sK1,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_42])])).

fof(f400,plain,
    ( ! [X0] :
        ( r1_tarski(sK3,k1_tops_1(sK1,X0))
        | ~ r1_tarski(sK3,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) )
    | ~ spl8_24
    | ~ spl8_42 ),
    inference(backward_demodulation,[],[f316,f211])).

fof(f211,plain,
    ( sK3 = k1_tops_1(sK1,sK3)
    | ~ spl8_24 ),
    inference(avatar_component_clause,[],[f209])).

fof(f316,plain,
    ( ! [X0] :
        ( r1_tarski(k1_tops_1(sK1,sK3),k1_tops_1(sK1,X0))
        | ~ r1_tarski(sK3,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) )
    | ~ spl8_42 ),
    inference(avatar_component_clause,[],[f315])).

fof(f419,plain,
    ( spl8_15
    | ~ spl8_41
    | ~ spl8_48 ),
    inference(avatar_split_clause,[],[f409,f353,f310,f143])).

fof(f143,plain,
    ( spl8_15
  <=> v3_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f310,plain,
    ( spl8_41
  <=> v3_pre_topc(k1_tops_1(sK0,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_41])])).

fof(f353,plain,
    ( spl8_48
  <=> sK2 = k1_tops_1(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_48])])).

fof(f409,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ spl8_41
    | ~ spl8_48 ),
    inference(backward_demodulation,[],[f312,f355])).

fof(f355,plain,
    ( sK2 = k1_tops_1(sK0,sK2)
    | ~ spl8_48 ),
    inference(avatar_component_clause,[],[f353])).

fof(f312,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
    | ~ spl8_41 ),
    inference(avatar_component_clause,[],[f310])).

fof(f418,plain,
    ( spl8_51
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_23 ),
    inference(avatar_split_clause,[],[f399,f201,f90,f80,f415])).

fof(f201,plain,
    ( spl8_23
  <=> v4_tops_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f399,plain,
    ( r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3)
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_23 ),
    inference(subsumption_resolution,[],[f398,f82])).

fof(f398,plain,
    ( r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3)
    | ~ l1_pre_topc(sK1)
    | ~ spl8_5
    | ~ spl8_23 ),
    inference(subsumption_resolution,[],[f395,f92])).

fof(f395,plain,
    ( r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | ~ spl8_23 ),
    inference(resolution,[],[f203,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v4_tops_1(X1,X0)
      | r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_tops_1(X1,X0)
              | ~ r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              | ~ r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) )
            & ( ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
                & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) )
              | ~ v4_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_tops_1(X1,X0)
              | ~ r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              | ~ r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) )
            & ( ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
                & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) )
              | ~ v4_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_tops_1(X1,X0)
          <=> ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_tops_1(X1,X0)
          <=> ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_tops_1)).

fof(f203,plain,
    ( v4_tops_1(sK3,sK1)
    | ~ spl8_23 ),
    inference(avatar_component_clause,[],[f201])).

fof(f404,plain,
    ( spl8_48
    | ~ spl8_4
    | ~ spl8_22
    | ~ spl8_30
    | ~ spl8_46 ),
    inference(avatar_split_clause,[],[f350,f337,f248,f192,f85,f353])).

fof(f85,plain,
    ( spl8_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f192,plain,
    ( spl8_22
  <=> sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f248,plain,
    ( spl8_30
  <=> k1_tops_1(sK0,sK2) = k1_tops_1(sK0,k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).

fof(f337,plain,
    ( spl8_46
  <=> ! [X0] :
        ( k1_tops_1(sK0,k2_pre_topc(sK0,X0)) = k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,X0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_46])])).

fof(f350,plain,
    ( sK2 = k1_tops_1(sK0,sK2)
    | ~ spl8_4
    | ~ spl8_22
    | ~ spl8_30
    | ~ spl8_46 ),
    inference(backward_demodulation,[],[f250,f346])).

fof(f346,plain,
    ( sK2 = k1_tops_1(sK0,sK2)
    | ~ spl8_4
    | ~ spl8_22
    | ~ spl8_46 ),
    inference(forward_demodulation,[],[f344,f194])).

fof(f194,plain,
    ( sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2))
    | ~ spl8_22 ),
    inference(avatar_component_clause,[],[f192])).

fof(f344,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) = k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK2)))
    | ~ spl8_4
    | ~ spl8_46 ),
    inference(resolution,[],[f338,f87])).

fof(f87,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f85])).

fof(f338,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_tops_1(sK0,k2_pre_topc(sK0,X0)) = k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,X0))) )
    | ~ spl8_46 ),
    inference(avatar_component_clause,[],[f337])).

fof(f250,plain,
    ( k1_tops_1(sK0,sK2) = k1_tops_1(sK0,k1_tops_1(sK0,sK2))
    | ~ spl8_30 ),
    inference(avatar_component_clause,[],[f248])).

fof(f393,plain,
    ( spl8_23
    | ~ spl8_15
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f377,f147,f143,f201])).

fof(f147,plain,
    ( spl8_16
  <=> v4_tops_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f377,plain,
    ( ~ v3_pre_topc(sK2,sK0)
    | v4_tops_1(sK3,sK1)
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f43,f148])).

fof(f148,plain,
    ( v4_tops_1(sK2,sK0)
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f147])).

fof(f43,plain,
    ( ~ v4_tops_1(sK2,sK0)
    | ~ v3_pre_topc(sK2,sK0)
    | v4_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f385,plain,
    ( ~ spl8_49
    | ~ spl8_15
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f376,f147,f143,f382])).

fof(f376,plain,
    ( ~ v3_pre_topc(sK2,sK0)
    | ~ v6_tops_1(sK3,sK1)
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f44,f148])).

fof(f44,plain,
    ( ~ v4_tops_1(sK2,sK0)
    | ~ v3_pre_topc(sK2,sK0)
    | ~ v6_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f373,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | ~ spl8_9
    | ~ spl8_39 ),
    inference(avatar_contradiction_clause,[],[f372])).

fof(f372,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_9
    | ~ spl8_39 ),
    inference(subsumption_resolution,[],[f371,f72])).

fof(f371,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ spl8_2
    | ~ spl8_9
    | ~ spl8_39 ),
    inference(subsumption_resolution,[],[f369,f77])).

fof(f369,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl8_9
    | ~ spl8_39 ),
    inference(resolution,[],[f304,f109])).

fof(f109,plain,
    ( ! [X0] :
        ( ~ sP4(X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl8_9
  <=> ! [X0] :
        ( ~ l1_pre_topc(X0)
        | ~ sP4(X0)
        | ~ v2_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f304,plain,
    ( sP4(sK0)
    | ~ spl8_39 ),
    inference(avatar_component_clause,[],[f302])).

fof(f302,plain,
    ( spl8_39
  <=> sP4(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_39])])).

fof(f360,plain,
    ( ~ spl8_4
    | ~ spl8_19
    | ~ spl8_22
    | spl8_28
    | ~ spl8_46 ),
    inference(avatar_contradiction_clause,[],[f359])).

fof(f359,plain,
    ( $false
    | ~ spl8_4
    | ~ spl8_19
    | ~ spl8_22
    | spl8_28
    | ~ spl8_46 ),
    inference(subsumption_resolution,[],[f351,f172])).

fof(f172,plain,
    ( r1_tarski(sK2,k2_pre_topc(sK0,sK2))
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f170])).

fof(f170,plain,
    ( spl8_19
  <=> r1_tarski(sK2,k2_pre_topc(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f351,plain,
    ( ~ r1_tarski(sK2,k2_pre_topc(sK0,sK2))
    | ~ spl8_4
    | ~ spl8_22
    | spl8_28
    | ~ spl8_46 ),
    inference(backward_demodulation,[],[f238,f346])).

fof(f238,plain,
    ( ~ r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2)))
    | spl8_28 ),
    inference(avatar_component_clause,[],[f236])).

fof(f236,plain,
    ( spl8_28
  <=> r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f358,plain,
    ( ~ spl8_4
    | ~ spl8_22
    | spl8_40
    | ~ spl8_46 ),
    inference(avatar_contradiction_clause,[],[f357])).

fof(f357,plain,
    ( $false
    | ~ spl8_4
    | ~ spl8_22
    | spl8_40
    | ~ spl8_46 ),
    inference(subsumption_resolution,[],[f349,f87])).

fof(f349,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_4
    | ~ spl8_22
    | spl8_40
    | ~ spl8_46 ),
    inference(backward_demodulation,[],[f308,f346])).

fof(f308,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl8_40 ),
    inference(avatar_component_clause,[],[f306])).

fof(f306,plain,
    ( spl8_40
  <=> m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_40])])).

fof(f339,plain,
    ( spl8_46
    | ~ spl8_2
    | ~ spl8_27 ),
    inference(avatar_split_clause,[],[f246,f232,f75,f337])).

fof(f232,plain,
    ( spl8_27
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_tops_1(sK0,X0) = k1_tops_1(sK0,k1_tops_1(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).

fof(f246,plain,
    ( ! [X0] :
        ( k1_tops_1(sK0,k2_pre_topc(sK0,X0)) = k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,X0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl8_2
    | ~ spl8_27 ),
    inference(subsumption_resolution,[],[f245,f77])).

fof(f245,plain,
    ( ! [X0] :
        ( k1_tops_1(sK0,k2_pre_topc(sK0,X0)) = k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,X0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl8_27 ),
    inference(resolution,[],[f233,f54])).

fof(f233,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_tops_1(sK0,X0) = k1_tops_1(sK0,k1_tops_1(sK0,X0)) )
    | ~ spl8_27 ),
    inference(avatar_component_clause,[],[f232])).

fof(f317,plain,
    ( spl8_42
    | ~ spl8_5
    | ~ spl8_33 ),
    inference(avatar_split_clause,[],[f284,f267,f90,f315])).

fof(f267,plain,
    ( spl8_33
  <=> ! [X3,X2] :
        ( ~ r1_tarski(X2,X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
        | r1_tarski(k1_tops_1(sK1,X2),k1_tops_1(sK1,X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).

fof(f284,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ r1_tarski(sK3,X0)
        | r1_tarski(k1_tops_1(sK1,sK3),k1_tops_1(sK1,X0)) )
    | ~ spl8_5
    | ~ spl8_33 ),
    inference(resolution,[],[f268,f92])).

fof(f268,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ r1_tarski(X2,X3)
        | r1_tarski(k1_tops_1(sK1,X2),k1_tops_1(sK1,X3)) )
    | ~ spl8_33 ),
    inference(avatar_component_clause,[],[f267])).

fof(f313,plain,
    ( spl8_39
    | ~ spl8_40
    | spl8_41
    | ~ spl8_30 ),
    inference(avatar_split_clause,[],[f256,f248,f310,f306,f302])).

fof(f256,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
    | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | sP4(sK0)
    | ~ spl8_30 ),
    inference(trivial_inequality_removal,[],[f255])).

fof(f255,plain,
    ( k1_tops_1(sK0,sK2) != k1_tops_1(sK0,sK2)
    | v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
    | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | sP4(sK0)
    | ~ spl8_30 ),
    inference(superposition,[],[f61,f250])).

fof(f61,plain,(
    ! [X2,X0] :
      ( k1_tops_1(X0,X2) != X2
      | v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | sP4(X0) ) ),
    inference(cnf_transformation,[],[f61_D])).

fof(f61_D,plain,(
    ! [X0] :
      ( ! [X2] :
          ( k1_tops_1(X0,X2) != X2
          | v3_pre_topc(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
    <=> ~ sP4(X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP4])])).

fof(f269,plain,
    ( spl8_33
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f217,f80,f267])).

fof(f217,plain,
    ( ! [X2,X3] :
        ( ~ r1_tarski(X2,X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
        | r1_tarski(k1_tops_1(sK1,X2),k1_tops_1(sK1,X3)) )
    | ~ spl8_3 ),
    inference(resolution,[],[f51,f82])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

fof(f251,plain,
    ( spl8_30
    | ~ spl8_4
    | ~ spl8_27 ),
    inference(avatar_split_clause,[],[f244,f232,f85,f248])).

fof(f244,plain,
    ( k1_tops_1(sK0,sK2) = k1_tops_1(sK0,k1_tops_1(sK0,sK2))
    | ~ spl8_4
    | ~ spl8_27 ),
    inference(resolution,[],[f233,f87])).

fof(f239,plain,
    ( spl8_16
    | ~ spl8_28
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_22 ),
    inference(avatar_split_clause,[],[f230,f192,f85,f75,f236,f147])).

fof(f230,plain,
    ( ~ r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2)))
    | v4_tops_1(sK2,sK0)
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_22 ),
    inference(subsumption_resolution,[],[f229,f77])).

fof(f229,plain,
    ( ~ r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2)))
    | v4_tops_1(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl8_4
    | ~ spl8_22 ),
    inference(subsumption_resolution,[],[f228,f87])).

fof(f228,plain,
    ( ~ r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2)))
    | v4_tops_1(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl8_22 ),
    inference(subsumption_resolution,[],[f227,f59])).

fof(f59,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f227,plain,
    ( ~ r1_tarski(sK2,sK2)
    | ~ r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2)))
    | v4_tops_1(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl8_22 ),
    inference(superposition,[],[f50,f194])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)
      | ~ r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
      | v4_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f234,plain,
    ( spl8_27
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f163,f75,f232])).

fof(f163,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_tops_1(sK0,X0) = k1_tops_1(sK0,k1_tops_1(sK0,X0)) )
    | ~ spl8_2 ),
    inference(resolution,[],[f55,f77])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',projectivity_k1_tops_1)).

fof(f212,plain,
    ( spl8_24
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_20 ),
    inference(avatar_split_clause,[],[f198,f175,f95,f90,f80,f209])).

fof(f95,plain,
    ( spl8_6
  <=> v3_pre_topc(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f175,plain,
    ( spl8_20
  <=> ! [X1,X3] :
        ( k1_tops_1(X1,X3) = X3
        | ~ v3_pre_topc(X3,X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ l1_pre_topc(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f198,plain,
    ( sK3 = k1_tops_1(sK1,sK3)
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f197,f82])).

fof(f197,plain,
    ( sK3 = k1_tops_1(sK1,sK3)
    | ~ l1_pre_topc(sK1)
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f196,f92])).

fof(f196,plain,
    ( sK3 = k1_tops_1(sK1,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | ~ spl8_6
    | ~ spl8_20 ),
    inference(resolution,[],[f97,f176])).

fof(f176,plain,
    ( ! [X3,X1] :
        ( ~ v3_pre_topc(X3,X1)
        | k1_tops_1(X1,X3) = X3
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ l1_pre_topc(X1) )
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f175])).

fof(f97,plain,
    ( v3_pre_topc(sK3,sK1)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f95])).

fof(f204,plain,
    ( spl8_23
    | spl8_7 ),
    inference(avatar_split_clause,[],[f199,f99,f201])).

fof(f199,plain,
    ( v4_tops_1(sK3,sK1)
    | spl8_7 ),
    inference(subsumption_resolution,[],[f40,f100])).

fof(f40,plain,
    ( v6_tops_1(sK2,sK0)
    | v4_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f195,plain,
    ( spl8_22
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f184,f99,f85,f75,f192])).

fof(f184,plain,
    ( sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2))
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f183,f77])).

fof(f183,plain,
    ( sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2))
    | ~ l1_pre_topc(sK0)
    | ~ spl8_4
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f182,f87])).

fof(f182,plain,
    ( sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl8_7 ),
    inference(resolution,[],[f46,f101])).

fof(f101,plain,
    ( v6_tops_1(sK2,sK0)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f99])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v6_tops_1(X1,X0)
      | k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f189,plain,
    ( spl8_21
    | ~ spl8_5
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f179,f160,f90,f186])).

fof(f160,plain,
    ( spl8_18
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
        | r1_tarski(X1,k2_pre_topc(sK1,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f179,plain,
    ( r1_tarski(sK3,k2_pre_topc(sK1,sK3))
    | ~ spl8_5
    | ~ spl8_18 ),
    inference(resolution,[],[f161,f92])).

fof(f161,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
        | r1_tarski(X1,k2_pre_topc(sK1,X1)) )
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f160])).

fof(f177,plain,
    ( spl8_20
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f168,f114,f175])).

fof(f114,plain,
    ( spl8_10
  <=> sP7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f168,plain,
    ( ! [X3,X1] :
        ( k1_tops_1(X1,X3) = X3
        | ~ v3_pre_topc(X3,X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ l1_pre_topc(X1) )
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f68,f116])).

fof(f116,plain,
    ( sP7
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f114])).

fof(f68,plain,(
    ! [X3,X1] :
      ( k1_tops_1(X1,X3) = X3
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ sP7 ) ),
    inference(general_splitting,[],[f66,f67_D])).

fof(f67,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ sP6(X0)
      | sP7 ) ),
    inference(cnf_transformation,[],[f67_D])).

fof(f67_D,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | ~ sP6(X0) )
  <=> ~ sP7 ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP7])])).

fof(f66,plain,(
    ! [X0,X3,X1] :
      ( k1_tops_1(X1,X3) = X3
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ sP6(X0) ) ),
    inference(general_splitting,[],[f52,f65_D])).

fof(f65,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | sP6(X0) ) ),
    inference(cnf_transformation,[],[f65_D])).

fof(f65_D,plain,(
    ! [X0] :
      ( ! [X2] : ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    <=> ~ sP6(X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP6])])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_tops_1(X1,X3) = X3
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( k1_tops_1(X0,X2) = X2
                     => v3_pre_topc(X2,X0) )
                    & ( v3_pre_topc(X3,X1)
                     => k1_tops_1(X1,X3) = X3 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).

fof(f173,plain,
    ( spl8_19
    | ~ spl8_4
    | ~ spl8_17 ),
    inference(avatar_split_clause,[],[f165,f156,f85,f170])).

fof(f156,plain,
    ( spl8_17
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(X0,k2_pre_topc(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f165,plain,
    ( r1_tarski(sK2,k2_pre_topc(sK0,sK2))
    | ~ spl8_4
    | ~ spl8_17 ),
    inference(resolution,[],[f157,f87])).

fof(f157,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(X0,k2_pre_topc(sK0,X0)) )
    | ~ spl8_17 ),
    inference(avatar_component_clause,[],[f156])).

fof(f162,plain,
    ( spl8_18
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f153,f80,f160])).

fof(f153,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
        | r1_tarski(X1,k2_pre_topc(sK1,X1)) )
    | ~ spl8_3 ),
    inference(resolution,[],[f45,f82])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(X1,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

fof(f158,plain,
    ( spl8_17
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f152,f75,f156])).

fof(f152,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(X0,k2_pre_topc(sK0,X0)) )
    | ~ spl8_2 ),
    inference(resolution,[],[f45,f77])).

fof(f150,plain,
    ( spl8_6
    | ~ spl8_15
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f42,f147,f143,f95])).

fof(f42,plain,
    ( ~ v4_tops_1(sK2,sK0)
    | ~ v3_pre_topc(sK2,sK0)
    | v3_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f141,plain,
    ( ~ spl8_3
    | ~ spl8_5
    | ~ spl8_13 ),
    inference(avatar_contradiction_clause,[],[f137])).

fof(f137,plain,
    ( $false
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_13 ),
    inference(unit_resulting_resolution,[],[f82,f92,f129])).

fof(f129,plain,
    ( ! [X3,X1] :
        ( ~ l1_pre_topc(X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl8_13
  <=> ! [X1,X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ l1_pre_topc(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f130,plain,
    ( spl8_13
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f121,f104,f128])).

fof(f104,plain,
    ( spl8_8
  <=> sP5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f121,plain,
    ( ! [X3,X1] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ l1_pre_topc(X1) )
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f64,f106])).

fof(f106,plain,
    ( sP5
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f104])).

fof(f64,plain,(
    ! [X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ sP5 ) ),
    inference(general_splitting,[],[f62,f63_D])).

fof(f63,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ sP4(X0)
      | sP5 ) ),
    inference(cnf_transformation,[],[f63_D])).

fof(f63_D,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | ~ sP4(X0) )
  <=> ~ sP5 ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP5])])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ sP4(X0) ) ),
    inference(general_splitting,[],[f53,f61_D])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X2,X0)
      | k1_tops_1(X0,X2) != X2
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f126,plain,
    ( spl8_12
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f111,f85,f123])).

fof(f111,plain,
    ( sP6(sK0)
    | ~ spl8_4 ),
    inference(resolution,[],[f65,f87])).

fof(f120,plain,
    ( spl8_10
    | spl8_11 ),
    inference(avatar_split_clause,[],[f67,f118,f114])).

fof(f110,plain,
    ( spl8_8
    | spl8_9 ),
    inference(avatar_split_clause,[],[f63,f108,f104])).

fof(f102,plain,
    ( spl8_6
    | spl8_7 ),
    inference(avatar_split_clause,[],[f39,f99,f95])).

fof(f39,plain,
    ( v6_tops_1(sK2,sK0)
    | v3_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f93,plain,(
    spl8_5 ),
    inference(avatar_split_clause,[],[f38,f90])).

fof(f38,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f28])).

fof(f88,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f37,f85])).

fof(f37,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f28])).

fof(f83,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f36,f80])).

fof(f36,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f78,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f35,f75])).

fof(f35,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f73,plain,(
    spl8_1 ),
    inference(avatar_split_clause,[],[f34,f70])).

fof(f34,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:14:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.51  % (23627)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (23625)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.51  % (23637)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.51  % (23639)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.52  % (23628)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.52  % (23633)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.52  % (23624)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (23631)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.52  % (23638)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.52  % (23624)Refutation not found, incomplete strategy% (23624)------------------------------
% 0.21/0.52  % (23624)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (23624)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (23624)Memory used [KB]: 10618
% 0.21/0.52  % (23624)Time elapsed: 0.100 s
% 0.21/0.52  % (23624)------------------------------
% 0.21/0.52  % (23624)------------------------------
% 0.21/0.52  % (23632)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.52  % (23626)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.52  % (23630)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.52  % (23629)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.53  % (23647)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.53  % (23646)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.53  % (23625)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f541,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f73,f78,f83,f88,f93,f102,f110,f120,f126,f130,f141,f150,f158,f162,f173,f177,f189,f195,f204,f212,f234,f239,f251,f269,f313,f317,f339,f358,f360,f373,f385,f393,f404,f418,f419,f431,f450,f501,f510,f523,f529,f540])).
% 0.21/0.53  fof(f540,plain,(
% 0.21/0.53    spl8_7 | ~spl8_49),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f539])).
% 0.21/0.53  fof(f539,plain,(
% 0.21/0.53    $false | (spl8_7 | ~spl8_49)),
% 0.21/0.53    inference(subsumption_resolution,[],[f538,f383])).
% 0.21/0.53  fof(f383,plain,(
% 0.21/0.53    v6_tops_1(sK3,sK1) | ~spl8_49),
% 0.21/0.53    inference(avatar_component_clause,[],[f382])).
% 0.21/0.53  fof(f382,plain,(
% 0.21/0.53    spl8_49 <=> v6_tops_1(sK3,sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_49])])).
% 0.21/0.53  fof(f538,plain,(
% 0.21/0.53    ~v6_tops_1(sK3,sK1) | spl8_7),
% 0.21/0.53    inference(subsumption_resolution,[],[f41,f100])).
% 0.21/0.53  fof(f100,plain,(
% 0.21/0.53    ~v6_tops_1(sK2,sK0) | spl8_7),
% 0.21/0.53    inference(avatar_component_clause,[],[f99])).
% 0.21/0.53  fof(f99,plain,(
% 0.21/0.53    spl8_7 <=> v6_tops_1(sK2,sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    v6_tops_1(sK2,sK0) | ~v6_tops_1(sK3,sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ((((((~v4_tops_1(sK2,sK0) | ~v3_pre_topc(sK2,sK0)) & v6_tops_1(sK2,sK0)) | (~v6_tops_1(sK3,sK1) & v4_tops_1(sK3,sK1) & v3_pre_topc(sK3,sK1))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f27,f26,f25,f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | (~v6_tops_1(X3,X1) & v4_tops_1(X3,X1) & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,sK0) | ~v3_pre_topc(X2,sK0)) & v6_tops_1(X2,sK0)) | (~v6_tops_1(X3,X1) & v4_tops_1(X3,X1) & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,sK0) | ~v3_pre_topc(X2,sK0)) & v6_tops_1(X2,sK0)) | (~v6_tops_1(X3,X1) & v4_tops_1(X3,X1) & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(X1)) => (? [X2] : (? [X3] : ((((~v4_tops_1(X2,sK0) | ~v3_pre_topc(X2,sK0)) & v6_tops_1(X2,sK0)) | (~v6_tops_1(X3,sK1) & v4_tops_1(X3,sK1) & v3_pre_topc(X3,sK1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK1))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ? [X2] : (? [X3] : ((((~v4_tops_1(X2,sK0) | ~v3_pre_topc(X2,sK0)) & v6_tops_1(X2,sK0)) | (~v6_tops_1(X3,sK1) & v4_tops_1(X3,sK1) & v3_pre_topc(X3,sK1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X3] : ((((~v4_tops_1(sK2,sK0) | ~v3_pre_topc(sK2,sK0)) & v6_tops_1(sK2,sK0)) | (~v6_tops_1(X3,sK1) & v4_tops_1(X3,sK1) & v3_pre_topc(X3,sK1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ? [X3] : ((((~v4_tops_1(sK2,sK0) | ~v3_pre_topc(sK2,sK0)) & v6_tops_1(sK2,sK0)) | (~v6_tops_1(X3,sK1) & v4_tops_1(X3,sK1) & v3_pre_topc(X3,sK1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) => ((((~v4_tops_1(sK2,sK0) | ~v3_pre_topc(sK2,sK0)) & v6_tops_1(sK2,sK0)) | (~v6_tops_1(sK3,sK1) & v4_tops_1(sK3,sK1) & v3_pre_topc(sK3,sK1))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f12,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | (~v6_tops_1(X3,X1) & v4_tops_1(X3,X1) & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f11])).
% 0.21/0.53  fof(f11,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | (~v6_tops_1(X3,X1) & (v4_tops_1(X3,X1) & v3_pre_topc(X3,X1)))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,negated_conjecture,(
% 0.21/0.53    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v6_tops_1(X2,X0) => (v4_tops_1(X2,X0) & v3_pre_topc(X2,X0))) & ((v4_tops_1(X3,X1) & v3_pre_topc(X3,X1)) => v6_tops_1(X3,X1)))))))),
% 0.21/0.53    inference(negated_conjecture,[],[f9])).
% 0.21/0.53  fof(f9,conjecture,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v6_tops_1(X2,X0) => (v4_tops_1(X2,X0) & v3_pre_topc(X2,X0))) & ((v4_tops_1(X3,X1) & v3_pre_topc(X3,X1)) => v6_tops_1(X3,X1)))))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_tops_1)).
% 0.21/0.53  % (23636)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (23641)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.53  % (23634)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.53  % (23642)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.53  % (23648)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.41/0.54  % (23643)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.41/0.54  % (23623)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.41/0.54  fof(f529,plain,(
% 1.41/0.54    ~spl8_1 | ~spl8_2 | ~spl8_11 | ~spl8_12),
% 1.41/0.54    inference(avatar_contradiction_clause,[],[f528])).
% 1.41/0.54  fof(f528,plain,(
% 1.41/0.54    $false | (~spl8_1 | ~spl8_2 | ~spl8_11 | ~spl8_12)),
% 1.41/0.54    inference(subsumption_resolution,[],[f527,f77])).
% 1.41/0.54  fof(f77,plain,(
% 1.41/0.54    l1_pre_topc(sK0) | ~spl8_2),
% 1.41/0.54    inference(avatar_component_clause,[],[f75])).
% 1.41/0.54  fof(f75,plain,(
% 1.41/0.54    spl8_2 <=> l1_pre_topc(sK0)),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 1.41/0.54  fof(f527,plain,(
% 1.41/0.54    ~l1_pre_topc(sK0) | (~spl8_1 | ~spl8_11 | ~spl8_12)),
% 1.41/0.54    inference(subsumption_resolution,[],[f525,f125])).
% 1.41/0.54  fof(f125,plain,(
% 1.41/0.54    sP6(sK0) | ~spl8_12),
% 1.41/0.54    inference(avatar_component_clause,[],[f123])).
% 1.41/0.54  fof(f123,plain,(
% 1.41/0.54    spl8_12 <=> sP6(sK0)),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 1.41/0.54  fof(f525,plain,(
% 1.41/0.54    ~sP6(sK0) | ~l1_pre_topc(sK0) | (~spl8_1 | ~spl8_11)),
% 1.41/0.54    inference(resolution,[],[f119,f72])).
% 1.41/0.54  fof(f72,plain,(
% 1.41/0.54    v2_pre_topc(sK0) | ~spl8_1),
% 1.41/0.54    inference(avatar_component_clause,[],[f70])).
% 1.41/0.54  % (23645)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.41/0.54  fof(f70,plain,(
% 1.41/0.54    spl8_1 <=> v2_pre_topc(sK0)),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 1.41/0.54  fof(f119,plain,(
% 1.41/0.54    ( ! [X0] : (~v2_pre_topc(X0) | ~sP6(X0) | ~l1_pre_topc(X0)) ) | ~spl8_11),
% 1.41/0.54    inference(avatar_component_clause,[],[f118])).
% 1.41/0.54  fof(f118,plain,(
% 1.41/0.54    spl8_11 <=> ! [X0] : (~l1_pre_topc(X0) | ~sP6(X0) | ~v2_pre_topc(X0))),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 1.41/0.54  fof(f523,plain,(
% 1.41/0.54    ~spl8_3 | ~spl8_5 | spl8_49 | ~spl8_54),
% 1.41/0.54    inference(avatar_contradiction_clause,[],[f522])).
% 1.41/0.54  fof(f522,plain,(
% 1.41/0.54    $false | (~spl8_3 | ~spl8_5 | spl8_49 | ~spl8_54)),
% 1.41/0.54    inference(subsumption_resolution,[],[f521,f82])).
% 1.41/0.54  fof(f82,plain,(
% 1.41/0.54    l1_pre_topc(sK1) | ~spl8_3),
% 1.41/0.54    inference(avatar_component_clause,[],[f80])).
% 1.41/0.54  fof(f80,plain,(
% 1.41/0.54    spl8_3 <=> l1_pre_topc(sK1)),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 1.41/0.54  fof(f521,plain,(
% 1.41/0.54    ~l1_pre_topc(sK1) | (~spl8_5 | spl8_49 | ~spl8_54)),
% 1.41/0.54    inference(subsumption_resolution,[],[f520,f92])).
% 1.41/0.54  fof(f92,plain,(
% 1.41/0.54    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) | ~spl8_5),
% 1.41/0.54    inference(avatar_component_clause,[],[f90])).
% 1.41/0.54  fof(f90,plain,(
% 1.41/0.54    spl8_5 <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 1.41/0.54  fof(f520,plain,(
% 1.41/0.54    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1) | (spl8_49 | ~spl8_54)),
% 1.41/0.54    inference(subsumption_resolution,[],[f518,f384])).
% 1.41/0.54  fof(f384,plain,(
% 1.41/0.54    ~v6_tops_1(sK3,sK1) | spl8_49),
% 1.41/0.54    inference(avatar_component_clause,[],[f382])).
% 1.41/0.54  fof(f518,plain,(
% 1.41/0.54    v6_tops_1(sK3,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1) | ~spl8_54),
% 1.41/0.54    inference(trivial_inequality_removal,[],[f516])).
% 1.41/0.54  fof(f516,plain,(
% 1.41/0.54    sK3 != sK3 | v6_tops_1(sK3,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1) | ~spl8_54),
% 1.41/0.54    inference(superposition,[],[f47,f445])).
% 1.41/0.54  fof(f445,plain,(
% 1.41/0.54    sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) | ~spl8_54),
% 1.41/0.54    inference(avatar_component_clause,[],[f443])).
% 1.41/0.54  fof(f443,plain,(
% 1.41/0.54    spl8_54 <=> sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3))),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_54])])).
% 1.41/0.54  fof(f47,plain,(
% 1.41/0.54    ( ! [X0,X1] : (k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1 | v6_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.41/0.54    inference(cnf_transformation,[],[f29])).
% 1.41/0.54  fof(f29,plain,(
% 1.41/0.54    ! [X0] : (! [X1] : (((v6_tops_1(X1,X0) | k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1) & (k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 | ~v6_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.41/0.54    inference(nnf_transformation,[],[f14])).
% 1.41/0.54  fof(f14,plain,(
% 1.41/0.54    ! [X0] : (! [X1] : ((v6_tops_1(X1,X0) <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.41/0.54    inference(ennf_transformation,[],[f5])).
% 1.41/0.54  fof(f5,axiom,(
% 1.41/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v6_tops_1(X1,X0) <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1)))),
% 1.41/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_tops_1)).
% 1.41/0.54  fof(f510,plain,(
% 1.41/0.54    ~spl8_5 | ~spl8_21 | spl8_55 | ~spl8_63),
% 1.41/0.54    inference(avatar_contradiction_clause,[],[f509])).
% 1.41/0.54  fof(f509,plain,(
% 1.41/0.54    $false | (~spl8_5 | ~spl8_21 | spl8_55 | ~spl8_63)),
% 1.41/0.54    inference(subsumption_resolution,[],[f508,f92])).
% 1.41/0.54  fof(f508,plain,(
% 1.41/0.54    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) | (~spl8_21 | spl8_55 | ~spl8_63)),
% 1.41/0.54    inference(subsumption_resolution,[],[f506,f449])).
% 1.41/0.54  fof(f449,plain,(
% 1.41/0.54    ~r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) | spl8_55),
% 1.41/0.54    inference(avatar_component_clause,[],[f447])).
% 1.41/0.54  fof(f447,plain,(
% 1.41/0.54    spl8_55 <=> r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3)))),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_55])])).
% 1.41/0.54  fof(f506,plain,(
% 1.41/0.54    r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) | (~spl8_21 | ~spl8_63)),
% 1.41/0.54    inference(resolution,[],[f500,f188])).
% 1.41/0.54  fof(f188,plain,(
% 1.41/0.54    r1_tarski(sK3,k2_pre_topc(sK1,sK3)) | ~spl8_21),
% 1.41/0.54    inference(avatar_component_clause,[],[f186])).
% 1.41/0.54  fof(f186,plain,(
% 1.41/0.54    spl8_21 <=> r1_tarski(sK3,k2_pre_topc(sK1,sK3))),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).
% 1.41/0.54  fof(f500,plain,(
% 1.41/0.54    ( ! [X0] : (~r1_tarski(sK3,k2_pre_topc(sK1,X0)) | r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,X0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))) ) | ~spl8_63),
% 1.41/0.54    inference(avatar_component_clause,[],[f499])).
% 1.41/0.54  fof(f499,plain,(
% 1.41/0.54    spl8_63 <=> ! [X0] : (~r1_tarski(sK3,k2_pre_topc(sK1,X0)) | r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,X0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))))),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_63])])).
% 1.41/0.54  fof(f501,plain,(
% 1.41/0.54    spl8_63 | ~spl8_3 | ~spl8_53),
% 1.41/0.54    inference(avatar_split_clause,[],[f441,f429,f80,f499])).
% 1.41/0.54  fof(f429,plain,(
% 1.41/0.54    spl8_53 <=> ! [X0] : (r1_tarski(sK3,k1_tops_1(sK1,X0)) | ~r1_tarski(sK3,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))))),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_53])])).
% 1.41/0.54  fof(f441,plain,(
% 1.41/0.54    ( ! [X0] : (~r1_tarski(sK3,k2_pre_topc(sK1,X0)) | r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,X0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))) ) | (~spl8_3 | ~spl8_53)),
% 1.41/0.54    inference(subsumption_resolution,[],[f438,f82])).
% 1.41/0.54  fof(f438,plain,(
% 1.41/0.54    ( ! [X0] : (~r1_tarski(sK3,k2_pre_topc(sK1,X0)) | r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,X0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1)) ) | ~spl8_53),
% 1.41/0.54    inference(resolution,[],[f430,f54])).
% 1.41/0.54  fof(f54,plain,(
% 1.41/0.54    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.41/0.54    inference(cnf_transformation,[],[f21])).
% 1.41/0.54  fof(f21,plain,(
% 1.41/0.54    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.41/0.54    inference(flattening,[],[f20])).
% 1.41/0.54  fof(f20,plain,(
% 1.41/0.54    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.41/0.54    inference(ennf_transformation,[],[f2])).
% 1.41/0.54  fof(f2,axiom,(
% 1.41/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.41/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 1.41/0.54  fof(f430,plain,(
% 1.41/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~r1_tarski(sK3,X0) | r1_tarski(sK3,k1_tops_1(sK1,X0))) ) | ~spl8_53),
% 1.41/0.54    inference(avatar_component_clause,[],[f429])).
% 1.41/0.54  fof(f450,plain,(
% 1.41/0.54    spl8_54 | ~spl8_55 | ~spl8_51),
% 1.41/0.54    inference(avatar_split_clause,[],[f422,f415,f447,f443])).
% 1.41/0.54  fof(f415,plain,(
% 1.41/0.54    spl8_51 <=> r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3)),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_51])])).
% 1.41/0.54  fof(f422,plain,(
% 1.41/0.54    ~r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) | sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) | ~spl8_51),
% 1.41/0.54    inference(resolution,[],[f417,f58])).
% 1.41/0.54  fof(f58,plain,(
% 1.41/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.41/0.54    inference(cnf_transformation,[],[f33])).
% 1.41/0.54  fof(f33,plain,(
% 1.41/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.41/0.54    inference(flattening,[],[f32])).
% 1.41/0.54  fof(f32,plain,(
% 1.41/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.41/0.54    inference(nnf_transformation,[],[f1])).
% 1.41/0.54  fof(f1,axiom,(
% 1.41/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.41/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.41/0.54  fof(f417,plain,(
% 1.41/0.54    r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3) | ~spl8_51),
% 1.41/0.54    inference(avatar_component_clause,[],[f415])).
% 1.41/0.54  fof(f431,plain,(
% 1.41/0.54    spl8_53 | ~spl8_24 | ~spl8_42),
% 1.41/0.54    inference(avatar_split_clause,[],[f400,f315,f209,f429])).
% 1.41/0.54  fof(f209,plain,(
% 1.41/0.54    spl8_24 <=> sK3 = k1_tops_1(sK1,sK3)),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).
% 1.41/0.54  fof(f315,plain,(
% 1.41/0.54    spl8_42 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~r1_tarski(sK3,X0) | r1_tarski(k1_tops_1(sK1,sK3),k1_tops_1(sK1,X0)))),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_42])])).
% 1.41/0.54  fof(f400,plain,(
% 1.41/0.54    ( ! [X0] : (r1_tarski(sK3,k1_tops_1(sK1,X0)) | ~r1_tarski(sK3,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))) ) | (~spl8_24 | ~spl8_42)),
% 1.41/0.54    inference(backward_demodulation,[],[f316,f211])).
% 1.41/0.54  fof(f211,plain,(
% 1.41/0.54    sK3 = k1_tops_1(sK1,sK3) | ~spl8_24),
% 1.41/0.54    inference(avatar_component_clause,[],[f209])).
% 1.41/0.54  fof(f316,plain,(
% 1.41/0.54    ( ! [X0] : (r1_tarski(k1_tops_1(sK1,sK3),k1_tops_1(sK1,X0)) | ~r1_tarski(sK3,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))) ) | ~spl8_42),
% 1.41/0.54    inference(avatar_component_clause,[],[f315])).
% 1.41/0.54  fof(f419,plain,(
% 1.41/0.54    spl8_15 | ~spl8_41 | ~spl8_48),
% 1.41/0.54    inference(avatar_split_clause,[],[f409,f353,f310,f143])).
% 1.41/0.54  fof(f143,plain,(
% 1.41/0.54    spl8_15 <=> v3_pre_topc(sK2,sK0)),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 1.41/0.54  fof(f310,plain,(
% 1.41/0.54    spl8_41 <=> v3_pre_topc(k1_tops_1(sK0,sK2),sK0)),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_41])])).
% 1.41/0.54  fof(f353,plain,(
% 1.41/0.54    spl8_48 <=> sK2 = k1_tops_1(sK0,sK2)),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_48])])).
% 1.41/0.54  fof(f409,plain,(
% 1.41/0.54    v3_pre_topc(sK2,sK0) | (~spl8_41 | ~spl8_48)),
% 1.41/0.54    inference(backward_demodulation,[],[f312,f355])).
% 1.41/0.54  fof(f355,plain,(
% 1.41/0.54    sK2 = k1_tops_1(sK0,sK2) | ~spl8_48),
% 1.41/0.54    inference(avatar_component_clause,[],[f353])).
% 1.41/0.54  fof(f312,plain,(
% 1.41/0.54    v3_pre_topc(k1_tops_1(sK0,sK2),sK0) | ~spl8_41),
% 1.41/0.54    inference(avatar_component_clause,[],[f310])).
% 1.41/0.54  fof(f418,plain,(
% 1.41/0.54    spl8_51 | ~spl8_3 | ~spl8_5 | ~spl8_23),
% 1.41/0.54    inference(avatar_split_clause,[],[f399,f201,f90,f80,f415])).
% 1.41/0.54  fof(f201,plain,(
% 1.41/0.54    spl8_23 <=> v4_tops_1(sK3,sK1)),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).
% 1.41/0.54  fof(f399,plain,(
% 1.41/0.54    r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3) | (~spl8_3 | ~spl8_5 | ~spl8_23)),
% 1.41/0.54    inference(subsumption_resolution,[],[f398,f82])).
% 1.41/0.54  fof(f398,plain,(
% 1.41/0.54    r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3) | ~l1_pre_topc(sK1) | (~spl8_5 | ~spl8_23)),
% 1.41/0.54    inference(subsumption_resolution,[],[f395,f92])).
% 1.41/0.54  fof(f395,plain,(
% 1.41/0.54    r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1) | ~spl8_23),
% 1.41/0.54    inference(resolution,[],[f203,f48])).
% 1.41/0.54  fof(f48,plain,(
% 1.41/0.54    ( ! [X0,X1] : (~v4_tops_1(X1,X0) | r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.41/0.54    inference(cnf_transformation,[],[f31])).
% 1.41/0.54  fof(f31,plain,(
% 1.41/0.54    ! [X0] : (! [X1] : (((v4_tops_1(X1,X0) | ~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) & ((r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) | ~v4_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.41/0.54    inference(flattening,[],[f30])).
% 1.41/0.54  fof(f30,plain,(
% 1.41/0.54    ! [X0] : (! [X1] : (((v4_tops_1(X1,X0) | (~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1))) & ((r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) | ~v4_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.41/0.54    inference(nnf_transformation,[],[f15])).
% 1.41/0.54  fof(f15,plain,(
% 1.41/0.54    ! [X0] : (! [X1] : ((v4_tops_1(X1,X0) <=> (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.41/0.54    inference(ennf_transformation,[],[f4])).
% 1.41/0.54  fof(f4,axiom,(
% 1.41/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_tops_1(X1,X0) <=> (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)))))),
% 1.41/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_tops_1)).
% 1.41/0.54  fof(f203,plain,(
% 1.41/0.54    v4_tops_1(sK3,sK1) | ~spl8_23),
% 1.41/0.54    inference(avatar_component_clause,[],[f201])).
% 1.41/0.54  fof(f404,plain,(
% 1.41/0.54    spl8_48 | ~spl8_4 | ~spl8_22 | ~spl8_30 | ~spl8_46),
% 1.41/0.54    inference(avatar_split_clause,[],[f350,f337,f248,f192,f85,f353])).
% 1.41/0.54  fof(f85,plain,(
% 1.41/0.54    spl8_4 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 1.41/0.54  fof(f192,plain,(
% 1.41/0.54    spl8_22 <=> sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2))),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).
% 1.41/0.54  fof(f248,plain,(
% 1.41/0.54    spl8_30 <=> k1_tops_1(sK0,sK2) = k1_tops_1(sK0,k1_tops_1(sK0,sK2))),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).
% 1.41/0.54  fof(f337,plain,(
% 1.41/0.54    spl8_46 <=> ! [X0] : (k1_tops_1(sK0,k2_pre_topc(sK0,X0)) = k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,X0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_46])])).
% 1.41/0.54  fof(f350,plain,(
% 1.41/0.54    sK2 = k1_tops_1(sK0,sK2) | (~spl8_4 | ~spl8_22 | ~spl8_30 | ~spl8_46)),
% 1.41/0.54    inference(backward_demodulation,[],[f250,f346])).
% 1.41/0.54  fof(f346,plain,(
% 1.41/0.54    sK2 = k1_tops_1(sK0,sK2) | (~spl8_4 | ~spl8_22 | ~spl8_46)),
% 1.41/0.54    inference(forward_demodulation,[],[f344,f194])).
% 1.41/0.54  fof(f194,plain,(
% 1.41/0.54    sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) | ~spl8_22),
% 1.41/0.54    inference(avatar_component_clause,[],[f192])).
% 1.41/0.54  fof(f344,plain,(
% 1.41/0.54    k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) = k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK2))) | (~spl8_4 | ~spl8_46)),
% 1.41/0.54    inference(resolution,[],[f338,f87])).
% 1.41/0.54  fof(f87,plain,(
% 1.41/0.54    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl8_4),
% 1.41/0.54    inference(avatar_component_clause,[],[f85])).
% 1.41/0.54  fof(f338,plain,(
% 1.41/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_tops_1(sK0,k2_pre_topc(sK0,X0)) = k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,X0)))) ) | ~spl8_46),
% 1.41/0.54    inference(avatar_component_clause,[],[f337])).
% 1.41/0.54  fof(f250,plain,(
% 1.41/0.54    k1_tops_1(sK0,sK2) = k1_tops_1(sK0,k1_tops_1(sK0,sK2)) | ~spl8_30),
% 1.41/0.54    inference(avatar_component_clause,[],[f248])).
% 1.41/0.54  fof(f393,plain,(
% 1.41/0.54    spl8_23 | ~spl8_15 | ~spl8_16),
% 1.41/0.54    inference(avatar_split_clause,[],[f377,f147,f143,f201])).
% 1.41/0.54  fof(f147,plain,(
% 1.41/0.54    spl8_16 <=> v4_tops_1(sK2,sK0)),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).
% 1.41/0.54  fof(f377,plain,(
% 1.41/0.54    ~v3_pre_topc(sK2,sK0) | v4_tops_1(sK3,sK1) | ~spl8_16),
% 1.41/0.54    inference(subsumption_resolution,[],[f43,f148])).
% 1.41/0.54  fof(f148,plain,(
% 1.41/0.54    v4_tops_1(sK2,sK0) | ~spl8_16),
% 1.41/0.54    inference(avatar_component_clause,[],[f147])).
% 1.41/0.54  fof(f43,plain,(
% 1.41/0.54    ~v4_tops_1(sK2,sK0) | ~v3_pre_topc(sK2,sK0) | v4_tops_1(sK3,sK1)),
% 1.41/0.54    inference(cnf_transformation,[],[f28])).
% 1.41/0.54  fof(f385,plain,(
% 1.41/0.54    ~spl8_49 | ~spl8_15 | ~spl8_16),
% 1.41/0.54    inference(avatar_split_clause,[],[f376,f147,f143,f382])).
% 1.41/0.54  fof(f376,plain,(
% 1.41/0.54    ~v3_pre_topc(sK2,sK0) | ~v6_tops_1(sK3,sK1) | ~spl8_16),
% 1.41/0.54    inference(subsumption_resolution,[],[f44,f148])).
% 1.41/0.54  fof(f44,plain,(
% 1.41/0.54    ~v4_tops_1(sK2,sK0) | ~v3_pre_topc(sK2,sK0) | ~v6_tops_1(sK3,sK1)),
% 1.41/0.54    inference(cnf_transformation,[],[f28])).
% 1.41/0.54  fof(f373,plain,(
% 1.41/0.54    ~spl8_1 | ~spl8_2 | ~spl8_9 | ~spl8_39),
% 1.41/0.54    inference(avatar_contradiction_clause,[],[f372])).
% 1.41/0.54  fof(f372,plain,(
% 1.41/0.54    $false | (~spl8_1 | ~spl8_2 | ~spl8_9 | ~spl8_39)),
% 1.41/0.54    inference(subsumption_resolution,[],[f371,f72])).
% 1.41/0.54  fof(f371,plain,(
% 1.41/0.54    ~v2_pre_topc(sK0) | (~spl8_2 | ~spl8_9 | ~spl8_39)),
% 1.41/0.54    inference(subsumption_resolution,[],[f369,f77])).
% 1.41/0.54  fof(f369,plain,(
% 1.41/0.54    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl8_9 | ~spl8_39)),
% 1.41/0.54    inference(resolution,[],[f304,f109])).
% 1.41/0.54  fof(f109,plain,(
% 1.41/0.54    ( ! [X0] : (~sP4(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl8_9),
% 1.41/0.54    inference(avatar_component_clause,[],[f108])).
% 1.41/0.54  fof(f108,plain,(
% 1.41/0.54    spl8_9 <=> ! [X0] : (~l1_pre_topc(X0) | ~sP4(X0) | ~v2_pre_topc(X0))),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 1.41/0.54  fof(f304,plain,(
% 1.41/0.54    sP4(sK0) | ~spl8_39),
% 1.41/0.54    inference(avatar_component_clause,[],[f302])).
% 1.41/0.54  fof(f302,plain,(
% 1.41/0.54    spl8_39 <=> sP4(sK0)),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_39])])).
% 1.41/0.54  fof(f360,plain,(
% 1.41/0.54    ~spl8_4 | ~spl8_19 | ~spl8_22 | spl8_28 | ~spl8_46),
% 1.41/0.54    inference(avatar_contradiction_clause,[],[f359])).
% 1.41/0.54  fof(f359,plain,(
% 1.41/0.54    $false | (~spl8_4 | ~spl8_19 | ~spl8_22 | spl8_28 | ~spl8_46)),
% 1.41/0.54    inference(subsumption_resolution,[],[f351,f172])).
% 1.41/0.54  fof(f172,plain,(
% 1.41/0.54    r1_tarski(sK2,k2_pre_topc(sK0,sK2)) | ~spl8_19),
% 1.41/0.54    inference(avatar_component_clause,[],[f170])).
% 1.41/0.54  fof(f170,plain,(
% 1.41/0.54    spl8_19 <=> r1_tarski(sK2,k2_pre_topc(sK0,sK2))),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).
% 1.41/0.54  fof(f351,plain,(
% 1.41/0.54    ~r1_tarski(sK2,k2_pre_topc(sK0,sK2)) | (~spl8_4 | ~spl8_22 | spl8_28 | ~spl8_46)),
% 1.41/0.54    inference(backward_demodulation,[],[f238,f346])).
% 1.41/0.54  fof(f238,plain,(
% 1.41/0.54    ~r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) | spl8_28),
% 1.41/0.54    inference(avatar_component_clause,[],[f236])).
% 1.41/0.54  fof(f236,plain,(
% 1.41/0.54    spl8_28 <=> r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2)))),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).
% 1.41/0.54  fof(f358,plain,(
% 1.41/0.54    ~spl8_4 | ~spl8_22 | spl8_40 | ~spl8_46),
% 1.41/0.54    inference(avatar_contradiction_clause,[],[f357])).
% 1.41/0.54  fof(f357,plain,(
% 1.41/0.54    $false | (~spl8_4 | ~spl8_22 | spl8_40 | ~spl8_46)),
% 1.41/0.54    inference(subsumption_resolution,[],[f349,f87])).
% 1.41/0.54  fof(f349,plain,(
% 1.41/0.54    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl8_4 | ~spl8_22 | spl8_40 | ~spl8_46)),
% 1.41/0.54    inference(backward_demodulation,[],[f308,f346])).
% 1.41/0.54  fof(f308,plain,(
% 1.41/0.54    ~m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl8_40),
% 1.41/0.54    inference(avatar_component_clause,[],[f306])).
% 1.41/0.54  fof(f306,plain,(
% 1.41/0.54    spl8_40 <=> m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_40])])).
% 1.41/0.54  fof(f339,plain,(
% 1.41/0.54    spl8_46 | ~spl8_2 | ~spl8_27),
% 1.41/0.54    inference(avatar_split_clause,[],[f246,f232,f75,f337])).
% 1.41/0.54  fof(f232,plain,(
% 1.41/0.54    spl8_27 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_tops_1(sK0,X0) = k1_tops_1(sK0,k1_tops_1(sK0,X0)))),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).
% 1.41/0.54  fof(f246,plain,(
% 1.41/0.54    ( ! [X0] : (k1_tops_1(sK0,k2_pre_topc(sK0,X0)) = k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,X0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl8_2 | ~spl8_27)),
% 1.41/0.54    inference(subsumption_resolution,[],[f245,f77])).
% 1.41/0.54  fof(f245,plain,(
% 1.41/0.54    ( ! [X0] : (k1_tops_1(sK0,k2_pre_topc(sK0,X0)) = k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,X0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) ) | ~spl8_27),
% 1.41/0.54    inference(resolution,[],[f233,f54])).
% 1.41/0.54  fof(f233,plain,(
% 1.41/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_tops_1(sK0,X0) = k1_tops_1(sK0,k1_tops_1(sK0,X0))) ) | ~spl8_27),
% 1.41/0.54    inference(avatar_component_clause,[],[f232])).
% 1.41/0.54  fof(f317,plain,(
% 1.41/0.54    spl8_42 | ~spl8_5 | ~spl8_33),
% 1.41/0.54    inference(avatar_split_clause,[],[f284,f267,f90,f315])).
% 1.41/0.54  fof(f267,plain,(
% 1.41/0.54    spl8_33 <=> ! [X3,X2] : (~r1_tarski(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) | r1_tarski(k1_tops_1(sK1,X2),k1_tops_1(sK1,X3)))),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).
% 1.41/0.54  fof(f284,plain,(
% 1.41/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~r1_tarski(sK3,X0) | r1_tarski(k1_tops_1(sK1,sK3),k1_tops_1(sK1,X0))) ) | (~spl8_5 | ~spl8_33)),
% 1.41/0.54    inference(resolution,[],[f268,f92])).
% 1.41/0.54  fof(f268,plain,(
% 1.41/0.54    ( ! [X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) | ~r1_tarski(X2,X3) | r1_tarski(k1_tops_1(sK1,X2),k1_tops_1(sK1,X3))) ) | ~spl8_33),
% 1.41/0.54    inference(avatar_component_clause,[],[f267])).
% 1.41/0.54  fof(f313,plain,(
% 1.41/0.54    spl8_39 | ~spl8_40 | spl8_41 | ~spl8_30),
% 1.41/0.54    inference(avatar_split_clause,[],[f256,f248,f310,f306,f302])).
% 1.41/0.54  fof(f256,plain,(
% 1.41/0.54    v3_pre_topc(k1_tops_1(sK0,sK2),sK0) | ~m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | sP4(sK0) | ~spl8_30),
% 1.41/0.54    inference(trivial_inequality_removal,[],[f255])).
% 1.41/0.54  fof(f255,plain,(
% 1.41/0.54    k1_tops_1(sK0,sK2) != k1_tops_1(sK0,sK2) | v3_pre_topc(k1_tops_1(sK0,sK2),sK0) | ~m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | sP4(sK0) | ~spl8_30),
% 1.41/0.54    inference(superposition,[],[f61,f250])).
% 1.41/0.54  fof(f61,plain,(
% 1.41/0.54    ( ! [X2,X0] : (k1_tops_1(X0,X2) != X2 | v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | sP4(X0)) )),
% 1.41/0.54    inference(cnf_transformation,[],[f61_D])).
% 1.41/0.54  fof(f61_D,plain,(
% 1.41/0.54    ( ! [X0] : (( ! [X2] : (k1_tops_1(X0,X2) != X2 | v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) ) <=> ~sP4(X0)) )),
% 1.41/0.54    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP4])])).
% 1.41/0.54  fof(f269,plain,(
% 1.41/0.54    spl8_33 | ~spl8_3),
% 1.41/0.54    inference(avatar_split_clause,[],[f217,f80,f267])).
% 1.41/0.54  fof(f217,plain,(
% 1.41/0.54    ( ! [X2,X3] : (~r1_tarski(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) | r1_tarski(k1_tops_1(sK1,X2),k1_tops_1(sK1,X3))) ) | ~spl8_3),
% 1.41/0.54    inference(resolution,[],[f51,f82])).
% 1.41/0.54  fof(f51,plain,(
% 1.41/0.54    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))) )),
% 1.41/0.54    inference(cnf_transformation,[],[f17])).
% 1.41/0.54  fof(f17,plain,(
% 1.41/0.54    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.41/0.54    inference(flattening,[],[f16])).
% 1.41/0.54  fof(f16,plain,(
% 1.41/0.54    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.41/0.54    inference(ennf_transformation,[],[f7])).
% 1.41/0.54  fof(f7,axiom,(
% 1.41/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 1.41/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).
% 1.41/0.54  fof(f251,plain,(
% 1.41/0.54    spl8_30 | ~spl8_4 | ~spl8_27),
% 1.41/0.54    inference(avatar_split_clause,[],[f244,f232,f85,f248])).
% 1.41/0.54  fof(f244,plain,(
% 1.41/0.54    k1_tops_1(sK0,sK2) = k1_tops_1(sK0,k1_tops_1(sK0,sK2)) | (~spl8_4 | ~spl8_27)),
% 1.41/0.54    inference(resolution,[],[f233,f87])).
% 1.41/0.54  fof(f239,plain,(
% 1.41/0.54    spl8_16 | ~spl8_28 | ~spl8_2 | ~spl8_4 | ~spl8_22),
% 1.41/0.54    inference(avatar_split_clause,[],[f230,f192,f85,f75,f236,f147])).
% 1.41/0.54  fof(f230,plain,(
% 1.41/0.54    ~r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) | v4_tops_1(sK2,sK0) | (~spl8_2 | ~spl8_4 | ~spl8_22)),
% 1.41/0.54    inference(subsumption_resolution,[],[f229,f77])).
% 1.41/0.54  fof(f229,plain,(
% 1.41/0.54    ~r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) | v4_tops_1(sK2,sK0) | ~l1_pre_topc(sK0) | (~spl8_4 | ~spl8_22)),
% 1.41/0.54    inference(subsumption_resolution,[],[f228,f87])).
% 1.41/0.54  fof(f228,plain,(
% 1.41/0.54    ~r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) | v4_tops_1(sK2,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl8_22),
% 1.41/0.54    inference(subsumption_resolution,[],[f227,f59])).
% 1.41/0.54  fof(f59,plain,(
% 1.41/0.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.41/0.54    inference(equality_resolution,[],[f57])).
% 1.41/0.54  fof(f57,plain,(
% 1.41/0.54    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.41/0.54    inference(cnf_transformation,[],[f33])).
% 1.41/0.54  fof(f227,plain,(
% 1.41/0.54    ~r1_tarski(sK2,sK2) | ~r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) | v4_tops_1(sK2,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl8_22),
% 1.41/0.54    inference(superposition,[],[f50,f194])).
% 1.41/0.54  fof(f50,plain,(
% 1.41/0.54    ( ! [X0,X1] : (~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) | ~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | v4_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.41/0.54    inference(cnf_transformation,[],[f31])).
% 1.41/0.54  fof(f234,plain,(
% 1.41/0.54    spl8_27 | ~spl8_2),
% 1.41/0.54    inference(avatar_split_clause,[],[f163,f75,f232])).
% 1.41/0.54  fof(f163,plain,(
% 1.41/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_tops_1(sK0,X0) = k1_tops_1(sK0,k1_tops_1(sK0,X0))) ) | ~spl8_2),
% 1.41/0.54    inference(resolution,[],[f55,f77])).
% 1.41/0.54  fof(f55,plain,(
% 1.41/0.54    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))) )),
% 1.41/0.54    inference(cnf_transformation,[],[f23])).
% 1.41/0.54  fof(f23,plain,(
% 1.41/0.54    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.41/0.54    inference(flattening,[],[f22])).
% 1.41/0.54  fof(f22,plain,(
% 1.41/0.54    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.41/0.54    inference(ennf_transformation,[],[f6])).
% 1.41/0.54  fof(f6,axiom,(
% 1.41/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)))),
% 1.41/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',projectivity_k1_tops_1)).
% 1.41/0.54  fof(f212,plain,(
% 1.41/0.54    spl8_24 | ~spl8_3 | ~spl8_5 | ~spl8_6 | ~spl8_20),
% 1.41/0.54    inference(avatar_split_clause,[],[f198,f175,f95,f90,f80,f209])).
% 1.41/0.54  fof(f95,plain,(
% 1.41/0.54    spl8_6 <=> v3_pre_topc(sK3,sK1)),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 1.41/0.54  fof(f175,plain,(
% 1.41/0.54    spl8_20 <=> ! [X1,X3] : (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1))),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).
% 1.41/0.54  fof(f198,plain,(
% 1.41/0.54    sK3 = k1_tops_1(sK1,sK3) | (~spl8_3 | ~spl8_5 | ~spl8_6 | ~spl8_20)),
% 1.41/0.54    inference(subsumption_resolution,[],[f197,f82])).
% 1.41/0.54  fof(f197,plain,(
% 1.41/0.54    sK3 = k1_tops_1(sK1,sK3) | ~l1_pre_topc(sK1) | (~spl8_5 | ~spl8_6 | ~spl8_20)),
% 1.41/0.54    inference(subsumption_resolution,[],[f196,f92])).
% 1.41/0.54  fof(f196,plain,(
% 1.41/0.54    sK3 = k1_tops_1(sK1,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1) | (~spl8_6 | ~spl8_20)),
% 1.41/0.54    inference(resolution,[],[f97,f176])).
% 1.41/0.54  fof(f176,plain,(
% 1.41/0.54    ( ! [X3,X1] : (~v3_pre_topc(X3,X1) | k1_tops_1(X1,X3) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1)) ) | ~spl8_20),
% 1.41/0.54    inference(avatar_component_clause,[],[f175])).
% 1.41/0.54  fof(f97,plain,(
% 1.41/0.54    v3_pre_topc(sK3,sK1) | ~spl8_6),
% 1.41/0.54    inference(avatar_component_clause,[],[f95])).
% 1.41/0.54  fof(f204,plain,(
% 1.41/0.54    spl8_23 | spl8_7),
% 1.41/0.54    inference(avatar_split_clause,[],[f199,f99,f201])).
% 1.41/0.54  fof(f199,plain,(
% 1.41/0.54    v4_tops_1(sK3,sK1) | spl8_7),
% 1.41/0.54    inference(subsumption_resolution,[],[f40,f100])).
% 1.41/0.54  fof(f40,plain,(
% 1.41/0.54    v6_tops_1(sK2,sK0) | v4_tops_1(sK3,sK1)),
% 1.41/0.54    inference(cnf_transformation,[],[f28])).
% 1.41/0.54  fof(f195,plain,(
% 1.41/0.54    spl8_22 | ~spl8_2 | ~spl8_4 | ~spl8_7),
% 1.41/0.54    inference(avatar_split_clause,[],[f184,f99,f85,f75,f192])).
% 1.41/0.54  fof(f184,plain,(
% 1.41/0.54    sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) | (~spl8_2 | ~spl8_4 | ~spl8_7)),
% 1.41/0.54    inference(subsumption_resolution,[],[f183,f77])).
% 1.41/0.54  fof(f183,plain,(
% 1.41/0.54    sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) | ~l1_pre_topc(sK0) | (~spl8_4 | ~spl8_7)),
% 1.41/0.54    inference(subsumption_resolution,[],[f182,f87])).
% 1.41/0.54  fof(f182,plain,(
% 1.41/0.54    sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl8_7),
% 1.41/0.54    inference(resolution,[],[f46,f101])).
% 1.41/0.54  fof(f101,plain,(
% 1.41/0.54    v6_tops_1(sK2,sK0) | ~spl8_7),
% 1.41/0.54    inference(avatar_component_clause,[],[f99])).
% 1.41/0.54  fof(f46,plain,(
% 1.41/0.54    ( ! [X0,X1] : (~v6_tops_1(X1,X0) | k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.41/0.54    inference(cnf_transformation,[],[f29])).
% 1.41/0.54  fof(f189,plain,(
% 1.41/0.54    spl8_21 | ~spl8_5 | ~spl8_18),
% 1.41/0.54    inference(avatar_split_clause,[],[f179,f160,f90,f186])).
% 1.41/0.54  fof(f160,plain,(
% 1.41/0.54    spl8_18 <=> ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | r1_tarski(X1,k2_pre_topc(sK1,X1)))),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).
% 1.41/0.54  fof(f179,plain,(
% 1.41/0.54    r1_tarski(sK3,k2_pre_topc(sK1,sK3)) | (~spl8_5 | ~spl8_18)),
% 1.41/0.54    inference(resolution,[],[f161,f92])).
% 1.41/0.54  fof(f161,plain,(
% 1.41/0.54    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | r1_tarski(X1,k2_pre_topc(sK1,X1))) ) | ~spl8_18),
% 1.41/0.54    inference(avatar_component_clause,[],[f160])).
% 1.41/0.54  fof(f177,plain,(
% 1.41/0.54    spl8_20 | ~spl8_10),
% 1.41/0.54    inference(avatar_split_clause,[],[f168,f114,f175])).
% 1.41/0.54  fof(f114,plain,(
% 1.41/0.54    spl8_10 <=> sP7),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 1.41/0.54  fof(f168,plain,(
% 1.41/0.54    ( ! [X3,X1] : (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1)) ) | ~spl8_10),
% 1.41/0.54    inference(subsumption_resolution,[],[f68,f116])).
% 1.41/0.54  fof(f116,plain,(
% 1.41/0.54    sP7 | ~spl8_10),
% 1.41/0.54    inference(avatar_component_clause,[],[f114])).
% 1.41/0.54  fof(f68,plain,(
% 1.41/0.54    ( ! [X3,X1] : (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~sP7) )),
% 1.41/0.54    inference(general_splitting,[],[f66,f67_D])).
% 1.41/0.54  fof(f67,plain,(
% 1.41/0.54    ( ! [X0] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~sP6(X0) | sP7) )),
% 1.41/0.54    inference(cnf_transformation,[],[f67_D])).
% 1.41/0.54  fof(f67_D,plain,(
% 1.41/0.54    ( ! [X0] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~sP6(X0)) ) <=> ~sP7),
% 1.41/0.54    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP7])])).
% 1.41/0.54  fof(f66,plain,(
% 1.41/0.54    ( ! [X0,X3,X1] : (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~sP6(X0)) )),
% 1.41/0.54    inference(general_splitting,[],[f52,f65_D])).
% 1.41/0.54  fof(f65,plain,(
% 1.41/0.54    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | sP6(X0)) )),
% 1.41/0.54    inference(cnf_transformation,[],[f65_D])).
% 1.41/0.54  fof(f65_D,plain,(
% 1.41/0.54    ( ! [X0] : (( ! [X2] : ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) <=> ~sP6(X0)) )),
% 1.41/0.54    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP6])])).
% 1.41/0.54  fof(f52,plain,(
% 1.41/0.54    ( ! [X2,X0,X3,X1] : (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.41/0.54    inference(cnf_transformation,[],[f19])).
% 1.41/0.54  fof(f19,plain,(
% 1.41/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.41/0.54    inference(flattening,[],[f18])).
% 1.41/0.54  fof(f18,plain,(
% 1.41/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.41/0.54    inference(ennf_transformation,[],[f8])).
% 1.41/0.54  fof(f8,axiom,(
% 1.41/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 1.41/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).
% 1.41/0.54  fof(f173,plain,(
% 1.41/0.54    spl8_19 | ~spl8_4 | ~spl8_17),
% 1.41/0.54    inference(avatar_split_clause,[],[f165,f156,f85,f170])).
% 1.41/0.54  fof(f156,plain,(
% 1.41/0.54    spl8_17 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(X0,k2_pre_topc(sK0,X0)))),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 1.41/0.54  fof(f165,plain,(
% 1.41/0.54    r1_tarski(sK2,k2_pre_topc(sK0,sK2)) | (~spl8_4 | ~spl8_17)),
% 1.41/0.54    inference(resolution,[],[f157,f87])).
% 1.41/0.55  fof(f157,plain,(
% 1.41/0.55    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(X0,k2_pre_topc(sK0,X0))) ) | ~spl8_17),
% 1.41/0.55    inference(avatar_component_clause,[],[f156])).
% 1.41/0.55  fof(f162,plain,(
% 1.41/0.55    spl8_18 | ~spl8_3),
% 1.41/0.55    inference(avatar_split_clause,[],[f153,f80,f160])).
% 1.41/0.55  fof(f153,plain,(
% 1.41/0.55    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | r1_tarski(X1,k2_pre_topc(sK1,X1))) ) | ~spl8_3),
% 1.41/0.55    inference(resolution,[],[f45,f82])).
% 1.41/0.55  fof(f45,plain,(
% 1.41/0.55    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(X1,k2_pre_topc(X0,X1))) )),
% 1.41/0.55    inference(cnf_transformation,[],[f13])).
% 1.41/0.55  fof(f13,plain,(
% 1.41/0.55    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.41/0.55    inference(ennf_transformation,[],[f3])).
% 1.41/0.55  fof(f3,axiom,(
% 1.41/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 1.41/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).
% 1.41/0.55  fof(f158,plain,(
% 1.41/0.55    spl8_17 | ~spl8_2),
% 1.41/0.55    inference(avatar_split_clause,[],[f152,f75,f156])).
% 1.41/0.55  fof(f152,plain,(
% 1.41/0.55    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(X0,k2_pre_topc(sK0,X0))) ) | ~spl8_2),
% 1.41/0.55    inference(resolution,[],[f45,f77])).
% 1.41/0.55  fof(f150,plain,(
% 1.41/0.55    spl8_6 | ~spl8_15 | ~spl8_16),
% 1.41/0.55    inference(avatar_split_clause,[],[f42,f147,f143,f95])).
% 1.41/0.55  fof(f42,plain,(
% 1.41/0.55    ~v4_tops_1(sK2,sK0) | ~v3_pre_topc(sK2,sK0) | v3_pre_topc(sK3,sK1)),
% 1.41/0.55    inference(cnf_transformation,[],[f28])).
% 1.41/0.55  fof(f141,plain,(
% 1.41/0.55    ~spl8_3 | ~spl8_5 | ~spl8_13),
% 1.41/0.55    inference(avatar_contradiction_clause,[],[f137])).
% 1.41/0.55  fof(f137,plain,(
% 1.41/0.55    $false | (~spl8_3 | ~spl8_5 | ~spl8_13)),
% 1.41/0.55    inference(unit_resulting_resolution,[],[f82,f92,f129])).
% 1.41/0.55  fof(f129,plain,(
% 1.41/0.55    ( ! [X3,X1] : (~l1_pre_topc(X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) ) | ~spl8_13),
% 1.41/0.55    inference(avatar_component_clause,[],[f128])).
% 1.41/0.55  fof(f128,plain,(
% 1.41/0.55    spl8_13 <=> ! [X1,X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1))),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 1.41/0.55  fof(f130,plain,(
% 1.41/0.55    spl8_13 | ~spl8_8),
% 1.41/0.55    inference(avatar_split_clause,[],[f121,f104,f128])).
% 1.41/0.55  fof(f104,plain,(
% 1.41/0.55    spl8_8 <=> sP5),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 1.41/0.55  fof(f121,plain,(
% 1.41/0.55    ( ! [X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1)) ) | ~spl8_8),
% 1.41/0.55    inference(subsumption_resolution,[],[f64,f106])).
% 1.41/0.55  fof(f106,plain,(
% 1.41/0.55    sP5 | ~spl8_8),
% 1.41/0.55    inference(avatar_component_clause,[],[f104])).
% 1.41/0.55  fof(f64,plain,(
% 1.41/0.55    ( ! [X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~sP5) )),
% 1.41/0.55    inference(general_splitting,[],[f62,f63_D])).
% 1.41/0.55  fof(f63,plain,(
% 1.41/0.55    ( ! [X0] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~sP4(X0) | sP5) )),
% 1.41/0.55    inference(cnf_transformation,[],[f63_D])).
% 1.41/0.55  fof(f63_D,plain,(
% 1.41/0.55    ( ! [X0] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~sP4(X0)) ) <=> ~sP5),
% 1.41/0.55    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP5])])).
% 1.41/0.55  fof(f62,plain,(
% 1.41/0.55    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~sP4(X0)) )),
% 1.41/0.55    inference(general_splitting,[],[f53,f61_D])).
% 1.41/0.55  fof(f53,plain,(
% 1.41/0.55    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f19])).
% 1.41/0.55  fof(f126,plain,(
% 1.41/0.55    spl8_12 | ~spl8_4),
% 1.41/0.55    inference(avatar_split_clause,[],[f111,f85,f123])).
% 1.41/0.55  fof(f111,plain,(
% 1.41/0.55    sP6(sK0) | ~spl8_4),
% 1.41/0.55    inference(resolution,[],[f65,f87])).
% 1.41/0.55  fof(f120,plain,(
% 1.41/0.55    spl8_10 | spl8_11),
% 1.41/0.55    inference(avatar_split_clause,[],[f67,f118,f114])).
% 1.41/0.55  fof(f110,plain,(
% 1.41/0.55    spl8_8 | spl8_9),
% 1.41/0.55    inference(avatar_split_clause,[],[f63,f108,f104])).
% 1.41/0.55  fof(f102,plain,(
% 1.41/0.55    spl8_6 | spl8_7),
% 1.41/0.55    inference(avatar_split_clause,[],[f39,f99,f95])).
% 1.41/0.55  fof(f39,plain,(
% 1.41/0.55    v6_tops_1(sK2,sK0) | v3_pre_topc(sK3,sK1)),
% 1.41/0.55    inference(cnf_transformation,[],[f28])).
% 1.41/0.55  fof(f93,plain,(
% 1.41/0.55    spl8_5),
% 1.41/0.55    inference(avatar_split_clause,[],[f38,f90])).
% 1.41/0.55  fof(f38,plain,(
% 1.41/0.55    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))),
% 1.41/0.55    inference(cnf_transformation,[],[f28])).
% 1.41/0.55  fof(f88,plain,(
% 1.41/0.55    spl8_4),
% 1.41/0.55    inference(avatar_split_clause,[],[f37,f85])).
% 1.41/0.55  fof(f37,plain,(
% 1.41/0.55    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.41/0.55    inference(cnf_transformation,[],[f28])).
% 1.41/0.55  fof(f83,plain,(
% 1.41/0.55    spl8_3),
% 1.41/0.55    inference(avatar_split_clause,[],[f36,f80])).
% 1.41/0.55  fof(f36,plain,(
% 1.41/0.55    l1_pre_topc(sK1)),
% 1.41/0.55    inference(cnf_transformation,[],[f28])).
% 1.41/0.55  fof(f78,plain,(
% 1.41/0.55    spl8_2),
% 1.41/0.55    inference(avatar_split_clause,[],[f35,f75])).
% 1.41/0.55  fof(f35,plain,(
% 1.41/0.55    l1_pre_topc(sK0)),
% 1.41/0.55    inference(cnf_transformation,[],[f28])).
% 1.41/0.55  fof(f73,plain,(
% 1.41/0.55    spl8_1),
% 1.41/0.55    inference(avatar_split_clause,[],[f34,f70])).
% 1.41/0.55  fof(f34,plain,(
% 1.41/0.55    v2_pre_topc(sK0)),
% 1.41/0.55    inference(cnf_transformation,[],[f28])).
% 1.41/0.55  % SZS output end Proof for theBenchmark
% 1.41/0.55  % (23625)------------------------------
% 1.41/0.55  % (23625)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (23625)Termination reason: Refutation
% 1.41/0.55  
% 1.41/0.55  % (23625)Memory used [KB]: 6524
% 1.41/0.55  % (23625)Time elapsed: 0.121 s
% 1.41/0.55  % (23625)------------------------------
% 1.41/0.55  % (23625)------------------------------
% 1.41/0.55  % (23640)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.41/0.55  % (23644)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.41/0.55  % (23622)Success in time 0.189 s
%------------------------------------------------------------------------------
