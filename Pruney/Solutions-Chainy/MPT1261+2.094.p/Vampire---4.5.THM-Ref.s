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
% DateTime   : Thu Dec  3 13:12:02 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  181 ( 317 expanded)
%              Number of leaves         :   48 ( 146 expanded)
%              Depth                    :   12
%              Number of atoms          :  554 (1059 expanded)
%              Number of equality atoms :  108 ( 225 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f861,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f72,f77,f82,f91,f105,f109,f113,f117,f121,f129,f133,f148,f152,f156,f182,f194,f198,f208,f224,f228,f246,f252,f273,f286,f302,f415,f433,f728,f761,f766,f780,f800,f856,f860])).

fof(f860,plain,
    ( ~ spl2_12
    | ~ spl2_17
    | ~ spl2_19
    | ~ spl2_67
    | spl2_70 ),
    inference(avatar_contradiction_clause,[],[f859])).

fof(f859,plain,
    ( $false
    | ~ spl2_12
    | ~ spl2_17
    | ~ spl2_19
    | ~ spl2_67
    | spl2_70 ),
    inference(subsumption_resolution,[],[f748,f857])).

fof(f857,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0))
    | ~ spl2_12
    | spl2_70 ),
    inference(unit_resulting_resolution,[],[f855,f120])).

fof(f120,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl2_12
  <=> ! [X1,X0] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f855,plain,
    ( ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_70 ),
    inference(avatar_component_clause,[],[f853])).

fof(f853,plain,
    ( spl2_70
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_70])])).

fof(f748,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0))
    | ~ spl2_17
    | ~ spl2_19
    | ~ spl2_67 ),
    inference(unit_resulting_resolution,[],[f147,f727,f155])).

fof(f155,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X1,X2)
        | r1_tarski(X0,X2)
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl2_19
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,X2)
        | ~ r1_tarski(X1,X2)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f727,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_67 ),
    inference(avatar_component_clause,[],[f725])).

fof(f725,plain,
    ( spl2_67
  <=> r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_67])])).

fof(f147,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl2_17
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f856,plain,
    ( ~ spl2_70
    | ~ spl2_3
    | ~ spl2_23
    | spl2_28
    | ~ spl2_34
    | ~ spl2_45
    | ~ spl2_67 ),
    inference(avatar_split_clause,[],[f799,f725,f413,f283,f243,f196,f79,f853])).

fof(f79,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f196,plain,
    ( spl2_23
  <=> ! [X1,X0,X2] :
        ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f243,plain,
    ( spl2_28
  <=> sK1 = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).

fof(f283,plain,
    ( spl2_34
  <=> k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).

fof(f413,plain,
    ( spl2_45
  <=> ! [X3,X2] :
        ( k2_xboole_0(X3,X2) = X3
        | ~ r1_tarski(X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_45])])).

fof(f799,plain,
    ( ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3
    | ~ spl2_23
    | spl2_28
    | ~ spl2_34
    | ~ spl2_45
    | ~ spl2_67 ),
    inference(subsumption_resolution,[],[f795,f245])).

fof(f245,plain,
    ( sK1 != k2_pre_topc(sK0,sK1)
    | spl2_28 ),
    inference(avatar_component_clause,[],[f243])).

fof(f795,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3
    | ~ spl2_23
    | ~ spl2_34
    | ~ spl2_45
    | ~ spl2_67 ),
    inference(forward_demodulation,[],[f794,f754])).

fof(f754,plain,
    ( sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_45
    | ~ spl2_67 ),
    inference(unit_resulting_resolution,[],[f727,f414])).

fof(f414,plain,
    ( ! [X2,X3] :
        ( k2_xboole_0(X3,X2) = X3
        | ~ r1_tarski(X2,X3) )
    | ~ spl2_45 ),
    inference(avatar_component_clause,[],[f413])).

fof(f794,plain,
    ( k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3
    | ~ spl2_23
    | ~ spl2_34 ),
    inference(subsumption_resolution,[],[f287,f81])).

fof(f81,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f79])).

fof(f287,plain,
    ( k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_23
    | ~ spl2_34 ),
    inference(superposition,[],[f285,f197])).

fof(f197,plain,
    ( ! [X2,X0,X1] :
        ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl2_23 ),
    inference(avatar_component_clause,[],[f196])).

fof(f285,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_34 ),
    inference(avatar_component_clause,[],[f283])).

fof(f800,plain,
    ( ~ spl2_4
    | ~ spl2_29
    | ~ spl2_36 ),
    inference(avatar_split_clause,[],[f798,f299,f250,f84])).

fof(f84,plain,
    ( spl2_4
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f250,plain,
    ( spl2_29
  <=> ! [X0] : k4_xboole_0(sK1,X0) = k7_subset_1(u1_struct_0(sK0),sK1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).

fof(f299,plain,
    ( spl2_36
  <=> k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_36])])).

fof(f798,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | ~ spl2_29
    | ~ spl2_36 ),
    inference(trivial_inequality_removal,[],[f797])).

fof(f797,plain,
    ( k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1)
    | ~ v4_pre_topc(sK1,sK0)
    | ~ spl2_29
    | ~ spl2_36 ),
    inference(forward_demodulation,[],[f796,f301])).

fof(f301,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_36 ),
    inference(avatar_component_clause,[],[f299])).

fof(f796,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0)
    | ~ spl2_29 ),
    inference(forward_demodulation,[],[f46,f251])).

fof(f251,plain,
    ( ! [X0] : k4_xboole_0(sK1,X0) = k7_subset_1(u1_struct_0(sK0),sK1,X0)
    | ~ spl2_29 ),
    inference(avatar_component_clause,[],[f250])).

fof(f46,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f37,f39,f38])).

fof(f38,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
              | ~ v4_pre_topc(X1,X0) )
            & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
              | v4_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
            | ~ v4_pre_topc(X1,sK0) )
          & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
            | v4_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X1] :
        ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
          | ~ v4_pre_topc(X1,sK0) )
        & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
          | v4_pre_topc(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
        | ~ v4_pre_topc(sK1,sK0) )
      & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
        | v4_pre_topc(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

fof(f780,plain,
    ( ~ spl2_18
    | spl2_36
    | ~ spl2_46
    | ~ spl2_67
    | ~ spl2_68 ),
    inference(avatar_contradiction_clause,[],[f779])).

fof(f779,plain,
    ( $false
    | ~ spl2_18
    | spl2_36
    | ~ spl2_46
    | ~ spl2_67
    | ~ spl2_68 ),
    inference(subsumption_resolution,[],[f300,f778])).

fof(f778,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_18
    | ~ spl2_46
    | ~ spl2_67
    | ~ spl2_68 ),
    inference(forward_demodulation,[],[f770,f755])).

fof(f755,plain,
    ( k2_tops_1(sK0,sK1) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_46
    | ~ spl2_67 ),
    inference(unit_resulting_resolution,[],[f727,f432])).

fof(f432,plain,
    ( ! [X2,X3] :
        ( k3_xboole_0(X3,X2) = X2
        | ~ r1_tarski(X2,X3) )
    | ~ spl2_46 ),
    inference(avatar_component_clause,[],[f431])).

fof(f431,plain,
    ( spl2_46
  <=> ! [X3,X2] :
        ( k3_xboole_0(X3,X2) = X2
        | ~ r1_tarski(X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_46])])).

fof(f770,plain,
    ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_18
    | ~ spl2_68 ),
    inference(superposition,[],[f151,f765])).

fof(f765,plain,
    ( k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_68 ),
    inference(avatar_component_clause,[],[f763])).

fof(f763,plain,
    ( spl2_68
  <=> k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_68])])).

fof(f151,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl2_18
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f300,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | spl2_36 ),
    inference(avatar_component_clause,[],[f299])).

% (3214)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% (3206)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% (3207)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
fof(f766,plain,
    ( spl2_68
    | ~ spl2_29
    | ~ spl2_32 ),
    inference(avatar_split_clause,[],[f274,f270,f250,f763])).

fof(f270,plain,
    ( spl2_32
  <=> k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).

fof(f274,plain,
    ( k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_29
    | ~ spl2_32 ),
    inference(superposition,[],[f272,f251])).

fof(f272,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_32 ),
    inference(avatar_component_clause,[],[f270])).

fof(f761,plain,
    ( ~ spl2_2
    | spl2_67
    | ~ spl2_4
    | ~ spl2_3
    | ~ spl2_22 ),
    inference(avatar_split_clause,[],[f202,f192,f79,f84,f725,f74])).

fof(f74,plain,
    ( spl2_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f192,plain,
    ( spl2_22
  <=> ! [X1,X0] :
        ( r1_tarski(k2_tops_1(X0,X1),X1)
        | ~ v4_pre_topc(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f202,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl2_3
    | ~ spl2_22 ),
    inference(resolution,[],[f193,f81])).

fof(f193,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v4_pre_topc(X1,X0)
        | r1_tarski(k2_tops_1(X0,X1),X1)
        | ~ l1_pre_topc(X0) )
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f192])).

fof(f728,plain,
    ( spl2_67
    | ~ spl2_8
    | ~ spl2_36 ),
    inference(avatar_split_clause,[],[f713,f299,f103,f725])).

fof(f103,plain,
    ( spl2_8
  <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f713,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_8
    | ~ spl2_36 ),
    inference(superposition,[],[f104,f301])).

fof(f104,plain,
    ( ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f103])).

fof(f433,plain,
    ( spl2_46
    | ~ spl2_10
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f163,f131,f111,f431])).

fof(f111,plain,
    ( spl2_10
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f131,plain,
    ( spl2_15
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f163,plain,
    ( ! [X2,X3] :
        ( k3_xboole_0(X3,X2) = X2
        | ~ r1_tarski(X2,X3) )
    | ~ spl2_10
    | ~ spl2_15 ),
    inference(superposition,[],[f132,f112])).

fof(f112,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f111])).

fof(f132,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f131])).

fof(f415,plain,
    ( spl2_45
    | ~ spl2_9
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f158,f127,f107,f413])).

fof(f107,plain,
    ( spl2_9
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f127,plain,
    ( spl2_14
  <=> ! [X1,X0] :
        ( k2_xboole_0(X0,X1) = X1
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f158,plain,
    ( ! [X2,X3] :
        ( k2_xboole_0(X3,X2) = X3
        | ~ r1_tarski(X2,X3) )
    | ~ spl2_9
    | ~ spl2_14 ),
    inference(superposition,[],[f128,f108])).

fof(f108,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f107])).

fof(f128,plain,
    ( ! [X0,X1] :
        ( k2_xboole_0(X0,X1) = X1
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f127])).

fof(f302,plain,
    ( ~ spl2_3
    | spl2_36
    | ~ spl2_5
    | ~ spl2_20 ),
    inference(avatar_split_clause,[],[f185,f180,f88,f299,f79])).

fof(f88,plain,
    ( spl2_5
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f180,plain,
    ( spl2_20
  <=> ! [X1,X0,X2] :
        ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f185,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_5
    | ~ spl2_20 ),
    inference(superposition,[],[f181,f90])).

fof(f90,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f88])).

fof(f181,plain,
    ( ! [X2,X0,X1] :
        ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f180])).

fof(f286,plain,
    ( spl2_34
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_27 ),
    inference(avatar_split_clause,[],[f236,f226,f79,f74,f283])).

fof(f226,plain,
    ( spl2_27
  <=> ! [X1,X0] :
        ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).

fof(f236,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_27 ),
    inference(unit_resulting_resolution,[],[f76,f81,f227])).

fof(f227,plain,
    ( ! [X0,X1] :
        ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl2_27 ),
    inference(avatar_component_clause,[],[f226])).

fof(f76,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f74])).

fof(f273,plain,
    ( spl2_32
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_26 ),
    inference(avatar_split_clause,[],[f230,f222,f79,f74,f270])).

fof(f222,plain,
    ( spl2_26
  <=> ! [X1,X0] :
        ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).

fof(f230,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_26 ),
    inference(unit_resulting_resolution,[],[f76,f81,f223])).

fof(f223,plain,
    ( ! [X0,X1] :
        ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl2_26 ),
    inference(avatar_component_clause,[],[f222])).

fof(f252,plain,
    ( spl2_29
    | ~ spl2_3
    | ~ spl2_20 ),
    inference(avatar_split_clause,[],[f183,f180,f79,f250])).

fof(f183,plain,
    ( ! [X0] : k4_xboole_0(sK1,X0) = k7_subset_1(u1_struct_0(sK0),sK1,X0)
    | ~ spl2_3
    | ~ spl2_20 ),
    inference(unit_resulting_resolution,[],[f81,f181])).

fof(f246,plain,
    ( ~ spl2_28
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | spl2_4
    | ~ spl2_24 ),
    inference(avatar_split_clause,[],[f229,f206,f84,f79,f74,f69,f243])).

fof(f69,plain,
    ( spl2_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f206,plain,
    ( spl2_24
  <=> ! [X1,X0] :
        ( v4_pre_topc(X1,X0)
        | k2_pre_topc(X0,X1) != X1
        | ~ v2_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f229,plain,
    ( sK1 != k2_pre_topc(sK0,sK1)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | spl2_4
    | ~ spl2_24 ),
    inference(unit_resulting_resolution,[],[f76,f71,f85,f81,f207])).

fof(f207,plain,
    ( ! [X0,X1] :
        ( k2_pre_topc(X0,X1) != X1
        | v4_pre_topc(X1,X0)
        | ~ v2_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl2_24 ),
    inference(avatar_component_clause,[],[f206])).

fof(f85,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | spl2_4 ),
    inference(avatar_component_clause,[],[f84])).

fof(f71,plain,
    ( v2_pre_topc(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f69])).

fof(f228,plain,(
    spl2_27 ),
    inference(avatar_split_clause,[],[f50,f226])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

fof(f224,plain,(
    spl2_26 ),
    inference(avatar_split_clause,[],[f49,f222])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

fof(f208,plain,(
    spl2_24 ),
    inference(avatar_split_clause,[],[f52,f206])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f198,plain,(
    spl2_23 ),
    inference(avatar_split_clause,[],[f66,f196])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f194,plain,(
    spl2_22 ),
    inference(avatar_split_clause,[],[f53,f192])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tops_1(X0,X1),X1)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

fof(f182,plain,(
    spl2_20 ),
    inference(avatar_split_clause,[],[f64,f180])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f156,plain,(
    spl2_19 ),
    inference(avatar_split_clause,[],[f65,f154])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f152,plain,(
    spl2_18 ),
    inference(avatar_split_clause,[],[f59,f150])).

fof(f59,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f148,plain,
    ( spl2_17
    | ~ spl2_3
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f134,f115,f79,f145])).

fof(f115,plain,
    ( spl2_11
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f134,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl2_3
    | ~ spl2_11 ),
    inference(unit_resulting_resolution,[],[f81,f116])).

fof(f116,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | r1_tarski(X0,X1) )
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f115])).

fof(f133,plain,(
    spl2_15 ),
    inference(avatar_split_clause,[],[f61,f131])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f129,plain,(
    spl2_14 ),
    inference(avatar_split_clause,[],[f60,f127])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f121,plain,(
    spl2_12 ),
    inference(avatar_split_clause,[],[f63,f119])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f117,plain,(
    spl2_11 ),
    inference(avatar_split_clause,[],[f62,f115])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f113,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f56,f111])).

fof(f56,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f109,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f55,f107])).

fof(f55,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f105,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f54,f103])).

fof(f54,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f91,plain,
    ( spl2_4
    | spl2_5 ),
    inference(avatar_split_clause,[],[f45,f88,f84])).

fof(f45,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f82,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f44,f79])).

fof(f44,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f40])).

fof(f77,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f43,f74])).

fof(f43,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f72,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f42,f69])).

fof(f42,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:57:57 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.41  % (3212)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.19/0.45  % (3210)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.19/0.46  % (3208)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.19/0.49  % (3204)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.19/0.50  % (3203)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.19/0.50  % (3200)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.19/0.50  % (3202)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.19/0.50  % (3213)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.19/0.51  % (3205)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.19/0.51  % (3211)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.19/0.51  % (3201)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.19/0.51  % (3209)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.19/0.51  % (3199)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.19/0.52  % (3215)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.19/0.52  % (3216)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.19/0.52  % (3204)Refutation found. Thanks to Tanya!
% 0.19/0.52  % SZS status Theorem for theBenchmark
% 0.19/0.52  % SZS output start Proof for theBenchmark
% 0.19/0.52  fof(f861,plain,(
% 0.19/0.52    $false),
% 0.19/0.52    inference(avatar_sat_refutation,[],[f72,f77,f82,f91,f105,f109,f113,f117,f121,f129,f133,f148,f152,f156,f182,f194,f198,f208,f224,f228,f246,f252,f273,f286,f302,f415,f433,f728,f761,f766,f780,f800,f856,f860])).
% 0.19/0.52  fof(f860,plain,(
% 0.19/0.52    ~spl2_12 | ~spl2_17 | ~spl2_19 | ~spl2_67 | spl2_70),
% 0.19/0.52    inference(avatar_contradiction_clause,[],[f859])).
% 0.19/0.52  fof(f859,plain,(
% 0.19/0.52    $false | (~spl2_12 | ~spl2_17 | ~spl2_19 | ~spl2_67 | spl2_70)),
% 0.19/0.52    inference(subsumption_resolution,[],[f748,f857])).
% 0.19/0.52  fof(f857,plain,(
% 0.19/0.52    ~r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) | (~spl2_12 | spl2_70)),
% 0.19/0.52    inference(unit_resulting_resolution,[],[f855,f120])).
% 0.19/0.52  fof(f120,plain,(
% 0.19/0.52    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) ) | ~spl2_12),
% 0.19/0.52    inference(avatar_component_clause,[],[f119])).
% 0.19/0.52  fof(f119,plain,(
% 0.19/0.52    spl2_12 <=> ! [X1,X0] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.19/0.52  fof(f855,plain,(
% 0.19/0.52    ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl2_70),
% 0.19/0.52    inference(avatar_component_clause,[],[f853])).
% 0.19/0.52  fof(f853,plain,(
% 0.19/0.52    spl2_70 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_70])])).
% 0.19/0.52  fof(f748,plain,(
% 0.19/0.52    r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) | (~spl2_17 | ~spl2_19 | ~spl2_67)),
% 0.19/0.52    inference(unit_resulting_resolution,[],[f147,f727,f155])).
% 0.19/0.52  fof(f155,plain,(
% 0.19/0.52    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) ) | ~spl2_19),
% 0.19/0.52    inference(avatar_component_clause,[],[f154])).
% 0.19/0.52  fof(f154,plain,(
% 0.19/0.52    spl2_19 <=> ! [X1,X0,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.19/0.52  fof(f727,plain,(
% 0.19/0.52    r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~spl2_67),
% 0.19/0.52    inference(avatar_component_clause,[],[f725])).
% 0.19/0.52  fof(f725,plain,(
% 0.19/0.52    spl2_67 <=> r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_67])])).
% 0.19/0.52  fof(f147,plain,(
% 0.19/0.52    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl2_17),
% 0.19/0.52    inference(avatar_component_clause,[],[f145])).
% 0.19/0.52  fof(f145,plain,(
% 0.19/0.52    spl2_17 <=> r1_tarski(sK1,u1_struct_0(sK0))),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.19/0.52  fof(f856,plain,(
% 0.19/0.52    ~spl2_70 | ~spl2_3 | ~spl2_23 | spl2_28 | ~spl2_34 | ~spl2_45 | ~spl2_67),
% 0.19/0.52    inference(avatar_split_clause,[],[f799,f725,f413,f283,f243,f196,f79,f853])).
% 0.19/0.52  fof(f79,plain,(
% 0.19/0.52    spl2_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.19/0.52  fof(f196,plain,(
% 0.19/0.52    spl2_23 <=> ! [X1,X0,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 0.19/0.52  fof(f243,plain,(
% 0.19/0.52    spl2_28 <=> sK1 = k2_pre_topc(sK0,sK1)),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).
% 0.19/0.52  fof(f283,plain,(
% 0.19/0.52    spl2_34 <=> k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).
% 0.19/0.52  fof(f413,plain,(
% 0.19/0.52    spl2_45 <=> ! [X3,X2] : (k2_xboole_0(X3,X2) = X3 | ~r1_tarski(X2,X3))),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_45])])).
% 0.19/0.52  fof(f799,plain,(
% 0.19/0.52    ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_3 | ~spl2_23 | spl2_28 | ~spl2_34 | ~spl2_45 | ~spl2_67)),
% 0.19/0.52    inference(subsumption_resolution,[],[f795,f245])).
% 0.19/0.52  fof(f245,plain,(
% 0.19/0.52    sK1 != k2_pre_topc(sK0,sK1) | spl2_28),
% 0.19/0.52    inference(avatar_component_clause,[],[f243])).
% 0.19/0.52  fof(f795,plain,(
% 0.19/0.52    sK1 = k2_pre_topc(sK0,sK1) | ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_3 | ~spl2_23 | ~spl2_34 | ~spl2_45 | ~spl2_67)),
% 0.19/0.52    inference(forward_demodulation,[],[f794,f754])).
% 0.19/0.52  fof(f754,plain,(
% 0.19/0.52    sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl2_45 | ~spl2_67)),
% 0.19/0.52    inference(unit_resulting_resolution,[],[f727,f414])).
% 0.19/0.52  fof(f414,plain,(
% 0.19/0.52    ( ! [X2,X3] : (k2_xboole_0(X3,X2) = X3 | ~r1_tarski(X2,X3)) ) | ~spl2_45),
% 0.19/0.52    inference(avatar_component_clause,[],[f413])).
% 0.19/0.52  fof(f794,plain,(
% 0.19/0.52    k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_3 | ~spl2_23 | ~spl2_34)),
% 0.19/0.52    inference(subsumption_resolution,[],[f287,f81])).
% 0.19/0.52  fof(f81,plain,(
% 0.19/0.52    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_3),
% 0.19/0.52    inference(avatar_component_clause,[],[f79])).
% 0.19/0.52  fof(f287,plain,(
% 0.19/0.52    k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_23 | ~spl2_34)),
% 0.19/0.52    inference(superposition,[],[f285,f197])).
% 0.19/0.52  fof(f197,plain,(
% 0.19/0.52    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl2_23),
% 0.19/0.52    inference(avatar_component_clause,[],[f196])).
% 0.19/0.52  fof(f285,plain,(
% 0.19/0.52    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~spl2_34),
% 0.19/0.52    inference(avatar_component_clause,[],[f283])).
% 0.19/0.52  fof(f800,plain,(
% 0.19/0.52    ~spl2_4 | ~spl2_29 | ~spl2_36),
% 0.19/0.52    inference(avatar_split_clause,[],[f798,f299,f250,f84])).
% 0.19/0.52  fof(f84,plain,(
% 0.19/0.52    spl2_4 <=> v4_pre_topc(sK1,sK0)),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.19/0.52  fof(f250,plain,(
% 0.19/0.52    spl2_29 <=> ! [X0] : k4_xboole_0(sK1,X0) = k7_subset_1(u1_struct_0(sK0),sK1,X0)),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).
% 0.19/0.52  fof(f299,plain,(
% 0.19/0.52    spl2_36 <=> k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_36])])).
% 0.19/0.52  fof(f798,plain,(
% 0.19/0.52    ~v4_pre_topc(sK1,sK0) | (~spl2_29 | ~spl2_36)),
% 0.19/0.52    inference(trivial_inequality_removal,[],[f797])).
% 0.19/0.52  fof(f797,plain,(
% 0.19/0.52    k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0) | (~spl2_29 | ~spl2_36)),
% 0.19/0.52    inference(forward_demodulation,[],[f796,f301])).
% 0.19/0.52  fof(f301,plain,(
% 0.19/0.52    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~spl2_36),
% 0.19/0.52    inference(avatar_component_clause,[],[f299])).
% 0.19/0.52  fof(f796,plain,(
% 0.19/0.52    k2_tops_1(sK0,sK1) != k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0) | ~spl2_29),
% 0.19/0.52    inference(forward_demodulation,[],[f46,f251])).
% 0.19/0.52  fof(f251,plain,(
% 0.19/0.52    ( ! [X0] : (k4_xboole_0(sK1,X0) = k7_subset_1(u1_struct_0(sK0),sK1,X0)) ) | ~spl2_29),
% 0.19/0.52    inference(avatar_component_clause,[],[f250])).
% 0.19/0.52  fof(f46,plain,(
% 0.19/0.52    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 0.19/0.52    inference(cnf_transformation,[],[f40])).
% 0.19/0.52  fof(f40,plain,(
% 0.19/0.52    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.19/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f37,f39,f38])).
% 0.19/0.52  fof(f38,plain,(
% 0.19/0.52    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.19/0.52    introduced(choice_axiom,[])).
% 0.19/0.52  fof(f39,plain,(
% 0.19/0.52    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.19/0.52    introduced(choice_axiom,[])).
% 0.19/0.52  fof(f37,plain,(
% 0.19/0.52    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.19/0.52    inference(flattening,[],[f36])).
% 0.19/0.52  fof(f36,plain,(
% 0.19/0.52    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.19/0.52    inference(nnf_transformation,[],[f22])).
% 0.19/0.52  fof(f22,plain,(
% 0.19/0.52    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.19/0.52    inference(flattening,[],[f21])).
% 0.19/0.52  fof(f21,plain,(
% 0.19/0.52    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.19/0.52    inference(ennf_transformation,[],[f20])).
% 0.19/0.52  fof(f20,negated_conjecture,(
% 0.19/0.52    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 0.19/0.52    inference(negated_conjecture,[],[f19])).
% 0.19/0.52  fof(f19,conjecture,(
% 0.19/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).
% 0.19/0.52  fof(f780,plain,(
% 0.19/0.52    ~spl2_18 | spl2_36 | ~spl2_46 | ~spl2_67 | ~spl2_68),
% 0.19/0.52    inference(avatar_contradiction_clause,[],[f779])).
% 0.19/0.52  fof(f779,plain,(
% 0.19/0.52    $false | (~spl2_18 | spl2_36 | ~spl2_46 | ~spl2_67 | ~spl2_68)),
% 0.19/0.52    inference(subsumption_resolution,[],[f300,f778])).
% 0.19/0.52  fof(f778,plain,(
% 0.19/0.52    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | (~spl2_18 | ~spl2_46 | ~spl2_67 | ~spl2_68)),
% 0.19/0.52    inference(forward_demodulation,[],[f770,f755])).
% 0.19/0.52  fof(f755,plain,(
% 0.19/0.52    k2_tops_1(sK0,sK1) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl2_46 | ~spl2_67)),
% 0.19/0.52    inference(unit_resulting_resolution,[],[f727,f432])).
% 0.19/0.52  fof(f432,plain,(
% 0.19/0.52    ( ! [X2,X3] : (k3_xboole_0(X3,X2) = X2 | ~r1_tarski(X2,X3)) ) | ~spl2_46),
% 0.19/0.52    inference(avatar_component_clause,[],[f431])).
% 0.19/0.52  fof(f431,plain,(
% 0.19/0.52    spl2_46 <=> ! [X3,X2] : (k3_xboole_0(X3,X2) = X2 | ~r1_tarski(X2,X3))),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_46])])).
% 0.19/0.52  fof(f770,plain,(
% 0.19/0.52    k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl2_18 | ~spl2_68)),
% 0.19/0.52    inference(superposition,[],[f151,f765])).
% 0.19/0.52  fof(f765,plain,(
% 0.19/0.52    k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl2_68),
% 0.19/0.52    inference(avatar_component_clause,[],[f763])).
% 0.19/0.52  fof(f763,plain,(
% 0.19/0.52    spl2_68 <=> k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_68])])).
% 0.19/0.52  fof(f151,plain,(
% 0.19/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) | ~spl2_18),
% 0.19/0.52    inference(avatar_component_clause,[],[f150])).
% 0.19/0.52  fof(f150,plain,(
% 0.19/0.52    spl2_18 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.19/0.52  fof(f300,plain,(
% 0.19/0.52    k2_tops_1(sK0,sK1) != k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | spl2_36),
% 0.19/0.52    inference(avatar_component_clause,[],[f299])).
% 0.19/0.52  % (3214)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.19/0.53  % (3206)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.19/0.53  % (3207)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.19/0.54  fof(f766,plain,(
% 0.19/0.54    spl2_68 | ~spl2_29 | ~spl2_32),
% 0.19/0.54    inference(avatar_split_clause,[],[f274,f270,f250,f763])).
% 0.19/0.54  fof(f270,plain,(
% 0.19/0.54    spl2_32 <=> k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 0.19/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).
% 0.19/0.54  fof(f274,plain,(
% 0.19/0.54    k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl2_29 | ~spl2_32)),
% 0.19/0.54    inference(superposition,[],[f272,f251])).
% 0.19/0.54  fof(f272,plain,(
% 0.19/0.54    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~spl2_32),
% 0.19/0.54    inference(avatar_component_clause,[],[f270])).
% 0.19/0.54  fof(f761,plain,(
% 0.19/0.54    ~spl2_2 | spl2_67 | ~spl2_4 | ~spl2_3 | ~spl2_22),
% 0.19/0.54    inference(avatar_split_clause,[],[f202,f192,f79,f84,f725,f74])).
% 0.19/0.54  fof(f74,plain,(
% 0.19/0.54    spl2_2 <=> l1_pre_topc(sK0)),
% 0.19/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.19/0.54  fof(f192,plain,(
% 0.19/0.54    spl2_22 <=> ! [X1,X0] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.19/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 0.19/0.54  fof(f202,plain,(
% 0.19/0.54    ~v4_pre_topc(sK1,sK0) | r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~l1_pre_topc(sK0) | (~spl2_3 | ~spl2_22)),
% 0.19/0.54    inference(resolution,[],[f193,f81])).
% 0.19/0.54  fof(f193,plain,(
% 0.19/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | r1_tarski(k2_tops_1(X0,X1),X1) | ~l1_pre_topc(X0)) ) | ~spl2_22),
% 0.19/0.54    inference(avatar_component_clause,[],[f192])).
% 0.19/0.54  fof(f728,plain,(
% 0.19/0.54    spl2_67 | ~spl2_8 | ~spl2_36),
% 0.19/0.54    inference(avatar_split_clause,[],[f713,f299,f103,f725])).
% 0.19/0.54  fof(f103,plain,(
% 0.19/0.54    spl2_8 <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.19/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.19/0.54  fof(f713,plain,(
% 0.19/0.54    r1_tarski(k2_tops_1(sK0,sK1),sK1) | (~spl2_8 | ~spl2_36)),
% 0.19/0.54    inference(superposition,[],[f104,f301])).
% 0.19/0.54  fof(f104,plain,(
% 0.19/0.54    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) ) | ~spl2_8),
% 0.19/0.54    inference(avatar_component_clause,[],[f103])).
% 0.19/0.54  fof(f433,plain,(
% 0.19/0.54    spl2_46 | ~spl2_10 | ~spl2_15),
% 0.19/0.54    inference(avatar_split_clause,[],[f163,f131,f111,f431])).
% 0.19/0.54  fof(f111,plain,(
% 0.19/0.54    spl2_10 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.19/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.19/0.54  fof(f131,plain,(
% 0.19/0.54    spl2_15 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.19/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.19/0.54  fof(f163,plain,(
% 0.19/0.54    ( ! [X2,X3] : (k3_xboole_0(X3,X2) = X2 | ~r1_tarski(X2,X3)) ) | (~spl2_10 | ~spl2_15)),
% 0.19/0.54    inference(superposition,[],[f132,f112])).
% 0.19/0.54  fof(f112,plain,(
% 0.19/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) ) | ~spl2_10),
% 0.19/0.54    inference(avatar_component_clause,[],[f111])).
% 0.19/0.54  fof(f132,plain,(
% 0.19/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) ) | ~spl2_15),
% 0.19/0.54    inference(avatar_component_clause,[],[f131])).
% 0.19/0.54  fof(f415,plain,(
% 0.19/0.54    spl2_45 | ~spl2_9 | ~spl2_14),
% 0.19/0.54    inference(avatar_split_clause,[],[f158,f127,f107,f413])).
% 0.19/0.54  fof(f107,plain,(
% 0.19/0.54    spl2_9 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.19/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.19/0.54  fof(f127,plain,(
% 0.19/0.54    spl2_14 <=> ! [X1,X0] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.19/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.19/0.54  fof(f158,plain,(
% 0.19/0.54    ( ! [X2,X3] : (k2_xboole_0(X3,X2) = X3 | ~r1_tarski(X2,X3)) ) | (~spl2_9 | ~spl2_14)),
% 0.19/0.54    inference(superposition,[],[f128,f108])).
% 0.19/0.54  fof(f108,plain,(
% 0.19/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) ) | ~spl2_9),
% 0.19/0.54    inference(avatar_component_clause,[],[f107])).
% 0.19/0.54  fof(f128,plain,(
% 0.19/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) ) | ~spl2_14),
% 0.19/0.54    inference(avatar_component_clause,[],[f127])).
% 0.19/0.54  fof(f302,plain,(
% 0.19/0.54    ~spl2_3 | spl2_36 | ~spl2_5 | ~spl2_20),
% 0.19/0.54    inference(avatar_split_clause,[],[f185,f180,f88,f299,f79])).
% 0.19/0.54  fof(f88,plain,(
% 0.19/0.54    spl2_5 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 0.19/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.19/0.54  fof(f180,plain,(
% 0.19/0.54    spl2_20 <=> ! [X1,X0,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 0.19/0.54  fof(f185,plain,(
% 0.19/0.54    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_5 | ~spl2_20)),
% 0.19/0.54    inference(superposition,[],[f181,f90])).
% 0.19/0.54  fof(f90,plain,(
% 0.19/0.54    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~spl2_5),
% 0.19/0.54    inference(avatar_component_clause,[],[f88])).
% 0.19/0.54  fof(f181,plain,(
% 0.19/0.54    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl2_20),
% 0.19/0.54    inference(avatar_component_clause,[],[f180])).
% 0.19/0.54  fof(f286,plain,(
% 0.19/0.54    spl2_34 | ~spl2_2 | ~spl2_3 | ~spl2_27),
% 0.19/0.54    inference(avatar_split_clause,[],[f236,f226,f79,f74,f283])).
% 0.19/0.54  fof(f226,plain,(
% 0.19/0.54    spl2_27 <=> ! [X1,X0] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.19/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).
% 0.19/0.54  fof(f236,plain,(
% 0.19/0.54    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_3 | ~spl2_27)),
% 0.19/0.54    inference(unit_resulting_resolution,[],[f76,f81,f227])).
% 0.19/0.54  fof(f227,plain,(
% 0.19/0.54    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl2_27),
% 0.19/0.54    inference(avatar_component_clause,[],[f226])).
% 0.19/0.54  fof(f76,plain,(
% 0.19/0.54    l1_pre_topc(sK0) | ~spl2_2),
% 0.19/0.54    inference(avatar_component_clause,[],[f74])).
% 0.19/0.54  fof(f273,plain,(
% 0.19/0.54    spl2_32 | ~spl2_2 | ~spl2_3 | ~spl2_26),
% 0.19/0.54    inference(avatar_split_clause,[],[f230,f222,f79,f74,f270])).
% 0.19/0.54  fof(f222,plain,(
% 0.19/0.54    spl2_26 <=> ! [X1,X0] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.19/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).
% 0.19/0.54  fof(f230,plain,(
% 0.19/0.54    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_3 | ~spl2_26)),
% 0.19/0.54    inference(unit_resulting_resolution,[],[f76,f81,f223])).
% 0.19/0.54  fof(f223,plain,(
% 0.19/0.54    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl2_26),
% 0.19/0.54    inference(avatar_component_clause,[],[f222])).
% 0.19/0.54  fof(f252,plain,(
% 0.19/0.54    spl2_29 | ~spl2_3 | ~spl2_20),
% 0.19/0.54    inference(avatar_split_clause,[],[f183,f180,f79,f250])).
% 0.19/0.54  fof(f183,plain,(
% 0.19/0.54    ( ! [X0] : (k4_xboole_0(sK1,X0) = k7_subset_1(u1_struct_0(sK0),sK1,X0)) ) | (~spl2_3 | ~spl2_20)),
% 0.19/0.54    inference(unit_resulting_resolution,[],[f81,f181])).
% 0.19/0.54  fof(f246,plain,(
% 0.19/0.54    ~spl2_28 | ~spl2_1 | ~spl2_2 | ~spl2_3 | spl2_4 | ~spl2_24),
% 0.19/0.54    inference(avatar_split_clause,[],[f229,f206,f84,f79,f74,f69,f243])).
% 0.19/0.54  fof(f69,plain,(
% 0.19/0.54    spl2_1 <=> v2_pre_topc(sK0)),
% 0.19/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.19/0.54  fof(f206,plain,(
% 0.19/0.54    spl2_24 <=> ! [X1,X0] : (v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.19/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 0.19/0.54  fof(f229,plain,(
% 0.19/0.54    sK1 != k2_pre_topc(sK0,sK1) | (~spl2_1 | ~spl2_2 | ~spl2_3 | spl2_4 | ~spl2_24)),
% 0.19/0.54    inference(unit_resulting_resolution,[],[f76,f71,f85,f81,f207])).
% 0.19/0.54  fof(f207,plain,(
% 0.19/0.54    ( ! [X0,X1] : (k2_pre_topc(X0,X1) != X1 | v4_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl2_24),
% 0.19/0.54    inference(avatar_component_clause,[],[f206])).
% 0.19/0.54  fof(f85,plain,(
% 0.19/0.54    ~v4_pre_topc(sK1,sK0) | spl2_4),
% 0.19/0.54    inference(avatar_component_clause,[],[f84])).
% 0.19/0.54  fof(f71,plain,(
% 0.19/0.54    v2_pre_topc(sK0) | ~spl2_1),
% 0.19/0.54    inference(avatar_component_clause,[],[f69])).
% 0.19/0.54  fof(f228,plain,(
% 0.19/0.54    spl2_27),
% 0.19/0.54    inference(avatar_split_clause,[],[f50,f226])).
% 0.19/0.54  fof(f50,plain,(
% 0.19/0.54    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.19/0.54    inference(cnf_transformation,[],[f24])).
% 0.19/0.54  fof(f24,plain,(
% 0.19/0.54    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.19/0.54    inference(ennf_transformation,[],[f16])).
% 0.19/0.54  fof(f16,axiom,(
% 0.19/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 0.19/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).
% 0.19/0.54  fof(f224,plain,(
% 0.19/0.54    spl2_26),
% 0.19/0.54    inference(avatar_split_clause,[],[f49,f222])).
% 0.19/0.54  fof(f49,plain,(
% 0.19/0.54    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.19/0.54    inference(cnf_transformation,[],[f23])).
% 0.19/0.54  fof(f23,plain,(
% 0.19/0.54    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.19/0.54    inference(ennf_transformation,[],[f18])).
% 0.19/0.54  fof(f18,axiom,(
% 0.19/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 0.19/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).
% 0.19/0.54  fof(f208,plain,(
% 0.19/0.54    spl2_24),
% 0.19/0.54    inference(avatar_split_clause,[],[f52,f206])).
% 0.19/0.54  fof(f52,plain,(
% 0.19/0.54    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.19/0.54    inference(cnf_transformation,[],[f26])).
% 0.19/0.54  fof(f26,plain,(
% 0.19/0.54    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.19/0.54    inference(flattening,[],[f25])).
% 0.19/0.54  fof(f25,plain,(
% 0.19/0.54    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.19/0.54    inference(ennf_transformation,[],[f15])).
% 0.19/0.54  fof(f15,axiom,(
% 0.19/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.19/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 0.19/0.54  fof(f198,plain,(
% 0.19/0.54    spl2_23),
% 0.19/0.54    inference(avatar_split_clause,[],[f66,f196])).
% 0.19/0.54  fof(f66,plain,(
% 0.19/0.54    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.19/0.54    inference(cnf_transformation,[],[f35])).
% 0.19/0.54  fof(f35,plain,(
% 0.19/0.54    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.54    inference(flattening,[],[f34])).
% 0.19/0.54  fof(f34,plain,(
% 0.19/0.54    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.19/0.54    inference(ennf_transformation,[],[f11])).
% 0.19/0.54  fof(f11,axiom,(
% 0.19/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 0.19/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.19/0.54  fof(f194,plain,(
% 0.19/0.54    spl2_22),
% 0.19/0.54    inference(avatar_split_clause,[],[f53,f192])).
% 0.19/0.54  fof(f53,plain,(
% 0.19/0.54    ( ! [X0,X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.19/0.54    inference(cnf_transformation,[],[f28])).
% 0.19/0.54  fof(f28,plain,(
% 0.19/0.54    ! [X0] : (! [X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.19/0.54    inference(flattening,[],[f27])).
% 0.19/0.54  fof(f27,plain,(
% 0.19/0.54    ! [X0] : (! [X1] : ((r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.19/0.54    inference(ennf_transformation,[],[f17])).
% 0.19/0.54  fof(f17,axiom,(
% 0.19/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 0.19/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).
% 0.19/0.54  fof(f182,plain,(
% 0.19/0.54    spl2_20),
% 0.19/0.54    inference(avatar_split_clause,[],[f64,f180])).
% 0.19/0.54  fof(f64,plain,(
% 0.19/0.54    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.19/0.54    inference(cnf_transformation,[],[f31])).
% 0.19/0.54  fof(f31,plain,(
% 0.19/0.54    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.54    inference(ennf_transformation,[],[f12])).
% 0.19/0.54  fof(f12,axiom,(
% 0.19/0.54    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.19/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.19/0.54  fof(f156,plain,(
% 0.19/0.54    spl2_19),
% 0.19/0.54    inference(avatar_split_clause,[],[f65,f154])).
% 0.19/0.54  fof(f65,plain,(
% 0.19/0.54    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.19/0.54    inference(cnf_transformation,[],[f33])).
% 0.19/0.54  fof(f33,plain,(
% 0.19/0.54    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.19/0.54    inference(flattening,[],[f32])).
% 0.19/0.54  fof(f32,plain,(
% 0.19/0.54    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.19/0.54    inference(ennf_transformation,[],[f5])).
% 0.19/0.54  fof(f5,axiom,(
% 0.19/0.54    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.19/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.19/0.54  fof(f152,plain,(
% 0.19/0.54    spl2_18),
% 0.19/0.54    inference(avatar_split_clause,[],[f59,f150])).
% 0.19/0.54  fof(f59,plain,(
% 0.19/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.19/0.54    inference(cnf_transformation,[],[f8])).
% 0.19/0.54  fof(f8,axiom,(
% 0.19/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.19/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.19/0.54  fof(f148,plain,(
% 0.19/0.54    spl2_17 | ~spl2_3 | ~spl2_11),
% 0.19/0.54    inference(avatar_split_clause,[],[f134,f115,f79,f145])).
% 0.19/0.54  fof(f115,plain,(
% 0.19/0.54    spl2_11 <=> ! [X1,X0] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.19/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.19/0.54  fof(f134,plain,(
% 0.19/0.54    r1_tarski(sK1,u1_struct_0(sK0)) | (~spl2_3 | ~spl2_11)),
% 0.19/0.54    inference(unit_resulting_resolution,[],[f81,f116])).
% 0.19/0.54  fof(f116,plain,(
% 0.19/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) ) | ~spl2_11),
% 0.19/0.54    inference(avatar_component_clause,[],[f115])).
% 0.19/0.54  fof(f133,plain,(
% 0.19/0.54    spl2_15),
% 0.19/0.54    inference(avatar_split_clause,[],[f61,f131])).
% 0.19/0.54  fof(f61,plain,(
% 0.19/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.19/0.54    inference(cnf_transformation,[],[f30])).
% 0.19/0.54  fof(f30,plain,(
% 0.19/0.54    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.19/0.54    inference(ennf_transformation,[],[f6])).
% 0.19/0.54  fof(f6,axiom,(
% 0.19/0.54    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.19/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.19/0.54  fof(f129,plain,(
% 0.19/0.54    spl2_14),
% 0.19/0.54    inference(avatar_split_clause,[],[f60,f127])).
% 0.19/0.54  fof(f60,plain,(
% 0.19/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.19/0.54    inference(cnf_transformation,[],[f29])).
% 0.19/0.54  fof(f29,plain,(
% 0.19/0.54    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.19/0.54    inference(ennf_transformation,[],[f4])).
% 0.19/0.54  fof(f4,axiom,(
% 0.19/0.54    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.19/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.19/0.54  fof(f121,plain,(
% 0.19/0.54    spl2_12),
% 0.19/0.54    inference(avatar_split_clause,[],[f63,f119])).
% 0.19/0.54  fof(f63,plain,(
% 0.19/0.54    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.19/0.54    inference(cnf_transformation,[],[f41])).
% 0.19/0.54  fof(f41,plain,(
% 0.19/0.54    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.19/0.54    inference(nnf_transformation,[],[f14])).
% 0.19/0.54  fof(f14,axiom,(
% 0.19/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.19/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.19/0.54  fof(f117,plain,(
% 0.19/0.54    spl2_11),
% 0.19/0.54    inference(avatar_split_clause,[],[f62,f115])).
% 0.19/0.54  fof(f62,plain,(
% 0.19/0.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.19/0.54    inference(cnf_transformation,[],[f41])).
% 0.19/0.54  fof(f113,plain,(
% 0.19/0.54    spl2_10),
% 0.19/0.54    inference(avatar_split_clause,[],[f56,f111])).
% 0.19/0.54  fof(f56,plain,(
% 0.19/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.19/0.54    inference(cnf_transformation,[],[f2])).
% 0.19/0.54  fof(f2,axiom,(
% 0.19/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.19/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.19/0.54  fof(f109,plain,(
% 0.19/0.54    spl2_9),
% 0.19/0.54    inference(avatar_split_clause,[],[f55,f107])).
% 0.19/0.54  fof(f55,plain,(
% 0.19/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.19/0.54    inference(cnf_transformation,[],[f1])).
% 0.19/0.54  fof(f1,axiom,(
% 0.19/0.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.19/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.19/0.54  fof(f105,plain,(
% 0.19/0.54    spl2_8),
% 0.19/0.54    inference(avatar_split_clause,[],[f54,f103])).
% 0.19/0.54  fof(f54,plain,(
% 0.19/0.54    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.19/0.54    inference(cnf_transformation,[],[f7])).
% 0.19/0.54  fof(f7,axiom,(
% 0.19/0.54    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.19/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.19/0.54  fof(f91,plain,(
% 0.19/0.54    spl2_4 | spl2_5),
% 0.19/0.54    inference(avatar_split_clause,[],[f45,f88,f84])).
% 0.19/0.54  fof(f45,plain,(
% 0.19/0.54    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 0.19/0.54    inference(cnf_transformation,[],[f40])).
% 0.19/0.54  fof(f82,plain,(
% 0.19/0.54    spl2_3),
% 0.19/0.54    inference(avatar_split_clause,[],[f44,f79])).
% 0.19/0.54  fof(f44,plain,(
% 0.19/0.54    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.19/0.54    inference(cnf_transformation,[],[f40])).
% 0.19/0.54  fof(f77,plain,(
% 0.19/0.54    spl2_2),
% 0.19/0.54    inference(avatar_split_clause,[],[f43,f74])).
% 0.19/0.54  fof(f43,plain,(
% 0.19/0.54    l1_pre_topc(sK0)),
% 0.19/0.54    inference(cnf_transformation,[],[f40])).
% 0.19/0.54  fof(f72,plain,(
% 0.19/0.54    spl2_1),
% 0.19/0.54    inference(avatar_split_clause,[],[f42,f69])).
% 0.19/0.54  fof(f42,plain,(
% 0.19/0.54    v2_pre_topc(sK0)),
% 0.19/0.54    inference(cnf_transformation,[],[f40])).
% 0.19/0.54  % SZS output end Proof for theBenchmark
% 0.19/0.54  % (3204)------------------------------
% 0.19/0.54  % (3204)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.54  % (3204)Termination reason: Refutation
% 0.19/0.54  
% 0.19/0.54  % (3204)Memory used [KB]: 6780
% 0.19/0.54  % (3204)Time elapsed: 0.098 s
% 0.19/0.54  % (3204)------------------------------
% 0.19/0.54  % (3204)------------------------------
% 0.19/0.54  % (3198)Success in time 0.193 s
%------------------------------------------------------------------------------
