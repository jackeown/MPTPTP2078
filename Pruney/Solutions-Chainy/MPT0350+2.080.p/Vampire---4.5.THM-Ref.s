%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:02 EST 2020

% Result     : Theorem 1.21s
% Output     : Refutation 1.21s
% Verified   : 
% Statistics : Number of formulae       :   72 (  99 expanded)
%              Number of leaves         :   22 (  40 expanded)
%              Depth                    :    8
%              Number of atoms          :  187 ( 238 expanded)
%              Number of equality atoms :   46 (  57 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f173,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f60,f83,f95,f97,f109,f121,f162,f172])).

fof(f172,plain,
    ( k3_subset_1(sK0,sK1) != k4_xboole_0(sK0,sK1)
    | sK0 != k2_xboole_0(sK1,k4_xboole_0(sK0,sK1))
    | k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) != k2_xboole_0(sK1,k3_subset_1(sK0,sK1))
    | sK0 = k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f162,plain,
    ( spl3_13
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f124,f80,f57,f159])).

fof(f159,plain,
    ( spl3_13
  <=> k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) = k2_xboole_0(sK1,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f57,plain,
    ( spl3_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f80,plain,
    ( spl3_4
  <=> m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f124,plain,
    ( k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) = k2_xboole_0(sK1,k3_subset_1(sK0,sK1))
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f59,f82,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f82,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f80])).

fof(f59,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f57])).

fof(f121,plain,
    ( spl3_8
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f115,f105,f117])).

fof(f117,plain,
    ( spl3_8
  <=> sK0 = k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f105,plain,
    ( spl3_7
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f115,plain,
    ( sK0 = k2_xboole_0(sK1,k4_xboole_0(sK0,sK1))
    | ~ spl3_7 ),
    inference(resolution,[],[f107,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).

fof(f107,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f105])).

fof(f109,plain,
    ( spl3_7
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f100,f75,f105])).

fof(f75,plain,
    ( spl3_3
  <=> r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f100,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl3_3 ),
    inference(resolution,[],[f77,f49])).

fof(f49,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK2(X0,X1),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r1_tarski(sK2(X0,X1),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK2(X0,X1),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( r1_tarski(sK2(X0,X1),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f77,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f75])).

fof(f97,plain,
    ( spl3_3
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f96,f57,f75])).

fof(f96,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f70,f29])).

fof(f29,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f70,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl3_2 ),
    inference(resolution,[],[f59,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f95,plain,
    ( spl3_5
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f68,f57,f85])).

fof(f85,plain,
    ( spl3_5
  <=> k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f68,plain,
    ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)
    | ~ spl3_2 ),
    inference(resolution,[],[f59,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f83,plain,
    ( spl3_4
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f64,f57,f80])).

fof(f64,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f59,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f60,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f27,f57])).

fof(f27,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f20])).

fof(f20,plain,
    ( ? [X0,X1] :
        ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

fof(f55,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f50,f52])).

fof(f52,plain,
    ( spl3_1
  <=> sK0 = k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f50,plain,(
    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f46,f47])).

fof(f47,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f31,f45])).

fof(f45,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f32,f30])).

fof(f30,plain,(
    ! [X0] : k1_subset_1(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_subset_1(X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

fof(f32,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

fof(f31,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f46,plain,(
    k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) != k3_subset_1(sK0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f28,f45])).

fof(f28,plain,(
    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:55:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.36  ipcrm: permission denied for id (807305218)
% 0.20/0.37  ipcrm: permission denied for id (807370756)
% 0.20/0.37  ipcrm: permission denied for id (807403530)
% 0.20/0.38  ipcrm: permission denied for id (807469069)
% 0.20/0.38  ipcrm: permission denied for id (807501840)
% 0.20/0.40  ipcrm: permission denied for id (807600159)
% 0.20/0.43  ipcrm: permission denied for id (807731261)
% 0.20/0.45  ipcrm: permission denied for id (807829582)
% 0.20/0.47  ipcrm: permission denied for id (807862363)
% 0.20/0.49  ipcrm: permission denied for id (808026218)
% 0.20/0.50  ipcrm: permission denied for id (808091765)
% 0.20/0.51  ipcrm: permission denied for id (808157309)
% 0.64/0.64  % (17346)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.64/0.64  % (17354)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.10/0.65  % (17360)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.10/0.65  % (17367)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.10/0.65  % (17368)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.10/0.66  % (17360)Refutation not found, incomplete strategy% (17360)------------------------------
% 1.10/0.66  % (17360)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.21/0.66  % (17368)Refutation found. Thanks to Tanya!
% 1.21/0.66  % SZS status Theorem for theBenchmark
% 1.21/0.66  % (17360)Termination reason: Refutation not found, incomplete strategy
% 1.21/0.66  
% 1.21/0.66  % (17360)Memory used [KB]: 10618
% 1.21/0.66  % (17360)Time elapsed: 0.096 s
% 1.21/0.66  % (17360)------------------------------
% 1.21/0.66  % (17360)------------------------------
% 1.21/0.66  % SZS output start Proof for theBenchmark
% 1.21/0.66  fof(f173,plain,(
% 1.21/0.66    $false),
% 1.21/0.66    inference(avatar_sat_refutation,[],[f55,f60,f83,f95,f97,f109,f121,f162,f172])).
% 1.21/0.66  fof(f172,plain,(
% 1.21/0.66    k3_subset_1(sK0,sK1) != k4_xboole_0(sK0,sK1) | sK0 != k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)) | k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) != k2_xboole_0(sK1,k3_subset_1(sK0,sK1)) | sK0 = k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 1.21/0.66    introduced(theory_tautology_sat_conflict,[])).
% 1.21/0.66  fof(f162,plain,(
% 1.21/0.66    spl3_13 | ~spl3_2 | ~spl3_4),
% 1.21/0.66    inference(avatar_split_clause,[],[f124,f80,f57,f159])).
% 1.21/0.66  fof(f159,plain,(
% 1.21/0.66    spl3_13 <=> k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) = k2_xboole_0(sK1,k3_subset_1(sK0,sK1))),
% 1.21/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 1.21/0.66  fof(f57,plain,(
% 1.21/0.66    spl3_2 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.21/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.21/0.66  fof(f80,plain,(
% 1.21/0.66    spl3_4 <=> m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))),
% 1.21/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.21/0.66  fof(f124,plain,(
% 1.21/0.66    k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) = k2_xboole_0(sK1,k3_subset_1(sK0,sK1)) | (~spl3_2 | ~spl3_4)),
% 1.21/0.66    inference(unit_resulting_resolution,[],[f59,f82,f44])).
% 1.21/0.66  fof(f44,plain,(
% 1.21/0.66    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.21/0.66    inference(cnf_transformation,[],[f19])).
% 1.21/0.66  fof(f19,plain,(
% 1.21/0.66    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.21/0.66    inference(flattening,[],[f18])).
% 1.21/0.66  fof(f18,plain,(
% 1.21/0.66    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.21/0.66    inference(ennf_transformation,[],[f9])).
% 1.21/0.66  fof(f9,axiom,(
% 1.21/0.66    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 1.21/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 1.21/0.66  fof(f82,plain,(
% 1.21/0.66    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl3_4),
% 1.21/0.66    inference(avatar_component_clause,[],[f80])).
% 1.21/0.66  fof(f59,plain,(
% 1.21/0.66    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl3_2),
% 1.21/0.66    inference(avatar_component_clause,[],[f57])).
% 1.21/0.66  fof(f121,plain,(
% 1.21/0.66    spl3_8 | ~spl3_7),
% 1.21/0.66    inference(avatar_split_clause,[],[f115,f105,f117])).
% 1.21/0.66  fof(f117,plain,(
% 1.21/0.66    spl3_8 <=> sK0 = k2_xboole_0(sK1,k4_xboole_0(sK0,sK1))),
% 1.21/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 1.21/0.66  fof(f105,plain,(
% 1.21/0.66    spl3_7 <=> r1_tarski(sK1,sK0)),
% 1.21/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 1.21/0.66  fof(f115,plain,(
% 1.21/0.66    sK0 = k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)) | ~spl3_7),
% 1.21/0.66    inference(resolution,[],[f107,f37])).
% 1.21/0.66  fof(f37,plain,(
% 1.21/0.66    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1)) )),
% 1.21/0.66    inference(cnf_transformation,[],[f15])).
% 1.21/0.66  fof(f15,plain,(
% 1.21/0.66    ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1))),
% 1.21/0.66    inference(ennf_transformation,[],[f1])).
% 1.21/0.66  fof(f1,axiom,(
% 1.21/0.66    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1)),
% 1.21/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).
% 1.21/0.66  fof(f107,plain,(
% 1.21/0.66    r1_tarski(sK1,sK0) | ~spl3_7),
% 1.21/0.66    inference(avatar_component_clause,[],[f105])).
% 1.21/0.66  fof(f109,plain,(
% 1.21/0.66    spl3_7 | ~spl3_3),
% 1.21/0.66    inference(avatar_split_clause,[],[f100,f75,f105])).
% 1.21/0.66  fof(f75,plain,(
% 1.21/0.66    spl3_3 <=> r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 1.21/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.21/0.66  fof(f100,plain,(
% 1.21/0.66    r1_tarski(sK1,sK0) | ~spl3_3),
% 1.21/0.66    inference(resolution,[],[f77,f49])).
% 1.21/0.66  fof(f49,plain,(
% 1.21/0.66    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 1.21/0.66    inference(equality_resolution,[],[f40])).
% 1.21/0.66  fof(f40,plain,(
% 1.21/0.66    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.21/0.66    inference(cnf_transformation,[],[f26])).
% 1.21/0.66  fof(f26,plain,(
% 1.21/0.66    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.21/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f25])).
% 1.21/0.66  fof(f25,plain,(
% 1.21/0.66    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 1.21/0.66    introduced(choice_axiom,[])).
% 1.21/0.66  fof(f24,plain,(
% 1.21/0.66    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.21/0.66    inference(rectify,[],[f23])).
% 1.21/0.66  fof(f23,plain,(
% 1.21/0.66    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.21/0.66    inference(nnf_transformation,[],[f2])).
% 1.21/0.66  fof(f2,axiom,(
% 1.21/0.66    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.21/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.21/0.66  fof(f77,plain,(
% 1.21/0.66    r2_hidden(sK1,k1_zfmisc_1(sK0)) | ~spl3_3),
% 1.21/0.66    inference(avatar_component_clause,[],[f75])).
% 1.21/0.66  fof(f97,plain,(
% 1.21/0.66    spl3_3 | ~spl3_2),
% 1.21/0.66    inference(avatar_split_clause,[],[f96,f57,f75])).
% 1.21/0.66  fof(f96,plain,(
% 1.21/0.66    r2_hidden(sK1,k1_zfmisc_1(sK0)) | ~spl3_2),
% 1.21/0.66    inference(subsumption_resolution,[],[f70,f29])).
% 1.21/0.66  fof(f29,plain,(
% 1.21/0.66    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.21/0.66    inference(cnf_transformation,[],[f8])).
% 1.21/0.66  fof(f8,axiom,(
% 1.21/0.66    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.21/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.21/0.66  fof(f70,plain,(
% 1.21/0.66    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0)) | ~spl3_2),
% 1.21/0.66    inference(resolution,[],[f59,f33])).
% 1.21/0.66  fof(f33,plain,(
% 1.21/0.66    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.21/0.66    inference(cnf_transformation,[],[f22])).
% 1.21/0.66  fof(f22,plain,(
% 1.21/0.66    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.21/0.66    inference(nnf_transformation,[],[f14])).
% 1.21/0.66  fof(f14,plain,(
% 1.21/0.66    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.21/0.66    inference(ennf_transformation,[],[f3])).
% 1.21/0.66  fof(f3,axiom,(
% 1.21/0.66    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.21/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 1.21/0.66  fof(f95,plain,(
% 1.21/0.66    spl3_5 | ~spl3_2),
% 1.21/0.66    inference(avatar_split_clause,[],[f68,f57,f85])).
% 1.21/0.66  fof(f85,plain,(
% 1.21/0.66    spl3_5 <=> k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 1.21/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.21/0.66  fof(f68,plain,(
% 1.21/0.66    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) | ~spl3_2),
% 1.21/0.66    inference(resolution,[],[f59,f39])).
% 1.21/0.66  fof(f39,plain,(
% 1.21/0.66    ( ! [X0,X1] : (k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.21/0.66    inference(cnf_transformation,[],[f17])).
% 1.21/0.66  fof(f17,plain,(
% 1.21/0.66    ! [X0,X1] : (k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.21/0.66    inference(ennf_transformation,[],[f6])).
% 1.21/0.66  fof(f6,axiom,(
% 1.21/0.66    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1))),
% 1.21/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 1.21/0.66  fof(f83,plain,(
% 1.21/0.66    spl3_4 | ~spl3_2),
% 1.21/0.66    inference(avatar_split_clause,[],[f64,f57,f80])).
% 1.21/0.66  fof(f64,plain,(
% 1.21/0.66    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl3_2),
% 1.21/0.66    inference(unit_resulting_resolution,[],[f59,f38])).
% 1.21/0.66  fof(f38,plain,(
% 1.21/0.66    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.21/0.66    inference(cnf_transformation,[],[f16])).
% 1.21/0.66  fof(f16,plain,(
% 1.21/0.66    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.21/0.66    inference(ennf_transformation,[],[f7])).
% 1.21/0.66  fof(f7,axiom,(
% 1.21/0.66    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.21/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 1.21/0.66  fof(f60,plain,(
% 1.21/0.66    spl3_2),
% 1.21/0.66    inference(avatar_split_clause,[],[f27,f57])).
% 1.21/0.66  fof(f27,plain,(
% 1.21/0.66    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.21/0.66    inference(cnf_transformation,[],[f21])).
% 1.21/0.66  fof(f21,plain,(
% 1.21/0.66    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.21/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f20])).
% 1.21/0.66  fof(f20,plain,(
% 1.21/0.66    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 1.21/0.66    introduced(choice_axiom,[])).
% 1.21/0.66  fof(f13,plain,(
% 1.21/0.66    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.21/0.66    inference(ennf_transformation,[],[f12])).
% 1.21/0.66  fof(f12,negated_conjecture,(
% 1.21/0.66    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 1.21/0.66    inference(negated_conjecture,[],[f11])).
% 1.21/0.66  fof(f11,conjecture,(
% 1.21/0.66    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 1.21/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).
% 1.21/0.66  fof(f55,plain,(
% 1.21/0.66    ~spl3_1),
% 1.21/0.66    inference(avatar_split_clause,[],[f50,f52])).
% 1.21/0.66  fof(f52,plain,(
% 1.21/0.66    spl3_1 <=> sK0 = k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 1.21/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.21/0.66  fof(f50,plain,(
% 1.21/0.66    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 1.21/0.66    inference(forward_demodulation,[],[f46,f47])).
% 1.21/0.66  fof(f47,plain,(
% 1.21/0.66    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 1.21/0.66    inference(definition_unfolding,[],[f31,f45])).
% 1.21/0.66  fof(f45,plain,(
% 1.21/0.66    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 1.21/0.66    inference(definition_unfolding,[],[f32,f30])).
% 1.21/0.66  fof(f30,plain,(
% 1.21/0.66    ( ! [X0] : (k1_subset_1(X0) = k1_xboole_0) )),
% 1.21/0.66    inference(cnf_transformation,[],[f4])).
% 1.21/0.66  fof(f4,axiom,(
% 1.21/0.66    ! [X0] : k1_subset_1(X0) = k1_xboole_0),
% 1.21/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).
% 1.21/0.66  fof(f32,plain,(
% 1.21/0.66    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 1.21/0.66    inference(cnf_transformation,[],[f10])).
% 1.21/0.66  fof(f10,axiom,(
% 1.21/0.66    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 1.21/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).
% 1.21/0.66  fof(f31,plain,(
% 1.21/0.66    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.21/0.66    inference(cnf_transformation,[],[f5])).
% 1.21/0.66  fof(f5,axiom,(
% 1.21/0.66    ! [X0] : k2_subset_1(X0) = X0),
% 1.21/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 1.21/0.66  fof(f46,plain,(
% 1.21/0.66    k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) != k3_subset_1(sK0,k1_xboole_0)),
% 1.21/0.66    inference(definition_unfolding,[],[f28,f45])).
% 1.21/0.66  fof(f28,plain,(
% 1.21/0.66    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 1.21/0.66    inference(cnf_transformation,[],[f21])).
% 1.21/0.66  % SZS output end Proof for theBenchmark
% 1.21/0.66  % (17368)------------------------------
% 1.21/0.66  % (17368)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.21/0.66  % (17368)Termination reason: Refutation
% 1.21/0.66  
% 1.21/0.66  % (17368)Memory used [KB]: 6268
% 1.21/0.66  % (17368)Time elapsed: 0.107 s
% 1.21/0.66  % (17368)------------------------------
% 1.21/0.66  % (17368)------------------------------
% 1.21/0.67  % (17151)Success in time 0.307 s
%------------------------------------------------------------------------------
