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
% DateTime   : Thu Dec  3 12:56:31 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 140 expanded)
%              Number of leaves         :   17 (  58 expanded)
%              Depth                    :   10
%              Number of atoms          :  207 ( 344 expanded)
%              Number of equality atoms :   31 (  67 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f160,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f29,f36,f44,f49,f55,f60,f78,f91,f100,f101,f142,f151,f159])).

fof(f159,plain,
    ( ~ spl8_5
    | spl8_9
    | ~ spl8_10 ),
    inference(avatar_contradiction_clause,[],[f158])).

fof(f158,plain,
    ( $false
    | ~ spl8_5
    | spl8_9
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f156,f90])).

fof(f90,plain,
    ( ~ r2_hidden(sK5(sK2,sK1),sK1)
    | spl8_9 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl8_9
  <=> r2_hidden(sK5(sK2,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f156,plain,
    ( r2_hidden(sK5(sK2,sK1),sK1)
    | ~ spl8_5
    | ~ spl8_10 ),
    inference(resolution,[],[f99,f50])).

fof(f50,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK2))
        | r2_hidden(X0,sK1) )
    | ~ spl8_5 ),
    inference(resolution,[],[f48,f23])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f48,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl8_5
  <=> m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f99,plain,
    ( r2_hidden(sK5(sK2,sK1),k2_relat_1(sK2))
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl8_10
  <=> r2_hidden(sK5(sK2,sK1),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f151,plain,
    ( spl8_13
    | ~ spl8_3
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f150,f58,f39,f130])).

fof(f130,plain,
    ( spl8_13
  <=> sP6(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f39,plain,
    ( spl8_3
  <=> r2_hidden(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f58,plain,
    ( spl8_7
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f150,plain,
    ( sP6(sK3,sK2)
    | ~ spl8_3
    | ~ spl8_7 ),
    inference(resolution,[],[f145,f40])).

fof(f40,plain,
    ( r2_hidden(sK3,sK1)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f39])).

fof(f145,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK1)
        | sP6(X1,sK2) )
    | ~ spl8_7 ),
    inference(superposition,[],[f24,f108])).

fof(f108,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f58])).

fof(f24,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k2_relat_1(X0))
      | sP6(X2,X0) ) ),
    inference(equality_resolution,[],[f19])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( sP6(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f142,plain,
    ( ~ spl8_6
    | ~ spl8_7
    | ~ spl8_13 ),
    inference(avatar_contradiction_clause,[],[f141])).

fof(f141,plain,
    ( $false
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f135,f112])).

fof(f112,plain,
    ( ! [X4] : ~ r2_hidden(k4_tarski(X4,sK3),sK2)
    | ~ spl8_6
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f110,f108])).

fof(f110,plain,
    ( ! [X4] :
        ( sK1 != k2_relat_1(sK2)
        | ~ r2_hidden(k4_tarski(X4,sK3),sK2) )
    | ~ spl8_6 ),
    inference(forward_demodulation,[],[f12,f54])).

fof(f54,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl8_6
  <=> k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f12,plain,(
    ! [X4] :
      ( sK1 != k2_relset_1(sK0,sK1,sK2)
      | ~ r2_hidden(k4_tarski(X4,sK3),sK2) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X4,X3),X2)
            | ~ r2_hidden(X3,X1) )
      <~> k2_relset_1(X0,X1,X2) = X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( ! [X3] :
              ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),X2)
                & r2_hidden(X3,X1) )
        <=> k2_relset_1(X0,X1,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),X2)
              & r2_hidden(X3,X1) )
      <=> k2_relset_1(X0,X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_relset_1)).

fof(f135,plain,
    ( r2_hidden(k4_tarski(sK7(sK2,sK3),sK3),sK2)
    | ~ spl8_13 ),
    inference(resolution,[],[f131,f16])).

fof(f16,plain,(
    ! [X2,X0] :
      ( ~ sP6(X2,X0)
      | r2_hidden(k4_tarski(sK7(X0,X2),X2),X0) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f131,plain,
    ( sP6(sK3,sK2)
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f130])).

fof(f101,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | k2_relset_1(sK0,sK1,sK2) != k2_relat_1(sK2)
    | sK1 = k2_relat_1(sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f100,plain,
    ( spl8_10
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f85,f76,f98])).

fof(f76,plain,
    ( spl8_8
  <=> sP6(sK5(sK2,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f85,plain,
    ( r2_hidden(sK5(sK2,sK1),k2_relat_1(sK2))
    | ~ spl8_8 ),
    inference(resolution,[],[f77,f25])).

fof(f25,plain,(
    ! [X2,X0] :
      ( ~ sP6(X2,X0)
      | r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f18])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( ~ sP6(X2,X0)
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f77,plain,
    ( sP6(sK5(sK2,sK1),sK2)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f76])).

fof(f91,plain,
    ( ~ spl8_9
    | spl8_7
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f86,f76,f58,f89])).

fof(f86,plain,
    ( ~ r2_hidden(sK5(sK2,sK1),sK1)
    | spl8_7
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f83,f59])).

fof(f59,plain,
    ( sK1 != k2_relat_1(sK2)
    | spl8_7 ),
    inference(avatar_component_clause,[],[f58])).

fof(f83,plain,
    ( ~ r2_hidden(sK5(sK2,sK1),sK1)
    | sK1 = k2_relat_1(sK2)
    | ~ spl8_8 ),
    inference(resolution,[],[f77,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ sP6(sK5(X0,X1),X0)
      | ~ r2_hidden(sK5(X0,X1),X1)
      | k2_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f78,plain,
    ( spl8_8
    | spl8_4
    | spl8_7 ),
    inference(avatar_split_clause,[],[f74,f58,f42,f76])).

fof(f42,plain,
    ( spl8_4
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f74,plain,
    ( sP6(sK5(sK2,sK1),sK2)
    | spl8_4
    | spl8_7 ),
    inference(subsumption_resolution,[],[f71,f59])).

fof(f71,plain,
    ( sP6(sK5(sK2,sK1),sK2)
    | sK1 = k2_relat_1(sK2)
    | spl8_4 ),
    inference(factoring,[],[f62])).

fof(f62,plain,
    ( ! [X0] :
        ( sP6(sK5(X0,sK1),X0)
        | sP6(sK5(X0,sK1),sK2)
        | k2_relat_1(X0) = sK1 )
    | spl8_4 ),
    inference(resolution,[],[f51,f17])).

fof(f17,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | sP6(X2,X0) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f51,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(sK4(sK5(X0,sK1)),sK5(X0,sK1)),sK2)
        | sP6(sK5(X0,sK1),X0)
        | k2_relat_1(X0) = sK1 )
    | spl8_4 ),
    inference(resolution,[],[f45,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( sP6(sK5(X0,X1),X0)
      | r2_hidden(sK5(X0,X1),X1)
      | k2_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f45,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,sK1)
        | r2_hidden(k4_tarski(sK4(X3),X3),sK2) )
    | spl8_4 ),
    inference(subsumption_resolution,[],[f13,f43])).

fof(f43,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | spl8_4 ),
    inference(avatar_component_clause,[],[f42])).

fof(f13,plain,(
    ! [X3] :
      ( sK1 = k2_relset_1(sK0,sK1,sK2)
      | ~ r2_hidden(X3,sK1)
      | r2_hidden(k4_tarski(sK4(X3),X3),sK2) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f60,plain,
    ( ~ spl8_7
    | spl8_4
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f56,f53,f42,f58])).

fof(f56,plain,
    ( sK1 != k2_relat_1(sK2)
    | spl8_4
    | ~ spl8_6 ),
    inference(superposition,[],[f43,f54])).

fof(f55,plain,
    ( spl8_6
    | ~ spl8_1 ),
    inference(avatar_split_clause,[],[f31,f27,f53])).

fof(f27,plain,
    ( spl8_1
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f31,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)
    | ~ spl8_1 ),
    inference(resolution,[],[f28,f15])).

fof(f15,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f28,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f27])).

fof(f49,plain,
    ( spl8_5
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f37,f34,f27,f47])).

fof(f34,plain,
    ( spl8_2
  <=> m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f37,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(forward_demodulation,[],[f35,f31])).

fof(f35,plain,
    ( m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1))
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f34])).

fof(f44,plain,
    ( spl8_3
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f11,f42,f39])).

fof(f11,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | r2_hidden(sK3,sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f36,plain,
    ( spl8_2
    | ~ spl8_1 ),
    inference(avatar_split_clause,[],[f30,f27,f34])).

fof(f30,plain,
    ( m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1))
    | ~ spl8_1 ),
    inference(resolution,[],[f28,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f29,plain,(
    spl8_1 ),
    inference(avatar_split_clause,[],[f14,f27])).

fof(f14,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:05:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.47  % (32111)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.47  % (32111)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.48  % (32117)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f160,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(avatar_sat_refutation,[],[f29,f36,f44,f49,f55,f60,f78,f91,f100,f101,f142,f151,f159])).
% 0.20/0.48  fof(f159,plain,(
% 0.20/0.48    ~spl8_5 | spl8_9 | ~spl8_10),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f158])).
% 0.20/0.48  fof(f158,plain,(
% 0.20/0.48    $false | (~spl8_5 | spl8_9 | ~spl8_10)),
% 0.20/0.48    inference(subsumption_resolution,[],[f156,f90])).
% 0.20/0.48  fof(f90,plain,(
% 0.20/0.48    ~r2_hidden(sK5(sK2,sK1),sK1) | spl8_9),
% 0.20/0.48    inference(avatar_component_clause,[],[f89])).
% 0.20/0.48  fof(f89,plain,(
% 0.20/0.48    spl8_9 <=> r2_hidden(sK5(sK2,sK1),sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.20/0.48  fof(f156,plain,(
% 0.20/0.48    r2_hidden(sK5(sK2,sK1),sK1) | (~spl8_5 | ~spl8_10)),
% 0.20/0.48    inference(resolution,[],[f99,f50])).
% 0.20/0.48  fof(f50,plain,(
% 0.20/0.48    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK2)) | r2_hidden(X0,sK1)) ) | ~spl8_5),
% 0.20/0.48    inference(resolution,[],[f48,f23])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f10])).
% 0.20/0.48  fof(f10,plain,(
% 0.20/0.48    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 0.20/0.48  fof(f48,plain,(
% 0.20/0.48    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) | ~spl8_5),
% 0.20/0.48    inference(avatar_component_clause,[],[f47])).
% 0.20/0.48  fof(f47,plain,(
% 0.20/0.48    spl8_5 <=> m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.20/0.48  fof(f99,plain,(
% 0.20/0.48    r2_hidden(sK5(sK2,sK1),k2_relat_1(sK2)) | ~spl8_10),
% 0.20/0.48    inference(avatar_component_clause,[],[f98])).
% 0.20/0.48  fof(f98,plain,(
% 0.20/0.48    spl8_10 <=> r2_hidden(sK5(sK2,sK1),k2_relat_1(sK2))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.20/0.48  fof(f151,plain,(
% 0.20/0.48    spl8_13 | ~spl8_3 | ~spl8_7),
% 0.20/0.48    inference(avatar_split_clause,[],[f150,f58,f39,f130])).
% 0.20/0.48  fof(f130,plain,(
% 0.20/0.48    spl8_13 <=> sP6(sK3,sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 0.20/0.48  fof(f39,plain,(
% 0.20/0.48    spl8_3 <=> r2_hidden(sK3,sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.20/0.48  fof(f58,plain,(
% 0.20/0.48    spl8_7 <=> sK1 = k2_relat_1(sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.20/0.48  fof(f150,plain,(
% 0.20/0.48    sP6(sK3,sK2) | (~spl8_3 | ~spl8_7)),
% 0.20/0.48    inference(resolution,[],[f145,f40])).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    r2_hidden(sK3,sK1) | ~spl8_3),
% 0.20/0.48    inference(avatar_component_clause,[],[f39])).
% 0.20/0.48  fof(f145,plain,(
% 0.20/0.48    ( ! [X1] : (~r2_hidden(X1,sK1) | sP6(X1,sK2)) ) | ~spl8_7),
% 0.20/0.48    inference(superposition,[],[f24,f108])).
% 0.20/0.48  fof(f108,plain,(
% 0.20/0.48    sK1 = k2_relat_1(sK2) | ~spl8_7),
% 0.20/0.48    inference(avatar_component_clause,[],[f58])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    ( ! [X2,X0] : (~r2_hidden(X2,k2_relat_1(X0)) | sP6(X2,X0)) )),
% 0.20/0.48    inference(equality_resolution,[],[f19])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (sP6(X2,X0) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.20/0.48    inference(cnf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).
% 0.20/0.48  fof(f142,plain,(
% 0.20/0.48    ~spl8_6 | ~spl8_7 | ~spl8_13),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f141])).
% 0.20/0.48  fof(f141,plain,(
% 0.20/0.48    $false | (~spl8_6 | ~spl8_7 | ~spl8_13)),
% 0.20/0.48    inference(subsumption_resolution,[],[f135,f112])).
% 0.20/0.48  fof(f112,plain,(
% 0.20/0.48    ( ! [X4] : (~r2_hidden(k4_tarski(X4,sK3),sK2)) ) | (~spl8_6 | ~spl8_7)),
% 0.20/0.48    inference(subsumption_resolution,[],[f110,f108])).
% 0.20/0.48  fof(f110,plain,(
% 0.20/0.48    ( ! [X4] : (sK1 != k2_relat_1(sK2) | ~r2_hidden(k4_tarski(X4,sK3),sK2)) ) | ~spl8_6),
% 0.20/0.48    inference(forward_demodulation,[],[f12,f54])).
% 0.20/0.48  fof(f54,plain,(
% 0.20/0.48    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) | ~spl8_6),
% 0.20/0.48    inference(avatar_component_clause,[],[f53])).
% 0.20/0.48  fof(f53,plain,(
% 0.20/0.48    spl8_6 <=> k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.20/0.48  fof(f12,plain,(
% 0.20/0.48    ( ! [X4] : (sK1 != k2_relset_1(sK0,sK1,sK2) | ~r2_hidden(k4_tarski(X4,sK3),sK2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f7])).
% 0.20/0.48  fof(f7,plain,(
% 0.20/0.48    ? [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X4,X3),X2) | ~r2_hidden(X3,X1)) <~> k2_relset_1(X0,X1,X2) = X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    inference(ennf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,negated_conjecture,(
% 0.20/0.48    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X4,X3),X2) & r2_hidden(X3,X1)) <=> k2_relset_1(X0,X1,X2) = X1))),
% 0.20/0.48    inference(negated_conjecture,[],[f5])).
% 0.20/0.48  fof(f5,conjecture,(
% 0.20/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X4,X3),X2) & r2_hidden(X3,X1)) <=> k2_relset_1(X0,X1,X2) = X1))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_relset_1)).
% 0.20/0.48  fof(f135,plain,(
% 0.20/0.48    r2_hidden(k4_tarski(sK7(sK2,sK3),sK3),sK2) | ~spl8_13),
% 0.20/0.48    inference(resolution,[],[f131,f16])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ( ! [X2,X0] : (~sP6(X2,X0) | r2_hidden(k4_tarski(sK7(X0,X2),X2),X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f2])).
% 0.20/0.48  fof(f131,plain,(
% 0.20/0.48    sP6(sK3,sK2) | ~spl8_13),
% 0.20/0.48    inference(avatar_component_clause,[],[f130])).
% 0.20/0.48  fof(f101,plain,(
% 0.20/0.48    sK1 != k2_relset_1(sK0,sK1,sK2) | k2_relset_1(sK0,sK1,sK2) != k2_relat_1(sK2) | sK1 = k2_relat_1(sK2)),
% 0.20/0.48    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.48  fof(f100,plain,(
% 0.20/0.48    spl8_10 | ~spl8_8),
% 0.20/0.48    inference(avatar_split_clause,[],[f85,f76,f98])).
% 0.20/0.48  fof(f76,plain,(
% 0.20/0.48    spl8_8 <=> sP6(sK5(sK2,sK1),sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.20/0.48  fof(f85,plain,(
% 0.20/0.48    r2_hidden(sK5(sK2,sK1),k2_relat_1(sK2)) | ~spl8_8),
% 0.20/0.48    inference(resolution,[],[f77,f25])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    ( ! [X2,X0] : (~sP6(X2,X0) | r2_hidden(X2,k2_relat_1(X0))) )),
% 0.20/0.48    inference(equality_resolution,[],[f18])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~sP6(X2,X0) | r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.20/0.48    inference(cnf_transformation,[],[f2])).
% 0.20/0.48  fof(f77,plain,(
% 0.20/0.48    sP6(sK5(sK2,sK1),sK2) | ~spl8_8),
% 0.20/0.48    inference(avatar_component_clause,[],[f76])).
% 0.20/0.48  fof(f91,plain,(
% 0.20/0.48    ~spl8_9 | spl8_7 | ~spl8_8),
% 0.20/0.48    inference(avatar_split_clause,[],[f86,f76,f58,f89])).
% 0.20/0.48  fof(f86,plain,(
% 0.20/0.48    ~r2_hidden(sK5(sK2,sK1),sK1) | (spl8_7 | ~spl8_8)),
% 0.20/0.48    inference(subsumption_resolution,[],[f83,f59])).
% 0.20/0.48  fof(f59,plain,(
% 0.20/0.48    sK1 != k2_relat_1(sK2) | spl8_7),
% 0.20/0.48    inference(avatar_component_clause,[],[f58])).
% 0.20/0.48  fof(f83,plain,(
% 0.20/0.48    ~r2_hidden(sK5(sK2,sK1),sK1) | sK1 = k2_relat_1(sK2) | ~spl8_8),
% 0.20/0.48    inference(resolution,[],[f77,f21])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~sP6(sK5(X0,X1),X0) | ~r2_hidden(sK5(X0,X1),X1) | k2_relat_1(X0) = X1) )),
% 0.20/0.48    inference(cnf_transformation,[],[f2])).
% 0.20/0.48  fof(f78,plain,(
% 0.20/0.48    spl8_8 | spl8_4 | spl8_7),
% 0.20/0.48    inference(avatar_split_clause,[],[f74,f58,f42,f76])).
% 0.20/0.48  fof(f42,plain,(
% 0.20/0.48    spl8_4 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.20/0.48  fof(f74,plain,(
% 0.20/0.48    sP6(sK5(sK2,sK1),sK2) | (spl8_4 | spl8_7)),
% 0.20/0.48    inference(subsumption_resolution,[],[f71,f59])).
% 0.20/0.48  fof(f71,plain,(
% 0.20/0.48    sP6(sK5(sK2,sK1),sK2) | sK1 = k2_relat_1(sK2) | spl8_4),
% 0.20/0.48    inference(factoring,[],[f62])).
% 0.20/0.48  fof(f62,plain,(
% 0.20/0.48    ( ! [X0] : (sP6(sK5(X0,sK1),X0) | sP6(sK5(X0,sK1),sK2) | k2_relat_1(X0) = sK1) ) | spl8_4),
% 0.20/0.48    inference(resolution,[],[f51,f17])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    ( ! [X2,X0,X3] : (~r2_hidden(k4_tarski(X3,X2),X0) | sP6(X2,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f2])).
% 0.20/0.48  fof(f51,plain,(
% 0.20/0.48    ( ! [X0] : (r2_hidden(k4_tarski(sK4(sK5(X0,sK1)),sK5(X0,sK1)),sK2) | sP6(sK5(X0,sK1),X0) | k2_relat_1(X0) = sK1) ) | spl8_4),
% 0.20/0.48    inference(resolution,[],[f45,f20])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ( ! [X0,X1] : (sP6(sK5(X0,X1),X0) | r2_hidden(sK5(X0,X1),X1) | k2_relat_1(X0) = X1) )),
% 0.20/0.48    inference(cnf_transformation,[],[f2])).
% 0.20/0.48  fof(f45,plain,(
% 0.20/0.48    ( ! [X3] : (~r2_hidden(X3,sK1) | r2_hidden(k4_tarski(sK4(X3),X3),sK2)) ) | spl8_4),
% 0.20/0.48    inference(subsumption_resolution,[],[f13,f43])).
% 0.20/0.48  fof(f43,plain,(
% 0.20/0.48    sK1 != k2_relset_1(sK0,sK1,sK2) | spl8_4),
% 0.20/0.48    inference(avatar_component_clause,[],[f42])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    ( ! [X3] : (sK1 = k2_relset_1(sK0,sK1,sK2) | ~r2_hidden(X3,sK1) | r2_hidden(k4_tarski(sK4(X3),X3),sK2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f7])).
% 0.20/0.48  fof(f60,plain,(
% 0.20/0.48    ~spl8_7 | spl8_4 | ~spl8_6),
% 0.20/0.48    inference(avatar_split_clause,[],[f56,f53,f42,f58])).
% 0.20/0.48  fof(f56,plain,(
% 0.20/0.48    sK1 != k2_relat_1(sK2) | (spl8_4 | ~spl8_6)),
% 0.20/0.48    inference(superposition,[],[f43,f54])).
% 0.20/0.48  fof(f55,plain,(
% 0.20/0.48    spl8_6 | ~spl8_1),
% 0.20/0.48    inference(avatar_split_clause,[],[f31,f27,f53])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    spl8_1 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.20/0.48  fof(f31,plain,(
% 0.20/0.48    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) | ~spl8_1),
% 0.20/0.48    inference(resolution,[],[f28,f15])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f8])).
% 0.20/0.48  fof(f8,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    inference(ennf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl8_1),
% 0.20/0.48    inference(avatar_component_clause,[],[f27])).
% 0.20/0.48  fof(f49,plain,(
% 0.20/0.48    spl8_5 | ~spl8_1 | ~spl8_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f37,f34,f27,f47])).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    spl8_2 <=> m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) | (~spl8_1 | ~spl8_2)),
% 0.20/0.48    inference(forward_demodulation,[],[f35,f31])).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1)) | ~spl8_2),
% 0.20/0.48    inference(avatar_component_clause,[],[f34])).
% 0.20/0.48  fof(f44,plain,(
% 0.20/0.48    spl8_3 | ~spl8_4),
% 0.20/0.48    inference(avatar_split_clause,[],[f11,f42,f39])).
% 0.20/0.48  fof(f11,plain,(
% 0.20/0.48    sK1 != k2_relset_1(sK0,sK1,sK2) | r2_hidden(sK3,sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f7])).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    spl8_2 | ~spl8_1),
% 0.20/0.48    inference(avatar_split_clause,[],[f30,f27,f34])).
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1)) | ~spl8_1),
% 0.20/0.48    inference(resolution,[],[f28,f22])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f9])).
% 0.20/0.48  fof(f9,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    inference(ennf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    spl8_1),
% 0.20/0.48    inference(avatar_split_clause,[],[f14,f27])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.48    inference(cnf_transformation,[],[f7])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (32111)------------------------------
% 0.20/0.48  % (32111)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (32111)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (32111)Memory used [KB]: 6140
% 0.20/0.48  % (32111)Time elapsed: 0.058 s
% 0.20/0.48  % (32111)------------------------------
% 0.20/0.48  % (32111)------------------------------
% 0.20/0.48  % (32119)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.48  % (32110)Success in time 0.121 s
%------------------------------------------------------------------------------
