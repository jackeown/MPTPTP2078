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
% DateTime   : Thu Dec  3 12:57:46 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  190 ( 336 expanded)
%              Number of leaves         :   43 ( 135 expanded)
%              Depth                    :   11
%              Number of atoms          :  514 ( 949 expanded)
%              Number of equality atoms :   83 ( 167 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f947,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f88,f94,f99,f140,f152,f159,f177,f183,f189,f234,f311,f324,f356,f372,f387,f409,f425,f446,f512,f621,f673,f678,f884,f899,f920,f940])).

fof(f940,plain,
    ( spl4_25
    | ~ spl4_72 ),
    inference(avatar_contradiction_clause,[],[f939])).

fof(f939,plain,
    ( $false
    | spl4_25
    | ~ spl4_72 ),
    inference(subsumption_resolution,[],[f926,f280])).

fof(f280,plain,
    ( k1_xboole_0 != sK2
    | spl4_25 ),
    inference(avatar_component_clause,[],[f279])).

fof(f279,plain,
    ( spl4_25
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f926,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_72 ),
    inference(resolution,[],[f919,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f919,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl4_72 ),
    inference(avatar_component_clause,[],[f917])).

fof(f917,plain,
    ( spl4_72
  <=> r1_tarski(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_72])])).

fof(f920,plain,
    ( spl4_72
    | ~ spl4_70 ),
    inference(avatar_split_clause,[],[f908,f896,f917])).

fof(f896,plain,
    ( spl4_70
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_70])])).

fof(f908,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl4_70 ),
    inference(resolution,[],[f898,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f898,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_70 ),
    inference(avatar_component_clause,[],[f896])).

fof(f899,plain,
    ( spl4_70
    | ~ spl4_69 ),
    inference(avatar_split_clause,[],[f892,f882,f896])).

fof(f882,plain,
    ( spl4_69
  <=> ! [X0] : m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_69])])).

% (21436)Refutation not found, incomplete strategy% (21436)------------------------------
% (21436)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (21436)Termination reason: Refutation not found, incomplete strategy

% (21436)Memory used [KB]: 10618
% (21436)Time elapsed: 0.119 s
% (21436)------------------------------
% (21436)------------------------------
% (21450)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% (21459)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
fof(f892,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_69 ),
    inference(superposition,[],[f883,f72])).

fof(f72,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f883,plain,
    ( ! [X0] : m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
    | ~ spl4_69 ),
    inference(avatar_component_clause,[],[f882])).

fof(f884,plain,
    ( spl4_69
    | ~ spl4_9
    | ~ spl4_13
    | ~ spl4_29
    | ~ spl4_41 ),
    inference(avatar_split_clause,[],[f880,f506,f322,f180,f137,f882])).

fof(f137,plain,
    ( spl4_9
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f180,plain,
    ( spl4_13
  <=> r1_tarski(k2_relat_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f322,plain,
    ( spl4_29
  <=> ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f506,plain,
    ( spl4_41
  <=> k1_xboole_0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).

fof(f880,plain,
    ( ! [X0] : m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
    | ~ spl4_9
    | ~ spl4_13
    | ~ spl4_29
    | ~ spl4_41 ),
    inference(subsumption_resolution,[],[f879,f323])).

fof(f323,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl4_29 ),
    inference(avatar_component_clause,[],[f322])).

fof(f879,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,X0)
        | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) )
    | ~ spl4_9
    | ~ spl4_13
    | ~ spl4_41 ),
    inference(forward_demodulation,[],[f199,f508])).

fof(f508,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl4_41 ),
    inference(avatar_component_clause,[],[f506])).

fof(f199,plain,
    ( ! [X0] :
        ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
        | ~ r1_tarski(k1_relat_1(sK2),X0) )
    | ~ spl4_9
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f196,f139])).

fof(f139,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f137])).

fof(f196,plain,
    ( ! [X0] :
        ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
        | ~ r1_tarski(k1_relat_1(sK2),X0)
        | ~ v1_relat_1(sK2) )
    | ~ spl4_13 ),
    inference(resolution,[],[f182,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X2),X1)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(f182,plain,
    ( r1_tarski(k2_relat_1(sK2),sK0)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f180])).

fof(f678,plain,
    ( ~ spl4_12
    | spl4_54 ),
    inference(avatar_contradiction_clause,[],[f677])).

fof(f677,plain,
    ( $false
    | ~ spl4_12
    | spl4_54 ),
    inference(subsumption_resolution,[],[f675,f176])).

fof(f176,plain,
    ( r1_tarski(k1_relat_1(sK2),sK1)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f174])).

fof(f174,plain,
    ( spl4_12
  <=> r1_tarski(k1_relat_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f675,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK1)
    | spl4_54 ),
    inference(resolution,[],[f672,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f672,plain,
    ( ~ m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK1))
    | spl4_54 ),
    inference(avatar_component_clause,[],[f670])).

fof(f670,plain,
    ( spl4_54
  <=> m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).

fof(f673,plain,
    ( ~ spl4_54
    | ~ spl4_42
    | ~ spl4_52 ),
    inference(avatar_split_clause,[],[f667,f618,f510,f670])).

fof(f510,plain,
    ( spl4_42
  <=> ! [X0] :
        ( ~ m1_subset_1(sK3(X0,k1_relat_1(sK2)),sK1)
        | ~ m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f618,plain,
    ( spl4_52
  <=> m1_subset_1(sK3(sK1,k1_relat_1(sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).

fof(f667,plain,
    ( ~ m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK1))
    | ~ spl4_42
    | ~ spl4_52 ),
    inference(resolution,[],[f620,f511])).

fof(f511,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3(X0,k1_relat_1(sK2)),sK1)
        | ~ m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(X0)) )
    | ~ spl4_42 ),
    inference(avatar_component_clause,[],[f510])).

fof(f620,plain,
    ( m1_subset_1(sK3(sK1,k1_relat_1(sK2)),sK1)
    | ~ spl4_52 ),
    inference(avatar_component_clause,[],[f618])).

fof(f621,plain,
    ( spl4_52
    | ~ spl4_12
    | spl4_41 ),
    inference(avatar_split_clause,[],[f528,f506,f174,f618])).

fof(f528,plain,
    ( m1_subset_1(sK3(sK1,k1_relat_1(sK2)),sK1)
    | ~ spl4_12
    | spl4_41 ),
    inference(subsumption_resolution,[],[f526,f507])).

fof(f507,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | spl4_41 ),
    inference(avatar_component_clause,[],[f506])).

fof(f526,plain,
    ( m1_subset_1(sK3(sK1,k1_relat_1(sK2)),sK1)
    | k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl4_12 ),
    inference(resolution,[],[f176,f154])).

fof(f154,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(sK3(X1,X0),X1)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f54,f60])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k1_xboole_0 = X1
      | m1_subset_1(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(sK3(X0,X1),X1)
        & m1_subset_1(sK3(X0,X1),X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f23,f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
     => ( r2_hidden(sK3(X0,X1),X1)
        & m1_subset_1(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ~ ( ! [X2] :
              ( m1_subset_1(X2,X0)
             => ~ r2_hidden(X2,X1) )
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_subset_1)).

fof(f512,plain,
    ( spl4_41
    | spl4_42
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f491,f186,f510,f506])).

fof(f186,plain,
    ( spl4_14
  <=> k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f491,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3(X0,k1_relat_1(sK2)),sK1)
        | ~ m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(X0))
        | k1_xboole_0 = k1_relat_1(sK2) )
    | ~ spl4_14 ),
    inference(forward_demodulation,[],[f490,f188])).

fof(f188,plain,
    ( k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f186])).

fof(f490,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(X0))
        | k1_xboole_0 = k1_relat_1(sK2)
        | ~ m1_subset_1(sK3(X0,k1_relset_1(sK1,sK0,sK2)),sK1) )
    | ~ spl4_14 ),
    inference(forward_demodulation,[],[f489,f188])).

fof(f489,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k1_relat_1(sK2)
        | ~ m1_subset_1(k1_relset_1(sK1,sK0,sK2),k1_zfmisc_1(X0))
        | ~ m1_subset_1(sK3(X0,k1_relset_1(sK1,sK0,sK2)),sK1) )
    | ~ spl4_14 ),
    inference(forward_demodulation,[],[f160,f188])).

fof(f160,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_relset_1(sK1,sK0,sK2)
      | ~ m1_subset_1(k1_relset_1(sK1,sK0,sK2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(sK3(X0,k1_relset_1(sK1,sK0,sK2)),sK1) ) ),
    inference(resolution,[],[f55,f46])).

fof(f46,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k1_relset_1(sK1,sK0,sK2))
      | ~ m1_subset_1(X3,sK1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k1_relset_1(sK1,sK0,sK2))
        | ~ m1_subset_1(X3,sK1) )
    & k1_xboole_0 != k2_relset_1(sK1,sK0,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & ~ v1_xboole_0(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f31,f30,f29])).

fof(f29,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ! [X3] :
                    ( ~ r2_hidden(X3,k1_relset_1(X1,X0,X2))
                    | ~ m1_subset_1(X3,X1) )
                & k1_xboole_0 != k2_relset_1(X1,X0,X2)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k1_relset_1(X1,sK0,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k2_relset_1(X1,sK0,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK0))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ! [X3] :
                ( ~ r2_hidden(X3,k1_relset_1(X1,sK0,X2))
                | ~ m1_subset_1(X3,X1) )
            & k1_xboole_0 != k2_relset_1(X1,sK0,X2)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK0))) )
        & ~ v1_xboole_0(X1) )
   => ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,k1_relset_1(sK1,sK0,X2))
              | ~ m1_subset_1(X3,sK1) )
          & k1_xboole_0 != k2_relset_1(sK1,sK0,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) )
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X2] :
        ( ! [X3] :
            ( ~ r2_hidden(X3,k1_relset_1(sK1,sK0,X2))
            | ~ m1_subset_1(X3,sK1) )
        & k1_xboole_0 != k2_relset_1(sK1,sK0,X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) )
   => ( ! [X3] :
          ( ~ r2_hidden(X3,k1_relset_1(sK1,sK0,sK2))
          | ~ m1_subset_1(X3,sK1) )
      & k1_xboole_0 != k2_relset_1(sK1,sK0,sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k1_relset_1(X1,X0,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k2_relset_1(X1,X0,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k1_relset_1(X1,X0,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k2_relset_1(X1,X0,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,X1)
                       => ~ r2_hidden(X3,k1_relset_1(X1,X0,X2)) )
                    & k1_xboole_0 != k2_relset_1(X1,X0,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
             => ~ ( ! [X3] :
                      ( m1_subset_1(X3,X1)
                     => ~ r2_hidden(X3,k1_relset_1(X1,X0,X2)) )
                  & k1_xboole_0 != k2_relset_1(X1,X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_relset_1)).

fof(f55,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f446,plain,
    ( spl4_36
    | ~ spl4_38 ),
    inference(avatar_contradiction_clause,[],[f445])).

fof(f445,plain,
    ( $false
    | spl4_36
    | ~ spl4_38 ),
    inference(subsumption_resolution,[],[f435,f408])).

fof(f408,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | spl4_36 ),
    inference(avatar_component_clause,[],[f406])).

fof(f406,plain,
    ( spl4_36
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f435,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl4_38 ),
    inference(resolution,[],[f424,f48])).

fof(f424,plain,
    ( ! [X0] : r1_tarski(k2_relat_1(k1_xboole_0),X0)
    | ~ spl4_38 ),
    inference(avatar_component_clause,[],[f423])).

fof(f423,plain,
    ( spl4_38
  <=> ! [X0] : r1_tarski(k2_relat_1(k1_xboole_0),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f425,plain,
    ( spl4_38
    | ~ spl4_3
    | ~ spl4_31 ),
    inference(avatar_split_clause,[],[f358,f354,f85,f423])).

fof(f85,plain,
    ( spl4_3
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f354,plain,
    ( spl4_31
  <=> ! [X3] : v5_relat_1(k1_xboole_0,X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f358,plain,
    ( ! [X0] : r1_tarski(k2_relat_1(k1_xboole_0),X0)
    | ~ spl4_3
    | ~ spl4_31 ),
    inference(subsumption_resolution,[],[f357,f87])).

fof(f87,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f85])).

fof(f357,plain,
    ( ! [X0] :
        ( r1_tarski(k2_relat_1(k1_xboole_0),X0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl4_31 ),
    inference(resolution,[],[f355,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f355,plain,
    ( ! [X3] : v5_relat_1(k1_xboole_0,X3)
    | ~ spl4_31 ),
    inference(avatar_component_clause,[],[f354])).

fof(f409,plain,
    ( ~ spl4_36
    | spl4_28
    | ~ spl4_32 ),
    inference(avatar_split_clause,[],[f404,f369,f308,f406])).

fof(f308,plain,
    ( spl4_28
  <=> k1_xboole_0 = k2_relset_1(sK1,sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f369,plain,
    ( spl4_32
  <=> k2_relat_1(k1_xboole_0) = k2_relset_1(sK1,sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f404,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | spl4_28
    | ~ spl4_32 ),
    inference(superposition,[],[f310,f371])).

fof(f371,plain,
    ( k2_relat_1(k1_xboole_0) = k2_relset_1(sK1,sK0,k1_xboole_0)
    | ~ spl4_32 ),
    inference(avatar_component_clause,[],[f369])).

fof(f310,plain,
    ( k1_xboole_0 != k2_relset_1(sK1,sK0,k1_xboole_0)
    | spl4_28 ),
    inference(avatar_component_clause,[],[f308])).

fof(f387,plain,
    ( spl4_26
    | ~ spl4_29 ),
    inference(avatar_contradiction_clause,[],[f386])).

fof(f386,plain,
    ( $false
    | spl4_26
    | ~ spl4_29 ),
    inference(subsumption_resolution,[],[f384,f323])).

fof(f384,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(sK1,sK0))
    | spl4_26 ),
    inference(resolution,[],[f299,f60])).

fof(f299,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl4_26 ),
    inference(avatar_component_clause,[],[f298])).

fof(f298,plain,
    ( spl4_26
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f372,plain,
    ( spl4_32
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f314,f298,f369])).

fof(f314,plain,
    ( k2_relat_1(k1_xboole_0) = k2_relset_1(sK1,sK0,k1_xboole_0)
    | ~ spl4_26 ),
    inference(resolution,[],[f300,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f300,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f298])).

fof(f356,plain,
    ( spl4_31
    | ~ spl4_29 ),
    inference(avatar_split_clause,[],[f330,f322,f354])).

fof(f330,plain,
    ( ! [X3] : v5_relat_1(k1_xboole_0,X3)
    | ~ spl4_29 ),
    inference(resolution,[],[f323,f142])).

fof(f142,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X2,X1))
      | v5_relat_1(X0,X1) ) ),
    inference(resolution,[],[f68,f60])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f324,plain,
    ( spl4_29
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f268,f232,f322])).

fof(f232,plain,
    ( spl4_20
  <=> ! [X0] : r1_tarski(k1_relat_1(k1_xboole_0),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f268,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl4_20 ),
    inference(backward_demodulation,[],[f233,f243])).

fof(f243,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl4_20 ),
    inference(resolution,[],[f233,f48])).

fof(f233,plain,
    ( ! [X0] : r1_tarski(k1_relat_1(k1_xboole_0),X0)
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f232])).

fof(f311,plain,
    ( ~ spl4_28
    | spl4_5
    | ~ spl4_25 ),
    inference(avatar_split_clause,[],[f284,f279,f96,f308])).

fof(f96,plain,
    ( spl4_5
  <=> k1_xboole_0 = k2_relset_1(sK1,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f284,plain,
    ( k1_xboole_0 != k2_relset_1(sK1,sK0,k1_xboole_0)
    | spl4_5
    | ~ spl4_25 ),
    inference(backward_demodulation,[],[f98,f281])).

fof(f281,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f279])).

fof(f98,plain,
    ( k1_xboole_0 != k2_relset_1(sK1,sK0,sK2)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f96])).

fof(f234,plain,
    ( spl4_20
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f226,f85,f232])).

fof(f226,plain,
    ( ! [X0] : r1_tarski(k1_relat_1(k1_xboole_0),X0)
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f225,f87])).

fof(f225,plain,(
    ! [X0] :
      ( r1_tarski(k1_relat_1(k1_xboole_0),X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[],[f223,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f223,plain,(
    ! [X0] : v4_relat_1(k1_xboole_0,X0) ),
    inference(resolution,[],[f220,f69])).

fof(f69,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f220,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | v4_relat_1(X0,X1) ) ),
    inference(resolution,[],[f134,f60])).

fof(f134,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | v4_relat_1(X1,X0) ) ),
    inference(superposition,[],[f67,f71])).

fof(f71,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f189,plain,
    ( spl4_14
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f163,f91,f186])).

fof(f91,plain,
    ( spl4_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f163,plain,
    ( k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2)
    | ~ spl4_4 ),
    inference(resolution,[],[f65,f93])).

fof(f93,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f91])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f183,plain,
    ( spl4_13
    | ~ spl4_9
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f168,f156,f137,f180])).

fof(f156,plain,
    ( spl4_11
  <=> v5_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f168,plain,
    ( r1_tarski(k2_relat_1(sK2),sK0)
    | ~ spl4_9
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f167,f139])).

fof(f167,plain,
    ( r1_tarski(k2_relat_1(sK2),sK0)
    | ~ v1_relat_1(sK2)
    | ~ spl4_11 ),
    inference(resolution,[],[f158,f50])).

fof(f158,plain,
    ( v5_relat_1(sK2,sK0)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f156])).

fof(f177,plain,
    ( spl4_12
    | ~ spl4_9
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f162,f149,f137,f174])).

fof(f149,plain,
    ( spl4_10
  <=> v4_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f162,plain,
    ( r1_tarski(k1_relat_1(sK2),sK1)
    | ~ spl4_9
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f161,f139])).

fof(f161,plain,
    ( r1_tarski(k1_relat_1(sK2),sK1)
    | ~ v1_relat_1(sK2)
    | ~ spl4_10 ),
    inference(resolution,[],[f151,f52])).

fof(f151,plain,
    ( v4_relat_1(sK2,sK1)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f149])).

fof(f159,plain,
    ( spl4_11
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f141,f91,f156])).

fof(f141,plain,
    ( v5_relat_1(sK2,sK0)
    | ~ spl4_4 ),
    inference(resolution,[],[f68,f93])).

fof(f152,plain,
    ( spl4_10
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f132,f91,f149])).

fof(f132,plain,
    ( v4_relat_1(sK2,sK1)
    | ~ spl4_4 ),
    inference(resolution,[],[f67,f93])).

fof(f140,plain,
    ( spl4_9
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f128,f91,f137])).

fof(f128,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_4 ),
    inference(resolution,[],[f108,f93])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f47,f49])).

fof(f49,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f99,plain,(
    ~ spl4_5 ),
    inference(avatar_split_clause,[],[f45,f96])).

fof(f45,plain,(
    k1_xboole_0 != k2_relset_1(sK1,sK0,sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f94,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f44,f91])).

fof(f44,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f32])).

fof(f88,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f83,f85])).

fof(f83,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f49,f71])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:31:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.23/0.50  % (21444)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.23/0.51  % (21439)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.23/0.51  % (21437)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.23/0.51  % (21440)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.23/0.52  % (21443)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.23/0.52  % (21456)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.23/0.52  % (21457)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.23/0.52  % (21447)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.23/0.53  % (21458)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.23/0.53  % (21442)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.23/0.53  % (21445)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.23/0.53  % (21449)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.23/0.53  % (21436)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.23/0.53  % (21441)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.23/0.53  % (21448)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.23/0.53  % (21452)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.23/0.53  % (21446)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.23/0.53  % (21438)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.23/0.53  % (21453)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.23/0.54  % (21441)Refutation not found, incomplete strategy% (21441)------------------------------
% 0.23/0.54  % (21441)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.54  % (21441)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.54  
% 0.23/0.54  % (21441)Memory used [KB]: 10618
% 0.23/0.54  % (21441)Time elapsed: 0.087 s
% 0.23/0.54  % (21441)------------------------------
% 0.23/0.54  % (21441)------------------------------
% 0.23/0.54  % (21455)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.23/0.54  % (21460)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.23/0.54  % (21435)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.23/0.55  % (21454)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.23/0.55  % (21437)Refutation found. Thanks to Tanya!
% 0.23/0.55  % SZS status Theorem for theBenchmark
% 0.23/0.55  % SZS output start Proof for theBenchmark
% 0.23/0.55  fof(f947,plain,(
% 0.23/0.55    $false),
% 0.23/0.55    inference(avatar_sat_refutation,[],[f88,f94,f99,f140,f152,f159,f177,f183,f189,f234,f311,f324,f356,f372,f387,f409,f425,f446,f512,f621,f673,f678,f884,f899,f920,f940])).
% 0.23/0.55  fof(f940,plain,(
% 0.23/0.55    spl4_25 | ~spl4_72),
% 0.23/0.55    inference(avatar_contradiction_clause,[],[f939])).
% 0.23/0.55  fof(f939,plain,(
% 0.23/0.55    $false | (spl4_25 | ~spl4_72)),
% 0.23/0.55    inference(subsumption_resolution,[],[f926,f280])).
% 0.23/0.55  fof(f280,plain,(
% 0.23/0.55    k1_xboole_0 != sK2 | spl4_25),
% 0.23/0.55    inference(avatar_component_clause,[],[f279])).
% 0.23/0.55  fof(f279,plain,(
% 0.23/0.55    spl4_25 <=> k1_xboole_0 = sK2),
% 0.23/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 0.23/0.55  fof(f926,plain,(
% 0.23/0.55    k1_xboole_0 = sK2 | ~spl4_72),
% 0.23/0.55    inference(resolution,[],[f919,f48])).
% 0.23/0.55  fof(f48,plain,(
% 0.23/0.55    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.23/0.55    inference(cnf_transformation,[],[f19])).
% 0.23/0.55  fof(f19,plain,(
% 0.23/0.55    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.23/0.55    inference(ennf_transformation,[],[f2])).
% 0.23/0.55  fof(f2,axiom,(
% 0.23/0.55    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.23/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.23/0.55  fof(f919,plain,(
% 0.23/0.55    r1_tarski(sK2,k1_xboole_0) | ~spl4_72),
% 0.23/0.55    inference(avatar_component_clause,[],[f917])).
% 0.23/0.55  fof(f917,plain,(
% 0.23/0.55    spl4_72 <=> r1_tarski(sK2,k1_xboole_0)),
% 0.23/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_72])])).
% 0.23/0.55  fof(f920,plain,(
% 0.23/0.55    spl4_72 | ~spl4_70),
% 0.23/0.55    inference(avatar_split_clause,[],[f908,f896,f917])).
% 0.23/0.55  fof(f896,plain,(
% 0.23/0.55    spl4_70 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.23/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_70])])).
% 0.23/0.55  fof(f908,plain,(
% 0.23/0.55    r1_tarski(sK2,k1_xboole_0) | ~spl4_70),
% 0.23/0.55    inference(resolution,[],[f898,f59])).
% 0.23/0.55  fof(f59,plain,(
% 0.23/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f39])).
% 0.23/0.55  fof(f39,plain,(
% 0.23/0.55    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.23/0.55    inference(nnf_transformation,[],[f5])).
% 0.23/0.55  fof(f5,axiom,(
% 0.23/0.55    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.23/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.23/0.55  fof(f898,plain,(
% 0.23/0.55    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl4_70),
% 0.23/0.55    inference(avatar_component_clause,[],[f896])).
% 0.23/0.55  fof(f899,plain,(
% 0.23/0.55    spl4_70 | ~spl4_69),
% 0.23/0.55    inference(avatar_split_clause,[],[f892,f882,f896])).
% 0.23/0.55  fof(f882,plain,(
% 0.23/0.55    spl4_69 <=> ! [X0] : m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))),
% 0.23/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_69])])).
% 0.23/0.55  % (21436)Refutation not found, incomplete strategy% (21436)------------------------------
% 0.23/0.55  % (21436)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.55  % (21436)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.55  
% 0.23/0.55  % (21436)Memory used [KB]: 10618
% 0.23/0.55  % (21436)Time elapsed: 0.119 s
% 0.23/0.55  % (21436)------------------------------
% 0.23/0.55  % (21436)------------------------------
% 0.23/0.55  % (21450)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.23/0.56  % (21459)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.23/0.56  fof(f892,plain,(
% 0.23/0.56    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl4_69),
% 0.23/0.56    inference(superposition,[],[f883,f72])).
% 0.23/0.56  fof(f72,plain,(
% 0.23/0.56    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.23/0.56    inference(equality_resolution,[],[f62])).
% 0.23/0.56  fof(f62,plain,(
% 0.23/0.56    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.23/0.56    inference(cnf_transformation,[],[f41])).
% 0.23/0.56  fof(f41,plain,(
% 0.23/0.56    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.23/0.56    inference(flattening,[],[f40])).
% 0.23/0.56  fof(f40,plain,(
% 0.23/0.56    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.23/0.56    inference(nnf_transformation,[],[f3])).
% 0.23/0.56  fof(f3,axiom,(
% 0.23/0.56    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.23/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.23/0.56  fof(f883,plain,(
% 0.23/0.56    ( ! [X0] : (m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))) ) | ~spl4_69),
% 0.23/0.56    inference(avatar_component_clause,[],[f882])).
% 0.23/0.56  fof(f884,plain,(
% 0.23/0.56    spl4_69 | ~spl4_9 | ~spl4_13 | ~spl4_29 | ~spl4_41),
% 0.23/0.56    inference(avatar_split_clause,[],[f880,f506,f322,f180,f137,f882])).
% 0.23/0.56  fof(f137,plain,(
% 0.23/0.56    spl4_9 <=> v1_relat_1(sK2)),
% 0.23/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.23/0.56  fof(f180,plain,(
% 0.23/0.56    spl4_13 <=> r1_tarski(k2_relat_1(sK2),sK0)),
% 0.23/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.23/0.56  fof(f322,plain,(
% 0.23/0.56    spl4_29 <=> ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.23/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 0.23/0.56  fof(f506,plain,(
% 0.23/0.56    spl4_41 <=> k1_xboole_0 = k1_relat_1(sK2)),
% 0.23/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).
% 0.23/0.56  fof(f880,plain,(
% 0.23/0.56    ( ! [X0] : (m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))) ) | (~spl4_9 | ~spl4_13 | ~spl4_29 | ~spl4_41)),
% 0.23/0.56    inference(subsumption_resolution,[],[f879,f323])).
% 0.23/0.56  fof(f323,plain,(
% 0.23/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl4_29),
% 0.23/0.56    inference(avatar_component_clause,[],[f322])).
% 0.23/0.56  fof(f879,plain,(
% 0.23/0.56    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))) ) | (~spl4_9 | ~spl4_13 | ~spl4_41)),
% 0.23/0.56    inference(forward_demodulation,[],[f199,f508])).
% 0.23/0.56  fof(f508,plain,(
% 0.23/0.56    k1_xboole_0 = k1_relat_1(sK2) | ~spl4_41),
% 0.23/0.56    inference(avatar_component_clause,[],[f506])).
% 0.23/0.56  fof(f199,plain,(
% 0.23/0.56    ( ! [X0] : (m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) | ~r1_tarski(k1_relat_1(sK2),X0)) ) | (~spl4_9 | ~spl4_13)),
% 0.23/0.56    inference(subsumption_resolution,[],[f196,f139])).
% 0.23/0.56  fof(f139,plain,(
% 0.23/0.56    v1_relat_1(sK2) | ~spl4_9),
% 0.23/0.56    inference(avatar_component_clause,[],[f137])).
% 0.23/0.57  fof(f196,plain,(
% 0.23/0.57    ( ! [X0] : (m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) | ~r1_tarski(k1_relat_1(sK2),X0) | ~v1_relat_1(sK2)) ) | ~spl4_13),
% 0.23/0.57    inference(resolution,[],[f182,f64])).
% 0.23/0.57  fof(f64,plain,(
% 0.23/0.57    ( ! [X2,X0,X1] : (~r1_tarski(k2_relat_1(X2),X1) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 0.23/0.57    inference(cnf_transformation,[],[f25])).
% 0.23/0.57  fof(f25,plain,(
% 0.23/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.23/0.57    inference(flattening,[],[f24])).
% 0.23/0.57  fof(f24,plain,(
% 0.23/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 0.23/0.57    inference(ennf_transformation,[],[f13])).
% 0.23/0.57  fof(f13,axiom,(
% 0.23/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.23/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).
% 0.23/0.57  fof(f182,plain,(
% 0.23/0.57    r1_tarski(k2_relat_1(sK2),sK0) | ~spl4_13),
% 0.23/0.57    inference(avatar_component_clause,[],[f180])).
% 0.23/0.57  fof(f678,plain,(
% 0.23/0.57    ~spl4_12 | spl4_54),
% 0.23/0.57    inference(avatar_contradiction_clause,[],[f677])).
% 0.23/0.57  fof(f677,plain,(
% 0.23/0.57    $false | (~spl4_12 | spl4_54)),
% 0.23/0.57    inference(subsumption_resolution,[],[f675,f176])).
% 0.23/0.57  fof(f176,plain,(
% 0.23/0.57    r1_tarski(k1_relat_1(sK2),sK1) | ~spl4_12),
% 0.23/0.57    inference(avatar_component_clause,[],[f174])).
% 0.23/0.57  fof(f174,plain,(
% 0.23/0.57    spl4_12 <=> r1_tarski(k1_relat_1(sK2),sK1)),
% 0.23/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.23/0.57  fof(f675,plain,(
% 0.23/0.57    ~r1_tarski(k1_relat_1(sK2),sK1) | spl4_54),
% 0.23/0.57    inference(resolution,[],[f672,f60])).
% 0.23/0.57  fof(f60,plain,(
% 0.23/0.57    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.23/0.57    inference(cnf_transformation,[],[f39])).
% 0.23/0.57  fof(f672,plain,(
% 0.23/0.57    ~m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK1)) | spl4_54),
% 0.23/0.57    inference(avatar_component_clause,[],[f670])).
% 0.23/0.57  fof(f670,plain,(
% 0.23/0.57    spl4_54 <=> m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK1))),
% 0.23/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).
% 0.23/0.57  fof(f673,plain,(
% 0.23/0.57    ~spl4_54 | ~spl4_42 | ~spl4_52),
% 0.23/0.57    inference(avatar_split_clause,[],[f667,f618,f510,f670])).
% 0.23/0.57  fof(f510,plain,(
% 0.23/0.57    spl4_42 <=> ! [X0] : (~m1_subset_1(sK3(X0,k1_relat_1(sK2)),sK1) | ~m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(X0)))),
% 0.23/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).
% 0.23/0.57  fof(f618,plain,(
% 0.23/0.57    spl4_52 <=> m1_subset_1(sK3(sK1,k1_relat_1(sK2)),sK1)),
% 0.23/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).
% 0.23/0.57  fof(f667,plain,(
% 0.23/0.57    ~m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK1)) | (~spl4_42 | ~spl4_52)),
% 0.23/0.57    inference(resolution,[],[f620,f511])).
% 0.23/0.57  fof(f511,plain,(
% 0.23/0.57    ( ! [X0] : (~m1_subset_1(sK3(X0,k1_relat_1(sK2)),sK1) | ~m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(X0))) ) | ~spl4_42),
% 0.23/0.57    inference(avatar_component_clause,[],[f510])).
% 0.23/0.57  fof(f620,plain,(
% 0.23/0.57    m1_subset_1(sK3(sK1,k1_relat_1(sK2)),sK1) | ~spl4_52),
% 0.23/0.57    inference(avatar_component_clause,[],[f618])).
% 0.23/0.57  fof(f621,plain,(
% 0.23/0.57    spl4_52 | ~spl4_12 | spl4_41),
% 0.23/0.57    inference(avatar_split_clause,[],[f528,f506,f174,f618])).
% 0.23/0.57  fof(f528,plain,(
% 0.23/0.57    m1_subset_1(sK3(sK1,k1_relat_1(sK2)),sK1) | (~spl4_12 | spl4_41)),
% 0.23/0.57    inference(subsumption_resolution,[],[f526,f507])).
% 0.23/0.57  fof(f507,plain,(
% 0.23/0.57    k1_xboole_0 != k1_relat_1(sK2) | spl4_41),
% 0.23/0.57    inference(avatar_component_clause,[],[f506])).
% 0.23/0.57  fof(f526,plain,(
% 0.23/0.57    m1_subset_1(sK3(sK1,k1_relat_1(sK2)),sK1) | k1_xboole_0 = k1_relat_1(sK2) | ~spl4_12),
% 0.23/0.57    inference(resolution,[],[f176,f154])).
% 0.23/0.57  fof(f154,plain,(
% 0.23/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(sK3(X1,X0),X1) | k1_xboole_0 = X0) )),
% 0.23/0.57    inference(resolution,[],[f54,f60])).
% 0.23/0.57  fof(f54,plain,(
% 0.23/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k1_xboole_0 = X1 | m1_subset_1(sK3(X0,X1),X0)) )),
% 0.23/0.57    inference(cnf_transformation,[],[f36])).
% 0.23/0.57  fof(f36,plain,(
% 0.23/0.57    ! [X0,X1] : ((r2_hidden(sK3(X0,X1),X1) & m1_subset_1(sK3(X0,X1),X0)) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.23/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f23,f35])).
% 0.23/0.57  fof(f35,plain,(
% 0.23/0.57    ! [X1,X0] : (? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,X0)) => (r2_hidden(sK3(X0,X1),X1) & m1_subset_1(sK3(X0,X1),X0)))),
% 0.23/0.57    introduced(choice_axiom,[])).
% 0.23/0.57  fof(f23,plain,(
% 0.23/0.57    ! [X0,X1] : (? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.23/0.57    inference(flattening,[],[f22])).
% 0.23/0.57  fof(f22,plain,(
% 0.23/0.57    ! [X0,X1] : ((? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | k1_xboole_0 = X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.23/0.57    inference(ennf_transformation,[],[f4])).
% 0.23/0.57  fof(f4,axiom,(
% 0.23/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ~(! [X2] : (m1_subset_1(X2,X0) => ~r2_hidden(X2,X1)) & k1_xboole_0 != X1))),
% 0.23/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_subset_1)).
% 0.23/0.57  fof(f512,plain,(
% 0.23/0.57    spl4_41 | spl4_42 | ~spl4_14),
% 0.23/0.57    inference(avatar_split_clause,[],[f491,f186,f510,f506])).
% 0.23/0.57  fof(f186,plain,(
% 0.23/0.57    spl4_14 <=> k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2)),
% 0.23/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.23/0.57  fof(f491,plain,(
% 0.23/0.57    ( ! [X0] : (~m1_subset_1(sK3(X0,k1_relat_1(sK2)),sK1) | ~m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(X0)) | k1_xboole_0 = k1_relat_1(sK2)) ) | ~spl4_14),
% 0.23/0.57    inference(forward_demodulation,[],[f490,f188])).
% 0.23/0.57  fof(f188,plain,(
% 0.23/0.57    k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2) | ~spl4_14),
% 0.23/0.57    inference(avatar_component_clause,[],[f186])).
% 0.23/0.57  fof(f490,plain,(
% 0.23/0.57    ( ! [X0] : (~m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(X0)) | k1_xboole_0 = k1_relat_1(sK2) | ~m1_subset_1(sK3(X0,k1_relset_1(sK1,sK0,sK2)),sK1)) ) | ~spl4_14),
% 0.23/0.57    inference(forward_demodulation,[],[f489,f188])).
% 0.23/0.57  fof(f489,plain,(
% 0.23/0.57    ( ! [X0] : (k1_xboole_0 = k1_relat_1(sK2) | ~m1_subset_1(k1_relset_1(sK1,sK0,sK2),k1_zfmisc_1(X0)) | ~m1_subset_1(sK3(X0,k1_relset_1(sK1,sK0,sK2)),sK1)) ) | ~spl4_14),
% 0.23/0.57    inference(forward_demodulation,[],[f160,f188])).
% 0.23/0.57  fof(f160,plain,(
% 0.23/0.57    ( ! [X0] : (k1_xboole_0 = k1_relset_1(sK1,sK0,sK2) | ~m1_subset_1(k1_relset_1(sK1,sK0,sK2),k1_zfmisc_1(X0)) | ~m1_subset_1(sK3(X0,k1_relset_1(sK1,sK0,sK2)),sK1)) )),
% 0.23/0.57    inference(resolution,[],[f55,f46])).
% 0.23/0.57  fof(f46,plain,(
% 0.23/0.57    ( ! [X3] : (~r2_hidden(X3,k1_relset_1(sK1,sK0,sK2)) | ~m1_subset_1(X3,sK1)) )),
% 0.23/0.57    inference(cnf_transformation,[],[f32])).
% 0.23/0.57  fof(f32,plain,(
% 0.23/0.57    ((! [X3] : (~r2_hidden(X3,k1_relset_1(sK1,sK0,sK2)) | ~m1_subset_1(X3,sK1)) & k1_xboole_0 != k2_relset_1(sK1,sK0,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 0.23/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f31,f30,f29])).
% 0.23/0.57  fof(f29,plain,(
% 0.23/0.57    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k1_relset_1(X1,X0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,X0,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k1_relset_1(X1,sK0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,sK0,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 0.23/0.57    introduced(choice_axiom,[])).
% 0.23/0.57  fof(f30,plain,(
% 0.23/0.57    ? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k1_relset_1(X1,sK0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,sK0,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))) & ~v1_xboole_0(X1)) => (? [X2] : (! [X3] : (~r2_hidden(X3,k1_relset_1(sK1,sK0,X2)) | ~m1_subset_1(X3,sK1)) & k1_xboole_0 != k2_relset_1(sK1,sK0,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))) & ~v1_xboole_0(sK1))),
% 0.23/0.57    introduced(choice_axiom,[])).
% 0.23/0.57  fof(f31,plain,(
% 0.23/0.57    ? [X2] : (! [X3] : (~r2_hidden(X3,k1_relset_1(sK1,sK0,X2)) | ~m1_subset_1(X3,sK1)) & k1_xboole_0 != k2_relset_1(sK1,sK0,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))) => (! [X3] : (~r2_hidden(X3,k1_relset_1(sK1,sK0,sK2)) | ~m1_subset_1(X3,sK1)) & k1_xboole_0 != k2_relset_1(sK1,sK0,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))))),
% 0.23/0.57    introduced(choice_axiom,[])).
% 0.23/0.57  fof(f17,plain,(
% 0.23/0.57    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k1_relset_1(X1,X0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,X0,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.23/0.57    inference(flattening,[],[f16])).
% 0.23/0.57  fof(f16,plain,(
% 0.23/0.57    ? [X0] : (? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X3,k1_relset_1(X1,X0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.23/0.57    inference(ennf_transformation,[],[f15])).
% 0.23/0.57  fof(f15,negated_conjecture,(
% 0.23/0.57    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k1_relset_1(X1,X0,X2))) & k1_xboole_0 != k2_relset_1(X1,X0,X2)))))),
% 0.23/0.57    inference(negated_conjecture,[],[f14])).
% 0.23/0.57  fof(f14,conjecture,(
% 0.23/0.57    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k1_relset_1(X1,X0,X2))) & k1_xboole_0 != k2_relset_1(X1,X0,X2)))))),
% 0.23/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_relset_1)).
% 0.23/0.57  fof(f55,plain,(
% 0.23/0.57    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.23/0.57    inference(cnf_transformation,[],[f36])).
% 0.23/0.57  fof(f446,plain,(
% 0.23/0.57    spl4_36 | ~spl4_38),
% 0.23/0.57    inference(avatar_contradiction_clause,[],[f445])).
% 0.23/0.57  fof(f445,plain,(
% 0.23/0.57    $false | (spl4_36 | ~spl4_38)),
% 0.23/0.57    inference(subsumption_resolution,[],[f435,f408])).
% 0.23/0.57  fof(f408,plain,(
% 0.23/0.57    k1_xboole_0 != k2_relat_1(k1_xboole_0) | spl4_36),
% 0.23/0.57    inference(avatar_component_clause,[],[f406])).
% 0.23/0.57  fof(f406,plain,(
% 0.23/0.57    spl4_36 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.23/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 0.23/0.57  fof(f435,plain,(
% 0.23/0.57    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl4_38),
% 0.23/0.57    inference(resolution,[],[f424,f48])).
% 0.23/0.57  fof(f424,plain,(
% 0.23/0.57    ( ! [X0] : (r1_tarski(k2_relat_1(k1_xboole_0),X0)) ) | ~spl4_38),
% 0.23/0.57    inference(avatar_component_clause,[],[f423])).
% 0.23/0.57  fof(f423,plain,(
% 0.23/0.57    spl4_38 <=> ! [X0] : r1_tarski(k2_relat_1(k1_xboole_0),X0)),
% 0.23/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).
% 0.23/0.57  fof(f425,plain,(
% 0.23/0.57    spl4_38 | ~spl4_3 | ~spl4_31),
% 0.23/0.57    inference(avatar_split_clause,[],[f358,f354,f85,f423])).
% 0.23/0.57  fof(f85,plain,(
% 0.23/0.57    spl4_3 <=> v1_relat_1(k1_xboole_0)),
% 0.23/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.23/0.57  fof(f354,plain,(
% 0.23/0.57    spl4_31 <=> ! [X3] : v5_relat_1(k1_xboole_0,X3)),
% 0.23/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).
% 0.23/0.57  fof(f358,plain,(
% 0.23/0.57    ( ! [X0] : (r1_tarski(k2_relat_1(k1_xboole_0),X0)) ) | (~spl4_3 | ~spl4_31)),
% 0.23/0.57    inference(subsumption_resolution,[],[f357,f87])).
% 0.23/0.57  fof(f87,plain,(
% 0.23/0.57    v1_relat_1(k1_xboole_0) | ~spl4_3),
% 0.23/0.57    inference(avatar_component_clause,[],[f85])).
% 0.23/0.57  fof(f357,plain,(
% 0.23/0.57    ( ! [X0] : (r1_tarski(k2_relat_1(k1_xboole_0),X0) | ~v1_relat_1(k1_xboole_0)) ) | ~spl4_31),
% 0.23/0.57    inference(resolution,[],[f355,f50])).
% 0.23/0.57  fof(f50,plain,(
% 0.23/0.57    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.23/0.57    inference(cnf_transformation,[],[f33])).
% 0.23/0.57  fof(f33,plain,(
% 0.23/0.57    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.23/0.57    inference(nnf_transformation,[],[f20])).
% 0.23/0.57  fof(f20,plain,(
% 0.23/0.57    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.23/0.57    inference(ennf_transformation,[],[f8])).
% 0.23/0.57  fof(f8,axiom,(
% 0.23/0.57    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.23/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.23/0.57  fof(f355,plain,(
% 0.23/0.57    ( ! [X3] : (v5_relat_1(k1_xboole_0,X3)) ) | ~spl4_31),
% 0.23/0.57    inference(avatar_component_clause,[],[f354])).
% 0.23/0.57  fof(f409,plain,(
% 0.23/0.57    ~spl4_36 | spl4_28 | ~spl4_32),
% 0.23/0.57    inference(avatar_split_clause,[],[f404,f369,f308,f406])).
% 0.23/0.57  fof(f308,plain,(
% 0.23/0.57    spl4_28 <=> k1_xboole_0 = k2_relset_1(sK1,sK0,k1_xboole_0)),
% 0.23/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 0.23/0.57  fof(f369,plain,(
% 0.23/0.57    spl4_32 <=> k2_relat_1(k1_xboole_0) = k2_relset_1(sK1,sK0,k1_xboole_0)),
% 0.23/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 0.23/0.57  fof(f404,plain,(
% 0.23/0.57    k1_xboole_0 != k2_relat_1(k1_xboole_0) | (spl4_28 | ~spl4_32)),
% 0.23/0.57    inference(superposition,[],[f310,f371])).
% 0.23/0.57  fof(f371,plain,(
% 0.23/0.57    k2_relat_1(k1_xboole_0) = k2_relset_1(sK1,sK0,k1_xboole_0) | ~spl4_32),
% 0.23/0.57    inference(avatar_component_clause,[],[f369])).
% 0.23/0.57  fof(f310,plain,(
% 0.23/0.57    k1_xboole_0 != k2_relset_1(sK1,sK0,k1_xboole_0) | spl4_28),
% 0.23/0.57    inference(avatar_component_clause,[],[f308])).
% 0.23/0.57  fof(f387,plain,(
% 0.23/0.57    spl4_26 | ~spl4_29),
% 0.23/0.57    inference(avatar_contradiction_clause,[],[f386])).
% 0.23/0.57  fof(f386,plain,(
% 0.23/0.57    $false | (spl4_26 | ~spl4_29)),
% 0.23/0.57    inference(subsumption_resolution,[],[f384,f323])).
% 0.23/0.57  fof(f384,plain,(
% 0.23/0.57    ~r1_tarski(k1_xboole_0,k2_zfmisc_1(sK1,sK0)) | spl4_26),
% 0.23/0.57    inference(resolution,[],[f299,f60])).
% 0.23/0.57  fof(f299,plain,(
% 0.23/0.57    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl4_26),
% 0.23/0.57    inference(avatar_component_clause,[],[f298])).
% 0.23/0.57  fof(f298,plain,(
% 0.23/0.57    spl4_26 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.23/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 0.23/0.57  fof(f372,plain,(
% 0.23/0.57    spl4_32 | ~spl4_26),
% 0.23/0.57    inference(avatar_split_clause,[],[f314,f298,f369])).
% 0.23/0.57  fof(f314,plain,(
% 0.23/0.57    k2_relat_1(k1_xboole_0) = k2_relset_1(sK1,sK0,k1_xboole_0) | ~spl4_26),
% 0.23/0.57    inference(resolution,[],[f300,f66])).
% 0.23/0.57  fof(f66,plain,(
% 0.23/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.23/0.57    inference(cnf_transformation,[],[f27])).
% 0.23/0.57  fof(f27,plain,(
% 0.23/0.57    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.23/0.57    inference(ennf_transformation,[],[f12])).
% 0.23/0.57  fof(f12,axiom,(
% 0.23/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.23/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.23/0.57  fof(f300,plain,(
% 0.23/0.57    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_26),
% 0.23/0.57    inference(avatar_component_clause,[],[f298])).
% 0.23/0.57  fof(f356,plain,(
% 0.23/0.57    spl4_31 | ~spl4_29),
% 0.23/0.57    inference(avatar_split_clause,[],[f330,f322,f354])).
% 0.23/0.57  fof(f330,plain,(
% 0.23/0.57    ( ! [X3] : (v5_relat_1(k1_xboole_0,X3)) ) | ~spl4_29),
% 0.23/0.57    inference(resolution,[],[f323,f142])).
% 0.23/0.57  fof(f142,plain,(
% 0.23/0.57    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_zfmisc_1(X2,X1)) | v5_relat_1(X0,X1)) )),
% 0.23/0.57    inference(resolution,[],[f68,f60])).
% 0.23/0.57  fof(f68,plain,(
% 0.23/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.23/0.57    inference(cnf_transformation,[],[f28])).
% 0.23/0.57  fof(f28,plain,(
% 0.23/0.57    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.23/0.57    inference(ennf_transformation,[],[f10])).
% 0.23/0.57  fof(f10,axiom,(
% 0.23/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.23/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.23/0.57  fof(f324,plain,(
% 0.23/0.57    spl4_29 | ~spl4_20),
% 0.23/0.57    inference(avatar_split_clause,[],[f268,f232,f322])).
% 0.23/0.57  fof(f232,plain,(
% 0.23/0.57    spl4_20 <=> ! [X0] : r1_tarski(k1_relat_1(k1_xboole_0),X0)),
% 0.23/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.23/0.57  fof(f268,plain,(
% 0.23/0.57    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl4_20),
% 0.23/0.57    inference(backward_demodulation,[],[f233,f243])).
% 0.23/0.57  fof(f243,plain,(
% 0.23/0.57    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl4_20),
% 0.23/0.57    inference(resolution,[],[f233,f48])).
% 0.23/0.57  fof(f233,plain,(
% 0.23/0.57    ( ! [X0] : (r1_tarski(k1_relat_1(k1_xboole_0),X0)) ) | ~spl4_20),
% 0.23/0.57    inference(avatar_component_clause,[],[f232])).
% 0.23/0.57  fof(f311,plain,(
% 0.23/0.57    ~spl4_28 | spl4_5 | ~spl4_25),
% 0.23/0.57    inference(avatar_split_clause,[],[f284,f279,f96,f308])).
% 0.23/0.57  fof(f96,plain,(
% 0.23/0.57    spl4_5 <=> k1_xboole_0 = k2_relset_1(sK1,sK0,sK2)),
% 0.23/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.23/0.57  fof(f284,plain,(
% 0.23/0.57    k1_xboole_0 != k2_relset_1(sK1,sK0,k1_xboole_0) | (spl4_5 | ~spl4_25)),
% 0.23/0.57    inference(backward_demodulation,[],[f98,f281])).
% 0.23/0.57  fof(f281,plain,(
% 0.23/0.57    k1_xboole_0 = sK2 | ~spl4_25),
% 0.23/0.57    inference(avatar_component_clause,[],[f279])).
% 0.23/0.57  fof(f98,plain,(
% 0.23/0.57    k1_xboole_0 != k2_relset_1(sK1,sK0,sK2) | spl4_5),
% 0.23/0.57    inference(avatar_component_clause,[],[f96])).
% 0.23/0.57  fof(f234,plain,(
% 0.23/0.57    spl4_20 | ~spl4_3),
% 0.23/0.57    inference(avatar_split_clause,[],[f226,f85,f232])).
% 0.23/0.57  fof(f226,plain,(
% 0.23/0.57    ( ! [X0] : (r1_tarski(k1_relat_1(k1_xboole_0),X0)) ) | ~spl4_3),
% 0.23/0.57    inference(subsumption_resolution,[],[f225,f87])).
% 0.23/0.57  fof(f225,plain,(
% 0.23/0.57    ( ! [X0] : (r1_tarski(k1_relat_1(k1_xboole_0),X0) | ~v1_relat_1(k1_xboole_0)) )),
% 0.23/0.57    inference(resolution,[],[f223,f52])).
% 0.23/0.57  fof(f52,plain,(
% 0.23/0.57    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.23/0.57    inference(cnf_transformation,[],[f34])).
% 0.23/0.57  fof(f34,plain,(
% 0.23/0.57    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.23/0.57    inference(nnf_transformation,[],[f21])).
% 0.23/0.57  fof(f21,plain,(
% 0.23/0.57    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.23/0.57    inference(ennf_transformation,[],[f7])).
% 0.23/0.57  fof(f7,axiom,(
% 0.23/0.57    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.23/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 0.23/0.57  fof(f223,plain,(
% 0.23/0.57    ( ! [X0] : (v4_relat_1(k1_xboole_0,X0)) )),
% 0.23/0.57    inference(resolution,[],[f220,f69])).
% 0.23/0.57  fof(f69,plain,(
% 0.23/0.57    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.23/0.57    inference(equality_resolution,[],[f57])).
% 0.23/0.57  fof(f57,plain,(
% 0.23/0.57    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.23/0.57    inference(cnf_transformation,[],[f38])).
% 0.23/0.57  fof(f38,plain,(
% 0.23/0.57    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.23/0.57    inference(flattening,[],[f37])).
% 0.23/0.57  fof(f37,plain,(
% 0.23/0.57    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.23/0.57    inference(nnf_transformation,[],[f1])).
% 0.23/0.57  fof(f1,axiom,(
% 0.23/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.23/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.23/0.57  fof(f220,plain,(
% 0.23/0.57    ( ! [X0,X1] : (~r1_tarski(X0,k1_xboole_0) | v4_relat_1(X0,X1)) )),
% 0.23/0.57    inference(resolution,[],[f134,f60])).
% 0.23/0.57  fof(f134,plain,(
% 0.23/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | v4_relat_1(X1,X0)) )),
% 0.23/0.57    inference(superposition,[],[f67,f71])).
% 0.23/0.57  fof(f71,plain,(
% 0.23/0.57    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.23/0.57    inference(equality_resolution,[],[f63])).
% 0.23/0.57  fof(f63,plain,(
% 0.23/0.57    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.23/0.57    inference(cnf_transformation,[],[f41])).
% 0.23/0.57  fof(f67,plain,(
% 0.23/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.23/0.57    inference(cnf_transformation,[],[f28])).
% 0.23/0.57  fof(f189,plain,(
% 0.23/0.57    spl4_14 | ~spl4_4),
% 0.23/0.57    inference(avatar_split_clause,[],[f163,f91,f186])).
% 0.23/0.57  fof(f91,plain,(
% 0.23/0.57    spl4_4 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.23/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.23/0.57  fof(f163,plain,(
% 0.23/0.57    k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2) | ~spl4_4),
% 0.23/0.57    inference(resolution,[],[f65,f93])).
% 0.23/0.57  fof(f93,plain,(
% 0.23/0.57    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_4),
% 0.23/0.57    inference(avatar_component_clause,[],[f91])).
% 0.23/0.57  fof(f65,plain,(
% 0.23/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.23/0.57    inference(cnf_transformation,[],[f26])).
% 0.23/0.57  fof(f26,plain,(
% 0.23/0.57    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.23/0.57    inference(ennf_transformation,[],[f11])).
% 0.23/0.57  fof(f11,axiom,(
% 0.23/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.23/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.23/0.57  fof(f183,plain,(
% 0.23/0.57    spl4_13 | ~spl4_9 | ~spl4_11),
% 0.23/0.57    inference(avatar_split_clause,[],[f168,f156,f137,f180])).
% 0.23/0.57  fof(f156,plain,(
% 0.23/0.57    spl4_11 <=> v5_relat_1(sK2,sK0)),
% 0.23/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.23/0.57  fof(f168,plain,(
% 0.23/0.57    r1_tarski(k2_relat_1(sK2),sK0) | (~spl4_9 | ~spl4_11)),
% 0.23/0.57    inference(subsumption_resolution,[],[f167,f139])).
% 0.23/0.57  fof(f167,plain,(
% 0.23/0.57    r1_tarski(k2_relat_1(sK2),sK0) | ~v1_relat_1(sK2) | ~spl4_11),
% 0.23/0.57    inference(resolution,[],[f158,f50])).
% 0.23/0.57  fof(f158,plain,(
% 0.23/0.57    v5_relat_1(sK2,sK0) | ~spl4_11),
% 0.23/0.57    inference(avatar_component_clause,[],[f156])).
% 0.23/0.57  fof(f177,plain,(
% 0.23/0.57    spl4_12 | ~spl4_9 | ~spl4_10),
% 0.23/0.57    inference(avatar_split_clause,[],[f162,f149,f137,f174])).
% 0.23/0.57  fof(f149,plain,(
% 0.23/0.57    spl4_10 <=> v4_relat_1(sK2,sK1)),
% 0.23/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.23/0.57  fof(f162,plain,(
% 0.23/0.57    r1_tarski(k1_relat_1(sK2),sK1) | (~spl4_9 | ~spl4_10)),
% 0.23/0.57    inference(subsumption_resolution,[],[f161,f139])).
% 0.23/0.57  fof(f161,plain,(
% 0.23/0.57    r1_tarski(k1_relat_1(sK2),sK1) | ~v1_relat_1(sK2) | ~spl4_10),
% 0.23/0.57    inference(resolution,[],[f151,f52])).
% 0.23/0.57  fof(f151,plain,(
% 0.23/0.57    v4_relat_1(sK2,sK1) | ~spl4_10),
% 0.23/0.57    inference(avatar_component_clause,[],[f149])).
% 0.23/0.57  fof(f159,plain,(
% 0.23/0.57    spl4_11 | ~spl4_4),
% 0.23/0.57    inference(avatar_split_clause,[],[f141,f91,f156])).
% 0.23/0.57  fof(f141,plain,(
% 0.23/0.57    v5_relat_1(sK2,sK0) | ~spl4_4),
% 0.23/0.57    inference(resolution,[],[f68,f93])).
% 0.23/0.57  fof(f152,plain,(
% 0.23/0.57    spl4_10 | ~spl4_4),
% 0.23/0.57    inference(avatar_split_clause,[],[f132,f91,f149])).
% 0.23/0.57  fof(f132,plain,(
% 0.23/0.57    v4_relat_1(sK2,sK1) | ~spl4_4),
% 0.23/0.57    inference(resolution,[],[f67,f93])).
% 0.23/0.57  fof(f140,plain,(
% 0.23/0.57    spl4_9 | ~spl4_4),
% 0.23/0.57    inference(avatar_split_clause,[],[f128,f91,f137])).
% 0.23/0.57  fof(f128,plain,(
% 0.23/0.57    v1_relat_1(sK2) | ~spl4_4),
% 0.23/0.57    inference(resolution,[],[f108,f93])).
% 0.23/0.57  fof(f108,plain,(
% 0.23/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0)) )),
% 0.23/0.57    inference(resolution,[],[f47,f49])).
% 0.23/0.57  fof(f49,plain,(
% 0.23/0.57    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.23/0.57    inference(cnf_transformation,[],[f9])).
% 0.23/0.57  fof(f9,axiom,(
% 0.23/0.57    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.23/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.23/0.57  fof(f47,plain,(
% 0.23/0.57    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 0.23/0.57    inference(cnf_transformation,[],[f18])).
% 0.23/0.57  fof(f18,plain,(
% 0.23/0.57    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.23/0.57    inference(ennf_transformation,[],[f6])).
% 0.23/0.57  fof(f6,axiom,(
% 0.23/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.23/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.23/0.57  fof(f99,plain,(
% 0.23/0.57    ~spl4_5),
% 0.23/0.57    inference(avatar_split_clause,[],[f45,f96])).
% 0.23/0.57  fof(f45,plain,(
% 0.23/0.57    k1_xboole_0 != k2_relset_1(sK1,sK0,sK2)),
% 0.23/0.57    inference(cnf_transformation,[],[f32])).
% 0.23/0.57  fof(f94,plain,(
% 0.23/0.57    spl4_4),
% 0.23/0.57    inference(avatar_split_clause,[],[f44,f91])).
% 0.23/0.57  fof(f44,plain,(
% 0.23/0.57    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.23/0.57    inference(cnf_transformation,[],[f32])).
% 0.23/0.57  fof(f88,plain,(
% 0.23/0.57    spl4_3),
% 0.23/0.57    inference(avatar_split_clause,[],[f83,f85])).
% 0.23/0.57  fof(f83,plain,(
% 0.23/0.57    v1_relat_1(k1_xboole_0)),
% 0.23/0.57    inference(superposition,[],[f49,f71])).
% 0.23/0.57  % SZS output end Proof for theBenchmark
% 0.23/0.57  % (21437)------------------------------
% 0.23/0.57  % (21437)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.57  % (21437)Termination reason: Refutation
% 0.23/0.57  
% 0.23/0.57  % (21437)Memory used [KB]: 6652
% 0.23/0.57  % (21437)Time elapsed: 0.137 s
% 0.23/0.57  % (21437)------------------------------
% 0.23/0.57  % (21437)------------------------------
% 0.23/0.57  % (21434)Success in time 0.198 s
%------------------------------------------------------------------------------
