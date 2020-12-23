%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:36 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 153 expanded)
%              Number of leaves         :   26 (  64 expanded)
%              Depth                    :    8
%              Number of atoms          :  259 ( 412 expanded)
%              Number of equality atoms :   37 (  58 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f180,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f50,f55,f61,f79,f91,f104,f114,f120,f138,f152,f157,f164,f170,f178,f179])).

fof(f179,plain,
    ( k2_relset_1(sK1,sK0,sK2) != k2_relat_1(sK2)
    | r1_tarski(sK1,k2_relset_1(sK1,sK0,sK2))
    | ~ r1_tarski(sK1,k2_relat_1(sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f178,plain,
    ( ~ spl3_9
    | spl3_14
    | ~ spl3_18 ),
    inference(avatar_contradiction_clause,[],[f177])).

fof(f177,plain,
    ( $false
    | ~ spl3_9
    | spl3_14
    | ~ spl3_18 ),
    inference(subsumption_resolution,[],[f176,f137])).

fof(f137,plain,
    ( sK1 != k1_relat_1(sK2)
    | spl3_14 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl3_14
  <=> sK1 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f176,plain,
    ( sK1 = k1_relat_1(sK2)
    | ~ spl3_9
    | ~ spl3_18 ),
    inference(subsumption_resolution,[],[f173,f103])).

fof(f103,plain,
    ( r1_tarski(k1_relat_1(sK2),sK1)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl3_9
  <=> r1_tarski(k1_relat_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f173,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK1)
    | sK1 = k1_relat_1(sK2)
    | ~ spl3_18 ),
    inference(resolution,[],[f163,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
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

fof(f163,plain,
    ( r1_tarski(sK1,k1_relat_1(sK2))
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f161])).

fof(f161,plain,
    ( spl3_18
  <=> r1_tarski(sK1,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f170,plain,
    ( spl3_19
    | ~ spl3_1
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f159,f155,f47,f167])).

fof(f167,plain,
    ( spl3_19
  <=> r1_tarski(sK1,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f47,plain,
    ( spl3_1
  <=> r1_tarski(k6_relat_1(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f155,plain,
    ( spl3_17
  <=> ! [X2] :
        ( ~ r1_tarski(k6_relat_1(X2),sK2)
        | r1_tarski(X2,k2_relat_1(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f159,plain,
    ( r1_tarski(sK1,k2_relat_1(sK2))
    | ~ spl3_1
    | ~ spl3_17 ),
    inference(resolution,[],[f156,f49])).

fof(f49,plain,
    ( r1_tarski(k6_relat_1(sK1),sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f47])).

fof(f156,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k6_relat_1(X2),sK2)
        | r1_tarski(X2,k2_relat_1(sK2)) )
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f155])).

fof(f164,plain,
    ( spl3_18
    | ~ spl3_1
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f158,f150,f47,f161])).

fof(f150,plain,
    ( spl3_16
  <=> ! [X2] :
        ( ~ r1_tarski(k6_relat_1(X2),sK2)
        | r1_tarski(X2,k1_relat_1(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f158,plain,
    ( r1_tarski(sK1,k1_relat_1(sK2))
    | ~ spl3_1
    | ~ spl3_16 ),
    inference(resolution,[],[f151,f49])).

fof(f151,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k6_relat_1(X2),sK2)
        | r1_tarski(X2,k1_relat_1(sK2)) )
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f150])).

fof(f157,plain,
    ( spl3_17
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f140,f58,f155])).

fof(f58,plain,
    ( spl3_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f140,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k6_relat_1(X2),sK2)
        | r1_tarski(X2,k2_relat_1(sK2)) )
    | ~ spl3_3 ),
    inference(resolution,[],[f107,f60])).

fof(f60,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f58])).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k6_relat_1(X0),X1)
      | r1_tarski(X0,k2_relat_1(X1)) ) ),
    inference(forward_demodulation,[],[f105,f31])).

fof(f31,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

% (5601)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
fof(f105,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1)
      | r1_tarski(k2_relat_1(k6_relat_1(X0)),k2_relat_1(X1)) ) ),
    inference(resolution,[],[f33,f29])).

fof(f29,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(f152,plain,
    ( spl3_16
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f132,f58,f150])).

fof(f132,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k6_relat_1(X2),sK2)
        | r1_tarski(X2,k1_relat_1(sK2)) )
    | ~ spl3_3 ),
    inference(resolution,[],[f99,f60])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k6_relat_1(X0),X1)
      | r1_tarski(X0,k1_relat_1(X1)) ) ),
    inference(forward_demodulation,[],[f97,f30])).

fof(f30,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1)
      | r1_tarski(k1_relat_1(k6_relat_1(X0)),k1_relat_1(X1)) ) ),
    inference(resolution,[],[f32,f29])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f138,plain,
    ( ~ spl3_14
    | spl3_6
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f121,f117,f84,f135])).

fof(f84,plain,
    ( spl3_6
  <=> sK1 = k1_relset_1(sK1,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f117,plain,
    ( spl3_11
  <=> k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f121,plain,
    ( sK1 != k1_relat_1(sK2)
    | spl3_6
    | ~ spl3_11 ),
    inference(superposition,[],[f86,f119])).

fof(f119,plain,
    ( k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f117])).

fof(f86,plain,
    ( sK1 != k1_relset_1(sK1,sK0,sK2)
    | spl3_6 ),
    inference(avatar_component_clause,[],[f84])).

fof(f120,plain,
    ( spl3_11
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f115,f52,f117])).

fof(f52,plain,
    ( spl3_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f115,plain,
    ( k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2)
    | ~ spl3_2 ),
    inference(resolution,[],[f41,f54])).

fof(f54,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f52])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f114,plain,
    ( spl3_10
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f109,f52,f111])).

fof(f111,plain,
    ( spl3_10
  <=> k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f109,plain,
    ( k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2)
    | ~ spl3_2 ),
    inference(resolution,[],[f40,f54])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f104,plain,
    ( spl3_9
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f82,f76,f58,f101])).

fof(f76,plain,
    ( spl3_5
  <=> v4_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f82,plain,
    ( r1_tarski(k1_relat_1(sK2),sK1)
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f81,f60])).

fof(f81,plain,
    ( r1_tarski(k1_relat_1(sK2),sK1)
    | ~ v1_relat_1(sK2)
    | ~ spl3_5 ),
    inference(resolution,[],[f78,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

% (5599)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
fof(f78,plain,
    ( v4_relat_1(sK2,sK1)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f76])).

fof(f91,plain,
    ( ~ spl3_6
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f28,f88,f84])).

fof(f88,plain,
    ( spl3_7
  <=> r1_tarski(sK1,k2_relset_1(sK1,sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f28,plain,
    ( ~ r1_tarski(sK1,k2_relset_1(sK1,sK0,sK2))
    | sK1 != k1_relset_1(sK1,sK0,sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ( ~ r1_tarski(sK1,k2_relset_1(sK1,sK0,sK2))
      | sK1 != k1_relset_1(sK1,sK0,sK2) )
    & r1_tarski(k6_relat_1(sK1),sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f21])).

fof(f21,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_tarski(X1,k2_relset_1(X1,X0,X2))
          | k1_relset_1(X1,X0,X2) != X1 )
        & r1_tarski(k6_relat_1(X1),X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
   => ( ( ~ r1_tarski(sK1,k2_relset_1(sK1,sK0,sK2))
        | sK1 != k1_relset_1(sK1,sK0,sK2) )
      & r1_tarski(k6_relat_1(sK1),sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_tarski(X1,k2_relset_1(X1,X0,X2))
        | k1_relset_1(X1,X0,X2) != X1 )
      & r1_tarski(k6_relat_1(X1),X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_tarski(X1,k2_relset_1(X1,X0,X2))
        | k1_relset_1(X1,X0,X2) != X1 )
      & r1_tarski(k6_relat_1(X1),X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
       => ( r1_tarski(k6_relat_1(X1),X2)
         => ( r1_tarski(X1,k2_relset_1(X1,X0,X2))
            & k1_relset_1(X1,X0,X2) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( r1_tarski(k6_relat_1(X1),X2)
       => ( r1_tarski(X1,k2_relset_1(X1,X0,X2))
          & k1_relset_1(X1,X0,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relset_1)).

fof(f79,plain,
    ( spl3_5
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f74,f52,f76])).

fof(f74,plain,
    ( v4_relat_1(sK2,sK1)
    | ~ spl3_2 ),
    inference(resolution,[],[f42,f54])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f61,plain,
    ( spl3_3
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f56,f52,f58])).

fof(f56,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_2 ),
    inference(resolution,[],[f39,f54])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f55,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f26,f52])).

fof(f26,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f22])).

fof(f50,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f27,f47])).

fof(f27,plain,(
    r1_tarski(k6_relat_1(sK1),sK2) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:29:44 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.47  % (5595)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.49  % (5595)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f180,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f50,f55,f61,f79,f91,f104,f114,f120,f138,f152,f157,f164,f170,f178,f179])).
% 0.21/0.49  fof(f179,plain,(
% 0.21/0.49    k2_relset_1(sK1,sK0,sK2) != k2_relat_1(sK2) | r1_tarski(sK1,k2_relset_1(sK1,sK0,sK2)) | ~r1_tarski(sK1,k2_relat_1(sK2))),
% 0.21/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.49  fof(f178,plain,(
% 0.21/0.49    ~spl3_9 | spl3_14 | ~spl3_18),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f177])).
% 0.21/0.49  fof(f177,plain,(
% 0.21/0.49    $false | (~spl3_9 | spl3_14 | ~spl3_18)),
% 0.21/0.49    inference(subsumption_resolution,[],[f176,f137])).
% 0.21/0.49  fof(f137,plain,(
% 0.21/0.49    sK1 != k1_relat_1(sK2) | spl3_14),
% 0.21/0.49    inference(avatar_component_clause,[],[f135])).
% 0.21/0.49  fof(f135,plain,(
% 0.21/0.49    spl3_14 <=> sK1 = k1_relat_1(sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.49  fof(f176,plain,(
% 0.21/0.49    sK1 = k1_relat_1(sK2) | (~spl3_9 | ~spl3_18)),
% 0.21/0.49    inference(subsumption_resolution,[],[f173,f103])).
% 0.21/0.49  fof(f103,plain,(
% 0.21/0.49    r1_tarski(k1_relat_1(sK2),sK1) | ~spl3_9),
% 0.21/0.49    inference(avatar_component_clause,[],[f101])).
% 0.21/0.49  fof(f101,plain,(
% 0.21/0.49    spl3_9 <=> r1_tarski(k1_relat_1(sK2),sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.49  fof(f173,plain,(
% 0.21/0.49    ~r1_tarski(k1_relat_1(sK2),sK1) | sK1 = k1_relat_1(sK2) | ~spl3_18),
% 0.21/0.49    inference(resolution,[],[f163,f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.49    inference(flattening,[],[f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.49    inference(nnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.49  fof(f163,plain,(
% 0.21/0.49    r1_tarski(sK1,k1_relat_1(sK2)) | ~spl3_18),
% 0.21/0.49    inference(avatar_component_clause,[],[f161])).
% 0.21/0.49  fof(f161,plain,(
% 0.21/0.49    spl3_18 <=> r1_tarski(sK1,k1_relat_1(sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.21/0.49  fof(f170,plain,(
% 0.21/0.49    spl3_19 | ~spl3_1 | ~spl3_17),
% 0.21/0.49    inference(avatar_split_clause,[],[f159,f155,f47,f167])).
% 0.21/0.49  fof(f167,plain,(
% 0.21/0.49    spl3_19 <=> r1_tarski(sK1,k2_relat_1(sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    spl3_1 <=> r1_tarski(k6_relat_1(sK1),sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.49  fof(f155,plain,(
% 0.21/0.49    spl3_17 <=> ! [X2] : (~r1_tarski(k6_relat_1(X2),sK2) | r1_tarski(X2,k2_relat_1(sK2)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.49  fof(f159,plain,(
% 0.21/0.49    r1_tarski(sK1,k2_relat_1(sK2)) | (~spl3_1 | ~spl3_17)),
% 0.21/0.49    inference(resolution,[],[f156,f49])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    r1_tarski(k6_relat_1(sK1),sK2) | ~spl3_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f47])).
% 0.21/0.49  fof(f156,plain,(
% 0.21/0.49    ( ! [X2] : (~r1_tarski(k6_relat_1(X2),sK2) | r1_tarski(X2,k2_relat_1(sK2))) ) | ~spl3_17),
% 0.21/0.49    inference(avatar_component_clause,[],[f155])).
% 0.21/0.49  fof(f164,plain,(
% 0.21/0.49    spl3_18 | ~spl3_1 | ~spl3_16),
% 0.21/0.49    inference(avatar_split_clause,[],[f158,f150,f47,f161])).
% 0.21/0.49  fof(f150,plain,(
% 0.21/0.49    spl3_16 <=> ! [X2] : (~r1_tarski(k6_relat_1(X2),sK2) | r1_tarski(X2,k1_relat_1(sK2)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.50  fof(f158,plain,(
% 0.21/0.50    r1_tarski(sK1,k1_relat_1(sK2)) | (~spl3_1 | ~spl3_16)),
% 0.21/0.50    inference(resolution,[],[f151,f49])).
% 0.21/0.50  fof(f151,plain,(
% 0.21/0.50    ( ! [X2] : (~r1_tarski(k6_relat_1(X2),sK2) | r1_tarski(X2,k1_relat_1(sK2))) ) | ~spl3_16),
% 0.21/0.50    inference(avatar_component_clause,[],[f150])).
% 0.21/0.50  fof(f157,plain,(
% 0.21/0.50    spl3_17 | ~spl3_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f140,f58,f155])).
% 0.21/0.50  fof(f58,plain,(
% 0.21/0.50    spl3_3 <=> v1_relat_1(sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.50  fof(f140,plain,(
% 0.21/0.50    ( ! [X2] : (~r1_tarski(k6_relat_1(X2),sK2) | r1_tarski(X2,k2_relat_1(sK2))) ) | ~spl3_3),
% 0.21/0.50    inference(resolution,[],[f107,f60])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    v1_relat_1(sK2) | ~spl3_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f58])).
% 0.21/0.50  fof(f107,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k6_relat_1(X0),X1) | r1_tarski(X0,k2_relat_1(X1))) )),
% 0.21/0.50    inference(forward_demodulation,[],[f105,f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.21/0.50  % (5601)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.50  fof(f105,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(k6_relat_1(X0),X1) | ~v1_relat_1(X1) | r1_tarski(k2_relat_1(k6_relat_1(X0)),k2_relat_1(X1))) )),
% 0.21/0.50    inference(resolution,[],[f33,f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_relat_1(X0) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(flattening,[],[f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).
% 0.21/0.50  fof(f152,plain,(
% 0.21/0.50    spl3_16 | ~spl3_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f132,f58,f150])).
% 0.21/0.50  fof(f132,plain,(
% 0.21/0.50    ( ! [X2] : (~r1_tarski(k6_relat_1(X2),sK2) | r1_tarski(X2,k1_relat_1(sK2))) ) | ~spl3_3),
% 0.21/0.50    inference(resolution,[],[f99,f60])).
% 0.21/0.50  fof(f99,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k6_relat_1(X0),X1) | r1_tarski(X0,k1_relat_1(X1))) )),
% 0.21/0.50    inference(forward_demodulation,[],[f97,f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f5])).
% 0.21/0.50  fof(f97,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(k6_relat_1(X0),X1) | ~v1_relat_1(X1) | r1_tarski(k1_relat_1(k6_relat_1(X0)),k1_relat_1(X1))) )),
% 0.21/0.50    inference(resolution,[],[f32,f29])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_relat_1(X0) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f138,plain,(
% 0.21/0.50    ~spl3_14 | spl3_6 | ~spl3_11),
% 0.21/0.50    inference(avatar_split_clause,[],[f121,f117,f84,f135])).
% 0.21/0.50  fof(f84,plain,(
% 0.21/0.50    spl3_6 <=> sK1 = k1_relset_1(sK1,sK0,sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.50  fof(f117,plain,(
% 0.21/0.50    spl3_11 <=> k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.50  fof(f121,plain,(
% 0.21/0.50    sK1 != k1_relat_1(sK2) | (spl3_6 | ~spl3_11)),
% 0.21/0.50    inference(superposition,[],[f86,f119])).
% 0.21/0.50  fof(f119,plain,(
% 0.21/0.50    k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2) | ~spl3_11),
% 0.21/0.50    inference(avatar_component_clause,[],[f117])).
% 0.21/0.50  fof(f86,plain,(
% 0.21/0.50    sK1 != k1_relset_1(sK1,sK0,sK2) | spl3_6),
% 0.21/0.50    inference(avatar_component_clause,[],[f84])).
% 0.21/0.50  fof(f120,plain,(
% 0.21/0.50    spl3_11 | ~spl3_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f115,f52,f117])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    spl3_2 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.50  fof(f115,plain,(
% 0.21/0.50    k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2) | ~spl3_2),
% 0.21/0.50    inference(resolution,[],[f41,f54])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl3_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f52])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.50  fof(f114,plain,(
% 0.21/0.50    spl3_10 | ~spl3_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f109,f52,f111])).
% 0.21/0.50  fof(f111,plain,(
% 0.21/0.50    spl3_10 <=> k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.50  fof(f109,plain,(
% 0.21/0.50    k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2) | ~spl3_2),
% 0.21/0.50    inference(resolution,[],[f40,f54])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.50  fof(f104,plain,(
% 0.21/0.50    spl3_9 | ~spl3_3 | ~spl3_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f82,f76,f58,f101])).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    spl3_5 <=> v4_relat_1(sK2,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.50  fof(f82,plain,(
% 0.21/0.50    r1_tarski(k1_relat_1(sK2),sK1) | (~spl3_3 | ~spl3_5)),
% 0.21/0.50    inference(subsumption_resolution,[],[f81,f60])).
% 0.21/0.50  fof(f81,plain,(
% 0.21/0.50    r1_tarski(k1_relat_1(sK2),sK1) | ~v1_relat_1(sK2) | ~spl3_5),
% 0.21/0.50    inference(resolution,[],[f78,f34])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(nnf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 0.21/0.50  % (5599)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.50  fof(f78,plain,(
% 0.21/0.50    v4_relat_1(sK2,sK1) | ~spl3_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f76])).
% 0.21/0.50  fof(f91,plain,(
% 0.21/0.50    ~spl3_6 | ~spl3_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f28,f88,f84])).
% 0.21/0.50  fof(f88,plain,(
% 0.21/0.50    spl3_7 <=> r1_tarski(sK1,k2_relset_1(sK1,sK0,sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ~r1_tarski(sK1,k2_relset_1(sK1,sK0,sK2)) | sK1 != k1_relset_1(sK1,sK0,sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    (~r1_tarski(sK1,k2_relset_1(sK1,sK0,sK2)) | sK1 != k1_relset_1(sK1,sK0,sK2)) & r1_tarski(k6_relat_1(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ? [X0,X1,X2] : ((~r1_tarski(X1,k2_relset_1(X1,X0,X2)) | k1_relset_1(X1,X0,X2) != X1) & r1_tarski(k6_relat_1(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) => ((~r1_tarski(sK1,k2_relset_1(sK1,sK0,sK2)) | sK1 != k1_relset_1(sK1,sK0,sK2)) & r1_tarski(k6_relat_1(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ? [X0,X1,X2] : ((~r1_tarski(X1,k2_relset_1(X1,X0,X2)) | k1_relset_1(X1,X0,X2) != X1) & r1_tarski(k6_relat_1(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.21/0.50    inference(flattening,[],[f12])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ? [X0,X1,X2] : (((~r1_tarski(X1,k2_relset_1(X1,X0,X2)) | k1_relset_1(X1,X0,X2) != X1) & r1_tarski(k6_relat_1(X1),X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.21/0.50    inference(ennf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (r1_tarski(k6_relat_1(X1),X2) => (r1_tarski(X1,k2_relset_1(X1,X0,X2)) & k1_relset_1(X1,X0,X2) = X1)))),
% 0.21/0.50    inference(negated_conjecture,[],[f10])).
% 0.21/0.50  fof(f10,conjecture,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (r1_tarski(k6_relat_1(X1),X2) => (r1_tarski(X1,k2_relset_1(X1,X0,X2)) & k1_relset_1(X1,X0,X2) = X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relset_1)).
% 0.21/0.50  fof(f79,plain,(
% 0.21/0.50    spl3_5 | ~spl3_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f74,f52,f76])).
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    v4_relat_1(sK2,sK1) | ~spl3_2),
% 0.21/0.50    inference(resolution,[],[f42,f54])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    spl3_3 | ~spl3_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f56,f52,f58])).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    v1_relat_1(sK2) | ~spl3_2),
% 0.21/0.50    inference(resolution,[],[f39,f54])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    spl3_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f26,f52])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    spl3_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f27,f47])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    r1_tarski(k6_relat_1(sK1),sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (5595)------------------------------
% 0.21/0.50  % (5595)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (5595)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (5595)Memory used [KB]: 6140
% 0.21/0.50  % (5595)Time elapsed: 0.086 s
% 0.21/0.50  % (5595)------------------------------
% 0.21/0.50  % (5595)------------------------------
% 0.21/0.50  % (5597)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.50  % (5599)Refutation not found, incomplete strategy% (5599)------------------------------
% 0.21/0.50  % (5599)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (5599)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (5599)Memory used [KB]: 10618
% 0.21/0.50  % (5599)Time elapsed: 0.091 s
% 0.21/0.50  % (5599)------------------------------
% 0.21/0.50  % (5599)------------------------------
% 0.21/0.50  % (5613)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.50  % (5592)Success in time 0.147 s
%------------------------------------------------------------------------------
