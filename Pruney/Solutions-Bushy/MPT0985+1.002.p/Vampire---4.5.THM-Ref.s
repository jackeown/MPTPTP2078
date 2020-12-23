%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0985+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:01 EST 2020

% Result     : Theorem 1.36s
% Output     : Refutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :  187 ( 765 expanded)
%              Number of leaves         :   35 ( 224 expanded)
%              Depth                    :   16
%              Number of atoms          :  612 (2599 expanded)
%              Number of equality atoms :   97 ( 389 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (3864)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
fof(f966,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f103,f119,f121,f129,f138,f152,f156,f168,f189,f193,f550,f692,f698,f747,f767,f876,f965])).

% (3866)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
fof(f965,plain,
    ( spl6_2
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_12
    | ~ spl6_28
    | ~ spl6_32 ),
    inference(avatar_contradiction_clause,[],[f961])).

fof(f961,plain,
    ( $false
    | spl6_2
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_12
    | ~ spl6_28
    | ~ spl6_32 ),
    inference(resolution,[],[f890,f850])).

fof(f850,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl6_6
    | ~ spl6_12
    | ~ spl6_28
    | ~ spl6_32 ),
    inference(backward_demodulation,[],[f797,f830])).

fof(f830,plain,
    ( k1_xboole_0 = sK3
    | ~ spl6_32 ),
    inference(resolution,[],[f743,f219])).

fof(f219,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 = X0 ) ),
    inference(backward_demodulation,[],[f207,f215])).

fof(f215,plain,(
    ! [X2] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X2) ),
    inference(resolution,[],[f211,f125])).

fof(f125,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f124])).

fof(f124,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f71,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f46,f47])).

fof(f47,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f211,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,k2_zfmisc_1(k1_xboole_0,X2))
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f207,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f207,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f131,f105])).

fof(f105,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(backward_demodulation,[],[f59,f104])).

fof(f104,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(resolution,[],[f60,f59])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

% (3859)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
fof(f16,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

fof(f59,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(f131,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f68,f60])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

fof(f743,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_32 ),
    inference(forward_demodulation,[],[f700,f215])).

fof(f700,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | ~ spl6_32 ),
    inference(backward_demodulation,[],[f55,f691])).

fof(f691,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_32 ),
    inference(avatar_component_clause,[],[f689])).

fof(f689,plain,
    ( spl6_32
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f55,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
      | ~ v1_funct_1(k2_funct_1(sK3)) )
    & sK2 = k2_relset_1(sK1,sK2,sK3)
    & v2_funct_1(sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f20,f41])).

fof(f41,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
          | ~ v1_funct_1(k2_funct_1(X2)) )
        & k2_relset_1(X0,X1,X2) = X1
        & v2_funct_1(X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
        | ~ v1_funct_1(k2_funct_1(sK3)) )
      & sK2 = k2_relset_1(sK1,sK2,sK3)
      & v2_funct_1(sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK3,sK1,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

fof(f797,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl6_6
    | ~ spl6_12
    | ~ spl6_28
    | ~ spl6_32 ),
    inference(backward_demodulation,[],[f699,f784])).

fof(f784,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_6
    | ~ spl6_12
    | ~ spl6_28 ),
    inference(backward_demodulation,[],[f196,f593])).

fof(f593,plain,
    ( k1_xboole_0 = k1_relat_1(k2_funct_1(sK3))
    | ~ spl6_6
    | ~ spl6_12
    | ~ spl6_28 ),
    inference(backward_demodulation,[],[f196,f569])).

fof(f569,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f567])).

fof(f567,plain,
    ( spl6_28
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f196,plain,
    ( sK2 = k1_relat_1(k2_funct_1(sK3))
    | ~ spl6_6
    | ~ spl6_12 ),
    inference(backward_demodulation,[],[f137,f187])).

fof(f187,plain,
    ( sK2 = k2_relat_1(sK3)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f185])).

fof(f185,plain,
    ( spl6_12
  <=> sK2 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f137,plain,
    ( k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl6_6
  <=> k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f699,plain,
    ( v1_funct_2(sK3,k1_xboole_0,sK2)
    | ~ spl6_32 ),
    inference(backward_demodulation,[],[f54,f691])).

fof(f54,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f890,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl6_2
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_12
    | ~ spl6_28
    | ~ spl6_32 ),
    inference(backward_demodulation,[],[f852,f878])).

fof(f878,plain,
    ( k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | ~ spl6_7
    | ~ spl6_32 ),
    inference(resolution,[],[f836,f60])).

fof(f836,plain,
    ( v1_xboole_0(k2_funct_1(k1_xboole_0))
    | ~ spl6_7
    | ~ spl6_32 ),
    inference(backward_demodulation,[],[f143,f830])).

fof(f143,plain,
    ( v1_xboole_0(k2_funct_1(sK3))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl6_7
  <=> v1_xboole_0(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f852,plain,
    ( ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | spl6_2
    | ~ spl6_6
    | ~ spl6_12
    | ~ spl6_28
    | ~ spl6_32 ),
    inference(backward_demodulation,[],[f799,f830])).

fof(f799,plain,
    ( ~ v1_funct_2(k2_funct_1(sK3),k1_xboole_0,k1_xboole_0)
    | spl6_2
    | ~ spl6_6
    | ~ spl6_12
    | ~ spl6_28
    | ~ spl6_32 ),
    inference(backward_demodulation,[],[f702,f784])).

fof(f702,plain,
    ( ~ v1_funct_2(k2_funct_1(sK3),sK2,k1_xboole_0)
    | spl6_2
    | ~ spl6_32 ),
    inference(backward_demodulation,[],[f98,f691])).

fof(f98,plain,
    ( ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl6_2
  <=> v1_funct_2(k2_funct_1(sK3),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f876,plain,
    ( ~ spl6_32
    | spl6_34 ),
    inference(avatar_contradiction_clause,[],[f874])).

fof(f874,plain,
    ( $false
    | ~ spl6_32
    | spl6_34 ),
    inference(resolution,[],[f844,f105])).

fof(f844,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl6_32
    | spl6_34 ),
    inference(backward_demodulation,[],[f758,f830])).

fof(f758,plain,
    ( ~ v1_xboole_0(sK3)
    | spl6_34 ),
    inference(avatar_component_clause,[],[f757])).

fof(f757,plain,
    ( spl6_34
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f767,plain,
    ( ~ spl6_34
    | spl6_28
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f198,f185,f567,f757])).

fof(f198,plain,
    ( k1_xboole_0 = sK2
    | ~ v1_xboole_0(sK3)
    | ~ spl6_12 ),
    inference(superposition,[],[f187,f107])).

fof(f107,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f61,f60])).

fof(f61,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc11_relat_1)).

fof(f747,plain,
    ( spl6_9
    | ~ spl6_32 ),
    inference(avatar_contradiction_clause,[],[f745])).

fof(f745,plain,
    ( $false
    | spl6_9
    | ~ spl6_32 ),
    inference(resolution,[],[f704,f105])).

fof(f704,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl6_9
    | ~ spl6_32 ),
    inference(backward_demodulation,[],[f161,f691])).

fof(f161,plain,
    ( ~ v1_xboole_0(sK1)
    | spl6_9 ),
    inference(resolution,[],[f160,f55])).

fof(f160,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_xboole_0(X0) )
    | spl6_9 ),
    inference(resolution,[],[f157,f68])).

fof(f157,plain,
    ( ~ v1_xboole_0(sK3)
    | spl6_9 ),
    inference(resolution,[],[f151,f61])).

fof(f151,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK3))
    | spl6_9 ),
    inference(avatar_component_clause,[],[f149])).

fof(f149,plain,
    ( spl6_9
  <=> v1_xboole_0(k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f698,plain,
    ( ~ spl6_3
    | ~ spl6_6
    | ~ spl6_12
    | spl6_31 ),
    inference(avatar_contradiction_clause,[],[f696])).

fof(f696,plain,
    ( $false
    | ~ spl6_3
    | ~ spl6_6
    | ~ spl6_12
    | spl6_31 ),
    inference(resolution,[],[f695,f101])).

fof(f101,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl6_3
  <=> m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f695,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl6_6
    | ~ spl6_12
    | spl6_31 ),
    inference(trivial_inequality_removal,[],[f694])).

fof(f694,plain,
    ( sK2 != sK2
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl6_6
    | ~ spl6_12
    | spl6_31 ),
    inference(forward_demodulation,[],[f693,f196])).

fof(f693,plain,
    ( sK2 != k1_relat_1(k2_funct_1(sK3))
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl6_31 ),
    inference(superposition,[],[f687,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f687,plain,
    ( sK2 != k1_relset_1(sK2,sK1,k2_funct_1(sK3))
    | spl6_31 ),
    inference(avatar_component_clause,[],[f685])).

fof(f685,plain,
    ( spl6_31
  <=> sK2 = k1_relset_1(sK2,sK1,k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f692,plain,
    ( ~ spl6_3
    | ~ spl6_31
    | spl6_32
    | spl6_2 ),
    inference(avatar_split_clause,[],[f681,f96,f689,f685,f100])).

fof(f681,plain,
    ( k1_xboole_0 = sK1
    | sK2 != k1_relset_1(sK2,sK1,k2_funct_1(sK3))
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl6_2 ),
    inference(resolution,[],[f485,f98])).

fof(f485,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(resolution,[],[f81,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f38,f39])).

fof(f39,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | k1_relset_1(X0,X2,X1) != X0
      | k1_xboole_0 = X2
      | v1_funct_2(X1,X0,X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X2 )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f50])).

fof(f50,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f550,plain,
    ( spl6_3
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_12 ),
    inference(avatar_contradiction_clause,[],[f547])).

fof(f547,plain,
    ( $false
    | spl6_3
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_12 ),
    inference(resolution,[],[f544,f55])).

fof(f544,plain,
    ( ! [X0] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
    | spl6_3
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_12 ),
    inference(resolution,[],[f542,f221])).

fof(f221,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relat_1(X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(duplicate_literal_removal,[],[f220])).

fof(f220,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relat_1(X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f78,f77])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(f542,plain,
    ( ~ m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK1))
    | spl6_3
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_12 ),
    inference(resolution,[],[f527,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f527,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),sK1)
    | spl6_3
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_12 ),
    inference(resolution,[],[f526,f102])).

fof(f102,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl6_3 ),
    inference(avatar_component_clause,[],[f100])).

% (3866)Refutation not found, incomplete strategy% (3866)------------------------------
% (3866)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (3866)Termination reason: Refutation not found, incomplete strategy

% (3866)Memory used [KB]: 10746
% (3866)Time elapsed: 0.137 s
% (3866)------------------------------
% (3866)------------------------------
fof(f526,plain,
    ( ! [X2] :
        ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X2)))
        | ~ r1_tarski(k1_relat_1(sK3),X2) )
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_12 ),
    inference(resolution,[],[f372,f125])).

fof(f372,plain,
    ( ! [X4,X3] :
        ( ~ r1_tarski(sK2,X4)
        | ~ r1_tarski(k1_relat_1(sK3),X3)
        | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X4,X3))) )
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_12 ),
    inference(forward_demodulation,[],[f371,f196])).

fof(f371,plain,
    ( ! [X4,X3] :
        ( ~ r1_tarski(k1_relat_1(sK3),X3)
        | ~ r1_tarski(k1_relat_1(k2_funct_1(sK3)),X4)
        | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X4,X3))) )
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(forward_demodulation,[],[f368,f167])).

fof(f167,plain,
    ( k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f165])).

fof(f165,plain,
    ( spl6_10
  <=> k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f368,plain,
    ( ! [X4,X3] :
        ( ~ r1_tarski(k2_relat_1(k2_funct_1(sK3)),X3)
        | ~ r1_tarski(k1_relat_1(k2_funct_1(sK3)),X4)
        | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X4,X3))) )
    | ~ spl6_8 ),
    inference(resolution,[],[f74,f146])).

fof(f146,plain,
    ( v1_relat_1(k2_funct_1(sK3))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl6_8
  <=> v1_relat_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

% (3875)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
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

fof(f193,plain,(
    spl6_11 ),
    inference(avatar_contradiction_clause,[],[f191])).

fof(f191,plain,
    ( $false
    | spl6_11 ),
    inference(resolution,[],[f183,f55])).

fof(f183,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | spl6_11 ),
    inference(avatar_component_clause,[],[f181])).

fof(f181,plain,
    ( spl6_11
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f189,plain,
    ( ~ spl6_11
    | spl6_12 ),
    inference(avatar_split_clause,[],[f179,f185,f181])).

fof(f179,plain,
    ( sK2 = k2_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(superposition,[],[f57,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f57,plain,(
    sK2 = k2_relset_1(sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f42])).

% (3881)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
fof(f168,plain,
    ( ~ spl6_4
    | ~ spl6_5
    | spl6_10 ),
    inference(avatar_split_clause,[],[f163,f165,f116,f112])).

fof(f112,plain,
    ( spl6_4
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f116,plain,
    ( spl6_5
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f163,plain,
    ( k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f66,f56])).

fof(f56,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f66,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f156,plain,
    ( ~ spl6_4
    | ~ spl6_5
    | spl6_8 ),
    inference(avatar_split_clause,[],[f154,f145,f116,f112])).

fof(f154,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | spl6_8 ),
    inference(resolution,[],[f147,f63])).

fof(f63,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f147,plain,
    ( ~ v1_relat_1(k2_funct_1(sK3))
    | spl6_8 ),
    inference(avatar_component_clause,[],[f145])).

fof(f152,plain,
    ( spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f139,f135,f149,f145,f141])).

fof(f139,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | v1_xboole_0(k2_funct_1(sK3))
    | ~ spl6_6 ),
    inference(superposition,[],[f62,f137])).

fof(f62,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_relat_1)).

fof(f138,plain,
    ( ~ spl6_4
    | ~ spl6_5
    | spl6_6 ),
    inference(avatar_split_clause,[],[f133,f135,f116,f112])).

fof(f133,plain,
    ( k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f65,f56])).

fof(f65,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f129,plain,(
    spl6_4 ),
    inference(avatar_contradiction_clause,[],[f127])).

fof(f127,plain,
    ( $false
    | spl6_4 ),
    inference(resolution,[],[f126,f55])).

fof(f126,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl6_4 ),
    inference(resolution,[],[f75,f114])).

fof(f114,plain,
    ( ~ v1_relat_1(sK3)
    | spl6_4 ),
    inference(avatar_component_clause,[],[f112])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f121,plain,(
    spl6_5 ),
    inference(avatar_contradiction_clause,[],[f120])).

fof(f120,plain,
    ( $false
    | spl6_5 ),
    inference(resolution,[],[f118,f53])).

fof(f53,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f118,plain,
    ( ~ v1_funct_1(sK3)
    | spl6_5 ),
    inference(avatar_component_clause,[],[f116])).

fof(f119,plain,
    ( ~ spl6_4
    | ~ spl6_5
    | spl6_1 ),
    inference(avatar_split_clause,[],[f110,f92,f116,f112])).

fof(f92,plain,
    ( spl6_1
  <=> v1_funct_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f110,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | spl6_1 ),
    inference(resolution,[],[f64,f94])).

fof(f94,plain,
    ( ~ v1_funct_1(k2_funct_1(sK3))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f92])).

fof(f64,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f103,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f58,f100,f96,f92])).

fof(f58,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(cnf_transformation,[],[f42])).

%------------------------------------------------------------------------------
