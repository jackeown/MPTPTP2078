%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:08 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  163 ( 725 expanded)
%              Number of leaves         :   23 ( 211 expanded)
%              Depth                    :   23
%              Number of atoms          :  684 (4457 expanded)
%              Number of equality atoms :  134 ( 716 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (9631)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f567,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f112,f210,f374,f426,f475,f566])).

fof(f566,plain,
    ( ~ spl10_1
    | spl10_2
    | spl10_21
    | ~ spl10_22 ),
    inference(avatar_contradiction_clause,[],[f565])).

fof(f565,plain,
    ( $false
    | ~ spl10_1
    | spl10_2
    | spl10_21
    | ~ spl10_22 ),
    inference(subsumption_resolution,[],[f564,f212])).

fof(f212,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl10_1 ),
    inference(backward_demodulation,[],[f96,f107])).

fof(f107,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl10_1
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f96,plain,(
    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(resolution,[],[f48,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f48,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f28])).

% (9653)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
fof(f28,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK3)
    & ! [X4] :
        ( k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4)
        | ~ r2_hidden(X4,sK0) )
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f27,f26])).

fof(f26,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r2_relset_1(X0,X1,X2,X3)
            & ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ r2_hidden(X4,X0) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ~ r2_relset_1(sK0,sK1,sK2,X3)
          & ! [X4] :
              ( k1_funct_1(X3,X4) = k1_funct_1(sK2,X4)
              | ~ r2_hidden(X4,sK0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
          & v1_funct_2(X3,sK0,sK1)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X3] :
        ( ~ r2_relset_1(sK0,sK1,sK2,X3)
        & ! [X4] :
            ( k1_funct_1(X3,X4) = k1_funct_1(sK2,X4)
            | ~ r2_hidden(X4,sK0) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        & v1_funct_2(X3,sK0,sK1)
        & v1_funct_1(X3) )
   => ( ~ r2_relset_1(sK0,sK1,sK2,sK3)
      & ! [X4] :
          ( k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4)
          | ~ r2_hidden(X4,sK0) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ r2_hidden(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ r2_hidden(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
           => ( ! [X4] :
                  ( r2_hidden(X4,X0)
                 => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
             => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( ! [X4] :
                ( r2_hidden(X4,X0)
               => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
           => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_2)).

fof(f564,plain,
    ( sK0 != k1_relat_1(sK2)
    | spl10_2
    | spl10_21
    | ~ spl10_22 ),
    inference(forward_demodulation,[],[f563,f239])).

fof(f239,plain,
    ( sK0 = k1_relat_1(sK3)
    | spl10_2 ),
    inference(backward_demodulation,[],[f230,f238])).

fof(f238,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | spl10_2 ),
    inference(subsumption_resolution,[],[f237,f110])).

fof(f110,plain,
    ( k1_xboole_0 != sK1
    | spl10_2 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl10_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f237,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(subsumption_resolution,[],[f231,f50])).

fof(f50,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f231,plain,
    ( ~ v1_funct_2(sK3,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(resolution,[],[f51,f70])).

% (9645)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f24])).

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
    inference(ennf_transformation,[],[f11])).

% (9657)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
fof(f11,axiom,(
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

fof(f51,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f28])).

fof(f230,plain,(
    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f51,f69])).

fof(f563,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK3)
    | spl10_21
    | ~ spl10_22 ),
    inference(subsumption_resolution,[],[f562,f229])).

fof(f229,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f51,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f562,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | spl10_21
    | ~ spl10_22 ),
    inference(subsumption_resolution,[],[f561,f49])).

fof(f49,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f561,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | spl10_21
    | ~ spl10_22 ),
    inference(subsumption_resolution,[],[f560,f95])).

fof(f95,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f48,f68])).

fof(f560,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | spl10_21
    | ~ spl10_22 ),
    inference(subsumption_resolution,[],[f559,f46])).

fof(f46,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f559,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | spl10_21
    | ~ spl10_22 ),
    inference(subsumption_resolution,[],[f558,f420])).

fof(f420,plain,
    ( sK2 != sK3
    | spl10_21 ),
    inference(avatar_component_clause,[],[f419])).

fof(f419,plain,
    ( spl10_21
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_21])])).

fof(f558,plain,
    ( sK2 = sK3
    | k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl10_22 ),
    inference(trivial_inequality_removal,[],[f557])).

fof(f557,plain,
    ( k1_funct_1(sK2,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2))
    | sK2 = sK3
    | k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl10_22 ),
    inference(superposition,[],[f56,f526])).

fof(f526,plain,
    ( k1_funct_1(sK2,sK4(sK3,sK2)) = k1_funct_1(sK3,sK4(sK3,sK2))
    | ~ spl10_22 ),
    inference(resolution,[],[f425,f52])).

fof(f52,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK0)
      | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f425,plain,
    ( r2_hidden(sK4(sK3,sK2),sK0)
    | ~ spl10_22 ),
    inference(avatar_component_clause,[],[f423])).

fof(f423,plain,
    ( spl10_22
  <=> r2_hidden(sK4(sK3,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
      | X0 = X1
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ( k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
            & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f17,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
        & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

% (9656)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( ! [X2] :
                  ( r2_hidden(X2,k1_relat_1(X0))
                 => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) )
              & k1_relat_1(X0) = k1_relat_1(X1) )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).

fof(f475,plain,
    ( ~ spl10_3
    | ~ spl10_21 ),
    inference(avatar_contradiction_clause,[],[f474])).

fof(f474,plain,
    ( $false
    | ~ spl10_3
    | ~ spl10_21 ),
    inference(subsumption_resolution,[],[f430,f271])).

fof(f271,plain,
    ( r2_relset_1(sK0,sK1,sK2,sK2)
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f270])).

fof(f270,plain,
    ( spl10_3
  <=> r2_relset_1(sK0,sK1,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f430,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK2)
    | ~ spl10_21 ),
    inference(backward_demodulation,[],[f53,f421])).

fof(f421,plain,
    ( sK2 = sK3
    | ~ spl10_21 ),
    inference(avatar_component_clause,[],[f419])).

% (9655)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
fof(f53,plain,(
    ~ r2_relset_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f426,plain,
    ( spl10_21
    | spl10_22
    | ~ spl10_1
    | spl10_2 ),
    inference(avatar_split_clause,[],[f417,f109,f105,f423,f419])).

fof(f417,plain,
    ( r2_hidden(sK4(sK3,sK2),sK0)
    | sK2 = sK3
    | ~ spl10_1
    | spl10_2 ),
    inference(subsumption_resolution,[],[f416,f229])).

fof(f416,plain,
    ( r2_hidden(sK4(sK3,sK2),sK0)
    | sK2 = sK3
    | ~ v1_relat_1(sK3)
    | ~ spl10_1
    | spl10_2 ),
    inference(subsumption_resolution,[],[f415,f49])).

fof(f415,plain,
    ( r2_hidden(sK4(sK3,sK2),sK0)
    | sK2 = sK3
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl10_1
    | spl10_2 ),
    inference(trivial_inequality_removal,[],[f414])).

fof(f414,plain,
    ( sK0 != sK0
    | r2_hidden(sK4(sK3,sK2),sK0)
    | sK2 = sK3
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl10_1
    | spl10_2 ),
    inference(superposition,[],[f217,f239])).

fof(f217,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) != sK0
        | r2_hidden(sK4(X0,sK2),sK0)
        | sK2 = X0
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl10_1 ),
    inference(inner_rewriting,[],[f216])).

fof(f216,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) != sK0
        | r2_hidden(sK4(X0,sK2),k1_relat_1(X0))
        | sK2 = X0
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f215,f95])).

fof(f215,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) != sK0
        | r2_hidden(sK4(X0,sK2),k1_relat_1(X0))
        | sK2 = X0
        | ~ v1_relat_1(sK2)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f213,f46])).

fof(f213,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) != sK0
        | r2_hidden(sK4(X0,sK2),k1_relat_1(X0))
        | sK2 = X0
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl10_1 ),
    inference(superposition,[],[f55,f212])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) != k1_relat_1(X1)
      | r2_hidden(sK4(X0,X1),k1_relat_1(X0))
      | X0 = X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f374,plain,(
    spl10_3 ),
    inference(avatar_contradiction_clause,[],[f373])).

fof(f373,plain,
    ( $false
    | spl10_3 ),
    inference(subsumption_resolution,[],[f372,f48])).

fof(f372,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl10_3 ),
    inference(subsumption_resolution,[],[f371,f326])).

fof(f326,plain,
    ( r2_hidden(k4_tarski(sK6(sK0,sK1,sK2,sK2),sK7(sK0,sK1,sK2,sK2)),sK2)
    | spl10_3 ),
    inference(subsumption_resolution,[],[f325,f272])).

fof(f272,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK2)
    | spl10_3 ),
    inference(avatar_component_clause,[],[f270])).

fof(f325,plain,
    ( r2_hidden(k4_tarski(sK6(sK0,sK1,sK2,sK2),sK7(sK0,sK1,sK2,sK2)),sK2)
    | r2_relset_1(sK0,sK1,sK2,sK2) ),
    inference(duplicate_literal_removal,[],[f321])).

fof(f321,plain,
    ( r2_hidden(k4_tarski(sK6(sK0,sK1,sK2,sK2),sK7(sK0,sK1,sK2,sK2)),sK2)
    | r2_relset_1(sK0,sK1,sK2,sK2)
    | r2_hidden(k4_tarski(sK6(sK0,sK1,sK2,sK2),sK7(sK0,sK1,sK2,sK2)),sK2) ),
    inference(resolution,[],[f99,f48])).

fof(f99,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | r2_hidden(k4_tarski(sK6(sK0,sK1,X0,sK2),sK7(sK0,sK1,X0,sK2)),X0)
      | r2_relset_1(sK0,sK1,X0,sK2)
      | r2_hidden(k4_tarski(sK6(sK0,sK1,X0,sK2),sK7(sK0,sK1,X0,sK2)),sK2) ) ),
    inference(resolution,[],[f48,f80])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_hidden(k4_tarski(sK6(X0,X1,X2,X3),sK7(X0,X1,X2,X3)),X3)
      | r2_hidden(k4_tarski(sK6(X0,X1,X2,X3),sK7(X0,X1,X2,X3)),X2)
      | r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( r2_relset_1(X0,X1,X2,X3)
              | ( ( ~ r2_hidden(k4_tarski(sK6(X0,X1,X2,X3),sK7(X0,X1,X2,X3)),X3)
                  | ~ r2_hidden(k4_tarski(sK6(X0,X1,X2,X3),sK7(X0,X1,X2,X3)),X2) )
                & ( r2_hidden(k4_tarski(sK6(X0,X1,X2,X3),sK7(X0,X1,X2,X3)),X3)
                  | r2_hidden(k4_tarski(sK6(X0,X1,X2,X3),sK7(X0,X1,X2,X3)),X2) )
                & m1_subset_1(sK7(X0,X1,X2,X3),X1)
                & m1_subset_1(sK6(X0,X1,X2,X3),X0) ) )
            & ( ! [X6] :
                  ( ! [X7] :
                      ( ( ( r2_hidden(k4_tarski(X6,X7),X2)
                          | ~ r2_hidden(k4_tarski(X6,X7),X3) )
                        & ( r2_hidden(k4_tarski(X6,X7),X3)
                          | ~ r2_hidden(k4_tarski(X6,X7),X2) ) )
                      | ~ m1_subset_1(X7,X1) )
                  | ~ m1_subset_1(X6,X0) )
              | ~ r2_relset_1(X0,X1,X2,X3) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f42,f44,f43])).

fof(f43,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ? [X5] :
              ( ( ~ r2_hidden(k4_tarski(X4,X5),X3)
                | ~ r2_hidden(k4_tarski(X4,X5),X2) )
              & ( r2_hidden(k4_tarski(X4,X5),X3)
                | r2_hidden(k4_tarski(X4,X5),X2) )
              & m1_subset_1(X5,X1) )
          & m1_subset_1(X4,X0) )
     => ( ? [X5] :
            ( ( ~ r2_hidden(k4_tarski(sK6(X0,X1,X2,X3),X5),X3)
              | ~ r2_hidden(k4_tarski(sK6(X0,X1,X2,X3),X5),X2) )
            & ( r2_hidden(k4_tarski(sK6(X0,X1,X2,X3),X5),X3)
              | r2_hidden(k4_tarski(sK6(X0,X1,X2,X3),X5),X2) )
            & m1_subset_1(X5,X1) )
        & m1_subset_1(sK6(X0,X1,X2,X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( ( ~ r2_hidden(k4_tarski(sK6(X0,X1,X2,X3),X5),X3)
            | ~ r2_hidden(k4_tarski(sK6(X0,X1,X2,X3),X5),X2) )
          & ( r2_hidden(k4_tarski(sK6(X0,X1,X2,X3),X5),X3)
            | r2_hidden(k4_tarski(sK6(X0,X1,X2,X3),X5),X2) )
          & m1_subset_1(X5,X1) )
     => ( ( ~ r2_hidden(k4_tarski(sK6(X0,X1,X2,X3),sK7(X0,X1,X2,X3)),X3)
          | ~ r2_hidden(k4_tarski(sK6(X0,X1,X2,X3),sK7(X0,X1,X2,X3)),X2) )
        & ( r2_hidden(k4_tarski(sK6(X0,X1,X2,X3),sK7(X0,X1,X2,X3)),X3)
          | r2_hidden(k4_tarski(sK6(X0,X1,X2,X3),sK7(X0,X1,X2,X3)),X2) )
        & m1_subset_1(sK7(X0,X1,X2,X3),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( r2_relset_1(X0,X1,X2,X3)
              | ? [X4] :
                  ( ? [X5] :
                      ( ( ~ r2_hidden(k4_tarski(X4,X5),X3)
                        | ~ r2_hidden(k4_tarski(X4,X5),X2) )
                      & ( r2_hidden(k4_tarski(X4,X5),X3)
                        | r2_hidden(k4_tarski(X4,X5),X2) )
                      & m1_subset_1(X5,X1) )
                  & m1_subset_1(X4,X0) ) )
            & ( ! [X6] :
                  ( ! [X7] :
                      ( ( ( r2_hidden(k4_tarski(X6,X7),X2)
                          | ~ r2_hidden(k4_tarski(X6,X7),X3) )
                        & ( r2_hidden(k4_tarski(X6,X7),X3)
                          | ~ r2_hidden(k4_tarski(X6,X7),X2) ) )
                      | ~ m1_subset_1(X7,X1) )
                  | ~ m1_subset_1(X6,X0) )
              | ~ r2_relset_1(X0,X1,X2,X3) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( r2_relset_1(X0,X1,X2,X3)
              | ? [X4] :
                  ( ? [X5] :
                      ( ( ~ r2_hidden(k4_tarski(X4,X5),X3)
                        | ~ r2_hidden(k4_tarski(X4,X5),X2) )
                      & ( r2_hidden(k4_tarski(X4,X5),X3)
                        | r2_hidden(k4_tarski(X4,X5),X2) )
                      & m1_subset_1(X5,X1) )
                  & m1_subset_1(X4,X0) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( ( ( r2_hidden(k4_tarski(X4,X5),X2)
                          | ~ r2_hidden(k4_tarski(X4,X5),X3) )
                        & ( r2_hidden(k4_tarski(X4,X5),X3)
                          | ~ r2_hidden(k4_tarski(X4,X5),X2) ) )
                      | ~ m1_subset_1(X5,X1) )
                  | ~ m1_subset_1(X4,X0) )
              | ~ r2_relset_1(X0,X1,X2,X3) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( r2_relset_1(X0,X1,X2,X3)
              | ? [X4] :
                  ( ? [X5] :
                      ( ( ~ r2_hidden(k4_tarski(X4,X5),X3)
                        | ~ r2_hidden(k4_tarski(X4,X5),X2) )
                      & ( r2_hidden(k4_tarski(X4,X5),X3)
                        | r2_hidden(k4_tarski(X4,X5),X2) )
                      & m1_subset_1(X5,X1) )
                  & m1_subset_1(X4,X0) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( ( ( r2_hidden(k4_tarski(X4,X5),X2)
                          | ~ r2_hidden(k4_tarski(X4,X5),X3) )
                        & ( r2_hidden(k4_tarski(X4,X5),X3)
                          | ~ r2_hidden(k4_tarski(X4,X5),X2) ) )
                      | ~ m1_subset_1(X5,X1) )
                  | ~ m1_subset_1(X4,X0) )
              | ~ r2_relset_1(X0,X1,X2,X3) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( r2_relset_1(X0,X1,X2,X3)
          <=> ! [X4] :
                ( ! [X5] :
                    ( ( r2_hidden(k4_tarski(X4,X5),X2)
                    <=> r2_hidden(k4_tarski(X4,X5),X3) )
                    | ~ m1_subset_1(X5,X1) )
                | ~ m1_subset_1(X4,X0) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( r2_relset_1(X0,X1,X2,X3)
          <=> ! [X4] :
                ( m1_subset_1(X4,X0)
               => ! [X5] :
                    ( m1_subset_1(X5,X1)
                   => ( r2_hidden(k4_tarski(X4,X5),X2)
                    <=> r2_hidden(k4_tarski(X4,X5),X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relset_1)).

fof(f371,plain,
    ( ~ r2_hidden(k4_tarski(sK6(sK0,sK1,sK2,sK2),sK7(sK0,sK1,sK2,sK2)),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl10_3 ),
    inference(subsumption_resolution,[],[f370,f272])).

fof(f370,plain,
    ( r2_relset_1(sK0,sK1,sK2,sK2)
    | ~ r2_hidden(k4_tarski(sK6(sK0,sK1,sK2,sK2),sK7(sK0,sK1,sK2,sK2)),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl10_3 ),
    inference(duplicate_literal_removal,[],[f367])).

fof(f367,plain,
    ( r2_relset_1(sK0,sK1,sK2,sK2)
    | ~ r2_hidden(k4_tarski(sK6(sK0,sK1,sK2,sK2),sK7(sK0,sK1,sK2,sK2)),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl10_3 ),
    inference(resolution,[],[f326,f81])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(sK6(X0,X1,X2,X3),sK7(X0,X1,X2,X3)),X3)
      | r2_relset_1(X0,X1,X2,X3)
      | ~ r2_hidden(k4_tarski(sK6(X0,X1,X2,X3),sK7(X0,X1,X2,X3)),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f210,plain,(
    ~ spl10_2 ),
    inference(avatar_contradiction_clause,[],[f209])).

fof(f209,plain,
    ( $false
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f201,f54])).

fof(f54,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f201,plain,
    ( ~ r1_tarski(k1_xboole_0,k4_tarski(sK6(sK0,k1_xboole_0,k1_xboole_0,k1_xboole_0),sK7(sK0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))
    | ~ spl10_2 ),
    inference(resolution,[],[f197,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f197,plain,
    ( r2_hidden(k4_tarski(sK6(sK0,k1_xboole_0,k1_xboole_0,k1_xboole_0),sK7(sK0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f194,f190])).

fof(f190,plain,
    ( ~ r2_relset_1(sK0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl10_2 ),
    inference(backward_demodulation,[],[f155,f184])).

fof(f184,plain,
    ( k1_xboole_0 = sK3
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f183,f54])).

fof(f183,plain,
    ( k1_xboole_0 = sK3
    | ~ r1_tarski(k1_xboole_0,sK3)
    | ~ spl10_2 ),
    inference(resolution,[],[f181,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f181,plain,
    ( r1_tarski(sK3,k1_xboole_0)
    | ~ spl10_2 ),
    inference(duplicate_literal_removal,[],[f178])).

fof(f178,plain,
    ( r1_tarski(sK3,k1_xboole_0)
    | r1_tarski(sK3,k1_xboole_0)
    | ~ spl10_2 ),
    inference(resolution,[],[f141,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f34,f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f141,plain,
    ( ! [X0] :
        ( r2_hidden(sK5(sK3,X0),k1_xboole_0)
        | r1_tarski(sK3,X0) )
    | ~ spl10_2 ),
    inference(resolution,[],[f138,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

% (9654)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
fof(f138,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK3)
        | r2_hidden(X0,k1_xboole_0) )
    | ~ spl10_2 ),
    inference(resolution,[],[f124,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f124,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl10_2 ),
    inference(forward_demodulation,[],[f116,f84])).

fof(f84,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f116,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl10_2 ),
    inference(backward_demodulation,[],[f51,f111])).

fof(f111,plain,
    ( k1_xboole_0 = sK1
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f109])).

fof(f155,plain,
    ( ~ r2_relset_1(sK0,k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl10_2 ),
    inference(backward_demodulation,[],[f117,f150])).

fof(f150,plain,
    ( k1_xboole_0 = sK2
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f149,f54])).

fof(f149,plain,
    ( k1_xboole_0 = sK2
    | ~ r1_tarski(k1_xboole_0,sK2)
    | ~ spl10_2 ),
    inference(resolution,[],[f147,f60])).

fof(f147,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl10_2 ),
    inference(duplicate_literal_removal,[],[f144])).

fof(f144,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | r1_tarski(sK2,k1_xboole_0)
    | ~ spl10_2 ),
    inference(resolution,[],[f140,f63])).

fof(f140,plain,
    ( ! [X0] :
        ( r2_hidden(sK5(sK2,X0),k1_xboole_0)
        | r1_tarski(sK2,X0) )
    | ~ spl10_2 ),
    inference(resolution,[],[f135,f62])).

fof(f135,plain,
    ( ! [X5] :
        ( ~ r2_hidden(X5,sK2)
        | r2_hidden(X5,k1_xboole_0) )
    | ~ spl10_2 ),
    inference(forward_demodulation,[],[f122,f84])).

fof(f122,plain,
    ( ! [X5] :
        ( r2_hidden(X5,k2_zfmisc_1(sK0,k1_xboole_0))
        | ~ r2_hidden(X5,sK2) )
    | ~ spl10_2 ),
    inference(backward_demodulation,[],[f102,f111])).

fof(f102,plain,(
    ! [X5] :
      ( r2_hidden(X5,k2_zfmisc_1(sK0,sK1))
      | ~ r2_hidden(X5,sK2) ) ),
    inference(resolution,[],[f48,f57])).

fof(f117,plain,
    ( ~ r2_relset_1(sK0,k1_xboole_0,sK2,sK3)
    | ~ spl10_2 ),
    inference(backward_demodulation,[],[f53,f111])).

fof(f194,plain,
    ( r2_hidden(k4_tarski(sK6(sK0,k1_xboole_0,k1_xboole_0,k1_xboole_0),sK7(sK0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | r2_relset_1(sK0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl10_2 ),
    inference(resolution,[],[f171,f157])).

fof(f157,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl10_2 ),
    inference(backward_demodulation,[],[f123,f150])).

fof(f123,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl10_2 ),
    inference(forward_demodulation,[],[f114,f84])).

fof(f114,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl10_2 ),
    inference(backward_demodulation,[],[f48,f111])).

fof(f171,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | r2_hidden(k4_tarski(sK6(sK0,k1_xboole_0,X0,k1_xboole_0),sK7(sK0,k1_xboole_0,X0,k1_xboole_0)),k1_xboole_0)
        | r2_relset_1(sK0,k1_xboole_0,X0,k1_xboole_0) )
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f170,f57])).

fof(f170,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(sK6(sK0,k1_xboole_0,X0,k1_xboole_0),sK7(sK0,k1_xboole_0,X0,k1_xboole_0)),X0)
        | r2_relset_1(sK0,k1_xboole_0,X0,k1_xboole_0)
        | r2_hidden(k4_tarski(sK6(sK0,k1_xboole_0,X0,k1_xboole_0),sK7(sK0,k1_xboole_0,X0,k1_xboole_0)),k1_xboole_0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl10_2 ),
    inference(forward_demodulation,[],[f169,f150])).

fof(f169,plain,
    ( ! [X0] :
        ( r2_relset_1(sK0,k1_xboole_0,X0,k1_xboole_0)
        | r2_hidden(k4_tarski(sK6(sK0,k1_xboole_0,X0,k1_xboole_0),sK7(sK0,k1_xboole_0,X0,k1_xboole_0)),k1_xboole_0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | r2_hidden(k4_tarski(sK6(sK0,k1_xboole_0,X0,sK2),sK7(sK0,k1_xboole_0,X0,sK2)),X0) )
    | ~ spl10_2 ),
    inference(forward_demodulation,[],[f158,f150])).

fof(f158,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(sK6(sK0,k1_xboole_0,X0,k1_xboole_0),sK7(sK0,k1_xboole_0,X0,k1_xboole_0)),k1_xboole_0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | r2_relset_1(sK0,k1_xboole_0,X0,sK2)
        | r2_hidden(k4_tarski(sK6(sK0,k1_xboole_0,X0,sK2),sK7(sK0,k1_xboole_0,X0,sK2)),X0) )
    | ~ spl10_2 ),
    inference(backward_demodulation,[],[f128,f150])).

fof(f128,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | r2_relset_1(sK0,k1_xboole_0,X0,sK2)
        | r2_hidden(k4_tarski(sK6(sK0,k1_xboole_0,X0,sK2),sK7(sK0,k1_xboole_0,X0,sK2)),X0)
        | r2_hidden(k4_tarski(sK6(sK0,k1_xboole_0,X0,sK2),sK7(sK0,k1_xboole_0,X0,sK2)),sK2) )
    | ~ spl10_2 ),
    inference(forward_demodulation,[],[f127,f84])).

fof(f127,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
        | r2_relset_1(sK0,k1_xboole_0,X0,sK2)
        | r2_hidden(k4_tarski(sK6(sK0,k1_xboole_0,X0,sK2),sK7(sK0,k1_xboole_0,X0,sK2)),X0)
        | r2_hidden(k4_tarski(sK6(sK0,k1_xboole_0,X0,sK2),sK7(sK0,k1_xboole_0,X0,sK2)),sK2) )
    | ~ spl10_2 ),
    inference(forward_demodulation,[],[f126,f111])).

fof(f126,plain,
    ( ! [X0] :
        ( r2_relset_1(sK0,k1_xboole_0,X0,sK2)
        | r2_hidden(k4_tarski(sK6(sK0,k1_xboole_0,X0,sK2),sK7(sK0,k1_xboole_0,X0,sK2)),X0)
        | r2_hidden(k4_tarski(sK6(sK0,k1_xboole_0,X0,sK2),sK7(sK0,k1_xboole_0,X0,sK2)),sK2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) )
    | ~ spl10_2 ),
    inference(forward_demodulation,[],[f125,f111])).

fof(f125,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(sK6(sK0,k1_xboole_0,X0,sK2),sK7(sK0,k1_xboole_0,X0,sK2)),X0)
        | r2_hidden(k4_tarski(sK6(sK0,k1_xboole_0,X0,sK2),sK7(sK0,k1_xboole_0,X0,sK2)),sK2)
        | r2_relset_1(sK0,sK1,X0,sK2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) )
    | ~ spl10_2 ),
    inference(forward_demodulation,[],[f119,f111])).

fof(f119,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(sK6(sK0,k1_xboole_0,X0,sK2),sK7(sK0,k1_xboole_0,X0,sK2)),sK2)
        | r2_hidden(k4_tarski(sK6(sK0,sK1,X0,sK2),sK7(sK0,sK1,X0,sK2)),X0)
        | r2_relset_1(sK0,sK1,X0,sK2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) )
    | ~ spl10_2 ),
    inference(backward_demodulation,[],[f99,f111])).

fof(f112,plain,
    ( spl10_1
    | spl10_2 ),
    inference(avatar_split_clause,[],[f103,f109,f105])).

fof(f103,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f97,f47])).

fof(f47,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f97,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f48,f70])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 15:51:36 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.23/0.51  % (9628)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.23/0.52  % (9636)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.23/0.53  % (9634)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.23/0.53  % (9651)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.23/0.54  % (9643)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.23/0.54  % (9652)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.23/0.54  % (9629)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.23/0.54  % (9636)Refutation found. Thanks to Tanya!
% 0.23/0.54  % SZS status Theorem for theBenchmark
% 0.23/0.54  % (9637)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.23/0.54  % (9635)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.23/0.54  % (9633)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.23/0.54  % (9632)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.23/0.54  % SZS output start Proof for theBenchmark
% 0.23/0.54  % (9631)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.23/0.54  fof(f567,plain,(
% 0.23/0.54    $false),
% 0.23/0.54    inference(avatar_sat_refutation,[],[f112,f210,f374,f426,f475,f566])).
% 0.23/0.54  fof(f566,plain,(
% 0.23/0.54    ~spl10_1 | spl10_2 | spl10_21 | ~spl10_22),
% 0.23/0.54    inference(avatar_contradiction_clause,[],[f565])).
% 0.23/0.54  fof(f565,plain,(
% 0.23/0.54    $false | (~spl10_1 | spl10_2 | spl10_21 | ~spl10_22)),
% 0.23/0.54    inference(subsumption_resolution,[],[f564,f212])).
% 0.23/0.54  fof(f212,plain,(
% 0.23/0.54    sK0 = k1_relat_1(sK2) | ~spl10_1),
% 0.23/0.54    inference(backward_demodulation,[],[f96,f107])).
% 0.23/0.54  fof(f107,plain,(
% 0.23/0.54    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl10_1),
% 0.23/0.54    inference(avatar_component_clause,[],[f105])).
% 0.23/0.54  fof(f105,plain,(
% 0.23/0.54    spl10_1 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.23/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 0.23/0.54  fof(f96,plain,(
% 0.23/0.54    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)),
% 0.23/0.54    inference(resolution,[],[f48,f69])).
% 0.23/0.55  fof(f69,plain,(
% 0.23/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f22])).
% 0.23/0.55  fof(f22,plain,(
% 0.23/0.55    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.23/0.55    inference(ennf_transformation,[],[f10])).
% 0.23/0.55  fof(f10,axiom,(
% 0.23/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.23/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.23/0.55  fof(f48,plain,(
% 0.23/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.23/0.55    inference(cnf_transformation,[],[f28])).
% 0.23/0.55  % (9653)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.23/0.55  fof(f28,plain,(
% 0.23/0.55    (~r2_relset_1(sK0,sK1,sK2,sK3) & ! [X4] : (k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) | ~r2_hidden(X4,sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 0.23/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f27,f26])).
% 0.23/0.55  fof(f26,plain,(
% 0.23/0.55    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK0,sK1,sK2,X3) & ! [X4] : (k1_funct_1(X3,X4) = k1_funct_1(sK2,X4) | ~r2_hidden(X4,sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X3,sK0,sK1) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 0.23/0.55    introduced(choice_axiom,[])).
% 0.23/0.55  fof(f27,plain,(
% 0.23/0.55    ? [X3] : (~r2_relset_1(sK0,sK1,sK2,X3) & ! [X4] : (k1_funct_1(X3,X4) = k1_funct_1(sK2,X4) | ~r2_hidden(X4,sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X3,sK0,sK1) & v1_funct_1(X3)) => (~r2_relset_1(sK0,sK1,sK2,sK3) & ! [X4] : (k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) | ~r2_hidden(X4,sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 0.23/0.55    introduced(choice_axiom,[])).
% 0.23/0.55  fof(f15,plain,(
% 0.23/0.55    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.23/0.55    inference(flattening,[],[f14])).
% 0.23/0.55  fof(f14,plain,(
% 0.23/0.55    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.23/0.55    inference(ennf_transformation,[],[f13])).
% 0.23/0.55  fof(f13,negated_conjecture,(
% 0.23/0.55    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 0.23/0.55    inference(negated_conjecture,[],[f12])).
% 0.23/0.55  fof(f12,conjecture,(
% 0.23/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 0.23/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_2)).
% 0.23/0.55  fof(f564,plain,(
% 0.23/0.55    sK0 != k1_relat_1(sK2) | (spl10_2 | spl10_21 | ~spl10_22)),
% 0.23/0.55    inference(forward_demodulation,[],[f563,f239])).
% 0.23/0.55  fof(f239,plain,(
% 0.23/0.55    sK0 = k1_relat_1(sK3) | spl10_2),
% 0.23/0.55    inference(backward_demodulation,[],[f230,f238])).
% 0.23/0.55  fof(f238,plain,(
% 0.23/0.55    sK0 = k1_relset_1(sK0,sK1,sK3) | spl10_2),
% 0.23/0.55    inference(subsumption_resolution,[],[f237,f110])).
% 0.23/0.55  fof(f110,plain,(
% 0.23/0.55    k1_xboole_0 != sK1 | spl10_2),
% 0.23/0.55    inference(avatar_component_clause,[],[f109])).
% 0.23/0.55  fof(f109,plain,(
% 0.23/0.55    spl10_2 <=> k1_xboole_0 = sK1),
% 0.23/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 0.23/0.55  fof(f237,plain,(
% 0.23/0.55    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.23/0.55    inference(subsumption_resolution,[],[f231,f50])).
% 0.23/0.55  fof(f50,plain,(
% 0.23/0.55    v1_funct_2(sK3,sK0,sK1)),
% 0.23/0.55    inference(cnf_transformation,[],[f28])).
% 0.23/0.55  fof(f231,plain,(
% 0.23/0.55    ~v1_funct_2(sK3,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.23/0.55    inference(resolution,[],[f51,f70])).
% 0.23/0.55  % (9645)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.23/0.55  fof(f70,plain,(
% 0.23/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.23/0.55    inference(cnf_transformation,[],[f39])).
% 0.23/0.55  fof(f39,plain,(
% 0.23/0.55    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.23/0.55    inference(nnf_transformation,[],[f24])).
% 0.23/0.55  fof(f24,plain,(
% 0.23/0.55    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.23/0.55    inference(flattening,[],[f23])).
% 0.23/0.55  fof(f23,plain,(
% 0.23/0.55    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.23/0.55    inference(ennf_transformation,[],[f11])).
% 0.23/0.55  % (9657)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.23/0.55  fof(f11,axiom,(
% 0.23/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.23/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.23/0.55  fof(f51,plain,(
% 0.23/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.23/0.55    inference(cnf_transformation,[],[f28])).
% 0.23/0.55  fof(f230,plain,(
% 0.23/0.55    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)),
% 0.23/0.55    inference(resolution,[],[f51,f69])).
% 0.23/0.55  fof(f563,plain,(
% 0.23/0.55    k1_relat_1(sK2) != k1_relat_1(sK3) | (spl10_21 | ~spl10_22)),
% 0.23/0.55    inference(subsumption_resolution,[],[f562,f229])).
% 0.23/0.55  fof(f229,plain,(
% 0.23/0.55    v1_relat_1(sK3)),
% 0.23/0.55    inference(resolution,[],[f51,f68])).
% 0.23/0.55  fof(f68,plain,(
% 0.23/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f21])).
% 0.23/0.55  fof(f21,plain,(
% 0.23/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.23/0.55    inference(ennf_transformation,[],[f8])).
% 0.23/0.55  fof(f8,axiom,(
% 0.23/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.23/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.23/0.55  fof(f562,plain,(
% 0.23/0.55    k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_relat_1(sK3) | (spl10_21 | ~spl10_22)),
% 0.23/0.55    inference(subsumption_resolution,[],[f561,f49])).
% 0.23/0.55  fof(f49,plain,(
% 0.23/0.55    v1_funct_1(sK3)),
% 0.23/0.55    inference(cnf_transformation,[],[f28])).
% 0.23/0.55  fof(f561,plain,(
% 0.23/0.55    k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (spl10_21 | ~spl10_22)),
% 0.23/0.55    inference(subsumption_resolution,[],[f560,f95])).
% 0.23/0.55  fof(f95,plain,(
% 0.23/0.55    v1_relat_1(sK2)),
% 0.23/0.55    inference(resolution,[],[f48,f68])).
% 0.23/0.55  fof(f560,plain,(
% 0.23/0.55    k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (spl10_21 | ~spl10_22)),
% 0.23/0.55    inference(subsumption_resolution,[],[f559,f46])).
% 0.23/0.55  fof(f46,plain,(
% 0.23/0.55    v1_funct_1(sK2)),
% 0.23/0.55    inference(cnf_transformation,[],[f28])).
% 0.23/0.55  fof(f559,plain,(
% 0.23/0.55    k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (spl10_21 | ~spl10_22)),
% 0.23/0.55    inference(subsumption_resolution,[],[f558,f420])).
% 0.23/0.55  fof(f420,plain,(
% 0.23/0.55    sK2 != sK3 | spl10_21),
% 0.23/0.55    inference(avatar_component_clause,[],[f419])).
% 0.23/0.55  fof(f419,plain,(
% 0.23/0.55    spl10_21 <=> sK2 = sK3),
% 0.23/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_21])])).
% 0.23/0.55  fof(f558,plain,(
% 0.23/0.55    sK2 = sK3 | k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl10_22),
% 0.23/0.55    inference(trivial_inequality_removal,[],[f557])).
% 0.23/0.55  fof(f557,plain,(
% 0.23/0.55    k1_funct_1(sK2,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2)) | sK2 = sK3 | k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl10_22),
% 0.23/0.55    inference(superposition,[],[f56,f526])).
% 0.23/0.55  fof(f526,plain,(
% 0.23/0.55    k1_funct_1(sK2,sK4(sK3,sK2)) = k1_funct_1(sK3,sK4(sK3,sK2)) | ~spl10_22),
% 0.23/0.55    inference(resolution,[],[f425,f52])).
% 0.23/0.55  fof(f52,plain,(
% 0.23/0.55    ( ! [X4] : (~r2_hidden(X4,sK0) | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f28])).
% 0.23/0.55  fof(f425,plain,(
% 0.23/0.55    r2_hidden(sK4(sK3,sK2),sK0) | ~spl10_22),
% 0.23/0.55    inference(avatar_component_clause,[],[f423])).
% 0.23/0.55  fof(f423,plain,(
% 0.23/0.55    spl10_22 <=> r2_hidden(sK4(sK3,sK2),sK0)),
% 0.23/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).
% 0.23/0.55  fof(f56,plain,(
% 0.23/0.55    ( ! [X0,X1] : (k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) | X0 = X1 | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f30])).
% 0.23/0.55  fof(f30,plain,(
% 0.23/0.55    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.23/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f17,f29])).
% 0.23/0.55  fof(f29,plain,(
% 0.23/0.55    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),k1_relat_1(X0))))),
% 0.23/0.55    introduced(choice_axiom,[])).
% 0.23/0.55  % (9656)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.23/0.56  fof(f17,plain,(
% 0.23/0.56    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.23/0.56    inference(flattening,[],[f16])).
% 0.23/0.56  fof(f16,plain,(
% 0.23/0.56    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.23/0.56    inference(ennf_transformation,[],[f6])).
% 0.23/0.56  fof(f6,axiom,(
% 0.23/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 0.23/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).
% 0.23/0.56  fof(f475,plain,(
% 0.23/0.56    ~spl10_3 | ~spl10_21),
% 0.23/0.56    inference(avatar_contradiction_clause,[],[f474])).
% 0.23/0.56  fof(f474,plain,(
% 0.23/0.56    $false | (~spl10_3 | ~spl10_21)),
% 0.23/0.56    inference(subsumption_resolution,[],[f430,f271])).
% 0.23/0.56  fof(f271,plain,(
% 0.23/0.56    r2_relset_1(sK0,sK1,sK2,sK2) | ~spl10_3),
% 0.23/0.56    inference(avatar_component_clause,[],[f270])).
% 0.23/0.56  fof(f270,plain,(
% 0.23/0.56    spl10_3 <=> r2_relset_1(sK0,sK1,sK2,sK2)),
% 0.23/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 0.23/0.56  fof(f430,plain,(
% 0.23/0.56    ~r2_relset_1(sK0,sK1,sK2,sK2) | ~spl10_21),
% 0.23/0.56    inference(backward_demodulation,[],[f53,f421])).
% 0.23/0.56  fof(f421,plain,(
% 0.23/0.56    sK2 = sK3 | ~spl10_21),
% 0.23/0.56    inference(avatar_component_clause,[],[f419])).
% 0.23/0.56  % (9655)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.23/0.56  fof(f53,plain,(
% 0.23/0.56    ~r2_relset_1(sK0,sK1,sK2,sK3)),
% 0.23/0.56    inference(cnf_transformation,[],[f28])).
% 0.23/0.56  fof(f426,plain,(
% 0.23/0.56    spl10_21 | spl10_22 | ~spl10_1 | spl10_2),
% 0.23/0.56    inference(avatar_split_clause,[],[f417,f109,f105,f423,f419])).
% 0.23/0.56  fof(f417,plain,(
% 0.23/0.56    r2_hidden(sK4(sK3,sK2),sK0) | sK2 = sK3 | (~spl10_1 | spl10_2)),
% 0.23/0.56    inference(subsumption_resolution,[],[f416,f229])).
% 0.23/0.56  fof(f416,plain,(
% 0.23/0.56    r2_hidden(sK4(sK3,sK2),sK0) | sK2 = sK3 | ~v1_relat_1(sK3) | (~spl10_1 | spl10_2)),
% 0.23/0.56    inference(subsumption_resolution,[],[f415,f49])).
% 0.23/0.56  fof(f415,plain,(
% 0.23/0.56    r2_hidden(sK4(sK3,sK2),sK0) | sK2 = sK3 | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl10_1 | spl10_2)),
% 0.23/0.56    inference(trivial_inequality_removal,[],[f414])).
% 0.23/0.56  fof(f414,plain,(
% 0.23/0.56    sK0 != sK0 | r2_hidden(sK4(sK3,sK2),sK0) | sK2 = sK3 | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl10_1 | spl10_2)),
% 0.23/0.56    inference(superposition,[],[f217,f239])).
% 0.23/0.56  fof(f217,plain,(
% 0.23/0.56    ( ! [X0] : (k1_relat_1(X0) != sK0 | r2_hidden(sK4(X0,sK2),sK0) | sK2 = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl10_1),
% 0.23/0.56    inference(inner_rewriting,[],[f216])).
% 0.23/0.56  fof(f216,plain,(
% 0.23/0.56    ( ! [X0] : (k1_relat_1(X0) != sK0 | r2_hidden(sK4(X0,sK2),k1_relat_1(X0)) | sK2 = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl10_1),
% 0.23/0.56    inference(subsumption_resolution,[],[f215,f95])).
% 0.23/0.56  fof(f215,plain,(
% 0.23/0.56    ( ! [X0] : (k1_relat_1(X0) != sK0 | r2_hidden(sK4(X0,sK2),k1_relat_1(X0)) | sK2 = X0 | ~v1_relat_1(sK2) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl10_1),
% 0.23/0.56    inference(subsumption_resolution,[],[f213,f46])).
% 0.23/0.56  fof(f213,plain,(
% 0.23/0.56    ( ! [X0] : (k1_relat_1(X0) != sK0 | r2_hidden(sK4(X0,sK2),k1_relat_1(X0)) | sK2 = X0 | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl10_1),
% 0.23/0.56    inference(superposition,[],[f55,f212])).
% 0.23/0.56  fof(f55,plain,(
% 0.23/0.56    ( ! [X0,X1] : (k1_relat_1(X0) != k1_relat_1(X1) | r2_hidden(sK4(X0,X1),k1_relat_1(X0)) | X0 = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.23/0.56    inference(cnf_transformation,[],[f30])).
% 0.23/0.56  fof(f374,plain,(
% 0.23/0.56    spl10_3),
% 0.23/0.56    inference(avatar_contradiction_clause,[],[f373])).
% 0.23/0.56  fof(f373,plain,(
% 0.23/0.56    $false | spl10_3),
% 0.23/0.56    inference(subsumption_resolution,[],[f372,f48])).
% 0.23/0.56  fof(f372,plain,(
% 0.23/0.56    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl10_3),
% 0.23/0.56    inference(subsumption_resolution,[],[f371,f326])).
% 0.23/0.56  fof(f326,plain,(
% 0.23/0.56    r2_hidden(k4_tarski(sK6(sK0,sK1,sK2,sK2),sK7(sK0,sK1,sK2,sK2)),sK2) | spl10_3),
% 0.23/0.56    inference(subsumption_resolution,[],[f325,f272])).
% 0.23/0.56  fof(f272,plain,(
% 0.23/0.56    ~r2_relset_1(sK0,sK1,sK2,sK2) | spl10_3),
% 0.23/0.56    inference(avatar_component_clause,[],[f270])).
% 0.23/0.56  fof(f325,plain,(
% 0.23/0.56    r2_hidden(k4_tarski(sK6(sK0,sK1,sK2,sK2),sK7(sK0,sK1,sK2,sK2)),sK2) | r2_relset_1(sK0,sK1,sK2,sK2)),
% 0.23/0.56    inference(duplicate_literal_removal,[],[f321])).
% 0.23/0.56  fof(f321,plain,(
% 0.23/0.56    r2_hidden(k4_tarski(sK6(sK0,sK1,sK2,sK2),sK7(sK0,sK1,sK2,sK2)),sK2) | r2_relset_1(sK0,sK1,sK2,sK2) | r2_hidden(k4_tarski(sK6(sK0,sK1,sK2,sK2),sK7(sK0,sK1,sK2,sK2)),sK2)),
% 0.23/0.56    inference(resolution,[],[f99,f48])).
% 0.23/0.56  fof(f99,plain,(
% 0.23/0.56    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | r2_hidden(k4_tarski(sK6(sK0,sK1,X0,sK2),sK7(sK0,sK1,X0,sK2)),X0) | r2_relset_1(sK0,sK1,X0,sK2) | r2_hidden(k4_tarski(sK6(sK0,sK1,X0,sK2),sK7(sK0,sK1,X0,sK2)),sK2)) )),
% 0.23/0.56    inference(resolution,[],[f48,f80])).
% 0.23/0.56  fof(f80,plain,(
% 0.23/0.56    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_hidden(k4_tarski(sK6(X0,X1,X2,X3),sK7(X0,X1,X2,X3)),X3) | r2_hidden(k4_tarski(sK6(X0,X1,X2,X3),sK7(X0,X1,X2,X3)),X2) | r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.23/0.56    inference(cnf_transformation,[],[f45])).
% 0.23/0.56  fof(f45,plain,(
% 0.23/0.56    ! [X0,X1,X2] : (! [X3] : (((r2_relset_1(X0,X1,X2,X3) | (((~r2_hidden(k4_tarski(sK6(X0,X1,X2,X3),sK7(X0,X1,X2,X3)),X3) | ~r2_hidden(k4_tarski(sK6(X0,X1,X2,X3),sK7(X0,X1,X2,X3)),X2)) & (r2_hidden(k4_tarski(sK6(X0,X1,X2,X3),sK7(X0,X1,X2,X3)),X3) | r2_hidden(k4_tarski(sK6(X0,X1,X2,X3),sK7(X0,X1,X2,X3)),X2)) & m1_subset_1(sK7(X0,X1,X2,X3),X1)) & m1_subset_1(sK6(X0,X1,X2,X3),X0))) & (! [X6] : (! [X7] : (((r2_hidden(k4_tarski(X6,X7),X2) | ~r2_hidden(k4_tarski(X6,X7),X3)) & (r2_hidden(k4_tarski(X6,X7),X3) | ~r2_hidden(k4_tarski(X6,X7),X2))) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0)) | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.23/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f42,f44,f43])).
% 0.23/0.56  fof(f43,plain,(
% 0.23/0.56    ! [X3,X2,X1,X0] : (? [X4] : (? [X5] : ((~r2_hidden(k4_tarski(X4,X5),X3) | ~r2_hidden(k4_tarski(X4,X5),X2)) & (r2_hidden(k4_tarski(X4,X5),X3) | r2_hidden(k4_tarski(X4,X5),X2)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,X0)) => (? [X5] : ((~r2_hidden(k4_tarski(sK6(X0,X1,X2,X3),X5),X3) | ~r2_hidden(k4_tarski(sK6(X0,X1,X2,X3),X5),X2)) & (r2_hidden(k4_tarski(sK6(X0,X1,X2,X3),X5),X3) | r2_hidden(k4_tarski(sK6(X0,X1,X2,X3),X5),X2)) & m1_subset_1(X5,X1)) & m1_subset_1(sK6(X0,X1,X2,X3),X0)))),
% 0.23/0.56    introduced(choice_axiom,[])).
% 0.23/0.56  fof(f44,plain,(
% 0.23/0.56    ! [X3,X2,X1,X0] : (? [X5] : ((~r2_hidden(k4_tarski(sK6(X0,X1,X2,X3),X5),X3) | ~r2_hidden(k4_tarski(sK6(X0,X1,X2,X3),X5),X2)) & (r2_hidden(k4_tarski(sK6(X0,X1,X2,X3),X5),X3) | r2_hidden(k4_tarski(sK6(X0,X1,X2,X3),X5),X2)) & m1_subset_1(X5,X1)) => ((~r2_hidden(k4_tarski(sK6(X0,X1,X2,X3),sK7(X0,X1,X2,X3)),X3) | ~r2_hidden(k4_tarski(sK6(X0,X1,X2,X3),sK7(X0,X1,X2,X3)),X2)) & (r2_hidden(k4_tarski(sK6(X0,X1,X2,X3),sK7(X0,X1,X2,X3)),X3) | r2_hidden(k4_tarski(sK6(X0,X1,X2,X3),sK7(X0,X1,X2,X3)),X2)) & m1_subset_1(sK7(X0,X1,X2,X3),X1)))),
% 0.23/0.56    introduced(choice_axiom,[])).
% 0.23/0.56  fof(f42,plain,(
% 0.23/0.56    ! [X0,X1,X2] : (! [X3] : (((r2_relset_1(X0,X1,X2,X3) | ? [X4] : (? [X5] : ((~r2_hidden(k4_tarski(X4,X5),X3) | ~r2_hidden(k4_tarski(X4,X5),X2)) & (r2_hidden(k4_tarski(X4,X5),X3) | r2_hidden(k4_tarski(X4,X5),X2)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,X0))) & (! [X6] : (! [X7] : (((r2_hidden(k4_tarski(X6,X7),X2) | ~r2_hidden(k4_tarski(X6,X7),X3)) & (r2_hidden(k4_tarski(X6,X7),X3) | ~r2_hidden(k4_tarski(X6,X7),X2))) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0)) | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.23/0.56    inference(rectify,[],[f41])).
% 0.23/0.56  fof(f41,plain,(
% 0.23/0.56    ! [X0,X1,X2] : (! [X3] : (((r2_relset_1(X0,X1,X2,X3) | ? [X4] : (? [X5] : ((~r2_hidden(k4_tarski(X4,X5),X3) | ~r2_hidden(k4_tarski(X4,X5),X2)) & (r2_hidden(k4_tarski(X4,X5),X3) | r2_hidden(k4_tarski(X4,X5),X2)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,X0))) & (! [X4] : (! [X5] : (((r2_hidden(k4_tarski(X4,X5),X2) | ~r2_hidden(k4_tarski(X4,X5),X3)) & (r2_hidden(k4_tarski(X4,X5),X3) | ~r2_hidden(k4_tarski(X4,X5),X2))) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,X0)) | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.23/0.56    inference(flattening,[],[f40])).
% 0.23/0.56  fof(f40,plain,(
% 0.23/0.56    ! [X0,X1,X2] : (! [X3] : (((r2_relset_1(X0,X1,X2,X3) | ? [X4] : (? [X5] : (((~r2_hidden(k4_tarski(X4,X5),X3) | ~r2_hidden(k4_tarski(X4,X5),X2)) & (r2_hidden(k4_tarski(X4,X5),X3) | r2_hidden(k4_tarski(X4,X5),X2))) & m1_subset_1(X5,X1)) & m1_subset_1(X4,X0))) & (! [X4] : (! [X5] : (((r2_hidden(k4_tarski(X4,X5),X2) | ~r2_hidden(k4_tarski(X4,X5),X3)) & (r2_hidden(k4_tarski(X4,X5),X3) | ~r2_hidden(k4_tarski(X4,X5),X2))) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,X0)) | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.23/0.56    inference(nnf_transformation,[],[f25])).
% 0.23/0.56  fof(f25,plain,(
% 0.23/0.56    ! [X0,X1,X2] : (! [X3] : ((r2_relset_1(X0,X1,X2,X3) <=> ! [X4] : (! [X5] : ((r2_hidden(k4_tarski(X4,X5),X2) <=> r2_hidden(k4_tarski(X4,X5),X3)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.23/0.56    inference(ennf_transformation,[],[f9])).
% 0.23/0.56  fof(f9,axiom,(
% 0.23/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r2_relset_1(X0,X1,X2,X3) <=> ! [X4] : (m1_subset_1(X4,X0) => ! [X5] : (m1_subset_1(X5,X1) => (r2_hidden(k4_tarski(X4,X5),X2) <=> r2_hidden(k4_tarski(X4,X5),X3)))))))),
% 0.23/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relset_1)).
% 0.23/0.56  fof(f371,plain,(
% 0.23/0.56    ~r2_hidden(k4_tarski(sK6(sK0,sK1,sK2,sK2),sK7(sK0,sK1,sK2,sK2)),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl10_3),
% 0.23/0.56    inference(subsumption_resolution,[],[f370,f272])).
% 0.23/0.56  fof(f370,plain,(
% 0.23/0.56    r2_relset_1(sK0,sK1,sK2,sK2) | ~r2_hidden(k4_tarski(sK6(sK0,sK1,sK2,sK2),sK7(sK0,sK1,sK2,sK2)),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl10_3),
% 0.23/0.56    inference(duplicate_literal_removal,[],[f367])).
% 0.23/0.56  fof(f367,plain,(
% 0.23/0.56    r2_relset_1(sK0,sK1,sK2,sK2) | ~r2_hidden(k4_tarski(sK6(sK0,sK1,sK2,sK2),sK7(sK0,sK1,sK2,sK2)),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl10_3),
% 0.23/0.56    inference(resolution,[],[f326,f81])).
% 0.23/0.56  fof(f81,plain,(
% 0.23/0.56    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(sK6(X0,X1,X2,X3),sK7(X0,X1,X2,X3)),X3) | r2_relset_1(X0,X1,X2,X3) | ~r2_hidden(k4_tarski(sK6(X0,X1,X2,X3),sK7(X0,X1,X2,X3)),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.23/0.56    inference(cnf_transformation,[],[f45])).
% 0.23/0.56  fof(f210,plain,(
% 0.23/0.56    ~spl10_2),
% 0.23/0.56    inference(avatar_contradiction_clause,[],[f209])).
% 0.23/0.56  fof(f209,plain,(
% 0.23/0.56    $false | ~spl10_2),
% 0.23/0.56    inference(subsumption_resolution,[],[f201,f54])).
% 0.23/0.56  fof(f54,plain,(
% 0.23/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.23/0.56    inference(cnf_transformation,[],[f3])).
% 0.23/0.56  fof(f3,axiom,(
% 0.23/0.56    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.23/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.23/0.56  fof(f201,plain,(
% 0.23/0.56    ~r1_tarski(k1_xboole_0,k4_tarski(sK6(sK0,k1_xboole_0,k1_xboole_0,k1_xboole_0),sK7(sK0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) | ~spl10_2),
% 0.23/0.56    inference(resolution,[],[f197,f67])).
% 0.23/0.56  fof(f67,plain,(
% 0.23/0.56    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.23/0.56    inference(cnf_transformation,[],[f20])).
% 0.23/0.56  fof(f20,plain,(
% 0.23/0.56    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.23/0.56    inference(ennf_transformation,[],[f7])).
% 0.23/0.56  fof(f7,axiom,(
% 0.23/0.56    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.23/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.23/0.56  fof(f197,plain,(
% 0.23/0.56    r2_hidden(k4_tarski(sK6(sK0,k1_xboole_0,k1_xboole_0,k1_xboole_0),sK7(sK0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),k1_xboole_0) | ~spl10_2),
% 0.23/0.56    inference(subsumption_resolution,[],[f194,f190])).
% 0.23/0.56  fof(f190,plain,(
% 0.23/0.56    ~r2_relset_1(sK0,k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~spl10_2),
% 0.23/0.56    inference(backward_demodulation,[],[f155,f184])).
% 0.23/0.56  fof(f184,plain,(
% 0.23/0.56    k1_xboole_0 = sK3 | ~spl10_2),
% 0.23/0.56    inference(subsumption_resolution,[],[f183,f54])).
% 0.23/0.56  fof(f183,plain,(
% 0.23/0.56    k1_xboole_0 = sK3 | ~r1_tarski(k1_xboole_0,sK3) | ~spl10_2),
% 0.23/0.56    inference(resolution,[],[f181,f60])).
% 0.23/0.56  fof(f60,plain,(
% 0.23/0.56    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.23/0.56    inference(cnf_transformation,[],[f32])).
% 0.23/0.56  fof(f32,plain,(
% 0.23/0.56    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.23/0.56    inference(flattening,[],[f31])).
% 0.23/0.56  fof(f31,plain,(
% 0.23/0.56    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.23/0.56    inference(nnf_transformation,[],[f2])).
% 0.23/0.56  fof(f2,axiom,(
% 0.23/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.23/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.23/0.56  fof(f181,plain,(
% 0.23/0.56    r1_tarski(sK3,k1_xboole_0) | ~spl10_2),
% 0.23/0.56    inference(duplicate_literal_removal,[],[f178])).
% 0.23/0.56  fof(f178,plain,(
% 0.23/0.56    r1_tarski(sK3,k1_xboole_0) | r1_tarski(sK3,k1_xboole_0) | ~spl10_2),
% 0.23/0.56    inference(resolution,[],[f141,f63])).
% 0.23/0.56  fof(f63,plain,(
% 0.23/0.56    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.23/0.56    inference(cnf_transformation,[],[f36])).
% 0.23/0.56  fof(f36,plain,(
% 0.23/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.23/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f34,f35])).
% 0.23/0.56  fof(f35,plain,(
% 0.23/0.56    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 0.23/0.56    introduced(choice_axiom,[])).
% 0.23/0.56  fof(f34,plain,(
% 0.23/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.23/0.56    inference(rectify,[],[f33])).
% 0.23/0.56  fof(f33,plain,(
% 0.23/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.23/0.56    inference(nnf_transformation,[],[f19])).
% 0.23/0.56  fof(f19,plain,(
% 0.23/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.23/0.56    inference(ennf_transformation,[],[f1])).
% 0.23/0.56  fof(f1,axiom,(
% 0.23/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.23/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.23/0.56  fof(f141,plain,(
% 0.23/0.56    ( ! [X0] : (r2_hidden(sK5(sK3,X0),k1_xboole_0) | r1_tarski(sK3,X0)) ) | ~spl10_2),
% 0.23/0.56    inference(resolution,[],[f138,f62])).
% 0.23/0.56  fof(f62,plain,(
% 0.23/0.56    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.23/0.56    inference(cnf_transformation,[],[f36])).
% 0.23/0.56  % (9654)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.23/0.56  fof(f138,plain,(
% 0.23/0.56    ( ! [X0] : (~r2_hidden(X0,sK3) | r2_hidden(X0,k1_xboole_0)) ) | ~spl10_2),
% 0.23/0.56    inference(resolution,[],[f124,f57])).
% 0.23/0.56  fof(f57,plain,(
% 0.23/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.23/0.56    inference(cnf_transformation,[],[f18])).
% 0.23/0.56  fof(f18,plain,(
% 0.23/0.56    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.23/0.56    inference(ennf_transformation,[],[f5])).
% 0.23/0.56  fof(f5,axiom,(
% 0.23/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.23/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.23/0.56  fof(f124,plain,(
% 0.23/0.56    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | ~spl10_2),
% 0.23/0.56    inference(forward_demodulation,[],[f116,f84])).
% 0.23/0.56  fof(f84,plain,(
% 0.23/0.56    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.23/0.56    inference(equality_resolution,[],[f66])).
% 0.23/0.56  fof(f66,plain,(
% 0.23/0.56    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.23/0.56    inference(cnf_transformation,[],[f38])).
% 0.23/0.56  fof(f38,plain,(
% 0.23/0.56    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.23/0.56    inference(flattening,[],[f37])).
% 0.23/0.56  fof(f37,plain,(
% 0.23/0.56    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.23/0.56    inference(nnf_transformation,[],[f4])).
% 0.23/0.56  fof(f4,axiom,(
% 0.23/0.56    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.23/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.23/0.56  fof(f116,plain,(
% 0.23/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl10_2),
% 0.23/0.56    inference(backward_demodulation,[],[f51,f111])).
% 0.23/0.56  fof(f111,plain,(
% 0.23/0.56    k1_xboole_0 = sK1 | ~spl10_2),
% 0.23/0.56    inference(avatar_component_clause,[],[f109])).
% 0.23/0.56  fof(f155,plain,(
% 0.23/0.56    ~r2_relset_1(sK0,k1_xboole_0,k1_xboole_0,sK3) | ~spl10_2),
% 0.23/0.56    inference(backward_demodulation,[],[f117,f150])).
% 0.23/0.56  fof(f150,plain,(
% 0.23/0.56    k1_xboole_0 = sK2 | ~spl10_2),
% 0.23/0.56    inference(subsumption_resolution,[],[f149,f54])).
% 0.23/0.56  fof(f149,plain,(
% 0.23/0.56    k1_xboole_0 = sK2 | ~r1_tarski(k1_xboole_0,sK2) | ~spl10_2),
% 0.23/0.56    inference(resolution,[],[f147,f60])).
% 0.23/0.56  fof(f147,plain,(
% 0.23/0.56    r1_tarski(sK2,k1_xboole_0) | ~spl10_2),
% 0.23/0.56    inference(duplicate_literal_removal,[],[f144])).
% 0.23/0.56  fof(f144,plain,(
% 0.23/0.56    r1_tarski(sK2,k1_xboole_0) | r1_tarski(sK2,k1_xboole_0) | ~spl10_2),
% 0.23/0.56    inference(resolution,[],[f140,f63])).
% 0.23/0.56  fof(f140,plain,(
% 0.23/0.56    ( ! [X0] : (r2_hidden(sK5(sK2,X0),k1_xboole_0) | r1_tarski(sK2,X0)) ) | ~spl10_2),
% 0.23/0.56    inference(resolution,[],[f135,f62])).
% 0.23/0.56  fof(f135,plain,(
% 0.23/0.56    ( ! [X5] : (~r2_hidden(X5,sK2) | r2_hidden(X5,k1_xboole_0)) ) | ~spl10_2),
% 0.23/0.56    inference(forward_demodulation,[],[f122,f84])).
% 0.23/0.56  fof(f122,plain,(
% 0.23/0.56    ( ! [X5] : (r2_hidden(X5,k2_zfmisc_1(sK0,k1_xboole_0)) | ~r2_hidden(X5,sK2)) ) | ~spl10_2),
% 0.23/0.56    inference(backward_demodulation,[],[f102,f111])).
% 0.23/0.56  fof(f102,plain,(
% 0.23/0.56    ( ! [X5] : (r2_hidden(X5,k2_zfmisc_1(sK0,sK1)) | ~r2_hidden(X5,sK2)) )),
% 0.23/0.56    inference(resolution,[],[f48,f57])).
% 0.23/0.56  fof(f117,plain,(
% 0.23/0.56    ~r2_relset_1(sK0,k1_xboole_0,sK2,sK3) | ~spl10_2),
% 0.23/0.56    inference(backward_demodulation,[],[f53,f111])).
% 0.23/0.56  fof(f194,plain,(
% 0.23/0.56    r2_hidden(k4_tarski(sK6(sK0,k1_xboole_0,k1_xboole_0,k1_xboole_0),sK7(sK0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),k1_xboole_0) | r2_relset_1(sK0,k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~spl10_2),
% 0.23/0.56    inference(resolution,[],[f171,f157])).
% 0.23/0.56  fof(f157,plain,(
% 0.23/0.56    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~spl10_2),
% 0.23/0.56    inference(backward_demodulation,[],[f123,f150])).
% 0.23/0.56  fof(f123,plain,(
% 0.23/0.56    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl10_2),
% 0.23/0.56    inference(forward_demodulation,[],[f114,f84])).
% 0.23/0.56  fof(f114,plain,(
% 0.23/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl10_2),
% 0.23/0.56    inference(backward_demodulation,[],[f48,f111])).
% 0.23/0.56  fof(f171,plain,(
% 0.23/0.56    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | r2_hidden(k4_tarski(sK6(sK0,k1_xboole_0,X0,k1_xboole_0),sK7(sK0,k1_xboole_0,X0,k1_xboole_0)),k1_xboole_0) | r2_relset_1(sK0,k1_xboole_0,X0,k1_xboole_0)) ) | ~spl10_2),
% 0.23/0.56    inference(subsumption_resolution,[],[f170,f57])).
% 0.23/0.56  fof(f170,plain,(
% 0.23/0.56    ( ! [X0] : (r2_hidden(k4_tarski(sK6(sK0,k1_xboole_0,X0,k1_xboole_0),sK7(sK0,k1_xboole_0,X0,k1_xboole_0)),X0) | r2_relset_1(sK0,k1_xboole_0,X0,k1_xboole_0) | r2_hidden(k4_tarski(sK6(sK0,k1_xboole_0,X0,k1_xboole_0),sK7(sK0,k1_xboole_0,X0,k1_xboole_0)),k1_xboole_0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))) ) | ~spl10_2),
% 0.23/0.56    inference(forward_demodulation,[],[f169,f150])).
% 0.23/0.56  fof(f169,plain,(
% 0.23/0.56    ( ! [X0] : (r2_relset_1(sK0,k1_xboole_0,X0,k1_xboole_0) | r2_hidden(k4_tarski(sK6(sK0,k1_xboole_0,X0,k1_xboole_0),sK7(sK0,k1_xboole_0,X0,k1_xboole_0)),k1_xboole_0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | r2_hidden(k4_tarski(sK6(sK0,k1_xboole_0,X0,sK2),sK7(sK0,k1_xboole_0,X0,sK2)),X0)) ) | ~spl10_2),
% 0.23/0.56    inference(forward_demodulation,[],[f158,f150])).
% 0.23/0.56  fof(f158,plain,(
% 0.23/0.56    ( ! [X0] : (r2_hidden(k4_tarski(sK6(sK0,k1_xboole_0,X0,k1_xboole_0),sK7(sK0,k1_xboole_0,X0,k1_xboole_0)),k1_xboole_0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | r2_relset_1(sK0,k1_xboole_0,X0,sK2) | r2_hidden(k4_tarski(sK6(sK0,k1_xboole_0,X0,sK2),sK7(sK0,k1_xboole_0,X0,sK2)),X0)) ) | ~spl10_2),
% 0.23/0.56    inference(backward_demodulation,[],[f128,f150])).
% 0.23/0.56  fof(f128,plain,(
% 0.23/0.56    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | r2_relset_1(sK0,k1_xboole_0,X0,sK2) | r2_hidden(k4_tarski(sK6(sK0,k1_xboole_0,X0,sK2),sK7(sK0,k1_xboole_0,X0,sK2)),X0) | r2_hidden(k4_tarski(sK6(sK0,k1_xboole_0,X0,sK2),sK7(sK0,k1_xboole_0,X0,sK2)),sK2)) ) | ~spl10_2),
% 0.23/0.56    inference(forward_demodulation,[],[f127,f84])).
% 0.23/0.56  fof(f127,plain,(
% 0.23/0.56    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | r2_relset_1(sK0,k1_xboole_0,X0,sK2) | r2_hidden(k4_tarski(sK6(sK0,k1_xboole_0,X0,sK2),sK7(sK0,k1_xboole_0,X0,sK2)),X0) | r2_hidden(k4_tarski(sK6(sK0,k1_xboole_0,X0,sK2),sK7(sK0,k1_xboole_0,X0,sK2)),sK2)) ) | ~spl10_2),
% 0.23/0.56    inference(forward_demodulation,[],[f126,f111])).
% 0.23/0.56  fof(f126,plain,(
% 0.23/0.56    ( ! [X0] : (r2_relset_1(sK0,k1_xboole_0,X0,sK2) | r2_hidden(k4_tarski(sK6(sK0,k1_xboole_0,X0,sK2),sK7(sK0,k1_xboole_0,X0,sK2)),X0) | r2_hidden(k4_tarski(sK6(sK0,k1_xboole_0,X0,sK2),sK7(sK0,k1_xboole_0,X0,sK2)),sK2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) ) | ~spl10_2),
% 0.23/0.56    inference(forward_demodulation,[],[f125,f111])).
% 0.23/0.56  fof(f125,plain,(
% 0.23/0.56    ( ! [X0] : (r2_hidden(k4_tarski(sK6(sK0,k1_xboole_0,X0,sK2),sK7(sK0,k1_xboole_0,X0,sK2)),X0) | r2_hidden(k4_tarski(sK6(sK0,k1_xboole_0,X0,sK2),sK7(sK0,k1_xboole_0,X0,sK2)),sK2) | r2_relset_1(sK0,sK1,X0,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) ) | ~spl10_2),
% 0.23/0.56    inference(forward_demodulation,[],[f119,f111])).
% 0.23/0.56  fof(f119,plain,(
% 0.23/0.56    ( ! [X0] : (r2_hidden(k4_tarski(sK6(sK0,k1_xboole_0,X0,sK2),sK7(sK0,k1_xboole_0,X0,sK2)),sK2) | r2_hidden(k4_tarski(sK6(sK0,sK1,X0,sK2),sK7(sK0,sK1,X0,sK2)),X0) | r2_relset_1(sK0,sK1,X0,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) ) | ~spl10_2),
% 0.23/0.56    inference(backward_demodulation,[],[f99,f111])).
% 0.23/0.56  fof(f112,plain,(
% 0.23/0.56    spl10_1 | spl10_2),
% 0.23/0.56    inference(avatar_split_clause,[],[f103,f109,f105])).
% 0.23/0.56  fof(f103,plain,(
% 0.23/0.56    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.23/0.56    inference(subsumption_resolution,[],[f97,f47])).
% 0.23/0.56  fof(f47,plain,(
% 0.23/0.56    v1_funct_2(sK2,sK0,sK1)),
% 0.23/0.56    inference(cnf_transformation,[],[f28])).
% 0.23/0.56  fof(f97,plain,(
% 0.23/0.56    ~v1_funct_2(sK2,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.23/0.56    inference(resolution,[],[f48,f70])).
% 0.23/0.56  % SZS output end Proof for theBenchmark
% 0.23/0.56  % (9636)------------------------------
% 0.23/0.56  % (9636)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.56  % (9636)Termination reason: Refutation
% 0.23/0.56  
% 0.23/0.56  % (9636)Memory used [KB]: 11001
% 0.23/0.56  % (9636)Time elapsed: 0.117 s
% 0.23/0.56  % (9636)------------------------------
% 0.23/0.56  % (9636)------------------------------
% 0.23/0.56  % (9650)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.23/0.56  % (9649)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.23/0.56  % (9627)Success in time 0.191 s
%------------------------------------------------------------------------------
