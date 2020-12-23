%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:20 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 214 expanded)
%              Number of leaves         :   25 (  83 expanded)
%              Depth                    :   16
%              Number of atoms          :  417 (1154 expanded)
%              Number of equality atoms :   95 ( 232 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f162,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f69,f74,f79,f84,f89,f99,f122,f127,f134,f151,f157,f160,f161])).

fof(f161,plain,
    ( k6_partfun1(sK0) != sK1
    | r2_funct_2(sK0,sK0,sK1,k6_partfun1(sK0))
    | ~ r2_funct_2(sK0,sK0,sK1,sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f160,plain,
    ( spl3_1
    | spl3_14
    | ~ spl3_15 ),
    inference(avatar_contradiction_clause,[],[f158])).

fof(f158,plain,
    ( $false
    | spl3_1
    | spl3_14
    | ~ spl3_15 ),
    inference(unit_resulting_resolution,[],[f68,f150,f156,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f156,plain,
    ( r2_hidden(sK2(sK0,sK1),sK0)
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl3_15
  <=> r2_hidden(sK2(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f150,plain,
    ( ~ m1_subset_1(sK2(sK0,sK1),sK0)
    | spl3_14 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl3_14
  <=> m1_subset_1(sK2(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f68,plain,
    ( ~ v1_xboole_0(sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl3_1
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f157,plain,
    ( ~ spl3_6
    | ~ spl3_2
    | spl3_13
    | spl3_15
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f135,f131,f154,f144,f71,f96])).

fof(f96,plain,
    ( spl3_6
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f71,plain,
    ( spl3_2
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f144,plain,
    ( spl3_13
  <=> k6_partfun1(sK0) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f131,plain,
    ( spl3_11
  <=> sK0 = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f135,plain,
    ( r2_hidden(sK2(sK0,sK1),sK0)
    | k6_partfun1(sK0) = sK1
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl3_11 ),
    inference(superposition,[],[f60,f133])).

fof(f133,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f131])).

fof(f60,plain,(
    ! [X1] :
      ( r2_hidden(sK2(k1_relat_1(X1),X1),k1_relat_1(X1))
      | k6_partfun1(k1_relat_1(X1)) = X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k6_partfun1(X0) = X1
      | r2_hidden(sK2(X0,X1),X0)
      | k1_relat_1(X1) != X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f47,f40])).

fof(f40,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f47,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) = X1
      | r2_hidden(sK2(X0,X1),X0)
      | k1_relat_1(X1) != X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ( sK2(X0,X1) != k1_funct_1(X1,sK2(X0,X1))
            & r2_hidden(sK2(X0,X1),X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X3] :
                ( k1_funct_1(X1,X3) = X3
                | ~ r2_hidden(X3,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X1,X2) != X2
          & r2_hidden(X2,X0) )
     => ( sK2(X0,X1) != k1_funct_1(X1,sK2(X0,X1))
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X3] :
                ( k1_funct_1(X1,X3) = X3
                | ~ r2_hidden(X3,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X2] :
                ( k1_funct_1(X1,X2) = X2
                | ~ r2_hidden(X2,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X2] :
                ( k1_funct_1(X1,X2) = X2
                | ~ r2_hidden(X2,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( r2_hidden(X2,X0)
             => k1_funct_1(X1,X2) = X2 )
          & k1_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_1)).

fof(f151,plain,
    ( ~ spl3_6
    | spl3_13
    | ~ spl3_14
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f138,f131,f148,f144,f96])).

fof(f138,plain,
    ( ~ m1_subset_1(sK2(sK0,sK1),sK0)
    | k6_partfun1(sK0) = sK1
    | ~ v1_relat_1(sK1)
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f137,f133])).

fof(f137,plain,
    ( k6_partfun1(sK0) = sK1
    | ~ v1_relat_1(sK1)
    | ~ m1_subset_1(sK2(k1_relat_1(sK1),sK1),sK0)
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f117,f133])).

fof(f117,plain,
    ( sK1 = k6_partfun1(k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ m1_subset_1(sK2(k1_relat_1(sK1),sK1),sK0) ),
    inference(global_subsumption,[],[f35,f116])).

fof(f116,plain,
    ( sK1 = k6_partfun1(k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ m1_subset_1(sK2(k1_relat_1(sK1),sK1),sK0) ),
    inference(trivial_inequality_removal,[],[f115])).

fof(f115,plain,
    ( sK2(k1_relat_1(sK1),sK1) != sK2(k1_relat_1(sK1),sK1)
    | sK1 = k6_partfun1(k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ m1_subset_1(sK2(k1_relat_1(sK1),sK1),sK0) ),
    inference(superposition,[],[f59,f113])).

fof(f113,plain,(
    ! [X1] :
      ( k1_funct_1(sK1,X1) = X1
      | ~ m1_subset_1(X1,sK0) ) ),
    inference(global_subsumption,[],[f34,f35,f36,f37,f112])).

fof(f112,plain,(
    ! [X1] :
      ( k1_funct_1(sK1,X1) = X1
      | ~ m1_subset_1(X1,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ v1_funct_2(sK1,sK0,sK0)
      | ~ v1_funct_1(sK1)
      | v1_xboole_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f109])).

fof(f109,plain,(
    ! [X1] :
      ( k1_funct_1(sK1,X1) = X1
      | ~ m1_subset_1(X1,sK0)
      | ~ m1_subset_1(X1,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ v1_funct_2(sK1,sK0,sK0)
      | ~ v1_funct_1(sK1)
      | v1_xboole_0(sK0) ) ),
    inference(superposition,[],[f38,f52])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

% (11153)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% (11168)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% (11163)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% (11147)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% (11156)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(f38,plain,(
    ! [X2] :
      ( k3_funct_2(sK0,sK0,sK1,X2) = X2
      | ~ m1_subset_1(X2,sK0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ~ r2_funct_2(sK0,sK0,sK1,k6_partfun1(sK0))
    & ! [X2] :
        ( k3_funct_2(sK0,sK0,sK1,X2) = X2
        | ~ m1_subset_1(X2,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f25,f24])).

fof(f24,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r2_funct_2(X0,X0,X1,k6_partfun1(X0))
            & ! [X2] :
                ( k3_funct_2(X0,X0,X1,X2) = X2
                | ~ m1_subset_1(X2,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X1,X0,X0)
            & v1_funct_1(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ~ r2_funct_2(sK0,sK0,X1,k6_partfun1(sK0))
          & ! [X2] :
              ( k3_funct_2(sK0,sK0,X1,X2) = X2
              | ~ m1_subset_1(X2,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
          & v1_funct_2(X1,sK0,sK0)
          & v1_funct_1(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X1] :
        ( ~ r2_funct_2(sK0,sK0,X1,k6_partfun1(sK0))
        & ! [X2] :
            ( k3_funct_2(sK0,sK0,X1,X2) = X2
            | ~ m1_subset_1(X2,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        & v1_funct_2(X1,sK0,sK0)
        & v1_funct_1(X1) )
   => ( ~ r2_funct_2(sK0,sK0,sK1,k6_partfun1(sK0))
      & ! [X2] :
          ( k3_funct_2(sK0,sK0,sK1,X2) = X2
          | ~ m1_subset_1(X2,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_funct_2(X0,X0,X1,k6_partfun1(X0))
          & ! [X2] :
              ( k3_funct_2(X0,X0,X1,X2) = X2
              | ~ m1_subset_1(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_funct_2(X0,X0,X1,k6_partfun1(X0))
          & ! [X2] :
              ( k3_funct_2(X0,X0,X1,X2) = X2
              | ~ m1_subset_1(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_2(X1,X0,X0)
              & v1_funct_1(X1) )
           => ( ! [X2] :
                  ( m1_subset_1(X2,X0)
                 => k3_funct_2(X0,X0,X1,X2) = X2 )
             => r2_funct_2(X0,X0,X1,k6_partfun1(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X1,X0,X0)
            & v1_funct_1(X1) )
         => ( ! [X2] :
                ( m1_subset_1(X2,X0)
               => k3_funct_2(X0,X0,X1,X2) = X2 )
           => r2_funct_2(X0,X0,X1,k6_partfun1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t201_funct_2)).

fof(f37,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f36,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f34,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f26])).

% (11140)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
fof(f59,plain,(
    ! [X1] :
      ( sK2(k1_relat_1(X1),X1) != k1_funct_1(X1,sK2(k1_relat_1(X1),X1))
      | k6_partfun1(k1_relat_1(X1)) = X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k6_partfun1(X0) = X1
      | sK2(X0,X1) != k1_funct_1(X1,sK2(X0,X1))
      | k1_relat_1(X1) != X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f48,f40])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) = X1
      | sK2(X0,X1) != k1_funct_1(X1,sK2(X0,X1))
      | k1_relat_1(X1) != X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f35,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f134,plain,
    ( ~ spl3_4
    | spl3_11
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f128,f124,f131,f81])).

fof(f81,plain,
    ( spl3_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f124,plain,
    ( spl3_10
  <=> sK0 = k1_relset_1(sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f128,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_10 ),
    inference(superposition,[],[f126,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f126,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f124])).

fof(f127,plain,
    ( ~ spl3_2
    | ~ spl3_3
    | spl3_10
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f90,f81,f124,f76,f71])).

fof(f76,plain,
    ( spl3_3
  <=> v1_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f90,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl3_4 ),
    inference(resolution,[],[f83,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | k1_relset_1(X0,X0,X1) = X0
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).

fof(f83,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f81])).

fof(f122,plain,
    ( ~ spl3_2
    | ~ spl3_3
    | spl3_9
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f92,f81,f119,f76,f71])).

fof(f119,plain,
    ( spl3_9
  <=> r2_funct_2(sK0,sK0,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f92,plain,
    ( r2_funct_2(sK0,sK0,sK1,sK1)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl3_4 ),
    inference(resolution,[],[f83,f64])).

% (11159)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
fof(f64,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_funct_2(X0,X1,X3,X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(duplicate_literal_removal,[],[f63])).

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_funct_2(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_funct_2(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

fof(f99,plain,
    ( spl3_6
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f93,f81,f96])).

fof(f93,plain,
    ( v1_relat_1(sK1)
    | ~ spl3_4 ),
    inference(resolution,[],[f83,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f89,plain,(
    ~ spl3_5 ),
    inference(avatar_split_clause,[],[f39,f86])).

fof(f86,plain,
    ( spl3_5
  <=> r2_funct_2(sK0,sK0,sK1,k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f39,plain,(
    ~ r2_funct_2(sK0,sK0,sK1,k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f26])).

fof(f84,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f37,f81])).

fof(f79,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f36,f76])).

fof(f74,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f35,f71])).

fof(f69,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f34,f66])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n003.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:39:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.53  % (11148)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.54  % (11150)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.54  % (11164)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.54  % (11150)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % (11145)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.54  % (11162)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.54  % (11141)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.54  % (11143)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.54  % (11151)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.54  % (11152)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.54  % (11144)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.54  % (11141)Refutation not found, incomplete strategy% (11141)------------------------------
% 0.22/0.54  % (11141)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (11141)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (11141)Memory used [KB]: 1791
% 0.22/0.54  % (11141)Time elapsed: 0.130 s
% 0.22/0.54  % (11141)------------------------------
% 0.22/0.54  % (11141)------------------------------
% 0.22/0.54  % (11142)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.54  % (11165)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.54  % (11144)Refutation not found, incomplete strategy% (11144)------------------------------
% 0.22/0.54  % (11144)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (11144)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (11144)Memory used [KB]: 1791
% 0.22/0.54  % (11144)Time elapsed: 0.125 s
% 0.22/0.54  % (11144)------------------------------
% 0.22/0.54  % (11144)------------------------------
% 0.22/0.54  % (11154)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.55  % (11146)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.55  % (11157)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.55  % (11161)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.55  % (11160)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.55  % (11169)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.55  % (11149)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.55  % (11169)Refutation not found, incomplete strategy% (11169)------------------------------
% 0.22/0.55  % (11169)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (11169)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (11169)Memory used [KB]: 1663
% 0.22/0.55  % (11169)Time elapsed: 0.001 s
% 0.22/0.55  % (11169)------------------------------
% 0.22/0.55  % (11169)------------------------------
% 0.22/0.55  % (11152)Refutation not found, incomplete strategy% (11152)------------------------------
% 0.22/0.55  % (11152)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (11152)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (11152)Memory used [KB]: 10746
% 0.22/0.55  % (11166)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.55  % (11152)Time elapsed: 0.133 s
% 0.22/0.55  % (11152)------------------------------
% 0.22/0.55  % (11152)------------------------------
% 0.22/0.55  % SZS output start Proof for theBenchmark
% 0.22/0.55  fof(f162,plain,(
% 0.22/0.55    $false),
% 0.22/0.55    inference(avatar_sat_refutation,[],[f69,f74,f79,f84,f89,f99,f122,f127,f134,f151,f157,f160,f161])).
% 0.22/0.55  fof(f161,plain,(
% 0.22/0.55    k6_partfun1(sK0) != sK1 | r2_funct_2(sK0,sK0,sK1,k6_partfun1(sK0)) | ~r2_funct_2(sK0,sK0,sK1,sK1)),
% 0.22/0.55    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.55  fof(f160,plain,(
% 0.22/0.55    spl3_1 | spl3_14 | ~spl3_15),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f158])).
% 0.22/0.55  fof(f158,plain,(
% 0.22/0.55    $false | (spl3_1 | spl3_14 | ~spl3_15)),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f68,f150,f156,f42])).
% 0.22/0.55  fof(f42,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~r2_hidden(X1,X0) | m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f27])).
% 0.22/0.55  fof(f27,plain,(
% 0.22/0.55    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.22/0.55    inference(nnf_transformation,[],[f13])).
% 0.22/0.55  fof(f13,plain,(
% 0.22/0.55    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.22/0.55    inference(ennf_transformation,[],[f1])).
% 0.22/0.55  fof(f1,axiom,(
% 0.22/0.55    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 0.22/0.55  fof(f156,plain,(
% 0.22/0.55    r2_hidden(sK2(sK0,sK1),sK0) | ~spl3_15),
% 0.22/0.55    inference(avatar_component_clause,[],[f154])).
% 0.22/0.55  fof(f154,plain,(
% 0.22/0.55    spl3_15 <=> r2_hidden(sK2(sK0,sK1),sK0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.22/0.55  fof(f150,plain,(
% 0.22/0.55    ~m1_subset_1(sK2(sK0,sK1),sK0) | spl3_14),
% 0.22/0.55    inference(avatar_component_clause,[],[f148])).
% 0.22/0.55  fof(f148,plain,(
% 0.22/0.55    spl3_14 <=> m1_subset_1(sK2(sK0,sK1),sK0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.22/0.55  fof(f68,plain,(
% 0.22/0.55    ~v1_xboole_0(sK0) | spl3_1),
% 0.22/0.55    inference(avatar_component_clause,[],[f66])).
% 0.22/0.55  fof(f66,plain,(
% 0.22/0.55    spl3_1 <=> v1_xboole_0(sK0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.55  fof(f157,plain,(
% 0.22/0.55    ~spl3_6 | ~spl3_2 | spl3_13 | spl3_15 | ~spl3_11),
% 0.22/0.55    inference(avatar_split_clause,[],[f135,f131,f154,f144,f71,f96])).
% 0.22/0.55  fof(f96,plain,(
% 0.22/0.55    spl3_6 <=> v1_relat_1(sK1)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.55  fof(f71,plain,(
% 0.22/0.55    spl3_2 <=> v1_funct_1(sK1)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.55  fof(f144,plain,(
% 0.22/0.55    spl3_13 <=> k6_partfun1(sK0) = sK1),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.22/0.55  fof(f131,plain,(
% 0.22/0.55    spl3_11 <=> sK0 = k1_relat_1(sK1)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.55  fof(f135,plain,(
% 0.22/0.55    r2_hidden(sK2(sK0,sK1),sK0) | k6_partfun1(sK0) = sK1 | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~spl3_11),
% 0.22/0.55    inference(superposition,[],[f60,f133])).
% 0.22/0.55  fof(f133,plain,(
% 0.22/0.55    sK0 = k1_relat_1(sK1) | ~spl3_11),
% 0.22/0.55    inference(avatar_component_clause,[],[f131])).
% 0.22/0.55  fof(f60,plain,(
% 0.22/0.55    ( ! [X1] : (r2_hidden(sK2(k1_relat_1(X1),X1),k1_relat_1(X1)) | k6_partfun1(k1_relat_1(X1)) = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.55    inference(equality_resolution,[],[f56])).
% 0.22/0.55  fof(f56,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k6_partfun1(X0) = X1 | r2_hidden(sK2(X0,X1),X0) | k1_relat_1(X1) != X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.55    inference(definition_unfolding,[],[f47,f40])).
% 0.22/0.55  fof(f40,plain,(
% 0.22/0.55    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f6])).
% 0.22/0.55  fof(f6,axiom,(
% 0.22/0.55    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.22/0.55  fof(f47,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k6_relat_1(X0) = X1 | r2_hidden(sK2(X0,X1),X0) | k1_relat_1(X1) != X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f32])).
% 0.22/0.55  fof(f32,plain,(
% 0.22/0.55    ! [X0,X1] : (((k6_relat_1(X0) = X1 | (sK2(X0,X1) != k1_funct_1(X1,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),X0)) | k1_relat_1(X1) != X0) & ((! [X3] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f31])).
% 0.22/0.55  fof(f31,plain,(
% 0.22/0.55    ! [X1,X0] : (? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) => (sK2(X0,X1) != k1_funct_1(X1,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),X0)))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f30,plain,(
% 0.22/0.55    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0) & ((! [X3] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.55    inference(rectify,[],[f29])).
% 0.22/0.55  fof(f29,plain,(
% 0.22/0.55    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.55    inference(flattening,[],[f28])).
% 0.22/0.55  fof(f28,plain,(
% 0.22/0.55    ! [X0,X1] : (((k6_relat_1(X0) = X1 | (? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0)) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.55    inference(nnf_transformation,[],[f15])).
% 0.22/0.55  fof(f15,plain,(
% 0.22/0.55    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.55    inference(flattening,[],[f14])).
% 0.22/0.55  fof(f14,plain,(
% 0.22/0.55    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.55    inference(ennf_transformation,[],[f2])).
% 0.22/0.55  fof(f2,axiom,(
% 0.22/0.55    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k6_relat_1(X0) = X1 <=> (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = X2) & k1_relat_1(X1) = X0)))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_1)).
% 0.22/0.55  fof(f151,plain,(
% 0.22/0.55    ~spl3_6 | spl3_13 | ~spl3_14 | ~spl3_11),
% 0.22/0.55    inference(avatar_split_clause,[],[f138,f131,f148,f144,f96])).
% 0.22/0.55  fof(f138,plain,(
% 0.22/0.55    ~m1_subset_1(sK2(sK0,sK1),sK0) | k6_partfun1(sK0) = sK1 | ~v1_relat_1(sK1) | ~spl3_11),
% 0.22/0.55    inference(forward_demodulation,[],[f137,f133])).
% 0.22/0.55  fof(f137,plain,(
% 0.22/0.55    k6_partfun1(sK0) = sK1 | ~v1_relat_1(sK1) | ~m1_subset_1(sK2(k1_relat_1(sK1),sK1),sK0) | ~spl3_11),
% 0.22/0.55    inference(forward_demodulation,[],[f117,f133])).
% 0.22/0.55  fof(f117,plain,(
% 0.22/0.55    sK1 = k6_partfun1(k1_relat_1(sK1)) | ~v1_relat_1(sK1) | ~m1_subset_1(sK2(k1_relat_1(sK1),sK1),sK0)),
% 0.22/0.55    inference(global_subsumption,[],[f35,f116])).
% 0.22/0.55  fof(f116,plain,(
% 0.22/0.55    sK1 = k6_partfun1(k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~m1_subset_1(sK2(k1_relat_1(sK1),sK1),sK0)),
% 0.22/0.55    inference(trivial_inequality_removal,[],[f115])).
% 0.22/0.55  fof(f115,plain,(
% 0.22/0.55    sK2(k1_relat_1(sK1),sK1) != sK2(k1_relat_1(sK1),sK1) | sK1 = k6_partfun1(k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~m1_subset_1(sK2(k1_relat_1(sK1),sK1),sK0)),
% 0.22/0.55    inference(superposition,[],[f59,f113])).
% 0.22/0.55  fof(f113,plain,(
% 0.22/0.55    ( ! [X1] : (k1_funct_1(sK1,X1) = X1 | ~m1_subset_1(X1,sK0)) )),
% 0.22/0.55    inference(global_subsumption,[],[f34,f35,f36,f37,f112])).
% 0.22/0.55  fof(f112,plain,(
% 0.22/0.55    ( ! [X1] : (k1_funct_1(sK1,X1) = X1 | ~m1_subset_1(X1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | v1_xboole_0(sK0)) )),
% 0.22/0.55    inference(duplicate_literal_removal,[],[f109])).
% 0.22/0.55  fof(f109,plain,(
% 0.22/0.55    ( ! [X1] : (k1_funct_1(sK1,X1) = X1 | ~m1_subset_1(X1,sK0) | ~m1_subset_1(X1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | v1_xboole_0(sK0)) )),
% 0.22/0.55    inference(superposition,[],[f38,f52])).
% 0.22/0.55  fof(f52,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f21])).
% 0.22/0.55  fof(f21,plain,(
% 0.22/0.55    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 0.22/0.55    inference(flattening,[],[f20])).
% 0.22/0.55  fof(f20,plain,(
% 0.22/0.55    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 0.22/0.55    inference(ennf_transformation,[],[f5])).
% 0.22/0.55  % (11153)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.55  % (11168)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.55  % (11163)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.55  % (11147)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.55  % (11156)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.55  fof(f5,axiom,(
% 0.22/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).
% 0.22/0.55  fof(f38,plain,(
% 0.22/0.55    ( ! [X2] : (k3_funct_2(sK0,sK0,sK1,X2) = X2 | ~m1_subset_1(X2,sK0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f26])).
% 0.22/0.55  fof(f26,plain,(
% 0.22/0.55    (~r2_funct_2(sK0,sK0,sK1,k6_partfun1(sK0)) & ! [X2] : (k3_funct_2(sK0,sK0,sK1,X2) = X2 | ~m1_subset_1(X2,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)) & ~v1_xboole_0(sK0)),
% 0.22/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f25,f24])).
% 0.22/0.55  fof(f24,plain,(
% 0.22/0.55    ? [X0] : (? [X1] : (~r2_funct_2(X0,X0,X1,k6_partfun1(X0)) & ! [X2] : (k3_funct_2(X0,X0,X1,X2) = X2 | ~m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (~r2_funct_2(sK0,sK0,X1,k6_partfun1(sK0)) & ! [X2] : (k3_funct_2(sK0,sK0,X1,X2) = X2 | ~m1_subset_1(X2,sK0)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(X1,sK0,sK0) & v1_funct_1(X1)) & ~v1_xboole_0(sK0))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f25,plain,(
% 0.22/0.55    ? [X1] : (~r2_funct_2(sK0,sK0,X1,k6_partfun1(sK0)) & ! [X2] : (k3_funct_2(sK0,sK0,X1,X2) = X2 | ~m1_subset_1(X2,sK0)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(X1,sK0,sK0) & v1_funct_1(X1)) => (~r2_funct_2(sK0,sK0,sK1,k6_partfun1(sK0)) & ! [X2] : (k3_funct_2(sK0,sK0,sK1,X2) = X2 | ~m1_subset_1(X2,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f12,plain,(
% 0.22/0.55    ? [X0] : (? [X1] : (~r2_funct_2(X0,X0,X1,k6_partfun1(X0)) & ! [X2] : (k3_funct_2(X0,X0,X1,X2) = X2 | ~m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) & ~v1_xboole_0(X0))),
% 0.22/0.55    inference(flattening,[],[f11])).
% 0.22/0.55  fof(f11,plain,(
% 0.22/0.55    ? [X0] : (? [X1] : ((~r2_funct_2(X0,X0,X1,k6_partfun1(X0)) & ! [X2] : (k3_funct_2(X0,X0,X1,X2) = X2 | ~m1_subset_1(X2,X0))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))) & ~v1_xboole_0(X0))),
% 0.22/0.55    inference(ennf_transformation,[],[f10])).
% 0.22/0.55  fof(f10,negated_conjecture,(
% 0.22/0.55    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (! [X2] : (m1_subset_1(X2,X0) => k3_funct_2(X0,X0,X1,X2) = X2) => r2_funct_2(X0,X0,X1,k6_partfun1(X0)))))),
% 0.22/0.55    inference(negated_conjecture,[],[f9])).
% 0.22/0.55  fof(f9,conjecture,(
% 0.22/0.55    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (! [X2] : (m1_subset_1(X2,X0) => k3_funct_2(X0,X0,X1,X2) = X2) => r2_funct_2(X0,X0,X1,k6_partfun1(X0)))))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t201_funct_2)).
% 0.22/0.55  fof(f37,plain,(
% 0.22/0.55    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.22/0.55    inference(cnf_transformation,[],[f26])).
% 0.22/0.55  fof(f36,plain,(
% 0.22/0.55    v1_funct_2(sK1,sK0,sK0)),
% 0.22/0.55    inference(cnf_transformation,[],[f26])).
% 0.22/0.55  fof(f34,plain,(
% 0.22/0.55    ~v1_xboole_0(sK0)),
% 0.22/0.55    inference(cnf_transformation,[],[f26])).
% 0.22/0.55  % (11140)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.55  fof(f59,plain,(
% 0.22/0.55    ( ! [X1] : (sK2(k1_relat_1(X1),X1) != k1_funct_1(X1,sK2(k1_relat_1(X1),X1)) | k6_partfun1(k1_relat_1(X1)) = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.55    inference(equality_resolution,[],[f55])).
% 0.22/0.55  fof(f55,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k6_partfun1(X0) = X1 | sK2(X0,X1) != k1_funct_1(X1,sK2(X0,X1)) | k1_relat_1(X1) != X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.55    inference(definition_unfolding,[],[f48,f40])).
% 0.22/0.55  fof(f48,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k6_relat_1(X0) = X1 | sK2(X0,X1) != k1_funct_1(X1,sK2(X0,X1)) | k1_relat_1(X1) != X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f32])).
% 0.22/0.55  fof(f35,plain,(
% 0.22/0.55    v1_funct_1(sK1)),
% 0.22/0.55    inference(cnf_transformation,[],[f26])).
% 0.22/0.55  fof(f134,plain,(
% 0.22/0.55    ~spl3_4 | spl3_11 | ~spl3_10),
% 0.22/0.55    inference(avatar_split_clause,[],[f128,f124,f131,f81])).
% 0.22/0.55  fof(f81,plain,(
% 0.22/0.55    spl3_4 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.55  fof(f124,plain,(
% 0.22/0.55    spl3_10 <=> sK0 = k1_relset_1(sK0,sK0,sK1)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.55  fof(f128,plain,(
% 0.22/0.55    sK0 = k1_relat_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl3_10),
% 0.22/0.55    inference(superposition,[],[f126,f51])).
% 0.22/0.55  fof(f51,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f19])).
% 0.22/0.55  fof(f19,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(ennf_transformation,[],[f4])).
% 0.22/0.55  fof(f4,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.55  fof(f126,plain,(
% 0.22/0.55    sK0 = k1_relset_1(sK0,sK0,sK1) | ~spl3_10),
% 0.22/0.55    inference(avatar_component_clause,[],[f124])).
% 0.22/0.55  fof(f127,plain,(
% 0.22/0.55    ~spl3_2 | ~spl3_3 | spl3_10 | ~spl3_4),
% 0.22/0.55    inference(avatar_split_clause,[],[f90,f81,f124,f76,f71])).
% 0.22/0.55  fof(f76,plain,(
% 0.22/0.55    spl3_3 <=> v1_funct_2(sK1,sK0,sK0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.55  fof(f90,plain,(
% 0.22/0.55    sK0 = k1_relset_1(sK0,sK0,sK1) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~spl3_4),
% 0.22/0.55    inference(resolution,[],[f83,f49])).
% 0.22/0.55  fof(f49,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | k1_relset_1(X0,X0,X1) = X0 | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f17])).
% 0.22/0.55  fof(f17,plain,(
% 0.22/0.55    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.22/0.55    inference(flattening,[],[f16])).
% 0.22/0.55  fof(f16,plain,(
% 0.22/0.55    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.22/0.55    inference(ennf_transformation,[],[f8])).
% 0.22/0.55  fof(f8,axiom,(
% 0.22/0.55    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).
% 0.22/0.55  fof(f83,plain,(
% 0.22/0.55    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl3_4),
% 0.22/0.55    inference(avatar_component_clause,[],[f81])).
% 0.22/0.55  fof(f122,plain,(
% 0.22/0.55    ~spl3_2 | ~spl3_3 | spl3_9 | ~spl3_4),
% 0.22/0.55    inference(avatar_split_clause,[],[f92,f81,f119,f76,f71])).
% 0.22/0.55  fof(f119,plain,(
% 0.22/0.55    spl3_9 <=> r2_funct_2(sK0,sK0,sK1,sK1)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.55  fof(f92,plain,(
% 0.22/0.55    r2_funct_2(sK0,sK0,sK1,sK1) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~spl3_4),
% 0.22/0.55    inference(resolution,[],[f83,f64])).
% 0.22/0.55  % (11159)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.55  fof(f64,plain,(
% 0.22/0.55    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_funct_2(X0,X1,X3,X3) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.22/0.55    inference(duplicate_literal_removal,[],[f63])).
% 0.22/0.55  fof(f63,plain,(
% 0.22/0.55    ( ! [X0,X3,X1] : (r2_funct_2(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.22/0.55    inference(equality_resolution,[],[f54])).
% 0.22/0.55  fof(f54,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f33])).
% 0.22/0.55  fof(f33,plain,(
% 0.22/0.55    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.55    inference(nnf_transformation,[],[f23])).
% 0.22/0.55  fof(f23,plain,(
% 0.22/0.55    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.55    inference(flattening,[],[f22])).
% 0.22/0.55  fof(f22,plain,(
% 0.22/0.55    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.22/0.55    inference(ennf_transformation,[],[f7])).
% 0.22/0.55  fof(f7,axiom,(
% 0.22/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).
% 0.22/0.55  fof(f99,plain,(
% 0.22/0.55    spl3_6 | ~spl3_4),
% 0.22/0.55    inference(avatar_split_clause,[],[f93,f81,f96])).
% 0.22/0.55  fof(f93,plain,(
% 0.22/0.55    v1_relat_1(sK1) | ~spl3_4),
% 0.22/0.55    inference(resolution,[],[f83,f50])).
% 0.22/0.55  fof(f50,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f18])).
% 0.22/0.55  fof(f18,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(ennf_transformation,[],[f3])).
% 0.22/0.55  fof(f3,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.55  fof(f89,plain,(
% 0.22/0.55    ~spl3_5),
% 0.22/0.55    inference(avatar_split_clause,[],[f39,f86])).
% 0.22/0.55  fof(f86,plain,(
% 0.22/0.55    spl3_5 <=> r2_funct_2(sK0,sK0,sK1,k6_partfun1(sK0))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.55  fof(f39,plain,(
% 0.22/0.55    ~r2_funct_2(sK0,sK0,sK1,k6_partfun1(sK0))),
% 0.22/0.55    inference(cnf_transformation,[],[f26])).
% 0.22/0.55  fof(f84,plain,(
% 0.22/0.55    spl3_4),
% 0.22/0.55    inference(avatar_split_clause,[],[f37,f81])).
% 0.22/0.55  fof(f79,plain,(
% 0.22/0.55    spl3_3),
% 0.22/0.55    inference(avatar_split_clause,[],[f36,f76])).
% 0.22/0.55  fof(f74,plain,(
% 0.22/0.55    spl3_2),
% 0.22/0.55    inference(avatar_split_clause,[],[f35,f71])).
% 0.22/0.55  fof(f69,plain,(
% 0.22/0.55    ~spl3_1),
% 0.22/0.55    inference(avatar_split_clause,[],[f34,f66])).
% 0.22/0.55  % SZS output end Proof for theBenchmark
% 0.22/0.55  % (11150)------------------------------
% 0.22/0.55  % (11150)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (11150)Termination reason: Refutation
% 0.22/0.55  
% 0.22/0.55  % (11150)Memory used [KB]: 10746
% 0.22/0.55  % (11150)Time elapsed: 0.128 s
% 0.22/0.55  % (11150)------------------------------
% 0.22/0.55  % (11150)------------------------------
% 0.22/0.55  % (11139)Success in time 0.187 s
%------------------------------------------------------------------------------
