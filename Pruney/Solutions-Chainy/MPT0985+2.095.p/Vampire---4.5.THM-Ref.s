%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:14 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  167 ( 588 expanded)
%              Number of leaves         :   30 ( 160 expanded)
%              Depth                    :   20
%              Number of atoms          :  566 (3140 expanded)
%              Number of equality atoms :   94 ( 427 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f609,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f112,f121,f134,f142,f444,f471,f589,f599,f607,f608])).

% (20219)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
fof(f608,plain,
    ( ~ spl9_12
    | spl9_2
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f422,f131,f105,f267])).

fof(f267,plain,
    ( spl9_12
  <=> k1_xboole_0 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f105,plain,
    ( spl9_2
  <=> v1_funct_2(k2_funct_1(sK6),sK5,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f131,plain,
    ( spl9_5
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f422,plain,
    ( k1_xboole_0 != sK5
    | spl9_2
    | ~ spl9_5 ),
    inference(superposition,[],[f419,f252])).

fof(f252,plain,(
    sK5 = k2_relat_1(sK6) ),
    inference(subsumption_resolution,[],[f250,f60])).

fof(f60,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
      | ~ v1_funct_2(k2_funct_1(sK6),sK5,sK4)
      | ~ v1_funct_1(k2_funct_1(sK6)) )
    & sK5 = k2_relset_1(sK4,sK5,sK6)
    & v2_funct_1(sK6)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    & v1_funct_2(sK6,sK4,sK5)
    & v1_funct_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f19,f44])).

fof(f44,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
          | ~ v1_funct_1(k2_funct_1(X2)) )
        & k2_relset_1(X0,X1,X2) = X1
        & v2_funct_1(X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ( ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
        | ~ v1_funct_2(k2_funct_1(sK6),sK5,sK4)
        | ~ v1_funct_1(k2_funct_1(sK6)) )
      & sK5 = k2_relset_1(sK4,sK5,sK6)
      & v2_funct_1(sK6)
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
      & v1_funct_2(sK6,sK4,sK5)
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

% (20235)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
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

fof(f250,plain,
    ( sK5 = k2_relat_1(sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(superposition,[],[f83,f62])).

fof(f62,plain,(
    sK5 = k2_relset_1(sK4,sK5,sK6) ),
    inference(cnf_transformation,[],[f45])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f419,plain,
    ( k1_xboole_0 != k2_relat_1(sK6)
    | spl9_2
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f418,f118])).

fof(f118,plain,(
    v1_relat_1(sK6) ),
    inference(resolution,[],[f82,f60])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f418,plain,
    ( k1_xboole_0 != k2_relat_1(sK6)
    | ~ v1_relat_1(sK6)
    | spl9_2
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f417,f58])).

fof(f58,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f45])).

fof(f417,plain,
    ( k1_xboole_0 != k2_relat_1(sK6)
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | spl9_2
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f416,f61])).

fof(f61,plain,(
    v2_funct_1(sK6) ),
    inference(cnf_transformation,[],[f45])).

fof(f416,plain,
    ( k1_xboole_0 != k2_relat_1(sK6)
    | ~ v2_funct_1(sK6)
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | spl9_2
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f412,f173])).

fof(f173,plain,
    ( ! [X0] : sP0(X0,k1_xboole_0)
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f172,f119])).

fof(f119,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f82,f67])).

fof(f67,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f172,plain,
    ( ! [X0] :
        ( sP0(X0,k1_xboole_0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f171,f133])).

fof(f133,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f131])).

fof(f171,plain,(
    ! [X0] :
      ( sP0(X0,k1_xboole_0)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f170,f66])).

fof(f66,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f170,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,X0)
      | sP0(X0,k1_xboole_0)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[],[f78,f65])).

fof(f65,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | sP0(X0,X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_folding,[],[f29,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ sP0(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

fof(f412,plain,
    ( ~ sP0(sK4,k1_xboole_0)
    | k1_xboole_0 != k2_relat_1(sK6)
    | ~ v2_funct_1(sK6)
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | spl9_2 ),
    inference(superposition,[],[f401,f204])).

fof(f204,plain,(
    ! [X6] :
      ( k1_xboole_0 = k2_funct_1(X6)
      | k1_xboole_0 != k2_relat_1(X6)
      | ~ v2_funct_1(X6)
      | ~ v1_funct_1(X6)
      | ~ v1_relat_1(X6) ) ),
    inference(subsumption_resolution,[],[f202,f70])).

fof(f70,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f202,plain,(
    ! [X6] :
      ( k1_xboole_0 != k2_relat_1(X6)
      | k1_xboole_0 = k2_funct_1(X6)
      | ~ v1_relat_1(k2_funct_1(X6))
      | ~ v2_funct_1(X6)
      | ~ v1_funct_1(X6)
      | ~ v1_relat_1(X6) ) ),
    inference(superposition,[],[f68,f72])).

fof(f72,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f68,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f401,plain,
    ( ~ sP0(sK4,k2_funct_1(sK6))
    | spl9_2 ),
    inference(resolution,[],[f400,f107])).

fof(f107,plain,
    ( ~ v1_funct_2(k2_funct_1(sK6),sK5,sK4)
    | spl9_2 ),
    inference(avatar_component_clause,[],[f105])).

fof(f400,plain,(
    ! [X3] :
      ( v1_funct_2(k2_funct_1(sK6),sK5,X3)
      | ~ sP0(X3,k2_funct_1(sK6)) ) ),
    inference(subsumption_resolution,[],[f399,f118])).

fof(f399,plain,(
    ! [X3] :
      ( v1_funct_2(k2_funct_1(sK6),sK5,X3)
      | ~ sP0(X3,k2_funct_1(sK6))
      | ~ v1_relat_1(sK6) ) ),
    inference(subsumption_resolution,[],[f398,f58])).

fof(f398,plain,(
    ! [X3] :
      ( v1_funct_2(k2_funct_1(sK6),sK5,X3)
      | ~ sP0(X3,k2_funct_1(sK6))
      | ~ v1_funct_1(sK6)
      | ~ v1_relat_1(sK6) ) ),
    inference(subsumption_resolution,[],[f390,f61])).

fof(f390,plain,(
    ! [X3] :
      ( v1_funct_2(k2_funct_1(sK6),sK5,X3)
      | ~ sP0(X3,k2_funct_1(sK6))
      | ~ v2_funct_1(sK6)
      | ~ v1_funct_1(sK6)
      | ~ v1_relat_1(sK6) ) ),
    inference(superposition,[],[f203,f252])).

fof(f203,plain,(
    ! [X8,X7] :
      ( v1_funct_2(k2_funct_1(X7),k2_relat_1(X7),X8)
      | ~ sP0(X8,k2_funct_1(X7))
      | ~ v2_funct_1(X7)
      | ~ v1_funct_1(X7)
      | ~ v1_relat_1(X7) ) ),
    inference(superposition,[],[f76,f72])).

fof(f76,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ sP0(X0,X1) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f607,plain,
    ( spl9_12
    | ~ spl9_17 ),
    inference(avatar_split_clause,[],[f472,f441,f267])).

fof(f441,plain,
    ( spl9_17
  <=> sP1(sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).

fof(f472,plain,
    ( k1_xboole_0 = sK5
    | ~ spl9_17 ),
    inference(resolution,[],[f443,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f443,plain,
    ( sP1(sK4,sK5)
    | ~ spl9_17 ),
    inference(avatar_component_clause,[],[f441])).

fof(f599,plain,
    ( ~ spl9_12
    | spl9_3 ),
    inference(avatar_split_clause,[],[f517,f109,f267])).

fof(f109,plain,
    ( spl9_3
  <=> m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f517,plain,
    ( k1_xboole_0 != sK5
    | spl9_3 ),
    inference(superposition,[],[f509,f252])).

fof(f509,plain,
    ( k1_xboole_0 != k2_relat_1(sK6)
    | spl9_3 ),
    inference(subsumption_resolution,[],[f508,f118])).

fof(f508,plain,
    ( k1_xboole_0 != k2_relat_1(sK6)
    | ~ v1_relat_1(sK6)
    | spl9_3 ),
    inference(subsumption_resolution,[],[f507,f58])).

fof(f507,plain,
    ( k1_xboole_0 != k2_relat_1(sK6)
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | spl9_3 ),
    inference(subsumption_resolution,[],[f506,f61])).

fof(f506,plain,
    ( k1_xboole_0 != k2_relat_1(sK6)
    | ~ v2_funct_1(sK6)
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | spl9_3 ),
    inference(subsumption_resolution,[],[f505,f67])).

fof(f505,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
    | k1_xboole_0 != k2_relat_1(sK6)
    | ~ v2_funct_1(sK6)
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | spl9_3 ),
    inference(superposition,[],[f111,f204])).

fof(f111,plain,
    ( ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
    | spl9_3 ),
    inference(avatar_component_clause,[],[f109])).

fof(f589,plain,
    ( spl9_3
    | ~ spl9_16 ),
    inference(avatar_contradiction_clause,[],[f588])).

fof(f588,plain,
    ( $false
    | spl9_3
    | ~ spl9_16 ),
    inference(subsumption_resolution,[],[f578,f488])).

fof(f488,plain,
    ( sP0(sK4,k2_funct_1(sK6))
    | ~ spl9_16 ),
    inference(subsumption_resolution,[],[f487,f118])).

fof(f487,plain,
    ( sP0(sK4,k2_funct_1(sK6))
    | ~ v1_relat_1(sK6)
    | ~ spl9_16 ),
    inference(subsumption_resolution,[],[f486,f58])).

fof(f486,plain,
    ( sP0(sK4,k2_funct_1(sK6))
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | ~ spl9_16 ),
    inference(subsumption_resolution,[],[f484,f61])).

fof(f484,plain,
    ( sP0(sK4,k2_funct_1(sK6))
    | ~ v2_funct_1(sK6)
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | ~ spl9_16 ),
    inference(superposition,[],[f216,f439])).

% (20240)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
fof(f439,plain,
    ( sK4 = k1_relat_1(sK6)
    | ~ spl9_16 ),
    inference(avatar_component_clause,[],[f437])).

fof(f437,plain,
    ( spl9_16
  <=> sK4 = k1_relat_1(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f216,plain,(
    ! [X0] :
      ( sP0(k1_relat_1(X0),k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f215,f70])).

fof(f215,plain,(
    ! [X0] :
      ( sP0(k1_relat_1(X0),k2_funct_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f212,f71])).

fof(f71,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f212,plain,(
    ! [X0] :
      ( sP0(k1_relat_1(X0),k2_funct_1(X0))
      | ~ v1_funct_1(k2_funct_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f169,f73])).

fof(f73,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f169,plain,(
    ! [X0] :
      ( sP0(k2_relat_1(X0),X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f78,f117])).

fof(f117,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f116])).

fof(f116,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f81,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK7(X0,X1),X1)
          & r2_hidden(sK7(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f48,f49])).

fof(f49,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK7(X0,X1),X1)
        & r2_hidden(sK7(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f47])).

fof(f47,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK7(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f578,plain,
    ( ~ sP0(sK4,k2_funct_1(sK6))
    | spl9_3 ),
    inference(resolution,[],[f577,f111])).

fof(f577,plain,(
    ! [X3] :
      ( m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,X3)))
      | ~ sP0(X3,k2_funct_1(sK6)) ) ),
    inference(subsumption_resolution,[],[f576,f118])).

fof(f576,plain,(
    ! [X3] :
      ( m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,X3)))
      | ~ sP0(X3,k2_funct_1(sK6))
      | ~ v1_relat_1(sK6) ) ),
    inference(subsumption_resolution,[],[f575,f58])).

fof(f575,plain,(
    ! [X3] :
      ( m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,X3)))
      | ~ sP0(X3,k2_funct_1(sK6))
      | ~ v1_funct_1(sK6)
      | ~ v1_relat_1(sK6) ) ),
    inference(subsumption_resolution,[],[f570,f61])).

fof(f570,plain,(
    ! [X3] :
      ( m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,X3)))
      | ~ sP0(X3,k2_funct_1(sK6))
      | ~ v2_funct_1(sK6)
      | ~ v1_funct_1(sK6)
      | ~ v1_relat_1(sK6) ) ),
    inference(superposition,[],[f201,f252])).

fof(f201,plain,(
    ! [X4,X5] :
      ( m1_subset_1(k2_funct_1(X4),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X4),X5)))
      | ~ sP0(X5,k2_funct_1(X4))
      | ~ v2_funct_1(X4)
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4) ) ),
    inference(superposition,[],[f77,f72])).

fof(f77,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f471,plain,
    ( spl9_2
    | ~ spl9_16 ),
    inference(avatar_contradiction_clause,[],[f470])).

fof(f470,plain,
    ( $false
    | spl9_2
    | ~ spl9_16 ),
    inference(subsumption_resolution,[],[f469,f118])).

fof(f469,plain,
    ( ~ v1_relat_1(sK6)
    | spl9_2
    | ~ spl9_16 ),
    inference(subsumption_resolution,[],[f468,f58])).

fof(f468,plain,
    ( ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | spl9_2
    | ~ spl9_16 ),
    inference(subsumption_resolution,[],[f467,f61])).

fof(f467,plain,
    ( ~ v2_funct_1(sK6)
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | spl9_2
    | ~ spl9_16 ),
    inference(subsumption_resolution,[],[f457,f401])).

fof(f457,plain,
    ( sP0(sK4,k2_funct_1(sK6))
    | ~ v2_funct_1(sK6)
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | ~ spl9_16 ),
    inference(superposition,[],[f216,f439])).

fof(f444,plain,
    ( spl9_16
    | spl9_17 ),
    inference(avatar_split_clause,[],[f435,f441,f437])).

fof(f435,plain,
    ( sP1(sK4,sK5)
    | sK4 = k1_relat_1(sK6) ),
    inference(subsumption_resolution,[],[f429,f59])).

fof(f59,plain,(
    v1_funct_2(sK6,sK4,sK5) ),
    inference(cnf_transformation,[],[f45])).

fof(f429,plain,
    ( ~ v1_funct_2(sK6,sK4,sK5)
    | sP1(sK4,sK5)
    | sK4 = k1_relat_1(sK6) ),
    inference(resolution,[],[f315,f60])).

fof(f315,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_2(X5,X3,X4)
      | sP1(X3,X4)
      | k1_relat_1(X5) = X3 ) ),
    inference(subsumption_resolution,[],[f313,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP2(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X2,X1,X0)
        & sP2(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f35,f42,f41,f40])).

fof(f41,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | sP1(X0,X1)
      | ~ sP2(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_xboole_0 = X2 )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP3(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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

fof(f313,plain,(
    ! [X4,X5,X3] :
      ( k1_relat_1(X5) = X3
      | ~ v1_funct_2(X5,X3,X4)
      | sP1(X3,X4)
      | ~ sP2(X3,X5,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(superposition,[],[f87,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X2,X1) = X0
      | ~ v1_funct_2(X1,X0,X2)
      | sP1(X0,X2)
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | sP1(X0,X2)
      | ~ sP2(X0,X1,X2) ) ),
    inference(rectify,[],[f53])).

fof(f53,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | sP1(X0,X1)
      | ~ sP2(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f142,plain,(
    ~ spl9_4 ),
    inference(avatar_contradiction_clause,[],[f141])).

% (20230)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
fof(f141,plain,
    ( $false
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f136,f94])).

fof(f94,plain,(
    v1_relat_1(sK8) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,
    ( v1_funct_1(sK8)
    & v1_relat_1(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f9,f56])).

fof(f56,plain,
    ( ? [X0] :
        ( v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( v1_funct_1(sK8)
      & v1_relat_1(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f9,axiom,(
    ? [X0] :
      ( v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_funct_1)).

% (20233)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
fof(f136,plain,
    ( ~ v1_relat_1(sK8)
    | ~ spl9_4 ),
    inference(resolution,[],[f129,f95])).

fof(f95,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f57])).

fof(f129,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl9_4
  <=> ! [X0] :
        ( ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f134,plain,
    ( spl9_4
    | spl9_5 ),
    inference(avatar_split_clause,[],[f126,f131,f128])).

fof(f126,plain,(
    ! [X0] :
      ( v1_funct_1(k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f74,f67])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_funct_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_funct_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_funct_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_funct_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_funct_1)).

fof(f121,plain,(
    spl9_1 ),
    inference(avatar_contradiction_clause,[],[f120])).

fof(f120,plain,
    ( $false
    | spl9_1 ),
    inference(subsumption_resolution,[],[f118,f114])).

fof(f114,plain,
    ( ~ v1_relat_1(sK6)
    | spl9_1 ),
    inference(subsumption_resolution,[],[f113,f58])).

fof(f113,plain,
    ( ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | spl9_1 ),
    inference(resolution,[],[f71,f103])).

fof(f103,plain,
    ( ~ v1_funct_1(k2_funct_1(sK6))
    | spl9_1 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl9_1
  <=> v1_funct_1(k2_funct_1(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f112,plain,
    ( ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3 ),
    inference(avatar_split_clause,[],[f63,f109,f105,f101])).

fof(f63,plain,
    ( ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
    | ~ v1_funct_2(k2_funct_1(sK6),sK5,sK4)
    | ~ v1_funct_1(k2_funct_1(sK6)) ),
    inference(cnf_transformation,[],[f45])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:27:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.52  % (20239)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.53  % (20231)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (20220)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (20222)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (20247)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (20224)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (20225)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.55  % (20223)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.55  % (20237)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (20237)Refutation not found, incomplete strategy% (20237)------------------------------
% 0.21/0.55  % (20237)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (20237)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (20237)Memory used [KB]: 10746
% 0.21/0.55  % (20237)Time elapsed: 0.126 s
% 0.21/0.55  % (20237)------------------------------
% 0.21/0.55  % (20237)------------------------------
% 0.21/0.55  % (20228)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.55  % (20246)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.55  % (20249)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.55  % (20245)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.55  % (20236)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.56  % (20241)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.56  % (20238)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.56  % (20232)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.56  % (20247)Refutation found. Thanks to Tanya!
% 0.21/0.56  % SZS status Theorem for theBenchmark
% 0.21/0.56  % SZS output start Proof for theBenchmark
% 0.21/0.56  fof(f609,plain,(
% 0.21/0.56    $false),
% 0.21/0.56    inference(avatar_sat_refutation,[],[f112,f121,f134,f142,f444,f471,f589,f599,f607,f608])).
% 0.21/0.56  % (20219)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.56  fof(f608,plain,(
% 0.21/0.56    ~spl9_12 | spl9_2 | ~spl9_5),
% 0.21/0.56    inference(avatar_split_clause,[],[f422,f131,f105,f267])).
% 0.21/0.56  fof(f267,plain,(
% 0.21/0.56    spl9_12 <=> k1_xboole_0 = sK5),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).
% 0.21/0.56  fof(f105,plain,(
% 0.21/0.56    spl9_2 <=> v1_funct_2(k2_funct_1(sK6),sK5,sK4)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 0.21/0.56  fof(f131,plain,(
% 0.21/0.56    spl9_5 <=> v1_funct_1(k1_xboole_0)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 0.21/0.56  fof(f422,plain,(
% 0.21/0.56    k1_xboole_0 != sK5 | (spl9_2 | ~spl9_5)),
% 0.21/0.56    inference(superposition,[],[f419,f252])).
% 0.21/0.56  fof(f252,plain,(
% 0.21/0.56    sK5 = k2_relat_1(sK6)),
% 0.21/0.56    inference(subsumption_resolution,[],[f250,f60])).
% 0.21/0.56  fof(f60,plain,(
% 0.21/0.56    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))),
% 0.21/0.56    inference(cnf_transformation,[],[f45])).
% 0.21/0.56  fof(f45,plain,(
% 0.21/0.56    (~m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(k2_funct_1(sK6),sK5,sK4) | ~v1_funct_1(k2_funct_1(sK6))) & sK5 = k2_relset_1(sK4,sK5,sK6) & v2_funct_1(sK6) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK6,sK4,sK5) & v1_funct_1(sK6)),
% 0.21/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f19,f44])).
% 0.21/0.56  fof(f44,plain,(
% 0.21/0.56    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(k2_funct_1(sK6),sK5,sK4) | ~v1_funct_1(k2_funct_1(sK6))) & sK5 = k2_relset_1(sK4,sK5,sK6) & v2_funct_1(sK6) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK6,sK4,sK5) & v1_funct_1(sK6))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  % (20235)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.56  fof(f19,plain,(
% 0.21/0.56    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.21/0.56    inference(flattening,[],[f18])).
% 0.21/0.56  fof(f18,plain,(
% 0.21/0.56    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.21/0.56    inference(ennf_transformation,[],[f17])).
% 0.21/0.56  fof(f17,negated_conjecture,(
% 0.21/0.56    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.21/0.56    inference(negated_conjecture,[],[f16])).
% 0.21/0.56  fof(f16,conjecture,(
% 0.21/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 0.21/0.56  fof(f250,plain,(
% 0.21/0.56    sK5 = k2_relat_1(sK6) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))),
% 0.21/0.56    inference(superposition,[],[f83,f62])).
% 0.21/0.56  fof(f62,plain,(
% 0.21/0.56    sK5 = k2_relset_1(sK4,sK5,sK6)),
% 0.21/0.56    inference(cnf_transformation,[],[f45])).
% 0.21/0.56  fof(f83,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f32])).
% 0.21/0.56  fof(f32,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.56    inference(ennf_transformation,[],[f13])).
% 0.21/0.56  fof(f13,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.56  fof(f419,plain,(
% 0.21/0.56    k1_xboole_0 != k2_relat_1(sK6) | (spl9_2 | ~spl9_5)),
% 0.21/0.56    inference(subsumption_resolution,[],[f418,f118])).
% 0.21/0.56  fof(f118,plain,(
% 0.21/0.56    v1_relat_1(sK6)),
% 0.21/0.56    inference(resolution,[],[f82,f60])).
% 0.21/0.56  fof(f82,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f31])).
% 0.21/0.56  fof(f31,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.56    inference(ennf_transformation,[],[f11])).
% 0.21/0.56  fof(f11,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.56  fof(f418,plain,(
% 0.21/0.56    k1_xboole_0 != k2_relat_1(sK6) | ~v1_relat_1(sK6) | (spl9_2 | ~spl9_5)),
% 0.21/0.56    inference(subsumption_resolution,[],[f417,f58])).
% 0.21/0.56  fof(f58,plain,(
% 0.21/0.56    v1_funct_1(sK6)),
% 0.21/0.56    inference(cnf_transformation,[],[f45])).
% 0.21/0.56  fof(f417,plain,(
% 0.21/0.56    k1_xboole_0 != k2_relat_1(sK6) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | (spl9_2 | ~spl9_5)),
% 0.21/0.56    inference(subsumption_resolution,[],[f416,f61])).
% 0.21/0.56  fof(f61,plain,(
% 0.21/0.56    v2_funct_1(sK6)),
% 0.21/0.56    inference(cnf_transformation,[],[f45])).
% 0.21/0.56  fof(f416,plain,(
% 0.21/0.56    k1_xboole_0 != k2_relat_1(sK6) | ~v2_funct_1(sK6) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | (spl9_2 | ~spl9_5)),
% 0.21/0.56    inference(subsumption_resolution,[],[f412,f173])).
% 0.21/0.56  fof(f173,plain,(
% 0.21/0.56    ( ! [X0] : (sP0(X0,k1_xboole_0)) ) | ~spl9_5),
% 0.21/0.56    inference(subsumption_resolution,[],[f172,f119])).
% 0.21/0.56  fof(f119,plain,(
% 0.21/0.56    v1_relat_1(k1_xboole_0)),
% 0.21/0.56    inference(resolution,[],[f82,f67])).
% 0.21/0.56  fof(f67,plain,(
% 0.21/0.56    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f3])).
% 0.21/0.56  fof(f3,axiom,(
% 0.21/0.56    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.56  fof(f172,plain,(
% 0.21/0.56    ( ! [X0] : (sP0(X0,k1_xboole_0) | ~v1_relat_1(k1_xboole_0)) ) | ~spl9_5),
% 0.21/0.56    inference(subsumption_resolution,[],[f171,f133])).
% 0.21/0.56  fof(f133,plain,(
% 0.21/0.56    v1_funct_1(k1_xboole_0) | ~spl9_5),
% 0.21/0.56    inference(avatar_component_clause,[],[f131])).
% 0.21/0.56  fof(f171,plain,(
% 0.21/0.56    ( ! [X0] : (sP0(X0,k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f170,f66])).
% 0.21/0.56  fof(f66,plain,(
% 0.21/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f2])).
% 0.21/0.56  fof(f2,axiom,(
% 0.21/0.56    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.56  fof(f170,plain,(
% 0.21/0.56    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | sP0(X0,k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)) )),
% 0.21/0.56    inference(superposition,[],[f78,f65])).
% 0.21/0.56  fof(f65,plain,(
% 0.21/0.56    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.56    inference(cnf_transformation,[],[f5])).
% 0.21/0.56  fof(f5,axiom,(
% 0.21/0.56    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.56  fof(f78,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | sP0(X0,X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f39])).
% 0.21/0.56  fof(f39,plain,(
% 0.21/0.56    ! [X0,X1] : (sP0(X0,X1) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.56    inference(definition_folding,[],[f29,f38])).
% 0.21/0.56  fof(f38,plain,(
% 0.21/0.56    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~sP0(X0,X1))),
% 0.21/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.56  fof(f29,plain,(
% 0.21/0.56    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.56    inference(flattening,[],[f28])).
% 0.21/0.56  fof(f28,plain,(
% 0.21/0.56    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.56    inference(ennf_transformation,[],[f15])).
% 0.21/0.56  fof(f15,axiom,(
% 0.21/0.56    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).
% 0.21/0.56  fof(f412,plain,(
% 0.21/0.56    ~sP0(sK4,k1_xboole_0) | k1_xboole_0 != k2_relat_1(sK6) | ~v2_funct_1(sK6) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | spl9_2),
% 0.21/0.56    inference(superposition,[],[f401,f204])).
% 0.21/0.56  fof(f204,plain,(
% 0.21/0.56    ( ! [X6] : (k1_xboole_0 = k2_funct_1(X6) | k1_xboole_0 != k2_relat_1(X6) | ~v2_funct_1(X6) | ~v1_funct_1(X6) | ~v1_relat_1(X6)) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f202,f70])).
% 0.21/0.56  fof(f70,plain,(
% 0.21/0.56    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f23])).
% 0.21/0.56  fof(f23,plain,(
% 0.21/0.56    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.56    inference(flattening,[],[f22])).
% 0.21/0.56  fof(f22,plain,(
% 0.21/0.56    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f8])).
% 0.21/0.56  fof(f8,axiom,(
% 0.21/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.21/0.56  fof(f202,plain,(
% 0.21/0.56    ( ! [X6] : (k1_xboole_0 != k2_relat_1(X6) | k1_xboole_0 = k2_funct_1(X6) | ~v1_relat_1(k2_funct_1(X6)) | ~v2_funct_1(X6) | ~v1_funct_1(X6) | ~v1_relat_1(X6)) )),
% 0.21/0.56    inference(superposition,[],[f68,f72])).
% 0.21/0.56  fof(f72,plain,(
% 0.21/0.56    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f25])).
% 0.21/0.56  fof(f25,plain,(
% 0.21/0.56    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.56    inference(flattening,[],[f24])).
% 0.21/0.56  fof(f24,plain,(
% 0.21/0.56    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f10])).
% 0.21/0.56  fof(f10,axiom,(
% 0.21/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 0.21/0.56  fof(f68,plain,(
% 0.21/0.56    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f21])).
% 0.21/0.56  fof(f21,plain,(
% 0.21/0.56    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.56    inference(flattening,[],[f20])).
% 0.21/0.56  fof(f20,plain,(
% 0.21/0.56    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f6])).
% 0.21/0.56  fof(f6,axiom,(
% 0.21/0.56    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 0.21/0.56  fof(f401,plain,(
% 0.21/0.56    ~sP0(sK4,k2_funct_1(sK6)) | spl9_2),
% 0.21/0.56    inference(resolution,[],[f400,f107])).
% 0.21/0.56  fof(f107,plain,(
% 0.21/0.56    ~v1_funct_2(k2_funct_1(sK6),sK5,sK4) | spl9_2),
% 0.21/0.56    inference(avatar_component_clause,[],[f105])).
% 0.21/0.56  fof(f400,plain,(
% 0.21/0.56    ( ! [X3] : (v1_funct_2(k2_funct_1(sK6),sK5,X3) | ~sP0(X3,k2_funct_1(sK6))) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f399,f118])).
% 0.21/0.56  fof(f399,plain,(
% 0.21/0.56    ( ! [X3] : (v1_funct_2(k2_funct_1(sK6),sK5,X3) | ~sP0(X3,k2_funct_1(sK6)) | ~v1_relat_1(sK6)) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f398,f58])).
% 0.21/0.56  fof(f398,plain,(
% 0.21/0.56    ( ! [X3] : (v1_funct_2(k2_funct_1(sK6),sK5,X3) | ~sP0(X3,k2_funct_1(sK6)) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6)) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f390,f61])).
% 0.21/0.56  fof(f390,plain,(
% 0.21/0.56    ( ! [X3] : (v1_funct_2(k2_funct_1(sK6),sK5,X3) | ~sP0(X3,k2_funct_1(sK6)) | ~v2_funct_1(sK6) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6)) )),
% 0.21/0.56    inference(superposition,[],[f203,f252])).
% 0.21/0.56  fof(f203,plain,(
% 0.21/0.56    ( ! [X8,X7] : (v1_funct_2(k2_funct_1(X7),k2_relat_1(X7),X8) | ~sP0(X8,k2_funct_1(X7)) | ~v2_funct_1(X7) | ~v1_funct_1(X7) | ~v1_relat_1(X7)) )),
% 0.21/0.56    inference(superposition,[],[f76,f72])).
% 0.21/0.56  fof(f76,plain,(
% 0.21/0.56    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~sP0(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f46])).
% 0.21/0.56  fof(f46,plain,(
% 0.21/0.56    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~sP0(X0,X1))),
% 0.21/0.56    inference(nnf_transformation,[],[f38])).
% 0.21/0.56  fof(f607,plain,(
% 0.21/0.56    spl9_12 | ~spl9_17),
% 0.21/0.56    inference(avatar_split_clause,[],[f472,f441,f267])).
% 0.21/0.56  fof(f441,plain,(
% 0.21/0.56    spl9_17 <=> sP1(sK4,sK5)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).
% 0.21/0.56  fof(f472,plain,(
% 0.21/0.56    k1_xboole_0 = sK5 | ~spl9_17),
% 0.21/0.56    inference(resolution,[],[f443,f89])).
% 0.21/0.56  fof(f89,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~sP1(X0,X1) | k1_xboole_0 = X1) )),
% 0.21/0.56    inference(cnf_transformation,[],[f55])).
% 0.21/0.56  fof(f55,plain,(
% 0.21/0.56    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP1(X0,X1))),
% 0.21/0.56    inference(nnf_transformation,[],[f40])).
% 0.21/0.56  fof(f40,plain,(
% 0.21/0.56    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP1(X0,X1))),
% 0.21/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.56  fof(f443,plain,(
% 0.21/0.56    sP1(sK4,sK5) | ~spl9_17),
% 0.21/0.56    inference(avatar_component_clause,[],[f441])).
% 0.21/0.56  fof(f599,plain,(
% 0.21/0.56    ~spl9_12 | spl9_3),
% 0.21/0.56    inference(avatar_split_clause,[],[f517,f109,f267])).
% 0.21/0.56  fof(f109,plain,(
% 0.21/0.56    spl9_3 <=> m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 0.21/0.56  fof(f517,plain,(
% 0.21/0.56    k1_xboole_0 != sK5 | spl9_3),
% 0.21/0.56    inference(superposition,[],[f509,f252])).
% 0.21/0.56  fof(f509,plain,(
% 0.21/0.56    k1_xboole_0 != k2_relat_1(sK6) | spl9_3),
% 0.21/0.56    inference(subsumption_resolution,[],[f508,f118])).
% 0.21/0.56  fof(f508,plain,(
% 0.21/0.56    k1_xboole_0 != k2_relat_1(sK6) | ~v1_relat_1(sK6) | spl9_3),
% 0.21/0.56    inference(subsumption_resolution,[],[f507,f58])).
% 0.21/0.56  fof(f507,plain,(
% 0.21/0.56    k1_xboole_0 != k2_relat_1(sK6) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | spl9_3),
% 0.21/0.56    inference(subsumption_resolution,[],[f506,f61])).
% 0.21/0.56  fof(f506,plain,(
% 0.21/0.56    k1_xboole_0 != k2_relat_1(sK6) | ~v2_funct_1(sK6) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | spl9_3),
% 0.21/0.56    inference(subsumption_resolution,[],[f505,f67])).
% 0.21/0.56  fof(f505,plain,(
% 0.21/0.56    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | k1_xboole_0 != k2_relat_1(sK6) | ~v2_funct_1(sK6) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | spl9_3),
% 0.21/0.56    inference(superposition,[],[f111,f204])).
% 0.21/0.56  fof(f111,plain,(
% 0.21/0.56    ~m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | spl9_3),
% 0.21/0.56    inference(avatar_component_clause,[],[f109])).
% 0.21/0.56  fof(f589,plain,(
% 0.21/0.56    spl9_3 | ~spl9_16),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f588])).
% 0.21/0.56  fof(f588,plain,(
% 0.21/0.56    $false | (spl9_3 | ~spl9_16)),
% 0.21/0.56    inference(subsumption_resolution,[],[f578,f488])).
% 0.21/0.56  fof(f488,plain,(
% 0.21/0.56    sP0(sK4,k2_funct_1(sK6)) | ~spl9_16),
% 0.21/0.56    inference(subsumption_resolution,[],[f487,f118])).
% 0.21/0.56  fof(f487,plain,(
% 0.21/0.56    sP0(sK4,k2_funct_1(sK6)) | ~v1_relat_1(sK6) | ~spl9_16),
% 0.21/0.56    inference(subsumption_resolution,[],[f486,f58])).
% 0.21/0.56  fof(f486,plain,(
% 0.21/0.56    sP0(sK4,k2_funct_1(sK6)) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | ~spl9_16),
% 0.21/0.56    inference(subsumption_resolution,[],[f484,f61])).
% 0.21/0.56  fof(f484,plain,(
% 0.21/0.56    sP0(sK4,k2_funct_1(sK6)) | ~v2_funct_1(sK6) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | ~spl9_16),
% 0.21/0.56    inference(superposition,[],[f216,f439])).
% 0.21/0.56  % (20240)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.56  fof(f439,plain,(
% 0.21/0.56    sK4 = k1_relat_1(sK6) | ~spl9_16),
% 0.21/0.56    inference(avatar_component_clause,[],[f437])).
% 0.21/0.56  fof(f437,plain,(
% 0.21/0.56    spl9_16 <=> sK4 = k1_relat_1(sK6)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).
% 0.21/0.56  fof(f216,plain,(
% 0.21/0.56    ( ! [X0] : (sP0(k1_relat_1(X0),k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f215,f70])).
% 0.21/0.56  fof(f215,plain,(
% 0.21/0.56    ( ! [X0] : (sP0(k1_relat_1(X0),k2_funct_1(X0)) | ~v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f212,f71])).
% 0.21/0.56  fof(f71,plain,(
% 0.21/0.56    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f23])).
% 0.21/0.56  fof(f212,plain,(
% 0.21/0.56    ( ! [X0] : (sP0(k1_relat_1(X0),k2_funct_1(X0)) | ~v1_funct_1(k2_funct_1(X0)) | ~v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.56    inference(superposition,[],[f169,f73])).
% 0.21/0.56  fof(f73,plain,(
% 0.21/0.56    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f25])).
% 0.21/0.56  fof(f169,plain,(
% 0.21/0.56    ( ! [X0] : (sP0(k2_relat_1(X0),X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.56    inference(resolution,[],[f78,f117])).
% 0.21/0.56  fof(f117,plain,(
% 0.21/0.56    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.21/0.56    inference(duplicate_literal_removal,[],[f116])).
% 0.21/0.56  fof(f116,plain,(
% 0.21/0.56    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 0.21/0.56    inference(resolution,[],[f81,f80])).
% 0.21/0.56  fof(f80,plain,(
% 0.21/0.56    ( ! [X0,X1] : (r2_hidden(sK7(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f50])).
% 0.21/0.56  fof(f50,plain,(
% 0.21/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f48,f49])).
% 0.21/0.56  fof(f49,plain,(
% 0.21/0.56    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0)))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f48,plain,(
% 0.21/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.56    inference(rectify,[],[f47])).
% 0.21/0.56  fof(f47,plain,(
% 0.21/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.56    inference(nnf_transformation,[],[f30])).
% 0.21/0.56  fof(f30,plain,(
% 0.21/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f1])).
% 0.21/0.56  fof(f1,axiom,(
% 0.21/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.56  fof(f81,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r2_hidden(sK7(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f50])).
% 0.21/0.56  fof(f578,plain,(
% 0.21/0.56    ~sP0(sK4,k2_funct_1(sK6)) | spl9_3),
% 0.21/0.56    inference(resolution,[],[f577,f111])).
% 0.21/0.56  fof(f577,plain,(
% 0.21/0.56    ( ! [X3] : (m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,X3))) | ~sP0(X3,k2_funct_1(sK6))) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f576,f118])).
% 0.21/0.56  fof(f576,plain,(
% 0.21/0.56    ( ! [X3] : (m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,X3))) | ~sP0(X3,k2_funct_1(sK6)) | ~v1_relat_1(sK6)) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f575,f58])).
% 0.21/0.56  fof(f575,plain,(
% 0.21/0.56    ( ! [X3] : (m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,X3))) | ~sP0(X3,k2_funct_1(sK6)) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6)) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f570,f61])).
% 0.21/0.56  fof(f570,plain,(
% 0.21/0.56    ( ! [X3] : (m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,X3))) | ~sP0(X3,k2_funct_1(sK6)) | ~v2_funct_1(sK6) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6)) )),
% 0.21/0.56    inference(superposition,[],[f201,f252])).
% 0.21/0.56  fof(f201,plain,(
% 0.21/0.56    ( ! [X4,X5] : (m1_subset_1(k2_funct_1(X4),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X4),X5))) | ~sP0(X5,k2_funct_1(X4)) | ~v2_funct_1(X4) | ~v1_funct_1(X4) | ~v1_relat_1(X4)) )),
% 0.21/0.56    inference(superposition,[],[f77,f72])).
% 0.21/0.56  fof(f77,plain,(
% 0.21/0.56    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~sP0(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f46])).
% 0.21/0.56  fof(f471,plain,(
% 0.21/0.56    spl9_2 | ~spl9_16),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f470])).
% 0.21/0.56  fof(f470,plain,(
% 0.21/0.56    $false | (spl9_2 | ~spl9_16)),
% 0.21/0.56    inference(subsumption_resolution,[],[f469,f118])).
% 0.21/0.56  fof(f469,plain,(
% 0.21/0.56    ~v1_relat_1(sK6) | (spl9_2 | ~spl9_16)),
% 0.21/0.56    inference(subsumption_resolution,[],[f468,f58])).
% 0.21/0.56  fof(f468,plain,(
% 0.21/0.56    ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | (spl9_2 | ~spl9_16)),
% 0.21/0.56    inference(subsumption_resolution,[],[f467,f61])).
% 0.21/0.56  fof(f467,plain,(
% 0.21/0.56    ~v2_funct_1(sK6) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | (spl9_2 | ~spl9_16)),
% 0.21/0.56    inference(subsumption_resolution,[],[f457,f401])).
% 0.21/0.56  fof(f457,plain,(
% 0.21/0.56    sP0(sK4,k2_funct_1(sK6)) | ~v2_funct_1(sK6) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | ~spl9_16),
% 0.21/0.56    inference(superposition,[],[f216,f439])).
% 0.21/0.56  fof(f444,plain,(
% 0.21/0.56    spl9_16 | spl9_17),
% 0.21/0.56    inference(avatar_split_clause,[],[f435,f441,f437])).
% 0.21/0.56  fof(f435,plain,(
% 0.21/0.56    sP1(sK4,sK5) | sK4 = k1_relat_1(sK6)),
% 0.21/0.56    inference(subsumption_resolution,[],[f429,f59])).
% 0.21/0.56  fof(f59,plain,(
% 0.21/0.56    v1_funct_2(sK6,sK4,sK5)),
% 0.21/0.56    inference(cnf_transformation,[],[f45])).
% 0.21/0.56  fof(f429,plain,(
% 0.21/0.56    ~v1_funct_2(sK6,sK4,sK5) | sP1(sK4,sK5) | sK4 = k1_relat_1(sK6)),
% 0.21/0.56    inference(resolution,[],[f315,f60])).
% 0.21/0.56  fof(f315,plain,(
% 0.21/0.56    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_2(X5,X3,X4) | sP1(X3,X4) | k1_relat_1(X5) = X3) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f313,f91])).
% 0.21/0.56  fof(f91,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP2(X0,X2,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f43])).
% 0.21/0.56  fof(f43,plain,(
% 0.21/0.56    ! [X0,X1,X2] : ((sP3(X2,X1,X0) & sP2(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.56    inference(definition_folding,[],[f35,f42,f41,f40])).
% 0.21/0.56  fof(f41,plain,(
% 0.21/0.56    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | sP1(X0,X1) | ~sP2(X0,X2,X1))),
% 0.21/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.21/0.56  fof(f42,plain,(
% 0.21/0.56    ! [X2,X1,X0] : ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~sP3(X2,X1,X0))),
% 0.21/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.21/0.56  fof(f35,plain,(
% 0.21/0.56    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.56    inference(flattening,[],[f34])).
% 0.21/0.56  fof(f34,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.56    inference(ennf_transformation,[],[f14])).
% 0.21/0.56  fof(f14,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.56  fof(f313,plain,(
% 0.21/0.56    ( ! [X4,X5,X3] : (k1_relat_1(X5) = X3 | ~v1_funct_2(X5,X3,X4) | sP1(X3,X4) | ~sP2(X3,X5,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 0.21/0.56    inference(superposition,[],[f87,f84])).
% 0.21/0.56  fof(f84,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f33])).
% 0.21/0.56  fof(f33,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.56    inference(ennf_transformation,[],[f12])).
% 0.21/0.56  fof(f12,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.56  fof(f87,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2) | sP1(X0,X2) | ~sP2(X0,X1,X2)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f54])).
% 0.21/0.56  fof(f54,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | sP1(X0,X2) | ~sP2(X0,X1,X2))),
% 0.21/0.56    inference(rectify,[],[f53])).
% 0.21/0.56  fof(f53,plain,(
% 0.21/0.56    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | sP1(X0,X1) | ~sP2(X0,X2,X1))),
% 0.21/0.56    inference(nnf_transformation,[],[f41])).
% 0.21/0.56  fof(f142,plain,(
% 0.21/0.56    ~spl9_4),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f141])).
% 0.21/0.56  % (20230)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.56  fof(f141,plain,(
% 0.21/0.56    $false | ~spl9_4),
% 0.21/0.56    inference(subsumption_resolution,[],[f136,f94])).
% 0.21/0.56  fof(f94,plain,(
% 0.21/0.56    v1_relat_1(sK8)),
% 0.21/0.56    inference(cnf_transformation,[],[f57])).
% 0.21/0.56  fof(f57,plain,(
% 0.21/0.56    v1_funct_1(sK8) & v1_relat_1(sK8)),
% 0.21/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f9,f56])).
% 0.21/0.56  fof(f56,plain,(
% 0.21/0.56    ? [X0] : (v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(sK8) & v1_relat_1(sK8))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f9,axiom,(
% 0.21/0.56    ? [X0] : (v1_funct_1(X0) & v1_relat_1(X0))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_funct_1)).
% 0.21/0.56  % (20233)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.56  fof(f136,plain,(
% 0.21/0.56    ~v1_relat_1(sK8) | ~spl9_4),
% 0.21/0.56    inference(resolution,[],[f129,f95])).
% 0.21/0.56  fof(f95,plain,(
% 0.21/0.56    v1_funct_1(sK8)),
% 0.21/0.56    inference(cnf_transformation,[],[f57])).
% 0.21/0.56  fof(f129,plain,(
% 0.21/0.56    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl9_4),
% 0.21/0.56    inference(avatar_component_clause,[],[f128])).
% 0.21/0.56  fof(f128,plain,(
% 0.21/0.56    spl9_4 <=> ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 0.21/0.56  fof(f134,plain,(
% 0.21/0.56    spl9_4 | spl9_5),
% 0.21/0.56    inference(avatar_split_clause,[],[f126,f131,f128])).
% 0.21/0.56  fof(f126,plain,(
% 0.21/0.56    ( ! [X0] : (v1_funct_1(k1_xboole_0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.56    inference(resolution,[],[f74,f67])).
% 0.21/0.56  fof(f74,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_funct_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f27])).
% 0.21/0.56  fof(f27,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.56    inference(flattening,[],[f26])).
% 0.21/0.56  fof(f26,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f7])).
% 0.21/0.56  fof(f7,axiom,(
% 0.21/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_funct_1(X1)))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_funct_1)).
% 0.21/0.56  fof(f121,plain,(
% 0.21/0.56    spl9_1),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f120])).
% 0.21/0.56  fof(f120,plain,(
% 0.21/0.56    $false | spl9_1),
% 0.21/0.56    inference(subsumption_resolution,[],[f118,f114])).
% 0.21/0.56  fof(f114,plain,(
% 0.21/0.56    ~v1_relat_1(sK6) | spl9_1),
% 0.21/0.56    inference(subsumption_resolution,[],[f113,f58])).
% 0.21/0.56  fof(f113,plain,(
% 0.21/0.56    ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | spl9_1),
% 0.21/0.56    inference(resolution,[],[f71,f103])).
% 0.21/0.56  fof(f103,plain,(
% 0.21/0.56    ~v1_funct_1(k2_funct_1(sK6)) | spl9_1),
% 0.21/0.56    inference(avatar_component_clause,[],[f101])).
% 0.21/0.56  fof(f101,plain,(
% 0.21/0.56    spl9_1 <=> v1_funct_1(k2_funct_1(sK6))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.21/0.56  fof(f112,plain,(
% 0.21/0.56    ~spl9_1 | ~spl9_2 | ~spl9_3),
% 0.21/0.56    inference(avatar_split_clause,[],[f63,f109,f105,f101])).
% 0.21/0.56  fof(f63,plain,(
% 0.21/0.56    ~m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(k2_funct_1(sK6),sK5,sK4) | ~v1_funct_1(k2_funct_1(sK6))),
% 0.21/0.56    inference(cnf_transformation,[],[f45])).
% 0.21/0.56  % SZS output end Proof for theBenchmark
% 0.21/0.56  % (20247)------------------------------
% 0.21/0.56  % (20247)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (20247)Termination reason: Refutation
% 0.21/0.56  
% 0.21/0.56  % (20247)Memory used [KB]: 6524
% 0.21/0.56  % (20247)Time elapsed: 0.139 s
% 0.21/0.56  % (20247)------------------------------
% 0.21/0.56  % (20247)------------------------------
% 0.21/0.57  % (20217)Success in time 0.2 s
%------------------------------------------------------------------------------
