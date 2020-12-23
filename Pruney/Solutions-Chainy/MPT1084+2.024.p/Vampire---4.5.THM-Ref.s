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
% DateTime   : Thu Dec  3 13:08:22 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 299 expanded)
%              Number of leaves         :   17 (  96 expanded)
%              Depth                    :   15
%              Number of atoms          :  380 (1852 expanded)
%              Number of equality atoms :   91 ( 341 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f133,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f82,f92,f106,f114,f132])).

fof(f132,plain,
    ( ~ spl3_3
    | spl3_5 ),
    inference(avatar_contradiction_clause,[],[f131])).

fof(f131,plain,
    ( $false
    | ~ spl3_3
    | spl3_5 ),
    inference(subsumption_resolution,[],[f130,f33])).

fof(f33,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ~ r2_funct_2(sK0,sK0,sK1,k6_partfun1(sK0))
    & ! [X2] :
        ( k3_funct_2(sK0,sK0,sK1,X2) = X2
        | ~ m1_subset_1(X2,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f26,f25])).

fof(f25,plain,
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

fof(f26,plain,
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

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

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
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
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

fof(f130,plain,
    ( v1_xboole_0(sK0)
    | ~ spl3_3
    | spl3_5 ),
    inference(subsumption_resolution,[],[f129,f34])).

fof(f34,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f129,plain,
    ( ~ v1_funct_1(sK1)
    | v1_xboole_0(sK0)
    | ~ spl3_3
    | spl3_5 ),
    inference(subsumption_resolution,[],[f128,f35])).

fof(f35,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f128,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | v1_xboole_0(sK0)
    | ~ spl3_3
    | spl3_5 ),
    inference(subsumption_resolution,[],[f127,f36])).

fof(f36,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f127,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | v1_xboole_0(sK0)
    | ~ spl3_3
    | spl3_5 ),
    inference(subsumption_resolution,[],[f126,f81])).

fof(f81,plain,
    ( m1_subset_1(sK2(sK0,sK1),sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl3_3
  <=> m1_subset_1(sK2(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f126,plain,
    ( ~ m1_subset_1(sK2(sK0,sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | v1_xboole_0(sK0)
    | ~ spl3_3
    | spl3_5 ),
    inference(subsumption_resolution,[],[f118,f113])).

% (30485)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
fof(f113,plain,
    ( sK2(sK0,sK1) != k1_funct_1(sK1,sK2(sK0,sK1))
    | spl3_5 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl3_5
  <=> sK2(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f118,plain,
    ( sK2(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1))
    | ~ m1_subset_1(sK2(sK0,sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | v1_xboole_0(sK0)
    | ~ spl3_3 ),
    inference(superposition,[],[f49,f115])).

fof(f115,plain,
    ( sK2(sK0,sK1) = k3_funct_2(sK0,sK0,sK1,sK2(sK0,sK1))
    | ~ spl3_3 ),
    inference(resolution,[],[f81,f37])).

fof(f37,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,sK0)
      | k3_funct_2(sK0,sK0,sK1,X2) = X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(f114,plain,
    ( spl3_1
    | ~ spl3_5
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f109,f75,f111,f71])).

fof(f71,plain,
    ( spl3_1
  <=> k6_partfun1(sK0) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f75,plain,
    ( spl3_2
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f109,plain,
    ( sK2(sK0,sK1) != k1_funct_1(sK1,sK2(sK0,sK1))
    | k6_partfun1(sK0) = sK1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f108,f76])).

fof(f76,plain,
    ( v1_relat_1(sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f75])).

fof(f108,plain,
    ( sK2(sK0,sK1) != k1_funct_1(sK1,sK2(sK0,sK1))
    | k6_partfun1(sK0) = sK1
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f98,f34])).

fof(f98,plain,
    ( sK2(sK0,sK1) != k1_funct_1(sK1,sK2(sK0,sK1))
    | k6_partfun1(sK0) = sK1
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f55,f65])).

fof(f65,plain,(
    sK0 = k1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f63,f36])).

fof(f63,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(superposition,[],[f62,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f62,plain,(
    sK0 = k1_relset_1(sK0,sK0,sK1) ),
    inference(subsumption_resolution,[],[f61,f35])).

fof(f61,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | sK0 = k1_relset_1(sK0,sK0,sK1) ),
    inference(resolution,[],[f60,f36])).

fof(f60,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(sK1,X0,X0)
      | k1_relset_1(X0,X0,sK1) = X0 ) ),
    inference(resolution,[],[f43,f34])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | k1_relset_1(X0,X0,X1) = X0 ) ),
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).

fof(f55,plain,(
    ! [X1] :
      ( sK2(k1_relat_1(X1),X1) != k1_funct_1(X1,sK2(k1_relat_1(X1),X1))
      | k6_partfun1(k1_relat_1(X1)) = X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k6_partfun1(X0) = X1
      | sK2(X0,X1) != k1_funct_1(X1,sK2(X0,X1))
      | k1_relat_1(X1) != X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f47,f39])).

fof(f39,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f47,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) = X1
      | sK2(X0,X1) != k1_funct_1(X1,sK2(X0,X1))
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
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( r2_hidden(X2,X0)
             => k1_funct_1(X1,X2) = X2 )
          & k1_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_1)).

fof(f106,plain,(
    ~ spl3_1 ),
    inference(avatar_contradiction_clause,[],[f105])).

fof(f105,plain,
    ( $false
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f104,f34])).

fof(f104,plain,
    ( ~ v1_funct_1(sK1)
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f103,f93])).

fof(f93,plain,
    ( ~ r2_funct_2(sK0,sK0,sK1,sK1)
    | ~ spl3_1 ),
    inference(backward_demodulation,[],[f38,f73])).

fof(f73,plain,
    ( k6_partfun1(sK0) = sK1
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f71])).

fof(f38,plain,(
    ~ r2_funct_2(sK0,sK0,sK1,k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f27])).

fof(f103,plain,
    ( r2_funct_2(sK0,sK0,sK1,sK1)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f102,f36])).

fof(f102,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | r2_funct_2(sK0,sK0,sK1,sK1)
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f101,f35])).

fof(f101,plain,(
    ! [X0] :
      ( ~ v1_funct_2(X0,sK0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | r2_funct_2(sK0,sK0,X0,X0)
      | ~ v1_funct_1(X0) ) ),
    inference(subsumption_resolution,[],[f100,f35])).

fof(f100,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK1,sK0,sK0)
      | r2_funct_2(sK0,sK0,X0,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ v1_funct_2(X0,sK0,sK0)
      | ~ v1_funct_1(X0) ) ),
    inference(resolution,[],[f99,f36])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(sK1,X0,X1)
      | r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(resolution,[],[f50,f34])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => r2_funct_2(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).

fof(f92,plain,(
    spl3_2 ),
    inference(avatar_contradiction_clause,[],[f91])).

fof(f91,plain,
    ( $false
    | spl3_2 ),
    inference(subsumption_resolution,[],[f90,f41])).

fof(f41,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

% (30497)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
fof(f90,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
    | spl3_2 ),
    inference(resolution,[],[f89,f36])).

fof(f89,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl3_2 ),
    inference(resolution,[],[f77,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f77,plain,
    ( ~ v1_relat_1(sK1)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f75])).

fof(f82,plain,
    ( spl3_1
    | ~ spl3_2
    | spl3_3 ),
    inference(avatar_split_clause,[],[f69,f79,f75,f71])).

fof(f69,plain,
    ( m1_subset_1(sK2(sK0,sK1),sK0)
    | ~ v1_relat_1(sK1)
    | k6_partfun1(sK0) = sK1 ),
    inference(subsumption_resolution,[],[f67,f34])).

fof(f67,plain,
    ( m1_subset_1(sK2(sK0,sK1),sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k6_partfun1(sK0) = sK1 ),
    inference(superposition,[],[f59,f65])).

fof(f59,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(k1_relat_1(X0),X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k6_partfun1(k1_relat_1(X0)) = X0 ) ),
    inference(resolution,[],[f56,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f56,plain,(
    ! [X1] :
      ( r2_hidden(sK2(k1_relat_1(X1),X1),k1_relat_1(X1))
      | k6_partfun1(k1_relat_1(X1)) = X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k6_partfun1(X0) = X1
      | r2_hidden(sK2(X0,X1),X0)
      | k1_relat_1(X1) != X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f46,f39])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) = X1
      | r2_hidden(sK2(X0,X1),X0)
      | k1_relat_1(X1) != X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:15:30 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.56  % (30487)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.56  % (30487)Refutation found. Thanks to Tanya!
% 0.20/0.56  % SZS status Theorem for theBenchmark
% 0.20/0.56  % (30505)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.57  % (30493)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.57  % (30488)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.57  % (30513)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.57  % (30502)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.57  % (30495)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.57  % SZS output start Proof for theBenchmark
% 0.20/0.57  fof(f133,plain,(
% 0.20/0.57    $false),
% 0.20/0.57    inference(avatar_sat_refutation,[],[f82,f92,f106,f114,f132])).
% 0.20/0.57  fof(f132,plain,(
% 0.20/0.57    ~spl3_3 | spl3_5),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f131])).
% 0.20/0.57  fof(f131,plain,(
% 0.20/0.57    $false | (~spl3_3 | spl3_5)),
% 0.20/0.57    inference(subsumption_resolution,[],[f130,f33])).
% 0.20/0.57  fof(f33,plain,(
% 0.20/0.57    ~v1_xboole_0(sK0)),
% 0.20/0.57    inference(cnf_transformation,[],[f27])).
% 0.20/0.57  fof(f27,plain,(
% 0.20/0.57    (~r2_funct_2(sK0,sK0,sK1,k6_partfun1(sK0)) & ! [X2] : (k3_funct_2(sK0,sK0,sK1,X2) = X2 | ~m1_subset_1(X2,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)) & ~v1_xboole_0(sK0)),
% 0.20/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f26,f25])).
% 0.20/0.57  fof(f25,plain,(
% 0.20/0.57    ? [X0] : (? [X1] : (~r2_funct_2(X0,X0,X1,k6_partfun1(X0)) & ! [X2] : (k3_funct_2(X0,X0,X1,X2) = X2 | ~m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (~r2_funct_2(sK0,sK0,X1,k6_partfun1(sK0)) & ! [X2] : (k3_funct_2(sK0,sK0,X1,X2) = X2 | ~m1_subset_1(X2,sK0)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(X1,sK0,sK0) & v1_funct_1(X1)) & ~v1_xboole_0(sK0))),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.57  fof(f26,plain,(
% 0.20/0.57    ? [X1] : (~r2_funct_2(sK0,sK0,X1,k6_partfun1(sK0)) & ! [X2] : (k3_funct_2(sK0,sK0,X1,X2) = X2 | ~m1_subset_1(X2,sK0)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(X1,sK0,sK0) & v1_funct_1(X1)) => (~r2_funct_2(sK0,sK0,sK1,k6_partfun1(sK0)) & ! [X2] : (k3_funct_2(sK0,sK0,sK1,X2) = X2 | ~m1_subset_1(X2,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.57  fof(f13,plain,(
% 0.20/0.57    ? [X0] : (? [X1] : (~r2_funct_2(X0,X0,X1,k6_partfun1(X0)) & ! [X2] : (k3_funct_2(X0,X0,X1,X2) = X2 | ~m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) & ~v1_xboole_0(X0))),
% 0.20/0.57    inference(flattening,[],[f12])).
% 0.20/0.57  fof(f12,plain,(
% 0.20/0.57    ? [X0] : (? [X1] : ((~r2_funct_2(X0,X0,X1,k6_partfun1(X0)) & ! [X2] : (k3_funct_2(X0,X0,X1,X2) = X2 | ~m1_subset_1(X2,X0))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))) & ~v1_xboole_0(X0))),
% 0.20/0.57    inference(ennf_transformation,[],[f11])).
% 0.20/0.57  fof(f11,negated_conjecture,(
% 0.20/0.57    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (! [X2] : (m1_subset_1(X2,X0) => k3_funct_2(X0,X0,X1,X2) = X2) => r2_funct_2(X0,X0,X1,k6_partfun1(X0)))))),
% 0.20/0.57    inference(negated_conjecture,[],[f10])).
% 0.20/0.57  fof(f10,conjecture,(
% 0.20/0.57    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (! [X2] : (m1_subset_1(X2,X0) => k3_funct_2(X0,X0,X1,X2) = X2) => r2_funct_2(X0,X0,X1,k6_partfun1(X0)))))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t201_funct_2)).
% 0.20/0.57  fof(f130,plain,(
% 0.20/0.57    v1_xboole_0(sK0) | (~spl3_3 | spl3_5)),
% 0.20/0.57    inference(subsumption_resolution,[],[f129,f34])).
% 0.20/0.57  fof(f34,plain,(
% 0.20/0.57    v1_funct_1(sK1)),
% 0.20/0.57    inference(cnf_transformation,[],[f27])).
% 0.20/0.57  fof(f129,plain,(
% 0.20/0.57    ~v1_funct_1(sK1) | v1_xboole_0(sK0) | (~spl3_3 | spl3_5)),
% 0.20/0.57    inference(subsumption_resolution,[],[f128,f35])).
% 0.20/0.57  fof(f35,plain,(
% 0.20/0.57    v1_funct_2(sK1,sK0,sK0)),
% 0.20/0.57    inference(cnf_transformation,[],[f27])).
% 0.20/0.57  fof(f128,plain,(
% 0.20/0.57    ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | v1_xboole_0(sK0) | (~spl3_3 | spl3_5)),
% 0.20/0.57    inference(subsumption_resolution,[],[f127,f36])).
% 0.20/0.57  fof(f36,plain,(
% 0.20/0.57    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.20/0.57    inference(cnf_transformation,[],[f27])).
% 0.20/0.57  fof(f127,plain,(
% 0.20/0.57    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | v1_xboole_0(sK0) | (~spl3_3 | spl3_5)),
% 0.20/0.57    inference(subsumption_resolution,[],[f126,f81])).
% 0.20/0.57  fof(f81,plain,(
% 0.20/0.57    m1_subset_1(sK2(sK0,sK1),sK0) | ~spl3_3),
% 0.20/0.57    inference(avatar_component_clause,[],[f79])).
% 0.20/0.57  fof(f79,plain,(
% 0.20/0.57    spl3_3 <=> m1_subset_1(sK2(sK0,sK1),sK0)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.57  fof(f126,plain,(
% 0.20/0.57    ~m1_subset_1(sK2(sK0,sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | v1_xboole_0(sK0) | (~spl3_3 | spl3_5)),
% 0.20/0.57    inference(subsumption_resolution,[],[f118,f113])).
% 0.20/0.57  % (30485)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.57  fof(f113,plain,(
% 0.20/0.57    sK2(sK0,sK1) != k1_funct_1(sK1,sK2(sK0,sK1)) | spl3_5),
% 0.20/0.57    inference(avatar_component_clause,[],[f111])).
% 0.20/0.57  fof(f111,plain,(
% 0.20/0.57    spl3_5 <=> sK2(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.57  fof(f118,plain,(
% 0.20/0.57    sK2(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1)) | ~m1_subset_1(sK2(sK0,sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | v1_xboole_0(sK0) | ~spl3_3),
% 0.20/0.57    inference(superposition,[],[f49,f115])).
% 0.20/0.57  fof(f115,plain,(
% 0.20/0.57    sK2(sK0,sK1) = k3_funct_2(sK0,sK0,sK1,sK2(sK0,sK1)) | ~spl3_3),
% 0.20/0.57    inference(resolution,[],[f81,f37])).
% 0.20/0.57  fof(f37,plain,(
% 0.20/0.57    ( ! [X2] : (~m1_subset_1(X2,sK0) | k3_funct_2(sK0,sK0,sK1,X2) = X2) )),
% 0.20/0.57    inference(cnf_transformation,[],[f27])).
% 0.20/0.57  fof(f49,plain,(
% 0.20/0.57    ( ! [X2,X0,X3,X1] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f22])).
% 0.20/0.57  fof(f22,plain,(
% 0.20/0.57    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 0.20/0.57    inference(flattening,[],[f21])).
% 0.20/0.57  fof(f21,plain,(
% 0.20/0.57    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 0.20/0.57    inference(ennf_transformation,[],[f6])).
% 0.20/0.57  fof(f6,axiom,(
% 0.20/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).
% 0.20/0.57  fof(f114,plain,(
% 0.20/0.57    spl3_1 | ~spl3_5 | ~spl3_2),
% 0.20/0.57    inference(avatar_split_clause,[],[f109,f75,f111,f71])).
% 0.20/0.57  fof(f71,plain,(
% 0.20/0.57    spl3_1 <=> k6_partfun1(sK0) = sK1),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.57  fof(f75,plain,(
% 0.20/0.57    spl3_2 <=> v1_relat_1(sK1)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.57  fof(f109,plain,(
% 0.20/0.57    sK2(sK0,sK1) != k1_funct_1(sK1,sK2(sK0,sK1)) | k6_partfun1(sK0) = sK1 | ~spl3_2),
% 0.20/0.57    inference(subsumption_resolution,[],[f108,f76])).
% 0.20/0.57  fof(f76,plain,(
% 0.20/0.57    v1_relat_1(sK1) | ~spl3_2),
% 0.20/0.57    inference(avatar_component_clause,[],[f75])).
% 0.20/0.57  fof(f108,plain,(
% 0.20/0.57    sK2(sK0,sK1) != k1_funct_1(sK1,sK2(sK0,sK1)) | k6_partfun1(sK0) = sK1 | ~v1_relat_1(sK1)),
% 0.20/0.57    inference(subsumption_resolution,[],[f98,f34])).
% 0.20/0.57  fof(f98,plain,(
% 0.20/0.57    sK2(sK0,sK1) != k1_funct_1(sK1,sK2(sK0,sK1)) | k6_partfun1(sK0) = sK1 | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 0.20/0.57    inference(superposition,[],[f55,f65])).
% 0.20/0.57  fof(f65,plain,(
% 0.20/0.57    sK0 = k1_relat_1(sK1)),
% 0.20/0.57    inference(subsumption_resolution,[],[f63,f36])).
% 0.20/0.57  fof(f63,plain,(
% 0.20/0.57    sK0 = k1_relat_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.20/0.57    inference(superposition,[],[f62,f48])).
% 0.20/0.57  fof(f48,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f20])).
% 0.20/0.57  fof(f20,plain,(
% 0.20/0.57    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.57    inference(ennf_transformation,[],[f5])).
% 0.20/0.57  fof(f5,axiom,(
% 0.20/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.57  fof(f62,plain,(
% 0.20/0.57    sK0 = k1_relset_1(sK0,sK0,sK1)),
% 0.20/0.57    inference(subsumption_resolution,[],[f61,f35])).
% 0.20/0.57  fof(f61,plain,(
% 0.20/0.57    ~v1_funct_2(sK1,sK0,sK0) | sK0 = k1_relset_1(sK0,sK0,sK1)),
% 0.20/0.57    inference(resolution,[],[f60,f36])).
% 0.20/0.57  fof(f60,plain,(
% 0.20/0.57    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(sK1,X0,X0) | k1_relset_1(X0,X0,sK1) = X0) )),
% 0.20/0.57    inference(resolution,[],[f43,f34])).
% 0.20/0.57  fof(f43,plain,(
% 0.20/0.57    ( ! [X0,X1] : (~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | k1_relset_1(X0,X0,X1) = X0) )),
% 0.20/0.57    inference(cnf_transformation,[],[f17])).
% 0.20/0.57  fof(f17,plain,(
% 0.20/0.57    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.20/0.57    inference(flattening,[],[f16])).
% 0.20/0.57  fof(f16,plain,(
% 0.20/0.57    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.20/0.57    inference(ennf_transformation,[],[f9])).
% 0.20/0.57  fof(f9,axiom,(
% 0.20/0.57    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).
% 0.20/0.57  fof(f55,plain,(
% 0.20/0.57    ( ! [X1] : (sK2(k1_relat_1(X1),X1) != k1_funct_1(X1,sK2(k1_relat_1(X1),X1)) | k6_partfun1(k1_relat_1(X1)) = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.57    inference(equality_resolution,[],[f51])).
% 0.20/0.57  fof(f51,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k6_partfun1(X0) = X1 | sK2(X0,X1) != k1_funct_1(X1,sK2(X0,X1)) | k1_relat_1(X1) != X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.57    inference(definition_unfolding,[],[f47,f39])).
% 0.20/0.57  fof(f39,plain,(
% 0.20/0.57    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f7])).
% 0.20/0.57  fof(f7,axiom,(
% 0.20/0.57    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.20/0.57  fof(f47,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k6_relat_1(X0) = X1 | sK2(X0,X1) != k1_funct_1(X1,sK2(X0,X1)) | k1_relat_1(X1) != X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f32])).
% 0.20/0.57  fof(f32,plain,(
% 0.20/0.57    ! [X0,X1] : (((k6_relat_1(X0) = X1 | (sK2(X0,X1) != k1_funct_1(X1,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),X0)) | k1_relat_1(X1) != X0) & ((! [X3] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f31])).
% 0.20/0.57  fof(f31,plain,(
% 0.20/0.57    ! [X1,X0] : (? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) => (sK2(X0,X1) != k1_funct_1(X1,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),X0)))),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.57  fof(f30,plain,(
% 0.20/0.57    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0) & ((! [X3] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.57    inference(rectify,[],[f29])).
% 0.20/0.57  fof(f29,plain,(
% 0.20/0.57    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.57    inference(flattening,[],[f28])).
% 0.20/0.57  fof(f28,plain,(
% 0.20/0.57    ! [X0,X1] : (((k6_relat_1(X0) = X1 | (? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0)) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.57    inference(nnf_transformation,[],[f19])).
% 0.20/0.57  fof(f19,plain,(
% 0.20/0.57    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.57    inference(flattening,[],[f18])).
% 0.20/0.57  fof(f18,plain,(
% 0.20/0.57    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.57    inference(ennf_transformation,[],[f4])).
% 0.20/0.57  fof(f4,axiom,(
% 0.20/0.57    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k6_relat_1(X0) = X1 <=> (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = X2) & k1_relat_1(X1) = X0)))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_1)).
% 0.20/0.57  fof(f106,plain,(
% 0.20/0.57    ~spl3_1),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f105])).
% 0.20/0.57  fof(f105,plain,(
% 0.20/0.57    $false | ~spl3_1),
% 0.20/0.57    inference(subsumption_resolution,[],[f104,f34])).
% 0.20/0.57  fof(f104,plain,(
% 0.20/0.57    ~v1_funct_1(sK1) | ~spl3_1),
% 0.20/0.57    inference(subsumption_resolution,[],[f103,f93])).
% 0.20/0.57  fof(f93,plain,(
% 0.20/0.57    ~r2_funct_2(sK0,sK0,sK1,sK1) | ~spl3_1),
% 0.20/0.57    inference(backward_demodulation,[],[f38,f73])).
% 0.20/0.57  fof(f73,plain,(
% 0.20/0.57    k6_partfun1(sK0) = sK1 | ~spl3_1),
% 0.20/0.57    inference(avatar_component_clause,[],[f71])).
% 0.20/0.57  fof(f38,plain,(
% 0.20/0.57    ~r2_funct_2(sK0,sK0,sK1,k6_partfun1(sK0))),
% 0.20/0.57    inference(cnf_transformation,[],[f27])).
% 0.20/0.57  fof(f103,plain,(
% 0.20/0.57    r2_funct_2(sK0,sK0,sK1,sK1) | ~v1_funct_1(sK1)),
% 0.20/0.57    inference(subsumption_resolution,[],[f102,f36])).
% 0.20/0.57  fof(f102,plain,(
% 0.20/0.57    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | r2_funct_2(sK0,sK0,sK1,sK1) | ~v1_funct_1(sK1)),
% 0.20/0.57    inference(resolution,[],[f101,f35])).
% 0.20/0.57  fof(f101,plain,(
% 0.20/0.57    ( ! [X0] : (~v1_funct_2(X0,sK0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | r2_funct_2(sK0,sK0,X0,X0) | ~v1_funct_1(X0)) )),
% 0.20/0.57    inference(subsumption_resolution,[],[f100,f35])).
% 0.20/0.57  fof(f100,plain,(
% 0.20/0.57    ( ! [X0] : (~v1_funct_2(sK1,sK0,sK0) | r2_funct_2(sK0,sK0,X0,X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(X0,sK0,sK0) | ~v1_funct_1(X0)) )),
% 0.20/0.57    inference(resolution,[],[f99,f36])).
% 0.20/0.57  fof(f99,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK1,X0,X1) | r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.57    inference(resolution,[],[f50,f34])).
% 0.20/0.57  fof(f50,plain,(
% 0.20/0.57    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f24])).
% 0.20/0.57  fof(f24,plain,(
% 0.20/0.57    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.57    inference(flattening,[],[f23])).
% 0.20/0.57  fof(f23,plain,(
% 0.20/0.57    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.20/0.57    inference(ennf_transformation,[],[f8])).
% 0.20/0.57  fof(f8,axiom,(
% 0.20/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => r2_funct_2(X0,X1,X2,X2))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).
% 0.20/0.57  fof(f92,plain,(
% 0.20/0.57    spl3_2),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f91])).
% 0.20/0.57  fof(f91,plain,(
% 0.20/0.57    $false | spl3_2),
% 0.20/0.57    inference(subsumption_resolution,[],[f90,f41])).
% 0.20/0.57  fof(f41,plain,(
% 0.20/0.57    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f3])).
% 0.20/0.57  fof(f3,axiom,(
% 0.20/0.57    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.57  % (30497)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.57  fof(f90,plain,(
% 0.20/0.57    ~v1_relat_1(k2_zfmisc_1(sK0,sK0)) | spl3_2),
% 0.20/0.57    inference(resolution,[],[f89,f36])).
% 0.20/0.57  fof(f89,plain,(
% 0.20/0.57    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl3_2),
% 0.20/0.57    inference(resolution,[],[f77,f40])).
% 0.20/0.57  fof(f40,plain,(
% 0.20/0.57    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f14])).
% 0.20/0.57  fof(f14,plain,(
% 0.20/0.57    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.57    inference(ennf_transformation,[],[f2])).
% 0.20/0.57  fof(f2,axiom,(
% 0.20/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.57  fof(f77,plain,(
% 0.20/0.57    ~v1_relat_1(sK1) | spl3_2),
% 0.20/0.57    inference(avatar_component_clause,[],[f75])).
% 0.20/0.57  fof(f82,plain,(
% 0.20/0.57    spl3_1 | ~spl3_2 | spl3_3),
% 0.20/0.57    inference(avatar_split_clause,[],[f69,f79,f75,f71])).
% 0.20/0.57  fof(f69,plain,(
% 0.20/0.57    m1_subset_1(sK2(sK0,sK1),sK0) | ~v1_relat_1(sK1) | k6_partfun1(sK0) = sK1),
% 0.20/0.57    inference(subsumption_resolution,[],[f67,f34])).
% 0.20/0.57  fof(f67,plain,(
% 0.20/0.57    m1_subset_1(sK2(sK0,sK1),sK0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | k6_partfun1(sK0) = sK1),
% 0.20/0.57    inference(superposition,[],[f59,f65])).
% 0.20/0.57  fof(f59,plain,(
% 0.20/0.57    ( ! [X0] : (m1_subset_1(sK2(k1_relat_1(X0),X0),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k6_partfun1(k1_relat_1(X0)) = X0) )),
% 0.20/0.57    inference(resolution,[],[f56,f42])).
% 0.20/0.57  fof(f42,plain,(
% 0.20/0.57    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f15])).
% 0.20/0.57  fof(f15,plain,(
% 0.20/0.57    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.20/0.57    inference(ennf_transformation,[],[f1])).
% 0.20/0.57  fof(f1,axiom,(
% 0.20/0.57    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 0.20/0.57  fof(f56,plain,(
% 0.20/0.57    ( ! [X1] : (r2_hidden(sK2(k1_relat_1(X1),X1),k1_relat_1(X1)) | k6_partfun1(k1_relat_1(X1)) = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.57    inference(equality_resolution,[],[f52])).
% 0.20/0.57  fof(f52,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k6_partfun1(X0) = X1 | r2_hidden(sK2(X0,X1),X0) | k1_relat_1(X1) != X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.57    inference(definition_unfolding,[],[f46,f39])).
% 0.20/0.57  fof(f46,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k6_relat_1(X0) = X1 | r2_hidden(sK2(X0,X1),X0) | k1_relat_1(X1) != X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f32])).
% 0.20/0.57  % SZS output end Proof for theBenchmark
% 0.20/0.57  % (30487)------------------------------
% 0.20/0.57  % (30487)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (30487)Termination reason: Refutation
% 0.20/0.57  
% 0.20/0.57  % (30487)Memory used [KB]: 10746
% 0.20/0.57  % (30487)Time elapsed: 0.130 s
% 0.20/0.57  % (30487)------------------------------
% 0.20/0.57  % (30487)------------------------------
% 0.20/0.58  % (30483)Success in time 0.216 s
%------------------------------------------------------------------------------
