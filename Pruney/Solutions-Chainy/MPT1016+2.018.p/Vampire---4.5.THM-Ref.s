%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:32 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   95 (3687 expanded)
%              Number of leaves         :   10 ( 966 expanded)
%              Depth                    :   39
%              Number of atoms          :  382 (30640 expanded)
%              Number of equality atoms :  138 (9366 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f118,plain,(
    $false ),
    inference(subsumption_resolution,[],[f117,f108])).

fof(f108,plain,(
    sK4 != sK5 ),
    inference(subsumption_resolution,[],[f36,f105])).

fof(f105,plain,(
    v2_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f51,f104])).

fof(f104,plain,(
    sP0(sK3) ),
    inference(subsumption_resolution,[],[f102,f43])).

% (29651)Termination reason: Refutation not found, incomplete strategy

% (29651)Memory used [KB]: 1663
% (29651)Time elapsed: 0.064 s
% (29651)------------------------------
% (29651)------------------------------
fof(f43,plain,(
    ! [X0] :
      ( sK6(X0) != sK7(X0)
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ( sK6(X0) != sK7(X0)
          & k1_funct_1(X0,sK6(X0)) = k1_funct_1(X0,sK7(X0))
          & r2_hidden(sK7(X0),k1_relat_1(X0))
          & r2_hidden(sK6(X0),k1_relat_1(X0)) ) )
      & ( ! [X3,X4] :
            ( X3 = X4
            | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
            | ~ r2_hidden(X4,k1_relat_1(X0))
            | ~ r2_hidden(X3,k1_relat_1(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f26,f27])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( X1 != X2
          & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
          & r2_hidden(X2,k1_relat_1(X0))
          & r2_hidden(X1,k1_relat_1(X0)) )
     => ( sK6(X0) != sK7(X0)
        & k1_funct_1(X0,sK6(X0)) = k1_funct_1(X0,sK7(X0))
        & r2_hidden(sK7(X0),k1_relat_1(X0))
        & r2_hidden(sK6(X0),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1,X2] :
            ( X1 != X2
            & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
            & r2_hidden(X2,k1_relat_1(X0))
            & r2_hidden(X1,k1_relat_1(X0)) ) )
      & ( ! [X3,X4] :
            ( X3 = X4
            | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
            | ~ r2_hidden(X4,k1_relat_1(X0))
            | ~ r2_hidden(X3,k1_relat_1(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1,X2] :
            ( X1 != X2
            & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
            & r2_hidden(X2,k1_relat_1(X0))
            & r2_hidden(X1,k1_relat_1(X0)) ) )
      & ( ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( sP0(X0)
    <=> ! [X1,X2] :
          ( X1 = X2
          | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
          | ~ r2_hidden(X2,k1_relat_1(X0))
          | ~ r2_hidden(X1,k1_relat_1(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f102,plain,
    ( sK6(sK3) = sK7(sK3)
    | sP0(sK3) ),
    inference(resolution,[],[f101,f52])).

fof(f52,plain,
    ( ~ v2_funct_1(sK3)
    | sP0(sK3) ),
    inference(resolution,[],[f50,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ~ sP1(X0)
      | ~ v2_funct_1(X0)
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ~ sP0(X0) )
        & ( sP0(X0)
          | ~ v2_funct_1(X0) ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> sP0(X0) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f50,plain,(
    sP1(sK3) ),
    inference(subsumption_resolution,[],[f49,f29])).

fof(f29,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ( ( sK4 != sK5
        & k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5)
        & r2_hidden(sK5,sK2)
        & r2_hidden(sK4,sK2) )
      | ~ v2_funct_1(sK3) )
    & ( ! [X4,X5] :
          ( X4 = X5
          | k1_funct_1(sK3,X4) != k1_funct_1(sK3,X5)
          | ~ r2_hidden(X5,sK2)
          | ~ r2_hidden(X4,sK2) )
      | v2_funct_1(sK3) )
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    & v1_funct_2(sK3,sK2,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f20,f22,f21])).

fof(f21,plain,
    ( ? [X0,X1] :
        ( ( ? [X2,X3] :
              ( X2 != X3
              & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | ~ v2_funct_1(X1) )
        & ( ! [X4,X5] :
              ( X4 = X5
              | k1_funct_1(X1,X4) != k1_funct_1(X1,X5)
              | ~ r2_hidden(X5,X0)
              | ~ r2_hidden(X4,X0) )
          | v2_funct_1(X1) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ( ? [X3,X2] :
            ( X2 != X3
            & k1_funct_1(sK3,X2) = k1_funct_1(sK3,X3)
            & r2_hidden(X3,sK2)
            & r2_hidden(X2,sK2) )
        | ~ v2_funct_1(sK3) )
      & ( ! [X5,X4] :
            ( X4 = X5
            | k1_funct_1(sK3,X4) != k1_funct_1(sK3,X5)
            | ~ r2_hidden(X5,sK2)
            | ~ r2_hidden(X4,sK2) )
        | v2_funct_1(sK3) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      & v1_funct_2(sK3,sK2,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X3,X2] :
        ( X2 != X3
        & k1_funct_1(sK3,X2) = k1_funct_1(sK3,X3)
        & r2_hidden(X3,sK2)
        & r2_hidden(X2,sK2) )
   => ( sK4 != sK5
      & k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5)
      & r2_hidden(sK5,sK2)
      & r2_hidden(sK4,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ( ? [X2,X3] :
            ( X2 != X3
            & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        | ~ v2_funct_1(X1) )
      & ( ! [X4,X5] :
            ( X4 = X5
            | k1_funct_1(X1,X4) != k1_funct_1(X1,X5)
            | ~ r2_hidden(X5,X0)
            | ~ r2_hidden(X4,X0) )
        | v2_funct_1(X1) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(rectify,[],[f19])).

% (29658)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% (29645)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
fof(f19,plain,(
    ? [X0,X1] :
      ( ( ? [X2,X3] :
            ( X2 != X3
            & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        | ~ v2_funct_1(X1) )
      & ( ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) )
        | v2_funct_1(X1) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ( ? [X2,X3] :
            ( X2 != X3
            & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        | ~ v2_funct_1(X1) )
      & ( ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) )
        | v2_funct_1(X1) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ( v2_funct_1(X1)
      <~> ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) ) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ( v2_funct_1(X1)
      <~> ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) ) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( v2_funct_1(X1)
        <=> ! [X2,X3] :
              ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
                & r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => X2 = X3 ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
      <=> ! [X2,X3] :
            ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_funct_2)).

fof(f49,plain,
    ( ~ v1_funct_1(sK3)
    | sP1(sK3) ),
    inference(resolution,[],[f48,f44])).

fof(f44,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | sP1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f10,f16,f15])).

fof(f10,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( ( k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).

fof(f48,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f46,f31])).

fof(f31,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f23])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f101,plain,
    ( v2_funct_1(sK3)
    | sK6(sK3) = sK7(sK3) ),
    inference(global_subsumption,[],[f51,f68,f100])).

fof(f100,plain,
    ( sK6(sK3) = sK7(sK3)
    | ~ r2_hidden(sK6(sK3),sK2)
    | v2_funct_1(sK3) ),
    inference(equality_resolution,[],[f98])).

fof(f98,plain,(
    ! [X0] :
      ( k1_funct_1(sK3,X0) != k1_funct_1(sK3,sK6(sK3))
      | sK7(sK3) = X0
      | ~ r2_hidden(X0,sK2)
      | v2_funct_1(sK3) ) ),
    inference(global_subsumption,[],[f51,f67,f96])).

fof(f96,plain,(
    ! [X0] :
      ( k1_funct_1(sK3,X0) != k1_funct_1(sK3,sK6(sK3))
      | sK7(sK3) = X0
      | ~ r2_hidden(sK7(sK3),sK2)
      | ~ r2_hidden(X0,sK2)
      | v2_funct_1(sK3) ) ),
    inference(superposition,[],[f32,f95])).

fof(f95,plain,(
    k1_funct_1(sK3,sK6(sK3)) = k1_funct_1(sK3,sK7(sK3)) ),
    inference(global_subsumption,[],[f34,f53,f94])).

fof(f94,plain,
    ( ~ r2_hidden(sK5,sK2)
    | k1_funct_1(sK3,sK6(sK3)) = k1_funct_1(sK3,sK7(sK3)) ),
    inference(subsumption_resolution,[],[f93,f56])).

fof(f56,plain,
    ( sK4 != sK5
    | k1_funct_1(sK3,sK6(sK3)) = k1_funct_1(sK3,sK7(sK3)) ),
    inference(resolution,[],[f53,f36])).

fof(f93,plain,
    ( ~ r2_hidden(sK5,sK2)
    | sK4 = sK5
    | k1_funct_1(sK3,sK6(sK3)) = k1_funct_1(sK3,sK7(sK3)) ),
    inference(trivial_inequality_removal,[],[f91])).

fof(f91,plain,
    ( k1_funct_1(sK3,sK4) != k1_funct_1(sK3,sK4)
    | ~ r2_hidden(sK5,sK2)
    | sK4 = sK5
    | k1_funct_1(sK3,sK6(sK3)) = k1_funct_1(sK3,sK7(sK3)) ),
    inference(superposition,[],[f88,f77])).

fof(f77,plain,(
    k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) ),
    inference(subsumption_resolution,[],[f75,f35])).

fof(f35,plain,
    ( ~ v2_funct_1(sK3)
    | k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) ),
    inference(cnf_transformation,[],[f23])).

fof(f75,plain,
    ( k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5)
    | v2_funct_1(sK3) ),
    inference(resolution,[],[f74,f51])).

fof(f74,plain,
    ( sP0(sK3)
    | k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) ),
    inference(subsumption_resolution,[],[f73,f68])).

fof(f73,plain,
    ( ~ r2_hidden(sK6(sK3),sK2)
    | k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5)
    | sP0(sK3) ),
    inference(subsumption_resolution,[],[f72,f43])).

fof(f72,plain,
    ( sK6(sK3) = sK7(sK3)
    | ~ r2_hidden(sK6(sK3),sK2)
    | k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5)
    | sP0(sK3) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X0] :
      ( k1_funct_1(sK3,X0) != k1_funct_1(sK3,sK6(sK3))
      | sK7(sK3) = X0
      | ~ r2_hidden(X0,sK2)
      | k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5)
      | sP0(sK3) ) ),
    inference(resolution,[],[f62,f67])).

fof(f62,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK7(sK3),sK2)
      | sK7(sK3) = X0
      | k1_funct_1(sK3,X0) != k1_funct_1(sK3,sK6(sK3))
      | ~ r2_hidden(X0,sK2)
      | k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) ) ),
    inference(subsumption_resolution,[],[f60,f35])).

fof(f60,plain,(
    ! [X0] :
      ( k1_funct_1(sK3,X0) != k1_funct_1(sK3,sK6(sK3))
      | sK7(sK3) = X0
      | ~ r2_hidden(sK7(sK3),sK2)
      | ~ r2_hidden(X0,sK2)
      | v2_funct_1(sK3)
      | k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) ) ),
    inference(superposition,[],[f32,f54])).

fof(f54,plain,
    ( k1_funct_1(sK3,sK6(sK3)) = k1_funct_1(sK3,sK7(sK3))
    | k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) ),
    inference(resolution,[],[f53,f35])).

fof(f88,plain,(
    ! [X0] :
      ( k1_funct_1(sK3,sK4) != k1_funct_1(sK3,X0)
      | ~ r2_hidden(X0,sK2)
      | sK4 = X0
      | k1_funct_1(sK3,sK6(sK3)) = k1_funct_1(sK3,sK7(sK3)) ) ),
    inference(subsumption_resolution,[],[f84,f53])).

fof(f84,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | k1_funct_1(sK3,sK4) != k1_funct_1(sK3,X0)
      | sK4 = X0
      | k1_funct_1(sK3,sK6(sK3)) = k1_funct_1(sK3,sK7(sK3))
      | ~ v2_funct_1(sK3) ) ),
    inference(resolution,[],[f83,f33])).

fof(f33,plain,
    ( r2_hidden(sK4,sK2)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,sK2)
      | ~ r2_hidden(X0,sK2)
      | k1_funct_1(sK3,X0) != k1_funct_1(sK3,X1)
      | X0 = X1
      | k1_funct_1(sK3,sK6(sK3)) = k1_funct_1(sK3,sK7(sK3)) ) ),
    inference(superposition,[],[f69,f66])).

fof(f66,plain,(
    sK2 = k1_relat_1(sK3) ),
    inference(backward_demodulation,[],[f57,f65])).

fof(f65,plain,(
    sK2 = k1_relset_1(sK2,sK2,sK3) ),
    inference(subsumption_resolution,[],[f64,f30])).

fof(f30,plain,(
    v1_funct_2(sK3,sK2,sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f64,plain,
    ( ~ v1_funct_2(sK3,sK2,sK2)
    | sK2 = k1_relset_1(sK2,sK2,sK3) ),
    inference(resolution,[],[f63,f31])).

fof(f63,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(sK3,X0,X0)
      | k1_relset_1(X0,X0,sK3) = X0 ) ),
    inference(resolution,[],[f45,f29])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | k1_relset_1(X0,X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).

fof(f57,plain,(
    k1_relset_1(sK2,sK2,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f47,f31])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ r2_hidden(X2,k1_relat_1(X0))
      | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
      | X1 = X2
      | k1_funct_1(X0,sK6(X0)) = k1_funct_1(X0,sK7(X0)) ) ),
    inference(resolution,[],[f39,f42])).

fof(f42,plain,(
    ! [X0] :
      ( sP0(X0)
      | k1_funct_1(X0,sK6(X0)) = k1_funct_1(X0,sK7(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f39,plain,(
    ! [X4,X0,X3] :
      ( ~ sP0(X0)
      | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | X3 = X4 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f53,plain,
    ( v2_funct_1(sK3)
    | k1_funct_1(sK3,sK6(sK3)) = k1_funct_1(sK3,sK7(sK3)) ),
    inference(resolution,[],[f42,f51])).

fof(f34,plain,
    ( r2_hidden(sK5,sK2)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f32,plain,(
    ! [X4,X5] :
      ( k1_funct_1(sK3,X4) != k1_funct_1(sK3,X5)
      | X4 = X5
      | ~ r2_hidden(X5,sK2)
      | ~ r2_hidden(X4,sK2)
      | v2_funct_1(sK3) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f67,plain,
    ( r2_hidden(sK7(sK3),sK2)
    | sP0(sK3) ),
    inference(superposition,[],[f41,f66])).

fof(f41,plain,(
    ! [X0] :
      ( r2_hidden(sK7(X0),k1_relat_1(X0))
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f68,plain,
    ( r2_hidden(sK6(sK3),sK2)
    | sP0(sK3) ),
    inference(superposition,[],[f40,f66])).

fof(f40,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0),k1_relat_1(X0))
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f51,plain,
    ( ~ sP0(sK3)
    | v2_funct_1(sK3) ),
    inference(resolution,[],[f50,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ~ sP1(X0)
      | ~ sP0(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f36,plain,
    ( ~ v2_funct_1(sK3)
    | sK4 != sK5 ),
    inference(cnf_transformation,[],[f23])).

fof(f117,plain,(
    sK4 = sK5 ),
    inference(subsumption_resolution,[],[f116,f77])).

fof(f116,plain,
    ( k1_funct_1(sK3,sK4) != k1_funct_1(sK3,sK5)
    | sK4 = sK5 ),
    inference(resolution,[],[f112,f107])).

fof(f107,plain,(
    r2_hidden(sK5,sK2) ),
    inference(subsumption_resolution,[],[f34,f105])).

fof(f112,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | k1_funct_1(sK3,sK4) != k1_funct_1(sK3,X0)
      | sK4 = X0 ) ),
    inference(resolution,[],[f111,f106])).

fof(f106,plain,(
    r2_hidden(sK4,sK2) ),
    inference(subsumption_resolution,[],[f33,f105])).

fof(f111,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,sK2)
      | ~ r2_hidden(X0,sK2)
      | k1_funct_1(sK3,X0) != k1_funct_1(sK3,X1)
      | X0 = X1 ) ),
    inference(forward_demodulation,[],[f110,f66])).

fof(f110,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,sK2)
      | k1_funct_1(sK3,X0) != k1_funct_1(sK3,X1)
      | ~ r2_hidden(X0,k1_relat_1(sK3))
      | X0 = X1 ) ),
    inference(forward_demodulation,[],[f109,f66])).

fof(f109,plain,(
    ! [X0,X1] :
      ( k1_funct_1(sK3,X0) != k1_funct_1(sK3,X1)
      | ~ r2_hidden(X1,k1_relat_1(sK3))
      | ~ r2_hidden(X0,k1_relat_1(sK3))
      | X0 = X1 ) ),
    inference(resolution,[],[f104,f39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n004.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:12:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.51  % (29663)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.51  % (29664)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.51  % (29647)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.51  % (29667)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.51  % (29648)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.51  % (29659)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.51  % (29650)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.51  % (29647)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.52  % (29656)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.52  % (29644)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.52  % (29651)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.52  % (29655)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.52  % (29651)Refutation not found, incomplete strategy% (29651)------------------------------
% 0.20/0.52  % (29651)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f118,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(subsumption_resolution,[],[f117,f108])).
% 0.20/0.52  fof(f108,plain,(
% 0.20/0.52    sK4 != sK5),
% 0.20/0.52    inference(subsumption_resolution,[],[f36,f105])).
% 0.20/0.52  fof(f105,plain,(
% 0.20/0.52    v2_funct_1(sK3)),
% 0.20/0.52    inference(subsumption_resolution,[],[f51,f104])).
% 0.20/0.52  fof(f104,plain,(
% 0.20/0.52    sP0(sK3)),
% 0.20/0.52    inference(subsumption_resolution,[],[f102,f43])).
% 0.20/0.52  % (29651)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (29651)Memory used [KB]: 1663
% 0.20/0.52  % (29651)Time elapsed: 0.064 s
% 0.20/0.52  % (29651)------------------------------
% 0.20/0.52  % (29651)------------------------------
% 0.20/0.52  fof(f43,plain,(
% 0.20/0.52    ( ! [X0] : (sK6(X0) != sK7(X0) | sP0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f28])).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    ! [X0] : ((sP0(X0) | (sK6(X0) != sK7(X0) & k1_funct_1(X0,sK6(X0)) = k1_funct_1(X0,sK7(X0)) & r2_hidden(sK7(X0),k1_relat_1(X0)) & r2_hidden(sK6(X0),k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~sP0(X0)))),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f26,f27])).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    ! [X0] : (? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => (sK6(X0) != sK7(X0) & k1_funct_1(X0,sK6(X0)) = k1_funct_1(X0,sK7(X0)) & r2_hidden(sK7(X0),k1_relat_1(X0)) & r2_hidden(sK6(X0),k1_relat_1(X0))))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    ! [X0] : ((sP0(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~sP0(X0)))),
% 0.20/0.52    inference(rectify,[],[f25])).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    ! [X0] : ((sP0(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))) | ~sP0(X0)))),
% 0.20/0.52    inference(nnf_transformation,[],[f15])).
% 0.20/0.52  fof(f15,plain,(
% 0.20/0.52    ! [X0] : (sP0(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))),
% 0.20/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.52  fof(f102,plain,(
% 0.20/0.52    sK6(sK3) = sK7(sK3) | sP0(sK3)),
% 0.20/0.52    inference(resolution,[],[f101,f52])).
% 0.20/0.52  fof(f52,plain,(
% 0.20/0.52    ~v2_funct_1(sK3) | sP0(sK3)),
% 0.20/0.52    inference(resolution,[],[f50,f37])).
% 0.20/0.52  fof(f37,plain,(
% 0.20/0.52    ( ! [X0] : (~sP1(X0) | ~v2_funct_1(X0) | sP0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f24])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ! [X0] : (((v2_funct_1(X0) | ~sP0(X0)) & (sP0(X0) | ~v2_funct_1(X0))) | ~sP1(X0))),
% 0.20/0.52    inference(nnf_transformation,[],[f16])).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    ! [X0] : ((v2_funct_1(X0) <=> sP0(X0)) | ~sP1(X0))),
% 0.20/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.20/0.52  fof(f50,plain,(
% 0.20/0.52    sP1(sK3)),
% 0.20/0.52    inference(subsumption_resolution,[],[f49,f29])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    v1_funct_1(sK3)),
% 0.20/0.52    inference(cnf_transformation,[],[f23])).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    ((sK4 != sK5 & k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) & r2_hidden(sK5,sK2) & r2_hidden(sK4,sK2)) | ~v2_funct_1(sK3)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(sK3,X4) != k1_funct_1(sK3,X5) | ~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK2)) | v2_funct_1(sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(sK3,sK2,sK2) & v1_funct_1(sK3)),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f20,f22,f21])).
% 0.20/0.52  fof(f21,plain,(
% 0.20/0.52    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(X1,X4) != k1_funct_1(X1,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((? [X3,X2] : (X2 != X3 & k1_funct_1(sK3,X2) = k1_funct_1(sK3,X3) & r2_hidden(X3,sK2) & r2_hidden(X2,sK2)) | ~v2_funct_1(sK3)) & (! [X5,X4] : (X4 = X5 | k1_funct_1(sK3,X4) != k1_funct_1(sK3,X5) | ~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK2)) | v2_funct_1(sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(sK3,sK2,sK2) & v1_funct_1(sK3))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    ? [X3,X2] : (X2 != X3 & k1_funct_1(sK3,X2) = k1_funct_1(sK3,X3) & r2_hidden(X3,sK2) & r2_hidden(X2,sK2)) => (sK4 != sK5 & k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) & r2_hidden(sK5,sK2) & r2_hidden(sK4,sK2))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(X1,X4) != k1_funct_1(X1,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.20/0.52    inference(rectify,[],[f19])).
% 0.20/0.52  % (29658)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.53  % (29645)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  fof(f19,plain,(
% 0.20/0.53    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.20/0.53    inference(flattening,[],[f18])).
% 0.20/0.53  fof(f18,plain,(
% 0.20/0.53    ? [X0,X1] : (((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) | v2_funct_1(X1))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.20/0.53    inference(nnf_transformation,[],[f8])).
% 0.20/0.53  fof(f8,plain,(
% 0.20/0.53    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.20/0.53    inference(flattening,[],[f7])).
% 0.20/0.53  fof(f7,plain,(
% 0.20/0.53    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | (k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 0.20/0.53    inference(ennf_transformation,[],[f6])).
% 0.20/0.53  fof(f6,negated_conjecture,(
% 0.20/0.53    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 0.20/0.53    inference(negated_conjecture,[],[f5])).
% 0.20/0.53  fof(f5,conjecture,(
% 0.20/0.53    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_funct_2)).
% 0.20/0.53  fof(f49,plain,(
% 0.20/0.53    ~v1_funct_1(sK3) | sP1(sK3)),
% 0.20/0.53    inference(resolution,[],[f48,f44])).
% 0.20/0.53  fof(f44,plain,(
% 0.20/0.53    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | sP1(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f17])).
% 0.20/0.53  fof(f17,plain,(
% 0.20/0.53    ! [X0] : (sP1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(definition_folding,[],[f10,f16,f15])).
% 0.20/0.53  fof(f10,plain,(
% 0.20/0.53    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(flattening,[],[f9])).
% 0.20/0.53  fof(f9,plain,(
% 0.20/0.53    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | (k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f1])).
% 0.20/0.53  fof(f1,axiom,(
% 0.20/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1,X2] : ((k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => X1 = X2)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).
% 0.20/0.53  fof(f48,plain,(
% 0.20/0.53    v1_relat_1(sK3)),
% 0.20/0.53    inference(resolution,[],[f46,f31])).
% 0.20/0.53  fof(f31,plain,(
% 0.20/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 0.20/0.53    inference(cnf_transformation,[],[f23])).
% 0.20/0.53  fof(f46,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f13])).
% 0.20/0.53  fof(f13,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(ennf_transformation,[],[f2])).
% 0.20/0.53  fof(f2,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.53  fof(f101,plain,(
% 0.20/0.53    v2_funct_1(sK3) | sK6(sK3) = sK7(sK3)),
% 0.20/0.53    inference(global_subsumption,[],[f51,f68,f100])).
% 0.20/0.53  fof(f100,plain,(
% 0.20/0.53    sK6(sK3) = sK7(sK3) | ~r2_hidden(sK6(sK3),sK2) | v2_funct_1(sK3)),
% 0.20/0.53    inference(equality_resolution,[],[f98])).
% 0.20/0.53  fof(f98,plain,(
% 0.20/0.53    ( ! [X0] : (k1_funct_1(sK3,X0) != k1_funct_1(sK3,sK6(sK3)) | sK7(sK3) = X0 | ~r2_hidden(X0,sK2) | v2_funct_1(sK3)) )),
% 0.20/0.53    inference(global_subsumption,[],[f51,f67,f96])).
% 0.20/0.53  fof(f96,plain,(
% 0.20/0.53    ( ! [X0] : (k1_funct_1(sK3,X0) != k1_funct_1(sK3,sK6(sK3)) | sK7(sK3) = X0 | ~r2_hidden(sK7(sK3),sK2) | ~r2_hidden(X0,sK2) | v2_funct_1(sK3)) )),
% 0.20/0.53    inference(superposition,[],[f32,f95])).
% 0.20/0.53  fof(f95,plain,(
% 0.20/0.53    k1_funct_1(sK3,sK6(sK3)) = k1_funct_1(sK3,sK7(sK3))),
% 0.20/0.53    inference(global_subsumption,[],[f34,f53,f94])).
% 0.20/0.53  fof(f94,plain,(
% 0.20/0.53    ~r2_hidden(sK5,sK2) | k1_funct_1(sK3,sK6(sK3)) = k1_funct_1(sK3,sK7(sK3))),
% 0.20/0.53    inference(subsumption_resolution,[],[f93,f56])).
% 0.20/0.53  fof(f56,plain,(
% 0.20/0.53    sK4 != sK5 | k1_funct_1(sK3,sK6(sK3)) = k1_funct_1(sK3,sK7(sK3))),
% 0.20/0.53    inference(resolution,[],[f53,f36])).
% 0.20/0.53  fof(f93,plain,(
% 0.20/0.53    ~r2_hidden(sK5,sK2) | sK4 = sK5 | k1_funct_1(sK3,sK6(sK3)) = k1_funct_1(sK3,sK7(sK3))),
% 0.20/0.53    inference(trivial_inequality_removal,[],[f91])).
% 0.20/0.53  fof(f91,plain,(
% 0.20/0.53    k1_funct_1(sK3,sK4) != k1_funct_1(sK3,sK4) | ~r2_hidden(sK5,sK2) | sK4 = sK5 | k1_funct_1(sK3,sK6(sK3)) = k1_funct_1(sK3,sK7(sK3))),
% 0.20/0.53    inference(superposition,[],[f88,f77])).
% 0.20/0.53  fof(f77,plain,(
% 0.20/0.53    k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5)),
% 0.20/0.53    inference(subsumption_resolution,[],[f75,f35])).
% 0.20/0.53  fof(f35,plain,(
% 0.20/0.53    ~v2_funct_1(sK3) | k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5)),
% 0.20/0.53    inference(cnf_transformation,[],[f23])).
% 0.20/0.53  fof(f75,plain,(
% 0.20/0.53    k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) | v2_funct_1(sK3)),
% 0.20/0.53    inference(resolution,[],[f74,f51])).
% 0.20/0.53  fof(f74,plain,(
% 0.20/0.53    sP0(sK3) | k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5)),
% 0.20/0.53    inference(subsumption_resolution,[],[f73,f68])).
% 0.20/0.53  fof(f73,plain,(
% 0.20/0.53    ~r2_hidden(sK6(sK3),sK2) | k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) | sP0(sK3)),
% 0.20/0.53    inference(subsumption_resolution,[],[f72,f43])).
% 0.20/0.53  fof(f72,plain,(
% 0.20/0.53    sK6(sK3) = sK7(sK3) | ~r2_hidden(sK6(sK3),sK2) | k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) | sP0(sK3)),
% 0.20/0.53    inference(equality_resolution,[],[f70])).
% 0.20/0.53  fof(f70,plain,(
% 0.20/0.53    ( ! [X0] : (k1_funct_1(sK3,X0) != k1_funct_1(sK3,sK6(sK3)) | sK7(sK3) = X0 | ~r2_hidden(X0,sK2) | k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) | sP0(sK3)) )),
% 0.20/0.53    inference(resolution,[],[f62,f67])).
% 0.20/0.53  fof(f62,plain,(
% 0.20/0.53    ( ! [X0] : (~r2_hidden(sK7(sK3),sK2) | sK7(sK3) = X0 | k1_funct_1(sK3,X0) != k1_funct_1(sK3,sK6(sK3)) | ~r2_hidden(X0,sK2) | k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f60,f35])).
% 0.20/0.53  fof(f60,plain,(
% 0.20/0.53    ( ! [X0] : (k1_funct_1(sK3,X0) != k1_funct_1(sK3,sK6(sK3)) | sK7(sK3) = X0 | ~r2_hidden(sK7(sK3),sK2) | ~r2_hidden(X0,sK2) | v2_funct_1(sK3) | k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5)) )),
% 0.20/0.53    inference(superposition,[],[f32,f54])).
% 0.20/0.53  fof(f54,plain,(
% 0.20/0.53    k1_funct_1(sK3,sK6(sK3)) = k1_funct_1(sK3,sK7(sK3)) | k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5)),
% 0.20/0.53    inference(resolution,[],[f53,f35])).
% 0.20/0.53  fof(f88,plain,(
% 0.20/0.53    ( ! [X0] : (k1_funct_1(sK3,sK4) != k1_funct_1(sK3,X0) | ~r2_hidden(X0,sK2) | sK4 = X0 | k1_funct_1(sK3,sK6(sK3)) = k1_funct_1(sK3,sK7(sK3))) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f84,f53])).
% 0.20/0.53  fof(f84,plain,(
% 0.20/0.53    ( ! [X0] : (~r2_hidden(X0,sK2) | k1_funct_1(sK3,sK4) != k1_funct_1(sK3,X0) | sK4 = X0 | k1_funct_1(sK3,sK6(sK3)) = k1_funct_1(sK3,sK7(sK3)) | ~v2_funct_1(sK3)) )),
% 0.20/0.53    inference(resolution,[],[f83,f33])).
% 0.20/0.53  fof(f33,plain,(
% 0.20/0.53    r2_hidden(sK4,sK2) | ~v2_funct_1(sK3)),
% 0.20/0.53    inference(cnf_transformation,[],[f23])).
% 0.20/0.53  fof(f83,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r2_hidden(X1,sK2) | ~r2_hidden(X0,sK2) | k1_funct_1(sK3,X0) != k1_funct_1(sK3,X1) | X0 = X1 | k1_funct_1(sK3,sK6(sK3)) = k1_funct_1(sK3,sK7(sK3))) )),
% 0.20/0.53    inference(superposition,[],[f69,f66])).
% 0.20/0.53  fof(f66,plain,(
% 0.20/0.53    sK2 = k1_relat_1(sK3)),
% 0.20/0.53    inference(backward_demodulation,[],[f57,f65])).
% 0.20/0.53  fof(f65,plain,(
% 0.20/0.53    sK2 = k1_relset_1(sK2,sK2,sK3)),
% 0.20/0.53    inference(subsumption_resolution,[],[f64,f30])).
% 0.20/0.53  fof(f30,plain,(
% 0.20/0.53    v1_funct_2(sK3,sK2,sK2)),
% 0.20/0.53    inference(cnf_transformation,[],[f23])).
% 0.20/0.53  fof(f64,plain,(
% 0.20/0.53    ~v1_funct_2(sK3,sK2,sK2) | sK2 = k1_relset_1(sK2,sK2,sK3)),
% 0.20/0.53    inference(resolution,[],[f63,f31])).
% 0.20/0.53  fof(f63,plain,(
% 0.20/0.53    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(sK3,X0,X0) | k1_relset_1(X0,X0,sK3) = X0) )),
% 0.20/0.53    inference(resolution,[],[f45,f29])).
% 0.20/0.53  fof(f45,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | k1_relset_1(X0,X0,X1) = X0) )),
% 0.20/0.53    inference(cnf_transformation,[],[f12])).
% 0.20/0.53  fof(f12,plain,(
% 0.20/0.53    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.20/0.53    inference(flattening,[],[f11])).
% 0.20/0.53  fof(f11,plain,(
% 0.20/0.53    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.20/0.53    inference(ennf_transformation,[],[f4])).
% 0.20/0.53  fof(f4,axiom,(
% 0.20/0.53    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).
% 0.20/0.53  fof(f57,plain,(
% 0.20/0.53    k1_relset_1(sK2,sK2,sK3) = k1_relat_1(sK3)),
% 0.20/0.53    inference(resolution,[],[f47,f31])).
% 0.20/0.53  fof(f47,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f14])).
% 0.20/0.53  fof(f14,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(ennf_transformation,[],[f3])).
% 0.20/0.53  fof(f3,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.53  fof(f69,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X1,k1_relat_1(X0)) | ~r2_hidden(X2,k1_relat_1(X0)) | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | X1 = X2 | k1_funct_1(X0,sK6(X0)) = k1_funct_1(X0,sK7(X0))) )),
% 0.20/0.53    inference(resolution,[],[f39,f42])).
% 0.20/0.53  fof(f42,plain,(
% 0.20/0.53    ( ! [X0] : (sP0(X0) | k1_funct_1(X0,sK6(X0)) = k1_funct_1(X0,sK7(X0))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f28])).
% 0.20/0.53  fof(f39,plain,(
% 0.20/0.53    ( ! [X4,X0,X3] : (~sP0(X0) | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0)) | X3 = X4) )),
% 0.20/0.53    inference(cnf_transformation,[],[f28])).
% 0.20/0.53  fof(f53,plain,(
% 0.20/0.53    v2_funct_1(sK3) | k1_funct_1(sK3,sK6(sK3)) = k1_funct_1(sK3,sK7(sK3))),
% 0.20/0.53    inference(resolution,[],[f42,f51])).
% 0.20/0.53  fof(f34,plain,(
% 0.20/0.53    r2_hidden(sK5,sK2) | ~v2_funct_1(sK3)),
% 0.20/0.53    inference(cnf_transformation,[],[f23])).
% 0.20/0.53  fof(f32,plain,(
% 0.20/0.53    ( ! [X4,X5] : (k1_funct_1(sK3,X4) != k1_funct_1(sK3,X5) | X4 = X5 | ~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK2) | v2_funct_1(sK3)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f23])).
% 0.20/0.53  fof(f67,plain,(
% 0.20/0.53    r2_hidden(sK7(sK3),sK2) | sP0(sK3)),
% 0.20/0.53    inference(superposition,[],[f41,f66])).
% 0.20/0.53  fof(f41,plain,(
% 0.20/0.53    ( ! [X0] : (r2_hidden(sK7(X0),k1_relat_1(X0)) | sP0(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f28])).
% 0.20/0.53  fof(f68,plain,(
% 0.20/0.53    r2_hidden(sK6(sK3),sK2) | sP0(sK3)),
% 0.20/0.53    inference(superposition,[],[f40,f66])).
% 0.20/0.53  fof(f40,plain,(
% 0.20/0.53    ( ! [X0] : (r2_hidden(sK6(X0),k1_relat_1(X0)) | sP0(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f28])).
% 0.20/0.53  fof(f51,plain,(
% 0.20/0.53    ~sP0(sK3) | v2_funct_1(sK3)),
% 0.20/0.53    inference(resolution,[],[f50,f38])).
% 0.20/0.53  fof(f38,plain,(
% 0.20/0.53    ( ! [X0] : (~sP1(X0) | ~sP0(X0) | v2_funct_1(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f24])).
% 0.20/0.53  fof(f36,plain,(
% 0.20/0.53    ~v2_funct_1(sK3) | sK4 != sK5),
% 0.20/0.53    inference(cnf_transformation,[],[f23])).
% 0.20/0.53  fof(f117,plain,(
% 0.20/0.53    sK4 = sK5),
% 0.20/0.53    inference(subsumption_resolution,[],[f116,f77])).
% 0.20/0.53  fof(f116,plain,(
% 0.20/0.53    k1_funct_1(sK3,sK4) != k1_funct_1(sK3,sK5) | sK4 = sK5),
% 0.20/0.53    inference(resolution,[],[f112,f107])).
% 0.20/0.53  fof(f107,plain,(
% 0.20/0.53    r2_hidden(sK5,sK2)),
% 0.20/0.53    inference(subsumption_resolution,[],[f34,f105])).
% 0.20/0.53  fof(f112,plain,(
% 0.20/0.53    ( ! [X0] : (~r2_hidden(X0,sK2) | k1_funct_1(sK3,sK4) != k1_funct_1(sK3,X0) | sK4 = X0) )),
% 0.20/0.53    inference(resolution,[],[f111,f106])).
% 0.20/0.53  fof(f106,plain,(
% 0.20/0.53    r2_hidden(sK4,sK2)),
% 0.20/0.53    inference(subsumption_resolution,[],[f33,f105])).
% 0.20/0.53  fof(f111,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r2_hidden(X1,sK2) | ~r2_hidden(X0,sK2) | k1_funct_1(sK3,X0) != k1_funct_1(sK3,X1) | X0 = X1) )),
% 0.20/0.53    inference(forward_demodulation,[],[f110,f66])).
% 0.20/0.53  fof(f110,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r2_hidden(X1,sK2) | k1_funct_1(sK3,X0) != k1_funct_1(sK3,X1) | ~r2_hidden(X0,k1_relat_1(sK3)) | X0 = X1) )),
% 0.20/0.53    inference(forward_demodulation,[],[f109,f66])).
% 0.20/0.53  fof(f109,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k1_funct_1(sK3,X0) != k1_funct_1(sK3,X1) | ~r2_hidden(X1,k1_relat_1(sK3)) | ~r2_hidden(X0,k1_relat_1(sK3)) | X0 = X1) )),
% 0.20/0.53    inference(resolution,[],[f104,f39])).
% 0.20/0.53  % SZS output end Proof for theBenchmark
% 0.20/0.53  % (29647)------------------------------
% 0.20/0.53  % (29647)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (29647)Termination reason: Refutation
% 0.20/0.53  
% 0.20/0.53  % (29647)Memory used [KB]: 6268
% 0.20/0.53  % (29647)Time elapsed: 0.105 s
% 0.20/0.53  % (29647)------------------------------
% 0.20/0.53  % (29647)------------------------------
% 0.20/0.53  % (29643)Success in time 0.166 s
%------------------------------------------------------------------------------
