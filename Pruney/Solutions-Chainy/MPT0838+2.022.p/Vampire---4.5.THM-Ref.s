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
% DateTime   : Thu Dec  3 12:57:32 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 155 expanded)
%              Number of leaves         :   26 (  64 expanded)
%              Depth                    :   10
%              Number of atoms          :  277 ( 506 expanded)
%              Number of equality atoms :   62 ( 106 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f265,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f56,f60,f68,f76,f81,f86,f92,f99,f192,f229,f262,f264])).

fof(f264,plain,(
    spl6_28 ),
    inference(avatar_contradiction_clause,[],[f263])).

fof(f263,plain,
    ( $false
    | spl6_28 ),
    inference(resolution,[],[f261,f38])).

fof(f38,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f261,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3(k1_xboole_0,k2_relat_1(sK2)))
    | spl6_28 ),
    inference(avatar_component_clause,[],[f260])).

fof(f260,plain,
    ( spl6_28
  <=> r1_tarski(k1_xboole_0,sK3(k1_xboole_0,k2_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f262,plain,
    ( ~ spl6_28
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f254,f227,f260])).

fof(f227,plain,
    ( spl6_22
  <=> r2_hidden(sK3(k1_xboole_0,k2_relat_1(sK2)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f254,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3(k1_xboole_0,k2_relat_1(sK2)))
    | ~ spl6_22 ),
    inference(resolution,[],[f228,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f228,plain,
    ( r2_hidden(sK3(k1_xboole_0,k2_relat_1(sK2)),k1_xboole_0)
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f227])).

fof(f229,plain,
    ( spl6_9
    | spl6_22
    | ~ spl6_4
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f223,f190,f66,f227,f96])).

fof(f96,plain,
    ( spl6_9
  <=> k1_xboole_0 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f66,plain,
    ( spl6_4
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f190,plain,
    ( spl6_18
  <=> ! [X0] :
        ( ~ r2_hidden(sK3(X0,k2_relat_1(sK2)),k2_relat_1(sK2))
        | r2_hidden(k4_tarski(sK3(X0,k2_relat_1(sK2)),sK4(X0,k2_relat_1(sK2))),X0)
        | k1_relat_1(X0) = k2_relat_1(sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f223,plain,
    ( r2_hidden(sK3(k1_xboole_0,k2_relat_1(sK2)),k1_xboole_0)
    | k1_xboole_0 = k2_relat_1(sK2)
    | ~ spl6_4
    | ~ spl6_18 ),
    inference(superposition,[],[f196,f67])).

fof(f67,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f66])).

fof(f196,plain,
    ( ! [X1] :
        ( r2_hidden(sK3(X1,k2_relat_1(sK2)),k1_relat_1(X1))
        | k1_relat_1(X1) = k2_relat_1(sK2) )
    | ~ spl6_18 ),
    inference(resolution,[],[f194,f51])).

% (28962)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% (28962)Refutation not found, incomplete strategy% (28962)------------------------------
% (28962)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (28962)Termination reason: Refutation not found, incomplete strategy

% (28962)Memory used [KB]: 10618
% (28962)Time elapsed: 0.083 s
% (28962)------------------------------
% (28962)------------------------------
% (28966)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% (28981)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% (28981)Refutation not found, incomplete strategy% (28981)------------------------------
% (28981)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (28981)Termination reason: Refutation not found, incomplete strategy

% (28981)Memory used [KB]: 10618
% (28981)Time elapsed: 0.115 s
% (28981)------------------------------
% (28981)------------------------------
% (28979)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% (28977)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% (28972)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% (28971)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% (28971)Refutation not found, incomplete strategy% (28971)------------------------------
% (28971)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (28971)Termination reason: Refutation not found, incomplete strategy

% (28971)Memory used [KB]: 6140
% (28971)Time elapsed: 0.126 s
% (28971)------------------------------
% (28971)------------------------------
% (28972)Refutation not found, incomplete strategy% (28972)------------------------------
% (28972)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (28972)Termination reason: Refutation not found, incomplete strategy

% (28972)Memory used [KB]: 10618
% (28972)Time elapsed: 0.125 s
% (28972)------------------------------
% (28972)------------------------------
% (28975)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% (28978)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
fof(f51,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X5,X6),X0)
      | r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK3(X0,X1),X3),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f28,f31,f30,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK3(X0,X1),X3),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f194,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(sK3(X0,k2_relat_1(sK2)),sK4(X0,k2_relat_1(sK2))),X0)
        | k1_relat_1(X0) = k2_relat_1(sK2) )
    | ~ spl6_18 ),
    inference(duplicate_literal_removal,[],[f193])).

fof(f193,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(sK3(X0,k2_relat_1(sK2)),sK4(X0,k2_relat_1(sK2))),X0)
        | k1_relat_1(X0) = k2_relat_1(sK2)
        | r2_hidden(k4_tarski(sK3(X0,k2_relat_1(sK2)),sK4(X0,k2_relat_1(sK2))),X0)
        | k1_relat_1(X0) = k2_relat_1(sK2) )
    | ~ spl6_18 ),
    inference(resolution,[],[f191,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0)
      | k1_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f191,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(X0,k2_relat_1(sK2)),k2_relat_1(sK2))
        | r2_hidden(k4_tarski(sK3(X0,k2_relat_1(sK2)),sK4(X0,k2_relat_1(sK2))),X0)
        | k1_relat_1(X0) = k2_relat_1(sK2) )
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f190])).

fof(f192,plain,
    ( ~ spl6_2
    | spl6_18
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f188,f90,f190,f58])).

fof(f58,plain,
    ( spl6_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f90,plain,
    ( spl6_8
  <=> m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f188,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(X0,k2_relat_1(sK2)),k2_relat_1(sK2))
        | k1_relat_1(X0) = k2_relat_1(sK2)
        | r2_hidden(k4_tarski(sK3(X0,k2_relat_1(sK2)),sK4(X0,k2_relat_1(sK2))),X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) )
    | ~ spl6_8 ),
    inference(superposition,[],[f187,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f187,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(X0,k2_relat_1(sK2)),k2_relset_1(sK0,sK1,sK2))
        | k1_relat_1(X0) = k2_relat_1(sK2)
        | r2_hidden(k4_tarski(sK3(X0,k2_relat_1(sK2)),sK4(X0,k2_relat_1(sK2))),X0) )
    | ~ spl6_8 ),
    inference(resolution,[],[f186,f35])).

fof(f35,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,sK1)
      | ~ r2_hidden(X3,k2_relset_1(sK0,sK1,sK2)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k2_relset_1(sK0,sK1,sK2))
        | ~ m1_subset_1(X3,sK1) )
    & k1_xboole_0 != k1_relset_1(sK0,sK1,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f24])).

fof(f24,plain,
    ( ? [X0,X1,X2] :
        ( ! [X3] :
            ( ~ r2_hidden(X3,k2_relset_1(X0,X1,X2))
            | ~ m1_subset_1(X3,X1) )
        & k1_xboole_0 != k1_relset_1(X0,X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ! [X3] :
          ( ~ r2_hidden(X3,k2_relset_1(sK0,sK1,sK2))
          | ~ m1_subset_1(X3,sK1) )
      & k1_xboole_0 != k1_relset_1(sK0,sK1,sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ! [X3] :
          ( ~ r2_hidden(X3,k2_relset_1(X0,X1,X2))
          | ~ m1_subset_1(X3,X1) )
      & k1_xboole_0 != k1_relset_1(X0,X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ! [X3] :
          ( ~ r2_hidden(X3,k2_relset_1(X0,X1,X2))
          | ~ m1_subset_1(X3,X1) )
      & k1_xboole_0 != k1_relset_1(X0,X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ~ ( ! [X3] :
                ( m1_subset_1(X3,X1)
               => ~ r2_hidden(X3,k2_relset_1(X0,X1,X2)) )
            & k1_xboole_0 != k1_relset_1(X0,X1,X2) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,X1)
                       => ~ r2_hidden(X3,k2_relset_1(X0,X1,X2)) )
                    & k1_xboole_0 != k1_relset_1(X0,X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
             => ~ ( ! [X3] :
                      ( m1_subset_1(X3,X1)
                     => ~ r2_hidden(X3,k2_relset_1(X0,X1,X2)) )
                  & k1_xboole_0 != k1_relset_1(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_relset_1)).

fof(f186,plain,
    ( ! [X2] :
        ( m1_subset_1(sK3(X2,k2_relat_1(sK2)),sK1)
        | r2_hidden(k4_tarski(sK3(X2,k2_relat_1(sK2)),sK4(X2,k2_relat_1(sK2))),X2)
        | k1_relat_1(X2) = k2_relat_1(sK2) )
    | ~ spl6_8 ),
    inference(resolution,[],[f101,f91])).

fof(f91,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f90])).

fof(f101,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(X5))
      | k1_relat_1(X3) = X4
      | r2_hidden(k4_tarski(sK3(X3,X4),sK4(X3,X4)),X3)
      | m1_subset_1(sK3(X3,X4),X5) ) ),
    inference(resolution,[],[f43,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f99,plain,
    ( ~ spl6_9
    | spl6_6
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f94,f58,f79,f96])).

fof(f79,plain,
    ( spl6_6
  <=> k1_xboole_0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f94,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | k1_xboole_0 != k2_relat_1(sK2)
    | ~ spl6_2 ),
    inference(resolution,[],[f70,f59])).

fof(f59,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f58])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k1_xboole_0 = k1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0) ) ),
    inference(resolution,[],[f40,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f40,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

fof(f92,plain,
    ( ~ spl6_2
    | spl6_8
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f87,f84,f90,f58])).

fof(f84,plain,
    ( spl6_7
  <=> m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f87,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_7 ),
    inference(superposition,[],[f85,f48])).

fof(f85,plain,
    ( m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f84])).

fof(f86,plain,
    ( spl6_7
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f82,f58,f84])).

fof(f82,plain,
    ( m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1))
    | ~ spl6_2 ),
    inference(resolution,[],[f49,f59])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f81,plain,
    ( ~ spl6_6
    | spl6_1
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f77,f74,f54,f79])).

fof(f54,plain,
    ( spl6_1
  <=> k1_xboole_0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f74,plain,
    ( spl6_5
  <=> k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f77,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | spl6_1
    | ~ spl6_5 ),
    inference(superposition,[],[f55,f75])).

fof(f75,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f74])).

fof(f55,plain,
    ( k1_xboole_0 != k1_relset_1(sK0,sK1,sK2)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f54])).

fof(f76,plain,
    ( spl6_5
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f72,f58,f74])).

fof(f72,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)
    | ~ spl6_2 ),
    inference(resolution,[],[f47,f59])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f68,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f36,f66])).

fof(f36,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f60,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f33,f58])).

fof(f33,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f25])).

fof(f56,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f34,f54])).

fof(f34,plain,(
    k1_xboole_0 != k1_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:45:00 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.48  % (28961)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.49  % (28970)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.49  % (28964)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.49  % (28969)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.49  % (28961)Refutation not found, incomplete strategy% (28961)------------------------------
% 0.22/0.49  % (28961)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (28961)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (28961)Memory used [KB]: 6140
% 0.22/0.49  % (28961)Time elapsed: 0.075 s
% 0.22/0.49  % (28961)------------------------------
% 0.22/0.49  % (28961)------------------------------
% 0.22/0.50  % (28974)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.50  % (28980)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.50  % (28965)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.50  % (28964)Refutation not found, incomplete strategy% (28964)------------------------------
% 0.22/0.50  % (28964)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (28964)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (28964)Memory used [KB]: 10618
% 0.22/0.50  % (28964)Time elapsed: 0.082 s
% 0.22/0.50  % (28964)------------------------------
% 0.22/0.50  % (28964)------------------------------
% 0.22/0.51  % (28963)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.52  % (28967)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.52  % (28976)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.52  % (28973)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (28973)Refutation not found, incomplete strategy% (28973)------------------------------
% 0.22/0.52  % (28973)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (28973)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (28973)Memory used [KB]: 6012
% 0.22/0.52  % (28973)Time elapsed: 0.002 s
% 0.22/0.52  % (28973)------------------------------
% 0.22/0.52  % (28973)------------------------------
% 0.22/0.52  % (28968)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.52  % (28967)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f265,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(avatar_sat_refutation,[],[f56,f60,f68,f76,f81,f86,f92,f99,f192,f229,f262,f264])).
% 0.22/0.52  fof(f264,plain,(
% 0.22/0.52    spl6_28),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f263])).
% 0.22/0.52  fof(f263,plain,(
% 0.22/0.52    $false | spl6_28),
% 0.22/0.52    inference(resolution,[],[f261,f38])).
% 0.22/0.52  fof(f38,plain,(
% 0.22/0.52    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.52  fof(f261,plain,(
% 0.22/0.52    ~r1_tarski(k1_xboole_0,sK3(k1_xboole_0,k2_relat_1(sK2))) | spl6_28),
% 0.22/0.52    inference(avatar_component_clause,[],[f260])).
% 0.22/0.52  fof(f260,plain,(
% 0.22/0.52    spl6_28 <=> r1_tarski(k1_xboole_0,sK3(k1_xboole_0,k2_relat_1(sK2)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).
% 0.22/0.52  fof(f262,plain,(
% 0.22/0.52    ~spl6_28 | ~spl6_22),
% 0.22/0.52    inference(avatar_split_clause,[],[f254,f227,f260])).
% 0.22/0.52  fof(f227,plain,(
% 0.22/0.52    spl6_22 <=> r2_hidden(sK3(k1_xboole_0,k2_relat_1(sK2)),k1_xboole_0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 0.22/0.52  fof(f254,plain,(
% 0.22/0.52    ~r1_tarski(k1_xboole_0,sK3(k1_xboole_0,k2_relat_1(sK2))) | ~spl6_22),
% 0.22/0.52    inference(resolution,[],[f228,f45])).
% 0.22/0.52  fof(f45,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f17])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,axiom,(
% 0.22/0.52    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.22/0.52  fof(f228,plain,(
% 0.22/0.52    r2_hidden(sK3(k1_xboole_0,k2_relat_1(sK2)),k1_xboole_0) | ~spl6_22),
% 0.22/0.52    inference(avatar_component_clause,[],[f227])).
% 0.22/0.52  fof(f229,plain,(
% 0.22/0.52    spl6_9 | spl6_22 | ~spl6_4 | ~spl6_18),
% 0.22/0.52    inference(avatar_split_clause,[],[f223,f190,f66,f227,f96])).
% 0.22/0.52  fof(f96,plain,(
% 0.22/0.52    spl6_9 <=> k1_xboole_0 = k2_relat_1(sK2)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.22/0.52  fof(f66,plain,(
% 0.22/0.52    spl6_4 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.22/0.52  fof(f190,plain,(
% 0.22/0.52    spl6_18 <=> ! [X0] : (~r2_hidden(sK3(X0,k2_relat_1(sK2)),k2_relat_1(sK2)) | r2_hidden(k4_tarski(sK3(X0,k2_relat_1(sK2)),sK4(X0,k2_relat_1(sK2))),X0) | k1_relat_1(X0) = k2_relat_1(sK2))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.22/0.52  fof(f223,plain,(
% 0.22/0.52    r2_hidden(sK3(k1_xboole_0,k2_relat_1(sK2)),k1_xboole_0) | k1_xboole_0 = k2_relat_1(sK2) | (~spl6_4 | ~spl6_18)),
% 0.22/0.52    inference(superposition,[],[f196,f67])).
% 0.22/0.52  fof(f67,plain,(
% 0.22/0.52    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl6_4),
% 0.22/0.52    inference(avatar_component_clause,[],[f66])).
% 0.22/0.52  fof(f196,plain,(
% 0.22/0.52    ( ! [X1] : (r2_hidden(sK3(X1,k2_relat_1(sK2)),k1_relat_1(X1)) | k1_relat_1(X1) = k2_relat_1(sK2)) ) | ~spl6_18),
% 0.22/0.52    inference(resolution,[],[f194,f51])).
% 0.22/0.53  % (28962)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (28962)Refutation not found, incomplete strategy% (28962)------------------------------
% 0.22/0.53  % (28962)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (28962)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (28962)Memory used [KB]: 10618
% 0.22/0.53  % (28962)Time elapsed: 0.083 s
% 0.22/0.53  % (28962)------------------------------
% 0.22/0.53  % (28962)------------------------------
% 0.22/0.53  % (28966)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.53  % (28981)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.53  % (28981)Refutation not found, incomplete strategy% (28981)------------------------------
% 0.22/0.53  % (28981)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (28981)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (28981)Memory used [KB]: 10618
% 0.22/0.53  % (28981)Time elapsed: 0.115 s
% 0.22/0.53  % (28981)------------------------------
% 0.22/0.53  % (28981)------------------------------
% 0.22/0.54  % (28979)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.54  % (28977)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.54  % (28972)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.54  % (28971)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.54  % (28971)Refutation not found, incomplete strategy% (28971)------------------------------
% 0.22/0.54  % (28971)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (28971)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (28971)Memory used [KB]: 6140
% 0.22/0.54  % (28971)Time elapsed: 0.126 s
% 0.22/0.54  % (28971)------------------------------
% 0.22/0.54  % (28971)------------------------------
% 0.22/0.54  % (28972)Refutation not found, incomplete strategy% (28972)------------------------------
% 0.22/0.54  % (28972)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (28972)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (28972)Memory used [KB]: 10618
% 0.22/0.54  % (28972)Time elapsed: 0.125 s
% 0.22/0.54  % (28972)------------------------------
% 0.22/0.54  % (28972)------------------------------
% 0.22/0.54  % (28975)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.55  % (28978)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.56  fof(f51,plain,(
% 0.22/0.56    ( ! [X6,X0,X5] : (~r2_hidden(k4_tarski(X5,X6),X0) | r2_hidden(X5,k1_relat_1(X0))) )),
% 0.22/0.56    inference(equality_resolution,[],[f42])).
% 0.22/0.56  fof(f42,plain,(
% 0.22/0.56    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 0.22/0.56    inference(cnf_transformation,[],[f32])).
% 0.22/0.56  fof(f32,plain,(
% 0.22/0.56    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK3(X0,X1),X3),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.22/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f28,f31,f30,f29])).
% 0.22/0.56  fof(f29,plain,(
% 0.22/0.56    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK3(X0,X1),X3),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f30,plain,(
% 0.22/0.56    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f31,plain,(
% 0.22/0.56    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f28,plain,(
% 0.22/0.56    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.22/0.56    inference(rectify,[],[f27])).
% 0.22/0.56  fof(f27,plain,(
% 0.22/0.56    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 0.22/0.56    inference(nnf_transformation,[],[f3])).
% 0.22/0.56  fof(f3,axiom,(
% 0.22/0.56    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).
% 0.22/0.56  fof(f194,plain,(
% 0.22/0.56    ( ! [X0] : (r2_hidden(k4_tarski(sK3(X0,k2_relat_1(sK2)),sK4(X0,k2_relat_1(sK2))),X0) | k1_relat_1(X0) = k2_relat_1(sK2)) ) | ~spl6_18),
% 0.22/0.56    inference(duplicate_literal_removal,[],[f193])).
% 0.22/0.56  fof(f193,plain,(
% 0.22/0.56    ( ! [X0] : (r2_hidden(k4_tarski(sK3(X0,k2_relat_1(sK2)),sK4(X0,k2_relat_1(sK2))),X0) | k1_relat_1(X0) = k2_relat_1(sK2) | r2_hidden(k4_tarski(sK3(X0,k2_relat_1(sK2)),sK4(X0,k2_relat_1(sK2))),X0) | k1_relat_1(X0) = k2_relat_1(sK2)) ) | ~spl6_18),
% 0.22/0.56    inference(resolution,[],[f191,f43])).
% 0.22/0.56  fof(f43,plain,(
% 0.22/0.56    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) | k1_relat_1(X0) = X1) )),
% 0.22/0.56    inference(cnf_transformation,[],[f32])).
% 0.22/0.56  fof(f191,plain,(
% 0.22/0.56    ( ! [X0] : (~r2_hidden(sK3(X0,k2_relat_1(sK2)),k2_relat_1(sK2)) | r2_hidden(k4_tarski(sK3(X0,k2_relat_1(sK2)),sK4(X0,k2_relat_1(sK2))),X0) | k1_relat_1(X0) = k2_relat_1(sK2)) ) | ~spl6_18),
% 0.22/0.56    inference(avatar_component_clause,[],[f190])).
% 0.22/0.56  fof(f192,plain,(
% 0.22/0.56    ~spl6_2 | spl6_18 | ~spl6_8),
% 0.22/0.56    inference(avatar_split_clause,[],[f188,f90,f190,f58])).
% 0.22/0.56  fof(f58,plain,(
% 0.22/0.56    spl6_2 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.22/0.56  fof(f90,plain,(
% 0.22/0.56    spl6_8 <=> m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.22/0.56  fof(f188,plain,(
% 0.22/0.56    ( ! [X0] : (~r2_hidden(sK3(X0,k2_relat_1(sK2)),k2_relat_1(sK2)) | k1_relat_1(X0) = k2_relat_1(sK2) | r2_hidden(k4_tarski(sK3(X0,k2_relat_1(sK2)),sK4(X0,k2_relat_1(sK2))),X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) ) | ~spl6_8),
% 0.22/0.56    inference(superposition,[],[f187,f48])).
% 0.22/0.56  fof(f48,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f20])).
% 0.22/0.56  fof(f20,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.56    inference(ennf_transformation,[],[f10])).
% 0.22/0.56  fof(f10,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.22/0.56  fof(f187,plain,(
% 0.22/0.56    ( ! [X0] : (~r2_hidden(sK3(X0,k2_relat_1(sK2)),k2_relset_1(sK0,sK1,sK2)) | k1_relat_1(X0) = k2_relat_1(sK2) | r2_hidden(k4_tarski(sK3(X0,k2_relat_1(sK2)),sK4(X0,k2_relat_1(sK2))),X0)) ) | ~spl6_8),
% 0.22/0.56    inference(resolution,[],[f186,f35])).
% 0.22/0.56  fof(f35,plain,(
% 0.22/0.56    ( ! [X3] : (~m1_subset_1(X3,sK1) | ~r2_hidden(X3,k2_relset_1(sK0,sK1,sK2))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f25])).
% 0.22/0.56  fof(f25,plain,(
% 0.22/0.56    ! [X3] : (~r2_hidden(X3,k2_relset_1(sK0,sK1,sK2)) | ~m1_subset_1(X3,sK1)) & k1_xboole_0 != k1_relset_1(sK0,sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f24])).
% 0.22/0.56  fof(f24,plain,(
% 0.22/0.56    ? [X0,X1,X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (! [X3] : (~r2_hidden(X3,k2_relset_1(sK0,sK1,sK2)) | ~m1_subset_1(X3,sK1)) & k1_xboole_0 != k1_relset_1(sK0,sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f15,plain,(
% 0.22/0.56    ? [X0,X1,X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.56    inference(flattening,[],[f14])).
% 0.22/0.56  fof(f14,plain,(
% 0.22/0.56    ? [X0,X1,X2] : ((! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.56    inference(ennf_transformation,[],[f13])).
% 0.22/0.56  fof(f13,plain,(
% 0.22/0.56    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k2_relset_1(X0,X1,X2))) & k1_xboole_0 != k1_relset_1(X0,X1,X2)))),
% 0.22/0.56    inference(pure_predicate_removal,[],[f12])).
% 0.22/0.56  fof(f12,negated_conjecture,(
% 0.22/0.56    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k2_relset_1(X0,X1,X2))) & k1_xboole_0 != k1_relset_1(X0,X1,X2)))))),
% 0.22/0.56    inference(negated_conjecture,[],[f11])).
% 0.22/0.56  fof(f11,conjecture,(
% 0.22/0.56    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k2_relset_1(X0,X1,X2))) & k1_xboole_0 != k1_relset_1(X0,X1,X2)))))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_relset_1)).
% 0.22/0.56  fof(f186,plain,(
% 0.22/0.56    ( ! [X2] : (m1_subset_1(sK3(X2,k2_relat_1(sK2)),sK1) | r2_hidden(k4_tarski(sK3(X2,k2_relat_1(sK2)),sK4(X2,k2_relat_1(sK2))),X2) | k1_relat_1(X2) = k2_relat_1(sK2)) ) | ~spl6_8),
% 0.22/0.56    inference(resolution,[],[f101,f91])).
% 0.22/0.56  fof(f91,plain,(
% 0.22/0.56    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) | ~spl6_8),
% 0.22/0.56    inference(avatar_component_clause,[],[f90])).
% 0.22/0.56  fof(f101,plain,(
% 0.22/0.56    ( ! [X4,X5,X3] : (~m1_subset_1(X4,k1_zfmisc_1(X5)) | k1_relat_1(X3) = X4 | r2_hidden(k4_tarski(sK3(X3,X4),sK4(X3,X4)),X3) | m1_subset_1(sK3(X3,X4),X5)) )),
% 0.22/0.56    inference(resolution,[],[f43,f50])).
% 0.22/0.56  fof(f50,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f23])).
% 0.22/0.56  fof(f23,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.56    inference(flattening,[],[f22])).
% 0.22/0.56  fof(f22,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.22/0.56    inference(ennf_transformation,[],[f2])).
% 0.22/0.56  fof(f2,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 0.22/0.56  fof(f99,plain,(
% 0.22/0.56    ~spl6_9 | spl6_6 | ~spl6_2),
% 0.22/0.56    inference(avatar_split_clause,[],[f94,f58,f79,f96])).
% 0.22/0.56  fof(f79,plain,(
% 0.22/0.56    spl6_6 <=> k1_xboole_0 = k1_relat_1(sK2)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.22/0.56  fof(f94,plain,(
% 0.22/0.56    k1_xboole_0 = k1_relat_1(sK2) | k1_xboole_0 != k2_relat_1(sK2) | ~spl6_2),
% 0.22/0.56    inference(resolution,[],[f70,f59])).
% 0.22/0.56  fof(f59,plain,(
% 0.22/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl6_2),
% 0.22/0.56    inference(avatar_component_clause,[],[f58])).
% 0.22/0.56  fof(f70,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) )),
% 0.22/0.56    inference(resolution,[],[f40,f46])).
% 0.22/0.56  fof(f46,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f18])).
% 0.22/0.56  fof(f18,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.56    inference(ennf_transformation,[],[f7])).
% 0.22/0.56  fof(f7,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.56  fof(f40,plain,(
% 0.22/0.56    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f26])).
% 0.22/0.56  fof(f26,plain,(
% 0.22/0.56    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.56    inference(nnf_transformation,[],[f16])).
% 0.22/0.56  fof(f16,plain,(
% 0.22/0.56    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f5])).
% 0.22/0.56  fof(f5,axiom,(
% 0.22/0.56    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).
% 0.22/0.56  fof(f92,plain,(
% 0.22/0.56    ~spl6_2 | spl6_8 | ~spl6_7),
% 0.22/0.56    inference(avatar_split_clause,[],[f87,f84,f90,f58])).
% 0.22/0.56  fof(f84,plain,(
% 0.22/0.56    spl6_7 <=> m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.22/0.56  fof(f87,plain,(
% 0.22/0.56    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl6_7),
% 0.22/0.56    inference(superposition,[],[f85,f48])).
% 0.22/0.56  fof(f85,plain,(
% 0.22/0.56    m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1)) | ~spl6_7),
% 0.22/0.56    inference(avatar_component_clause,[],[f84])).
% 0.22/0.56  fof(f86,plain,(
% 0.22/0.56    spl6_7 | ~spl6_2),
% 0.22/0.56    inference(avatar_split_clause,[],[f82,f58,f84])).
% 0.22/0.56  fof(f82,plain,(
% 0.22/0.56    m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1)) | ~spl6_2),
% 0.22/0.56    inference(resolution,[],[f49,f59])).
% 0.22/0.56  fof(f49,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f21])).
% 0.22/0.56  fof(f21,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.56    inference(ennf_transformation,[],[f8])).
% 0.22/0.56  fof(f8,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 0.22/0.56  fof(f81,plain,(
% 0.22/0.56    ~spl6_6 | spl6_1 | ~spl6_5),
% 0.22/0.56    inference(avatar_split_clause,[],[f77,f74,f54,f79])).
% 0.22/0.56  fof(f54,plain,(
% 0.22/0.56    spl6_1 <=> k1_xboole_0 = k1_relset_1(sK0,sK1,sK2)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.22/0.56  fof(f74,plain,(
% 0.22/0.56    spl6_5 <=> k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.22/0.56  fof(f77,plain,(
% 0.22/0.56    k1_xboole_0 != k1_relat_1(sK2) | (spl6_1 | ~spl6_5)),
% 0.22/0.56    inference(superposition,[],[f55,f75])).
% 0.22/0.56  fof(f75,plain,(
% 0.22/0.56    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) | ~spl6_5),
% 0.22/0.56    inference(avatar_component_clause,[],[f74])).
% 0.22/0.56  fof(f55,plain,(
% 0.22/0.56    k1_xboole_0 != k1_relset_1(sK0,sK1,sK2) | spl6_1),
% 0.22/0.56    inference(avatar_component_clause,[],[f54])).
% 0.22/0.56  fof(f76,plain,(
% 0.22/0.56    spl6_5 | ~spl6_2),
% 0.22/0.56    inference(avatar_split_clause,[],[f72,f58,f74])).
% 0.22/0.56  fof(f72,plain,(
% 0.22/0.56    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) | ~spl6_2),
% 0.22/0.56    inference(resolution,[],[f47,f59])).
% 0.22/0.56  fof(f47,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f19])).
% 0.22/0.56  fof(f19,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.56    inference(ennf_transformation,[],[f9])).
% 0.22/0.56  fof(f9,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.56  fof(f68,plain,(
% 0.22/0.56    spl6_4),
% 0.22/0.56    inference(avatar_split_clause,[],[f36,f66])).
% 0.22/0.56  fof(f36,plain,(
% 0.22/0.56    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.56    inference(cnf_transformation,[],[f4])).
% 0.22/0.56  fof(f4,axiom,(
% 0.22/0.56    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.22/0.56  fof(f60,plain,(
% 0.22/0.56    spl6_2),
% 0.22/0.56    inference(avatar_split_clause,[],[f33,f58])).
% 0.22/0.56  fof(f33,plain,(
% 0.22/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.56    inference(cnf_transformation,[],[f25])).
% 0.22/0.56  fof(f56,plain,(
% 0.22/0.56    ~spl6_1),
% 0.22/0.56    inference(avatar_split_clause,[],[f34,f54])).
% 0.22/0.56  fof(f34,plain,(
% 0.22/0.56    k1_xboole_0 != k1_relset_1(sK0,sK1,sK2)),
% 0.22/0.56    inference(cnf_transformation,[],[f25])).
% 0.22/0.56  % SZS output end Proof for theBenchmark
% 0.22/0.56  % (28967)------------------------------
% 0.22/0.56  % (28967)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (28967)Termination reason: Refutation
% 0.22/0.56  
% 0.22/0.56  % (28967)Memory used [KB]: 10874
% 0.22/0.56  % (28967)Time elapsed: 0.111 s
% 0.22/0.56  % (28967)------------------------------
% 0.22/0.56  % (28967)------------------------------
% 0.22/0.56  % (28960)Success in time 0.198 s
%------------------------------------------------------------------------------
