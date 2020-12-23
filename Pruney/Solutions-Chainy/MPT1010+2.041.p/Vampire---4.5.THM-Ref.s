%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:04:56 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.26s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 198 expanded)
%              Number of leaves         :   28 (  69 expanded)
%              Depth                    :   13
%              Number of atoms          :  393 ( 753 expanded)
%              Number of equality atoms :  124 ( 280 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f697,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f91,f96,f101,f106,f112,f135,f182,f188,f196,f220,f263,f535,f696])).

fof(f696,plain,(
    ~ spl6_17 ),
    inference(avatar_contradiction_clause,[],[f695])).

fof(f695,plain,
    ( $false
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f685,f119])).

fof(f119,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f44,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f44,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f685,plain,
    ( r2_hidden(sK1,k1_xboole_0)
    | ~ spl6_17 ),
    inference(superposition,[],[f83,f219])).

fof(f219,plain,
    ( k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f217])).

fof(f217,plain,
    ( spl6_17
  <=> k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f83,plain,(
    ! [X4,X0] : r2_hidden(X4,k1_enumset1(X0,X0,X4)) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k1_enumset1(X0,X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f64,f48])).

fof(f48,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f64,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f38])).

% (17189)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK5(X0,X1,X2) != X1
              & sK5(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( sK5(X0,X1,X2) = X1
            | sK5(X0,X1,X2) = X0
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f36,f37])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK5(X0,X1,X2) != X1
            & sK5(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( sK5(X0,X1,X2) = X1
          | sK5(X0,X1,X2) = X0
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f535,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_11
    | spl6_12
    | ~ spl6_21 ),
    inference(avatar_contradiction_clause,[],[f534])).

fof(f534,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_11
    | spl6_12
    | ~ spl6_21 ),
    inference(subsumption_resolution,[],[f530,f191])).

fof(f191,plain,
    ( ~ m1_subset_1(k1_funct_1(sK3,sK2),k1_enumset1(sK1,sK1,sK1))
    | spl6_12 ),
    inference(unit_resulting_resolution,[],[f122,f187,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f187,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK2),k1_enumset1(sK1,sK1,sK1))
    | spl6_12 ),
    inference(avatar_component_clause,[],[f185])).

fof(f185,plain,
    ( spl6_12
  <=> r2_hidden(k1_funct_1(sK3,sK2),k1_enumset1(sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f122,plain,(
    ! [X0,X1] : ~ v1_xboole_0(k1_enumset1(X0,X0,X1)) ),
    inference(unit_resulting_resolution,[],[f83,f46])).

fof(f46,plain,(
    ! [X2,X0] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK4(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f30,f31])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f530,plain,
    ( m1_subset_1(k1_funct_1(sK3,sK2),k1_enumset1(sK1,sK1,sK1))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_11
    | ~ spl6_21 ),
    inference(unit_resulting_resolution,[],[f95,f181,f443])).

fof(f443,plain,
    ( ! [X0,X1] :
        ( ~ v5_relat_1(sK3,X1)
        | m1_subset_1(k1_funct_1(sK3,X0),X1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl6_1
    | ~ spl6_7
    | ~ spl6_21 ),
    inference(backward_demodulation,[],[f151,f248])).

% (17177)Refutation not found, incomplete strategy% (17177)------------------------------
% (17177)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (17177)Termination reason: Refutation not found, incomplete strategy

% (17177)Memory used [KB]: 10746
% (17177)Time elapsed: 0.111 s
% (17177)------------------------------
% (17177)------------------------------
fof(f248,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f246])).

fof(f246,plain,
    ( spl6_21
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f151,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k1_relat_1(sK3))
        | m1_subset_1(k1_funct_1(sK3,X0),X1)
        | ~ v5_relat_1(sK3,X1) )
    | ~ spl6_1
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f150,f134])).

fof(f134,plain,
    ( v1_relat_1(sK3)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl6_7
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f150,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k1_relat_1(sK3))
        | m1_subset_1(k1_funct_1(sK3,X0),X1)
        | ~ v5_relat_1(sK3,X1)
        | ~ v1_relat_1(sK3) )
    | ~ spl6_1 ),
    inference(resolution,[],[f61,f90])).

fof(f90,plain,
    ( v1_funct_1(sK3)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl6_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | m1_subset_1(k1_funct_1(X2,X1),X0)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_funct_1(X2,X1),X0)
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_funct_1(X2,X1),X0)
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v5_relat_1(X2,X0)
        & v1_relat_1(X2) )
     => ( r2_hidden(X1,k1_relat_1(X2))
       => m1_subset_1(k1_funct_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_funct_1)).

fof(f181,plain,
    ( v5_relat_1(sK3,k1_enumset1(sK1,sK1,sK1))
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f179])).

fof(f179,plain,
    ( spl6_11
  <=> v5_relat_1(sK3,k1_enumset1(sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

% (17172)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% (17181)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% (17191)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% (17181)Refutation not found, incomplete strategy% (17181)------------------------------
% (17181)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (17181)Termination reason: Refutation not found, incomplete strategy

% (17181)Memory used [KB]: 1791
% (17181)Time elapsed: 0.117 s
% (17181)------------------------------
% (17181)------------------------------
% (17186)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% (17176)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
fof(f95,plain,
    ( r2_hidden(sK2,sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl6_2
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f263,plain,
    ( spl6_21
    | ~ spl6_13
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f253,f213,f193,f246])).

fof(f193,plain,
    ( spl6_13
  <=> k1_relat_1(sK3) = k1_relset_1(sK0,k1_enumset1(sK1,sK1,sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f213,plain,
    ( spl6_16
  <=> sK0 = k1_relset_1(sK0,k1_enumset1(sK1,sK1,sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f253,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl6_13
    | ~ spl6_16 ),
    inference(backward_demodulation,[],[f195,f215])).

fof(f215,plain,
    ( sK0 = k1_relset_1(sK0,k1_enumset1(sK1,sK1,sK1),sK3)
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f213])).

fof(f195,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK0,k1_enumset1(sK1,sK1,sK1),sK3)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f193])).

fof(f220,plain,
    ( spl6_16
    | spl6_17
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f158,f109,f103,f217,f213])).

fof(f103,plain,
    ( spl6_4
  <=> v1_funct_2(sK3,sK0,k1_enumset1(sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f109,plain,
    ( spl6_5
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f158,plain,
    ( k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)
    | sK0 = k1_relset_1(sK0,k1_enumset1(sK1,sK1,sK1),sK3)
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f157,f105])).

fof(f105,plain,
    ( v1_funct_2(sK3,sK0,k1_enumset1(sK1,sK1,sK1))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f103])).

fof(f157,plain,
    ( ~ v1_funct_2(sK3,sK0,k1_enumset1(sK1,sK1,sK1))
    | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)
    | sK0 = k1_relset_1(sK0,k1_enumset1(sK1,sK1,sK1),sK3)
    | ~ spl6_5 ),
    inference(resolution,[],[f55,f111])).

fof(f111,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1))))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f109])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f196,plain,
    ( spl6_13
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f148,f109,f193])).

fof(f148,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK0,k1_enumset1(sK1,sK1,sK1),sK3)
    | ~ spl6_5 ),
    inference(unit_resulting_resolution,[],[f111,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f21])).

% (17173)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% (17167)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% (17190)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% (17193)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% (17185)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% (17185)Refutation not found, incomplete strategy% (17185)------------------------------
% (17185)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f188,plain,
    ( ~ spl6_12
    | spl6_3 ),
    inference(avatar_split_clause,[],[f138,f98,f185])).

fof(f98,plain,
    ( spl6_3
  <=> sK1 = k1_funct_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f138,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK2),k1_enumset1(sK1,sK1,sK1))
    | spl6_3 ),
    inference(unit_resulting_resolution,[],[f100,f100,f86])).

fof(f86,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k1_enumset1(X0,X0,X1))
      | X0 = X4
      | X1 = X4 ) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f62,f48])).

fof(f62,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f100,plain,
    ( sK1 != k1_funct_1(sK3,sK2)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f98])).

fof(f182,plain,
    ( spl6_11
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f136,f109,f179])).

fof(f136,plain,
    ( v5_relat_1(sK3,k1_enumset1(sK1,sK1,sK1))
    | ~ spl6_5 ),
    inference(unit_resulting_resolution,[],[f111,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f135,plain,
    ( spl6_7
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f127,f109,f132])).

fof(f127,plain,
    ( v1_relat_1(sK3)
    | ~ spl6_5 ),
    inference(unit_resulting_resolution,[],[f111,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f112,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f69,f109])).

fof(f69,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1)))) ),
    inference(definition_unfolding,[],[f41,f68])).

fof(f68,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f45,f48])).

fof(f45,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f41,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( sK1 != k1_funct_1(sK3,sK2)
    & r2_hidden(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    & v1_funct_2(sK3,sK0,k1_tarski(sK1))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f27])).

fof(f27,plain,
    ( ? [X0,X1,X2,X3] :
        ( k1_funct_1(X3,X2) != X1
        & r2_hidden(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
   => ( sK1 != k1_funct_1(sK3,sK2)
      & r2_hidden(sK2,sK0)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
      & v1_funct_2(sK3,sK0,k1_tarski(sK1))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => k1_funct_1(X3,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => k1_funct_1(X3,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

fof(f106,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f70,f103])).

fof(f70,plain,(
    v1_funct_2(sK3,sK0,k1_enumset1(sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f40,f68])).

fof(f40,plain,(
    v1_funct_2(sK3,sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f28])).

fof(f101,plain,(
    ~ spl6_3 ),
    inference(avatar_split_clause,[],[f43,f98])).

fof(f43,plain,(
    sK1 != k1_funct_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f96,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f42,f93])).

fof(f42,plain,(
    r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f91,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f39,f88])).

fof(f39,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:21:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.47  % (17169)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.47  % (17195)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.47  % (17179)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.48  % (17179)Refutation not found, incomplete strategy% (17179)------------------------------
% 0.20/0.48  % (17179)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (17187)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.48  % (17179)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (17179)Memory used [KB]: 10618
% 0.20/0.48  % (17179)Time elapsed: 0.077 s
% 0.20/0.48  % (17179)------------------------------
% 0.20/0.48  % (17179)------------------------------
% 0.20/0.48  % (17183)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.48  % (17195)Refutation not found, incomplete strategy% (17195)------------------------------
% 0.20/0.48  % (17195)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (17195)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (17195)Memory used [KB]: 10746
% 0.20/0.48  % (17195)Time elapsed: 0.082 s
% 0.20/0.48  % (17195)------------------------------
% 0.20/0.48  % (17195)------------------------------
% 0.20/0.48  % (17183)Refutation not found, incomplete strategy% (17183)------------------------------
% 0.20/0.48  % (17183)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (17183)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (17183)Memory used [KB]: 10618
% 0.20/0.48  % (17183)Time elapsed: 0.091 s
% 0.20/0.48  % (17183)------------------------------
% 0.20/0.48  % (17183)------------------------------
% 0.20/0.49  % (17182)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.49  % (17180)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.50  % (17170)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.50  % (17188)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.50  % (17194)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.50  % (17171)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.50  % (17175)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.50  % (17178)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.50  % (17192)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.51  % (17174)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.51  % (17168)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.51  % (17187)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % (17192)Refutation not found, incomplete strategy% (17192)------------------------------
% 0.20/0.51  % (17192)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (17177)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.51  % (17196)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.51  % (17196)Refutation not found, incomplete strategy% (17196)------------------------------
% 0.20/0.51  % (17196)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (17196)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (17196)Memory used [KB]: 1663
% 0.20/0.51  % (17196)Time elapsed: 0.089 s
% 0.20/0.51  % (17196)------------------------------
% 0.20/0.51  % (17196)------------------------------
% 0.20/0.51  % (17192)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (17192)Memory used [KB]: 6268
% 0.20/0.51  % (17192)Time elapsed: 0.110 s
% 0.20/0.51  % (17192)------------------------------
% 0.20/0.51  % (17192)------------------------------
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f697,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f91,f96,f101,f106,f112,f135,f182,f188,f196,f220,f263,f535,f696])).
% 0.20/0.51  fof(f696,plain,(
% 0.20/0.51    ~spl6_17),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f695])).
% 0.20/0.51  fof(f695,plain,(
% 0.20/0.51    $false | ~spl6_17),
% 0.20/0.51    inference(subsumption_resolution,[],[f685,f119])).
% 0.20/0.51  fof(f119,plain,(
% 0.20/0.51    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f44,f50])).
% 0.20/0.51  fof(f50,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f19])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,axiom,(
% 0.20/0.51    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.20/0.51  fof(f44,plain,(
% 0.20/0.51    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.51  fof(f685,plain,(
% 0.20/0.51    r2_hidden(sK1,k1_xboole_0) | ~spl6_17),
% 0.20/0.51    inference(superposition,[],[f83,f219])).
% 0.20/0.51  fof(f219,plain,(
% 0.20/0.51    k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) | ~spl6_17),
% 0.20/0.51    inference(avatar_component_clause,[],[f217])).
% 0.20/0.51  fof(f217,plain,(
% 0.20/0.51    spl6_17 <=> k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.20/0.51  fof(f83,plain,(
% 0.20/0.51    ( ! [X4,X0] : (r2_hidden(X4,k1_enumset1(X0,X0,X4))) )),
% 0.20/0.51    inference(equality_resolution,[],[f82])).
% 0.20/0.51  fof(f82,plain,(
% 0.20/0.51    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k1_enumset1(X0,X0,X4) != X2) )),
% 0.20/0.51    inference(equality_resolution,[],[f74])).
% 0.20/0.51  fof(f74,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k1_enumset1(X0,X0,X1) != X2) )),
% 0.20/0.51    inference(definition_unfolding,[],[f64,f48])).
% 0.20/0.51  fof(f48,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.51  fof(f64,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 0.20/0.51    inference(cnf_transformation,[],[f38])).
% 0.20/0.51  % (17189)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.51  fof(f38,plain,(
% 0.20/0.51    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK5(X0,X1,X2) != X1 & sK5(X0,X1,X2) != X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (sK5(X0,X1,X2) = X1 | sK5(X0,X1,X2) = X0 | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f36,f37])).
% 0.20/0.51  fof(f37,plain,(
% 0.20/0.51    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK5(X0,X1,X2) != X1 & sK5(X0,X1,X2) != X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (sK5(X0,X1,X2) = X1 | sK5(X0,X1,X2) = X0 | r2_hidden(sK5(X0,X1,X2),X2))))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f36,plain,(
% 0.20/0.51    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 0.20/0.51    inference(rectify,[],[f35])).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 0.20/0.51    inference(flattening,[],[f34])).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 0.20/0.51    inference(nnf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 0.20/0.51  fof(f535,plain,(
% 0.20/0.51    ~spl6_1 | ~spl6_2 | ~spl6_7 | ~spl6_11 | spl6_12 | ~spl6_21),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f534])).
% 0.20/0.51  fof(f534,plain,(
% 0.20/0.51    $false | (~spl6_1 | ~spl6_2 | ~spl6_7 | ~spl6_11 | spl6_12 | ~spl6_21)),
% 0.20/0.51    inference(subsumption_resolution,[],[f530,f191])).
% 0.20/0.51  fof(f191,plain,(
% 0.20/0.51    ~m1_subset_1(k1_funct_1(sK3,sK2),k1_enumset1(sK1,sK1,sK1)) | spl6_12),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f122,f187,f49])).
% 0.20/0.51  fof(f49,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f18])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.20/0.51    inference(flattening,[],[f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.20/0.51  fof(f187,plain,(
% 0.20/0.51    ~r2_hidden(k1_funct_1(sK3,sK2),k1_enumset1(sK1,sK1,sK1)) | spl6_12),
% 0.20/0.51    inference(avatar_component_clause,[],[f185])).
% 0.20/0.51  fof(f185,plain,(
% 0.20/0.51    spl6_12 <=> r2_hidden(k1_funct_1(sK3,sK2),k1_enumset1(sK1,sK1,sK1))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.20/0.51  fof(f122,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~v1_xboole_0(k1_enumset1(X0,X0,X1))) )),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f83,f46])).
% 0.20/0.51  fof(f46,plain,(
% 0.20/0.51    ( ! [X2,X0] : (~v1_xboole_0(X0) | ~r2_hidden(X2,X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f32])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK4(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f30,f31])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.51    inference(rectify,[],[f29])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.51    inference(nnf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.51  fof(f530,plain,(
% 0.20/0.51    m1_subset_1(k1_funct_1(sK3,sK2),k1_enumset1(sK1,sK1,sK1)) | (~spl6_1 | ~spl6_2 | ~spl6_7 | ~spl6_11 | ~spl6_21)),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f95,f181,f443])).
% 0.20/0.51  fof(f443,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~v5_relat_1(sK3,X1) | m1_subset_1(k1_funct_1(sK3,X0),X1) | ~r2_hidden(X0,sK0)) ) | (~spl6_1 | ~spl6_7 | ~spl6_21)),
% 0.20/0.51    inference(backward_demodulation,[],[f151,f248])).
% 0.20/0.51  % (17177)Refutation not found, incomplete strategy% (17177)------------------------------
% 0.20/0.51  % (17177)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (17177)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (17177)Memory used [KB]: 10746
% 0.20/0.51  % (17177)Time elapsed: 0.111 s
% 0.20/0.51  % (17177)------------------------------
% 0.20/0.51  % (17177)------------------------------
% 0.20/0.51  fof(f248,plain,(
% 0.20/0.51    sK0 = k1_relat_1(sK3) | ~spl6_21),
% 0.20/0.51    inference(avatar_component_clause,[],[f246])).
% 0.20/0.51  fof(f246,plain,(
% 0.20/0.51    spl6_21 <=> sK0 = k1_relat_1(sK3)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 0.20/0.51  fof(f151,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r2_hidden(X0,k1_relat_1(sK3)) | m1_subset_1(k1_funct_1(sK3,X0),X1) | ~v5_relat_1(sK3,X1)) ) | (~spl6_1 | ~spl6_7)),
% 0.20/0.51    inference(subsumption_resolution,[],[f150,f134])).
% 0.20/0.51  fof(f134,plain,(
% 0.20/0.51    v1_relat_1(sK3) | ~spl6_7),
% 0.20/0.51    inference(avatar_component_clause,[],[f132])).
% 0.20/0.51  fof(f132,plain,(
% 0.20/0.51    spl6_7 <=> v1_relat_1(sK3)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.20/0.51  fof(f150,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r2_hidden(X0,k1_relat_1(sK3)) | m1_subset_1(k1_funct_1(sK3,X0),X1) | ~v5_relat_1(sK3,X1) | ~v1_relat_1(sK3)) ) | ~spl6_1),
% 0.20/0.51    inference(resolution,[],[f61,f90])).
% 0.20/0.51  fof(f90,plain,(
% 0.20/0.51    v1_funct_1(sK3) | ~spl6_1),
% 0.20/0.51    inference(avatar_component_clause,[],[f88])).
% 0.20/0.51  fof(f88,plain,(
% 0.20/0.51    spl6_1 <=> v1_funct_1(sK3)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.20/0.51  fof(f61,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~r2_hidden(X1,k1_relat_1(X2)) | m1_subset_1(k1_funct_1(X2,X1),X0) | ~v5_relat_1(X2,X0) | ~v1_relat_1(X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f26])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (m1_subset_1(k1_funct_1(X2,X1),X0) | ~r2_hidden(X1,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v5_relat_1(X2,X0) | ~v1_relat_1(X2))),
% 0.20/0.51    inference(flattening,[],[f25])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ! [X0,X1,X2] : ((m1_subset_1(k1_funct_1(X2,X1),X0) | ~r2_hidden(X1,k1_relat_1(X2))) | (~v1_funct_1(X2) | ~v5_relat_1(X2,X0) | ~v1_relat_1(X2)))),
% 0.20/0.51    inference(ennf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : ((v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) => (r2_hidden(X1,k1_relat_1(X2)) => m1_subset_1(k1_funct_1(X2,X1),X0)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_funct_1)).
% 0.20/0.51  fof(f181,plain,(
% 0.20/0.51    v5_relat_1(sK3,k1_enumset1(sK1,sK1,sK1)) | ~spl6_11),
% 0.20/0.51    inference(avatar_component_clause,[],[f179])).
% 0.20/0.51  fof(f179,plain,(
% 0.20/0.51    spl6_11 <=> v5_relat_1(sK3,k1_enumset1(sK1,sK1,sK1))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.20/0.51  % (17172)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.51  % (17181)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.52  % (17191)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.52  % (17181)Refutation not found, incomplete strategy% (17181)------------------------------
% 0.20/0.52  % (17181)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (17181)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (17181)Memory used [KB]: 1791
% 0.20/0.52  % (17181)Time elapsed: 0.117 s
% 0.20/0.52  % (17181)------------------------------
% 0.20/0.52  % (17181)------------------------------
% 0.20/0.52  % (17186)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.52  % (17176)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.52  fof(f95,plain,(
% 0.20/0.52    r2_hidden(sK2,sK0) | ~spl6_2),
% 0.20/0.52    inference(avatar_component_clause,[],[f93])).
% 0.20/0.52  fof(f93,plain,(
% 0.20/0.52    spl6_2 <=> r2_hidden(sK2,sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.20/0.52  fof(f263,plain,(
% 0.20/0.52    spl6_21 | ~spl6_13 | ~spl6_16),
% 0.20/0.52    inference(avatar_split_clause,[],[f253,f213,f193,f246])).
% 0.20/0.52  fof(f193,plain,(
% 0.20/0.52    spl6_13 <=> k1_relat_1(sK3) = k1_relset_1(sK0,k1_enumset1(sK1,sK1,sK1),sK3)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.20/0.52  fof(f213,plain,(
% 0.20/0.52    spl6_16 <=> sK0 = k1_relset_1(sK0,k1_enumset1(sK1,sK1,sK1),sK3)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.20/0.52  fof(f253,plain,(
% 0.20/0.52    sK0 = k1_relat_1(sK3) | (~spl6_13 | ~spl6_16)),
% 0.20/0.52    inference(backward_demodulation,[],[f195,f215])).
% 0.20/0.52  fof(f215,plain,(
% 0.20/0.52    sK0 = k1_relset_1(sK0,k1_enumset1(sK1,sK1,sK1),sK3) | ~spl6_16),
% 0.20/0.52    inference(avatar_component_clause,[],[f213])).
% 0.20/0.52  fof(f195,plain,(
% 0.20/0.52    k1_relat_1(sK3) = k1_relset_1(sK0,k1_enumset1(sK1,sK1,sK1),sK3) | ~spl6_13),
% 0.20/0.52    inference(avatar_component_clause,[],[f193])).
% 0.20/0.52  fof(f220,plain,(
% 0.20/0.52    spl6_16 | spl6_17 | ~spl6_4 | ~spl6_5),
% 0.20/0.52    inference(avatar_split_clause,[],[f158,f109,f103,f217,f213])).
% 0.20/0.52  fof(f103,plain,(
% 0.20/0.52    spl6_4 <=> v1_funct_2(sK3,sK0,k1_enumset1(sK1,sK1,sK1))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.20/0.52  fof(f109,plain,(
% 0.20/0.52    spl6_5 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1))))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.20/0.52  fof(f158,plain,(
% 0.20/0.52    k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) | sK0 = k1_relset_1(sK0,k1_enumset1(sK1,sK1,sK1),sK3) | (~spl6_4 | ~spl6_5)),
% 0.20/0.52    inference(subsumption_resolution,[],[f157,f105])).
% 0.20/0.52  fof(f105,plain,(
% 0.20/0.52    v1_funct_2(sK3,sK0,k1_enumset1(sK1,sK1,sK1)) | ~spl6_4),
% 0.20/0.52    inference(avatar_component_clause,[],[f103])).
% 0.20/0.52  fof(f157,plain,(
% 0.20/0.52    ~v1_funct_2(sK3,sK0,k1_enumset1(sK1,sK1,sK1)) | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) | sK0 = k1_relset_1(sK0,k1_enumset1(sK1,sK1,sK1),sK3) | ~spl6_5),
% 0.20/0.52    inference(resolution,[],[f55,f111])).
% 0.20/0.52  fof(f111,plain,(
% 0.20/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1)))) | ~spl6_5),
% 0.20/0.52    inference(avatar_component_clause,[],[f109])).
% 0.20/0.52  fof(f55,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f33])).
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.52    inference(nnf_transformation,[],[f24])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.52    inference(flattening,[],[f23])).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.52    inference(ennf_transformation,[],[f12])).
% 0.20/0.52  fof(f12,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.52  fof(f196,plain,(
% 0.20/0.52    spl6_13 | ~spl6_5),
% 0.20/0.52    inference(avatar_split_clause,[],[f148,f109,f193])).
% 0.20/0.52  fof(f148,plain,(
% 0.20/0.52    k1_relat_1(sK3) = k1_relset_1(sK0,k1_enumset1(sK1,sK1,sK1),sK3) | ~spl6_5),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f111,f52])).
% 0.20/0.52  fof(f52,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relat_1(X2) = k1_relset_1(X0,X1,X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f21])).
% 0.20/0.52  % (17173)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (17167)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.52  % (17190)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.52  % (17193)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.53  % (17185)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.53  % (17185)Refutation not found, incomplete strategy% (17185)------------------------------
% 0.20/0.53  % (17185)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  fof(f21,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(ennf_transformation,[],[f11])).
% 0.20/0.53  fof(f11,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.53  fof(f188,plain,(
% 0.20/0.53    ~spl6_12 | spl6_3),
% 0.20/0.53    inference(avatar_split_clause,[],[f138,f98,f185])).
% 0.20/0.53  fof(f98,plain,(
% 0.20/0.53    spl6_3 <=> sK1 = k1_funct_1(sK3,sK2)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.20/0.53  fof(f138,plain,(
% 0.20/0.53    ~r2_hidden(k1_funct_1(sK3,sK2),k1_enumset1(sK1,sK1,sK1)) | spl6_3),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f100,f100,f86])).
% 0.20/0.53  fof(f86,plain,(
% 0.20/0.53    ( ! [X4,X0,X1] : (~r2_hidden(X4,k1_enumset1(X0,X0,X1)) | X0 = X4 | X1 = X4) )),
% 0.20/0.53    inference(equality_resolution,[],[f76])).
% 0.20/0.53  fof(f76,plain,(
% 0.20/0.53    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k1_enumset1(X0,X0,X1) != X2) )),
% 0.20/0.53    inference(definition_unfolding,[],[f62,f48])).
% 0.20/0.53  fof(f62,plain,(
% 0.20/0.53    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 0.20/0.53    inference(cnf_transformation,[],[f38])).
% 0.20/0.53  fof(f100,plain,(
% 0.20/0.53    sK1 != k1_funct_1(sK3,sK2) | spl6_3),
% 0.20/0.53    inference(avatar_component_clause,[],[f98])).
% 0.20/0.53  fof(f182,plain,(
% 0.20/0.53    spl6_11 | ~spl6_5),
% 0.20/0.53    inference(avatar_split_clause,[],[f136,f109,f179])).
% 0.20/0.53  fof(f136,plain,(
% 0.20/0.53    v5_relat_1(sK3,k1_enumset1(sK1,sK1,sK1)) | ~spl6_5),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f111,f54])).
% 0.20/0.53  fof(f54,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f22])).
% 0.20/0.53  fof(f22,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(ennf_transformation,[],[f10])).
% 0.20/0.53  fof(f10,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.53  fof(f135,plain,(
% 0.20/0.53    spl6_7 | ~spl6_5),
% 0.20/0.53    inference(avatar_split_clause,[],[f127,f109,f132])).
% 0.20/0.53  fof(f127,plain,(
% 0.20/0.53    v1_relat_1(sK3) | ~spl6_5),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f111,f51])).
% 1.26/0.53  fof(f51,plain,(
% 1.26/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.26/0.53    inference(cnf_transformation,[],[f20])).
% 1.26/0.53  fof(f20,plain,(
% 1.26/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.26/0.53    inference(ennf_transformation,[],[f9])).
% 1.26/0.53  fof(f9,axiom,(
% 1.26/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.26/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.26/0.53  fof(f112,plain,(
% 1.26/0.53    spl6_5),
% 1.26/0.53    inference(avatar_split_clause,[],[f69,f109])).
% 1.26/0.53  fof(f69,plain,(
% 1.26/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1))))),
% 1.26/0.53    inference(definition_unfolding,[],[f41,f68])).
% 1.26/0.53  fof(f68,plain,(
% 1.26/0.53    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 1.26/0.53    inference(definition_unfolding,[],[f45,f48])).
% 1.26/0.53  fof(f45,plain,(
% 1.26/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.26/0.53    inference(cnf_transformation,[],[f4])).
% 1.26/0.53  fof(f4,axiom,(
% 1.26/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.26/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.26/0.53  fof(f41,plain,(
% 1.26/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))),
% 1.26/0.53    inference(cnf_transformation,[],[f28])).
% 1.26/0.53  fof(f28,plain,(
% 1.26/0.53    sK1 != k1_funct_1(sK3,sK2) & r2_hidden(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_2(sK3,sK0,k1_tarski(sK1)) & v1_funct_1(sK3)),
% 1.26/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f27])).
% 1.26/0.53  fof(f27,plain,(
% 1.26/0.53    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (sK1 != k1_funct_1(sK3,sK2) & r2_hidden(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_2(sK3,sK0,k1_tarski(sK1)) & v1_funct_1(sK3))),
% 1.26/0.53    introduced(choice_axiom,[])).
% 1.26/0.53  fof(f16,plain,(
% 1.26/0.53    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))),
% 1.26/0.53    inference(flattening,[],[f15])).
% 1.26/0.53  fof(f15,plain,(
% 1.26/0.53    ? [X0,X1,X2,X3] : ((k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)))),
% 1.26/0.53    inference(ennf_transformation,[],[f14])).
% 1.26/0.53  fof(f14,negated_conjecture,(
% 1.26/0.53    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 1.26/0.53    inference(negated_conjecture,[],[f13])).
% 1.26/0.53  fof(f13,conjecture,(
% 1.26/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 1.26/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).
% 1.26/0.53  fof(f106,plain,(
% 1.26/0.53    spl6_4),
% 1.26/0.53    inference(avatar_split_clause,[],[f70,f103])).
% 1.26/0.53  fof(f70,plain,(
% 1.26/0.53    v1_funct_2(sK3,sK0,k1_enumset1(sK1,sK1,sK1))),
% 1.26/0.53    inference(definition_unfolding,[],[f40,f68])).
% 1.26/0.53  fof(f40,plain,(
% 1.26/0.53    v1_funct_2(sK3,sK0,k1_tarski(sK1))),
% 1.26/0.53    inference(cnf_transformation,[],[f28])).
% 1.26/0.53  fof(f101,plain,(
% 1.26/0.53    ~spl6_3),
% 1.26/0.53    inference(avatar_split_clause,[],[f43,f98])).
% 1.26/0.53  fof(f43,plain,(
% 1.26/0.53    sK1 != k1_funct_1(sK3,sK2)),
% 1.26/0.53    inference(cnf_transformation,[],[f28])).
% 1.26/0.53  fof(f96,plain,(
% 1.26/0.53    spl6_2),
% 1.26/0.53    inference(avatar_split_clause,[],[f42,f93])).
% 1.26/0.53  fof(f42,plain,(
% 1.26/0.53    r2_hidden(sK2,sK0)),
% 1.26/0.53    inference(cnf_transformation,[],[f28])).
% 1.26/0.53  fof(f91,plain,(
% 1.26/0.53    spl6_1),
% 1.26/0.53    inference(avatar_split_clause,[],[f39,f88])).
% 1.26/0.53  fof(f39,plain,(
% 1.26/0.53    v1_funct_1(sK3)),
% 1.26/0.53    inference(cnf_transformation,[],[f28])).
% 1.26/0.53  % SZS output end Proof for theBenchmark
% 1.26/0.53  % (17187)------------------------------
% 1.26/0.53  % (17187)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.53  % (17187)Termination reason: Refutation
% 1.26/0.53  
% 1.26/0.53  % (17187)Memory used [KB]: 11129
% 1.26/0.53  % (17187)Time elapsed: 0.110 s
% 1.26/0.53  % (17187)------------------------------
% 1.26/0.53  % (17187)------------------------------
% 1.26/0.53  % (17166)Success in time 0.165 s
%------------------------------------------------------------------------------
