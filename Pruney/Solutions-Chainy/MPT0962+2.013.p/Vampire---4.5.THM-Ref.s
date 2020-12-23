%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:23 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.40s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 352 expanded)
%              Number of leaves         :   20 (  95 expanded)
%              Depth                    :   15
%              Number of atoms          :  375 (1479 expanded)
%              Number of equality atoms :   75 ( 403 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f294,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f95,f97,f152,f178,f201,f218,f219,f285,f288,f292])).

fof(f292,plain,
    ( spl3_2
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_14 ),
    inference(avatar_contradiction_clause,[],[f291])).

fof(f291,plain,
    ( $false
    | spl3_2
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f290,f274])).

fof(f274,plain,
    ( ~ v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)
    | spl3_2
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(backward_demodulation,[],[f223,f272])).

fof(f272,plain,
    ( k1_xboole_0 = k1_relat_1(sK1)
    | spl3_2
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f270,f45])).

fof(f45,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
      | ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
      | ~ v1_funct_1(sK1) )
    & r1_tarski(k2_relat_1(sK1),sK0)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f34])).

fof(f34,plain,
    ( ? [X0,X1] :
        ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
          | ~ v1_funct_1(X1) )
        & r1_tarski(k2_relat_1(X1),X0)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
        | ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
        | ~ v1_funct_1(sK1) )
      & r1_tarski(k2_relat_1(sK1),sK0)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
        | ~ v1_funct_1(X1) )
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
        | ~ v1_funct_1(X1) )
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( r1_tarski(k2_relat_1(X1),X0)
         => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
            & v1_funct_2(X1,k1_relat_1(X1),X0)
            & v1_funct_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

fof(f270,plain,
    ( k1_xboole_0 = k1_relat_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl3_2
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(trivial_inequality_removal,[],[f269])).

fof(f269,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl3_2
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(superposition,[],[f51,f246])).

fof(f246,plain,
    ( k1_xboole_0 = k2_relat_1(sK1)
    | spl3_2
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f112,f221])).

fof(f221,plain,
    ( k1_xboole_0 = sK0
    | spl3_2
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f220,f90])).

fof(f90,plain,
    ( ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl3_2
  <=> v1_funct_2(sK1,k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f220,plain,
    ( k1_xboole_0 = sK0
    | v1_funct_2(sK1,k1_relat_1(sK1),sK0)
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f211,f212])).

fof(f212,plain,
    ( k1_relat_1(sK1) = k1_relset_1(k1_relat_1(sK1),sK0,sK1)
    | ~ spl3_3 ),
    inference(resolution,[],[f93,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f93,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl3_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f211,plain,
    ( k1_relat_1(sK1) != k1_relset_1(k1_relat_1(sK1),sK0,sK1)
    | k1_xboole_0 = sK0
    | v1_funct_2(sK1,k1_relat_1(sK1),sK0)
    | ~ spl3_3 ),
    inference(resolution,[],[f93,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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

fof(f112,plain,
    ( sK0 = k2_relat_1(sK1)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl3_5
  <=> sK0 = k2_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f51,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

fof(f223,plain,
    ( ~ v1_funct_2(sK1,k1_relat_1(sK1),k1_xboole_0)
    | spl3_2
    | ~ spl3_3 ),
    inference(backward_demodulation,[],[f90,f221])).

fof(f290,plain,
    ( v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)
    | spl3_2
    | ~ spl3_3
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f171,f221])).

fof(f171,plain,
    ( v1_funct_2(sK1,k1_xboole_0,sK0)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f170])).

fof(f170,plain,
    ( spl3_14
  <=> v1_funct_2(sK1,k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f288,plain,
    ( spl3_2
    | ~ spl3_3
    | ~ spl3_5
    | spl3_13 ),
    inference(avatar_contradiction_clause,[],[f287])).

fof(f287,plain,
    ( $false
    | spl3_2
    | ~ spl3_3
    | ~ spl3_5
    | spl3_13 ),
    inference(subsumption_resolution,[],[f279,f240])).

fof(f240,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK1)
    | spl3_2
    | ~ spl3_3
    | spl3_13 ),
    inference(backward_demodulation,[],[f167,f221])).

fof(f167,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,sK1)
    | spl3_13 ),
    inference(avatar_component_clause,[],[f166])).

fof(f166,plain,
    ( spl3_13
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f279,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK1)
    | spl3_2
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(backward_demodulation,[],[f242,f272])).

fof(f242,plain,
    ( k1_relat_1(sK1) = k1_relset_1(k1_relat_1(sK1),k1_xboole_0,sK1)
    | spl3_2
    | ~ spl3_3 ),
    inference(backward_demodulation,[],[f212,f221])).

fof(f285,plain,
    ( spl3_2
    | ~ spl3_3
    | ~ spl3_5
    | spl3_15 ),
    inference(avatar_contradiction_clause,[],[f284])).

fof(f284,plain,
    ( $false
    | spl3_2
    | ~ spl3_3
    | ~ spl3_5
    | spl3_15 ),
    inference(subsumption_resolution,[],[f273,f77])).

fof(f77,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
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
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f273,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | spl3_2
    | ~ spl3_3
    | ~ spl3_5
    | spl3_15 ),
    inference(backward_demodulation,[],[f176,f272])).

fof(f176,plain,
    ( ~ r1_tarski(k1_relat_1(sK1),k1_xboole_0)
    | spl3_15 ),
    inference(avatar_component_clause,[],[f174])).

fof(f174,plain,
    ( spl3_15
  <=> r1_tarski(k1_relat_1(sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f219,plain,
    ( ~ spl3_4
    | spl3_5 ),
    inference(avatar_split_clause,[],[f206,f110,f106])).

fof(f106,plain,
    ( spl3_4
  <=> r1_tarski(sK0,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f206,plain,
    ( sK0 = k2_relat_1(sK1)
    | ~ r1_tarski(sK0,k2_relat_1(sK1)) ),
    inference(resolution,[],[f47,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f47,plain,(
    r1_tarski(k2_relat_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f218,plain,
    ( spl3_2
    | ~ spl3_3
    | spl3_10 ),
    inference(avatar_contradiction_clause,[],[f217])).

fof(f217,plain,
    ( $false
    | spl3_2
    | ~ spl3_3
    | spl3_10 ),
    inference(subsumption_resolution,[],[f212,f216])).

fof(f216,plain,
    ( k1_relat_1(sK1) != k1_relset_1(k1_relat_1(sK1),sK0,sK1)
    | spl3_2
    | ~ spl3_3
    | spl3_10 ),
    inference(subsumption_resolution,[],[f215,f90])).

fof(f215,plain,
    ( k1_relat_1(sK1) != k1_relset_1(k1_relat_1(sK1),sK0,sK1)
    | v1_funct_2(sK1,k1_relat_1(sK1),sK0)
    | ~ spl3_3
    | spl3_10 ),
    inference(subsumption_resolution,[],[f211,f155])).

fof(f155,plain,
    ( k1_xboole_0 != sK0
    | spl3_10 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl3_10
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f201,plain,
    ( spl3_4
    | ~ spl3_10 ),
    inference(avatar_contradiction_clause,[],[f200])).

% (3417)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
fof(f200,plain,
    ( $false
    | spl3_4
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f192,f49])).

fof(f49,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f192,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl3_4
    | ~ spl3_10 ),
    inference(backward_demodulation,[],[f137,f156])).

fof(f156,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f154])).

fof(f137,plain,
    ( ~ v1_xboole_0(sK0)
    | spl3_4 ),
    inference(resolution,[],[f132,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f132,plain,
    ( r2_hidden(sK2(sK0,k2_relat_1(sK1)),sK0)
    | spl3_4 ),
    inference(resolution,[],[f108,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f40,f41])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f39])).

% (3432)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% (3435)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% (3418)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% (3423)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% (3429)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% (3424)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% (3428)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% (3438)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% (3436)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% (3430)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f108,plain,
    ( ~ r1_tarski(sK0,k2_relat_1(sK1))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f106])).

fof(f178,plain,
    ( spl3_14
    | ~ spl3_13
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f148,f174,f166,f170])).

fof(f148,plain,
    ( ~ r1_tarski(k1_relat_1(sK1),k1_xboole_0)
    | k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,sK1)
    | v1_funct_2(sK1,k1_xboole_0,sK0) ),
    inference(resolution,[],[f104,f81])).

fof(f81,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f104,plain,(
    ! [X0] :
      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
      | ~ r1_tarski(k1_relat_1(sK1),X0) ) ),
    inference(subsumption_resolution,[],[f98,f45])).

fof(f98,plain,(
    ! [X0] :
      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
      | ~ r1_tarski(k1_relat_1(sK1),X0)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f47,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X2),X1)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

fof(f152,plain,(
    spl3_3 ),
    inference(avatar_contradiction_clause,[],[f151])).

fof(f151,plain,
    ( $false
    | spl3_3 ),
    inference(subsumption_resolution,[],[f143,f77])).

fof(f143,plain,
    ( ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1))
    | spl3_3 ),
    inference(resolution,[],[f104,f94])).

fof(f94,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f92])).

fof(f97,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f96])).

fof(f96,plain,
    ( $false
    | spl3_1 ),
    inference(subsumption_resolution,[],[f86,f46])).

fof(f46,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f86,plain,
    ( ~ v1_funct_1(sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl3_1
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f95,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f48,f92,f88,f84])).

fof(f48,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
    | ~ v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:09:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.52  % (3420)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.52  % (3422)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.53  % (3437)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.53  % (3425)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.53  % (3415)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.54  % (3427)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.54  % (3441)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.54  % (3440)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.54  % (3433)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.54  % (3413)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.54  % (3416)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.54  % (3439)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.54  % (3421)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.54  % (3434)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.54  % (3419)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.54  % (3426)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.54  % (3412)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.55  % (3431)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.55  % (3414)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.55  % (3420)Refutation found. Thanks to Tanya!
% 0.20/0.55  % SZS status Theorem for theBenchmark
% 0.20/0.55  % SZS output start Proof for theBenchmark
% 0.20/0.55  fof(f294,plain,(
% 0.20/0.55    $false),
% 0.20/0.55    inference(avatar_sat_refutation,[],[f95,f97,f152,f178,f201,f218,f219,f285,f288,f292])).
% 0.20/0.55  fof(f292,plain,(
% 0.20/0.55    spl3_2 | ~spl3_3 | ~spl3_5 | ~spl3_14),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f291])).
% 0.20/0.55  fof(f291,plain,(
% 0.20/0.55    $false | (spl3_2 | ~spl3_3 | ~spl3_5 | ~spl3_14)),
% 0.20/0.55    inference(subsumption_resolution,[],[f290,f274])).
% 0.20/0.55  fof(f274,plain,(
% 0.20/0.55    ~v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) | (spl3_2 | ~spl3_3 | ~spl3_5)),
% 0.20/0.55    inference(backward_demodulation,[],[f223,f272])).
% 0.20/0.55  fof(f272,plain,(
% 0.20/0.55    k1_xboole_0 = k1_relat_1(sK1) | (spl3_2 | ~spl3_3 | ~spl3_5)),
% 0.20/0.55    inference(subsumption_resolution,[],[f270,f45])).
% 0.20/0.55  fof(f45,plain,(
% 0.20/0.55    v1_relat_1(sK1)),
% 0.20/0.55    inference(cnf_transformation,[],[f35])).
% 0.20/0.55  fof(f35,plain,(
% 0.20/0.55    (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | ~v1_funct_2(sK1,k1_relat_1(sK1),sK0) | ~v1_funct_1(sK1)) & r1_tarski(k2_relat_1(sK1),sK0) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 0.20/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f34])).
% 0.20/0.55  fof(f34,plain,(
% 0.20/0.55    ? [X0,X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0) & v1_funct_1(X1) & v1_relat_1(X1)) => ((~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | ~v1_funct_2(sK1,k1_relat_1(sK1),sK0) | ~v1_funct_1(sK1)) & r1_tarski(k2_relat_1(sK1),sK0) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f20,plain,(
% 0.20/0.55    ? [X0,X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.20/0.55    inference(flattening,[],[f19])).
% 0.20/0.55  fof(f19,plain,(
% 0.20/0.55    ? [X0,X1] : (((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.20/0.55    inference(ennf_transformation,[],[f17])).
% 0.20/0.55  fof(f17,negated_conjecture,(
% 0.20/0.55    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.20/0.55    inference(negated_conjecture,[],[f16])).
% 0.20/0.55  fof(f16,conjecture,(
% 0.20/0.55    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).
% 0.20/0.55  fof(f270,plain,(
% 0.20/0.55    k1_xboole_0 = k1_relat_1(sK1) | ~v1_relat_1(sK1) | (spl3_2 | ~spl3_3 | ~spl3_5)),
% 0.20/0.55    inference(trivial_inequality_removal,[],[f269])).
% 0.20/0.55  fof(f269,plain,(
% 0.20/0.55    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k1_relat_1(sK1) | ~v1_relat_1(sK1) | (spl3_2 | ~spl3_3 | ~spl3_5)),
% 0.20/0.55    inference(superposition,[],[f51,f246])).
% 0.20/0.55  fof(f246,plain,(
% 0.20/0.55    k1_xboole_0 = k2_relat_1(sK1) | (spl3_2 | ~spl3_3 | ~spl3_5)),
% 0.20/0.55    inference(forward_demodulation,[],[f112,f221])).
% 0.20/0.55  fof(f221,plain,(
% 0.20/0.55    k1_xboole_0 = sK0 | (spl3_2 | ~spl3_3)),
% 0.20/0.55    inference(subsumption_resolution,[],[f220,f90])).
% 0.20/0.55  fof(f90,plain,(
% 0.20/0.55    ~v1_funct_2(sK1,k1_relat_1(sK1),sK0) | spl3_2),
% 0.20/0.55    inference(avatar_component_clause,[],[f88])).
% 0.20/0.55  fof(f88,plain,(
% 0.20/0.55    spl3_2 <=> v1_funct_2(sK1,k1_relat_1(sK1),sK0)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.55  fof(f220,plain,(
% 0.20/0.55    k1_xboole_0 = sK0 | v1_funct_2(sK1,k1_relat_1(sK1),sK0) | ~spl3_3),
% 0.20/0.55    inference(subsumption_resolution,[],[f211,f212])).
% 0.20/0.55  fof(f212,plain,(
% 0.20/0.55    k1_relat_1(sK1) = k1_relset_1(k1_relat_1(sK1),sK0,sK1) | ~spl3_3),
% 0.20/0.55    inference(resolution,[],[f93,f68])).
% 0.20/0.55  fof(f68,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f29])).
% 0.20/0.55  fof(f29,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.55    inference(ennf_transformation,[],[f13])).
% 0.20/0.55  fof(f13,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.55  fof(f93,plain,(
% 0.20/0.55    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | ~spl3_3),
% 0.20/0.55    inference(avatar_component_clause,[],[f92])).
% 0.20/0.55  fof(f92,plain,(
% 0.20/0.55    spl3_3 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.55  fof(f211,plain,(
% 0.20/0.55    k1_relat_1(sK1) != k1_relset_1(k1_relat_1(sK1),sK0,sK1) | k1_xboole_0 = sK0 | v1_funct_2(sK1,k1_relat_1(sK1),sK0) | ~spl3_3),
% 0.20/0.55    inference(resolution,[],[f93,f71])).
% 0.20/0.55  fof(f71,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | v1_funct_2(X2,X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f44])).
% 0.20/0.55  fof(f44,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.55    inference(nnf_transformation,[],[f31])).
% 0.20/0.55  fof(f31,plain,(
% 0.20/0.55    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.55    inference(flattening,[],[f30])).
% 0.20/0.55  fof(f30,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.55    inference(ennf_transformation,[],[f15])).
% 0.20/0.55  fof(f15,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.55  fof(f112,plain,(
% 0.20/0.55    sK0 = k2_relat_1(sK1) | ~spl3_5),
% 0.20/0.55    inference(avatar_component_clause,[],[f110])).
% 0.20/0.55  fof(f110,plain,(
% 0.20/0.55    spl3_5 <=> sK0 = k2_relat_1(sK1)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.55  fof(f51,plain,(
% 0.20/0.55    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f36])).
% 0.20/0.55  fof(f36,plain,(
% 0.20/0.55    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.55    inference(nnf_transformation,[],[f21])).
% 0.20/0.55  fof(f21,plain,(
% 0.20/0.55    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f12])).
% 0.20/0.55  fof(f12,axiom,(
% 0.20/0.55    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).
% 0.20/0.55  fof(f223,plain,(
% 0.20/0.55    ~v1_funct_2(sK1,k1_relat_1(sK1),k1_xboole_0) | (spl3_2 | ~spl3_3)),
% 0.20/0.55    inference(backward_demodulation,[],[f90,f221])).
% 0.20/0.55  fof(f290,plain,(
% 0.20/0.55    v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) | (spl3_2 | ~spl3_3 | ~spl3_14)),
% 0.20/0.55    inference(forward_demodulation,[],[f171,f221])).
% 0.20/0.55  fof(f171,plain,(
% 0.20/0.55    v1_funct_2(sK1,k1_xboole_0,sK0) | ~spl3_14),
% 0.20/0.55    inference(avatar_component_clause,[],[f170])).
% 0.20/0.55  fof(f170,plain,(
% 0.20/0.55    spl3_14 <=> v1_funct_2(sK1,k1_xboole_0,sK0)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.20/0.55  fof(f288,plain,(
% 0.20/0.55    spl3_2 | ~spl3_3 | ~spl3_5 | spl3_13),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f287])).
% 0.20/0.55  fof(f287,plain,(
% 0.20/0.55    $false | (spl3_2 | ~spl3_3 | ~spl3_5 | spl3_13)),
% 0.20/0.55    inference(subsumption_resolution,[],[f279,f240])).
% 0.20/0.55  fof(f240,plain,(
% 0.20/0.55    k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) | (spl3_2 | ~spl3_3 | spl3_13)),
% 0.20/0.55    inference(backward_demodulation,[],[f167,f221])).
% 0.20/0.55  fof(f167,plain,(
% 0.20/0.55    k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,sK1) | spl3_13),
% 0.20/0.55    inference(avatar_component_clause,[],[f166])).
% 0.20/0.55  fof(f166,plain,(
% 0.20/0.55    spl3_13 <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,sK0,sK1)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.20/0.55  fof(f279,plain,(
% 0.20/0.55    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) | (spl3_2 | ~spl3_3 | ~spl3_5)),
% 0.20/0.55    inference(backward_demodulation,[],[f242,f272])).
% 0.20/0.55  fof(f242,plain,(
% 0.20/0.55    k1_relat_1(sK1) = k1_relset_1(k1_relat_1(sK1),k1_xboole_0,sK1) | (spl3_2 | ~spl3_3)),
% 0.20/0.55    inference(backward_demodulation,[],[f212,f221])).
% 0.20/0.55  fof(f285,plain,(
% 0.20/0.55    spl3_2 | ~spl3_3 | ~spl3_5 | spl3_15),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f284])).
% 0.20/0.55  fof(f284,plain,(
% 0.20/0.55    $false | (spl3_2 | ~spl3_3 | ~spl3_5 | spl3_15)),
% 0.20/0.55    inference(subsumption_resolution,[],[f273,f77])).
% 0.20/0.55  fof(f77,plain,(
% 0.20/0.55    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.55    inference(equality_resolution,[],[f59])).
% 0.20/0.55  fof(f59,plain,(
% 0.20/0.55    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.20/0.55    inference(cnf_transformation,[],[f38])).
% 0.20/0.55  fof(f38,plain,(
% 0.20/0.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.55    inference(flattening,[],[f37])).
% 0.20/0.55  fof(f37,plain,(
% 0.20/0.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.55    inference(nnf_transformation,[],[f4])).
% 0.20/0.55  fof(f4,axiom,(
% 0.20/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.55  fof(f273,plain,(
% 0.20/0.55    ~r1_tarski(k1_xboole_0,k1_xboole_0) | (spl3_2 | ~spl3_3 | ~spl3_5 | spl3_15)),
% 0.20/0.55    inference(backward_demodulation,[],[f176,f272])).
% 0.20/0.55  fof(f176,plain,(
% 0.20/0.55    ~r1_tarski(k1_relat_1(sK1),k1_xboole_0) | spl3_15),
% 0.20/0.55    inference(avatar_component_clause,[],[f174])).
% 0.20/0.55  fof(f174,plain,(
% 0.20/0.55    spl3_15 <=> r1_tarski(k1_relat_1(sK1),k1_xboole_0)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.20/0.55  fof(f219,plain,(
% 0.20/0.55    ~spl3_4 | spl3_5),
% 0.20/0.55    inference(avatar_split_clause,[],[f206,f110,f106])).
% 0.20/0.55  fof(f106,plain,(
% 0.20/0.55    spl3_4 <=> r1_tarski(sK0,k2_relat_1(sK1))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.55  fof(f206,plain,(
% 0.20/0.55    sK0 = k2_relat_1(sK1) | ~r1_tarski(sK0,k2_relat_1(sK1))),
% 0.20/0.55    inference(resolution,[],[f47,f61])).
% 0.20/0.55  fof(f61,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f38])).
% 0.20/0.55  fof(f47,plain,(
% 0.20/0.55    r1_tarski(k2_relat_1(sK1),sK0)),
% 0.20/0.55    inference(cnf_transformation,[],[f35])).
% 0.20/0.55  fof(f218,plain,(
% 0.20/0.55    spl3_2 | ~spl3_3 | spl3_10),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f217])).
% 0.20/0.55  fof(f217,plain,(
% 0.20/0.55    $false | (spl3_2 | ~spl3_3 | spl3_10)),
% 0.20/0.55    inference(subsumption_resolution,[],[f212,f216])).
% 0.20/0.55  fof(f216,plain,(
% 0.20/0.55    k1_relat_1(sK1) != k1_relset_1(k1_relat_1(sK1),sK0,sK1) | (spl3_2 | ~spl3_3 | spl3_10)),
% 0.20/0.55    inference(subsumption_resolution,[],[f215,f90])).
% 0.20/0.55  fof(f215,plain,(
% 0.20/0.55    k1_relat_1(sK1) != k1_relset_1(k1_relat_1(sK1),sK0,sK1) | v1_funct_2(sK1,k1_relat_1(sK1),sK0) | (~spl3_3 | spl3_10)),
% 0.20/0.55    inference(subsumption_resolution,[],[f211,f155])).
% 0.20/0.55  fof(f155,plain,(
% 0.20/0.55    k1_xboole_0 != sK0 | spl3_10),
% 0.20/0.55    inference(avatar_component_clause,[],[f154])).
% 0.20/0.55  fof(f154,plain,(
% 0.20/0.55    spl3_10 <=> k1_xboole_0 = sK0),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.55  fof(f201,plain,(
% 0.20/0.55    spl3_4 | ~spl3_10),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f200])).
% 0.20/0.55  % (3417)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.55  fof(f200,plain,(
% 0.20/0.55    $false | (spl3_4 | ~spl3_10)),
% 0.20/0.55    inference(subsumption_resolution,[],[f192,f49])).
% 0.20/0.55  fof(f49,plain,(
% 0.20/0.55    v1_xboole_0(k1_xboole_0)),
% 0.20/0.55    inference(cnf_transformation,[],[f3])).
% 0.20/0.55  fof(f3,axiom,(
% 0.20/0.55    v1_xboole_0(k1_xboole_0)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.55  fof(f192,plain,(
% 0.20/0.55    ~v1_xboole_0(k1_xboole_0) | (spl3_4 | ~spl3_10)),
% 0.20/0.55    inference(backward_demodulation,[],[f137,f156])).
% 0.20/0.55  fof(f156,plain,(
% 0.20/0.55    k1_xboole_0 = sK0 | ~spl3_10),
% 0.20/0.55    inference(avatar_component_clause,[],[f154])).
% 0.20/0.55  fof(f137,plain,(
% 0.20/0.55    ~v1_xboole_0(sK0) | spl3_4),
% 0.20/0.55    inference(resolution,[],[f132,f55])).
% 0.20/0.55  fof(f55,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f25])).
% 0.20/0.55  fof(f25,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f18])).
% 0.20/0.55  fof(f18,plain,(
% 0.20/0.55    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.55    inference(unused_predicate_definition_removal,[],[f1])).
% 0.20/0.55  fof(f1,axiom,(
% 0.20/0.55    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.55  fof(f132,plain,(
% 0.20/0.55    r2_hidden(sK2(sK0,k2_relat_1(sK1)),sK0) | spl3_4),
% 0.20/0.55    inference(resolution,[],[f108,f63])).
% 0.20/0.55  fof(f63,plain,(
% 0.20/0.55    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK2(X0,X1),X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f42])).
% 0.20/0.55  fof(f42,plain,(
% 0.20/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f40,f41])).
% 0.20/0.55  fof(f41,plain,(
% 0.20/0.55    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f40,plain,(
% 0.20/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.55    inference(rectify,[],[f39])).
% 0.20/0.55  % (3432)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.55  % (3435)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.55  % (3418)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.55  % (3423)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.55  % (3429)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.56  % (3424)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.56  % (3428)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.56  % (3438)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.56  % (3436)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.56  % (3430)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.40/0.57  fof(f39,plain,(
% 1.40/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.40/0.57    inference(nnf_transformation,[],[f26])).
% 1.40/0.57  fof(f26,plain,(
% 1.40/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.40/0.57    inference(ennf_transformation,[],[f2])).
% 1.40/0.57  fof(f2,axiom,(
% 1.40/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.40/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.40/0.57  fof(f108,plain,(
% 1.40/0.57    ~r1_tarski(sK0,k2_relat_1(sK1)) | spl3_4),
% 1.40/0.57    inference(avatar_component_clause,[],[f106])).
% 1.40/0.57  fof(f178,plain,(
% 1.40/0.57    spl3_14 | ~spl3_13 | ~spl3_15),
% 1.40/0.57    inference(avatar_split_clause,[],[f148,f174,f166,f170])).
% 1.40/0.57  fof(f148,plain,(
% 1.40/0.57    ~r1_tarski(k1_relat_1(sK1),k1_xboole_0) | k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,sK1) | v1_funct_2(sK1,k1_xboole_0,sK0)),
% 1.40/0.57    inference(resolution,[],[f104,f81])).
% 1.40/0.57  fof(f81,plain,(
% 1.40/0.57    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1)) )),
% 1.40/0.57    inference(equality_resolution,[],[f72])).
% 1.40/0.57  fof(f72,plain,(
% 1.40/0.57    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.40/0.57    inference(cnf_transformation,[],[f44])).
% 1.40/0.57  fof(f104,plain,(
% 1.40/0.57    ( ! [X0] : (m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) | ~r1_tarski(k1_relat_1(sK1),X0)) )),
% 1.40/0.57    inference(subsumption_resolution,[],[f98,f45])).
% 1.40/0.57  fof(f98,plain,(
% 1.40/0.57    ( ! [X0] : (m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) | ~r1_tarski(k1_relat_1(sK1),X0) | ~v1_relat_1(sK1)) )),
% 1.40/0.57    inference(resolution,[],[f47,f67])).
% 1.40/0.57  fof(f67,plain,(
% 1.40/0.57    ( ! [X2,X0,X1] : (~r1_tarski(k2_relat_1(X2),X1) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 1.40/0.57    inference(cnf_transformation,[],[f28])).
% 1.40/0.57  fof(f28,plain,(
% 1.40/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 1.40/0.57    inference(flattening,[],[f27])).
% 1.40/0.57  fof(f27,plain,(
% 1.40/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 1.40/0.57    inference(ennf_transformation,[],[f14])).
% 1.40/0.57  fof(f14,axiom,(
% 1.40/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.40/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).
% 1.40/0.57  fof(f152,plain,(
% 1.40/0.57    spl3_3),
% 1.40/0.57    inference(avatar_contradiction_clause,[],[f151])).
% 1.40/0.57  fof(f151,plain,(
% 1.40/0.57    $false | spl3_3),
% 1.40/0.57    inference(subsumption_resolution,[],[f143,f77])).
% 1.40/0.57  fof(f143,plain,(
% 1.40/0.57    ~r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) | spl3_3),
% 1.40/0.57    inference(resolution,[],[f104,f94])).
% 1.40/0.57  fof(f94,plain,(
% 1.40/0.57    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | spl3_3),
% 1.40/0.57    inference(avatar_component_clause,[],[f92])).
% 1.40/0.57  fof(f97,plain,(
% 1.40/0.57    spl3_1),
% 1.40/0.57    inference(avatar_contradiction_clause,[],[f96])).
% 1.40/0.57  fof(f96,plain,(
% 1.40/0.57    $false | spl3_1),
% 1.40/0.57    inference(subsumption_resolution,[],[f86,f46])).
% 1.40/0.57  fof(f46,plain,(
% 1.40/0.57    v1_funct_1(sK1)),
% 1.40/0.57    inference(cnf_transformation,[],[f35])).
% 1.40/0.57  fof(f86,plain,(
% 1.40/0.57    ~v1_funct_1(sK1) | spl3_1),
% 1.40/0.57    inference(avatar_component_clause,[],[f84])).
% 1.40/0.57  fof(f84,plain,(
% 1.40/0.57    spl3_1 <=> v1_funct_1(sK1)),
% 1.40/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.40/0.57  fof(f95,plain,(
% 1.40/0.57    ~spl3_1 | ~spl3_2 | ~spl3_3),
% 1.40/0.57    inference(avatar_split_clause,[],[f48,f92,f88,f84])).
% 1.40/0.57  fof(f48,plain,(
% 1.40/0.57    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | ~v1_funct_2(sK1,k1_relat_1(sK1),sK0) | ~v1_funct_1(sK1)),
% 1.40/0.57    inference(cnf_transformation,[],[f35])).
% 1.40/0.57  % SZS output end Proof for theBenchmark
% 1.40/0.57  % (3420)------------------------------
% 1.40/0.57  % (3420)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.57  % (3420)Termination reason: Refutation
% 1.40/0.57  
% 1.40/0.57  % (3420)Memory used [KB]: 10746
% 1.40/0.57  % (3420)Time elapsed: 0.133 s
% 1.40/0.57  % (3420)------------------------------
% 1.40/0.57  % (3420)------------------------------
% 1.40/0.57  % (3411)Success in time 0.209 s
%------------------------------------------------------------------------------
