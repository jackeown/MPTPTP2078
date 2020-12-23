%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:21 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 149 expanded)
%              Number of leaves         :   17 (  47 expanded)
%              Depth                    :   19
%              Number of atoms          :  216 ( 439 expanded)
%              Number of equality atoms :   72 ( 162 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f178,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f59,f63,f110,f124,f148,f167])).

fof(f167,plain,(
    ~ spl3_6 ),
    inference(avatar_contradiction_clause,[],[f165])).

fof(f165,plain,
    ( $false
    | ~ spl3_6 ),
    inference(resolution,[],[f108,f65])).

fof(f65,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f36,f45])).

fof(f45,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f36,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f108,plain,
    ( r2_hidden(k3_subset_1(sK0,sK2(k7_setfam_1(sK0,k1_xboole_0))),k1_xboole_0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl3_6
  <=> r2_hidden(k3_subset_1(sK0,sK2(k7_setfam_1(sK0,k1_xboole_0))),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f148,plain,(
    ~ spl3_8 ),
    inference(avatar_contradiction_clause,[],[f146])).

fof(f146,plain,
    ( $false
    | ~ spl3_8 ),
    inference(resolution,[],[f123,f65])).

fof(f123,plain,
    ( r2_hidden(k3_subset_1(sK0,sK2(sK1)),k1_xboole_0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl3_8
  <=> r2_hidden(k3_subset_1(sK0,sK2(sK1)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f124,plain,
    ( ~ spl3_4
    | spl3_2
    | spl3_8
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f116,f48,f122,f51,f61])).

fof(f61,plain,
    ( spl3_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f51,plain,
    ( spl3_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f48,plain,
    ( spl3_1
  <=> k1_xboole_0 = k7_setfam_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f116,plain,
    ( r2_hidden(k3_subset_1(sK0,sK2(sK1)),k1_xboole_0)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_1 ),
    inference(superposition,[],[f83,f49])).

fof(f49,plain,
    ( k1_xboole_0 = k7_setfam_1(sK0,sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f48])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r2_hidden(k3_subset_1(X1,sK2(X0)),k7_setfam_1(X1,X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) ) ),
    inference(duplicate_literal_removal,[],[f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
      | k1_xboole_0 = X0
      | r2_hidden(k3_subset_1(X1,sK2(X0)),k7_setfam_1(X1,X0))
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f81,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f81,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k1_xboole_0 = X1
      | r2_hidden(k3_subset_1(X0,sK2(X1)),k7_setfam_1(X0,X1)) ) ),
    inference(duplicate_literal_removal,[],[f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r2_hidden(k3_subset_1(X0,sK2(X1)),k7_setfam_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k1_xboole_0 = X1
      | v1_xboole_0(X1) ) ),
    inference(resolution,[],[f79,f35])).

fof(f35,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK2(X0),X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f23])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ? [X1] : r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
     => v1_xboole_0(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK2(X0),X2)
      | r2_hidden(k3_subset_1(X1,sK2(X0)),k7_setfam_1(X1,X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f78,f34])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | r2_hidden(k3_subset_1(X0,sK2(X1)),k7_setfam_1(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ r2_hidden(sK2(X1),X2) ) ),
    inference(resolution,[],[f77,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f19])).

% (22426)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2(X1),k1_zfmisc_1(X0))
      | r2_hidden(k3_subset_1(X0,sK2(X1)),k7_setfam_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | v1_xboole_0(X1) ) ),
    inference(resolution,[],[f40,f35])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
              | ~ r2_hidden(X2,X1) )
            & ( r2_hidden(X2,X1)
              | ~ r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
          <=> r2_hidden(X2,X1) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
          <=> r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_setfam_1)).

fof(f110,plain,
    ( spl3_6
    | spl3_3
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f105,f61,f51,f57,f107])).

fof(f57,plain,
    ( spl3_3
  <=> k1_xboole_0 = k7_setfam_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f105,plain,
    ( k1_xboole_0 = k7_setfam_1(sK0,k1_xboole_0)
    | r2_hidden(k3_subset_1(sK0,sK2(k7_setfam_1(sK0,k1_xboole_0))),k1_xboole_0)
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f104,f52])).

fof(f52,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f51])).

fof(f104,plain,
    ( r2_hidden(k3_subset_1(sK0,sK2(k7_setfam_1(sK0,k1_xboole_0))),k1_xboole_0)
    | k1_xboole_0 = k7_setfam_1(sK0,sK1)
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f100,f52])).

fof(f100,plain,
    ( r2_hidden(k3_subset_1(sK0,sK2(k7_setfam_1(sK0,sK1))),sK1)
    | k1_xboole_0 = k7_setfam_1(sK0,sK1)
    | ~ spl3_4 ),
    inference(resolution,[],[f99,f62])).

fof(f62,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f61])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | r2_hidden(k3_subset_1(X0,sK2(k7_setfam_1(X0,X1))),X1)
      | k1_xboole_0 = k7_setfam_1(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_setfam_1(X0,X1)
      | r2_hidden(k3_subset_1(X0,sK2(k7_setfam_1(X0,X1))),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(resolution,[],[f86,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_setfam_1)).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k1_xboole_0 = k7_setfam_1(X0,X1)
      | r2_hidden(k3_subset_1(X0,sK2(k7_setfam_1(X0,X1))),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(superposition,[],[f83,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

fof(f63,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f28,f61])).

fof(f28,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ( ( k1_xboole_0 = sK1
        & k1_xboole_0 != k7_setfam_1(sK0,sK1) )
      | ( k1_xboole_0 = k7_setfam_1(sK0,sK1)
        & k1_xboole_0 != sK1 ) )
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f21])).

fof(f21,plain,
    ( ? [X0,X1] :
        ( ( ( k1_xboole_0 = X1
            & k1_xboole_0 != k7_setfam_1(X0,X1) )
          | ( k1_xboole_0 = k7_setfam_1(X0,X1)
            & k1_xboole_0 != X1 ) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( ( ( k1_xboole_0 = sK1
          & k1_xboole_0 != k7_setfam_1(sK0,sK1) )
        | ( k1_xboole_0 = k7_setfam_1(sK0,sK1)
          & k1_xboole_0 != sK1 ) )
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ( ( k1_xboole_0 = X1
          & k1_xboole_0 != k7_setfam_1(X0,X1) )
        | ( k1_xboole_0 = k7_setfam_1(X0,X1)
          & k1_xboole_0 != X1 ) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ( ~ ( k1_xboole_0 = X1
              & k1_xboole_0 != k7_setfam_1(X0,X1) )
          & ~ ( k1_xboole_0 = k7_setfam_1(X0,X1)
              & k1_xboole_0 != X1 ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ~ ( k1_xboole_0 = X1
            & k1_xboole_0 != k7_setfam_1(X0,X1) )
        & ~ ( k1_xboole_0 = k7_setfam_1(X0,X1)
            & k1_xboole_0 != X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_tops_2)).

fof(f59,plain,
    ( ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f54,f57,f51])).

fof(f54,plain,
    ( k1_xboole_0 != k7_setfam_1(sK0,k1_xboole_0)
    | k1_xboole_0 != sK1 ),
    inference(inner_rewriting,[],[f29])).

fof(f29,plain,
    ( k1_xboole_0 != k7_setfam_1(sK0,sK1)
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f22])).

fof(f53,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f32,f51,f48])).

fof(f32,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = k7_setfam_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n012.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 14:46:22 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.52  % (22438)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.52  % (22427)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.52  % (22430)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.53  % (22428)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.53  % (22435)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.53  % (22435)Refutation not found, incomplete strategy% (22435)------------------------------
% 0.22/0.53  % (22435)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (22435)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (22435)Memory used [KB]: 6012
% 0.22/0.53  % (22435)Time elapsed: 0.074 s
% 0.22/0.53  % (22435)------------------------------
% 0.22/0.53  % (22435)------------------------------
% 0.22/0.53  % (22428)Refutation not found, incomplete strategy% (22428)------------------------------
% 0.22/0.53  % (22428)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (22428)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (22428)Memory used [KB]: 10618
% 0.22/0.53  % (22428)Time elapsed: 0.074 s
% 0.22/0.53  % (22428)------------------------------
% 0.22/0.53  % (22428)------------------------------
% 0.22/0.53  % (22444)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.56  % (22425)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.56  % (22440)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.56  % (22425)Refutation not found, incomplete strategy% (22425)------------------------------
% 0.22/0.56  % (22425)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (22425)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (22425)Memory used [KB]: 6140
% 0.22/0.56  % (22425)Time elapsed: 0.115 s
% 0.22/0.56  % (22425)------------------------------
% 0.22/0.56  % (22425)------------------------------
% 0.22/0.56  % (22429)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.57  % (22431)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.57  % (22432)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.57  % (22445)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.58  % (22439)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.58  % (22445)Refutation not found, incomplete strategy% (22445)------------------------------
% 0.22/0.58  % (22445)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (22445)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.58  
% 0.22/0.58  % (22445)Memory used [KB]: 10618
% 0.22/0.58  % (22445)Time elapsed: 0.134 s
% 0.22/0.58  % (22445)------------------------------
% 0.22/0.58  % (22445)------------------------------
% 0.22/0.58  % (22433)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.58  % (22434)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.58  % (22431)Refutation found. Thanks to Tanya!
% 0.22/0.58  % SZS status Theorem for theBenchmark
% 0.22/0.58  % SZS output start Proof for theBenchmark
% 0.22/0.58  fof(f178,plain,(
% 0.22/0.58    $false),
% 0.22/0.58    inference(avatar_sat_refutation,[],[f53,f59,f63,f110,f124,f148,f167])).
% 0.22/0.58  fof(f167,plain,(
% 0.22/0.58    ~spl3_6),
% 0.22/0.58    inference(avatar_contradiction_clause,[],[f165])).
% 0.22/0.58  fof(f165,plain,(
% 0.22/0.58    $false | ~spl3_6),
% 0.22/0.58    inference(resolution,[],[f108,f65])).
% 0.22/0.58  fof(f65,plain,(
% 0.22/0.58    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.22/0.58    inference(superposition,[],[f36,f45])).
% 0.22/0.58  fof(f45,plain,(
% 0.22/0.58    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.22/0.58    inference(equality_resolution,[],[f43])).
% 0.22/0.58  fof(f43,plain,(
% 0.22/0.58    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.22/0.58    inference(cnf_transformation,[],[f27])).
% 0.22/0.58  fof(f27,plain,(
% 0.22/0.58    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.22/0.58    inference(flattening,[],[f26])).
% 0.22/0.58  fof(f26,plain,(
% 0.22/0.58    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.22/0.58    inference(nnf_transformation,[],[f3])).
% 0.22/0.58  fof(f3,axiom,(
% 0.22/0.58    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.58  fof(f36,plain,(
% 0.22/0.58    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 0.22/0.58    inference(cnf_transformation,[],[f4])).
% 0.22/0.58  fof(f4,axiom,(
% 0.22/0.58    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 0.22/0.58  fof(f108,plain,(
% 0.22/0.58    r2_hidden(k3_subset_1(sK0,sK2(k7_setfam_1(sK0,k1_xboole_0))),k1_xboole_0) | ~spl3_6),
% 0.22/0.58    inference(avatar_component_clause,[],[f107])).
% 0.22/0.58  fof(f107,plain,(
% 0.22/0.58    spl3_6 <=> r2_hidden(k3_subset_1(sK0,sK2(k7_setfam_1(sK0,k1_xboole_0))),k1_xboole_0)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.58  fof(f148,plain,(
% 0.22/0.58    ~spl3_8),
% 0.22/0.58    inference(avatar_contradiction_clause,[],[f146])).
% 0.22/0.58  fof(f146,plain,(
% 0.22/0.58    $false | ~spl3_8),
% 0.22/0.58    inference(resolution,[],[f123,f65])).
% 0.22/0.58  fof(f123,plain,(
% 0.22/0.58    r2_hidden(k3_subset_1(sK0,sK2(sK1)),k1_xboole_0) | ~spl3_8),
% 0.22/0.58    inference(avatar_component_clause,[],[f122])).
% 0.22/0.58  fof(f122,plain,(
% 0.22/0.58    spl3_8 <=> r2_hidden(k3_subset_1(sK0,sK2(sK1)),k1_xboole_0)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.58  fof(f124,plain,(
% 0.22/0.58    ~spl3_4 | spl3_2 | spl3_8 | ~spl3_1),
% 0.22/0.58    inference(avatar_split_clause,[],[f116,f48,f122,f51,f61])).
% 0.22/0.58  fof(f61,plain,(
% 0.22/0.58    spl3_4 <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.58  fof(f51,plain,(
% 0.22/0.58    spl3_2 <=> k1_xboole_0 = sK1),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.58  fof(f48,plain,(
% 0.22/0.58    spl3_1 <=> k1_xboole_0 = k7_setfam_1(sK0,sK1)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.58  fof(f116,plain,(
% 0.22/0.58    r2_hidden(k3_subset_1(sK0,sK2(sK1)),k1_xboole_0) | k1_xboole_0 = sK1 | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl3_1),
% 0.22/0.58    inference(superposition,[],[f83,f49])).
% 0.22/0.58  fof(f49,plain,(
% 0.22/0.58    k1_xboole_0 = k7_setfam_1(sK0,sK1) | ~spl3_1),
% 0.22/0.58    inference(avatar_component_clause,[],[f48])).
% 0.22/0.58  fof(f83,plain,(
% 0.22/0.58    ( ! [X0,X1] : (r2_hidden(k3_subset_1(X1,sK2(X0)),k7_setfam_1(X1,X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))) )),
% 0.22/0.58    inference(duplicate_literal_removal,[],[f82])).
% 0.22/0.58  fof(f82,plain,(
% 0.22/0.58    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) | k1_xboole_0 = X0 | r2_hidden(k3_subset_1(X1,sK2(X0)),k7_setfam_1(X1,X0)) | k1_xboole_0 = X0) )),
% 0.22/0.58    inference(resolution,[],[f81,f34])).
% 0.22/0.58  fof(f34,plain,(
% 0.22/0.58    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.22/0.58    inference(cnf_transformation,[],[f14])).
% 0.22/0.58  fof(f14,plain,(
% 0.22/0.58    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.58    inference(ennf_transformation,[],[f2])).
% 0.22/0.58  fof(f2,axiom,(
% 0.22/0.58    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.22/0.58  fof(f81,plain,(
% 0.22/0.58    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k1_xboole_0 = X1 | r2_hidden(k3_subset_1(X0,sK2(X1)),k7_setfam_1(X0,X1))) )),
% 0.22/0.58    inference(duplicate_literal_removal,[],[f80])).
% 0.22/0.58  fof(f80,plain,(
% 0.22/0.58    ( ! [X0,X1] : (r2_hidden(k3_subset_1(X0,sK2(X1)),k7_setfam_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k1_xboole_0 = X1 | v1_xboole_0(X1)) )),
% 0.22/0.58    inference(resolution,[],[f79,f35])).
% 0.22/0.58  fof(f35,plain,(
% 0.22/0.58    ( ! [X0] : (r2_hidden(sK2(X0),X0) | v1_xboole_0(X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f24])).
% 0.22/0.58  fof(f24,plain,(
% 0.22/0.58    ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK2(X0),X0))),
% 0.22/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f23])).
% 0.22/0.58  fof(f23,plain,(
% 0.22/0.58    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 0.22/0.58    introduced(choice_axiom,[])).
% 0.22/0.58  fof(f15,plain,(
% 0.22/0.58    ! [X0] : (v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0))),
% 0.22/0.58    inference(ennf_transformation,[],[f12])).
% 0.22/0.59  fof(f12,plain,(
% 0.22/0.59    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) => v1_xboole_0(X0))),
% 0.22/0.59    inference(unused_predicate_definition_removal,[],[f1])).
% 0.22/0.59  fof(f1,axiom,(
% 0.22/0.59    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.22/0.59  fof(f79,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (~r2_hidden(sK2(X0),X2) | r2_hidden(k3_subset_1(X1,sK2(X0)),k7_setfam_1(X1,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) | k1_xboole_0 = X0) )),
% 0.22/0.59    inference(resolution,[],[f78,f34])).
% 0.22/0.59  fof(f78,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | r2_hidden(k3_subset_1(X0,sK2(X1)),k7_setfam_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~r2_hidden(sK2(X1),X2)) )),
% 0.22/0.59    inference(resolution,[],[f77,f44])).
% 0.22/0.59  fof(f44,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f20])).
% 0.22/0.59  fof(f20,plain,(
% 0.22/0.59    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.59    inference(flattening,[],[f19])).
% 0.22/0.59  % (22426)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.59  fof(f19,plain,(
% 0.22/0.59    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.22/0.59    inference(ennf_transformation,[],[f9])).
% 0.22/0.59  fof(f9,axiom,(
% 0.22/0.59    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 0.22/0.59  fof(f77,plain,(
% 0.22/0.59    ( ! [X0,X1] : (~m1_subset_1(sK2(X1),k1_zfmisc_1(X0)) | r2_hidden(k3_subset_1(X0,sK2(X1)),k7_setfam_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | v1_xboole_0(X1)) )),
% 0.22/0.59    inference(resolution,[],[f40,f35])).
% 0.22/0.59  fof(f40,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.22/0.59    inference(cnf_transformation,[],[f25])).
% 0.22/0.59  fof(f25,plain,(
% 0.22/0.59    ! [X0,X1] : (! [X2] : (((r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) | ~r2_hidden(X2,X1)) & (r2_hidden(X2,X1) | ~r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.59    inference(nnf_transformation,[],[f18])).
% 0.22/0.59  fof(f18,plain,(
% 0.22/0.59    ! [X0,X1] : (! [X2] : ((r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) <=> r2_hidden(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.59    inference(ennf_transformation,[],[f8])).
% 0.22/0.59  fof(f8,axiom,(
% 0.22/0.59    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) <=> r2_hidden(X2,X1))))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_setfam_1)).
% 0.22/0.59  fof(f110,plain,(
% 0.22/0.59    spl3_6 | spl3_3 | ~spl3_2 | ~spl3_4),
% 0.22/0.59    inference(avatar_split_clause,[],[f105,f61,f51,f57,f107])).
% 0.22/0.59  fof(f57,plain,(
% 0.22/0.59    spl3_3 <=> k1_xboole_0 = k7_setfam_1(sK0,k1_xboole_0)),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.59  fof(f105,plain,(
% 0.22/0.59    k1_xboole_0 = k7_setfam_1(sK0,k1_xboole_0) | r2_hidden(k3_subset_1(sK0,sK2(k7_setfam_1(sK0,k1_xboole_0))),k1_xboole_0) | (~spl3_2 | ~spl3_4)),
% 0.22/0.59    inference(forward_demodulation,[],[f104,f52])).
% 0.22/0.59  fof(f52,plain,(
% 0.22/0.59    k1_xboole_0 = sK1 | ~spl3_2),
% 0.22/0.59    inference(avatar_component_clause,[],[f51])).
% 0.22/0.59  fof(f104,plain,(
% 0.22/0.59    r2_hidden(k3_subset_1(sK0,sK2(k7_setfam_1(sK0,k1_xboole_0))),k1_xboole_0) | k1_xboole_0 = k7_setfam_1(sK0,sK1) | (~spl3_2 | ~spl3_4)),
% 0.22/0.59    inference(forward_demodulation,[],[f100,f52])).
% 0.22/0.59  fof(f100,plain,(
% 0.22/0.59    r2_hidden(k3_subset_1(sK0,sK2(k7_setfam_1(sK0,sK1))),sK1) | k1_xboole_0 = k7_setfam_1(sK0,sK1) | ~spl3_4),
% 0.22/0.59    inference(resolution,[],[f99,f62])).
% 0.22/0.59  fof(f62,plain,(
% 0.22/0.59    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl3_4),
% 0.22/0.59    inference(avatar_component_clause,[],[f61])).
% 0.22/0.59  fof(f99,plain,(
% 0.22/0.59    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | r2_hidden(k3_subset_1(X0,sK2(k7_setfam_1(X0,X1))),X1) | k1_xboole_0 = k7_setfam_1(X0,X1)) )),
% 0.22/0.59    inference(duplicate_literal_removal,[],[f95])).
% 0.22/0.59  fof(f95,plain,(
% 0.22/0.59    ( ! [X0,X1] : (k1_xboole_0 = k7_setfam_1(X0,X1) | r2_hidden(k3_subset_1(X0,sK2(k7_setfam_1(X0,X1))),X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.22/0.59    inference(resolution,[],[f86,f38])).
% 0.22/0.59  fof(f38,plain,(
% 0.22/0.59    ( ! [X0,X1] : (m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.22/0.59    inference(cnf_transformation,[],[f17])).
% 0.22/0.59  fof(f17,plain,(
% 0.22/0.59    ! [X0,X1] : (m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.59    inference(ennf_transformation,[],[f6])).
% 0.22/0.59  fof(f6,axiom,(
% 0.22/0.59    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_setfam_1)).
% 0.22/0.59  fof(f86,plain,(
% 0.22/0.59    ( ! [X0,X1] : (~m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | k1_xboole_0 = k7_setfam_1(X0,X1) | r2_hidden(k3_subset_1(X0,sK2(k7_setfam_1(X0,X1))),X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.22/0.59    inference(superposition,[],[f83,f37])).
% 0.22/0.59  fof(f37,plain,(
% 0.22/0.59    ( ! [X0,X1] : (k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.22/0.59    inference(cnf_transformation,[],[f16])).
% 0.22/0.59  fof(f16,plain,(
% 0.22/0.59    ! [X0,X1] : (k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.59    inference(ennf_transformation,[],[f7])).
% 0.22/0.59  fof(f7,axiom,(
% 0.22/0.59    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1)),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).
% 0.22/0.59  fof(f63,plain,(
% 0.22/0.59    spl3_4),
% 0.22/0.59    inference(avatar_split_clause,[],[f28,f61])).
% 0.22/0.59  fof(f28,plain,(
% 0.22/0.59    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.22/0.59    inference(cnf_transformation,[],[f22])).
% 0.22/0.59  fof(f22,plain,(
% 0.22/0.59    ((k1_xboole_0 = sK1 & k1_xboole_0 != k7_setfam_1(sK0,sK1)) | (k1_xboole_0 = k7_setfam_1(sK0,sK1) & k1_xboole_0 != sK1)) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.22/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f21])).
% 0.22/0.59  fof(f21,plain,(
% 0.22/0.59    ? [X0,X1] : (((k1_xboole_0 = X1 & k1_xboole_0 != k7_setfam_1(X0,X1)) | (k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (((k1_xboole_0 = sK1 & k1_xboole_0 != k7_setfam_1(sK0,sK1)) | (k1_xboole_0 = k7_setfam_1(sK0,sK1) & k1_xboole_0 != sK1)) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 0.22/0.59    introduced(choice_axiom,[])).
% 0.22/0.59  fof(f13,plain,(
% 0.22/0.59    ? [X0,X1] : (((k1_xboole_0 = X1 & k1_xboole_0 != k7_setfam_1(X0,X1)) | (k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.59    inference(ennf_transformation,[],[f11])).
% 0.22/0.59  fof(f11,negated_conjecture,(
% 0.22/0.59    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (~(k1_xboole_0 = X1 & k1_xboole_0 != k7_setfam_1(X0,X1)) & ~(k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1)))),
% 0.22/0.59    inference(negated_conjecture,[],[f10])).
% 0.22/0.59  fof(f10,conjecture,(
% 0.22/0.59    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (~(k1_xboole_0 = X1 & k1_xboole_0 != k7_setfam_1(X0,X1)) & ~(k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1)))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_tops_2)).
% 0.22/0.59  fof(f59,plain,(
% 0.22/0.59    ~spl3_2 | ~spl3_3),
% 0.22/0.59    inference(avatar_split_clause,[],[f54,f57,f51])).
% 0.22/0.59  fof(f54,plain,(
% 0.22/0.59    k1_xboole_0 != k7_setfam_1(sK0,k1_xboole_0) | k1_xboole_0 != sK1),
% 0.22/0.59    inference(inner_rewriting,[],[f29])).
% 0.22/0.59  fof(f29,plain,(
% 0.22/0.59    k1_xboole_0 != k7_setfam_1(sK0,sK1) | k1_xboole_0 != sK1),
% 0.22/0.59    inference(cnf_transformation,[],[f22])).
% 0.22/0.59  fof(f53,plain,(
% 0.22/0.59    spl3_1 | spl3_2),
% 0.22/0.59    inference(avatar_split_clause,[],[f32,f51,f48])).
% 0.22/0.59  fof(f32,plain,(
% 0.22/0.59    k1_xboole_0 = sK1 | k1_xboole_0 = k7_setfam_1(sK0,sK1)),
% 0.22/0.59    inference(cnf_transformation,[],[f22])).
% 0.22/0.59  % SZS output end Proof for theBenchmark
% 0.22/0.59  % (22431)------------------------------
% 0.22/0.59  % (22431)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.59  % (22431)Termination reason: Refutation
% 0.22/0.59  
% 0.22/0.59  % (22431)Memory used [KB]: 10746
% 0.22/0.59  % (22431)Time elapsed: 0.126 s
% 0.22/0.59  % (22431)------------------------------
% 0.22/0.59  % (22431)------------------------------
% 0.22/0.59  % (22424)Success in time 0.221 s
%------------------------------------------------------------------------------
