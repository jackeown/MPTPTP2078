%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0344+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:47 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   58 (  84 expanded)
%              Number of leaves         :   15 (  35 expanded)
%              Depth                    :    6
%              Number of atoms          :  155 ( 236 expanded)
%              Number of equality atoms :   13 (  23 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f107,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f27,f31,f35,f39,f47,f51,f64,f82,f89,f92,f106])).

fof(f106,plain,
    ( spl3_1
    | ~ spl3_4
    | ~ spl3_12 ),
    inference(avatar_contradiction_clause,[],[f105])).

fof(f105,plain,
    ( $false
    | spl3_1
    | ~ spl3_4
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f103,f26])).

fof(f26,plain,
    ( k1_xboole_0 != sK1
    | spl3_1 ),
    inference(avatar_component_clause,[],[f25])).

fof(f25,plain,
    ( spl3_1
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f103,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_4
    | ~ spl3_12 ),
    inference(resolution,[],[f72,f38])).

fof(f38,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 )
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f37])).

fof(f37,plain,
    ( spl3_4
  <=> ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f72,plain,
    ( v1_xboole_0(sK1)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl3_12
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f92,plain,
    ( spl3_12
    | ~ spl3_6
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f90,f87,f45,f71])).

fof(f45,plain,
    ( spl3_6
  <=> ! [X0] :
        ( r2_hidden(sK2(X0),X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f87,plain,
    ( spl3_15
  <=> ! [X0] : ~ r2_hidden(X0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f90,plain,
    ( v1_xboole_0(sK1)
    | ~ spl3_6
    | ~ spl3_15 ),
    inference(resolution,[],[f88,f46])).

fof(f46,plain,
    ( ! [X0] :
        ( r2_hidden(sK2(X0),X0)
        | v1_xboole_0(X0) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f45])).

fof(f88,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK1)
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f87])).

fof(f89,plain,
    ( spl3_15
    | ~ spl3_2
    | ~ spl3_10
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f85,f80,f62,f29,f87])).

fof(f29,plain,
    ( spl3_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f62,plain,
    ( spl3_10
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | ~ r2_hidden(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f80,plain,
    ( spl3_14
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ r2_hidden(X2,X1)
        | r2_hidden(X2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f85,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK1)
    | ~ spl3_2
    | ~ spl3_10
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f83,f63])).

fof(f63,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f62])).

fof(f83,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | r2_hidden(X0,sK0) )
    | ~ spl3_2
    | ~ spl3_14 ),
    inference(resolution,[],[f81,f30])).

fof(f30,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f29])).

fof(f81,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ r2_hidden(X2,X1)
        | r2_hidden(X2,X0) )
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f80])).

fof(f82,plain,(
    spl3_14 ),
    inference(avatar_split_clause,[],[f22,f80])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

% (18382)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
fof(f64,plain,
    ( spl3_10
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f60,f49,f33,f62])).

fof(f33,plain,
    ( spl3_3
  <=> ! [X2] :
        ( ~ m1_subset_1(X2,sK0)
        | ~ r2_hidden(X2,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f49,plain,
    ( spl3_7
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X1,X0)
        | m1_subset_1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f60,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(resolution,[],[f50,f34])).

fof(f34,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK0)
        | ~ r2_hidden(X2,sK1) )
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f33])).

fof(f50,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(X1,X0)
        | ~ r2_hidden(X1,X0) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f49])).

fof(f51,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f23,f49])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0) ) ),
    inference(subsumption_resolution,[],[f20,f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f20,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f47,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f16,f45])).

fof(f16,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f39,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f15,f37])).

fof(f15,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

fof(f35,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f12,f33])).

fof(f12,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,sK0)
      | ~ r2_hidden(X2,sK1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r2_hidden(X2,X1)
          | ~ m1_subset_1(X2,X0) )
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r2_hidden(X2,X1)
          | ~ m1_subset_1(X2,X0) )
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ~ ( ! [X2] :
                ( m1_subset_1(X2,X0)
               => ~ r2_hidden(X2,X1) )
            & k1_xboole_0 != X1 ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ~ ( ! [X2] :
              ( m1_subset_1(X2,X0)
             => ~ r2_hidden(X2,X1) )
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_subset_1)).

fof(f31,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f13,f29])).

fof(f13,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f27,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f14,f25])).

fof(f14,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f8])).

%------------------------------------------------------------------------------
