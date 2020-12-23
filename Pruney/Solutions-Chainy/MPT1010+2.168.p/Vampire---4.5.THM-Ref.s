%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:14 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.55s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 111 expanded)
%              Number of leaves         :   17 (  39 expanded)
%              Depth                    :   11
%              Number of atoms          :  244 ( 415 expanded)
%              Number of equality atoms :   99 ( 134 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f156,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f58,f63,f68,f73,f78,f129,f135,f139,f155])).

fof(f155,plain,
    ( spl5_1
    | ~ spl5_2
    | ~ spl5_6 ),
    inference(avatar_contradiction_clause,[],[f154])).

fof(f154,plain,
    ( $false
    | spl5_1
    | ~ spl5_2
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f152,f62])).

fof(f62,plain,
    ( r2_hidden(sK2,sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl5_2
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f152,plain,
    ( ~ r2_hidden(sK2,sK0)
    | spl5_1
    | ~ spl5_6 ),
    inference(trivial_inequality_removal,[],[f149])).

fof(f149,plain,
    ( sK1 != sK1
    | ~ r2_hidden(sK2,sK0)
    | spl5_1
    | ~ spl5_6 ),
    inference(superposition,[],[f57,f146])).

fof(f146,plain,
    ( ! [X0] :
        ( sK1 = k1_funct_1(sK3,X0)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl5_6 ),
    inference(resolution,[],[f99,f53])).

fof(f53,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK4(X0,X1) != X0
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( sK4(X0,X1) = X0
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f23])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK4(X0,X1) != X0
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( sK4(X0,X1) = X0
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

% (18500)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f99,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK3,X0),k1_tarski(sK1))
        | ~ r2_hidden(X0,sK0) )
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl5_6
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | r2_hidden(k1_funct_1(sK3,X0),k1_tarski(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f57,plain,
    ( sK1 != k1_funct_1(sK3,sK2)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl5_1
  <=> sK1 = k1_funct_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f139,plain,
    ( spl5_6
    | spl5_7
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f138,f75,f70,f65,f101,f98])).

fof(f101,plain,
    ( spl5_7
  <=> k1_xboole_0 = k1_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f65,plain,
    ( spl5_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f70,plain,
    ( spl5_4
  <=> v1_funct_2(sK3,sK0,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f75,plain,
    ( spl5_5
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f138,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k1_tarski(sK1)
        | ~ r2_hidden(X0,sK0)
        | r2_hidden(k1_funct_1(sK3,X0),k1_tarski(sK1)) )
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f137,f77])).

fof(f77,plain,
    ( v1_funct_1(sK3)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f75])).

fof(f137,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k1_tarski(sK1)
        | ~ r2_hidden(X0,sK0)
        | r2_hidden(k1_funct_1(sK3,X0),k1_tarski(sK1))
        | ~ v1_funct_1(sK3) )
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f136,f72])).

fof(f72,plain,
    ( v1_funct_2(sK3,sK0,k1_tarski(sK1))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f70])).

fof(f136,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k1_tarski(sK1)
        | ~ r2_hidden(X0,sK0)
        | r2_hidden(k1_funct_1(sK3,X0),k1_tarski(sK1))
        | ~ v1_funct_2(sK3,sK0,k1_tarski(sK1))
        | ~ v1_funct_1(sK3) )
    | ~ spl5_3 ),
    inference(resolution,[],[f67,f30])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | r2_hidden(k1_funct_1(X3,X2),X1)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

fof(f67,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f65])).

fof(f135,plain,
    ( spl5_10
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f114,f101,f126])).

% (18528)Refutation not found, incomplete strategy% (18528)------------------------------
% (18528)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f126,plain,
    ( spl5_10
  <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f114,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl5_7 ),
    inference(superposition,[],[f86,f103])).

fof(f103,plain,
    ( k1_xboole_0 = k1_tarski(sK1)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f101])).

fof(f86,plain,(
    ! [X3] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_tarski(X3)) ),
    inference(superposition,[],[f49,f80])).

fof(f80,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(superposition,[],[f43,f45])).

fof(f45,plain,(
    ! [X0] : k1_tarski(X0) = k3_relat_1(k1_tarski(k4_tarski(X0,X0))) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_tarski(X0) = k3_relat_1(k1_tarski(k4_tarski(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t208_relat_1)).

fof(f43,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_relat_1(k1_tarski(k4_tarski(X0,X1))) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_relat_1(k1_tarski(k4_tarski(X0,X1))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_relat_1)).

fof(f49,plain,(
    ! [X2,X1] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k2_tarski(X1,X2)) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,k2_tarski(X1,X2)) = k1_xboole_0
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | k4_xboole_0(X0,k2_tarski(X1,X2)) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,k2_tarski(X1,X2)) = k1_xboole_0
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | k4_xboole_0(X0,k2_tarski(X1,X2)) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,k2_tarski(X1,X2)) = k1_xboole_0
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,k2_tarski(X1,X2)) = k1_xboole_0
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_zfmisc_1)).

fof(f129,plain,
    ( ~ spl5_10
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f111,f101,f126])).

fof(f111,plain,
    ( k1_xboole_0 != k4_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl5_7 ),
    inference(superposition,[],[f50,f103])).

fof(f50,plain,(
    ! [X1] : k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
      & ( X0 != X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f78,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f25,f75])).

fof(f25,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( sK1 != k1_funct_1(sK3,sK2)
    & r2_hidden(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    & v1_funct_2(sK3,sK0,k1_tarski(sK1))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f16])).

fof(f16,plain,
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

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => k1_funct_1(X3,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => k1_funct_1(X3,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

fof(f73,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f26,f70])).

fof(f26,plain,(
    v1_funct_2(sK3,sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f68,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f27,f65])).

fof(f27,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    inference(cnf_transformation,[],[f17])).

fof(f63,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f28,f60])).

fof(f28,plain,(
    r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f58,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f29,f55])).

fof(f29,plain,(
    sK1 != k1_funct_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:31:30 EST 2020
% 0.21/0.35  % CPUTime    : 
% 0.21/0.55  % (18512)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.56  % (18520)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.56  % (18503)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.57  % (18520)Refutation found. Thanks to Tanya!
% 0.21/0.57  % SZS status Theorem for theBenchmark
% 0.21/0.57  % (18504)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.55/0.57  % (18505)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.55/0.57  % (18499)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.55/0.57  % (18502)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.55/0.57  % (18528)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.55/0.57  % SZS output start Proof for theBenchmark
% 1.55/0.57  fof(f156,plain,(
% 1.55/0.57    $false),
% 1.55/0.57    inference(avatar_sat_refutation,[],[f58,f63,f68,f73,f78,f129,f135,f139,f155])).
% 1.55/0.57  fof(f155,plain,(
% 1.55/0.57    spl5_1 | ~spl5_2 | ~spl5_6),
% 1.55/0.57    inference(avatar_contradiction_clause,[],[f154])).
% 1.55/0.57  fof(f154,plain,(
% 1.55/0.57    $false | (spl5_1 | ~spl5_2 | ~spl5_6)),
% 1.55/0.57    inference(subsumption_resolution,[],[f152,f62])).
% 1.55/0.57  fof(f62,plain,(
% 1.55/0.57    r2_hidden(sK2,sK0) | ~spl5_2),
% 1.55/0.57    inference(avatar_component_clause,[],[f60])).
% 1.55/0.57  fof(f60,plain,(
% 1.55/0.57    spl5_2 <=> r2_hidden(sK2,sK0)),
% 1.55/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.55/0.57  fof(f152,plain,(
% 1.55/0.57    ~r2_hidden(sK2,sK0) | (spl5_1 | ~spl5_6)),
% 1.55/0.57    inference(trivial_inequality_removal,[],[f149])).
% 1.55/0.57  fof(f149,plain,(
% 1.55/0.57    sK1 != sK1 | ~r2_hidden(sK2,sK0) | (spl5_1 | ~spl5_6)),
% 1.55/0.57    inference(superposition,[],[f57,f146])).
% 1.55/0.57  fof(f146,plain,(
% 1.55/0.57    ( ! [X0] : (sK1 = k1_funct_1(sK3,X0) | ~r2_hidden(X0,sK0)) ) | ~spl5_6),
% 1.55/0.57    inference(resolution,[],[f99,f53])).
% 1.55/0.57  fof(f53,plain,(
% 1.55/0.57    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 1.55/0.57    inference(equality_resolution,[],[f39])).
% 1.55/0.57  fof(f39,plain,(
% 1.55/0.57    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.55/0.57    inference(cnf_transformation,[],[f24])).
% 1.55/0.57  fof(f24,plain,(
% 1.55/0.57    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.55/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f23])).
% 1.55/0.57  fof(f23,plain,(
% 1.55/0.57    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1))))),
% 1.55/0.57    introduced(choice_axiom,[])).
% 1.55/0.57  fof(f22,plain,(
% 1.55/0.57    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.55/0.57    inference(rectify,[],[f21])).
% 1.55/0.57  fof(f21,plain,(
% 1.55/0.57    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.55/0.57    inference(nnf_transformation,[],[f1])).
% 1.55/0.57  % (18500)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.55/0.57  fof(f1,axiom,(
% 1.55/0.57    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.55/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 1.55/0.57  fof(f99,plain,(
% 1.55/0.57    ( ! [X0] : (r2_hidden(k1_funct_1(sK3,X0),k1_tarski(sK1)) | ~r2_hidden(X0,sK0)) ) | ~spl5_6),
% 1.55/0.57    inference(avatar_component_clause,[],[f98])).
% 1.55/0.57  fof(f98,plain,(
% 1.55/0.57    spl5_6 <=> ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(k1_funct_1(sK3,X0),k1_tarski(sK1)))),
% 1.55/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.55/0.57  fof(f57,plain,(
% 1.55/0.57    sK1 != k1_funct_1(sK3,sK2) | spl5_1),
% 1.55/0.57    inference(avatar_component_clause,[],[f55])).
% 1.55/0.57  fof(f55,plain,(
% 1.55/0.57    spl5_1 <=> sK1 = k1_funct_1(sK3,sK2)),
% 1.55/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.55/0.57  fof(f139,plain,(
% 1.55/0.57    spl5_6 | spl5_7 | ~spl5_3 | ~spl5_4 | ~spl5_5),
% 1.55/0.57    inference(avatar_split_clause,[],[f138,f75,f70,f65,f101,f98])).
% 1.55/0.57  fof(f101,plain,(
% 1.55/0.57    spl5_7 <=> k1_xboole_0 = k1_tarski(sK1)),
% 1.55/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 1.55/0.57  fof(f65,plain,(
% 1.55/0.57    spl5_3 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))),
% 1.55/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.55/0.57  fof(f70,plain,(
% 1.55/0.57    spl5_4 <=> v1_funct_2(sK3,sK0,k1_tarski(sK1))),
% 1.55/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.55/0.57  fof(f75,plain,(
% 1.55/0.57    spl5_5 <=> v1_funct_1(sK3)),
% 1.55/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.55/0.57  fof(f138,plain,(
% 1.55/0.57    ( ! [X0] : (k1_xboole_0 = k1_tarski(sK1) | ~r2_hidden(X0,sK0) | r2_hidden(k1_funct_1(sK3,X0),k1_tarski(sK1))) ) | (~spl5_3 | ~spl5_4 | ~spl5_5)),
% 1.55/0.57    inference(subsumption_resolution,[],[f137,f77])).
% 1.55/0.57  fof(f77,plain,(
% 1.55/0.57    v1_funct_1(sK3) | ~spl5_5),
% 1.55/0.57    inference(avatar_component_clause,[],[f75])).
% 1.55/0.57  fof(f137,plain,(
% 1.55/0.57    ( ! [X0] : (k1_xboole_0 = k1_tarski(sK1) | ~r2_hidden(X0,sK0) | r2_hidden(k1_funct_1(sK3,X0),k1_tarski(sK1)) | ~v1_funct_1(sK3)) ) | (~spl5_3 | ~spl5_4)),
% 1.55/0.57    inference(subsumption_resolution,[],[f136,f72])).
% 1.55/0.57  fof(f72,plain,(
% 1.55/0.57    v1_funct_2(sK3,sK0,k1_tarski(sK1)) | ~spl5_4),
% 1.55/0.57    inference(avatar_component_clause,[],[f70])).
% 1.55/0.57  fof(f136,plain,(
% 1.55/0.57    ( ! [X0] : (k1_xboole_0 = k1_tarski(sK1) | ~r2_hidden(X0,sK0) | r2_hidden(k1_funct_1(sK3,X0),k1_tarski(sK1)) | ~v1_funct_2(sK3,sK0,k1_tarski(sK1)) | ~v1_funct_1(sK3)) ) | ~spl5_3),
% 1.55/0.57    inference(resolution,[],[f67,f30])).
% 1.55/0.57  fof(f30,plain,(
% 1.55/0.57    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | r2_hidden(k1_funct_1(X3,X2),X1) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.55/0.57    inference(cnf_transformation,[],[f14])).
% 1.55/0.57  fof(f14,plain,(
% 1.55/0.57    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.55/0.57    inference(flattening,[],[f13])).
% 1.55/0.57  fof(f13,plain,(
% 1.55/0.57    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.55/0.57    inference(ennf_transformation,[],[f8])).
% 1.55/0.57  fof(f8,axiom,(
% 1.55/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 1.55/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).
% 1.55/0.57  fof(f67,plain,(
% 1.55/0.57    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | ~spl5_3),
% 1.55/0.57    inference(avatar_component_clause,[],[f65])).
% 1.55/0.57  fof(f135,plain,(
% 1.55/0.57    spl5_10 | ~spl5_7),
% 1.55/0.57    inference(avatar_split_clause,[],[f114,f101,f126])).
% 1.55/0.58  % (18528)Refutation not found, incomplete strategy% (18528)------------------------------
% 1.55/0.58  % (18528)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.58  fof(f126,plain,(
% 1.55/0.58    spl5_10 <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.55/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 1.55/0.58  fof(f114,plain,(
% 1.55/0.58    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl5_7),
% 1.55/0.58    inference(superposition,[],[f86,f103])).
% 1.55/0.58  fof(f103,plain,(
% 1.55/0.58    k1_xboole_0 = k1_tarski(sK1) | ~spl5_7),
% 1.55/0.58    inference(avatar_component_clause,[],[f101])).
% 1.55/0.58  fof(f86,plain,(
% 1.55/0.58    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_tarski(X3))) )),
% 1.55/0.58    inference(superposition,[],[f49,f80])).
% 1.55/0.58  fof(f80,plain,(
% 1.55/0.58    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.55/0.58    inference(superposition,[],[f43,f45])).
% 1.55/0.58  fof(f45,plain,(
% 1.55/0.58    ( ! [X0] : (k1_tarski(X0) = k3_relat_1(k1_tarski(k4_tarski(X0,X0)))) )),
% 1.55/0.58    inference(cnf_transformation,[],[f6])).
% 1.55/0.58  fof(f6,axiom,(
% 1.55/0.58    ! [X0] : k1_tarski(X0) = k3_relat_1(k1_tarski(k4_tarski(X0,X0)))),
% 1.55/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t208_relat_1)).
% 1.55/0.58  fof(f43,plain,(
% 1.55/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_relat_1(k1_tarski(k4_tarski(X0,X1)))) )),
% 1.55/0.58    inference(cnf_transformation,[],[f7])).
% 1.55/0.58  fof(f7,axiom,(
% 1.55/0.58    ! [X0,X1] : k2_tarski(X0,X1) = k3_relat_1(k1_tarski(k4_tarski(X0,X1)))),
% 1.55/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_relat_1)).
% 1.55/0.58  fof(f49,plain,(
% 1.55/0.58    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,k2_tarski(X1,X2))) )),
% 1.55/0.58    inference(equality_resolution,[],[f33])).
% 1.55/0.58  fof(f33,plain,(
% 1.55/0.58    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_tarski(X1,X2)) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 1.55/0.58    inference(cnf_transformation,[],[f19])).
% 1.55/0.58  fof(f19,plain,(
% 1.55/0.58    ! [X0,X1,X2] : ((k4_xboole_0(X0,k2_tarski(X1,X2)) = k1_xboole_0 | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | k4_xboole_0(X0,k2_tarski(X1,X2)) != k1_xboole_0))),
% 1.55/0.58    inference(flattening,[],[f18])).
% 1.55/0.58  fof(f18,plain,(
% 1.55/0.58    ! [X0,X1,X2] : ((k4_xboole_0(X0,k2_tarski(X1,X2)) = k1_xboole_0 | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | k4_xboole_0(X0,k2_tarski(X1,X2)) != k1_xboole_0))),
% 1.55/0.58    inference(nnf_transformation,[],[f15])).
% 1.55/0.58  fof(f15,plain,(
% 1.55/0.58    ! [X0,X1,X2] : (k4_xboole_0(X0,k2_tarski(X1,X2)) = k1_xboole_0 <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.55/0.58    inference(ennf_transformation,[],[f5])).
% 1.55/0.58  fof(f5,axiom,(
% 1.55/0.58    ! [X0,X1,X2] : (k4_xboole_0(X0,k2_tarski(X1,X2)) = k1_xboole_0 <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 1.55/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_zfmisc_1)).
% 1.55/0.58  fof(f129,plain,(
% 1.55/0.58    ~spl5_10 | ~spl5_7),
% 1.55/0.58    inference(avatar_split_clause,[],[f111,f101,f126])).
% 1.55/0.58  fof(f111,plain,(
% 1.55/0.58    k1_xboole_0 != k4_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl5_7),
% 1.55/0.58    inference(superposition,[],[f50,f103])).
% 1.55/0.58  fof(f50,plain,(
% 1.55/0.58    ( ! [X1] : (k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1))) )),
% 1.55/0.58    inference(equality_resolution,[],[f37])).
% 1.55/0.58  fof(f37,plain,(
% 1.55/0.58    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 1.55/0.58    inference(cnf_transformation,[],[f20])).
% 1.55/0.58  fof(f20,plain,(
% 1.55/0.58    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) & (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 1.55/0.58    inference(nnf_transformation,[],[f4])).
% 1.55/0.58  fof(f4,axiom,(
% 1.55/0.58    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 1.55/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 1.55/0.58  fof(f78,plain,(
% 1.55/0.58    spl5_5),
% 1.55/0.58    inference(avatar_split_clause,[],[f25,f75])).
% 1.55/0.58  fof(f25,plain,(
% 1.55/0.58    v1_funct_1(sK3)),
% 1.55/0.58    inference(cnf_transformation,[],[f17])).
% 1.55/0.58  fof(f17,plain,(
% 1.55/0.58    sK1 != k1_funct_1(sK3,sK2) & r2_hidden(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_2(sK3,sK0,k1_tarski(sK1)) & v1_funct_1(sK3)),
% 1.55/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f16])).
% 1.55/0.58  fof(f16,plain,(
% 1.55/0.58    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (sK1 != k1_funct_1(sK3,sK2) & r2_hidden(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_2(sK3,sK0,k1_tarski(sK1)) & v1_funct_1(sK3))),
% 1.55/0.58    introduced(choice_axiom,[])).
% 1.55/0.58  fof(f12,plain,(
% 1.55/0.58    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))),
% 1.55/0.58    inference(flattening,[],[f11])).
% 1.55/0.58  fof(f11,plain,(
% 1.55/0.58    ? [X0,X1,X2,X3] : ((k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)))),
% 1.55/0.58    inference(ennf_transformation,[],[f10])).
% 1.55/0.58  fof(f10,negated_conjecture,(
% 1.55/0.58    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 1.55/0.58    inference(negated_conjecture,[],[f9])).
% 1.55/0.58  fof(f9,conjecture,(
% 1.55/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 1.55/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).
% 1.55/0.58  fof(f73,plain,(
% 1.55/0.58    spl5_4),
% 1.55/0.58    inference(avatar_split_clause,[],[f26,f70])).
% 1.55/0.58  fof(f26,plain,(
% 1.55/0.58    v1_funct_2(sK3,sK0,k1_tarski(sK1))),
% 1.55/0.58    inference(cnf_transformation,[],[f17])).
% 1.55/0.58  fof(f68,plain,(
% 1.55/0.58    spl5_3),
% 1.55/0.58    inference(avatar_split_clause,[],[f27,f65])).
% 1.55/0.58  fof(f27,plain,(
% 1.55/0.58    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))),
% 1.55/0.58    inference(cnf_transformation,[],[f17])).
% 1.55/0.58  fof(f63,plain,(
% 1.55/0.58    spl5_2),
% 1.55/0.58    inference(avatar_split_clause,[],[f28,f60])).
% 1.55/0.58  fof(f28,plain,(
% 1.55/0.58    r2_hidden(sK2,sK0)),
% 1.55/0.58    inference(cnf_transformation,[],[f17])).
% 1.55/0.58  fof(f58,plain,(
% 1.55/0.58    ~spl5_1),
% 1.55/0.58    inference(avatar_split_clause,[],[f29,f55])).
% 1.55/0.58  fof(f29,plain,(
% 1.55/0.58    sK1 != k1_funct_1(sK3,sK2)),
% 1.55/0.58    inference(cnf_transformation,[],[f17])).
% 1.55/0.58  % SZS output end Proof for theBenchmark
% 1.55/0.58  % (18520)------------------------------
% 1.55/0.58  % (18520)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.58  % (18520)Termination reason: Refutation
% 1.55/0.58  
% 1.55/0.58  % (18520)Memory used [KB]: 6268
% 1.55/0.58  % (18520)Time elapsed: 0.140 s
% 1.55/0.58  % (18520)------------------------------
% 1.55/0.58  % (18520)------------------------------
% 1.55/0.58  % (18514)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.55/0.58  % (18498)Success in time 0.211 s
%------------------------------------------------------------------------------
