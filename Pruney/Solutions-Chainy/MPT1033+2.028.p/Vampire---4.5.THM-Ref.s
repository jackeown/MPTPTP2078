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
% DateTime   : Thu Dec  3 13:06:46 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 424 expanded)
%              Number of leaves         :   29 ( 130 expanded)
%              Depth                    :   22
%              Number of atoms          :  543 (2024 expanded)
%              Number of equality atoms :   39 ( 125 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f279,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f64,f69,f78,f83,f88,f93,f107,f112,f119,f124,f135,f146,f154,f235,f238,f268,f269,f278])).

fof(f278,plain,
    ( sK2 != k2_zfmisc_1(sK0,sK1)
    | sK3 != k2_zfmisc_1(sK0,sK1)
    | r2_relset_1(sK0,sK1,sK2,sK3)
    | ~ r2_relset_1(sK0,sK1,sK2,sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f269,plain,
    ( ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_10
    | spl7_16
    | ~ spl7_18 ),
    inference(avatar_contradiction_clause,[],[f267])).

fof(f267,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_10
    | spl7_16
    | ~ spl7_18 ),
    inference(subsumption_resolution,[],[f254,f198])).

fof(f198,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_18 ),
    inference(forward_demodulation,[],[f195,f194])).

fof(f194,plain,
    ( k1_xboole_0 = sK5(sK1)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_18 ),
    inference(resolution,[],[f192,f37])).

fof(f37,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4] :
                  ~ ( k3_mcart_1(X2,X3,X4) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).

fof(f192,plain,
    ( ! [X2] : ~ r2_hidden(X2,sK5(sK1))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_18 ),
    inference(resolution,[],[f189,f38])).

fof(f38,plain,(
    ! [X0] : m1_subset_1(sK5(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
    ? [X1] :
      ( ~ v1_subset_1(X1,X0)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_subset_1)).

fof(f189,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
        | ~ r2_hidden(X1,X0) )
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_18 ),
    inference(subsumption_resolution,[],[f188,f87])).

fof(f87,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl7_5
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f188,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(sK2,sK0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
        | ~ r2_hidden(X1,X0) )
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_18 ),
    inference(subsumption_resolution,[],[f187,f111])).

fof(f111,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl7_10
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f187,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_2(sK2,sK0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
        | ~ r2_hidden(X1,X0) )
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_9
    | ~ spl7_18 ),
    inference(subsumption_resolution,[],[f186,f106])).

fof(f106,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl7_9
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f186,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_2(sK2,sK0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
        | ~ r2_hidden(X1,X0) )
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_18 ),
    inference(resolution,[],[f185,f82])).

fof(f82,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl7_4
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f185,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ v1_funct_2(sK3,X0,X1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
        | ~ r2_hidden(X3,X2) )
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_18 ),
    inference(resolution,[],[f184,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f184,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK3,X0,X1)
        | ~ v1_funct_2(sK2,X0,X1) )
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_18 ),
    inference(duplicate_literal_removal,[],[f183])).

fof(f183,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_xboole_0(X1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK3,X0,X1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK2,X0,X1) )
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_18 ),
    inference(condensation,[],[f182])).

fof(f182,plain,
    ( ! [X2,X0,X1] :
        ( v1_xboole_0(X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_funct_2(sK3,X1,X0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(sK2,X1,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_18 ),
    inference(factoring,[],[f180])).

fof(f180,plain,
    ( ! [X2,X0,X3,X1] :
        ( v1_xboole_0(X2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK3,X0,X2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | v1_xboole_0(X3)
        | ~ v1_funct_2(sK2,X0,X3)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) )
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_18 ),
    inference(resolution,[],[f179,f73])).

fof(f73,plain,
    ( ! [X4,X3] :
        ( v1_partfun1(sK2,X3)
        | v1_xboole_0(X4)
        | ~ v1_funct_2(sK2,X3,X4)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
    | ~ spl7_2 ),
    inference(resolution,[],[f68,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f17])).

% (20116)Refutation not found, incomplete strategy% (20116)------------------------------
% (20116)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (20116)Termination reason: Refutation not found, incomplete strategy

% (20116)Memory used [KB]: 10746
% (20116)Time elapsed: 0.142 s
% (20116)------------------------------
% (20116)------------------------------
fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f68,plain,
    ( v1_funct_1(sK2)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl7_2
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f179,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_partfun1(sK2,X0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_xboole_0(X2)
        | ~ v1_funct_2(sK3,X0,X2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) )
    | ~ spl7_1
    | ~ spl7_18 ),
    inference(resolution,[],[f153,f71])).

fof(f71,plain,
    ( ! [X4,X3] :
        ( v1_partfun1(sK3,X3)
        | v1_xboole_0(X4)
        | ~ v1_funct_2(sK3,X3,X4)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
    | ~ spl7_1 ),
    inference(resolution,[],[f63,f40])).

fof(f63,plain,
    ( v1_funct_1(sK3)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl7_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f153,plain,
    ( ! [X0,X1] :
        ( ~ v1_partfun1(sK3,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_partfun1(sK2,X0) )
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f152])).

fof(f152,plain,
    ( spl7_18
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_partfun1(sK3,X0)
        | ~ v1_partfun1(sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f195,plain,
    ( ! [X0] : r1_tarski(sK5(sK1),X0)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_18 ),
    inference(resolution,[],[f192,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f254,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_10
    | spl7_16
    | ~ spl7_18 ),
    inference(forward_demodulation,[],[f247,f57])).

fof(f57,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f247,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,k1_xboole_0),sK2)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_10
    | spl7_16
    | ~ spl7_18 ),
    inference(backward_demodulation,[],[f145,f207])).

fof(f207,plain,
    ( k1_xboole_0 = sK1
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_18 ),
    inference(resolution,[],[f204,f37])).

fof(f204,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK1)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_18 ),
    inference(resolution,[],[f191,f56])).

fof(f56,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f191,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X1,sK1)
        | ~ r2_hidden(X0,X1) )
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_18 ),
    inference(resolution,[],[f189,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f145,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),sK2)
    | spl7_16 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl7_16
  <=> r1_tarski(k2_zfmisc_1(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f268,plain,
    ( ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_10
    | spl7_14
    | ~ spl7_18 ),
    inference(avatar_contradiction_clause,[],[f266])).

fof(f266,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_10
    | spl7_14
    | ~ spl7_18 ),
    inference(subsumption_resolution,[],[f253,f198])).

% (20115)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
fof(f253,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_10
    | spl7_14
    | ~ spl7_18 ),
    inference(forward_demodulation,[],[f246,f57])).

fof(f246,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,k1_xboole_0),sK3)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_10
    | spl7_14
    | ~ spl7_18 ),
    inference(backward_demodulation,[],[f134,f207])).

fof(f134,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),sK3)
    | spl7_14 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl7_14
  <=> r1_tarski(k2_zfmisc_1(sK0,sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f238,plain,
    ( ~ spl7_10
    | spl7_20 ),
    inference(avatar_contradiction_clause,[],[f237])).

fof(f237,plain,
    ( $false
    | ~ spl7_10
    | spl7_20 ),
    inference(subsumption_resolution,[],[f236,f111])).

fof(f236,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl7_20 ),
    inference(resolution,[],[f234,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r2_relset_1(X1,X2,X0,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(condensation,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X2,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

fof(f234,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK2)
    | spl7_20 ),
    inference(avatar_component_clause,[],[f232])).

fof(f232,plain,
    ( spl7_20
  <=> r2_relset_1(sK0,sK1,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f235,plain,
    ( ~ spl7_20
    | spl7_6
    | ~ spl7_17 ),
    inference(avatar_split_clause,[],[f160,f148,f90,f232])).

fof(f90,plain,
    ( spl7_6
  <=> r2_relset_1(sK0,sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f148,plain,
    ( spl7_17
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f160,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK2)
    | spl7_6
    | ~ spl7_17 ),
    inference(backward_demodulation,[],[f92,f150])).

fof(f150,plain,
    ( sK2 = sK3
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f148])).

fof(f92,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK3)
    | spl7_6 ),
    inference(avatar_component_clause,[],[f90])).

fof(f154,plain,
    ( spl7_17
    | spl7_18
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f137,f75,f66,f61,f152,f148])).

fof(f75,plain,
    ( spl7_3
  <=> r1_partfun1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f137,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_partfun1(sK2,X0)
        | ~ v1_partfun1(sK3,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | sK2 = sK3 )
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f136,f63])).

fof(f136,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(sK3)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_partfun1(sK2,X0)
        | ~ v1_partfun1(sK3,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | sK2 = sK3 )
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(resolution,[],[f72,f77])).

fof(f77,plain,
    ( r1_partfun1(sK2,sK3)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f75])).

fof(f72,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_partfun1(sK2,X2)
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_partfun1(sK2,X0)
        | ~ v1_partfun1(X2,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | sK2 = X2 )
    | ~ spl7_2 ),
    inference(resolution,[],[f68,f52])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_partfun1(X2,X0)
      | ~ v1_partfun1(X3,X0)
      | ~ r1_partfun1(X2,X3)
      | X2 = X3 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( X2 = X3
          | ~ r1_partfun1(X2,X3)
          | ~ v1_partfun1(X3,X0)
          | ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( X2 = X3
          | ~ r1_partfun1(X2,X3)
          | ~ v1_partfun1(X3,X0)
          | ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
         => ( ( r1_partfun1(X2,X3)
              & v1_partfun1(X3,X0)
              & v1_partfun1(X2,X0) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_partfun1)).

fof(f146,plain,
    ( spl7_15
    | ~ spl7_16
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f126,f121,f143,f139])).

fof(f139,plain,
    ( spl7_15
  <=> sK2 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f121,plain,
    ( spl7_12
  <=> r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f126,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),sK2)
    | sK2 = k2_zfmisc_1(sK0,sK1)
    | ~ spl7_12 ),
    inference(resolution,[],[f123,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f123,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f121])).

fof(f135,plain,
    ( spl7_13
    | ~ spl7_14
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f125,f116,f132,f128])).

fof(f128,plain,
    ( spl7_13
  <=> sK3 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f116,plain,
    ( spl7_11
  <=> r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f125,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),sK3)
    | sK3 = k2_zfmisc_1(sK0,sK1)
    | ~ spl7_11 ),
    inference(resolution,[],[f118,f43])).

fof(f118,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f116])).

fof(f124,plain,
    ( spl7_12
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f114,f109,f121])).

fof(f114,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))
    | ~ spl7_10 ),
    inference(resolution,[],[f111,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f119,plain,
    ( spl7_11
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f113,f104,f116])).

fof(f113,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))
    | ~ spl7_9 ),
    inference(resolution,[],[f106,f48])).

fof(f112,plain,(
    spl7_10 ),
    inference(avatar_split_clause,[],[f33,f109])).

fof(f33,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & r1_partfun1(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & r1_partfun1(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
           => ( r1_partfun1(X2,X3)
             => ( r2_relset_1(X0,X1,X2,X3)
                | ( k1_xboole_0 != X0
                  & k1_xboole_0 = X1 ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( r1_partfun1(X2,X3)
           => ( r2_relset_1(X0,X1,X2,X3)
              | ( k1_xboole_0 != X0
                & k1_xboole_0 = X1 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_2)).

fof(f107,plain,(
    spl7_9 ),
    inference(avatar_split_clause,[],[f28,f104])).

fof(f28,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f15])).

fof(f93,plain,(
    ~ spl7_6 ),
    inference(avatar_split_clause,[],[f30,f90])).

fof(f30,plain,(
    ~ r2_relset_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f15])).

fof(f88,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f32,f85])).

fof(f32,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f83,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f27,f80])).

fof(f27,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f78,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f29,f75])).

fof(f29,plain,(
    r1_partfun1(sK2,sK3) ),
    inference(cnf_transformation,[],[f15])).

fof(f69,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f31,f66])).

fof(f31,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f64,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f26,f61])).

fof(f26,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:12:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.50  % (20103)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.50  % (20117)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.51  % (20105)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.51  % (20108)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.51  % (20102)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.52  % (20119)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.52  % (20113)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.52  % (20099)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (20099)Refutation not found, incomplete strategy% (20099)------------------------------
% 0.20/0.52  % (20099)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (20099)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (20099)Memory used [KB]: 1663
% 0.20/0.52  % (20099)Time elapsed: 0.113 s
% 0.20/0.52  % (20099)------------------------------
% 0.20/0.52  % (20099)------------------------------
% 0.20/0.52  % (20104)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.52  % (20109)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.52  % (20111)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (20114)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.53  % (20100)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (20123)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.53  % (20110)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.53  % (20101)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (20107)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.53  % (20119)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.53  % (20124)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.53  % (20125)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.54  % (20127)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.54  % (20107)Refutation not found, incomplete strategy% (20107)------------------------------
% 0.20/0.54  % (20107)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (20107)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (20107)Memory used [KB]: 10746
% 0.20/0.54  % (20107)Time elapsed: 0.130 s
% 0.20/0.54  % (20107)------------------------------
% 0.20/0.54  % (20107)------------------------------
% 0.20/0.54  % (20128)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.54  % (20121)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.54  % (20122)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.54  % (20112)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.54  % (20116)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.55  % SZS output start Proof for theBenchmark
% 0.20/0.55  fof(f279,plain,(
% 0.20/0.55    $false),
% 0.20/0.55    inference(avatar_sat_refutation,[],[f64,f69,f78,f83,f88,f93,f107,f112,f119,f124,f135,f146,f154,f235,f238,f268,f269,f278])).
% 0.20/0.55  fof(f278,plain,(
% 0.20/0.55    sK2 != k2_zfmisc_1(sK0,sK1) | sK3 != k2_zfmisc_1(sK0,sK1) | r2_relset_1(sK0,sK1,sK2,sK3) | ~r2_relset_1(sK0,sK1,sK2,sK2)),
% 0.20/0.55    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.55  fof(f269,plain,(
% 0.20/0.55    ~spl7_1 | ~spl7_2 | ~spl7_4 | ~spl7_5 | ~spl7_9 | ~spl7_10 | spl7_16 | ~spl7_18),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f267])).
% 0.20/0.55  fof(f267,plain,(
% 0.20/0.55    $false | (~spl7_1 | ~spl7_2 | ~spl7_4 | ~spl7_5 | ~spl7_9 | ~spl7_10 | spl7_16 | ~spl7_18)),
% 0.20/0.55    inference(subsumption_resolution,[],[f254,f198])).
% 0.20/0.55  fof(f198,plain,(
% 0.20/0.55    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | (~spl7_1 | ~spl7_2 | ~spl7_4 | ~spl7_5 | ~spl7_9 | ~spl7_10 | ~spl7_18)),
% 0.20/0.55    inference(forward_demodulation,[],[f195,f194])).
% 0.20/0.55  fof(f194,plain,(
% 0.20/0.55    k1_xboole_0 = sK5(sK1) | (~spl7_1 | ~spl7_2 | ~spl7_4 | ~spl7_5 | ~spl7_9 | ~spl7_10 | ~spl7_18)),
% 0.20/0.55    inference(resolution,[],[f192,f37])).
% 0.20/0.55  fof(f37,plain,(
% 0.20/0.55    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 0.20/0.55    inference(cnf_transformation,[],[f16])).
% 0.20/0.55  fof(f16,plain,(
% 0.20/0.55    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.20/0.55    inference(ennf_transformation,[],[f9])).
% 0.20/0.55  fof(f9,axiom,(
% 0.20/0.55    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4] : ~(k3_mcart_1(X2,X3,X4) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).
% 0.20/0.55  fof(f192,plain,(
% 0.20/0.55    ( ! [X2] : (~r2_hidden(X2,sK5(sK1))) ) | (~spl7_1 | ~spl7_2 | ~spl7_4 | ~spl7_5 | ~spl7_9 | ~spl7_10 | ~spl7_18)),
% 0.20/0.55    inference(resolution,[],[f189,f38])).
% 0.20/0.55  fof(f38,plain,(
% 0.20/0.55    ( ! [X0] : (m1_subset_1(sK5(X0),k1_zfmisc_1(X0))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f5])).
% 0.20/0.55  fof(f5,axiom,(
% 0.20/0.55    ! [X0] : ? [X1] : (~v1_subset_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_subset_1)).
% 0.20/0.55  fof(f189,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(sK1)) | ~r2_hidden(X1,X0)) ) | (~spl7_1 | ~spl7_2 | ~spl7_4 | ~spl7_5 | ~spl7_9 | ~spl7_10 | ~spl7_18)),
% 0.20/0.55    inference(subsumption_resolution,[],[f188,f87])).
% 0.20/0.55  fof(f87,plain,(
% 0.20/0.55    v1_funct_2(sK2,sK0,sK1) | ~spl7_5),
% 0.20/0.55    inference(avatar_component_clause,[],[f85])).
% 0.20/0.55  fof(f85,plain,(
% 0.20/0.55    spl7_5 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.20/0.55  fof(f188,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(sK1)) | ~r2_hidden(X1,X0)) ) | (~spl7_1 | ~spl7_2 | ~spl7_4 | ~spl7_9 | ~spl7_10 | ~spl7_18)),
% 0.20/0.55    inference(subsumption_resolution,[],[f187,f111])).
% 0.20/0.55  fof(f111,plain,(
% 0.20/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl7_10),
% 0.20/0.55    inference(avatar_component_clause,[],[f109])).
% 0.20/0.55  fof(f109,plain,(
% 0.20/0.55    spl7_10 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.20/0.55  fof(f187,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(sK1)) | ~r2_hidden(X1,X0)) ) | (~spl7_1 | ~spl7_2 | ~spl7_4 | ~spl7_9 | ~spl7_18)),
% 0.20/0.55    inference(subsumption_resolution,[],[f186,f106])).
% 0.20/0.55  fof(f106,plain,(
% 0.20/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl7_9),
% 0.20/0.55    inference(avatar_component_clause,[],[f104])).
% 0.20/0.55  fof(f104,plain,(
% 0.20/0.55    spl7_9 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.20/0.55  fof(f186,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(sK1)) | ~r2_hidden(X1,X0)) ) | (~spl7_1 | ~spl7_2 | ~spl7_4 | ~spl7_18)),
% 0.20/0.55    inference(resolution,[],[f185,f82])).
% 0.20/0.55  fof(f82,plain,(
% 0.20/0.55    v1_funct_2(sK3,sK0,sK1) | ~spl7_4),
% 0.20/0.55    inference(avatar_component_clause,[],[f80])).
% 0.20/0.55  fof(f80,plain,(
% 0.20/0.55    spl7_4 <=> v1_funct_2(sK3,sK0,sK1)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.20/0.55  fof(f185,plain,(
% 0.20/0.55    ( ! [X2,X0,X3,X1] : (~v1_funct_2(sK3,X0,X1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X1)) | ~r2_hidden(X3,X2)) ) | (~spl7_1 | ~spl7_2 | ~spl7_18)),
% 0.20/0.55    inference(resolution,[],[f184,f53])).
% 0.20/0.55  fof(f53,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f22])).
% 0.20/0.55  fof(f22,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.20/0.55    inference(ennf_transformation,[],[f7])).
% 0.20/0.55  fof(f7,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.20/0.55  fof(f184,plain,(
% 0.20/0.55    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK3,X0,X1) | ~v1_funct_2(sK2,X0,X1)) ) | (~spl7_1 | ~spl7_2 | ~spl7_18)),
% 0.20/0.55    inference(duplicate_literal_removal,[],[f183])).
% 0.20/0.55  fof(f183,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK3,X0,X1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1)) ) | (~spl7_1 | ~spl7_2 | ~spl7_18)),
% 0.20/0.55    inference(condensation,[],[f182])).
% 0.20/0.55  fof(f182,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(sK3,X1,X0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(sK2,X1,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) ) | (~spl7_1 | ~spl7_2 | ~spl7_18)),
% 0.20/0.55    inference(factoring,[],[f180])).
% 0.20/0.55  fof(f180,plain,(
% 0.20/0.55    ( ! [X2,X0,X3,X1] : (v1_xboole_0(X2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK3,X0,X2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | v1_xboole_0(X3) | ~v1_funct_2(sK2,X0,X3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))) ) | (~spl7_1 | ~spl7_2 | ~spl7_18)),
% 0.20/0.55    inference(resolution,[],[f179,f73])).
% 0.20/0.55  fof(f73,plain,(
% 0.20/0.55    ( ! [X4,X3] : (v1_partfun1(sK2,X3) | v1_xboole_0(X4) | ~v1_funct_2(sK2,X3,X4) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) ) | ~spl7_2),
% 0.20/0.55    inference(resolution,[],[f68,f40])).
% 0.20/0.55  fof(f40,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f18])).
% 0.20/0.55  fof(f18,plain,(
% 0.20/0.55    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.20/0.55    inference(flattening,[],[f17])).
% 0.20/0.55  % (20116)Refutation not found, incomplete strategy% (20116)------------------------------
% 0.20/0.55  % (20116)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (20116)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (20116)Memory used [KB]: 10746
% 0.20/0.55  % (20116)Time elapsed: 0.142 s
% 0.20/0.55  % (20116)------------------------------
% 0.20/0.55  % (20116)------------------------------
% 0.20/0.55  fof(f17,plain,(
% 0.20/0.55    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.20/0.55    inference(ennf_transformation,[],[f10])).
% 0.20/0.55  fof(f10,axiom,(
% 0.20/0.55    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.20/0.55  fof(f68,plain,(
% 0.20/0.55    v1_funct_1(sK2) | ~spl7_2),
% 0.20/0.55    inference(avatar_component_clause,[],[f66])).
% 0.20/0.55  fof(f66,plain,(
% 0.20/0.55    spl7_2 <=> v1_funct_1(sK2)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.20/0.55  fof(f179,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~v1_partfun1(sK2,X0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X2) | ~v1_funct_2(sK3,X0,X2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) ) | (~spl7_1 | ~spl7_18)),
% 0.20/0.55    inference(resolution,[],[f153,f71])).
% 0.20/0.55  fof(f71,plain,(
% 0.20/0.55    ( ! [X4,X3] : (v1_partfun1(sK3,X3) | v1_xboole_0(X4) | ~v1_funct_2(sK3,X3,X4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) ) | ~spl7_1),
% 0.20/0.55    inference(resolution,[],[f63,f40])).
% 0.20/0.55  fof(f63,plain,(
% 0.20/0.55    v1_funct_1(sK3) | ~spl7_1),
% 0.20/0.55    inference(avatar_component_clause,[],[f61])).
% 0.20/0.55  fof(f61,plain,(
% 0.20/0.55    spl7_1 <=> v1_funct_1(sK3)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.20/0.55  fof(f153,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~v1_partfun1(sK3,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_partfun1(sK2,X0)) ) | ~spl7_18),
% 0.20/0.55    inference(avatar_component_clause,[],[f152])).
% 0.20/0.55  fof(f152,plain,(
% 0.20/0.55    spl7_18 <=> ! [X1,X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_partfun1(sK3,X0) | ~v1_partfun1(sK2,X0))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 0.20/0.55  fof(f195,plain,(
% 0.20/0.55    ( ! [X0] : (r1_tarski(sK5(sK1),X0)) ) | (~spl7_1 | ~spl7_2 | ~spl7_4 | ~spl7_5 | ~spl7_9 | ~spl7_10 | ~spl7_18)),
% 0.20/0.55    inference(resolution,[],[f192,f45])).
% 0.20/0.55  fof(f45,plain,(
% 0.20/0.55    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f19])).
% 0.20/0.55  fof(f19,plain,(
% 0.20/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.55    inference(ennf_transformation,[],[f1])).
% 0.20/0.55  fof(f1,axiom,(
% 0.20/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.55  fof(f254,plain,(
% 0.20/0.55    ~r1_tarski(k1_xboole_0,sK2) | (~spl7_1 | ~spl7_2 | ~spl7_4 | ~spl7_5 | ~spl7_9 | ~spl7_10 | spl7_16 | ~spl7_18)),
% 0.20/0.55    inference(forward_demodulation,[],[f247,f57])).
% 0.20/0.55  fof(f57,plain,(
% 0.20/0.55    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.20/0.55    inference(equality_resolution,[],[f51])).
% 0.20/0.55  fof(f51,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f4])).
% 0.20/0.55  fof(f4,axiom,(
% 0.20/0.55    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.55  fof(f247,plain,(
% 0.20/0.55    ~r1_tarski(k2_zfmisc_1(sK0,k1_xboole_0),sK2) | (~spl7_1 | ~spl7_2 | ~spl7_4 | ~spl7_5 | ~spl7_9 | ~spl7_10 | spl7_16 | ~spl7_18)),
% 0.20/0.55    inference(backward_demodulation,[],[f145,f207])).
% 0.20/0.55  fof(f207,plain,(
% 0.20/0.55    k1_xboole_0 = sK1 | (~spl7_1 | ~spl7_2 | ~spl7_4 | ~spl7_5 | ~spl7_9 | ~spl7_10 | ~spl7_18)),
% 0.20/0.55    inference(resolution,[],[f204,f37])).
% 0.20/0.55  fof(f204,plain,(
% 0.20/0.55    ( ! [X0] : (~r2_hidden(X0,sK1)) ) | (~spl7_1 | ~spl7_2 | ~spl7_4 | ~spl7_5 | ~spl7_9 | ~spl7_10 | ~spl7_18)),
% 0.20/0.55    inference(resolution,[],[f191,f56])).
% 0.20/0.55  fof(f56,plain,(
% 0.20/0.55    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.55    inference(equality_resolution,[],[f41])).
% 0.20/0.55  fof(f41,plain,(
% 0.20/0.55    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.20/0.55    inference(cnf_transformation,[],[f3])).
% 0.20/0.55  fof(f3,axiom,(
% 0.20/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.55  fof(f191,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~r1_tarski(X1,sK1) | ~r2_hidden(X0,X1)) ) | (~spl7_1 | ~spl7_2 | ~spl7_4 | ~spl7_5 | ~spl7_9 | ~spl7_10 | ~spl7_18)),
% 0.20/0.55    inference(resolution,[],[f189,f47])).
% 0.20/0.55  fof(f47,plain,(
% 0.20/0.55    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f6])).
% 0.20/0.55  fof(f6,axiom,(
% 0.20/0.55    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.55  fof(f145,plain,(
% 0.20/0.55    ~r1_tarski(k2_zfmisc_1(sK0,sK1),sK2) | spl7_16),
% 0.20/0.55    inference(avatar_component_clause,[],[f143])).
% 0.20/0.55  fof(f143,plain,(
% 0.20/0.55    spl7_16 <=> r1_tarski(k2_zfmisc_1(sK0,sK1),sK2)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 0.20/0.55  fof(f268,plain,(
% 0.20/0.55    ~spl7_1 | ~spl7_2 | ~spl7_4 | ~spl7_5 | ~spl7_9 | ~spl7_10 | spl7_14 | ~spl7_18),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f266])).
% 0.20/0.55  fof(f266,plain,(
% 0.20/0.55    $false | (~spl7_1 | ~spl7_2 | ~spl7_4 | ~spl7_5 | ~spl7_9 | ~spl7_10 | spl7_14 | ~spl7_18)),
% 0.20/0.55    inference(subsumption_resolution,[],[f253,f198])).
% 0.20/0.55  % (20115)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.55  fof(f253,plain,(
% 0.20/0.55    ~r1_tarski(k1_xboole_0,sK3) | (~spl7_1 | ~spl7_2 | ~spl7_4 | ~spl7_5 | ~spl7_9 | ~spl7_10 | spl7_14 | ~spl7_18)),
% 0.20/0.55    inference(forward_demodulation,[],[f246,f57])).
% 0.20/0.55  fof(f246,plain,(
% 0.20/0.55    ~r1_tarski(k2_zfmisc_1(sK0,k1_xboole_0),sK3) | (~spl7_1 | ~spl7_2 | ~spl7_4 | ~spl7_5 | ~spl7_9 | ~spl7_10 | spl7_14 | ~spl7_18)),
% 0.20/0.55    inference(backward_demodulation,[],[f134,f207])).
% 0.20/0.55  fof(f134,plain,(
% 0.20/0.55    ~r1_tarski(k2_zfmisc_1(sK0,sK1),sK3) | spl7_14),
% 0.20/0.55    inference(avatar_component_clause,[],[f132])).
% 0.20/0.55  fof(f132,plain,(
% 0.20/0.55    spl7_14 <=> r1_tarski(k2_zfmisc_1(sK0,sK1),sK3)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 0.20/0.55  fof(f238,plain,(
% 0.20/0.55    ~spl7_10 | spl7_20),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f237])).
% 0.20/0.55  fof(f237,plain,(
% 0.20/0.55    $false | (~spl7_10 | spl7_20)),
% 0.20/0.55    inference(subsumption_resolution,[],[f236,f111])).
% 0.20/0.55  fof(f236,plain,(
% 0.20/0.55    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl7_20),
% 0.20/0.55    inference(resolution,[],[f234,f59])).
% 0.20/0.55  fof(f59,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (r2_relset_1(X1,X2,X0,X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 0.20/0.55    inference(condensation,[],[f54])).
% 0.20/0.55  fof(f54,plain,(
% 0.20/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X2,X2)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f24])).
% 0.20/0.55  fof(f24,plain,(
% 0.20/0.55    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.55    inference(flattening,[],[f23])).
% 0.20/0.55  fof(f23,plain,(
% 0.20/0.55    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.20/0.55    inference(ennf_transformation,[],[f8])).
% 0.20/0.55  fof(f8,axiom,(
% 0.20/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).
% 0.20/0.55  fof(f234,plain,(
% 0.20/0.55    ~r2_relset_1(sK0,sK1,sK2,sK2) | spl7_20),
% 0.20/0.55    inference(avatar_component_clause,[],[f232])).
% 0.20/0.55  fof(f232,plain,(
% 0.20/0.55    spl7_20 <=> r2_relset_1(sK0,sK1,sK2,sK2)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).
% 0.20/0.55  fof(f235,plain,(
% 0.20/0.55    ~spl7_20 | spl7_6 | ~spl7_17),
% 0.20/0.55    inference(avatar_split_clause,[],[f160,f148,f90,f232])).
% 0.20/0.55  fof(f90,plain,(
% 0.20/0.55    spl7_6 <=> r2_relset_1(sK0,sK1,sK2,sK3)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.20/0.55  fof(f148,plain,(
% 0.20/0.55    spl7_17 <=> sK2 = sK3),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 0.20/0.55  fof(f160,plain,(
% 0.20/0.55    ~r2_relset_1(sK0,sK1,sK2,sK2) | (spl7_6 | ~spl7_17)),
% 0.20/0.55    inference(backward_demodulation,[],[f92,f150])).
% 0.20/0.55  fof(f150,plain,(
% 0.20/0.55    sK2 = sK3 | ~spl7_17),
% 0.20/0.55    inference(avatar_component_clause,[],[f148])).
% 0.20/0.55  fof(f92,plain,(
% 0.20/0.55    ~r2_relset_1(sK0,sK1,sK2,sK3) | spl7_6),
% 0.20/0.55    inference(avatar_component_clause,[],[f90])).
% 0.20/0.55  fof(f154,plain,(
% 0.20/0.55    spl7_17 | spl7_18 | ~spl7_1 | ~spl7_2 | ~spl7_3),
% 0.20/0.55    inference(avatar_split_clause,[],[f137,f75,f66,f61,f152,f148])).
% 0.20/0.55  fof(f75,plain,(
% 0.20/0.55    spl7_3 <=> r1_partfun1(sK2,sK3)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.20/0.55  fof(f137,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_partfun1(sK2,X0) | ~v1_partfun1(sK3,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sK2 = sK3) ) | (~spl7_1 | ~spl7_2 | ~spl7_3)),
% 0.20/0.55    inference(subsumption_resolution,[],[f136,f63])).
% 0.20/0.55  fof(f136,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_partfun1(sK2,X0) | ~v1_partfun1(sK3,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sK2 = sK3) ) | (~spl7_2 | ~spl7_3)),
% 0.20/0.55    inference(resolution,[],[f72,f77])).
% 0.20/0.55  fof(f77,plain,(
% 0.20/0.55    r1_partfun1(sK2,sK3) | ~spl7_3),
% 0.20/0.55    inference(avatar_component_clause,[],[f75])).
% 0.20/0.55  fof(f72,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~r1_partfun1(sK2,X2) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_partfun1(sK2,X0) | ~v1_partfun1(X2,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sK2 = X2) ) | ~spl7_2),
% 0.20/0.55    inference(resolution,[],[f68,f52])).
% 0.20/0.55  fof(f52,plain,(
% 0.20/0.55    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_partfun1(X2,X0) | ~v1_partfun1(X3,X0) | ~r1_partfun1(X2,X3) | X2 = X3) )),
% 0.20/0.55    inference(cnf_transformation,[],[f21])).
% 0.20/0.55  fof(f21,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (! [X3] : (X2 = X3 | ~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.20/0.55    inference(flattening,[],[f20])).
% 0.20/0.55  fof(f20,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (! [X3] : ((X2 = X3 | (~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.20/0.55    inference(ennf_transformation,[],[f11])).
% 0.20/0.55  fof(f11,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ((r1_partfun1(X2,X3) & v1_partfun1(X3,X0) & v1_partfun1(X2,X0)) => X2 = X3)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_partfun1)).
% 0.20/0.55  fof(f146,plain,(
% 0.20/0.55    spl7_15 | ~spl7_16 | ~spl7_12),
% 0.20/0.55    inference(avatar_split_clause,[],[f126,f121,f143,f139])).
% 0.20/0.55  fof(f139,plain,(
% 0.20/0.55    spl7_15 <=> sK2 = k2_zfmisc_1(sK0,sK1)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 0.20/0.55  fof(f121,plain,(
% 0.20/0.55    spl7_12 <=> r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.20/0.55  fof(f126,plain,(
% 0.20/0.55    ~r1_tarski(k2_zfmisc_1(sK0,sK1),sK2) | sK2 = k2_zfmisc_1(sK0,sK1) | ~spl7_12),
% 0.20/0.55    inference(resolution,[],[f123,f43])).
% 0.20/0.55  fof(f43,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.20/0.55    inference(cnf_transformation,[],[f3])).
% 0.20/0.55  fof(f123,plain,(
% 0.20/0.55    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) | ~spl7_12),
% 0.20/0.55    inference(avatar_component_clause,[],[f121])).
% 0.20/0.55  fof(f135,plain,(
% 0.20/0.55    spl7_13 | ~spl7_14 | ~spl7_11),
% 0.20/0.55    inference(avatar_split_clause,[],[f125,f116,f132,f128])).
% 0.20/0.55  fof(f128,plain,(
% 0.20/0.55    spl7_13 <=> sK3 = k2_zfmisc_1(sK0,sK1)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.20/0.55  fof(f116,plain,(
% 0.20/0.55    spl7_11 <=> r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.20/0.55  fof(f125,plain,(
% 0.20/0.55    ~r1_tarski(k2_zfmisc_1(sK0,sK1),sK3) | sK3 = k2_zfmisc_1(sK0,sK1) | ~spl7_11),
% 0.20/0.55    inference(resolution,[],[f118,f43])).
% 0.20/0.55  fof(f118,plain,(
% 0.20/0.55    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) | ~spl7_11),
% 0.20/0.55    inference(avatar_component_clause,[],[f116])).
% 0.20/0.55  fof(f124,plain,(
% 0.20/0.55    spl7_12 | ~spl7_10),
% 0.20/0.55    inference(avatar_split_clause,[],[f114,f109,f121])).
% 0.20/0.55  fof(f114,plain,(
% 0.20/0.55    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) | ~spl7_10),
% 0.20/0.55    inference(resolution,[],[f111,f48])).
% 0.20/0.55  fof(f48,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f6])).
% 0.20/0.55  fof(f119,plain,(
% 0.20/0.55    spl7_11 | ~spl7_9),
% 0.20/0.55    inference(avatar_split_clause,[],[f113,f104,f116])).
% 0.20/0.55  fof(f113,plain,(
% 0.20/0.55    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) | ~spl7_9),
% 0.20/0.55    inference(resolution,[],[f106,f48])).
% 0.20/0.55  fof(f112,plain,(
% 0.20/0.55    spl7_10),
% 0.20/0.55    inference(avatar_split_clause,[],[f33,f109])).
% 0.20/0.55  fof(f33,plain,(
% 0.20/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.55    inference(cnf_transformation,[],[f15])).
% 0.20/0.55  fof(f15,plain,(
% 0.20/0.55    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.20/0.55    inference(flattening,[],[f14])).
% 0.20/0.55  fof(f14,plain,(
% 0.20/0.55    ? [X0,X1,X2] : (? [X3] : (((~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_partfun1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.20/0.55    inference(ennf_transformation,[],[f13])).
% 0.20/0.55  fof(f13,negated_conjecture,(
% 0.20/0.55    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_relset_1(X0,X1,X2,X3) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 0.20/0.55    inference(negated_conjecture,[],[f12])).
% 0.20/0.55  fof(f12,conjecture,(
% 0.20/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_relset_1(X0,X1,X2,X3) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_2)).
% 0.20/0.55  fof(f107,plain,(
% 0.20/0.55    spl7_9),
% 0.20/0.55    inference(avatar_split_clause,[],[f28,f104])).
% 0.20/0.55  fof(f28,plain,(
% 0.20/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.55    inference(cnf_transformation,[],[f15])).
% 0.20/0.55  fof(f93,plain,(
% 0.20/0.55    ~spl7_6),
% 0.20/0.55    inference(avatar_split_clause,[],[f30,f90])).
% 0.20/0.55  fof(f30,plain,(
% 0.20/0.55    ~r2_relset_1(sK0,sK1,sK2,sK3)),
% 0.20/0.55    inference(cnf_transformation,[],[f15])).
% 0.20/0.55  fof(f88,plain,(
% 0.20/0.55    spl7_5),
% 0.20/0.55    inference(avatar_split_clause,[],[f32,f85])).
% 0.20/0.55  fof(f32,plain,(
% 0.20/0.55    v1_funct_2(sK2,sK0,sK1)),
% 0.20/0.55    inference(cnf_transformation,[],[f15])).
% 0.20/0.55  fof(f83,plain,(
% 0.20/0.55    spl7_4),
% 0.20/0.55    inference(avatar_split_clause,[],[f27,f80])).
% 0.20/0.55  fof(f27,plain,(
% 0.20/0.55    v1_funct_2(sK3,sK0,sK1)),
% 0.20/0.55    inference(cnf_transformation,[],[f15])).
% 0.20/0.55  fof(f78,plain,(
% 0.20/0.55    spl7_3),
% 0.20/0.55    inference(avatar_split_clause,[],[f29,f75])).
% 0.20/0.55  fof(f29,plain,(
% 0.20/0.55    r1_partfun1(sK2,sK3)),
% 0.20/0.55    inference(cnf_transformation,[],[f15])).
% 0.20/0.55  fof(f69,plain,(
% 0.20/0.55    spl7_2),
% 0.20/0.55    inference(avatar_split_clause,[],[f31,f66])).
% 0.20/0.55  fof(f31,plain,(
% 0.20/0.55    v1_funct_1(sK2)),
% 0.20/0.55    inference(cnf_transformation,[],[f15])).
% 0.20/0.55  fof(f64,plain,(
% 0.20/0.55    spl7_1),
% 0.20/0.55    inference(avatar_split_clause,[],[f26,f61])).
% 0.20/0.55  fof(f26,plain,(
% 0.20/0.55    v1_funct_1(sK3)),
% 0.20/0.55    inference(cnf_transformation,[],[f15])).
% 0.20/0.55  % SZS output end Proof for theBenchmark
% 0.20/0.55  % (20119)------------------------------
% 0.20/0.55  % (20119)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (20119)Termination reason: Refutation
% 0.20/0.55  
% 0.20/0.55  % (20119)Memory used [KB]: 10874
% 0.20/0.55  % (20119)Time elapsed: 0.127 s
% 0.20/0.55  % (20119)------------------------------
% 0.20/0.55  % (20119)------------------------------
% 0.20/0.55  % (20098)Success in time 0.192 s
%------------------------------------------------------------------------------
