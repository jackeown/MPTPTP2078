%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:31 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 430 expanded)
%              Number of leaves         :   20 ( 121 expanded)
%              Depth                    :   19
%              Number of atoms          :  492 (3428 expanded)
%              Number of equality atoms :  122 (1000 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f198,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f60,f65,f70,f75,f79,f119,f171,f186,f197])).

fof(f197,plain,
    ( ~ spl6_1
    | spl6_2
    | ~ spl6_5
    | spl6_11
    | ~ spl6_12 ),
    inference(avatar_contradiction_clause,[],[f196])).

fof(f196,plain,
    ( $false
    | ~ spl6_1
    | spl6_2
    | ~ spl6_5
    | spl6_11
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f193,f59])).

fof(f59,plain,
    ( sK2 != sK3
    | spl6_2 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl6_2
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f193,plain,
    ( sK2 = sK3
    | ~ spl6_1
    | ~ spl6_5
    | spl6_11
    | ~ spl6_12 ),
    inference(superposition,[],[f170,f191])).

fof(f191,plain,
    ( sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | ~ spl6_1
    | ~ spl6_5
    | spl6_11 ),
    inference(subsumption_resolution,[],[f190,f32])).

fof(f32,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ( ( sK2 != sK3
        & k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
        & r2_hidden(sK3,sK0)
        & r2_hidden(sK2,sK0) )
      | ~ v2_funct_1(sK1) )
    & ( ! [X4,X5] :
          ( X4 = X5
          | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5)
          | ~ r2_hidden(X5,sK0)
          | ~ r2_hidden(X4,sK0) )
      | v2_funct_1(sK1) )
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f26,f25])).

fof(f25,plain,
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
            & k1_funct_1(sK1,X2) = k1_funct_1(sK1,X3)
            & r2_hidden(X3,sK0)
            & r2_hidden(X2,sK0) )
        | ~ v2_funct_1(sK1) )
      & ( ! [X5,X4] :
            ( X4 = X5
            | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5)
            | ~ r2_hidden(X5,sK0)
            | ~ r2_hidden(X4,sK0) )
        | v2_funct_1(sK1) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X3,X2] :
        ( X2 != X3
        & k1_funct_1(sK1,X2) = k1_funct_1(sK1,X3)
        & r2_hidden(X3,sK0)
        & r2_hidden(X2,sK0) )
   => ( sK2 != sK3
      & k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
      & r2_hidden(sK3,sK0)
      & r2_hidden(sK2,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
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
    inference(rectify,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
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
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
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

fof(f190,plain,
    ( sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | ~ v1_funct_1(sK1)
    | ~ spl6_1
    | ~ spl6_5
    | spl6_11 ),
    inference(subsumption_resolution,[],[f189,f33])).

fof(f33,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f189,plain,
    ( sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl6_1
    | ~ spl6_5
    | spl6_11 ),
    inference(subsumption_resolution,[],[f188,f165])).

fof(f165,plain,
    ( k1_xboole_0 != sK0
    | spl6_11 ),
    inference(avatar_component_clause,[],[f164])).

fof(f164,plain,
    ( spl6_11
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f188,plain,
    ( sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | k1_xboole_0 = sK0
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl6_1
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f187,f54])).

fof(f54,plain,
    ( v2_funct_1(sK1)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl6_1
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f187,plain,
    ( sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | ~ v2_funct_1(sK1)
    | k1_xboole_0 = sK0
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl6_5 ),
    inference(resolution,[],[f150,f34])).

fof(f34,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f150,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
        | sK2 = k1_funct_1(k2_funct_1(X2),k1_funct_1(X2,sK2))
        | ~ v2_funct_1(X2)
        | k1_xboole_0 = X1
        | ~ v1_funct_2(X2,sK0,X1)
        | ~ v1_funct_1(X2) )
    | ~ spl6_5 ),
    inference(resolution,[],[f74,f51])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X1
      | k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f20])).

% (31490)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( ( r2_hidden(X2,X0)
          & v2_funct_1(X3) )
       => ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_funct_2)).

fof(f74,plain,
    ( r2_hidden(sK2,sK0)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl6_5
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f170,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f168])).

fof(f168,plain,
    ( spl6_12
  <=> sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f186,plain,
    ( ~ spl6_5
    | ~ spl6_11 ),
    inference(avatar_contradiction_clause,[],[f185])).

fof(f185,plain,
    ( $false
    | ~ spl6_5
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f182,f40])).

fof(f40,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f182,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | ~ spl6_5
    | ~ spl6_11 ),
    inference(superposition,[],[f152,f166])).

fof(f166,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f164])).

fof(f152,plain,
    ( ~ r1_tarski(sK0,sK2)
    | ~ spl6_5 ),
    inference(resolution,[],[f74,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f171,plain,
    ( spl6_11
    | spl6_12
    | ~ spl6_1
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f162,f67,f62,f53,f168,f164])).

fof(f62,plain,
    ( spl6_3
  <=> k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f67,plain,
    ( spl6_4
  <=> r2_hidden(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f162,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | k1_xboole_0 = sK0
    | ~ spl6_1
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(forward_demodulation,[],[f161,f64])).

fof(f64,plain,
    ( k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f62])).

fof(f161,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3))
    | k1_xboole_0 = sK0
    | ~ spl6_1
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f160,f32])).

fof(f160,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3))
    | k1_xboole_0 = sK0
    | ~ v1_funct_1(sK1)
    | ~ spl6_1
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f159,f33])).

fof(f159,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3))
    | k1_xboole_0 = sK0
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl6_1
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f158,f54])).

fof(f158,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3))
    | ~ v2_funct_1(sK1)
    | k1_xboole_0 = sK0
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl6_4 ),
    inference(resolution,[],[f145,f34])).

fof(f145,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
        | sK3 = k1_funct_1(k2_funct_1(X2),k1_funct_1(X2,sK3))
        | ~ v2_funct_1(X2)
        | k1_xboole_0 = X1
        | ~ v1_funct_2(X2,sK0,X1)
        | ~ v1_funct_1(X2) )
    | ~ spl6_4 ),
    inference(resolution,[],[f69,f51])).

fof(f69,plain,
    ( r2_hidden(sK3,sK0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f67])).

fof(f119,plain,
    ( spl6_1
    | ~ spl6_6 ),
    inference(avatar_contradiction_clause,[],[f118])).

fof(f118,plain,
    ( $false
    | spl6_1
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f117,f97])).

fof(f97,plain,
    ( k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))
    | spl6_1 ),
    inference(subsumption_resolution,[],[f96,f80])).

fof(f80,plain,(
    v1_relat_1(sK1) ),
    inference(resolution,[],[f48,f34])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f96,plain,
    ( k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))
    | ~ v1_relat_1(sK1)
    | spl6_1 ),
    inference(subsumption_resolution,[],[f95,f55])).

fof(f55,plain,
    ( ~ v2_funct_1(sK1)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f53])).

fof(f95,plain,
    ( k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))
    | v2_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f44,f32])).

fof(f44,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0))
      | v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ( sK4(X0) != sK5(X0)
            & k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0))
            & r2_hidden(sK5(X0),k1_relat_1(X0))
            & r2_hidden(sK4(X0),k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f29,f30])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( X1 != X2
          & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
          & r2_hidden(X2,k1_relat_1(X0))
          & r2_hidden(X1,k1_relat_1(X0)) )
     => ( sK4(X0) != sK5(X0)
        & k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0))
        & r2_hidden(sK5(X0),k1_relat_1(X0))
        & r2_hidden(sK4(X0),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
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
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
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
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f117,plain,
    ( k1_funct_1(sK1,sK4(sK1)) != k1_funct_1(sK1,sK5(sK1))
    | spl6_1
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f116,f89])).

fof(f89,plain,
    ( sK4(sK1) != sK5(sK1)
    | spl6_1 ),
    inference(subsumption_resolution,[],[f88,f80])).

fof(f88,plain,
    ( sK4(sK1) != sK5(sK1)
    | ~ v1_relat_1(sK1)
    | spl6_1 ),
    inference(subsumption_resolution,[],[f87,f55])).

fof(f87,plain,
    ( sK4(sK1) != sK5(sK1)
    | v2_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f45,f32])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | sK4(X0) != sK5(X0)
      | v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f116,plain,
    ( sK4(sK1) = sK5(sK1)
    | k1_funct_1(sK1,sK4(sK1)) != k1_funct_1(sK1,sK5(sK1))
    | spl6_1
    | ~ spl6_6 ),
    inference(resolution,[],[f105,f109])).

fof(f109,plain,
    ( r2_hidden(sK5(sK1),sK0)
    | spl6_1 ),
    inference(resolution,[],[f102,f92])).

fof(f92,plain,(
    m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(sK0)) ),
    inference(forward_demodulation,[],[f91,f90])).

fof(f90,plain,(
    k1_relat_1(sK1) = k1_relset_1(sK0,sK0,sK1) ),
    inference(resolution,[],[f49,f34])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f91,plain,(
    m1_subset_1(k1_relset_1(sK0,sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f50,f34])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(f102,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(X3))
        | r2_hidden(sK5(sK1),X3) )
    | spl6_1 ),
    inference(resolution,[],[f86,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f86,plain,
    ( r2_hidden(sK5(sK1),k1_relat_1(sK1))
    | spl6_1 ),
    inference(subsumption_resolution,[],[f85,f80])).

fof(f85,plain,
    ( r2_hidden(sK5(sK1),k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | spl6_1 ),
    inference(subsumption_resolution,[],[f84,f55])).

fof(f84,plain,
    ( r2_hidden(sK5(sK1),k1_relat_1(sK1))
    | v2_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f43,f32])).

fof(f43,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | r2_hidden(sK5(X0),k1_relat_1(X0))
      | v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f105,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | sK4(sK1) = X0
        | k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1)) )
    | spl6_1
    | ~ spl6_6 ),
    inference(resolution,[],[f104,f78])).

fof(f78,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(X4,sK0)
        | X4 = X5
        | ~ r2_hidden(X5,sK0)
        | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5) )
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl6_6
  <=> ! [X5,X4] :
        ( X4 = X5
        | ~ r2_hidden(X4,sK0)
        | ~ r2_hidden(X5,sK0)
        | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f104,plain,
    ( r2_hidden(sK4(sK1),sK0)
    | spl6_1 ),
    inference(resolution,[],[f93,f92])).

fof(f93,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(X0))
        | r2_hidden(sK4(sK1),X0) )
    | spl6_1 ),
    inference(resolution,[],[f83,f46])).

fof(f83,plain,
    ( r2_hidden(sK4(sK1),k1_relat_1(sK1))
    | spl6_1 ),
    inference(subsumption_resolution,[],[f82,f80])).

fof(f82,plain,
    ( r2_hidden(sK4(sK1),k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | spl6_1 ),
    inference(subsumption_resolution,[],[f81,f55])).

fof(f81,plain,
    ( r2_hidden(sK4(sK1),k1_relat_1(sK1))
    | v2_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f42,f32])).

fof(f42,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | r2_hidden(sK4(X0),k1_relat_1(X0))
      | v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f79,plain,
    ( spl6_1
    | spl6_6 ),
    inference(avatar_split_clause,[],[f35,f77,f53])).

fof(f35,plain,(
    ! [X4,X5] :
      ( X4 = X5
      | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5)
      | ~ r2_hidden(X5,sK0)
      | ~ r2_hidden(X4,sK0)
      | v2_funct_1(sK1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f75,plain,
    ( ~ spl6_1
    | spl6_5 ),
    inference(avatar_split_clause,[],[f36,f72,f53])).

fof(f36,plain,
    ( r2_hidden(sK2,sK0)
    | ~ v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f70,plain,
    ( ~ spl6_1
    | spl6_4 ),
    inference(avatar_split_clause,[],[f37,f67,f53])).

fof(f37,plain,
    ( r2_hidden(sK3,sK0)
    | ~ v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f65,plain,
    ( ~ spl6_1
    | spl6_3 ),
    inference(avatar_split_clause,[],[f38,f62,f53])).

fof(f38,plain,
    ( k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
    | ~ v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f60,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f39,f57,f53])).

fof(f39,plain,
    ( sK2 != sK3
    | ~ v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:12:47 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.46  % (31482)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.19/0.46  % (31482)Refutation found. Thanks to Tanya!
% 0.19/0.46  % SZS status Theorem for theBenchmark
% 0.19/0.46  % SZS output start Proof for theBenchmark
% 0.19/0.46  fof(f198,plain,(
% 0.19/0.46    $false),
% 0.19/0.46    inference(avatar_sat_refutation,[],[f60,f65,f70,f75,f79,f119,f171,f186,f197])).
% 0.19/0.46  fof(f197,plain,(
% 0.19/0.46    ~spl6_1 | spl6_2 | ~spl6_5 | spl6_11 | ~spl6_12),
% 0.19/0.46    inference(avatar_contradiction_clause,[],[f196])).
% 0.19/0.46  fof(f196,plain,(
% 0.19/0.46    $false | (~spl6_1 | spl6_2 | ~spl6_5 | spl6_11 | ~spl6_12)),
% 0.19/0.46    inference(subsumption_resolution,[],[f193,f59])).
% 0.19/0.46  fof(f59,plain,(
% 0.19/0.46    sK2 != sK3 | spl6_2),
% 0.19/0.46    inference(avatar_component_clause,[],[f57])).
% 0.19/0.46  fof(f57,plain,(
% 0.19/0.46    spl6_2 <=> sK2 = sK3),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.19/0.46  fof(f193,plain,(
% 0.19/0.46    sK2 = sK3 | (~spl6_1 | ~spl6_5 | spl6_11 | ~spl6_12)),
% 0.19/0.46    inference(superposition,[],[f170,f191])).
% 0.19/0.46  fof(f191,plain,(
% 0.19/0.46    sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | (~spl6_1 | ~spl6_5 | spl6_11)),
% 0.19/0.46    inference(subsumption_resolution,[],[f190,f32])).
% 0.19/0.46  fof(f32,plain,(
% 0.19/0.46    v1_funct_1(sK1)),
% 0.19/0.46    inference(cnf_transformation,[],[f27])).
% 0.19/0.46  fof(f27,plain,(
% 0.19/0.46    ((sK2 != sK3 & k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) & r2_hidden(sK3,sK0) & r2_hidden(sK2,sK0)) | ~v2_funct_1(sK1)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5) | ~r2_hidden(X5,sK0) | ~r2_hidden(X4,sK0)) | v2_funct_1(sK1)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 0.19/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f26,f25])).
% 0.19/0.46  fof(f25,plain,(
% 0.19/0.46    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(X1,X4) != k1_funct_1(X1,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((? [X3,X2] : (X2 != X3 & k1_funct_1(sK1,X2) = k1_funct_1(sK1,X3) & r2_hidden(X3,sK0) & r2_hidden(X2,sK0)) | ~v2_funct_1(sK1)) & (! [X5,X4] : (X4 = X5 | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5) | ~r2_hidden(X5,sK0) | ~r2_hidden(X4,sK0)) | v2_funct_1(sK1)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 0.19/0.46    introduced(choice_axiom,[])).
% 0.19/0.46  fof(f26,plain,(
% 0.19/0.46    ? [X3,X2] : (X2 != X3 & k1_funct_1(sK1,X2) = k1_funct_1(sK1,X3) & r2_hidden(X3,sK0) & r2_hidden(X2,sK0)) => (sK2 != sK3 & k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) & r2_hidden(sK3,sK0) & r2_hidden(sK2,sK0))),
% 0.19/0.46    introduced(choice_axiom,[])).
% 0.19/0.46  fof(f24,plain,(
% 0.19/0.46    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(X1,X4) != k1_funct_1(X1,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.19/0.46    inference(rectify,[],[f23])).
% 0.19/0.46  fof(f23,plain,(
% 0.19/0.46    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.19/0.46    inference(flattening,[],[f22])).
% 0.19/0.46  fof(f22,plain,(
% 0.19/0.46    ? [X0,X1] : (((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) | v2_funct_1(X1))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.19/0.46    inference(nnf_transformation,[],[f12])).
% 0.19/0.46  fof(f12,plain,(
% 0.19/0.46    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.19/0.46    inference(flattening,[],[f11])).
% 0.19/0.46  fof(f11,plain,(
% 0.19/0.46    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | (k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 0.19/0.46    inference(ennf_transformation,[],[f10])).
% 0.19/0.46  fof(f10,negated_conjecture,(
% 0.19/0.46    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 0.19/0.46    inference(negated_conjecture,[],[f9])).
% 0.19/0.46  fof(f9,conjecture,(
% 0.19/0.46    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 0.19/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_funct_2)).
% 0.19/0.46  fof(f190,plain,(
% 0.19/0.46    sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | ~v1_funct_1(sK1) | (~spl6_1 | ~spl6_5 | spl6_11)),
% 0.19/0.46    inference(subsumption_resolution,[],[f189,f33])).
% 0.19/0.46  fof(f33,plain,(
% 0.19/0.46    v1_funct_2(sK1,sK0,sK0)),
% 0.19/0.46    inference(cnf_transformation,[],[f27])).
% 0.19/0.46  fof(f189,plain,(
% 0.19/0.46    sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | (~spl6_1 | ~spl6_5 | spl6_11)),
% 0.19/0.46    inference(subsumption_resolution,[],[f188,f165])).
% 0.19/0.46  fof(f165,plain,(
% 0.19/0.46    k1_xboole_0 != sK0 | spl6_11),
% 0.19/0.46    inference(avatar_component_clause,[],[f164])).
% 0.19/0.46  fof(f164,plain,(
% 0.19/0.46    spl6_11 <=> k1_xboole_0 = sK0),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.19/0.46  fof(f188,plain,(
% 0.19/0.46    sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | k1_xboole_0 = sK0 | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | (~spl6_1 | ~spl6_5)),
% 0.19/0.46    inference(subsumption_resolution,[],[f187,f54])).
% 0.19/0.46  fof(f54,plain,(
% 0.19/0.46    v2_funct_1(sK1) | ~spl6_1),
% 0.19/0.46    inference(avatar_component_clause,[],[f53])).
% 0.19/0.46  fof(f53,plain,(
% 0.19/0.46    spl6_1 <=> v2_funct_1(sK1)),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.19/0.46  fof(f187,plain,(
% 0.19/0.46    sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | ~v2_funct_1(sK1) | k1_xboole_0 = sK0 | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~spl6_5),
% 0.19/0.46    inference(resolution,[],[f150,f34])).
% 0.19/0.46  fof(f34,plain,(
% 0.19/0.46    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.19/0.46    inference(cnf_transformation,[],[f27])).
% 0.19/0.46  fof(f150,plain,(
% 0.19/0.46    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) | sK2 = k1_funct_1(k2_funct_1(X2),k1_funct_1(X2,sK2)) | ~v2_funct_1(X2) | k1_xboole_0 = X1 | ~v1_funct_2(X2,sK0,X1) | ~v1_funct_1(X2)) ) | ~spl6_5),
% 0.19/0.46    inference(resolution,[],[f74,f51])).
% 0.19/0.46  fof(f51,plain,(
% 0.19/0.46    ( ! [X2,X0,X3,X1] : (~r2_hidden(X2,X0) | k1_xboole_0 = X1 | k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | ~v2_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f21])).
% 0.19/0.46  fof(f21,plain,(
% 0.19/0.46    ! [X0,X1,X2,X3] : (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v2_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.19/0.46    inference(flattening,[],[f20])).
% 0.19/0.46  % (31490)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.19/0.46  fof(f20,plain,(
% 0.19/0.46    ! [X0,X1,X2,X3] : (((k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1) | (~r2_hidden(X2,X0) | ~v2_funct_1(X3))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.19/0.46    inference(ennf_transformation,[],[f8])).
% 0.19/0.46  fof(f8,axiom,(
% 0.19/0.46    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((r2_hidden(X2,X0) & v2_funct_1(X3)) => (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1)))),
% 0.19/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_funct_2)).
% 0.19/0.46  fof(f74,plain,(
% 0.19/0.46    r2_hidden(sK2,sK0) | ~spl6_5),
% 0.19/0.46    inference(avatar_component_clause,[],[f72])).
% 0.19/0.46  fof(f72,plain,(
% 0.19/0.46    spl6_5 <=> r2_hidden(sK2,sK0)),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.19/0.46  fof(f170,plain,(
% 0.19/0.46    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | ~spl6_12),
% 0.19/0.46    inference(avatar_component_clause,[],[f168])).
% 0.19/0.46  fof(f168,plain,(
% 0.19/0.46    spl6_12 <=> sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.19/0.46  fof(f186,plain,(
% 0.19/0.46    ~spl6_5 | ~spl6_11),
% 0.19/0.46    inference(avatar_contradiction_clause,[],[f185])).
% 0.19/0.46  fof(f185,plain,(
% 0.19/0.46    $false | (~spl6_5 | ~spl6_11)),
% 0.19/0.46    inference(subsumption_resolution,[],[f182,f40])).
% 0.19/0.46  fof(f40,plain,(
% 0.19/0.46    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f1])).
% 0.19/0.46  fof(f1,axiom,(
% 0.19/0.46    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.19/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.19/0.46  fof(f182,plain,(
% 0.19/0.46    ~r1_tarski(k1_xboole_0,sK2) | (~spl6_5 | ~spl6_11)),
% 0.19/0.46    inference(superposition,[],[f152,f166])).
% 0.19/0.46  fof(f166,plain,(
% 0.19/0.46    k1_xboole_0 = sK0 | ~spl6_11),
% 0.19/0.46    inference(avatar_component_clause,[],[f164])).
% 0.19/0.46  fof(f152,plain,(
% 0.19/0.46    ~r1_tarski(sK0,sK2) | ~spl6_5),
% 0.19/0.46    inference(resolution,[],[f74,f47])).
% 0.19/0.46  fof(f47,plain,(
% 0.19/0.46    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f16])).
% 0.19/0.46  fof(f16,plain,(
% 0.19/0.46    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.19/0.46    inference(ennf_transformation,[],[f4])).
% 0.19/0.46  fof(f4,axiom,(
% 0.19/0.46    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.19/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.19/0.46  fof(f171,plain,(
% 0.19/0.46    spl6_11 | spl6_12 | ~spl6_1 | ~spl6_3 | ~spl6_4),
% 0.19/0.46    inference(avatar_split_clause,[],[f162,f67,f62,f53,f168,f164])).
% 0.19/0.46  fof(f62,plain,(
% 0.19/0.46    spl6_3 <=> k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.19/0.46  fof(f67,plain,(
% 0.19/0.46    spl6_4 <=> r2_hidden(sK3,sK0)),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.19/0.46  fof(f162,plain,(
% 0.19/0.46    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | k1_xboole_0 = sK0 | (~spl6_1 | ~spl6_3 | ~spl6_4)),
% 0.19/0.46    inference(forward_demodulation,[],[f161,f64])).
% 0.19/0.46  fof(f64,plain,(
% 0.19/0.46    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) | ~spl6_3),
% 0.19/0.46    inference(avatar_component_clause,[],[f62])).
% 0.19/0.46  fof(f161,plain,(
% 0.19/0.46    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3)) | k1_xboole_0 = sK0 | (~spl6_1 | ~spl6_4)),
% 0.19/0.46    inference(subsumption_resolution,[],[f160,f32])).
% 0.19/0.46  fof(f160,plain,(
% 0.19/0.46    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3)) | k1_xboole_0 = sK0 | ~v1_funct_1(sK1) | (~spl6_1 | ~spl6_4)),
% 0.19/0.46    inference(subsumption_resolution,[],[f159,f33])).
% 0.19/0.46  fof(f159,plain,(
% 0.19/0.46    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3)) | k1_xboole_0 = sK0 | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | (~spl6_1 | ~spl6_4)),
% 0.19/0.46    inference(subsumption_resolution,[],[f158,f54])).
% 0.19/0.46  fof(f158,plain,(
% 0.19/0.46    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3)) | ~v2_funct_1(sK1) | k1_xboole_0 = sK0 | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~spl6_4),
% 0.19/0.46    inference(resolution,[],[f145,f34])).
% 0.19/0.46  fof(f145,plain,(
% 0.19/0.46    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) | sK3 = k1_funct_1(k2_funct_1(X2),k1_funct_1(X2,sK3)) | ~v2_funct_1(X2) | k1_xboole_0 = X1 | ~v1_funct_2(X2,sK0,X1) | ~v1_funct_1(X2)) ) | ~spl6_4),
% 0.19/0.46    inference(resolution,[],[f69,f51])).
% 0.19/0.46  fof(f69,plain,(
% 0.19/0.46    r2_hidden(sK3,sK0) | ~spl6_4),
% 0.19/0.46    inference(avatar_component_clause,[],[f67])).
% 0.19/0.46  fof(f119,plain,(
% 0.19/0.46    spl6_1 | ~spl6_6),
% 0.19/0.46    inference(avatar_contradiction_clause,[],[f118])).
% 0.19/0.46  fof(f118,plain,(
% 0.19/0.46    $false | (spl6_1 | ~spl6_6)),
% 0.19/0.46    inference(subsumption_resolution,[],[f117,f97])).
% 0.19/0.46  fof(f97,plain,(
% 0.19/0.46    k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) | spl6_1),
% 0.19/0.46    inference(subsumption_resolution,[],[f96,f80])).
% 0.19/0.46  fof(f80,plain,(
% 0.19/0.46    v1_relat_1(sK1)),
% 0.19/0.46    inference(resolution,[],[f48,f34])).
% 0.19/0.46  fof(f48,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f17])).
% 0.19/0.46  fof(f17,plain,(
% 0.19/0.46    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.46    inference(ennf_transformation,[],[f5])).
% 0.19/0.47  fof(f5,axiom,(
% 0.19/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.19/0.47  fof(f96,plain,(
% 0.19/0.47    k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) | ~v1_relat_1(sK1) | spl6_1),
% 0.19/0.47    inference(subsumption_resolution,[],[f95,f55])).
% 0.19/0.47  fof(f55,plain,(
% 0.19/0.47    ~v2_funct_1(sK1) | spl6_1),
% 0.19/0.47    inference(avatar_component_clause,[],[f53])).
% 0.19/0.47  fof(f95,plain,(
% 0.19/0.47    k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) | v2_funct_1(sK1) | ~v1_relat_1(sK1)),
% 0.19/0.47    inference(resolution,[],[f44,f32])).
% 0.19/0.47  fof(f44,plain,(
% 0.19/0.47    ( ! [X0] : (~v1_funct_1(X0) | k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0)) | v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f31])).
% 0.19/0.47  fof(f31,plain,(
% 0.19/0.47    ! [X0] : (((v2_funct_1(X0) | (sK4(X0) != sK5(X0) & k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0)) & r2_hidden(sK5(X0),k1_relat_1(X0)) & r2_hidden(sK4(X0),k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.19/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f29,f30])).
% 0.19/0.47  fof(f30,plain,(
% 0.19/0.47    ! [X0] : (? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => (sK4(X0) != sK5(X0) & k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0)) & r2_hidden(sK5(X0),k1_relat_1(X0)) & r2_hidden(sK4(X0),k1_relat_1(X0))))),
% 0.19/0.47    introduced(choice_axiom,[])).
% 0.19/0.47  fof(f29,plain,(
% 0.19/0.47    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.19/0.47    inference(rectify,[],[f28])).
% 0.19/0.47  fof(f28,plain,(
% 0.19/0.47    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.19/0.47    inference(nnf_transformation,[],[f14])).
% 0.19/0.47  fof(f14,plain,(
% 0.19/0.47    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.19/0.47    inference(flattening,[],[f13])).
% 0.19/0.47  fof(f13,plain,(
% 0.19/0.47    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | (k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.19/0.47    inference(ennf_transformation,[],[f3])).
% 0.19/0.47  fof(f3,axiom,(
% 0.19/0.47    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1,X2] : ((k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => X1 = X2)))),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).
% 0.19/0.47  fof(f117,plain,(
% 0.19/0.47    k1_funct_1(sK1,sK4(sK1)) != k1_funct_1(sK1,sK5(sK1)) | (spl6_1 | ~spl6_6)),
% 0.19/0.47    inference(subsumption_resolution,[],[f116,f89])).
% 0.19/0.47  fof(f89,plain,(
% 0.19/0.47    sK4(sK1) != sK5(sK1) | spl6_1),
% 0.19/0.47    inference(subsumption_resolution,[],[f88,f80])).
% 0.19/0.47  fof(f88,plain,(
% 0.19/0.47    sK4(sK1) != sK5(sK1) | ~v1_relat_1(sK1) | spl6_1),
% 0.19/0.47    inference(subsumption_resolution,[],[f87,f55])).
% 0.19/0.47  fof(f87,plain,(
% 0.19/0.47    sK4(sK1) != sK5(sK1) | v2_funct_1(sK1) | ~v1_relat_1(sK1)),
% 0.19/0.47    inference(resolution,[],[f45,f32])).
% 0.19/0.47  fof(f45,plain,(
% 0.19/0.47    ( ! [X0] : (~v1_funct_1(X0) | sK4(X0) != sK5(X0) | v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f31])).
% 0.19/0.47  fof(f116,plain,(
% 0.19/0.47    sK4(sK1) = sK5(sK1) | k1_funct_1(sK1,sK4(sK1)) != k1_funct_1(sK1,sK5(sK1)) | (spl6_1 | ~spl6_6)),
% 0.19/0.47    inference(resolution,[],[f105,f109])).
% 0.19/0.47  fof(f109,plain,(
% 0.19/0.47    r2_hidden(sK5(sK1),sK0) | spl6_1),
% 0.19/0.47    inference(resolution,[],[f102,f92])).
% 0.19/0.47  fof(f92,plain,(
% 0.19/0.47    m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(sK0))),
% 0.19/0.47    inference(forward_demodulation,[],[f91,f90])).
% 0.19/0.47  fof(f90,plain,(
% 0.19/0.47    k1_relat_1(sK1) = k1_relset_1(sK0,sK0,sK1)),
% 0.19/0.47    inference(resolution,[],[f49,f34])).
% 0.19/0.47  fof(f49,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f18])).
% 0.19/0.47  fof(f18,plain,(
% 0.19/0.47    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.47    inference(ennf_transformation,[],[f7])).
% 0.19/0.47  fof(f7,axiom,(
% 0.19/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.19/0.47  fof(f91,plain,(
% 0.19/0.47    m1_subset_1(k1_relset_1(sK0,sK0,sK1),k1_zfmisc_1(sK0))),
% 0.19/0.47    inference(resolution,[],[f50,f34])).
% 0.19/0.47  fof(f50,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))) )),
% 0.19/0.47    inference(cnf_transformation,[],[f19])).
% 0.19/0.47  fof(f19,plain,(
% 0.19/0.47    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.47    inference(ennf_transformation,[],[f6])).
% 0.19/0.47  fof(f6,axiom,(
% 0.19/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).
% 0.19/0.47  fof(f102,plain,(
% 0.19/0.47    ( ! [X3] : (~m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(X3)) | r2_hidden(sK5(sK1),X3)) ) | spl6_1),
% 0.19/0.47    inference(resolution,[],[f86,f46])).
% 0.19/0.47  fof(f46,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | r2_hidden(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.19/0.47    inference(cnf_transformation,[],[f15])).
% 0.19/0.47  fof(f15,plain,(
% 0.19/0.47    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.47    inference(ennf_transformation,[],[f2])).
% 0.19/0.47  fof(f2,axiom,(
% 0.19/0.47    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.19/0.47  fof(f86,plain,(
% 0.19/0.47    r2_hidden(sK5(sK1),k1_relat_1(sK1)) | spl6_1),
% 0.19/0.47    inference(subsumption_resolution,[],[f85,f80])).
% 0.19/0.47  fof(f85,plain,(
% 0.19/0.47    r2_hidden(sK5(sK1),k1_relat_1(sK1)) | ~v1_relat_1(sK1) | spl6_1),
% 0.19/0.47    inference(subsumption_resolution,[],[f84,f55])).
% 0.19/0.47  fof(f84,plain,(
% 0.19/0.47    r2_hidden(sK5(sK1),k1_relat_1(sK1)) | v2_funct_1(sK1) | ~v1_relat_1(sK1)),
% 0.19/0.47    inference(resolution,[],[f43,f32])).
% 0.19/0.47  fof(f43,plain,(
% 0.19/0.47    ( ! [X0] : (~v1_funct_1(X0) | r2_hidden(sK5(X0),k1_relat_1(X0)) | v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f31])).
% 0.19/0.47  fof(f105,plain,(
% 0.19/0.47    ( ! [X0] : (~r2_hidden(X0,sK0) | sK4(sK1) = X0 | k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1))) ) | (spl6_1 | ~spl6_6)),
% 0.19/0.47    inference(resolution,[],[f104,f78])).
% 0.19/0.47  fof(f78,plain,(
% 0.19/0.47    ( ! [X4,X5] : (~r2_hidden(X4,sK0) | X4 = X5 | ~r2_hidden(X5,sK0) | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5)) ) | ~spl6_6),
% 0.19/0.47    inference(avatar_component_clause,[],[f77])).
% 0.19/0.47  fof(f77,plain,(
% 0.19/0.47    spl6_6 <=> ! [X5,X4] : (X4 = X5 | ~r2_hidden(X4,sK0) | ~r2_hidden(X5,sK0) | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5))),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.19/0.47  fof(f104,plain,(
% 0.19/0.47    r2_hidden(sK4(sK1),sK0) | spl6_1),
% 0.19/0.47    inference(resolution,[],[f93,f92])).
% 0.19/0.47  fof(f93,plain,(
% 0.19/0.47    ( ! [X0] : (~m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(X0)) | r2_hidden(sK4(sK1),X0)) ) | spl6_1),
% 0.19/0.47    inference(resolution,[],[f83,f46])).
% 0.19/0.47  fof(f83,plain,(
% 0.19/0.47    r2_hidden(sK4(sK1),k1_relat_1(sK1)) | spl6_1),
% 0.19/0.47    inference(subsumption_resolution,[],[f82,f80])).
% 0.19/0.47  fof(f82,plain,(
% 0.19/0.47    r2_hidden(sK4(sK1),k1_relat_1(sK1)) | ~v1_relat_1(sK1) | spl6_1),
% 0.19/0.47    inference(subsumption_resolution,[],[f81,f55])).
% 0.19/0.47  fof(f81,plain,(
% 0.19/0.47    r2_hidden(sK4(sK1),k1_relat_1(sK1)) | v2_funct_1(sK1) | ~v1_relat_1(sK1)),
% 0.19/0.47    inference(resolution,[],[f42,f32])).
% 0.19/0.47  fof(f42,plain,(
% 0.19/0.47    ( ! [X0] : (~v1_funct_1(X0) | r2_hidden(sK4(X0),k1_relat_1(X0)) | v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f31])).
% 0.19/0.47  fof(f79,plain,(
% 0.19/0.47    spl6_1 | spl6_6),
% 0.19/0.47    inference(avatar_split_clause,[],[f35,f77,f53])).
% 0.19/0.47  fof(f35,plain,(
% 0.19/0.47    ( ! [X4,X5] : (X4 = X5 | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5) | ~r2_hidden(X5,sK0) | ~r2_hidden(X4,sK0) | v2_funct_1(sK1)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f27])).
% 0.19/0.47  fof(f75,plain,(
% 0.19/0.47    ~spl6_1 | spl6_5),
% 0.19/0.47    inference(avatar_split_clause,[],[f36,f72,f53])).
% 0.19/0.47  fof(f36,plain,(
% 0.19/0.47    r2_hidden(sK2,sK0) | ~v2_funct_1(sK1)),
% 0.19/0.47    inference(cnf_transformation,[],[f27])).
% 0.19/0.47  fof(f70,plain,(
% 0.19/0.47    ~spl6_1 | spl6_4),
% 0.19/0.47    inference(avatar_split_clause,[],[f37,f67,f53])).
% 0.19/0.47  fof(f37,plain,(
% 0.19/0.47    r2_hidden(sK3,sK0) | ~v2_funct_1(sK1)),
% 0.19/0.47    inference(cnf_transformation,[],[f27])).
% 0.19/0.47  fof(f65,plain,(
% 0.19/0.47    ~spl6_1 | spl6_3),
% 0.19/0.47    inference(avatar_split_clause,[],[f38,f62,f53])).
% 0.19/0.47  fof(f38,plain,(
% 0.19/0.47    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) | ~v2_funct_1(sK1)),
% 0.19/0.47    inference(cnf_transformation,[],[f27])).
% 0.19/0.47  fof(f60,plain,(
% 0.19/0.47    ~spl6_1 | ~spl6_2),
% 0.19/0.47    inference(avatar_split_clause,[],[f39,f57,f53])).
% 0.19/0.47  fof(f39,plain,(
% 0.19/0.47    sK2 != sK3 | ~v2_funct_1(sK1)),
% 0.19/0.47    inference(cnf_transformation,[],[f27])).
% 0.19/0.47  % SZS output end Proof for theBenchmark
% 0.19/0.47  % (31482)------------------------------
% 0.19/0.47  % (31482)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.47  % (31482)Termination reason: Refutation
% 0.19/0.47  
% 0.19/0.47  % (31482)Memory used [KB]: 10746
% 0.19/0.47  % (31482)Time elapsed: 0.061 s
% 0.19/0.47  % (31482)------------------------------
% 0.19/0.47  % (31482)------------------------------
% 0.19/0.47  % (31471)Success in time 0.121 s
%------------------------------------------------------------------------------
