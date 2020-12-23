%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : subset_1__t50_subset_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:24 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 101 expanded)
%              Number of leaves         :   16 (  35 expanded)
%              Depth                    :    8
%              Number of atoms          :  168 ( 282 expanded)
%              Number of equality atoms :   24 (  43 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f236,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f61,f65,f69,f75,f92,f125,f197,f217,f230,f235])).

fof(f235,plain,
    ( spl6_5
    | ~ spl6_8 ),
    inference(avatar_contradiction_clause,[],[f234])).

fof(f234,plain,
    ( $false
    | ~ spl6_5
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f231,f68])).

fof(f68,plain,
    ( k1_xboole_0 != sK0
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl6_5
  <=> k1_xboole_0 != sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f231,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_8 ),
    inference(resolution,[],[f229,f53])).

fof(f53,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t50_subset_1.p',t6_boole)).

fof(f229,plain,
    ( v1_xboole_0(sK0)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f228])).

fof(f228,plain,
    ( spl6_8
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f230,plain,
    ( spl6_8
    | spl6_14
    | ~ spl6_0 ),
    inference(avatar_split_clause,[],[f71,f59,f94,f228])).

fof(f94,plain,
    ( spl6_14
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f59,plain,
    ( spl6_0
  <=> m1_subset_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_0])])).

fof(f71,plain,
    ( r2_hidden(sK2,sK0)
    | v1_xboole_0(sK0)
    | ~ spl6_0 ),
    inference(resolution,[],[f60,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t50_subset_1.p',d2_subset_1)).

fof(f60,plain,
    ( m1_subset_1(sK2,sK0)
    | ~ spl6_0 ),
    inference(avatar_component_clause,[],[f59])).

fof(f217,plain,
    ( spl6_3
    | spl6_13
    | ~ spl6_14
    | ~ spl6_42 ),
    inference(avatar_contradiction_clause,[],[f216])).

fof(f216,plain,
    ( $false
    | ~ spl6_3
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_42 ),
    inference(subsumption_resolution,[],[f215,f91])).

fof(f91,plain,
    ( ~ r2_hidden(sK2,k3_subset_1(sK0,sK1))
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl6_13
  <=> ~ r2_hidden(sK2,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f215,plain,
    ( r2_hidden(sK2,k3_subset_1(sK0,sK1))
    | ~ spl6_3
    | ~ spl6_14
    | ~ spl6_42 ),
    inference(subsumption_resolution,[],[f209,f64])).

fof(f64,plain,
    ( ~ r2_hidden(sK2,sK1)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl6_3
  <=> ~ r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f209,plain,
    ( r2_hidden(sK2,sK1)
    | r2_hidden(sK2,k3_subset_1(sK0,sK1))
    | ~ spl6_14
    | ~ spl6_42 ),
    inference(superposition,[],[f192,f196])).

fof(f196,plain,
    ( k4_xboole_0(sK0,k3_subset_1(sK0,sK1)) = sK1
    | ~ spl6_42 ),
    inference(avatar_component_clause,[],[f195])).

fof(f195,plain,
    ( spl6_42
  <=> k4_xboole_0(sK0,k3_subset_1(sK0,sK1)) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).

fof(f192,plain,
    ( ! [X2] :
        ( r2_hidden(sK2,k4_xboole_0(sK0,X2))
        | r2_hidden(sK2,X2) )
    | ~ spl6_14 ),
    inference(resolution,[],[f100,f57])).

fof(f57,plain,(
    ! [X0,X3,X1] :
      ( ~ sP4(X3,X1,X0)
      | r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP4(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t50_subset_1.p',d5_xboole_0)).

fof(f100,plain,
    ( ! [X0] :
        ( sP4(sK2,X0,sK0)
        | r2_hidden(sK2,X0) )
    | ~ spl6_14 ),
    inference(resolution,[],[f95,f38])).

fof(f38,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | sP4(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f95,plain,
    ( r2_hidden(sK2,sK0)
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f94])).

fof(f197,plain,
    ( spl6_42
    | ~ spl6_6
    | ~ spl6_24 ),
    inference(avatar_split_clause,[],[f145,f123,f73,f195])).

fof(f73,plain,
    ( spl6_6
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f123,plain,
    ( spl6_24
  <=> m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f145,plain,
    ( k4_xboole_0(sK0,k3_subset_1(sK0,sK1)) = sK1
    | ~ spl6_6
    | ~ spl6_24 ),
    inference(forward_demodulation,[],[f141,f77])).

fof(f77,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,sK1)) = sK1
    | ~ spl6_6 ),
    inference(resolution,[],[f74,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t50_subset_1.p',involutiveness_k3_subset_1)).

fof(f74,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f73])).

fof(f141,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,sK1)) = k4_xboole_0(sK0,k3_subset_1(sK0,sK1))
    | ~ spl6_24 ),
    inference(resolution,[],[f124,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t50_subset_1.p',d5_subset_1)).

fof(f124,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f123])).

fof(f125,plain,
    ( spl6_24
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f76,f73,f123])).

fof(f76,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl6_6 ),
    inference(resolution,[],[f74,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t50_subset_1.p',dt_k3_subset_1)).

fof(f92,plain,(
    ~ spl6_13 ),
    inference(avatar_split_clause,[],[f32,f90])).

fof(f32,plain,(
    ~ r2_hidden(sK2,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(X2,k3_subset_1(X0,X1))
              & ~ r2_hidden(X2,X1)
              & m1_subset_1(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
      & k1_xboole_0 != X0 ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(X2,k3_subset_1(X0,X1))
              & ~ r2_hidden(X2,X1)
              & m1_subset_1(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( k1_xboole_0 != X0
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(X0))
           => ! [X2] :
                ( m1_subset_1(X2,X0)
               => ( ~ r2_hidden(X2,X1)
                 => r2_hidden(X2,k3_subset_1(X0,X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ! [X2] :
              ( m1_subset_1(X2,X0)
             => ( ~ r2_hidden(X2,X1)
               => r2_hidden(X2,k3_subset_1(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t50_subset_1.p',t50_subset_1)).

fof(f75,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f33,f73])).

fof(f33,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f69,plain,(
    ~ spl6_5 ),
    inference(avatar_split_clause,[],[f34,f67])).

fof(f34,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f21])).

fof(f65,plain,(
    ~ spl6_3 ),
    inference(avatar_split_clause,[],[f31,f63])).

fof(f31,plain,(
    ~ r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f61,plain,(
    spl6_0 ),
    inference(avatar_split_clause,[],[f30,f59])).

fof(f30,plain,(
    m1_subset_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
