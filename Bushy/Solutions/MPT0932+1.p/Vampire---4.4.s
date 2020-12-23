%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : mcart_1__t93_mcart_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:16 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   54 (  78 expanded)
%              Number of leaves         :   12 (  28 expanded)
%              Depth                    :   11
%              Number of atoms          :  145 ( 199 expanded)
%              Number of equality atoms :   15 (  15 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f175,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f72,f79,f88,f108,f167,f174])).

fof(f174,plain,
    ( ~ spl5_2
    | spl5_11 ),
    inference(avatar_contradiction_clause,[],[f173])).

fof(f173,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_11 ),
    inference(subsumption_resolution,[],[f172,f71])).

fof(f71,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl5_2
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f172,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ spl5_11 ),
    inference(resolution,[],[f166,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t93_mcart_1.p',t1_subset)).

fof(f166,plain,
    ( ~ m1_subset_1(sK1,sK0)
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f165])).

fof(f165,plain,
    ( spl5_11
  <=> ~ m1_subset_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f167,plain,
    ( ~ spl5_11
    | ~ spl5_0
    | spl5_5
    | spl5_7 ),
    inference(avatar_split_clause,[],[f148,f86,f77,f63,f165])).

fof(f63,plain,
    ( spl5_0
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_0])])).

fof(f77,plain,
    ( spl5_5
  <=> ~ r2_hidden(k2_mcart_1(sK1),k11_relat_1(sK0,k1_mcart_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f86,plain,
    ( spl5_7
  <=> ~ v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f148,plain,
    ( ~ m1_subset_1(sK1,sK0)
    | ~ spl5_0
    | ~ spl5_5
    | ~ spl5_7 ),
    inference(resolution,[],[f129,f78])).

fof(f78,plain,
    ( ~ r2_hidden(k2_mcart_1(sK1),k11_relat_1(sK0,k1_mcart_1(sK1)))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f77])).

fof(f129,plain,
    ( ! [X0] :
        ( r2_hidden(k2_mcart_1(X0),k11_relat_1(sK0,k1_mcart_1(X0)))
        | ~ m1_subset_1(X0,sK0) )
    | ~ spl5_0
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f128,f87])).

fof(f87,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f86])).

fof(f128,plain,
    ( ! [X0] :
        ( r2_hidden(k2_mcart_1(X0),k11_relat_1(sK0,k1_mcart_1(X0)))
        | ~ m1_subset_1(X0,sK0)
        | v1_xboole_0(sK0) )
    | ~ spl5_0
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f125,f64])).

fof(f64,plain,
    ( v1_relat_1(sK0)
    | ~ spl5_0 ),
    inference(avatar_component_clause,[],[f63])).

fof(f125,plain,
    ( ! [X0] :
        ( r2_hidden(k2_mcart_1(X0),k11_relat_1(sK0,k1_mcart_1(X0)))
        | ~ v1_relat_1(sK0)
        | ~ m1_subset_1(X0,sK0)
        | v1_xboole_0(sK0) )
    | ~ spl5_0
    | ~ spl5_7 ),
    inference(superposition,[],[f57,f92])).

fof(f92,plain,
    ( ! [X0] : k11_relat_1(sK0,X0) = a_2_0_mcart_1(sK0,X0)
    | ~ spl5_0
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f91,f64])).

fof(f91,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK0)
        | k11_relat_1(sK0,X0) = a_2_0_mcart_1(sK0,X0) )
    | ~ spl5_7 ),
    inference(resolution,[],[f87,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ v1_relat_1(X0)
      | k11_relat_1(X0,X1) = a_2_0_mcart_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = a_2_0_mcart_1(X0,X1)
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = a_2_0_mcart_1(X0,X1)
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] : k11_relat_1(X0,X1) = a_2_0_mcart_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t93_mcart_1.p',t92_mcart_1)).

fof(f57,plain,(
    ! [X3,X1] :
      ( r2_hidden(k2_mcart_1(X3),a_2_0_mcart_1(X1,k1_mcart_1(X3)))
      | ~ v1_relat_1(X1)
      | ~ m1_subset_1(X3,X1)
      | v1_xboole_0(X1) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X2,X3,X1] :
      ( v1_xboole_0(X1)
      | ~ v1_relat_1(X1)
      | ~ m1_subset_1(X3,X1)
      | k1_mcart_1(X3) != X2
      | r2_hidden(k2_mcart_1(X3),a_2_0_mcart_1(X1,X2)) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_xboole_0(X1)
      | ~ v1_relat_1(X1)
      | ~ m1_subset_1(X3,X1)
      | k2_mcart_1(X3) != X0
      | k1_mcart_1(X3) != X2
      | r2_hidden(X0,a_2_0_mcart_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_mcart_1(X1,X2))
      <=> ? [X3] :
            ( k1_mcart_1(X3) = X2
            & k2_mcart_1(X3) = X0
            & m1_subset_1(X3,X1) ) )
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_mcart_1(X1,X2))
      <=> ? [X3] :
            ( k1_mcart_1(X3) = X2
            & k2_mcart_1(X3) = X0
            & m1_subset_1(X3,X1) ) )
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_relat_1(X1)
        & ~ v1_xboole_0(X1) )
     => ( r2_hidden(X0,a_2_0_mcart_1(X1,X2))
      <=> ? [X3] :
            ( k1_mcart_1(X3) = X2
            & k2_mcart_1(X3) = X0
            & m1_subset_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t93_mcart_1.p',fraenkel_a_2_0_mcart_1)).

fof(f108,plain,
    ( ~ spl5_9
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f81,f70,f106])).

fof(f106,plain,
    ( spl5_9
  <=> ~ r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f81,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ spl5_2 ),
    inference(resolution,[],[f54,f71])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t93_mcart_1.p',antisymmetry_r2_hidden)).

fof(f88,plain,
    ( ~ spl5_7
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f80,f70,f86])).

fof(f80,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl5_2 ),
    inference(resolution,[],[f50,f71])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t93_mcart_1.p',t7_boole)).

fof(f79,plain,(
    ~ spl5_5 ),
    inference(avatar_split_clause,[],[f38,f77])).

fof(f38,plain,(
    ~ r2_hidden(k2_mcart_1(sK1),k11_relat_1(sK0,k1_mcart_1(sK1))) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k2_mcart_1(X1),k11_relat_1(X0,k1_mcart_1(X1)))
          & r2_hidden(X1,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( r2_hidden(X1,X0)
           => r2_hidden(k2_mcart_1(X1),k11_relat_1(X0,k1_mcart_1(X1))) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r2_hidden(X1,X0)
         => r2_hidden(k2_mcart_1(X1),k11_relat_1(X0,k1_mcart_1(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t93_mcart_1.p',t93_mcart_1)).

fof(f72,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f37,f70])).

fof(f37,plain,(
    r2_hidden(sK1,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f65,plain,(
    spl5_0 ),
    inference(avatar_split_clause,[],[f39,f63])).

fof(f39,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
