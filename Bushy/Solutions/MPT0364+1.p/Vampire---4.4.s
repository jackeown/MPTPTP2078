%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : subset_1__t44_subset_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:23 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  156 ( 361 expanded)
%              Number of leaves         :   44 ( 156 expanded)
%              Depth                    :   11
%              Number of atoms          :  416 ( 989 expanded)
%              Number of equality atoms :   45 ( 111 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f337,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f63,f70,f77,f84,f98,f99,f111,f118,f131,f138,f148,f158,f169,f177,f185,f215,f222,f244,f250,f259,f280,f283,f284,f297,f310,f332,f336])).

fof(f336,plain,
    ( ~ spl4_35
    | ~ spl4_4
    | ~ spl4_8
    | spl4_11
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f335,f116,f93,f90,f75,f242])).

fof(f242,plain,
    ( spl4_35
  <=> ~ m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f75,plain,
    ( spl4_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f90,plain,
    ( spl4_8
  <=> r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f93,plain,
    ( spl4_11
  <=> ~ r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f116,plain,
    ( spl4_14
  <=> k3_subset_1(sK0,k3_subset_1(sK0,sK2)) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f335,plain,
    ( ~ m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ spl4_4
    | ~ spl4_8
    | ~ spl4_11
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f334,f94])).

fof(f94,plain,
    ( ~ r1_tarski(sK1,sK2)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f93])).

fof(f334,plain,
    ( r1_tarski(sK1,sK2)
    | ~ m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ spl4_4
    | ~ spl4_8
    | ~ spl4_14 ),
    inference(forward_demodulation,[],[f333,f117])).

fof(f117,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,sK2)) = sK2
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f116])).

fof(f333,plain,
    ( ~ m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))
    | r1_tarski(sK1,k3_subset_1(sK0,k3_subset_1(sK0,sK2)))
    | ~ spl4_4
    | ~ spl4_8 ),
    inference(resolution,[],[f251,f76])).

fof(f76,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f75])).

fof(f251,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
        | ~ m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(X0))
        | r1_tarski(sK1,k3_subset_1(X0,k3_subset_1(sK0,sK2))) )
    | ~ spl4_8 ),
    inference(resolution,[],[f91,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X1,X2)
      | r1_tarski(X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_xboole_0(X1,X2)
              | ~ r1_tarski(X1,k3_subset_1(X0,X2)) )
            & ( r1_tarski(X1,k3_subset_1(X0,X2))
              | ~ r1_xboole_0(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t44_subset_1.p',t43_subset_1)).

fof(f91,plain,
    ( r1_xboole_0(sK1,k3_subset_1(sK0,sK2))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f90])).

fof(f332,plain,
    ( ~ spl4_53
    | spl4_54
    | ~ spl4_20
    | ~ spl4_22
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f317,f183,f156,f146,f330,f324])).

fof(f324,plain,
    ( spl4_53
  <=> ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).

fof(f330,plain,
    ( spl4_54
  <=> r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).

fof(f146,plain,
    ( spl4_20
  <=> k3_subset_1(k1_xboole_0,sK3(k1_zfmisc_1(k1_xboole_0))) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f156,plain,
    ( spl4_22
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f183,plain,
    ( spl4_28
  <=> k1_xboole_0 = sK3(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f317,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl4_20
    | ~ spl4_22
    | ~ spl4_28 ),
    inference(forward_demodulation,[],[f316,f147])).

fof(f147,plain,
    ( k3_subset_1(k1_xboole_0,sK3(k1_zfmisc_1(k1_xboole_0))) = k1_xboole_0
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f146])).

fof(f316,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | r1_xboole_0(k1_xboole_0,k3_subset_1(k1_xboole_0,sK3(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl4_20
    | ~ spl4_22
    | ~ spl4_28 ),
    inference(subsumption_resolution,[],[f315,f157])).

fof(f157,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f156])).

fof(f315,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | r1_xboole_0(k1_xboole_0,k3_subset_1(k1_xboole_0,sK3(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl4_20
    | ~ spl4_22
    | ~ spl4_28 ),
    inference(forward_demodulation,[],[f314,f147])).

fof(f314,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k3_subset_1(k1_xboole_0,sK3(k1_zfmisc_1(k1_xboole_0))),k1_zfmisc_1(k1_xboole_0))
    | r1_xboole_0(k1_xboole_0,k3_subset_1(k1_xboole_0,sK3(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl4_22
    | ~ spl4_28 ),
    inference(forward_demodulation,[],[f311,f184])).

fof(f184,plain,
    ( k1_xboole_0 = sK3(k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f183])).

fof(f311,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3(k1_zfmisc_1(k1_xboole_0)))
    | ~ m1_subset_1(k3_subset_1(k1_xboole_0,sK3(k1_zfmisc_1(k1_xboole_0))),k1_zfmisc_1(k1_xboole_0))
    | r1_xboole_0(k1_xboole_0,k3_subset_1(k1_xboole_0,sK3(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl4_22 ),
    inference(superposition,[],[f231,f104])).

fof(f104,plain,(
    ! [X2] : k3_subset_1(X2,k3_subset_1(X2,sK3(k1_zfmisc_1(X2)))) = sK3(k1_zfmisc_1(X2)) ),
    inference(resolution,[],[f51,f48])).

fof(f48,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f12,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f12,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t44_subset_1.p',existence_m1_subset_1)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t44_subset_1.p',involutiveness_k3_subset_1)).

fof(f231,plain,
    ( ! [X5] :
        ( ~ r1_tarski(k1_xboole_0,k3_subset_1(k1_xboole_0,X5))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k1_xboole_0))
        | r1_xboole_0(k1_xboole_0,X5) )
    | ~ spl4_22 ),
    inference(resolution,[],[f54,f157])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r1_tarski(X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | r1_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f310,plain,
    ( spl4_48
    | ~ spl4_35
    | ~ spl4_51
    | ~ spl4_6
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f246,f116,f82,f308,f242,f302])).

fof(f302,plain,
    ( spl4_48
  <=> r1_xboole_0(sK2,k3_subset_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).

fof(f308,plain,
    ( spl4_51
  <=> ~ r1_tarski(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_51])])).

fof(f82,plain,
    ( spl4_6
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f246,plain,
    ( ~ r1_tarski(sK2,sK2)
    | ~ m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))
    | r1_xboole_0(sK2,k3_subset_1(sK0,sK2))
    | ~ spl4_6
    | ~ spl4_14 ),
    inference(superposition,[],[f229,f117])).

fof(f229,plain,
    ( ! [X1] :
        ( ~ r1_tarski(sK2,k3_subset_1(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(sK0))
        | r1_xboole_0(sK2,X1) )
    | ~ spl4_6 ),
    inference(resolution,[],[f54,f83])).

fof(f83,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f82])).

fof(f297,plain,
    ( spl4_44
    | ~ spl4_41
    | ~ spl4_47
    | ~ spl4_6
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f245,f109,f82,f295,f272,f289])).

fof(f289,plain,
    ( spl4_44
  <=> r1_xboole_0(sK2,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).

fof(f272,plain,
    ( spl4_41
  <=> ~ m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).

fof(f295,plain,
    ( spl4_47
  <=> ~ r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).

fof(f109,plain,
    ( spl4_12
  <=> k3_subset_1(sK0,k3_subset_1(sK0,sK1)) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f245,plain,
    ( ~ r1_tarski(sK2,sK1)
    | ~ m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | r1_xboole_0(sK2,k3_subset_1(sK0,sK1))
    | ~ spl4_6
    | ~ spl4_12 ),
    inference(superposition,[],[f229,f110])).

fof(f110,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,sK1)) = sK1
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f109])).

fof(f284,plain,
    ( spl4_8
    | ~ spl4_35
    | ~ spl4_11
    | ~ spl4_4
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f234,f116,f75,f93,f242,f90])).

fof(f234,plain,
    ( ~ r1_tarski(sK1,sK2)
    | ~ m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))
    | r1_xboole_0(sK1,k3_subset_1(sK0,sK2))
    | ~ spl4_4
    | ~ spl4_14 ),
    inference(superposition,[],[f228,f117])).

fof(f228,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK1,k3_subset_1(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | r1_xboole_0(sK1,X0) )
    | ~ spl4_4 ),
    inference(resolution,[],[f54,f76])).

fof(f283,plain,
    ( ~ spl4_4
    | spl4_41 ),
    inference(avatar_contradiction_clause,[],[f282])).

fof(f282,plain,
    ( $false
    | ~ spl4_4
    | ~ spl4_41 ),
    inference(subsumption_resolution,[],[f281,f76])).

fof(f281,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl4_41 ),
    inference(resolution,[],[f273,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t44_subset_1.p',dt_k3_subset_1)).

fof(f273,plain,
    ( ~ m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl4_41 ),
    inference(avatar_component_clause,[],[f272])).

fof(f280,plain,
    ( spl4_38
    | ~ spl4_41
    | ~ spl4_43
    | ~ spl4_4
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f233,f109,f75,f278,f272,f266])).

fof(f266,plain,
    ( spl4_38
  <=> r1_xboole_0(sK1,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f278,plain,
    ( spl4_43
  <=> ~ r1_tarski(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).

fof(f233,plain,
    ( ~ r1_tarski(sK1,sK1)
    | ~ m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | r1_xboole_0(sK1,k3_subset_1(sK0,sK1))
    | ~ spl4_4
    | ~ spl4_12 ),
    inference(superposition,[],[f228,f110])).

fof(f259,plain,
    ( spl4_36
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f252,f90,f257])).

fof(f257,plain,
    ( spl4_36
  <=> r1_xboole_0(k3_subset_1(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f252,plain,
    ( r1_xboole_0(k3_subset_1(sK0,sK2),sK1)
    | ~ spl4_8 ),
    inference(resolution,[],[f91,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t44_subset_1.p',symmetry_r1_xboole_0)).

fof(f250,plain,
    ( ~ spl4_6
    | spl4_35 ),
    inference(avatar_contradiction_clause,[],[f249])).

fof(f249,plain,
    ( $false
    | ~ spl4_6
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f248,f83])).

fof(f248,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl4_35 ),
    inference(resolution,[],[f243,f50])).

fof(f243,plain,
    ( ~ m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ spl4_35 ),
    inference(avatar_component_clause,[],[f242])).

fof(f244,plain,
    ( ~ spl4_35
    | ~ spl4_4
    | spl4_9
    | ~ spl4_10
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f237,f116,f96,f87,f75,f242])).

fof(f87,plain,
    ( spl4_9
  <=> ~ r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f96,plain,
    ( spl4_10
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f237,plain,
    ( ~ m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ spl4_4
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f236,f88])).

fof(f88,plain,
    ( ~ r1_xboole_0(sK1,k3_subset_1(sK0,sK2))
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f87])).

fof(f236,plain,
    ( ~ m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))
    | r1_xboole_0(sK1,k3_subset_1(sK0,sK2))
    | ~ spl4_4
    | ~ spl4_10
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f234,f97])).

fof(f97,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f96])).

fof(f222,plain,
    ( spl4_32
    | ~ spl4_6
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f205,f116,f82,f220])).

fof(f220,plain,
    ( spl4_32
  <=> k4_xboole_0(sK0,k3_subset_1(sK0,sK2)) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f205,plain,
    ( k4_xboole_0(sK0,k3_subset_1(sK0,sK2)) = sK2
    | ~ spl4_6
    | ~ spl4_14 ),
    inference(forward_demodulation,[],[f200,f117])).

fof(f200,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,sK2)) = k4_xboole_0(sK0,k3_subset_1(sK0,sK2))
    | ~ spl4_6 ),
    inference(resolution,[],[f123,f83])).

fof(f123,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = k4_xboole_0(X0,k3_subset_1(X0,X1)) ) ),
    inference(resolution,[],[f52,f50])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t44_subset_1.p',d5_subset_1)).

fof(f215,plain,
    ( spl4_30
    | ~ spl4_4
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f204,f109,f75,f213])).

fof(f213,plain,
    ( spl4_30
  <=> k4_xboole_0(sK0,k3_subset_1(sK0,sK1)) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f204,plain,
    ( k4_xboole_0(sK0,k3_subset_1(sK0,sK1)) = sK1
    | ~ spl4_4
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f199,f110])).

fof(f199,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,sK1)) = k4_xboole_0(sK0,k3_subset_1(sK0,sK1))
    | ~ spl4_4 ),
    inference(resolution,[],[f123,f76])).

fof(f185,plain,
    ( spl4_28
    | ~ spl4_24
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f178,f175,f167,f183])).

fof(f167,plain,
    ( spl4_24
  <=> k3_subset_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f175,plain,
    ( spl4_26
  <=> k3_subset_1(k1_xboole_0,k1_xboole_0) = sK3(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f178,plain,
    ( k1_xboole_0 = sK3(k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_24
    | ~ spl4_26 ),
    inference(forward_demodulation,[],[f176,f168])).

fof(f168,plain,
    ( k3_subset_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f167])).

fof(f176,plain,
    ( k3_subset_1(k1_xboole_0,k1_xboole_0) = sK3(k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f175])).

fof(f177,plain,
    ( spl4_26
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f149,f146,f175])).

fof(f149,plain,
    ( k3_subset_1(k1_xboole_0,k1_xboole_0) = sK3(k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_20 ),
    inference(superposition,[],[f104,f147])).

fof(f169,plain,
    ( spl4_24
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f161,f156,f167])).

fof(f161,plain,
    ( k3_subset_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | ~ spl4_22 ),
    inference(forward_demodulation,[],[f159,f45])).

fof(f45,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/subset_1__t44_subset_1.p',t3_boole)).

fof(f159,plain,
    ( k3_subset_1(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl4_22 ),
    inference(resolution,[],[f157,f52])).

fof(f158,plain,
    ( spl4_22
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f151,f146,f156])).

fof(f151,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f150,f48])).

fof(f150,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ m1_subset_1(sK3(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_20 ),
    inference(superposition,[],[f50,f147])).

fof(f148,plain,(
    spl4_20 ),
    inference(avatar_split_clause,[],[f140,f146])).

fof(f140,plain,(
    k3_subset_1(k1_xboole_0,sK3(k1_zfmisc_1(k1_xboole_0))) = k1_xboole_0 ),
    inference(superposition,[],[f124,f46])).

fof(f46,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t44_subset_1.p',t4_boole)).

fof(f124,plain,(
    ! [X2] : k3_subset_1(X2,sK3(k1_zfmisc_1(X2))) = k4_xboole_0(X2,sK3(k1_zfmisc_1(X2))) ),
    inference(resolution,[],[f52,f48])).

fof(f138,plain,
    ( spl4_18
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f122,f82,f136])).

fof(f136,plain,
    ( spl4_18
  <=> k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f122,plain,
    ( k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)
    | ~ spl4_6 ),
    inference(resolution,[],[f52,f83])).

fof(f131,plain,
    ( spl4_16
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f121,f75,f129])).

fof(f129,plain,
    ( spl4_16
  <=> k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f121,plain,
    ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)
    | ~ spl4_4 ),
    inference(resolution,[],[f52,f76])).

fof(f118,plain,
    ( spl4_14
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f102,f82,f116])).

fof(f102,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,sK2)) = sK2
    | ~ spl4_6 ),
    inference(resolution,[],[f51,f83])).

fof(f111,plain,
    ( spl4_12
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f101,f75,f109])).

fof(f101,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,sK1)) = sK1
    | ~ spl4_4 ),
    inference(resolution,[],[f51,f76])).

fof(f99,plain,
    ( ~ spl4_9
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f42,f93,f87])).

fof(f42,plain,
    ( ~ r1_tarski(sK1,sK2)
    | ~ r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ( ~ r1_tarski(sK1,sK2)
      | ~ r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) )
    & ( r1_tarski(sK1,sK2)
      | r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) )
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f32,f34,f33])).

fof(f33,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ r1_tarski(X1,X2)
              | ~ r1_xboole_0(X1,k3_subset_1(X0,X2)) )
            & ( r1_tarski(X1,X2)
              | r1_xboole_0(X1,k3_subset_1(X0,X2)) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ( ~ r1_tarski(sK1,X2)
            | ~ r1_xboole_0(sK1,k3_subset_1(sK0,X2)) )
          & ( r1_tarski(sK1,X2)
            | r1_xboole_0(sK1,k3_subset_1(sK0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X1,X2)
            | ~ r1_xboole_0(X1,k3_subset_1(X0,X2)) )
          & ( r1_tarski(X1,X2)
            | r1_xboole_0(X1,k3_subset_1(X0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
     => ( ( ~ r1_tarski(X1,sK2)
          | ~ r1_xboole_0(X1,k3_subset_1(X0,sK2)) )
        & ( r1_tarski(X1,sK2)
          | r1_xboole_0(X1,k3_subset_1(X0,sK2)) )
        & m1_subset_1(sK2,k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X1,X2)
            | ~ r1_xboole_0(X1,k3_subset_1(X0,X2)) )
          & ( r1_tarski(X1,X2)
            | r1_xboole_0(X1,k3_subset_1(X0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X1,X2)
            | ~ r1_xboole_0(X1,k3_subset_1(X0,X2)) )
          & ( r1_tarski(X1,X2)
            | r1_xboole_0(X1,k3_subset_1(X0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <~> r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_xboole_0(X1,k3_subset_1(X0,X2))
            <=> r1_tarski(X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <=> r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t44_subset_1.p',t44_subset_1)).

fof(f98,plain,
    ( spl4_8
    | spl4_10 ),
    inference(avatar_split_clause,[],[f41,f96,f90])).

fof(f41,plain,
    ( r1_tarski(sK1,sK2)
    | r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f35])).

fof(f84,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f40,f82])).

fof(f40,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f35])).

fof(f77,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f39,f75])).

fof(f39,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f35])).

fof(f70,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f44,f68])).

fof(f68,plain,
    ( spl4_2
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f44,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/subset_1__t44_subset_1.p',d2_xboole_0)).

fof(f63,plain,(
    spl4_0 ),
    inference(avatar_split_clause,[],[f56,f61])).

fof(f61,plain,
    ( spl4_0
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_0])])).

fof(f56,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(forward_demodulation,[],[f43,f44])).

fof(f43,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t44_subset_1.p',dt_o_0_0_xboole_0)).
%------------------------------------------------------------------------------
