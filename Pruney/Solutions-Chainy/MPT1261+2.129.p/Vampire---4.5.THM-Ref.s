%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:07 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  170 ( 310 expanded)
%              Number of leaves         :   45 ( 145 expanded)
%              Depth                    :   12
%              Number of atoms          :  524 (1049 expanded)
%              Number of equality atoms :   78 ( 185 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f592,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f60,f65,f70,f79,f85,f89,f93,f97,f101,f110,f118,f135,f146,f150,f157,f164,f169,f178,f185,f201,f208,f213,f284,f323,f352,f402,f469,f472,f494,f548,f573,f581])).

fof(f581,plain,
    ( ~ spl2_20
    | ~ spl2_22
    | ~ spl2_52
    | ~ spl2_54 ),
    inference(avatar_contradiction_clause,[],[f580])).

fof(f580,plain,
    ( $false
    | ~ spl2_20
    | ~ spl2_22
    | ~ spl2_52
    | ~ spl2_54 ),
    inference(subsumption_resolution,[],[f565,f579])).

fof(f579,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | ~ spl2_22
    | ~ spl2_52
    | ~ spl2_54 ),
    inference(subsumption_resolution,[],[f429,f578])).

fof(f578,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_52
    | ~ spl2_54 ),
    inference(forward_demodulation,[],[f493,f547])).

% (10165)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
fof(f547,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_54 ),
    inference(avatar_component_clause,[],[f545])).

fof(f545,plain,
    ( spl2_54
  <=> sK1 = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_54])])).

fof(f493,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl2_52 ),
    inference(avatar_component_clause,[],[f491])).

fof(f491,plain,
    ( spl2_52
  <=> k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_52])])).

fof(f429,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0)
    | ~ spl2_22 ),
    inference(forward_demodulation,[],[f41,f184])).

fof(f184,plain,
    ( ! [X0] : k4_xboole_0(sK1,X0) = k7_subset_1(u1_struct_0(sK0),sK1,X0)
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f183])).

fof(f183,plain,
    ( spl2_22
  <=> ! [X0] : k4_xboole_0(sK1,X0) = k7_subset_1(u1_struct_0(sK0),sK1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f41,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f34,f33])).

fof(f33,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
              | ~ v4_pre_topc(X1,X0) )
            & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
              | v4_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
            | ~ v4_pre_topc(X1,sK0) )
          & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
            | v4_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X1] :
        ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
          | ~ v4_pre_topc(X1,sK0) )
        & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
          | v4_pre_topc(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
        | ~ v4_pre_topc(sK1,sK0) )
      & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
        | v4_pre_topc(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

fof(f565,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl2_20
    | ~ spl2_54 ),
    inference(superposition,[],[f168,f547])).

fof(f168,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f166])).

fof(f166,plain,
    ( spl2_20
  <=> v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f573,plain,
    ( ~ spl2_3
    | spl2_51
    | ~ spl2_54 ),
    inference(avatar_contradiction_clause,[],[f572])).

fof(f572,plain,
    ( $false
    | ~ spl2_3
    | spl2_51
    | ~ spl2_54 ),
    inference(subsumption_resolution,[],[f69,f563])).

fof(f563,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_51
    | ~ spl2_54 ),
    inference(superposition,[],[f489,f547])).

fof(f489,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_51 ),
    inference(avatar_component_clause,[],[f487])).

fof(f487,plain,
    ( spl2_51
  <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_51])])).

fof(f69,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f548,plain,
    ( ~ spl2_3
    | spl2_54
    | ~ spl2_9
    | ~ spl2_18
    | ~ spl2_25
    | ~ spl2_32
    | ~ spl2_43
    | ~ spl2_50 ),
    inference(avatar_split_clause,[],[f543,f466,f399,f282,f198,f155,f95,f545,f67])).

fof(f95,plain,
    ( spl2_9
  <=> ! [X1,X0] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f155,plain,
    ( spl2_18
  <=> ! [X1,X0,X2] :
        ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f198,plain,
    ( spl2_25
  <=> k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).

fof(f282,plain,
    ( spl2_32
  <=> ! [X3,X2] :
        ( k2_xboole_0(X3,X2) = X3
        | ~ r1_tarski(X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).

fof(f399,plain,
    ( spl2_43
  <=> r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_43])])).

fof(f466,plain,
    ( spl2_50
  <=> r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_50])])).

fof(f543,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_9
    | ~ spl2_18
    | ~ spl2_25
    | ~ spl2_32
    | ~ spl2_43
    | ~ spl2_50 ),
    inference(forward_demodulation,[],[f542,f404])).

fof(f404,plain,
    ( sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_32
    | ~ spl2_43 ),
    inference(unit_resulting_resolution,[],[f401,f283])).

fof(f283,plain,
    ( ! [X2,X3] :
        ( k2_xboole_0(X3,X2) = X3
        | ~ r1_tarski(X2,X3) )
    | ~ spl2_32 ),
    inference(avatar_component_clause,[],[f282])).

fof(f401,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_43 ),
    inference(avatar_component_clause,[],[f399])).

fof(f542,plain,
    ( k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_9
    | ~ spl2_18
    | ~ spl2_25
    | ~ spl2_50 ),
    inference(subsumption_resolution,[],[f202,f540])).

fof(f540,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_9
    | ~ spl2_50 ),
    inference(unit_resulting_resolution,[],[f468,f96])).

fof(f96,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f95])).

fof(f468,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0))
    | ~ spl2_50 ),
    inference(avatar_component_clause,[],[f466])).

fof(f202,plain,
    ( k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_18
    | ~ spl2_25 ),
    inference(superposition,[],[f200,f156])).

fof(f156,plain,
    ( ! [X2,X0,X1] :
        ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f155])).

fof(f200,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_25 ),
    inference(avatar_component_clause,[],[f198])).

fof(f494,plain,
    ( ~ spl2_51
    | spl2_52
    | ~ spl2_15
    | ~ spl2_27 ),
    inference(avatar_split_clause,[],[f214,f210,f133,f491,f487])).

fof(f133,plain,
    ( spl2_15
  <=> ! [X1,X0,X2] :
        ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f210,plain,
    ( spl2_27
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).

fof(f214,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_15
    | ~ spl2_27 ),
    inference(superposition,[],[f212,f134])).

fof(f134,plain,
    ( ! [X2,X0,X1] :
        ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f133])).

fof(f212,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl2_27 ),
    inference(avatar_component_clause,[],[f210])).

fof(f472,plain,
    ( spl2_43
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_11
    | ~ spl2_36 ),
    inference(avatar_split_clause,[],[f431,f321,f107,f72,f62,f399])).

fof(f62,plain,
    ( spl2_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f72,plain,
    ( spl2_4
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f107,plain,
    ( spl2_11
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f321,plain,
    ( spl2_36
  <=> ! [X1,X0] :
        ( ~ v4_pre_topc(X0,X1)
        | r1_tarski(k2_tops_1(X1,X0),X0)
        | ~ l1_pre_topc(X1)
        | ~ r1_tarski(X0,u1_struct_0(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_36])])).

fof(f431,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_11
    | ~ spl2_36 ),
    inference(unit_resulting_resolution,[],[f64,f109,f74,f322])).

fof(f322,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k2_tops_1(X1,X0),X0)
        | ~ v4_pre_topc(X0,X1)
        | ~ l1_pre_topc(X1)
        | ~ r1_tarski(X0,u1_struct_0(X1)) )
    | ~ spl2_36 ),
    inference(avatar_component_clause,[],[f321])).

fof(f74,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f72])).

fof(f109,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f107])).

fof(f64,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f469,plain,
    ( spl2_50
    | ~ spl2_39
    | ~ spl2_43 ),
    inference(avatar_split_clause,[],[f403,f399,f350,f466])).

fof(f350,plain,
    ( spl2_39
  <=> ! [X0] :
        ( r1_tarski(X0,u1_struct_0(sK0))
        | ~ r1_tarski(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_39])])).

fof(f403,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0))
    | ~ spl2_39
    | ~ spl2_43 ),
    inference(unit_resulting_resolution,[],[f401,f351])).

fof(f351,plain,
    ( ! [X0] :
        ( r1_tarski(X0,u1_struct_0(sK0))
        | ~ r1_tarski(X0,sK1) )
    | ~ spl2_39 ),
    inference(avatar_component_clause,[],[f350])).

fof(f402,plain,
    ( spl2_43
    | ~ spl2_6
    | ~ spl2_26 ),
    inference(avatar_split_clause,[],[f397,f205,f83,f399])).

fof(f83,plain,
    ( spl2_6
  <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f205,plain,
    ( spl2_26
  <=> k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).

fof(f397,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_6
    | ~ spl2_26 ),
    inference(superposition,[],[f84,f207])).

fof(f207,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_26 ),
    inference(avatar_component_clause,[],[f205])).

fof(f84,plain,
    ( ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f83])).

fof(f352,plain,
    ( spl2_39
    | ~ spl2_11
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f139,f116,f107,f350])).

fof(f116,plain,
    ( spl2_13
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,X2)
        | ~ r1_tarski(X1,X2)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f139,plain,
    ( ! [X0] :
        ( r1_tarski(X0,u1_struct_0(sK0))
        | ~ r1_tarski(X0,sK1) )
    | ~ spl2_11
    | ~ spl2_13 ),
    inference(resolution,[],[f109,f117])).

fof(f117,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X1,X2)
        | r1_tarski(X0,X2)
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f116])).

fof(f323,plain,
    ( spl2_36
    | ~ spl2_9
    | ~ spl2_17 ),
    inference(avatar_split_clause,[],[f159,f148,f95,f321])).

fof(f148,plain,
    ( spl2_17
  <=> ! [X1,X0] :
        ( r1_tarski(k2_tops_1(X0,X1),X1)
        | ~ v4_pre_topc(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f159,plain,
    ( ! [X0,X1] :
        ( ~ v4_pre_topc(X0,X1)
        | r1_tarski(k2_tops_1(X1,X0),X0)
        | ~ l1_pre_topc(X1)
        | ~ r1_tarski(X0,u1_struct_0(X1)) )
    | ~ spl2_9
    | ~ spl2_17 ),
    inference(resolution,[],[f149,f96])).

fof(f149,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v4_pre_topc(X1,X0)
        | r1_tarski(k2_tops_1(X0,X1),X1)
        | ~ l1_pre_topc(X0) )
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f148])).

fof(f284,plain,
    ( spl2_32
    | ~ spl2_7
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f120,f99,f87,f282])).

fof(f87,plain,
    ( spl2_7
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f99,plain,
    ( spl2_10
  <=> ! [X1,X0] :
        ( k2_xboole_0(X0,X1) = X1
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f120,plain,
    ( ! [X2,X3] :
        ( k2_xboole_0(X3,X2) = X3
        | ~ r1_tarski(X2,X3) )
    | ~ spl2_7
    | ~ spl2_10 ),
    inference(superposition,[],[f100,f88])).

fof(f88,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f87])).

fof(f100,plain,
    ( ! [X0,X1] :
        ( k2_xboole_0(X0,X1) = X1
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f99])).

fof(f213,plain,
    ( spl2_27
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_21 ),
    inference(avatar_split_clause,[],[f179,f176,f67,f62,f210])).

fof(f176,plain,
    ( spl2_21
  <=> ! [X1,X0] :
        ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f179,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_21 ),
    inference(unit_resulting_resolution,[],[f64,f69,f177])).

fof(f177,plain,
    ( ! [X0,X1] :
        ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl2_21 ),
    inference(avatar_component_clause,[],[f176])).

fof(f208,plain,
    ( ~ spl2_3
    | spl2_26
    | ~ spl2_5
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f141,f133,f76,f205,f67])).

fof(f76,plain,
    ( spl2_5
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f141,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_5
    | ~ spl2_15 ),
    inference(superposition,[],[f134,f78])).

fof(f78,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f76])).

fof(f201,plain,
    ( spl2_25
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_19 ),
    inference(avatar_split_clause,[],[f170,f162,f67,f62,f198])).

fof(f162,plain,
    ( spl2_19
  <=> ! [X1,X0] :
        ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f170,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_19 ),
    inference(unit_resulting_resolution,[],[f64,f69,f163])).

fof(f163,plain,
    ( ! [X0,X1] :
        ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f162])).

fof(f185,plain,
    ( spl2_22
    | ~ spl2_3
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f140,f133,f67,f183])).

fof(f140,plain,
    ( ! [X0] : k4_xboole_0(sK1,X0) = k7_subset_1(u1_struct_0(sK0),sK1,X0)
    | ~ spl2_3
    | ~ spl2_15 ),
    inference(unit_resulting_resolution,[],[f69,f134])).

fof(f178,plain,(
    spl2_21 ),
    inference(avatar_split_clause,[],[f43,f176])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

fof(f169,plain,
    ( spl2_20
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f151,f144,f67,f62,f57,f166])).

fof(f57,plain,
    ( spl2_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f144,plain,
    ( spl2_16
  <=> ! [X1,X0] :
        ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f151,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_16 ),
    inference(unit_resulting_resolution,[],[f59,f64,f69,f145])).

fof(f145,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | v4_pre_topc(k2_pre_topc(X0,X1),X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f144])).

fof(f59,plain,
    ( v2_pre_topc(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f57])).

fof(f164,plain,(
    spl2_19 ),
    inference(avatar_split_clause,[],[f42,f162])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

fof(f157,plain,(
    spl2_18 ),
    inference(avatar_split_clause,[],[f55,f155])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f150,plain,(
    spl2_17 ),
    inference(avatar_split_clause,[],[f44,f148])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tops_1(X0,X1),X1)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

fof(f146,plain,(
    spl2_16 ),
    inference(avatar_split_clause,[],[f49,f144])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).

fof(f135,plain,(
    spl2_15 ),
    inference(avatar_split_clause,[],[f52,f133])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f118,plain,(
    spl2_13 ),
    inference(avatar_split_clause,[],[f54,f116])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f110,plain,
    ( spl2_11
    | ~ spl2_3
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f102,f91,f67,f107])).

fof(f91,plain,
    ( spl2_8
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f102,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl2_3
    | ~ spl2_8 ),
    inference(unit_resulting_resolution,[],[f69,f92])).

fof(f92,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | r1_tarski(X0,X1) )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f91])).

fof(f101,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f48,f99])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f97,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f51,f95])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f93,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f50,f91])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f89,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f46,f87])).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f85,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f45,f83])).

fof(f45,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f79,plain,
    ( spl2_4
    | spl2_5 ),
    inference(avatar_split_clause,[],[f40,f76,f72])).

fof(f40,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f70,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f39,f67])).

fof(f39,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f35])).

fof(f65,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f38,f62])).

fof(f38,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f60,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f37,f57])).

fof(f37,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:40:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.45  % (10167)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.45  % (10172)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.46  % (10167)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f592,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(avatar_sat_refutation,[],[f60,f65,f70,f79,f85,f89,f93,f97,f101,f110,f118,f135,f146,f150,f157,f164,f169,f178,f185,f201,f208,f213,f284,f323,f352,f402,f469,f472,f494,f548,f573,f581])).
% 0.20/0.46  fof(f581,plain,(
% 0.20/0.46    ~spl2_20 | ~spl2_22 | ~spl2_52 | ~spl2_54),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f580])).
% 0.20/0.46  fof(f580,plain,(
% 0.20/0.46    $false | (~spl2_20 | ~spl2_22 | ~spl2_52 | ~spl2_54)),
% 0.20/0.46    inference(subsumption_resolution,[],[f565,f579])).
% 0.20/0.46  fof(f579,plain,(
% 0.20/0.46    ~v4_pre_topc(sK1,sK0) | (~spl2_22 | ~spl2_52 | ~spl2_54)),
% 0.20/0.46    inference(subsumption_resolution,[],[f429,f578])).
% 0.20/0.46  fof(f578,plain,(
% 0.20/0.46    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | (~spl2_52 | ~spl2_54)),
% 0.20/0.46    inference(forward_demodulation,[],[f493,f547])).
% 0.20/0.46  % (10165)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.46  fof(f547,plain,(
% 0.20/0.46    sK1 = k2_pre_topc(sK0,sK1) | ~spl2_54),
% 0.20/0.46    inference(avatar_component_clause,[],[f545])).
% 0.20/0.46  fof(f545,plain,(
% 0.20/0.46    spl2_54 <=> sK1 = k2_pre_topc(sK0,sK1)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_54])])).
% 0.20/0.46  fof(f493,plain,(
% 0.20/0.46    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | ~spl2_52),
% 0.20/0.46    inference(avatar_component_clause,[],[f491])).
% 0.20/0.46  fof(f491,plain,(
% 0.20/0.46    spl2_52 <=> k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_52])])).
% 0.20/0.46  fof(f429,plain,(
% 0.20/0.46    k2_tops_1(sK0,sK1) != k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0) | ~spl2_22),
% 0.20/0.46    inference(forward_demodulation,[],[f41,f184])).
% 0.20/0.46  fof(f184,plain,(
% 0.20/0.46    ( ! [X0] : (k4_xboole_0(sK1,X0) = k7_subset_1(u1_struct_0(sK0),sK1,X0)) ) | ~spl2_22),
% 0.20/0.46    inference(avatar_component_clause,[],[f183])).
% 0.20/0.46  fof(f183,plain,(
% 0.20/0.46    spl2_22 <=> ! [X0] : k4_xboole_0(sK1,X0) = k7_subset_1(u1_struct_0(sK0),sK1,X0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 0.20/0.46  fof(f41,plain,(
% 0.20/0.46    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 0.20/0.46    inference(cnf_transformation,[],[f35])).
% 0.20/0.46  fof(f35,plain,(
% 0.20/0.46    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f34,f33])).
% 0.20/0.46  fof(f33,plain,(
% 0.20/0.46    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f34,plain,(
% 0.20/0.46    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f32,plain,(
% 0.20/0.46    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.20/0.46    inference(flattening,[],[f31])).
% 0.20/0.46  fof(f31,plain,(
% 0.20/0.46    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.20/0.46    inference(nnf_transformation,[],[f17])).
% 0.20/0.46  fof(f17,plain,(
% 0.20/0.46    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.20/0.46    inference(flattening,[],[f16])).
% 0.20/0.46  fof(f16,plain,(
% 0.20/0.46    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f15])).
% 0.20/0.46  fof(f15,negated_conjecture,(
% 0.20/0.46    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 0.20/0.46    inference(negated_conjecture,[],[f14])).
% 0.20/0.46  fof(f14,conjecture,(
% 0.20/0.46    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).
% 0.20/0.46  fof(f565,plain,(
% 0.20/0.46    v4_pre_topc(sK1,sK0) | (~spl2_20 | ~spl2_54)),
% 0.20/0.46    inference(superposition,[],[f168,f547])).
% 0.20/0.46  fof(f168,plain,(
% 0.20/0.46    v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) | ~spl2_20),
% 0.20/0.46    inference(avatar_component_clause,[],[f166])).
% 0.20/0.46  fof(f166,plain,(
% 0.20/0.46    spl2_20 <=> v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 0.20/0.46  fof(f573,plain,(
% 0.20/0.46    ~spl2_3 | spl2_51 | ~spl2_54),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f572])).
% 0.20/0.46  fof(f572,plain,(
% 0.20/0.46    $false | (~spl2_3 | spl2_51 | ~spl2_54)),
% 0.20/0.46    inference(subsumption_resolution,[],[f69,f563])).
% 0.20/0.46  fof(f563,plain,(
% 0.20/0.46    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (spl2_51 | ~spl2_54)),
% 0.20/0.46    inference(superposition,[],[f489,f547])).
% 0.20/0.47  fof(f489,plain,(
% 0.20/0.47    ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl2_51),
% 0.20/0.47    inference(avatar_component_clause,[],[f487])).
% 0.20/0.47  fof(f487,plain,(
% 0.20/0.47    spl2_51 <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_51])])).
% 0.20/0.47  fof(f69,plain,(
% 0.20/0.47    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_3),
% 0.20/0.47    inference(avatar_component_clause,[],[f67])).
% 0.20/0.47  fof(f67,plain,(
% 0.20/0.47    spl2_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.47  fof(f548,plain,(
% 0.20/0.47    ~spl2_3 | spl2_54 | ~spl2_9 | ~spl2_18 | ~spl2_25 | ~spl2_32 | ~spl2_43 | ~spl2_50),
% 0.20/0.47    inference(avatar_split_clause,[],[f543,f466,f399,f282,f198,f155,f95,f545,f67])).
% 0.20/0.47  fof(f95,plain,(
% 0.20/0.47    spl2_9 <=> ! [X1,X0] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.20/0.47  fof(f155,plain,(
% 0.20/0.47    spl2_18 <=> ! [X1,X0,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.20/0.47  fof(f198,plain,(
% 0.20/0.47    spl2_25 <=> k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).
% 0.20/0.47  fof(f282,plain,(
% 0.20/0.47    spl2_32 <=> ! [X3,X2] : (k2_xboole_0(X3,X2) = X3 | ~r1_tarski(X2,X3))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).
% 0.20/0.47  fof(f399,plain,(
% 0.20/0.47    spl2_43 <=> r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_43])])).
% 0.20/0.47  fof(f466,plain,(
% 0.20/0.47    spl2_50 <=> r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_50])])).
% 0.20/0.47  fof(f543,plain,(
% 0.20/0.47    sK1 = k2_pre_topc(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_9 | ~spl2_18 | ~spl2_25 | ~spl2_32 | ~spl2_43 | ~spl2_50)),
% 0.20/0.47    inference(forward_demodulation,[],[f542,f404])).
% 0.20/0.47  fof(f404,plain,(
% 0.20/0.47    sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl2_32 | ~spl2_43)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f401,f283])).
% 0.20/0.47  fof(f283,plain,(
% 0.20/0.47    ( ! [X2,X3] : (k2_xboole_0(X3,X2) = X3 | ~r1_tarski(X2,X3)) ) | ~spl2_32),
% 0.20/0.47    inference(avatar_component_clause,[],[f282])).
% 0.20/0.47  fof(f401,plain,(
% 0.20/0.47    r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~spl2_43),
% 0.20/0.47    inference(avatar_component_clause,[],[f399])).
% 0.20/0.47  fof(f542,plain,(
% 0.20/0.47    k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_9 | ~spl2_18 | ~spl2_25 | ~spl2_50)),
% 0.20/0.47    inference(subsumption_resolution,[],[f202,f540])).
% 0.20/0.47  fof(f540,plain,(
% 0.20/0.47    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_9 | ~spl2_50)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f468,f96])).
% 0.20/0.47  fof(f96,plain,(
% 0.20/0.47    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) ) | ~spl2_9),
% 0.20/0.47    inference(avatar_component_clause,[],[f95])).
% 0.20/0.47  fof(f468,plain,(
% 0.20/0.47    r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) | ~spl2_50),
% 0.20/0.47    inference(avatar_component_clause,[],[f466])).
% 0.20/0.47  fof(f202,plain,(
% 0.20/0.47    k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_18 | ~spl2_25)),
% 0.20/0.47    inference(superposition,[],[f200,f156])).
% 0.20/0.47  fof(f156,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl2_18),
% 0.20/0.47    inference(avatar_component_clause,[],[f155])).
% 0.20/0.47  fof(f200,plain,(
% 0.20/0.47    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~spl2_25),
% 0.20/0.47    inference(avatar_component_clause,[],[f198])).
% 0.20/0.47  fof(f494,plain,(
% 0.20/0.47    ~spl2_51 | spl2_52 | ~spl2_15 | ~spl2_27),
% 0.20/0.47    inference(avatar_split_clause,[],[f214,f210,f133,f491,f487])).
% 0.20/0.47  fof(f133,plain,(
% 0.20/0.47    spl2_15 <=> ! [X1,X0,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.20/0.47  fof(f210,plain,(
% 0.20/0.47    spl2_27 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).
% 0.20/0.47  fof(f214,plain,(
% 0.20/0.47    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_15 | ~spl2_27)),
% 0.20/0.47    inference(superposition,[],[f212,f134])).
% 0.20/0.47  fof(f134,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl2_15),
% 0.20/0.47    inference(avatar_component_clause,[],[f133])).
% 0.20/0.47  fof(f212,plain,(
% 0.20/0.47    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | ~spl2_27),
% 0.20/0.47    inference(avatar_component_clause,[],[f210])).
% 0.20/0.47  fof(f472,plain,(
% 0.20/0.47    spl2_43 | ~spl2_2 | ~spl2_4 | ~spl2_11 | ~spl2_36),
% 0.20/0.47    inference(avatar_split_clause,[],[f431,f321,f107,f72,f62,f399])).
% 0.20/0.47  fof(f62,plain,(
% 0.20/0.47    spl2_2 <=> l1_pre_topc(sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.47  fof(f72,plain,(
% 0.20/0.47    spl2_4 <=> v4_pre_topc(sK1,sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.47  fof(f107,plain,(
% 0.20/0.47    spl2_11 <=> r1_tarski(sK1,u1_struct_0(sK0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.20/0.47  fof(f321,plain,(
% 0.20/0.47    spl2_36 <=> ! [X1,X0] : (~v4_pre_topc(X0,X1) | r1_tarski(k2_tops_1(X1,X0),X0) | ~l1_pre_topc(X1) | ~r1_tarski(X0,u1_struct_0(X1)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_36])])).
% 0.20/0.47  fof(f431,plain,(
% 0.20/0.47    r1_tarski(k2_tops_1(sK0,sK1),sK1) | (~spl2_2 | ~spl2_4 | ~spl2_11 | ~spl2_36)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f64,f109,f74,f322])).
% 0.20/0.47  fof(f322,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_tarski(k2_tops_1(X1,X0),X0) | ~v4_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~r1_tarski(X0,u1_struct_0(X1))) ) | ~spl2_36),
% 0.20/0.47    inference(avatar_component_clause,[],[f321])).
% 0.20/0.47  fof(f74,plain,(
% 0.20/0.47    v4_pre_topc(sK1,sK0) | ~spl2_4),
% 0.20/0.47    inference(avatar_component_clause,[],[f72])).
% 0.20/0.47  fof(f109,plain,(
% 0.20/0.47    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl2_11),
% 0.20/0.47    inference(avatar_component_clause,[],[f107])).
% 0.20/0.47  fof(f64,plain,(
% 0.20/0.47    l1_pre_topc(sK0) | ~spl2_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f62])).
% 0.20/0.47  fof(f469,plain,(
% 0.20/0.47    spl2_50 | ~spl2_39 | ~spl2_43),
% 0.20/0.47    inference(avatar_split_clause,[],[f403,f399,f350,f466])).
% 0.20/0.47  fof(f350,plain,(
% 0.20/0.47    spl2_39 <=> ! [X0] : (r1_tarski(X0,u1_struct_0(sK0)) | ~r1_tarski(X0,sK1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_39])])).
% 0.20/0.47  fof(f403,plain,(
% 0.20/0.47    r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) | (~spl2_39 | ~spl2_43)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f401,f351])).
% 0.20/0.47  fof(f351,plain,(
% 0.20/0.47    ( ! [X0] : (r1_tarski(X0,u1_struct_0(sK0)) | ~r1_tarski(X0,sK1)) ) | ~spl2_39),
% 0.20/0.47    inference(avatar_component_clause,[],[f350])).
% 0.20/0.47  fof(f402,plain,(
% 0.20/0.47    spl2_43 | ~spl2_6 | ~spl2_26),
% 0.20/0.47    inference(avatar_split_clause,[],[f397,f205,f83,f399])).
% 0.20/0.47  fof(f83,plain,(
% 0.20/0.47    spl2_6 <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.20/0.47  fof(f205,plain,(
% 0.20/0.47    spl2_26 <=> k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).
% 0.20/0.47  fof(f397,plain,(
% 0.20/0.47    r1_tarski(k2_tops_1(sK0,sK1),sK1) | (~spl2_6 | ~spl2_26)),
% 0.20/0.47    inference(superposition,[],[f84,f207])).
% 0.20/0.47  fof(f207,plain,(
% 0.20/0.47    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~spl2_26),
% 0.20/0.47    inference(avatar_component_clause,[],[f205])).
% 0.20/0.47  fof(f84,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) ) | ~spl2_6),
% 0.20/0.47    inference(avatar_component_clause,[],[f83])).
% 0.20/0.47  fof(f352,plain,(
% 0.20/0.47    spl2_39 | ~spl2_11 | ~spl2_13),
% 0.20/0.47    inference(avatar_split_clause,[],[f139,f116,f107,f350])).
% 0.20/0.47  fof(f116,plain,(
% 0.20/0.47    spl2_13 <=> ! [X1,X0,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.20/0.47  fof(f139,plain,(
% 0.20/0.47    ( ! [X0] : (r1_tarski(X0,u1_struct_0(sK0)) | ~r1_tarski(X0,sK1)) ) | (~spl2_11 | ~spl2_13)),
% 0.20/0.47    inference(resolution,[],[f109,f117])).
% 0.20/0.47  fof(f117,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) ) | ~spl2_13),
% 0.20/0.47    inference(avatar_component_clause,[],[f116])).
% 0.20/0.47  fof(f323,plain,(
% 0.20/0.47    spl2_36 | ~spl2_9 | ~spl2_17),
% 0.20/0.47    inference(avatar_split_clause,[],[f159,f148,f95,f321])).
% 0.20/0.47  fof(f148,plain,(
% 0.20/0.47    spl2_17 <=> ! [X1,X0] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.20/0.47  fof(f159,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~v4_pre_topc(X0,X1) | r1_tarski(k2_tops_1(X1,X0),X0) | ~l1_pre_topc(X1) | ~r1_tarski(X0,u1_struct_0(X1))) ) | (~spl2_9 | ~spl2_17)),
% 0.20/0.47    inference(resolution,[],[f149,f96])).
% 0.20/0.47  fof(f149,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | r1_tarski(k2_tops_1(X0,X1),X1) | ~l1_pre_topc(X0)) ) | ~spl2_17),
% 0.20/0.47    inference(avatar_component_clause,[],[f148])).
% 0.20/0.47  fof(f284,plain,(
% 0.20/0.47    spl2_32 | ~spl2_7 | ~spl2_10),
% 0.20/0.47    inference(avatar_split_clause,[],[f120,f99,f87,f282])).
% 0.20/0.47  fof(f87,plain,(
% 0.20/0.47    spl2_7 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.20/0.47  fof(f99,plain,(
% 0.20/0.47    spl2_10 <=> ! [X1,X0] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.20/0.47  fof(f120,plain,(
% 0.20/0.47    ( ! [X2,X3] : (k2_xboole_0(X3,X2) = X3 | ~r1_tarski(X2,X3)) ) | (~spl2_7 | ~spl2_10)),
% 0.20/0.47    inference(superposition,[],[f100,f88])).
% 0.20/0.47  fof(f88,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) ) | ~spl2_7),
% 0.20/0.47    inference(avatar_component_clause,[],[f87])).
% 0.20/0.47  fof(f100,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) ) | ~spl2_10),
% 0.20/0.47    inference(avatar_component_clause,[],[f99])).
% 0.20/0.47  fof(f213,plain,(
% 0.20/0.47    spl2_27 | ~spl2_2 | ~spl2_3 | ~spl2_21),
% 0.20/0.47    inference(avatar_split_clause,[],[f179,f176,f67,f62,f210])).
% 0.20/0.47  fof(f176,plain,(
% 0.20/0.47    spl2_21 <=> ! [X1,X0] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).
% 0.20/0.47  fof(f179,plain,(
% 0.20/0.47    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_3 | ~spl2_21)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f64,f69,f177])).
% 0.20/0.47  fof(f177,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl2_21),
% 0.20/0.47    inference(avatar_component_clause,[],[f176])).
% 0.20/0.47  fof(f208,plain,(
% 0.20/0.47    ~spl2_3 | spl2_26 | ~spl2_5 | ~spl2_15),
% 0.20/0.47    inference(avatar_split_clause,[],[f141,f133,f76,f205,f67])).
% 0.20/0.47  fof(f76,plain,(
% 0.20/0.47    spl2_5 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.20/0.47  fof(f141,plain,(
% 0.20/0.47    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_5 | ~spl2_15)),
% 0.20/0.47    inference(superposition,[],[f134,f78])).
% 0.20/0.47  fof(f78,plain,(
% 0.20/0.47    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~spl2_5),
% 0.20/0.47    inference(avatar_component_clause,[],[f76])).
% 0.20/0.47  fof(f201,plain,(
% 0.20/0.47    spl2_25 | ~spl2_2 | ~spl2_3 | ~spl2_19),
% 0.20/0.47    inference(avatar_split_clause,[],[f170,f162,f67,f62,f198])).
% 0.20/0.47  fof(f162,plain,(
% 0.20/0.47    spl2_19 <=> ! [X1,X0] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.20/0.47  fof(f170,plain,(
% 0.20/0.47    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_3 | ~spl2_19)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f64,f69,f163])).
% 0.20/0.47  fof(f163,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl2_19),
% 0.20/0.47    inference(avatar_component_clause,[],[f162])).
% 0.20/0.47  fof(f185,plain,(
% 0.20/0.47    spl2_22 | ~spl2_3 | ~spl2_15),
% 0.20/0.47    inference(avatar_split_clause,[],[f140,f133,f67,f183])).
% 0.20/0.47  fof(f140,plain,(
% 0.20/0.47    ( ! [X0] : (k4_xboole_0(sK1,X0) = k7_subset_1(u1_struct_0(sK0),sK1,X0)) ) | (~spl2_3 | ~spl2_15)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f69,f134])).
% 0.20/0.47  fof(f178,plain,(
% 0.20/0.47    spl2_21),
% 0.20/0.47    inference(avatar_split_clause,[],[f43,f176])).
% 0.20/0.47  fof(f43,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f19])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f11])).
% 0.20/0.47  fof(f11,axiom,(
% 0.20/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).
% 0.20/0.47  fof(f169,plain,(
% 0.20/0.47    spl2_20 | ~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_16),
% 0.20/0.47    inference(avatar_split_clause,[],[f151,f144,f67,f62,f57,f166])).
% 0.20/0.47  fof(f57,plain,(
% 0.20/0.47    spl2_1 <=> v2_pre_topc(sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.47  fof(f144,plain,(
% 0.20/0.47    spl2_16 <=> ! [X1,X0] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.20/0.47  fof(f151,plain,(
% 0.20/0.47    v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_16)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f59,f64,f69,f145])).
% 0.20/0.47  fof(f145,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl2_16),
% 0.20/0.47    inference(avatar_component_clause,[],[f144])).
% 0.20/0.47  fof(f59,plain,(
% 0.20/0.47    v2_pre_topc(sK0) | ~spl2_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f57])).
% 0.20/0.47  fof(f164,plain,(
% 0.20/0.47    spl2_19),
% 0.20/0.47    inference(avatar_split_clause,[],[f42,f162])).
% 0.20/0.47  fof(f42,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f18])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f12])).
% 0.20/0.47  fof(f12,axiom,(
% 0.20/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).
% 0.20/0.47  fof(f157,plain,(
% 0.20/0.47    spl2_18),
% 0.20/0.47    inference(avatar_split_clause,[],[f55,f155])).
% 0.20/0.47  fof(f55,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f30])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.47    inference(flattening,[],[f29])).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.20/0.47    inference(ennf_transformation,[],[f7])).
% 0.20/0.47  fof(f7,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.20/0.47  fof(f150,plain,(
% 0.20/0.47    spl2_17),
% 0.20/0.47    inference(avatar_split_clause,[],[f44,f148])).
% 0.20/0.47  fof(f44,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f21])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.47    inference(flattening,[],[f20])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : ((r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f13])).
% 0.20/0.47  fof(f13,axiom,(
% 0.20/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).
% 0.20/0.47  fof(f146,plain,(
% 0.20/0.47    spl2_16),
% 0.20/0.47    inference(avatar_split_clause,[],[f49,f144])).
% 0.20/0.47  fof(f49,plain,(
% 0.20/0.47    ( ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f24])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.47    inference(flattening,[],[f23])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f10])).
% 0.20/0.47  fof(f10,axiom,(
% 0.20/0.47    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_pre_topc(X0,X1),X0))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).
% 0.20/0.47  fof(f135,plain,(
% 0.20/0.47    spl2_15),
% 0.20/0.47    inference(avatar_split_clause,[],[f52,f133])).
% 0.20/0.47  fof(f52,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f25])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f8])).
% 0.20/0.47  fof(f8,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.20/0.47  fof(f118,plain,(
% 0.20/0.47    spl2_13),
% 0.20/0.47    inference(avatar_split_clause,[],[f54,f116])).
% 0.20/0.47  fof(f54,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f28])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.47    inference(flattening,[],[f27])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.47    inference(ennf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.20/0.47  fof(f110,plain,(
% 0.20/0.47    spl2_11 | ~spl2_3 | ~spl2_8),
% 0.20/0.47    inference(avatar_split_clause,[],[f102,f91,f67,f107])).
% 0.20/0.47  fof(f91,plain,(
% 0.20/0.47    spl2_8 <=> ! [X1,X0] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.20/0.47  fof(f102,plain,(
% 0.20/0.47    r1_tarski(sK1,u1_struct_0(sK0)) | (~spl2_3 | ~spl2_8)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f69,f92])).
% 0.20/0.47  fof(f92,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) ) | ~spl2_8),
% 0.20/0.47    inference(avatar_component_clause,[],[f91])).
% 0.20/0.47  fof(f101,plain,(
% 0.20/0.47    spl2_10),
% 0.20/0.47    inference(avatar_split_clause,[],[f48,f99])).
% 0.20/0.47  fof(f48,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f22])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.20/0.47  fof(f97,plain,(
% 0.20/0.47    spl2_9),
% 0.20/0.47    inference(avatar_split_clause,[],[f51,f95])).
% 0.20/0.47  fof(f51,plain,(
% 0.20/0.47    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f36])).
% 0.20/0.47  fof(f36,plain,(
% 0.20/0.47    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.47    inference(nnf_transformation,[],[f9])).
% 0.20/0.47  fof(f9,axiom,(
% 0.20/0.47    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.47  fof(f93,plain,(
% 0.20/0.47    spl2_8),
% 0.20/0.47    inference(avatar_split_clause,[],[f50,f91])).
% 0.20/0.47  fof(f50,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f36])).
% 0.20/0.47  fof(f89,plain,(
% 0.20/0.47    spl2_7),
% 0.20/0.47    inference(avatar_split_clause,[],[f46,f87])).
% 0.20/0.47  fof(f46,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.20/0.47  fof(f85,plain,(
% 0.20/0.47    spl2_6),
% 0.20/0.47    inference(avatar_split_clause,[],[f45,f83])).
% 0.20/0.47  fof(f45,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,axiom,(
% 0.20/0.47    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.20/0.47  fof(f79,plain,(
% 0.20/0.47    spl2_4 | spl2_5),
% 0.20/0.47    inference(avatar_split_clause,[],[f40,f76,f72])).
% 0.20/0.47  fof(f40,plain,(
% 0.20/0.47    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f35])).
% 0.20/0.47  fof(f70,plain,(
% 0.20/0.47    spl2_3),
% 0.20/0.47    inference(avatar_split_clause,[],[f39,f67])).
% 0.20/0.47  fof(f39,plain,(
% 0.20/0.47    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.47    inference(cnf_transformation,[],[f35])).
% 0.20/0.47  fof(f65,plain,(
% 0.20/0.47    spl2_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f38,f62])).
% 0.20/0.47  fof(f38,plain,(
% 0.20/0.47    l1_pre_topc(sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f35])).
% 0.20/0.47  fof(f60,plain,(
% 0.20/0.47    spl2_1),
% 0.20/0.47    inference(avatar_split_clause,[],[f37,f57])).
% 0.20/0.47  fof(f37,plain,(
% 0.20/0.47    v2_pre_topc(sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f35])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (10167)------------------------------
% 0.20/0.47  % (10167)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (10167)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (10167)Memory used [KB]: 6524
% 0.20/0.47  % (10167)Time elapsed: 0.028 s
% 0.20/0.47  % (10167)------------------------------
% 0.20/0.47  % (10167)------------------------------
% 0.20/0.47  % (10161)Success in time 0.115 s
%------------------------------------------------------------------------------
