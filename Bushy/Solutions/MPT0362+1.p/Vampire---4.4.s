%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : subset_1__t42_subset_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:23 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  184 ( 471 expanded)
%              Number of leaves         :   48 ( 189 expanded)
%              Depth                    :    9
%              Number of atoms          :  399 (1025 expanded)
%              Number of equality atoms :   71 ( 174 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6009,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f79,f86,f93,f100,f127,f142,f149,f162,f169,f292,f308,f315,f325,f360,f802,f812,f829,f837,f845,f860,f1513,f1521,f1529,f3863,f3870,f4655,f4679,f4897,f4921,f5990])).

fof(f5990,plain,
    ( ~ spl4_4
    | spl4_39 ),
    inference(avatar_contradiction_clause,[],[f5989])).

fof(f5989,plain,
    ( $false
    | ~ spl4_4
    | ~ spl4_39 ),
    inference(subsumption_resolution,[],[f5988,f282])).

fof(f282,plain,
    ( ! [X0] : m1_subset_1(k3_xboole_0(sK1,X0),k1_zfmisc_1(sK0))
    | ~ spl4_4 ),
    inference(superposition,[],[f270,f61])).

fof(f61,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t42_subset_1.p',commutativity_k3_xboole_0)).

fof(f270,plain,
    ( ! [X7] : m1_subset_1(k3_xboole_0(X7,sK1),k1_zfmisc_1(sK0))
    | ~ spl4_4 ),
    inference(superposition,[],[f170,f241])).

fof(f241,plain,
    ( ! [X0] : k9_subset_1(sK0,X0,sK1) = k3_xboole_0(X0,sK1)
    | ~ spl4_4 ),
    inference(resolution,[],[f70,f92])).

fof(f92,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl4_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t42_subset_1.p',redefinition_k9_subset_1)).

fof(f170,plain,
    ( ! [X0] : m1_subset_1(k9_subset_1(sK0,X0,sK1),k1_zfmisc_1(sK0))
    | ~ spl4_4 ),
    inference(resolution,[],[f69,f92])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t42_subset_1.p',dt_k9_subset_1)).

fof(f5988,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
    | ~ spl4_4
    | ~ spl4_39 ),
    inference(subsumption_resolution,[],[f5961,f92])).

fof(f5961,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
    | ~ spl4_39 ),
    inference(resolution,[],[f861,f859])).

fof(f859,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k3_xboole_0(sK1,sK2)))
    | ~ spl4_39 ),
    inference(avatar_component_clause,[],[f858])).

fof(f858,plain,
    ( spl4_39
  <=> ~ r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k3_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f861,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k3_xboole_0(X1,X2)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(resolution,[],[f65,f60])).

fof(f60,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t42_subset_1.p',t17_xboole_1)).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_tarski(X1,X2)
              | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
            & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | ~ r1_tarski(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t42_subset_1.p',t31_subset_1)).

fof(f4921,plain,
    ( spl4_56
    | ~ spl4_22
    | ~ spl4_24
    | ~ spl4_54 ),
    inference(avatar_split_clause,[],[f4898,f4895,f323,f313,f4919])).

fof(f4919,plain,
    ( spl4_56
  <=> r1_tarski(k3_subset_1(sK0,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).

fof(f313,plain,
    ( spl4_22
  <=> k3_subset_1(sK0,sK0) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f323,plain,
    ( spl4_24
  <=> m1_subset_1(sK0,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f4895,plain,
    ( spl4_54
  <=> m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).

fof(f4898,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),sK0)
    | ~ spl4_22
    | ~ spl4_24
    | ~ spl4_54 ),
    inference(resolution,[],[f4896,f1426])).

fof(f1426,plain,
    ( ! [X10] :
        ( ~ m1_subset_1(X10,k1_zfmisc_1(sK0))
        | r1_tarski(X10,sK0) )
    | ~ spl4_22
    | ~ spl4_24 ),
    inference(subsumption_resolution,[],[f1425,f324])).

fof(f324,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(sK0))
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f323])).

fof(f1425,plain,
    ( ! [X10] :
        ( r1_tarski(X10,sK0)
        | ~ m1_subset_1(sK0,k1_zfmisc_1(sK0))
        | ~ m1_subset_1(X10,k1_zfmisc_1(sK0)) )
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f1404,f102])).

fof(f102,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(superposition,[],[f60,f56])).

fof(f56,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/subset_1__t42_subset_1.p',t2_boole)).

fof(f1404,plain,
    ( ! [X10] :
        ( ~ r1_tarski(k1_xboole_0,k3_subset_1(sK0,X10))
        | r1_tarski(X10,sK0)
        | ~ m1_subset_1(sK0,k1_zfmisc_1(sK0))
        | ~ m1_subset_1(X10,k1_zfmisc_1(sK0)) )
    | ~ spl4_22 ),
    inference(superposition,[],[f66,f314])).

fof(f314,plain,
    ( k3_subset_1(sK0,sK0) = k1_xboole_0
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f313])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f4896,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ spl4_54 ),
    inference(avatar_component_clause,[],[f4895])).

fof(f4897,plain,
    ( spl4_54
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f4885,f98,f4895])).

fof(f98,plain,
    ( spl4_6
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f4885,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ spl4_6 ),
    inference(superposition,[],[f4873,f59])).

fof(f59,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/subset_1__t42_subset_1.p',idempotence_k3_xboole_0)).

fof(f4873,plain,
    ( ! [X6] : m1_subset_1(k3_xboole_0(X6,k3_subset_1(sK0,sK2)),k1_zfmisc_1(sK0))
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f4869,f99])).

fof(f99,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f98])).

fof(f4869,plain,
    ( ! [X6] :
        ( m1_subset_1(k3_xboole_0(X6,k3_subset_1(sK0,sK2)),k1_zfmisc_1(sK0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0)) )
    | ~ spl4_6 ),
    inference(superposition,[],[f172,f4578])).

fof(f4578,plain,
    ( ! [X339] : k9_subset_1(sK0,X339,k3_subset_1(sK0,sK2)) = k3_xboole_0(X339,k3_subset_1(sK0,sK2))
    | ~ spl4_6 ),
    inference(resolution,[],[f249,f99])).

fof(f249,plain,(
    ! [X21,X22,X20] :
      ( ~ m1_subset_1(X22,k1_zfmisc_1(X20))
      | k9_subset_1(X20,X21,k3_subset_1(X20,X22)) = k3_xboole_0(X21,k3_subset_1(X20,X22)) ) ),
    inference(resolution,[],[f70,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t42_subset_1.p',dt_k3_subset_1)).

fof(f172,plain,(
    ! [X4,X2,X3] :
      ( m1_subset_1(k9_subset_1(X2,X3,k3_subset_1(X2,X4)),k1_zfmisc_1(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X2)) ) ),
    inference(resolution,[],[f69,f62])).

fof(f4679,plain,
    ( spl4_52
    | ~ spl4_22
    | ~ spl4_24
    | ~ spl4_50 ),
    inference(avatar_split_clause,[],[f4656,f4653,f323,f313,f4677])).

fof(f4677,plain,
    ( spl4_52
  <=> r1_tarski(k3_subset_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).

fof(f4653,plain,
    ( spl4_50
  <=> m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).

fof(f4656,plain,
    ( r1_tarski(k3_subset_1(sK0,sK1),sK0)
    | ~ spl4_22
    | ~ spl4_24
    | ~ spl4_50 ),
    inference(resolution,[],[f4654,f1426])).

fof(f4654,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl4_50 ),
    inference(avatar_component_clause,[],[f4653])).

fof(f4655,plain,
    ( spl4_50
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f4643,f91,f4653])).

fof(f4643,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl4_4 ),
    inference(superposition,[],[f4631,f59])).

fof(f4631,plain,
    ( ! [X6] : m1_subset_1(k3_xboole_0(X6,k3_subset_1(sK0,sK1)),k1_zfmisc_1(sK0))
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f4627,f92])).

fof(f4627,plain,
    ( ! [X6] :
        ( m1_subset_1(k3_xboole_0(X6,k3_subset_1(sK0,sK1)),k1_zfmisc_1(sK0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0)) )
    | ~ spl4_4 ),
    inference(superposition,[],[f172,f4577])).

fof(f4577,plain,
    ( ! [X338] : k9_subset_1(sK0,X338,k3_subset_1(sK0,sK1)) = k3_xboole_0(X338,k3_subset_1(sK0,sK1))
    | ~ spl4_4 ),
    inference(resolution,[],[f249,f92])).

fof(f3870,plain,
    ( spl4_48
    | ~ spl4_6
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f3855,f147,f98,f3868])).

fof(f3868,plain,
    ( spl4_48
  <=> k4_xboole_0(sK0,k3_subset_1(sK0,sK2)) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).

fof(f147,plain,
    ( spl4_12
  <=> k3_subset_1(sK0,k3_subset_1(sK0,sK2)) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f3855,plain,
    ( k4_xboole_0(sK0,k3_subset_1(sK0,sK2)) = sK2
    | ~ spl4_6
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f3758,f148])).

fof(f148,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,sK2)) = sK2
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f147])).

fof(f3758,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,sK2)) = k4_xboole_0(sK0,k3_subset_1(sK0,sK2))
    | ~ spl4_6 ),
    inference(resolution,[],[f154,f99])).

fof(f154,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = k4_xboole_0(X0,k3_subset_1(X0,X1)) ) ),
    inference(resolution,[],[f64,f62])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t42_subset_1.p',d5_subset_1)).

fof(f3863,plain,
    ( spl4_46
    | ~ spl4_4
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f3854,f140,f91,f3861])).

fof(f3861,plain,
    ( spl4_46
  <=> k4_xboole_0(sK0,k3_subset_1(sK0,sK1)) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).

fof(f140,plain,
    ( spl4_10
  <=> k3_subset_1(sK0,k3_subset_1(sK0,sK1)) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f3854,plain,
    ( k4_xboole_0(sK0,k3_subset_1(sK0,sK1)) = sK1
    | ~ spl4_4
    | ~ spl4_10 ),
    inference(forward_demodulation,[],[f3757,f141])).

fof(f141,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,sK1)) = sK1
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f140])).

fof(f3757,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,sK1)) = k4_xboole_0(sK0,k3_subset_1(sK0,sK1))
    | ~ spl4_4 ),
    inference(resolution,[],[f154,f92])).

fof(f1529,plain,
    ( spl4_44
    | ~ spl4_22
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f1493,f323,f313,f1527])).

fof(f1527,plain,
    ( spl4_44
  <=> r1_tarski(sK3(k1_zfmisc_1(sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).

fof(f1493,plain,
    ( r1_tarski(sK3(k1_zfmisc_1(sK0)),sK0)
    | ~ spl4_22
    | ~ spl4_24 ),
    inference(resolution,[],[f1426,f58])).

fof(f58,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f16,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t42_subset_1.p',existence_m1_subset_1)).

fof(f1521,plain,
    ( spl4_42
    | ~ spl4_6
    | ~ spl4_22
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f1490,f323,f313,f98,f1519])).

fof(f1519,plain,
    ( spl4_42
  <=> r1_tarski(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f1490,plain,
    ( r1_tarski(sK2,sK0)
    | ~ spl4_6
    | ~ spl4_22
    | ~ spl4_24 ),
    inference(resolution,[],[f1426,f99])).

fof(f1513,plain,
    ( spl4_40
    | ~ spl4_4
    | ~ spl4_22
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f1489,f323,f313,f91,f1511])).

fof(f1511,plain,
    ( spl4_40
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f1489,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl4_4
    | ~ spl4_22
    | ~ spl4_24 ),
    inference(resolution,[],[f1426,f92])).

fof(f860,plain,
    ( ~ spl4_39
    | ~ spl4_6
    | spl4_9 ),
    inference(avatar_split_clause,[],[f373,f125,f98,f858])).

fof(f125,plain,
    ( spl4_9
  <=> ~ r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k9_subset_1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f373,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k3_xboole_0(sK1,sK2)))
    | ~ spl4_6
    | ~ spl4_9 ),
    inference(superposition,[],[f126,f242])).

fof(f242,plain,
    ( ! [X1] : k9_subset_1(sK0,X1,sK2) = k3_xboole_0(X1,sK2)
    | ~ spl4_6 ),
    inference(resolution,[],[f70,f99])).

fof(f126,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k9_subset_1(sK0,sK1,sK2)))
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f125])).

fof(f845,plain,
    ( spl4_36
    | ~ spl4_32
    | ~ spl4_34 ),
    inference(avatar_split_clause,[],[f838,f835,f827,f843])).

fof(f843,plain,
    ( spl4_36
  <=> k1_xboole_0 = sK3(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f827,plain,
    ( spl4_32
  <=> k3_subset_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f835,plain,
    ( spl4_34
  <=> k3_subset_1(k1_xboole_0,k1_xboole_0) = sK3(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f838,plain,
    ( k1_xboole_0 = sK3(k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_32
    | ~ spl4_34 ),
    inference(forward_demodulation,[],[f836,f828])).

fof(f828,plain,
    ( k3_subset_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | ~ spl4_32 ),
    inference(avatar_component_clause,[],[f827])).

fof(f836,plain,
    ( k3_subset_1(k1_xboole_0,k1_xboole_0) = sK3(k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_34 ),
    inference(avatar_component_clause,[],[f835])).

fof(f837,plain,
    ( spl4_34
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f803,f800,f835])).

fof(f800,plain,
    ( spl4_28
  <=> k3_subset_1(k1_xboole_0,sK3(k1_zfmisc_1(k1_xboole_0))) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f803,plain,
    ( k3_subset_1(k1_xboole_0,k1_xboole_0) = sK3(k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_28 ),
    inference(superposition,[],[f135,f801])).

fof(f801,plain,
    ( k3_subset_1(k1_xboole_0,sK3(k1_zfmisc_1(k1_xboole_0))) = k1_xboole_0
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f800])).

fof(f135,plain,(
    ! [X2] : k3_subset_1(X2,k3_subset_1(X2,sK3(k1_zfmisc_1(X2)))) = sK3(k1_zfmisc_1(X2)) ),
    inference(resolution,[],[f63,f58])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t42_subset_1.p',involutiveness_k3_subset_1)).

fof(f829,plain,
    ( spl4_32
    | ~ spl4_30 ),
    inference(avatar_split_clause,[],[f821,f810,f827])).

fof(f810,plain,
    ( spl4_30
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f821,plain,
    ( k3_subset_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f816,f54])).

fof(f54,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/subset_1__t42_subset_1.p',t3_boole)).

fof(f816,plain,
    ( k3_subset_1(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl4_30 ),
    inference(resolution,[],[f811,f64])).

fof(f811,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f810])).

fof(f812,plain,
    ( spl4_30
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f805,f800,f810])).

fof(f805,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_28 ),
    inference(subsumption_resolution,[],[f804,f58])).

fof(f804,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ m1_subset_1(sK3(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_28 ),
    inference(superposition,[],[f62,f801])).

fof(f802,plain,(
    spl4_28 ),
    inference(avatar_split_clause,[],[f239,f800])).

fof(f239,plain,(
    k3_subset_1(k1_xboole_0,sK3(k1_zfmisc_1(k1_xboole_0))) = k1_xboole_0 ),
    inference(superposition,[],[f155,f55])).

fof(f55,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t42_subset_1.p',t4_boole)).

fof(f155,plain,(
    ! [X2] : k3_subset_1(X2,sK3(k1_zfmisc_1(X2))) = k4_xboole_0(X2,sK3(k1_zfmisc_1(X2))) ),
    inference(resolution,[],[f64,f58])).

fof(f360,plain,
    ( spl4_26
    | ~ spl4_22
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f332,f323,f313,f358])).

fof(f358,plain,
    ( spl4_26
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f332,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK0)
    | ~ spl4_22
    | ~ spl4_24 ),
    inference(forward_demodulation,[],[f328,f314])).

fof(f328,plain,
    ( k3_subset_1(sK0,sK0) = k4_xboole_0(sK0,sK0)
    | ~ spl4_24 ),
    inference(resolution,[],[f324,f64])).

fof(f325,plain,
    ( spl4_24
    | ~ spl4_18
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f317,f306,f290,f323])).

fof(f290,plain,
    ( spl4_18
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f306,plain,
    ( spl4_20
  <=> k3_subset_1(sK0,k1_xboole_0) = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f317,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(sK0))
    | ~ spl4_18
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f316,f291])).

fof(f291,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0))
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f290])).

fof(f316,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0))
    | ~ spl4_20 ),
    inference(superposition,[],[f62,f307])).

fof(f307,plain,
    ( k3_subset_1(sK0,k1_xboole_0) = sK0
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f306])).

fof(f315,plain,
    ( spl4_22
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f301,f290,f313])).

fof(f301,plain,
    ( k3_subset_1(sK0,sK0) = k1_xboole_0
    | ~ spl4_18 ),
    inference(forward_demodulation,[],[f296,f300])).

fof(f300,plain,
    ( k3_subset_1(sK0,k1_xboole_0) = sK0
    | ~ spl4_18 ),
    inference(forward_demodulation,[],[f295,f54])).

fof(f295,plain,
    ( k3_subset_1(sK0,k1_xboole_0) = k4_xboole_0(sK0,k1_xboole_0)
    | ~ spl4_18 ),
    inference(resolution,[],[f291,f64])).

fof(f296,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,k1_xboole_0)) = k1_xboole_0
    | ~ spl4_18 ),
    inference(resolution,[],[f291,f63])).

fof(f308,plain,
    ( spl4_20
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f300,f290,f306])).

fof(f292,plain,
    ( spl4_18
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f284,f91,f290])).

fof(f284,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0))
    | ~ spl4_4 ),
    inference(superposition,[],[f270,f104])).

fof(f104,plain,(
    ! [X0] : k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[],[f61,f56])).

fof(f169,plain,
    ( spl4_16
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f153,f98,f167])).

fof(f167,plain,
    ( spl4_16
  <=> k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f153,plain,
    ( k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)
    | ~ spl4_6 ),
    inference(resolution,[],[f64,f99])).

fof(f162,plain,
    ( spl4_14
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f152,f91,f160])).

fof(f160,plain,
    ( spl4_14
  <=> k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f152,plain,
    ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)
    | ~ spl4_4 ),
    inference(resolution,[],[f64,f92])).

fof(f149,plain,
    ( spl4_12
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f133,f98,f147])).

fof(f133,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,sK2)) = sK2
    | ~ spl4_6 ),
    inference(resolution,[],[f63,f99])).

fof(f142,plain,
    ( spl4_10
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f132,f91,f140])).

fof(f132,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,sK1)) = sK1
    | ~ spl4_4 ),
    inference(resolution,[],[f63,f92])).

fof(f127,plain,(
    ~ spl4_9 ),
    inference(avatar_split_clause,[],[f51,f125])).

fof(f51,plain,(
    ~ r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k9_subset_1(sK0,sK1,sK2))) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k9_subset_1(sK0,sK1,sK2)))
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f32,f44,f43])).

fof(f43,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k9_subset_1(sK0,sK1,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
     => ( ~ r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,sK2)))
        & m1_subset_1(sK2,k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2))) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t42_subset_1.p',t42_subset_1)).

fof(f100,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f50,f98])).

fof(f50,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f45])).

fof(f93,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f49,f91])).

fof(f49,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f45])).

fof(f86,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f53,f84])).

fof(f84,plain,
    ( spl4_2
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f53,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/subset_1__t42_subset_1.p',d2_xboole_0)).

fof(f79,plain,(
    spl4_0 ),
    inference(avatar_split_clause,[],[f72,f77])).

fof(f77,plain,
    ( spl4_0
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_0])])).

fof(f72,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(forward_demodulation,[],[f52,f53])).

fof(f52,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t42_subset_1.p',dt_o_0_0_xboole_0)).
%------------------------------------------------------------------------------
