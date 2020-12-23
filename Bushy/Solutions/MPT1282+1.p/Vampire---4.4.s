%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tops_1__t104_tops_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:26 EDT 2019

% Result     : Theorem 0.17s
% Output     : Refutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :  192 ( 593 expanded)
%              Number of leaves         :   52 ( 235 expanded)
%              Depth                    :   10
%              Number of atoms          :  498 (1356 expanded)
%              Number of equality atoms :   82 ( 259 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1225,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f135,f142,f149,f156,f163,f176,f203,f224,f234,f243,f253,f277,f291,f309,f515,f679,f719,f740,f747,f775,f827,f883,f890,f897,f1022,f1045,f1054,f1176,f1224])).

fof(f1224,plain,
    ( ~ spl4_0
    | ~ spl4_8
    | ~ spl4_38
    | ~ spl4_50
    | ~ spl4_52
    | ~ spl4_54 ),
    inference(avatar_contradiction_clause,[],[f1223])).

fof(f1223,plain,
    ( $false
    | ~ spl4_0
    | ~ spl4_8
    | ~ spl4_38
    | ~ spl4_50
    | ~ spl4_52
    | ~ spl4_54 ),
    inference(subsumption_resolution,[],[f1222,f1215])).

fof(f1215,plain,
    ( k2_tops_1(sK0,sK1) != k2_tops_1(sK0,k2_pre_topc(sK0,sK1))
    | ~ spl4_0
    | ~ spl4_8
    | ~ spl4_50 ),
    inference(duplicate_literal_removal,[],[f1214])).

fof(f1214,plain,
    ( k2_tops_1(sK0,sK1) != k2_tops_1(sK0,k2_pre_topc(sK0,sK1))
    | k2_tops_1(sK0,sK1) != k2_tops_1(sK0,k2_pre_topc(sK0,sK1))
    | ~ spl4_0
    | ~ spl4_8
    | ~ spl4_50 ),
    inference(backward_demodulation,[],[f1213,f94])).

fof(f94,plain,
    ( k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | k2_tops_1(sK0,sK1) != k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) ),
    inference(cnf_transformation,[],[f85])).

fof(f85,plain,
    ( ( k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | k2_tops_1(sK0,sK1) != k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) )
    & v6_tops_1(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f50,f84,f83])).

fof(f83,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k2_tops_1(X0,k2_pre_topc(X0,X1)) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
              | k2_tops_1(X0,X1) != k2_tops_1(X0,k2_pre_topc(X0,X1)) )
            & v6_tops_1(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k2_tops_1(sK0,k2_pre_topc(sK0,X1)) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
            | k2_tops_1(sK0,X1) != k2_tops_1(sK0,k2_pre_topc(sK0,X1)) )
          & v6_tops_1(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f84,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,k2_pre_topc(X0,X1)) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | k2_tops_1(X0,X1) != k2_tops_1(X0,k2_pre_topc(X0,X1)) )
          & v6_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( k2_tops_1(X0,k2_pre_topc(X0,sK1)) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,sK1),sK1)
          | k2_tops_1(X0,sK1) != k2_tops_1(X0,k2_pre_topc(X0,sK1)) )
        & v6_tops_1(sK1,X0)
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,k2_pre_topc(X0,X1)) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | k2_tops_1(X0,X1) != k2_tops_1(X0,k2_pre_topc(X0,X1)) )
          & v6_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,k2_pre_topc(X0,X1)) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | k2_tops_1(X0,X1) != k2_tops_1(X0,k2_pre_topc(X0,X1)) )
          & v6_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v6_tops_1(X1,X0)
             => ( k2_tops_1(X0,k2_pre_topc(X0,X1)) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
                & k2_tops_1(X0,X1) = k2_tops_1(X0,k2_pre_topc(X0,X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v6_tops_1(X1,X0)
           => ( k2_tops_1(X0,k2_pre_topc(X0,X1)) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
              & k2_tops_1(X0,X1) = k2_tops_1(X0,k2_pre_topc(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t104_tops_1.p',t104_tops_1)).

fof(f1213,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ spl4_0
    | ~ spl4_8
    | ~ spl4_50 ),
    inference(forward_demodulation,[],[f1208,f1044])).

fof(f1044,plain,
    ( k1_tops_1(sK0,sK1) = sK1
    | ~ spl4_50 ),
    inference(avatar_component_clause,[],[f1043])).

fof(f1043,plain,
    ( spl4_50
  <=> k1_tops_1(sK0,sK1) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).

fof(f1208,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl4_0
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f134,f162,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t104_tops_1.p',l78_tops_1)).

fof(f162,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f161])).

fof(f161,plain,
    ( spl4_8
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f134,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_0 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl4_0
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_0])])).

fof(f1222,plain,
    ( k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k2_pre_topc(sK0,sK1))
    | ~ spl4_0
    | ~ spl4_8
    | ~ spl4_38
    | ~ spl4_50
    | ~ spl4_52
    | ~ spl4_54 ),
    inference(forward_demodulation,[],[f1221,f1213])).

fof(f1221,plain,
    ( k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ spl4_0
    | ~ spl4_38
    | ~ spl4_52
    | ~ spl4_54 ),
    inference(forward_demodulation,[],[f1220,f1175])).

fof(f1175,plain,
    ( k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK1))
    | ~ spl4_54 ),
    inference(avatar_component_clause,[],[f1174])).

fof(f1174,plain,
    ( spl4_54
  <=> k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).

fof(f1220,plain,
    ( k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)),sK1)
    | ~ spl4_0
    | ~ spl4_38
    | ~ spl4_52 ),
    inference(forward_demodulation,[],[f1180,f1053])).

fof(f1053,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = sK1
    | ~ spl4_52 ),
    inference(avatar_component_clause,[],[f1052])).

fof(f1052,plain,
    ( spl4_52
  <=> k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).

fof(f1180,plain,
    ( k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))
    | ~ spl4_0
    | ~ spl4_38 ),
    inference(unit_resulting_resolution,[],[f134,f774,f100])).

fof(f774,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_38 ),
    inference(avatar_component_clause,[],[f773])).

fof(f773,plain,
    ( spl4_38
  <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f1176,plain,
    ( spl4_54
    | ~ spl4_0
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f919,f161,f133,f1174])).

fof(f919,plain,
    ( k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK1))
    | ~ spl4_0
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f134,f162,f117])).

fof(f117,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t104_tops_1.p',projectivity_k2_pre_topc)).

fof(f1054,plain,
    ( spl4_52
    | ~ spl4_0
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f1023,f161,f154,f133,f1052])).

fof(f154,plain,
    ( spl4_6
  <=> v6_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f1023,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = sK1
    | ~ spl4_0
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f134,f155,f162,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ v6_tops_1(X1,X0)
      | k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f86,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v6_tops_1(X1,X0)
              | k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1 )
            & ( k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1
              | ~ v6_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v6_tops_1(X1,X0)
          <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v6_tops_1(X1,X0)
          <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t104_tops_1.p',d8_tops_1)).

fof(f155,plain,
    ( v6_tops_1(sK1,sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f154])).

fof(f1045,plain,
    ( spl4_50
    | ~ spl4_0
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_38 ),
    inference(avatar_split_clause,[],[f1025,f773,f161,f154,f133,f1043])).

fof(f1025,plain,
    ( k1_tops_1(sK0,sK1) = sK1
    | ~ spl4_0
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_38 ),
    inference(backward_demodulation,[],[f1023,f830])).

fof(f830,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))
    | ~ spl4_0
    | ~ spl4_38 ),
    inference(unit_resulting_resolution,[],[f134,f774,f116])).

fof(f116,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t104_tops_1.p',projectivity_k1_tops_1)).

fof(f1022,plain,
    ( spl4_48
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f516,f513,f1020])).

fof(f1020,plain,
    ( spl4_48
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).

fof(f513,plain,
    ( spl4_28
  <=> m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f516,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_28 ),
    inference(unit_resulting_resolution,[],[f514,f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t104_tops_1.p',dt_k3_subset_1)).

fof(f514,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f513])).

fof(f897,plain,
    ( spl4_46
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f761,f147,f140,f895])).

fof(f895,plain,
    ( spl4_46
  <=> m1_subset_1(k2_pre_topc(sK3,o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).

fof(f140,plain,
    ( spl4_2
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f147,plain,
    ( spl4_4
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f761,plain,
    ( m1_subset_1(k2_pre_topc(sK3,o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f148,f606,f115])).

fof(f115,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t104_tops_1.p',dt_k2_pre_topc)).

fof(f606,plain,
    ( ! [X5] : m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(X5))
    | ~ spl4_2 ),
    inference(superposition,[],[f481,f180])).

fof(f180,plain,
    ( ! [X1] : k3_xboole_0(o_0_0_xboole_0,X1) = o_0_0_xboole_0
    | ~ spl4_2 ),
    inference(superposition,[],[f107,f168])).

fof(f168,plain,
    ( ! [X0] : k3_xboole_0(X0,o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f164,f97])).

fof(f97,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t104_tops_1.p',t2_boole)).

fof(f164,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f141,f99])).

fof(f99,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f43])).

fof(f43,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t104_tops_1.p',t6_boole)).

fof(f141,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f140])).

fof(f107,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t104_tops_1.p',commutativity_k3_xboole_0)).

fof(f481,plain,(
    ! [X0,X1] : m1_subset_1(k3_xboole_0(X1,sK2(k1_zfmisc_1(X0))),k1_zfmisc_1(X0)) ),
    inference(backward_demodulation,[],[f465,f314])).

fof(f314,plain,(
    ! [X0,X1] : m1_subset_1(k9_subset_1(X0,X1,sK2(k1_zfmisc_1(X0))),k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f105,f121])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t104_tops_1.p',dt_k9_subset_1)).

fof(f105,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(cnf_transformation,[],[f88])).

fof(f88,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f26,f87])).

fof(f87,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f26,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t104_tops_1.p',existence_m1_subset_1)).

fof(f465,plain,(
    ! [X0,X1] : k3_xboole_0(X0,sK2(k1_zfmisc_1(X1))) = k9_subset_1(X1,X0,sK2(k1_zfmisc_1(X1))) ),
    inference(unit_resulting_resolution,[],[f105,f124])).

fof(f124,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t104_tops_1.p',redefinition_k9_subset_1)).

fof(f148,plain,
    ( l1_pre_topc(sK3)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f147])).

fof(f890,plain,
    ( spl4_44
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f691,f147,f140,f888])).

fof(f888,plain,
    ( spl4_44
  <=> m1_subset_1(k2_tops_1(sK3,o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).

fof(f691,plain,
    ( m1_subset_1(k2_tops_1(sK3,o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f148,f606,f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t104_tops_1.p',dt_k2_tops_1)).

fof(f883,plain,
    ( spl4_42
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f638,f147,f140,f881])).

fof(f881,plain,
    ( spl4_42
  <=> m1_subset_1(k1_tops_1(sK3,o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f638,plain,
    ( m1_subset_1(k1_tops_1(sK3,o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f148,f606,f113])).

fof(f113,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t104_tops_1.p',dt_k1_tops_1)).

fof(f827,plain,
    ( spl4_40
    | ~ spl4_0
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f760,f140,f133,f825])).

fof(f825,plain,
    ( spl4_40
  <=> m1_subset_1(k2_pre_topc(sK0,o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f760,plain,
    ( m1_subset_1(k2_pre_topc(sK0,o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f134,f606,f115])).

fof(f775,plain,
    ( spl4_38
    | ~ spl4_0
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f765,f161,f133,f773])).

fof(f765,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f134,f162,f115])).

fof(f747,plain,
    ( spl4_36
    | ~ spl4_0
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f690,f140,f133,f745])).

fof(f745,plain,
    ( spl4_36
  <=> m1_subset_1(k2_tops_1(sK0,o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f690,plain,
    ( m1_subset_1(k2_tops_1(sK0,o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f134,f606,f114])).

fof(f740,plain,
    ( spl4_34
    | ~ spl4_0
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f637,f140,f133,f738])).

fof(f738,plain,
    ( spl4_34
  <=> m1_subset_1(k1_tops_1(sK0,o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f637,plain,
    ( m1_subset_1(k1_tops_1(sK0,o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f134,f606,f113])).

fof(f719,plain,
    ( spl4_32
    | ~ spl4_0
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f695,f161,f133,f717])).

fof(f717,plain,
    ( spl4_32
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f695,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f134,f162,f114])).

fof(f679,plain,
    ( spl4_30
    | ~ spl4_0
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f642,f161,f133,f677])).

fof(f677,plain,
    ( spl4_30
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f642,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f134,f162,f113])).

fof(f515,plain,
    ( spl4_28
    | ~ spl4_2
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f506,f161,f140,f513])).

fof(f506,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_2
    | ~ spl4_8 ),
    inference(superposition,[],[f487,f180])).

fof(f487,plain,
    ( ! [X0] : m1_subset_1(k3_xboole_0(X0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_8 ),
    inference(backward_demodulation,[],[f464,f313])).

fof(f313,plain,
    ( ! [X0] : m1_subset_1(k9_subset_1(u1_struct_0(sK0),X0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f162,f121])).

fof(f464,plain,
    ( ! [X0] : k3_xboole_0(X0,sK1) = k9_subset_1(u1_struct_0(sK0),X0,sK1)
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f162,f124])).

fof(f309,plain,
    ( spl4_26
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f280,f161,f307])).

fof(f307,plain,
    ( spl4_26
  <=> k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f280,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = sK1
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f162,f112])).

fof(f112,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t104_tops_1.p',involutiveness_k3_subset_1)).

fof(f291,plain,
    ( spl4_24
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f195,f161,f289])).

fof(f289,plain,
    ( spl4_24
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f195,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f162,f111])).

fof(f277,plain,
    ( spl4_22
    | ~ spl4_2
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f259,f251,f140,f275])).

fof(f275,plain,
    ( spl4_22
  <=> k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f251,plain,
    ( spl4_20
  <=> v1_xboole_0(k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f259,plain,
    ( k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl4_2
    | ~ spl4_20 ),
    inference(unit_resulting_resolution,[],[f252,f166])).

fof(f166,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | o_0_0_xboole_0 = X0 )
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f164,f99])).

fof(f252,plain,
    ( v1_xboole_0(k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f251])).

fof(f253,plain,
    ( spl4_20
    | ~ spl4_2
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f246,f241,f140,f251])).

fof(f241,plain,
    ( spl4_18
  <=> m1_subset_1(k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f246,plain,
    ( v1_xboole_0(k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl4_2
    | ~ spl4_18 ),
    inference(unit_resulting_resolution,[],[f105,f245,f110])).

fof(f110,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t104_tops_1.p',t2_subset)).

fof(f245,plain,
    ( ! [X0] : ~ r2_hidden(X0,k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl4_2
    | ~ spl4_18 ),
    inference(unit_resulting_resolution,[],[f141,f242,f127])).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f82])).

fof(f82,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f42])).

fof(f42,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t104_tops_1.p',t5_subset)).

fof(f242,plain,
    ( m1_subset_1(k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f241])).

fof(f243,plain,
    ( spl4_18
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f235,f232,f241])).

fof(f232,plain,
    ( spl4_16
  <=> m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f235,plain,
    ( m1_subset_1(k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl4_16 ),
    inference(unit_resulting_resolution,[],[f233,f111])).

fof(f233,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f232])).

fof(f234,plain,
    ( spl4_16
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f225,f222,f232])).

fof(f222,plain,
    ( spl4_14
  <=> o_0_0_xboole_0 = sK2(k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f225,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl4_14 ),
    inference(superposition,[],[f105,f223])).

fof(f223,plain,
    ( o_0_0_xboole_0 = sK2(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f222])).

fof(f224,plain,
    ( spl4_14
    | ~ spl4_2
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f209,f201,f140,f222])).

fof(f201,plain,
    ( spl4_12
  <=> v1_xboole_0(sK2(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f209,plain,
    ( o_0_0_xboole_0 = sK2(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl4_2
    | ~ spl4_12 ),
    inference(unit_resulting_resolution,[],[f202,f166])).

fof(f202,plain,
    ( v1_xboole_0(sK2(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f201])).

fof(f203,plain,
    ( spl4_12
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f196,f140,f201])).

fof(f196,plain,
    ( v1_xboole_0(sK2(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f105,f193,f110])).

fof(f193,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK2(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f141,f105,f127])).

fof(f176,plain,
    ( spl4_10
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f164,f140,f174])).

fof(f174,plain,
    ( spl4_10
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f163,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f92,f161])).

fof(f92,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f85])).

fof(f156,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f93,f154])).

fof(f93,plain,(
    v6_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f85])).

fof(f149,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f128,f147])).

fof(f128,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f90])).

fof(f90,plain,(
    l1_pre_topc(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f89])).

fof(f89,plain,
    ( ? [X0] : l1_pre_topc(X0)
   => l1_pre_topc(sK3) ),
    introduced(choice_axiom,[])).

fof(f24,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t104_tops_1.p',existence_l1_pre_topc)).

fof(f142,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f95,f140])).

fof(f95,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t104_tops_1.p',dt_o_0_0_xboole_0)).

fof(f135,plain,(
    spl4_0 ),
    inference(avatar_split_clause,[],[f91,f133])).

fof(f91,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f85])).
%------------------------------------------------------------------------------
