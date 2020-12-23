%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tops_1__t90_tops_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:33 EDT 2019

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  228 ( 655 expanded)
%              Number of leaves         :   62 ( 290 expanded)
%              Depth                    :   10
%              Number of atoms          :  714 (2009 expanded)
%              Number of equality atoms :   52 ( 126 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1040,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f118,f125,f132,f139,f146,f153,f160,f167,f178,f188,f210,f231,f239,f251,f258,f265,f275,f282,f293,f300,f313,f322,f329,f336,f347,f407,f414,f458,f481,f488,f501,f721,f729,f785,f870,f879,f886,f905,f912,f919,f975])).

fof(f975,plain,
    ( ~ spl5_0
    | ~ spl5_2
    | ~ spl5_12
    | ~ spl5_14
    | ~ spl5_34
    | ~ spl5_36
    | ~ spl5_38
    | ~ spl5_42
    | ~ spl5_44
    | spl5_67
    | ~ spl5_70 ),
    inference(avatar_contradiction_clause,[],[f974])).

fof(f974,plain,
    ( $false
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_12
    | ~ spl5_14
    | ~ spl5_34
    | ~ spl5_36
    | ~ spl5_38
    | ~ spl5_42
    | ~ spl5_44
    | ~ spl5_67
    | ~ spl5_70 ),
    inference(subsumption_resolution,[],[f971,f784])).

fof(f784,plain,
    ( ~ v2_tops_1(k2_pre_topc(sK0,k2_xboole_0(sK1,sK2)),sK0)
    | ~ spl5_67 ),
    inference(avatar_component_clause,[],[f783])).

fof(f783,plain,
    ( spl5_67
  <=> ~ v2_tops_1(k2_pre_topc(sK0,k2_xboole_0(sK1,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_67])])).

fof(f971,plain,
    ( v2_tops_1(k2_pre_topc(sK0,k2_xboole_0(sK1,sK2)),sK0)
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_12
    | ~ spl5_14
    | ~ spl5_34
    | ~ spl5_36
    | ~ spl5_38
    | ~ spl5_42
    | ~ spl5_44
    | ~ spl5_70 ),
    inference(backward_demodulation,[],[f970,f893])).

fof(f893,plain,
    ( v2_tops_1(k2_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),sK0)
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_34
    | ~ spl5_36
    | ~ spl5_38
    | ~ spl5_42
    | ~ spl5_44 ),
    inference(forward_demodulation,[],[f889,f525])).

fof(f525,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)) = k2_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))
    | ~ spl5_36
    | ~ spl5_38 ),
    inference(unit_resulting_resolution,[],[f292,f299,f107])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f65])).

fof(f65,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t90_tops_1.p',redefinition_k4_subset_1)).

fof(f299,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_38 ),
    inference(avatar_component_clause,[],[f298])).

fof(f298,plain,
    ( spl5_38
  <=> m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).

fof(f292,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_36 ),
    inference(avatar_component_clause,[],[f291])).

fof(f291,plain,
    ( spl5_36
  <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

fof(f889,plain,
    ( v2_tops_1(k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),sK0)
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_34
    | ~ spl5_36
    | ~ spl5_38
    | ~ spl5_42
    | ~ spl5_44 ),
    inference(unit_resulting_resolution,[],[f117,f124,f321,f292,f281,f328,f299,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ v2_tops_1(X2,X0)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v2_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ v2_tops_1(X2,X0)
              | ~ v2_tops_1(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ v2_tops_1(X2,X0)
              | ~ v2_tops_1(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v4_pre_topc(X2,X0)
                  & v2_tops_1(X2,X0)
                  & v2_tops_1(X1,X0) )
               => v2_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t90_tops_1.p',t85_tops_1)).

fof(f328,plain,
    ( v2_tops_1(k2_pre_topc(sK0,sK2),sK0)
    | ~ spl5_44 ),
    inference(avatar_component_clause,[],[f327])).

fof(f327,plain,
    ( spl5_44
  <=> v2_tops_1(k2_pre_topc(sK0,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).

fof(f281,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK2),sK0)
    | ~ spl5_34 ),
    inference(avatar_component_clause,[],[f280])).

fof(f280,plain,
    ( spl5_34
  <=> v4_pre_topc(k2_pre_topc(sK0,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f321,plain,
    ( v2_tops_1(k2_pre_topc(sK0,sK1),sK0)
    | ~ spl5_42 ),
    inference(avatar_component_clause,[],[f320])).

fof(f320,plain,
    ( spl5_42
  <=> v2_tops_1(k2_pre_topc(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).

fof(f124,plain,
    ( l1_pre_topc(sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl5_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f117,plain,
    ( v2_pre_topc(sK0)
    | ~ spl5_0 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl5_0
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_0])])).

fof(f970,plain,
    ( k2_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)) = k2_pre_topc(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_12
    | ~ spl5_14
    | ~ spl5_36
    | ~ spl5_38
    | ~ spl5_70 ),
    inference(backward_demodulation,[],[f969,f525])).

fof(f969,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)) = k2_pre_topc(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_12
    | ~ spl5_14
    | ~ spl5_70 ),
    inference(forward_demodulation,[],[f947,f878])).

fof(f878,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2)
    | ~ spl5_70 ),
    inference(avatar_component_clause,[],[f877])).

fof(f877,plain,
    ( spl5_70
  <=> k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_70])])).

fof(f947,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)) = k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_12
    | ~ spl5_14 ),
    inference(unit_resulting_resolution,[],[f117,f124,f159,f166,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) = k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) = k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) = k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) = k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t90_tops_1.p',t50_pre_topc)).

fof(f166,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f165])).

fof(f165,plain,
    ( spl5_14
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f159,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f158])).

fof(f158,plain,
    ( spl5_12
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f919,plain,
    ( spl5_78
    | ~ spl5_14
    | ~ spl5_36 ),
    inference(avatar_split_clause,[],[f605,f291,f165,f917])).

fof(f917,plain,
    ( spl5_78
  <=> m1_subset_1(k2_xboole_0(sK2,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_78])])).

fof(f605,plain,
    ( m1_subset_1(k2_xboole_0(sK2,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_14
    | ~ spl5_36 ),
    inference(backward_demodulation,[],[f604,f372])).

fof(f372,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_14
    | ~ spl5_36 ),
    inference(unit_resulting_resolution,[],[f292,f166,f106])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t90_tops_1.p',dt_k4_subset_1)).

fof(f604,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK2) = k2_xboole_0(sK2,k2_pre_topc(sK0,sK1))
    | ~ spl5_14
    | ~ spl5_36 ),
    inference(forward_demodulation,[],[f541,f95])).

fof(f95,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t90_tops_1.p',commutativity_k2_xboole_0)).

fof(f541,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK2) = k2_xboole_0(k2_pre_topc(sK0,sK1),sK2)
    | ~ spl5_14
    | ~ spl5_36 ),
    inference(unit_resulting_resolution,[],[f292,f166,f107])).

fof(f912,plain,
    ( spl5_76
    | ~ spl5_14
    | ~ spl5_38 ),
    inference(avatar_split_clause,[],[f603,f298,f165,f910])).

fof(f910,plain,
    ( spl5_76
  <=> m1_subset_1(k2_xboole_0(sK2,k2_pre_topc(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_76])])).

fof(f603,plain,
    ( m1_subset_1(k2_xboole_0(sK2,k2_pre_topc(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_14
    | ~ spl5_38 ),
    inference(backward_demodulation,[],[f602,f373])).

fof(f373,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_14
    | ~ spl5_38 ),
    inference(unit_resulting_resolution,[],[f299,f166,f106])).

fof(f602,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),sK2) = k2_xboole_0(sK2,k2_pre_topc(sK0,sK2))
    | ~ spl5_14
    | ~ spl5_38 ),
    inference(forward_demodulation,[],[f542,f95])).

fof(f542,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),sK2) = k2_xboole_0(k2_pre_topc(sK0,sK2),sK2)
    | ~ spl5_14
    | ~ spl5_38 ),
    inference(unit_resulting_resolution,[],[f299,f166,f107])).

fof(f905,plain,
    ( spl5_74
    | ~ spl5_2
    | ~ spl5_12
    | ~ spl5_14
    | ~ spl5_52 ),
    inference(avatar_split_clause,[],[f582,f412,f165,f158,f123,f903])).

fof(f903,plain,
    ( spl5_74
  <=> m1_subset_1(k2_pre_topc(sK0,k2_xboole_0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_74])])).

fof(f412,plain,
    ( spl5_52
  <=> m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).

fof(f582,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k2_xboole_0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_2
    | ~ spl5_12
    | ~ spl5_14
    | ~ spl5_52 ),
    inference(backward_demodulation,[],[f543,f433])).

fof(f433,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_2
    | ~ spl5_52 ),
    inference(unit_resulting_resolution,[],[f124,f413,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t90_tops_1.p',dt_k2_pre_topc)).

fof(f413,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_52 ),
    inference(avatar_component_clause,[],[f412])).

fof(f543,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2)
    | ~ spl5_12
    | ~ spl5_14 ),
    inference(unit_resulting_resolution,[],[f159,f166,f107])).

fof(f886,plain,
    ( spl5_72
    | ~ spl5_12
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f613,f165,f158,f884])).

fof(f884,plain,
    ( spl5_72
  <=> k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_72])])).

fof(f613,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k2_xboole_0(sK1,sK2)
    | ~ spl5_12
    | ~ spl5_14 ),
    inference(forward_demodulation,[],[f537,f95])).

fof(f537,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k2_xboole_0(sK2,sK1)
    | ~ spl5_12
    | ~ spl5_14 ),
    inference(unit_resulting_resolution,[],[f166,f159,f107])).

fof(f879,plain,
    ( spl5_70
    | ~ spl5_12
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f543,f165,f158,f877])).

fof(f870,plain,
    ( spl5_68
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_12
    | ~ spl5_14
    | ~ spl5_52 ),
    inference(avatar_split_clause,[],[f583,f412,f165,f158,f123,f116,f868])).

fof(f868,plain,
    ( spl5_68
  <=> v4_pre_topc(k2_pre_topc(sK0,k2_xboole_0(sK1,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_68])])).

fof(f583,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,k2_xboole_0(sK1,sK2)),sK0)
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_12
    | ~ spl5_14
    | ~ spl5_52 ),
    inference(backward_demodulation,[],[f543,f434])).

fof(f434,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),sK0)
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_52 ),
    inference(unit_resulting_resolution,[],[f117,f124,f413,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t90_tops_1.p',fc1_tops_1)).

fof(f785,plain,
    ( ~ spl5_67
    | ~ spl5_2
    | ~ spl5_12
    | ~ spl5_14
    | spl5_19
    | ~ spl5_52 ),
    inference(avatar_split_clause,[],[f581,f412,f186,f165,f158,f123,f783])).

fof(f186,plain,
    ( spl5_19
  <=> ~ v3_tops_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f581,plain,
    ( ~ v2_tops_1(k2_pre_topc(sK0,k2_xboole_0(sK1,sK2)),sK0)
    | ~ spl5_2
    | ~ spl5_12
    | ~ spl5_14
    | ~ spl5_19
    | ~ spl5_52 ),
    inference(backward_demodulation,[],[f543,f432])).

fof(f432,plain,
    ( ~ v2_tops_1(k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),sK0)
    | ~ spl5_2
    | ~ spl5_19
    | ~ spl5_52 ),
    inference(unit_resulting_resolution,[],[f124,f187,f413,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( v3_tops_1(X1,X0)
      | ~ v2_tops_1(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tops_1(X1,X0)
              | ~ v2_tops_1(k2_pre_topc(X0,X1),X0) )
            & ( v2_tops_1(k2_pre_topc(X0,X1),X0)
              | ~ v3_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tops_1(X1,X0)
          <=> v2_tops_1(k2_pre_topc(X0,X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
          <=> v2_tops_1(k2_pre_topc(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t90_tops_1.p',d5_tops_1)).

fof(f187,plain,
    ( ~ v3_tops_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f186])).

fof(f729,plain,
    ( spl5_64
    | ~ spl5_12
    | ~ spl5_14
    | ~ spl5_52 ),
    inference(avatar_split_clause,[],[f580,f412,f165,f158,f727])).

fof(f727,plain,
    ( spl5_64
  <=> m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_64])])).

fof(f580,plain,
    ( m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_12
    | ~ spl5_14
    | ~ spl5_52 ),
    inference(backward_demodulation,[],[f543,f413])).

fof(f721,plain,
    ( ~ spl5_63
    | ~ spl5_12
    | ~ spl5_14
    | spl5_19 ),
    inference(avatar_split_clause,[],[f578,f186,f165,f158,f719])).

fof(f719,plain,
    ( spl5_63
  <=> ~ v3_tops_1(k2_xboole_0(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_63])])).

fof(f578,plain,
    ( ~ v3_tops_1(k2_xboole_0(sK1,sK2),sK0)
    | ~ spl5_12
    | ~ spl5_14
    | ~ spl5_19 ),
    inference(backward_demodulation,[],[f543,f187])).

fof(f501,plain,
    ( spl5_60
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f416,f405,f123,f116,f499])).

fof(f499,plain,
    ( spl5_60
  <=> v4_pre_topc(k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK2,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_60])])).

fof(f405,plain,
    ( spl5_50
  <=> m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_50])])).

fof(f416,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK2,sK1)),sK0)
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_50 ),
    inference(unit_resulting_resolution,[],[f117,f124,f406,f99])).

fof(f406,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_50 ),
    inference(avatar_component_clause,[],[f405])).

fof(f488,plain,
    ( spl5_58
    | ~ spl5_2
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f464,f165,f123,f486])).

fof(f486,plain,
    ( spl5_58
  <=> k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_58])])).

fof(f464,plain,
    ( k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK2))
    | ~ spl5_2
    | ~ spl5_14 ),
    inference(unit_resulting_resolution,[],[f124,f166,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t90_tops_1.p',projectivity_k2_pre_topc)).

fof(f481,plain,
    ( spl5_56
    | ~ spl5_2
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f463,f158,f123,f479])).

fof(f479,plain,
    ( spl5_56
  <=> k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_56])])).

fof(f463,plain,
    ( k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK1))
    | ~ spl5_2
    | ~ spl5_12 ),
    inference(unit_resulting_resolution,[],[f124,f159,f101])).

fof(f458,plain,
    ( spl5_54
    | ~ spl5_2
    | ~ spl5_36 ),
    inference(avatar_split_clause,[],[f301,f291,f123,f456])).

fof(f456,plain,
    ( spl5_54
  <=> m1_subset_1(k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_54])])).

fof(f301,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_2
    | ~ spl5_36 ),
    inference(unit_resulting_resolution,[],[f124,f292,f100])).

fof(f414,plain,
    ( spl5_52
    | ~ spl5_12
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f374,f165,f158,f412])).

fof(f374,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_12
    | ~ spl5_14 ),
    inference(unit_resulting_resolution,[],[f159,f166,f106])).

fof(f407,plain,
    ( spl5_50
    | ~ spl5_12
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f370,f165,f158,f405])).

fof(f370,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_12
    | ~ spl5_14 ),
    inference(unit_resulting_resolution,[],[f166,f159,f106])).

fof(f347,plain,
    ( spl5_48
    | ~ spl5_0
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f268,f123,f116,f345])).

fof(f345,plain,
    ( spl5_48
  <=> v4_pre_topc(k2_pre_topc(sK0,sK3(k1_zfmisc_1(u1_struct_0(sK0)))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_48])])).

fof(f268,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK3(k1_zfmisc_1(u1_struct_0(sK0)))),sK0)
    | ~ spl5_0
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f117,f124,f93,f99])).

fof(f93,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f75])).

fof(f75,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f19,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t90_tops_1.p',existence_m1_subset_1)).

fof(f336,plain,
    ( spl5_46
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_38 ),
    inference(avatar_split_clause,[],[f305,f298,f123,f116,f334])).

fof(f334,plain,
    ( spl5_46
  <=> v4_pre_topc(k2_pre_topc(sK0,k2_pre_topc(sK0,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_46])])).

fof(f305,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,k2_pre_topc(sK0,sK2)),sK0)
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_38 ),
    inference(unit_resulting_resolution,[],[f117,f124,f299,f99])).

fof(f329,plain,
    ( spl5_44
    | ~ spl5_2
    | ~ spl5_10
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f315,f165,f151,f123,f327])).

fof(f151,plain,
    ( spl5_10
  <=> v3_tops_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f315,plain,
    ( v2_tops_1(k2_pre_topc(sK0,sK2),sK0)
    | ~ spl5_2
    | ~ spl5_10
    | ~ spl5_14 ),
    inference(unit_resulting_resolution,[],[f124,f152,f166,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( v2_tops_1(k2_pre_topc(X0,X1),X0)
      | ~ v3_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f152,plain,
    ( v3_tops_1(sK2,sK0)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f151])).

fof(f322,plain,
    ( spl5_42
    | ~ spl5_2
    | ~ spl5_8
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f314,f158,f144,f123,f320])).

fof(f144,plain,
    ( spl5_8
  <=> v3_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f314,plain,
    ( v2_tops_1(k2_pre_topc(sK0,sK1),sK0)
    | ~ spl5_2
    | ~ spl5_8
    | ~ spl5_12 ),
    inference(unit_resulting_resolution,[],[f124,f145,f159,f89])).

fof(f145,plain,
    ( v3_tops_1(sK1,sK0)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f144])).

fof(f313,plain,
    ( spl5_40
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_36 ),
    inference(avatar_split_clause,[],[f302,f291,f123,f116,f311])).

fof(f311,plain,
    ( spl5_40
  <=> v4_pre_topc(k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).

fof(f302,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)),sK0)
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_36 ),
    inference(unit_resulting_resolution,[],[f117,f124,f292,f99])).

fof(f300,plain,
    ( spl5_38
    | ~ spl5_2
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f284,f165,f123,f298])).

fof(f284,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_2
    | ~ spl5_14 ),
    inference(unit_resulting_resolution,[],[f124,f166,f100])).

fof(f293,plain,
    ( spl5_36
    | ~ spl5_2
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f283,f158,f123,f291])).

fof(f283,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_2
    | ~ spl5_12 ),
    inference(unit_resulting_resolution,[],[f124,f159,f100])).

fof(f282,plain,
    ( spl5_34
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f267,f165,f123,f116,f280])).

fof(f267,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK2),sK0)
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_14 ),
    inference(unit_resulting_resolution,[],[f117,f124,f166,f99])).

fof(f275,plain,
    ( spl5_32
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f266,f158,f123,f116,f273])).

fof(f273,plain,
    ( spl5_32
  <=> v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f266,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_12 ),
    inference(unit_resulting_resolution,[],[f117,f124,f159,f99])).

fof(f265,plain,
    ( spl5_30
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f243,f165,f263])).

fof(f263,plain,
    ( spl5_30
  <=> k4_subset_1(u1_struct_0(sK0),sK2,sK2) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f243,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK2) = sK2
    | ~ spl5_14 ),
    inference(unit_resulting_resolution,[],[f166,f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( k4_subset_1(X1,X0,X0) = X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(condensation,[],[f105])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t90_tops_1.p',idempotence_k4_subset_1)).

fof(f258,plain,
    ( spl5_28
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f242,f158,f256])).

fof(f256,plain,
    ( spl5_28
  <=> k4_subset_1(u1_struct_0(sK0),sK1,sK1) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f242,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) = sK1
    | ~ spl5_12 ),
    inference(unit_resulting_resolution,[],[f159,f111])).

fof(f251,plain,
    ( spl5_26
    | ~ spl5_24 ),
    inference(avatar_split_clause,[],[f241,f237,f249])).

fof(f249,plain,
    ( spl5_26
  <=> k4_subset_1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f237,plain,
    ( spl5_24
  <=> m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f241,plain,
    ( k4_subset_1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_24 ),
    inference(unit_resulting_resolution,[],[f238,f111])).

fof(f238,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f237])).

fof(f239,plain,
    ( spl5_24
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f232,f229,f237])).

fof(f229,plain,
    ( spl5_22
  <=> o_0_0_xboole_0 = sK3(k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f232,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_22 ),
    inference(superposition,[],[f93,f230])).

fof(f230,plain,
    ( o_0_0_xboole_0 = sK3(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f229])).

fof(f231,plain,
    ( spl5_22
    | ~ spl5_4
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f216,f208,f130,f229])).

fof(f130,plain,
    ( spl5_4
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f208,plain,
    ( spl5_20
  <=> v1_xboole_0(sK3(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f216,plain,
    ( o_0_0_xboole_0 = sK3(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_4
    | ~ spl5_20 ),
    inference(unit_resulting_resolution,[],[f209,f170])).

fof(f170,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | o_0_0_xboole_0 = X0 )
    | ~ spl5_4 ),
    inference(backward_demodulation,[],[f168,f88])).

fof(f88,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t90_tops_1.p',t6_boole)).

fof(f168,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl5_4 ),
    inference(unit_resulting_resolution,[],[f131,f88])).

fof(f131,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f130])).

fof(f209,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f208])).

fof(f210,plain,
    ( spl5_20
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f203,f130,f208])).

fof(f203,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl5_4 ),
    inference(unit_resulting_resolution,[],[f93,f202,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t90_tops_1.p',t2_subset)).

fof(f202,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK3(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl5_4 ),
    inference(unit_resulting_resolution,[],[f131,f93,f109])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t90_tops_1.p',t5_subset)).

fof(f188,plain,(
    ~ spl5_19 ),
    inference(avatar_split_clause,[],[f85,f186])).

fof(f85,plain,(
    ~ v3_tops_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,
    ( ~ v3_tops_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    & v3_tops_1(sK2,sK0)
    & v3_tops_1(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f40,f72,f71,f70])).

fof(f70,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v3_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
                & v3_tops_1(X2,X0)
                & v3_tops_1(X1,X0)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v3_tops_1(k4_subset_1(u1_struct_0(sK0),X1,X2),sK0)
              & v3_tops_1(X2,sK0)
              & v3_tops_1(X1,sK0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f71,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v3_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v3_tops_1(X2,X0)
              & v3_tops_1(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ~ v3_tops_1(k4_subset_1(u1_struct_0(X0),sK1,X2),X0)
            & v3_tops_1(X2,X0)
            & v3_tops_1(sK1,X0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ v3_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
          & v3_tops_1(X2,X0)
          & v3_tops_1(X1,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_tops_1(k4_subset_1(u1_struct_0(X0),X1,sK2),X0)
        & v3_tops_1(sK2,X0)
        & v3_tops_1(X1,X0)
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v3_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v3_tops_1(X2,X0)
              & v3_tops_1(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v3_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v3_tops_1(X2,X0)
              & v3_tops_1(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v3_tops_1(X2,X0)
                    & v3_tops_1(X1,X0) )
                 => v3_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v3_tops_1(X2,X0)
                  & v3_tops_1(X1,X0) )
               => v3_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t90_tops_1.p',t90_tops_1)).

fof(f178,plain,
    ( spl5_16
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f168,f130,f176])).

fof(f176,plain,
    ( spl5_16
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f167,plain,(
    spl5_14 ),
    inference(avatar_split_clause,[],[f82,f165])).

fof(f82,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f73])).

fof(f160,plain,(
    spl5_12 ),
    inference(avatar_split_clause,[],[f81,f158])).

fof(f81,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f73])).

fof(f153,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f84,f151])).

fof(f84,plain,(
    v3_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f73])).

fof(f146,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f83,f144])).

fof(f83,plain,(
    v3_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f73])).

fof(f139,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f110,f137])).

fof(f137,plain,
    ( spl5_6
  <=> l1_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f110,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    l1_pre_topc(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f17,f77])).

fof(f77,plain,
    ( ? [X0] : l1_pre_topc(X0)
   => l1_pre_topc(sK4) ),
    introduced(choice_axiom,[])).

fof(f17,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t90_tops_1.p',existence_l1_pre_topc)).

fof(f132,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f86,f130])).

fof(f86,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t90_tops_1.p',dt_o_0_0_xboole_0)).

fof(f125,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f80,f123])).

fof(f80,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f73])).

fof(f118,plain,(
    spl5_0 ),
    inference(avatar_split_clause,[],[f79,f116])).

fof(f79,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f73])).
%------------------------------------------------------------------------------
