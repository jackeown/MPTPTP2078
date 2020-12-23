%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tops_1__t93_tops_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:34 EDT 2019

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 257 expanded)
%              Number of leaves         :   37 ( 107 expanded)
%              Depth                    :   10
%              Number of atoms          :  361 ( 738 expanded)
%              Number of equality atoms :   26 (  47 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f303,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f83,f90,f97,f104,f111,f118,f125,f135,f152,f173,f181,f206,f221,f238,f265,f273,f282,f292,f297,f302])).

fof(f302,plain,
    ( ~ spl4_0
    | ~ spl4_6
    | spl4_11
    | ~ spl4_12
    | ~ spl4_30 ),
    inference(avatar_contradiction_clause,[],[f301])).

fof(f301,plain,
    ( $false
    | ~ spl4_0
    | ~ spl4_6
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f300,f82])).

fof(f82,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_0 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl4_0
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_0])])).

fof(f300,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl4_6
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f299,f124])).

fof(f124,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl4_12
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f299,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_6
    | ~ spl4_11
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f298,f117])).

fof(f117,plain,
    ( ~ v3_tops_1(sK1,sK0)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl4_11
  <=> ~ v3_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f298,plain,
    ( v3_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_6
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f294,f103])).

fof(f103,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl4_6
  <=> v2_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f294,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | v3_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_30 ),
    inference(superposition,[],[f65,f264])).

fof(f264,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f263])).

fof(f263,plain,
    ( spl4_30
  <=> k2_pre_topc(sK0,sK1) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ v2_tops_1(k2_pre_topc(X0,X1),X0)
      | v3_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tops_1(X1,X0)
              | ~ v2_tops_1(k2_pre_topc(X0,X1),X0) )
            & ( v2_tops_1(k2_pre_topc(X0,X1),X0)
              | ~ v3_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tops_1(X1,X0)
          <=> v2_tops_1(k2_pre_topc(X0,X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
          <=> v2_tops_1(k2_pre_topc(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t93_tops_1.p',d5_tops_1)).

fof(f297,plain,
    ( ~ spl4_0
    | ~ spl4_6
    | spl4_11
    | ~ spl4_12
    | ~ spl4_30 ),
    inference(avatar_contradiction_clause,[],[f296])).

fof(f296,plain,
    ( $false
    | ~ spl4_0
    | ~ spl4_6
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f295,f103])).

fof(f295,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | ~ spl4_0
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f293,f264])).

fof(f293,plain,
    ( ~ v2_tops_1(k2_pre_topc(sK0,sK1),sK0)
    | ~ spl4_0
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(unit_resulting_resolution,[],[f82,f117,f124,f65])).

fof(f292,plain,
    ( ~ spl4_37
    | spl4_33 ),
    inference(avatar_split_clause,[],[f274,f271,f290])).

fof(f290,plain,
    ( spl4_37
  <=> ~ r2_hidden(k1_zfmisc_1(o_0_0_xboole_0),sK2(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f271,plain,
    ( spl4_33
  <=> ~ m1_subset_1(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f274,plain,
    ( ~ r2_hidden(k1_zfmisc_1(o_0_0_xboole_0),sK2(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl4_33 ),
    inference(unit_resulting_resolution,[],[f66,f272,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t93_tops_1.p',t4_subset)).

fof(f272,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl4_33 ),
    inference(avatar_component_clause,[],[f271])).

fof(f66,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f15,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t93_tops_1.p',existence_m1_subset_1)).

fof(f282,plain,
    ( ~ spl4_35
    | spl4_33 ),
    inference(avatar_split_clause,[],[f275,f271,f280])).

fof(f280,plain,
    ( spl4_35
  <=> ~ r2_hidden(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f275,plain,
    ( ~ r2_hidden(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl4_33 ),
    inference(unit_resulting_resolution,[],[f272,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t93_tops_1.p',t1_subset)).

fof(f273,plain,
    ( ~ spl4_33
    | ~ spl4_2
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f249,f219,f88,f271])).

fof(f88,plain,
    ( spl4_2
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f219,plain,
    ( spl4_26
  <=> r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f249,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl4_2
    | ~ spl4_26 ),
    inference(unit_resulting_resolution,[],[f89,f220,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t93_tops_1.p',t5_subset)).

fof(f220,plain,
    ( r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f219])).

fof(f89,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f88])).

fof(f265,plain,
    ( spl4_30
    | ~ spl4_0
    | ~ spl4_8
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f239,f123,f109,f81,f263])).

fof(f109,plain,
    ( spl4_8
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f239,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | ~ spl4_0
    | ~ spl4_8
    | ~ spl4_12 ),
    inference(unit_resulting_resolution,[],[f82,f110,f124,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = X1
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = X1
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => k2_pre_topc(X0,X1) = X1 ) ) ) ),
    inference(pure_predicate_removal,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t93_tops_1.p',t52_pre_topc)).

fof(f110,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f109])).

fof(f238,plain,
    ( ~ spl4_29
    | ~ spl4_2
    | spl4_25 ),
    inference(avatar_split_clause,[],[f228,f210,f88,f236])).

fof(f236,plain,
    ( spl4_29
  <=> ~ v1_xboole_0(k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f210,plain,
    ( spl4_25
  <=> k1_zfmisc_1(o_0_0_xboole_0) != o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f228,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl4_2
    | ~ spl4_25 ),
    inference(unit_resulting_resolution,[],[f89,f211,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t93_tops_1.p',t8_boole)).

fof(f211,plain,
    ( k1_zfmisc_1(o_0_0_xboole_0) != o_0_0_xboole_0
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f210])).

fof(f221,plain,
    ( spl4_24
    | spl4_26
    | ~ spl4_2
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f186,f179,f88,f219,f213])).

fof(f213,plain,
    ( spl4_24
  <=> k1_zfmisc_1(o_0_0_xboole_0) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f179,plain,
    ( spl4_20
  <=> m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f186,plain,
    ( r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | k1_zfmisc_1(o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl4_2
    | ~ spl4_20 ),
    inference(resolution,[],[f143,f180])).

fof(f180,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f179])).

fof(f143,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(X3,X4)
        | r2_hidden(X3,X4)
        | o_0_0_xboole_0 = X4 )
    | ~ spl4_2 ),
    inference(resolution,[],[f69,f128])).

fof(f128,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | o_0_0_xboole_0 = X0 )
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f126,f62])).

fof(f62,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t93_tops_1.p',t6_boole)).

fof(f126,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f89,f62])).

fof(f69,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t93_tops_1.p',t2_subset)).

fof(f206,plain,
    ( spl4_22
    | ~ spl4_0
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f198,f123,f81,f204])).

fof(f204,plain,
    ( spl4_22
  <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f198,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_12 ),
    inference(unit_resulting_resolution,[],[f82,f124,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t93_tops_1.p',dt_k2_pre_topc)).

fof(f181,plain,
    ( spl4_20
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f174,f171,f179])).

fof(f171,plain,
    ( spl4_18
  <=> o_0_0_xboole_0 = sK2(k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f174,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl4_18 ),
    inference(superposition,[],[f66,f172])).

fof(f172,plain,
    ( o_0_0_xboole_0 = sK2(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f171])).

fof(f173,plain,
    ( spl4_18
    | ~ spl4_2
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f158,f150,f88,f171])).

fof(f150,plain,
    ( spl4_16
  <=> v1_xboole_0(sK2(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f158,plain,
    ( o_0_0_xboole_0 = sK2(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl4_2
    | ~ spl4_16 ),
    inference(unit_resulting_resolution,[],[f151,f128])).

fof(f151,plain,
    ( v1_xboole_0(sK2(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f150])).

fof(f152,plain,
    ( spl4_16
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f145,f88,f150])).

fof(f145,plain,
    ( v1_xboole_0(sK2(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f66,f144,f69])).

fof(f144,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK2(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f89,f66,f75])).

fof(f135,plain,
    ( spl4_14
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f126,f88,f133])).

fof(f133,plain,
    ( spl4_14
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f125,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f57,f123])).

fof(f57,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,
    ( ~ v3_tops_1(sK1,sK0)
    & v4_pre_topc(sK1,sK0)
    & v2_tops_1(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f49,f48])).

fof(f48,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v3_tops_1(X1,X0)
            & v4_pre_topc(X1,X0)
            & v2_tops_1(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ v3_tops_1(X1,sK0)
          & v4_pre_topc(X1,sK0)
          & v2_tops_1(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_tops_1(X1,X0)
          & v4_pre_topc(X1,X0)
          & v2_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_tops_1(sK1,X0)
        & v4_pre_topc(sK1,X0)
        & v2_tops_1(sK1,X0)
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_tops_1(X1,X0)
          & v4_pre_topc(X1,X0)
          & v2_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_tops_1(X1,X0)
          & v4_pre_topc(X1,X0)
          & v2_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ( v4_pre_topc(X1,X0)
                & v2_tops_1(X1,X0) )
             => v3_tops_1(X1,X0) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v4_pre_topc(X1,X0)
              & v2_tops_1(X1,X0) )
           => v3_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t93_tops_1.p',t93_tops_1)).

fof(f118,plain,(
    ~ spl4_11 ),
    inference(avatar_split_clause,[],[f60,f116])).

fof(f60,plain,(
    ~ v3_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f111,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f59,f109])).

fof(f59,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f104,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f58,f102])).

fof(f58,plain,(
    v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f97,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f76,f95])).

fof(f95,plain,
    ( spl4_4
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f76,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    l1_pre_topc(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f13,f54])).

fof(f54,plain,
    ( ? [X0] : l1_pre_topc(X0)
   => l1_pre_topc(sK3) ),
    introduced(choice_axiom,[])).

fof(f13,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t93_tops_1.p',existence_l1_pre_topc)).

fof(f90,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f61,f88])).

fof(f61,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t93_tops_1.p',dt_o_0_0_xboole_0)).

fof(f83,plain,(
    spl4_0 ),
    inference(avatar_split_clause,[],[f56,f81])).

fof(f56,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f50])).
%------------------------------------------------------------------------------
