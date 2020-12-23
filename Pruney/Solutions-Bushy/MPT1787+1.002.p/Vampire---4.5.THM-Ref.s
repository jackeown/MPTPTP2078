%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1787+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:32 EST 2020

% Result     : Theorem 1.83s
% Output     : Refutation 1.83s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 263 expanded)
%              Number of leaves         :   39 ( 107 expanded)
%              Depth                    :   14
%              Number of atoms          :  565 ( 893 expanded)
%              Number of equality atoms :   46 (  53 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2204,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f124,f129,f134,f139,f144,f150,f160,f185,f220,f231,f244,f251,f411,f416,f1693,f2199])).

fof(f2199,plain,
    ( spl14_1
    | ~ spl14_2
    | ~ spl14_3
    | ~ spl14_4
    | spl14_5
    | ~ spl14_10
    | ~ spl14_12
    | ~ spl14_13
    | ~ spl14_30
    | ~ spl14_31
    | ~ spl14_98 ),
    inference(avatar_contradiction_clause,[],[f2198])).

fof(f2198,plain,
    ( $false
    | spl14_1
    | ~ spl14_2
    | ~ spl14_3
    | ~ spl14_4
    | spl14_5
    | ~ spl14_10
    | ~ spl14_12
    | ~ spl14_13
    | ~ spl14_30
    | ~ spl14_31
    | ~ spl14_98 ),
    inference(subsumption_resolution,[],[f2197,f123])).

fof(f123,plain,
    ( ~ r2_hidden(sK7,k5_tmap_1(sK6,sK7))
    | spl14_1 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl14_1
  <=> r2_hidden(sK7,k5_tmap_1(sK6,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_1])])).

fof(f2197,plain,
    ( r2_hidden(sK7,k5_tmap_1(sK6,sK7))
    | ~ spl14_2
    | ~ spl14_3
    | ~ spl14_4
    | spl14_5
    | ~ spl14_10
    | ~ spl14_12
    | ~ spl14_13
    | ~ spl14_30
    | ~ spl14_31
    | ~ spl14_98 ),
    inference(forward_demodulation,[],[f2196,f243])).

fof(f243,plain,
    ( sK7 = k3_xboole_0(sK7,u1_struct_0(sK6))
    | ~ spl14_13 ),
    inference(avatar_component_clause,[],[f241])).

fof(f241,plain,
    ( spl14_13
  <=> sK7 = k3_xboole_0(sK7,u1_struct_0(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_13])])).

fof(f2196,plain,
    ( r2_hidden(k3_xboole_0(sK7,u1_struct_0(sK6)),k5_tmap_1(sK6,sK7))
    | ~ spl14_2
    | ~ spl14_3
    | ~ spl14_4
    | spl14_5
    | ~ spl14_10
    | ~ spl14_12
    | ~ spl14_30
    | ~ spl14_31
    | ~ spl14_98 ),
    inference(forward_demodulation,[],[f2116,f1692])).

fof(f1692,plain,
    ( k5_tmap_1(sK6,sK7) = a_2_0_tmap_1(sK6,sK7)
    | ~ spl14_98 ),
    inference(avatar_component_clause,[],[f1690])).

fof(f1690,plain,
    ( spl14_98
  <=> k5_tmap_1(sK6,sK7) = a_2_0_tmap_1(sK6,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_98])])).

fof(f2116,plain,
    ( r2_hidden(k3_xboole_0(sK7,u1_struct_0(sK6)),a_2_0_tmap_1(sK6,sK7))
    | ~ spl14_2
    | ~ spl14_3
    | ~ spl14_4
    | spl14_5
    | ~ spl14_10
    | ~ spl14_12
    | ~ spl14_30
    | ~ spl14_31 ),
    inference(unit_resulting_resolution,[],[f1248,f1940,f109])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,a_2_0_tmap_1(X2,X0))
      | ~ sP4(X2,X1,X0)
      | ~ sP5(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X1,a_2_0_tmap_1(X2,X0))
          | ~ sP4(X2,X1,X0) )
        & ( sP4(X2,X1,X0)
          | ~ r2_hidden(X1,a_2_0_tmap_1(X2,X0)) ) )
      | ~ sP5(X0,X1,X2) ) ),
    inference(rectify,[],[f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ( ( r2_hidden(X0,a_2_0_tmap_1(X1,X2))
          | ~ sP4(X1,X0,X2) )
        & ( sP4(X1,X0,X2)
          | ~ r2_hidden(X0,a_2_0_tmap_1(X1,X2)) ) )
      | ~ sP5(X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ( r2_hidden(X0,a_2_0_tmap_1(X1,X2))
      <=> sP4(X1,X0,X2) )
      | ~ sP5(X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).

fof(f1940,plain,
    ( ! [X0] : sP4(sK6,k3_xboole_0(X0,u1_struct_0(sK6)),X0)
    | ~ spl14_10
    | ~ spl14_12
    | ~ spl14_30
    | ~ spl14_31 ),
    inference(forward_demodulation,[],[f1939,f1630])).

fof(f1630,plain,
    ( ! [X0] : k3_xboole_0(X0,u1_struct_0(sK6)) = k4_subset_1(u1_struct_0(sK6),k1_xboole_0,k3_xboole_0(X0,u1_struct_0(sK6)))
    | ~ spl14_30
    | ~ spl14_31 ),
    inference(forward_demodulation,[],[f1310,f195])).

fof(f195,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f100,f78])).

fof(f78,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f100,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f1310,plain,
    ( ! [X0] : k4_subset_1(u1_struct_0(sK6),k1_xboole_0,k3_xboole_0(X0,u1_struct_0(sK6))) = k2_xboole_0(k1_xboole_0,k3_xboole_0(X0,u1_struct_0(sK6)))
    | ~ spl14_30
    | ~ spl14_31 ),
    inference(unit_resulting_resolution,[],[f410,f648,f118])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f648,plain,
    ( ! [X0] : m1_subset_1(k3_xboole_0(X0,u1_struct_0(sK6)),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ spl14_31 ),
    inference(backward_demodulation,[],[f476,f564])).

fof(f564,plain,
    ( ! [X0] : k9_subset_1(u1_struct_0(sK6),X0,u1_struct_0(sK6)) = k3_xboole_0(X0,u1_struct_0(sK6))
    | ~ spl14_31 ),
    inference(unit_resulting_resolution,[],[f415,f106])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f415,plain,
    ( m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ spl14_31 ),
    inference(avatar_component_clause,[],[f413])).

fof(f413,plain,
    ( spl14_31
  <=> m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_31])])).

fof(f476,plain,
    ( ! [X0] : m1_subset_1(k9_subset_1(u1_struct_0(sK6),X0,u1_struct_0(sK6)),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ spl14_31 ),
    inference(unit_resulting_resolution,[],[f415,f105])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f410,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ spl14_30 ),
    inference(avatar_component_clause,[],[f408])).

fof(f408,plain,
    ( spl14_30
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_30])])).

fof(f1939,plain,
    ( ! [X0] : sP4(sK6,k4_subset_1(u1_struct_0(sK6),k1_xboole_0,k3_xboole_0(X0,u1_struct_0(sK6))),X0)
    | ~ spl14_10
    | ~ spl14_12
    | ~ spl14_30
    | ~ spl14_31 ),
    inference(forward_demodulation,[],[f1921,f999])).

fof(f999,plain,
    ( ! [X0] : k3_xboole_0(X0,u1_struct_0(sK6)) = k9_subset_1(u1_struct_0(sK6),u1_struct_0(sK6),X0)
    | ~ spl14_31 ),
    inference(forward_demodulation,[],[f971,f564])).

fof(f971,plain,
    ( ! [X0] : k9_subset_1(u1_struct_0(sK6),X0,u1_struct_0(sK6)) = k9_subset_1(u1_struct_0(sK6),u1_struct_0(sK6),X0)
    | ~ spl14_31 ),
    inference(unit_resulting_resolution,[],[f415,f107])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(f1921,plain,
    ( ! [X0] : sP4(sK6,k4_subset_1(u1_struct_0(sK6),k1_xboole_0,k9_subset_1(u1_struct_0(sK6),u1_struct_0(sK6),X0)),X0)
    | ~ spl14_10
    | ~ spl14_12
    | ~ spl14_30
    | ~ spl14_31 ),
    inference(unit_resulting_resolution,[],[f230,f410,f184,f415,f119])).

fof(f119,plain,(
    ! [X4,X2,X0,X3] :
      ( sP4(X0,k4_subset_1(u1_struct_0(X0),X3,k9_subset_1(u1_struct_0(X0),X4,X2)),X2)
      | ~ r2_hidden(X4,u1_pre_topc(X0))
      | ~ r2_hidden(X3,u1_pre_topc(X0))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(equality_resolution,[],[f115])).

fof(f115,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP4(X0,X1,X2)
      | ~ r2_hidden(X4,u1_pre_topc(X0))
      | ~ r2_hidden(X3,u1_pre_topc(X0))
      | k4_subset_1(u1_struct_0(X0),X3,k9_subset_1(u1_struct_0(X0),X4,X2)) != X1
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1,X2] :
      ( ( sP4(X0,X1,X2)
        | ! [X3,X4] :
            ( ~ r2_hidden(X4,u1_pre_topc(X0))
            | ~ r2_hidden(X3,u1_pre_topc(X0))
            | k4_subset_1(u1_struct_0(X0),X3,k9_subset_1(u1_struct_0(X0),X4,X2)) != X1
            | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ( r2_hidden(sK13(X0,X1,X2),u1_pre_topc(X0))
          & r2_hidden(sK12(X0,X1,X2),u1_pre_topc(X0))
          & k4_subset_1(u1_struct_0(X0),sK12(X0,X1,X2),k9_subset_1(u1_struct_0(X0),sK13(X0,X1,X2),X2)) = X1
          & m1_subset_1(sK13(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
          & m1_subset_1(sK12(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP4(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12,sK13])],[f69,f70])).

fof(f70,plain,(
    ! [X2,X1,X0] :
      ( ? [X5,X6] :
          ( r2_hidden(X6,u1_pre_topc(X0))
          & r2_hidden(X5,u1_pre_topc(X0))
          & k4_subset_1(u1_struct_0(X0),X5,k9_subset_1(u1_struct_0(X0),X6,X2)) = X1
          & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r2_hidden(sK13(X0,X1,X2),u1_pre_topc(X0))
        & r2_hidden(sK12(X0,X1,X2),u1_pre_topc(X0))
        & k4_subset_1(u1_struct_0(X0),sK12(X0,X1,X2),k9_subset_1(u1_struct_0(X0),sK13(X0,X1,X2),X2)) = X1
        & m1_subset_1(sK13(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
        & m1_subset_1(sK12(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f69,plain,(
    ! [X0,X1,X2] :
      ( ( sP4(X0,X1,X2)
        | ! [X3,X4] :
            ( ~ r2_hidden(X4,u1_pre_topc(X0))
            | ~ r2_hidden(X3,u1_pre_topc(X0))
            | k4_subset_1(u1_struct_0(X0),X3,k9_subset_1(u1_struct_0(X0),X4,X2)) != X1
            | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ? [X5,X6] :
            ( r2_hidden(X6,u1_pre_topc(X0))
            & r2_hidden(X5,u1_pre_topc(X0))
            & k4_subset_1(u1_struct_0(X0),X5,k9_subset_1(u1_struct_0(X0),X6,X2)) = X1
            & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
            & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP4(X0,X1,X2) ) ) ),
    inference(rectify,[],[f68])).

fof(f68,plain,(
    ! [X1,X0,X2] :
      ( ( sP4(X1,X0,X2)
        | ! [X3,X4] :
            ( ~ r2_hidden(X4,u1_pre_topc(X1))
            | ~ r2_hidden(X3,u1_pre_topc(X1))
            | k4_subset_1(u1_struct_0(X1),X3,k9_subset_1(u1_struct_0(X1),X4,X2)) != X0
            | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
      & ( ? [X3,X4] :
            ( r2_hidden(X4,u1_pre_topc(X1))
            & r2_hidden(X3,u1_pre_topc(X1))
            & k4_subset_1(u1_struct_0(X1),X3,k9_subset_1(u1_struct_0(X1),X4,X2)) = X0
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ sP4(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X1,X0,X2] :
      ( sP4(X1,X0,X2)
    <=> ? [X3,X4] :
          ( r2_hidden(X4,u1_pre_topc(X1))
          & r2_hidden(X3,u1_pre_topc(X1))
          & k4_subset_1(u1_struct_0(X1),X3,k9_subset_1(u1_struct_0(X1),X4,X2)) = X0
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f184,plain,
    ( r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK6))
    | ~ spl14_10 ),
    inference(avatar_component_clause,[],[f182])).

fof(f182,plain,
    ( spl14_10
  <=> r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_10])])).

fof(f230,plain,
    ( r2_hidden(k1_xboole_0,u1_pre_topc(sK6))
    | ~ spl14_12 ),
    inference(avatar_component_clause,[],[f228])).

fof(f228,plain,
    ( spl14_12
  <=> r2_hidden(k1_xboole_0,u1_pre_topc(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_12])])).

fof(f1248,plain,
    ( ! [X0] : sP5(sK7,X0,sK6)
    | ~ spl14_2
    | ~ spl14_3
    | ~ spl14_4
    | spl14_5 ),
    inference(unit_resulting_resolution,[],[f143,f138,f133,f128,f116])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | sP5(X2,X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( sP5(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(definition_folding,[],[f35,f46,f45])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_tmap_1(X1,X2))
      <=> ? [X3,X4] :
            ( r2_hidden(X4,u1_pre_topc(X1))
            & r2_hidden(X3,u1_pre_topc(X1))
            & k4_subset_1(u1_struct_0(X1),X3,k9_subset_1(u1_struct_0(X1),X4,X2)) = X0
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_tmap_1(X1,X2))
      <=> ? [X3,X4] :
            ( r2_hidden(X4,u1_pre_topc(X1))
            & r2_hidden(X3,u1_pre_topc(X1))
            & k4_subset_1(u1_struct_0(X1),X3,k9_subset_1(u1_struct_0(X1),X4,X2)) = X0
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_0_tmap_1(X1,X2))
      <=> ? [X3,X4] :
            ( r2_hidden(X4,u1_pre_topc(X1))
            & r2_hidden(X3,u1_pre_topc(X1))
            & k4_subset_1(u1_struct_0(X1),X3,k9_subset_1(u1_struct_0(X1),X4,X2)) = X0
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_0_tmap_1)).

fof(f128,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ spl14_2 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl14_2
  <=> m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_2])])).

fof(f133,plain,
    ( l1_pre_topc(sK6)
    | ~ spl14_3 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl14_3
  <=> l1_pre_topc(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_3])])).

fof(f138,plain,
    ( v2_pre_topc(sK6)
    | ~ spl14_4 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl14_4
  <=> v2_pre_topc(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_4])])).

fof(f143,plain,
    ( ~ v2_struct_0(sK6)
    | spl14_5 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl14_5
  <=> v2_struct_0(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_5])])).

fof(f1693,plain,
    ( spl14_98
    | ~ spl14_2
    | ~ spl14_3
    | ~ spl14_4
    | spl14_5 ),
    inference(avatar_split_clause,[],[f1674,f141,f136,f131,f126,f1690])).

fof(f1674,plain,
    ( k5_tmap_1(sK6,sK7) = a_2_0_tmap_1(sK6,sK7)
    | ~ spl14_2
    | ~ spl14_3
    | ~ spl14_4
    | spl14_5 ),
    inference(unit_resulting_resolution,[],[f143,f138,f133,f128,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( k5_tmap_1(X0,X1) = a_2_0_tmap_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k5_tmap_1(X0,X1) = a_2_0_tmap_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k5_tmap_1(X0,X1) = a_2_0_tmap_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k5_tmap_1(X0,X1) = a_2_0_tmap_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_tmap_1)).

fof(f416,plain,
    ( spl14_31
    | ~ spl14_10
    | ~ spl14_14 ),
    inference(avatar_split_clause,[],[f384,f248,f182,f413])).

fof(f248,plain,
    ( spl14_14
  <=> m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_14])])).

fof(f384,plain,
    ( m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ spl14_10
    | ~ spl14_14 ),
    inference(unit_resulting_resolution,[],[f184,f250,f117])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f250,plain,
    ( m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6))))
    | ~ spl14_14 ),
    inference(avatar_component_clause,[],[f248])).

fof(f411,plain,
    ( spl14_30
    | ~ spl14_12
    | ~ spl14_14 ),
    inference(avatar_split_clause,[],[f385,f248,f228,f408])).

fof(f385,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ spl14_12
    | ~ spl14_14 ),
    inference(unit_resulting_resolution,[],[f230,f250,f117])).

fof(f251,plain,
    ( spl14_14
    | ~ spl14_3 ),
    inference(avatar_split_clause,[],[f245,f131,f248])).

fof(f245,plain,
    ( m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6))))
    | ~ spl14_3 ),
    inference(unit_resulting_resolution,[],[f133,f79])).

fof(f79,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f244,plain,
    ( spl14_13
    | ~ spl14_11 ),
    inference(avatar_split_clause,[],[f232,f216,f241])).

fof(f216,plain,
    ( spl14_11
  <=> r1_tarski(sK7,u1_struct_0(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_11])])).

fof(f232,plain,
    ( sK7 = k3_xboole_0(sK7,u1_struct_0(sK6))
    | ~ spl14_11 ),
    inference(unit_resulting_resolution,[],[f218,f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f218,plain,
    ( r1_tarski(sK7,u1_struct_0(sK6))
    | ~ spl14_11 ),
    inference(avatar_component_clause,[],[f216])).

fof(f231,plain,
    ( spl14_12
    | ~ spl14_3
    | ~ spl14_4 ),
    inference(avatar_split_clause,[],[f226,f136,f131,f228])).

fof(f226,plain,
    ( r2_hidden(k1_xboole_0,u1_pre_topc(sK6))
    | ~ spl14_3
    | ~ spl14_4 ),
    inference(unit_resulting_resolution,[],[f138,f133,f98])).

fof(f98,plain,(
    ! [X0] :
      ( r2_hidden(k1_xboole_0,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( r2_hidden(k1_xboole_0,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( r2_hidden(k1_xboole_0,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => r2_hidden(k1_xboole_0,u1_pre_topc(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_pre_topc)).

fof(f220,plain,
    ( spl14_11
    | ~ spl14_2 ),
    inference(avatar_split_clause,[],[f213,f126,f216])).

fof(f213,plain,
    ( r1_tarski(sK7,u1_struct_0(sK6))
    | ~ spl14_2 ),
    inference(resolution,[],[f103,f128])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f185,plain,
    ( spl14_10
    | ~ spl14_7 ),
    inference(avatar_split_clause,[],[f180,f155,f182])).

fof(f155,plain,
    ( spl14_7
  <=> sP2(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_7])])).

fof(f180,plain,
    ( r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK6))
    | ~ spl14_7 ),
    inference(unit_resulting_resolution,[],[f157,f82])).

fof(f82,plain,(
    ! [X0] :
      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ sP2(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ( sP2(X0)
        | ~ sP1(X0)
        | ~ sP0(X0)
        | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
      & ( ( sP1(X0)
          & sP0(X0)
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        | ~ sP2(X0) ) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ( sP2(X0)
        | ~ sP1(X0)
        | ~ sP0(X0)
        | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
      & ( ( sP1(X0)
          & sP0(X0)
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        | ~ sP2(X0) ) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( sP2(X0)
    <=> ( sP1(X0)
        & sP0(X0)
        & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f157,plain,
    ( sP2(sK6)
    | ~ spl14_7 ),
    inference(avatar_component_clause,[],[f155])).

fof(f160,plain,
    ( spl14_7
    | ~ spl14_4
    | ~ spl14_6 ),
    inference(avatar_split_clause,[],[f159,f147,f136,f155])).

fof(f147,plain,
    ( spl14_6
  <=> sP3(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_6])])).

fof(f159,plain,
    ( sP2(sK6)
    | ~ spl14_4
    | ~ spl14_6 ),
    inference(subsumption_resolution,[],[f153,f138])).

fof(f153,plain,
    ( ~ v2_pre_topc(sK6)
    | sP2(sK6)
    | ~ spl14_6 ),
    inference(resolution,[],[f80,f149])).

fof(f149,plain,
    ( sP3(sK6)
    | ~ spl14_6 ),
    inference(avatar_component_clause,[],[f147])).

fof(f80,plain,(
    ! [X0] :
      ( ~ sP3(X0)
      | ~ v2_pre_topc(X0)
      | sP2(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ~ sP2(X0) )
        & ( sP2(X0)
          | ~ v2_pre_topc(X0) ) )
      | ~ sP3(X0) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> sP2(X0) )
      | ~ sP3(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f150,plain,
    ( spl14_6
    | ~ spl14_3 ),
    inference(avatar_split_clause,[],[f145,f131,f147])).

fof(f145,plain,
    ( sP3(sK6)
    | ~ spl14_3 ),
    inference(unit_resulting_resolution,[],[f133,f96])).

fof(f96,plain,(
    ! [X0] :
      ( sP3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( sP3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f25,f43,f42,f41,f40])).

fof(f40,plain,(
    ! [X0] :
      ( sP0(X0)
    <=> ! [X3] :
          ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
          | ~ r1_tarski(X3,u1_pre_topc(X0))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f41,plain,(
    ! [X0] :
      ( sP1(X0)
    <=> ! [X1] :
          ( ! [X2] :
              ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
              | ~ r2_hidden(X2,u1_pre_topc(X0))
              | ~ r2_hidden(X1,u1_pre_topc(X0))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f25,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X0))
                      & r2_hidden(X1,u1_pre_topc(X0)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) ) ) )
          & ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( r1_tarski(X3,u1_pre_topc(X0))
               => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) ) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X0))
                      & r2_hidden(X1,u1_pre_topc(X0)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) ) ) )
          & ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( r1_tarski(X1,u1_pre_topc(X0))
               => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) ) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_pre_topc)).

fof(f144,plain,(
    ~ spl14_5 ),
    inference(avatar_split_clause,[],[f72,f141])).

fof(f72,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,
    ( ~ r2_hidden(sK7,k5_tmap_1(sK6,sK7))
    & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    & l1_pre_topc(sK6)
    & v2_pre_topc(sK6)
    & ~ v2_struct_0(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f22,f49,f48])).

fof(f48,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r2_hidden(X1,k5_tmap_1(X0,X1))
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ r2_hidden(X1,k5_tmap_1(sK6,X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) )
      & l1_pre_topc(sK6)
      & v2_pre_topc(sK6)
      & ~ v2_struct_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ? [X1] :
        ( ~ r2_hidden(X1,k5_tmap_1(sK6,X1))
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) )
   => ( ~ r2_hidden(sK7,k5_tmap_1(sK6,sK7))
      & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(X1,k5_tmap_1(X0,X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(X1,k5_tmap_1(X0,X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => r2_hidden(X1,k5_tmap_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r2_hidden(X1,k5_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_tmap_1)).

fof(f139,plain,(
    spl14_4 ),
    inference(avatar_split_clause,[],[f73,f136])).

fof(f73,plain,(
    v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f50])).

fof(f134,plain,(
    spl14_3 ),
    inference(avatar_split_clause,[],[f74,f131])).

fof(f74,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f50])).

fof(f129,plain,(
    spl14_2 ),
    inference(avatar_split_clause,[],[f75,f126])).

fof(f75,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f50])).

fof(f124,plain,(
    ~ spl14_1 ),
    inference(avatar_split_clause,[],[f76,f121])).

fof(f76,plain,(
    ~ r2_hidden(sK7,k5_tmap_1(sK6,sK7)) ),
    inference(cnf_transformation,[],[f50])).

%------------------------------------------------------------------------------
