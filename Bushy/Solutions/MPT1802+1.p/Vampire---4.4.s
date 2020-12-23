%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tmap_1__t118_tmap_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:04 EDT 2019

% Result     : Theorem 7.30s
% Output     : Refutation 7.37s
% Verified   : 
% Statistics : Number of formulae       :  369 (1521 expanded)
%              Number of leaves         :   69 ( 600 expanded)
%              Depth                    :   29
%              Number of atoms          : 1538 (11596 expanded)
%              Number of equality atoms :  146 ( 378 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f196416,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f497,f501,f1201,f1203,f1407,f8004,f8056,f8059,f9199,f9205,f9664,f9680,f10737,f10741,f10742,f10743,f10751,f10979,f11143,f11413,f196243])).

fof(f196243,plain,
    ( ~ spl15_78
    | ~ spl15_128
    | ~ spl15_1080
    | ~ spl15_1216
    | ~ spl15_1220 ),
    inference(avatar_contradiction_clause,[],[f196242])).

fof(f196242,plain,
    ( $false
    | ~ spl15_78
    | ~ spl15_128
    | ~ spl15_1080
    | ~ spl15_1216
    | ~ spl15_1220 ),
    inference(subsumption_resolution,[],[f196203,f229])).

fof(f229,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f188])).

fof(f188,plain,
    ( ~ r1_tmap_1(sK2,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),sK3)
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & r1_tsep_1(sK1,sK2)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f89,f187,f186,f185,f184])).

fof(f184,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3)
                    & m1_subset_1(X3,u1_struct_0(X2)) )
                & r1_tsep_1(X1,X2)
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tmap_1(X2,k8_tmap_1(sK0,X1),k2_tmap_1(sK0,k8_tmap_1(sK0,X1),k9_tmap_1(sK0,X1),X2),X3)
                  & m1_subset_1(X3,u1_struct_0(X2)) )
              & r1_tsep_1(X1,X2)
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f185,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3)
                  & m1_subset_1(X3,u1_struct_0(X2)) )
              & r1_tsep_1(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ~ r1_tmap_1(X2,k8_tmap_1(X0,sK1),k2_tmap_1(X0,k8_tmap_1(X0,sK1),k9_tmap_1(X0,sK1),X2),X3)
                & m1_subset_1(X3,u1_struct_0(X2)) )
            & r1_tsep_1(sK1,X2)
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(sK1,X0)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f186,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3)
              & m1_subset_1(X3,u1_struct_0(X2)) )
          & r1_tsep_1(X1,X2)
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ~ r1_tmap_1(sK2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),sK2),X3)
            & m1_subset_1(X3,u1_struct_0(sK2)) )
        & r1_tsep_1(X1,sK2)
        & m1_pre_topc(sK2,X0)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f187,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3)
          & m1_subset_1(X3,u1_struct_0(X2)) )
     => ( ~ r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),sK3)
        & m1_subset_1(sK3,u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f89,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3)
                  & m1_subset_1(X3,u1_struct_0(X2)) )
              & r1_tsep_1(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f88])).

fof(f88,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3)
                  & m1_subset_1(X3,u1_struct_0(X2)) )
              & r1_tsep_1(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ( r1_tsep_1(X1,X2)
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X2))
                     => r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( r1_tsep_1(X1,X2)
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X2))
                   => r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t118_tmap_1.p',t118_tmap_1)).

fof(f196203,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ spl15_78
    | ~ spl15_128
    | ~ spl15_1080
    | ~ spl15_1216
    | ~ spl15_1220 ),
    inference(resolution,[],[f33268,f230])).

fof(f230,plain,(
    ~ r1_tmap_1(sK2,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),sK3) ),
    inference(cnf_transformation,[],[f188])).

fof(f33268,plain,
    ( ! [X1] :
        ( r1_tmap_1(sK2,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK2)) )
    | ~ spl15_78
    | ~ spl15_128
    | ~ spl15_1080
    | ~ spl15_1216
    | ~ spl15_1220 ),
    inference(subsumption_resolution,[],[f33267,f226])).

fof(f226,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f188])).

fof(f33267,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK2))
        | r1_tmap_1(sK2,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),X1)
        | v2_struct_0(sK2) )
    | ~ spl15_78
    | ~ spl15_128
    | ~ spl15_1080
    | ~ spl15_1216
    | ~ spl15_1220 ),
    inference(subsumption_resolution,[],[f33264,f11520])).

fof(f11520,plain,
    ( r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ spl15_78
    | ~ spl15_1216
    | ~ spl15_1220 ),
    inference(subsumption_resolution,[],[f11515,f1110])).

fof(f1110,plain,
    ( l1_struct_0(sK1)
    | ~ spl15_78 ),
    inference(avatar_component_clause,[],[f1109])).

fof(f1109,plain,
    ( spl15_78
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_78])])).

fof(f11515,plain,
    ( ~ l1_struct_0(sK1)
    | r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ spl15_1216
    | ~ spl15_1220 ),
    inference(resolution,[],[f10978,f10990])).

fof(f10990,plain,
    ( r1_tsep_1(k6_tmap_1(sK2,o_0_0_xboole_0),sK1)
    | ~ spl15_1220 ),
    inference(avatar_component_clause,[],[f10989])).

fof(f10989,plain,
    ( spl15_1220
  <=> r1_tsep_1(k6_tmap_1(sK2,o_0_0_xboole_0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1220])])).

fof(f10978,plain,
    ( ! [X0] :
        ( ~ r1_tsep_1(k6_tmap_1(sK2,o_0_0_xboole_0),X0)
        | ~ l1_struct_0(X0)
        | r1_xboole_0(u1_struct_0(sK2),u1_struct_0(X0)) )
    | ~ spl15_1216 ),
    inference(avatar_component_clause,[],[f10977])).

fof(f10977,plain,
    ( spl15_1216
  <=> ! [X0] :
        ( r1_xboole_0(u1_struct_0(sK2),u1_struct_0(X0))
        | ~ l1_struct_0(X0)
        | ~ r1_tsep_1(k6_tmap_1(sK2,o_0_0_xboole_0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1216])])).

fof(f33264,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK2))
        | ~ r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK1))
        | r1_tmap_1(sK2,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),X1)
        | v2_struct_0(sK2) )
    | ~ spl15_128
    | ~ spl15_1080 ),
    inference(resolution,[],[f32386,f227])).

fof(f227,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f188])).

fof(f32386,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK1))
        | r1_tmap_1(X0,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),X0),X1)
        | v2_struct_0(X0) )
    | ~ spl15_128
    | ~ spl15_1080 ),
    inference(forward_demodulation,[],[f6760,f9198])).

fof(f9198,plain,
    ( k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl15_1080 ),
    inference(avatar_component_clause,[],[f9197])).

fof(f9197,plain,
    ( spl15_1080
  <=> k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1080])])).

fof(f6760,plain,
    ( ! [X0,X1] :
        ( r1_tmap_1(X0,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X0),X1)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0) )
    | ~ spl15_128 ),
    inference(subsumption_resolution,[],[f6759,f221])).

fof(f221,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f188])).

fof(f6759,plain,
    ( ! [X0,X1] :
        ( r1_tmap_1(X0,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X0),X1)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | v2_struct_0(sK0) )
    | ~ spl15_128 ),
    inference(subsumption_resolution,[],[f6758,f222])).

fof(f222,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f188])).

fof(f6758,plain,
    ( ! [X0,X1] :
        ( r1_tmap_1(X0,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X0),X1)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl15_128 ),
    inference(subsumption_resolution,[],[f6757,f223])).

fof(f223,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f188])).

fof(f6757,plain,
    ( ! [X0,X1] :
        ( r1_tmap_1(X0,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X0),X1)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl15_128 ),
    inference(subsumption_resolution,[],[f6755,f1359])).

fof(f1359,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_128 ),
    inference(avatar_component_clause,[],[f1358])).

fof(f1358,plain,
    ( spl15_128
  <=> m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_128])])).

fof(f6755,plain,(
    ! [X0,X1] :
      ( r1_tmap_1(X0,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X0),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK1))
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f259,f5816])).

fof(f5816,plain,(
    k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f5815,f223])).

fof(f5815,plain,
    ( k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f5814,f222])).

fof(f5814,plain,
    ( ~ v2_pre_topc(sK0)
    | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f5810,f221])).

fof(f5810,plain,
    ( v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f5734,f225])).

fof(f225,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f188])).

fof(f5734,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f5733,f289])).

fof(f289,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f129])).

fof(f129,plain,(
    ! [X0,X1] :
      ( ( v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1))
        & ~ v2_struct_0(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f128])).

fof(f128,plain,(
    ! [X0,X1] :
      ( ( v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1))
        & ~ v2_struct_0(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f85])).

fof(f85,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1))
        & ~ v2_struct_0(k8_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t118_tmap_1.p',fc5_tmap_1)).

fof(f5733,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ v1_pre_topc(k8_tmap_1(X0,X1))
      | k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0) ) ),
    inference(subsumption_resolution,[],[f5732,f293])).

fof(f293,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f131])).

fof(f131,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f130])).

fof(f130,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t118_tmap_1.p',dt_k8_tmap_1)).

fof(f5732,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ v1_pre_topc(k8_tmap_1(X0,X1))
      | k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0) ) ),
    inference(subsumption_resolution,[],[f359,f290])).

fof(f290,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f129])).

fof(f359,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ v1_pre_topc(k8_tmap_1(X0,X1))
      | k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0) ) ),
    inference(global_subsumption,[],[f244,f351])).

fof(f351,plain,(
    ! [X0,X1] :
      ( k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f350])).

fof(f350,plain,(
    ! [X2,X0,X1] :
      ( k6_tmap_1(X0,u1_struct_0(X1)) = X2
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | k8_tmap_1(X0,X1) != X2
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f250])).

fof(f250,plain,(
    ! [X4,X2,X0,X1] :
      ( k6_tmap_1(X0,X4) = X2
      | u1_struct_0(X1) != X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | k8_tmap_1(X0,X1) != X2
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f196])).

fof(f196,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k8_tmap_1(X0,X1) = X2
                  | ( k6_tmap_1(X0,sK5(X0,X1,X2)) != X2
                    & u1_struct_0(X1) = sK5(X0,X1,X2)
                    & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( k6_tmap_1(X0,X4) = X2
                      | u1_struct_0(X1) != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k8_tmap_1(X0,X1) != X2 ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f194,f195])).

fof(f195,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k6_tmap_1(X0,X3) != X2
          & u1_struct_0(X1) = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k6_tmap_1(X0,sK5(X0,X1,X2)) != X2
        & u1_struct_0(X1) = sK5(X0,X1,X2)
        & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f194,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k8_tmap_1(X0,X1) = X2
                  | ? [X3] :
                      ( k6_tmap_1(X0,X3) != X2
                      & u1_struct_0(X1) = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( k6_tmap_1(X0,X4) = X2
                      | u1_struct_0(X1) != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k8_tmap_1(X0,X1) != X2 ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f193])).

fof(f193,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k8_tmap_1(X0,X1) = X2
                  | ? [X3] :
                      ( k6_tmap_1(X0,X3) != X2
                      & u1_struct_0(X1) = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X3] :
                      ( k6_tmap_1(X0,X3) = X2
                      | u1_struct_0(X1) != X3
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k8_tmap_1(X0,X1) != X2 ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f103])).

fof(f103,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k8_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( k6_tmap_1(X0,X3) = X2
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f102])).

fof(f102,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k8_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( k6_tmap_1(X0,X3) = X2
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2)
                & v1_pre_topc(X2) )
             => ( k8_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( u1_struct_0(X1) = X3
                     => k6_tmap_1(X0,X3) = X2 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t118_tmap_1.p',d11_tmap_1)).

fof(f244,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f96])).

fof(f96,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f69])).

fof(f69,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t118_tmap_1.p',t1_tsep_1)).

fof(f259,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ r1_xboole_0(u1_struct_0(X2),X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f109])).

fof(f109,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X2)) )
              | ~ r1_xboole_0(u1_struct_0(X2),X1)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f108])).

fof(f108,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X2)) )
              | ~ r1_xboole_0(u1_struct_0(X2),X1)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f65])).

fof(f65,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( r1_xboole_0(u1_struct_0(X2),X1)
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X2))
                   => r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t118_tmap_1.p',t109_tmap_1)).

fof(f11413,plain,
    ( ~ spl15_78
    | ~ spl15_954
    | ~ spl15_1130
    | ~ spl15_1200
    | ~ spl15_1214
    | spl15_1221 ),
    inference(avatar_contradiction_clause,[],[f11412])).

fof(f11412,plain,
    ( $false
    | ~ spl15_78
    | ~ spl15_954
    | ~ spl15_1130
    | ~ spl15_1200
    | ~ spl15_1214
    | ~ spl15_1221 ),
    inference(subsumption_resolution,[],[f11411,f1110])).

fof(f11411,plain,
    ( ~ l1_struct_0(sK1)
    | ~ spl15_78
    | ~ spl15_954
    | ~ spl15_1130
    | ~ spl15_1200
    | ~ spl15_1214
    | ~ spl15_1221 ),
    inference(subsumption_resolution,[],[f11410,f8046])).

fof(f8046,plain,
    ( l1_struct_0(sK2)
    | ~ spl15_954 ),
    inference(avatar_component_clause,[],[f8045])).

fof(f8045,plain,
    ( spl15_954
  <=> l1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_954])])).

fof(f11410,plain,
    ( ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK1)
    | ~ spl15_78
    | ~ spl15_954
    | ~ spl15_1130
    | ~ spl15_1200
    | ~ spl15_1214
    | ~ spl15_1221 ),
    inference(subsumption_resolution,[],[f11409,f228])).

fof(f228,plain,(
    r1_tsep_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f188])).

fof(f11409,plain,
    ( ~ r1_tsep_1(sK1,sK2)
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK1)
    | ~ spl15_78
    | ~ spl15_954
    | ~ spl15_1130
    | ~ spl15_1200
    | ~ spl15_1214
    | ~ spl15_1221 ),
    inference(resolution,[],[f11407,f307])).

fof(f307,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f143])).

fof(f143,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f142])).

fof(f142,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f63])).

fof(f63,axiom,(
    ! [X0,X1] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( r1_tsep_1(X0,X1)
       => r1_tsep_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t118_tmap_1.p',symmetry_r1_tsep_1)).

fof(f11407,plain,
    ( ~ r1_tsep_1(sK2,sK1)
    | ~ spl15_78
    | ~ spl15_954
    | ~ spl15_1130
    | ~ spl15_1200
    | ~ spl15_1214
    | ~ spl15_1221 ),
    inference(subsumption_resolution,[],[f11406,f8046])).

fof(f11406,plain,
    ( ~ r1_tsep_1(sK2,sK1)
    | ~ l1_struct_0(sK2)
    | ~ spl15_78
    | ~ spl15_1130
    | ~ spl15_1200
    | ~ spl15_1214
    | ~ spl15_1221 ),
    inference(subsumption_resolution,[],[f11404,f1110])).

fof(f11404,plain,
    ( ~ r1_tsep_1(sK2,sK1)
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK2)
    | ~ spl15_78
    | ~ spl15_1130
    | ~ spl15_1200
    | ~ spl15_1214
    | ~ spl15_1221 ),
    inference(resolution,[],[f11151,f238])).

fof(f238,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f189])).

fof(f189,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_tsep_1(X0,X1)
              | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
            & ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
              | ~ r1_tsep_1(X0,X1) ) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f90])).

fof(f90,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t118_tmap_1.p',d3_tsep_1)).

fof(f11151,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ spl15_78
    | ~ spl15_1130
    | ~ spl15_1200
    | ~ spl15_1214
    | ~ spl15_1221 ),
    inference(forward_demodulation,[],[f11150,f10920])).

fof(f10920,plain,
    ( u1_struct_0(sK2) = u1_struct_0(k6_tmap_1(sK2,o_0_0_xboole_0))
    | ~ spl15_1130
    | ~ spl15_1200 ),
    inference(trivial_inequality_removal,[],[f10917])).

fof(f10917,plain,
    ( k6_tmap_1(sK2,o_0_0_xboole_0) != k6_tmap_1(sK2,o_0_0_xboole_0)
    | u1_struct_0(sK2) = u1_struct_0(k6_tmap_1(sK2,o_0_0_xboole_0))
    | ~ spl15_1130
    | ~ spl15_1200 ),
    inference(superposition,[],[f9738,f10750])).

fof(f10750,plain,
    ( g1_pre_topc(u1_struct_0(k6_tmap_1(sK2,o_0_0_xboole_0)),u1_pre_topc(k6_tmap_1(sK2,o_0_0_xboole_0))) = k6_tmap_1(sK2,o_0_0_xboole_0)
    | ~ spl15_1200 ),
    inference(avatar_component_clause,[],[f10749])).

fof(f10749,plain,
    ( spl15_1200
  <=> g1_pre_topc(u1_struct_0(k6_tmap_1(sK2,o_0_0_xboole_0)),u1_pre_topc(k6_tmap_1(sK2,o_0_0_xboole_0))) = k6_tmap_1(sK2,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1200])])).

fof(f9738,plain,
    ( ! [X0,X1] :
        ( g1_pre_topc(X0,X1) != k6_tmap_1(sK2,o_0_0_xboole_0)
        | u1_struct_0(sK2) = X0 )
    | ~ spl15_1130 ),
    inference(avatar_component_clause,[],[f9737])).

fof(f9737,plain,
    ( spl15_1130
  <=> ! [X1,X0] :
        ( g1_pre_topc(X0,X1) != k6_tmap_1(sK2,o_0_0_xboole_0)
        | u1_struct_0(sK2) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1130])])).

fof(f11150,plain,
    ( ~ r1_xboole_0(u1_struct_0(k6_tmap_1(sK2,o_0_0_xboole_0)),u1_struct_0(sK1))
    | ~ spl15_78
    | ~ spl15_1214
    | ~ spl15_1221 ),
    inference(subsumption_resolution,[],[f11149,f10972])).

fof(f10972,plain,
    ( l1_struct_0(k6_tmap_1(sK2,o_0_0_xboole_0))
    | ~ spl15_1214 ),
    inference(avatar_component_clause,[],[f10971])).

fof(f10971,plain,
    ( spl15_1214
  <=> l1_struct_0(k6_tmap_1(sK2,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1214])])).

fof(f11149,plain,
    ( ~ r1_xboole_0(u1_struct_0(k6_tmap_1(sK2,o_0_0_xboole_0)),u1_struct_0(sK1))
    | ~ l1_struct_0(k6_tmap_1(sK2,o_0_0_xboole_0))
    | ~ spl15_78
    | ~ spl15_1221 ),
    inference(subsumption_resolution,[],[f11147,f1110])).

fof(f11147,plain,
    ( ~ r1_xboole_0(u1_struct_0(k6_tmap_1(sK2,o_0_0_xboole_0)),u1_struct_0(sK1))
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(k6_tmap_1(sK2,o_0_0_xboole_0))
    | ~ spl15_1221 ),
    inference(resolution,[],[f10993,f239])).

fof(f239,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X0,X1)
      | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f189])).

fof(f10993,plain,
    ( ~ r1_tsep_1(k6_tmap_1(sK2,o_0_0_xboole_0),sK1)
    | ~ spl15_1221 ),
    inference(avatar_component_clause,[],[f10992])).

fof(f10992,plain,
    ( spl15_1221
  <=> ~ r1_tsep_1(k6_tmap_1(sK2,o_0_0_xboole_0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1221])])).

fof(f11143,plain,
    ( ~ spl15_1128
    | spl15_1215 ),
    inference(avatar_contradiction_clause,[],[f11142])).

fof(f11142,plain,
    ( $false
    | ~ spl15_1128
    | ~ spl15_1215 ),
    inference(subsumption_resolution,[],[f11141,f9734])).

fof(f9734,plain,
    ( l1_pre_topc(k6_tmap_1(sK2,o_0_0_xboole_0))
    | ~ spl15_1128 ),
    inference(avatar_component_clause,[],[f9733])).

fof(f9733,plain,
    ( spl15_1128
  <=> l1_pre_topc(k6_tmap_1(sK2,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1128])])).

fof(f11141,plain,
    ( ~ l1_pre_topc(k6_tmap_1(sK2,o_0_0_xboole_0))
    | ~ spl15_1215 ),
    inference(resolution,[],[f10975,f240])).

fof(f240,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f91])).

fof(f91,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t118_tmap_1.p',dt_l1_pre_topc)).

fof(f10975,plain,
    ( ~ l1_struct_0(k6_tmap_1(sK2,o_0_0_xboole_0))
    | ~ spl15_1215 ),
    inference(avatar_component_clause,[],[f10974])).

fof(f10974,plain,
    ( spl15_1215
  <=> ~ l1_struct_0(k6_tmap_1(sK2,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1215])])).

fof(f10979,plain,
    ( ~ spl15_1215
    | spl15_1216
    | ~ spl15_1130
    | ~ spl15_1200 ),
    inference(avatar_split_clause,[],[f10936,f10749,f9737,f10977,f10974])).

fof(f10936,plain,
    ( ! [X0] :
        ( r1_xboole_0(u1_struct_0(sK2),u1_struct_0(X0))
        | ~ r1_tsep_1(k6_tmap_1(sK2,o_0_0_xboole_0),X0)
        | ~ l1_struct_0(X0)
        | ~ l1_struct_0(k6_tmap_1(sK2,o_0_0_xboole_0)) )
    | ~ spl15_1130
    | ~ spl15_1200 ),
    inference(superposition,[],[f238,f10920])).

fof(f10751,plain,
    ( ~ spl15_1129
    | spl15_1200
    | ~ spl15_1126 ),
    inference(avatar_split_clause,[],[f10744,f9726,f10749,f9730])).

fof(f9730,plain,
    ( spl15_1129
  <=> ~ l1_pre_topc(k6_tmap_1(sK2,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1129])])).

fof(f9726,plain,
    ( spl15_1126
  <=> v1_pre_topc(k6_tmap_1(sK2,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1126])])).

fof(f10744,plain,
    ( g1_pre_topc(u1_struct_0(k6_tmap_1(sK2,o_0_0_xboole_0)),u1_pre_topc(k6_tmap_1(sK2,o_0_0_xboole_0))) = k6_tmap_1(sK2,o_0_0_xboole_0)
    | ~ l1_pre_topc(k6_tmap_1(sK2,o_0_0_xboole_0))
    | ~ spl15_1126 ),
    inference(resolution,[],[f9727,f242])).

fof(f242,plain,(
    ! [X0] :
      ( ~ v1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f94])).

fof(f94,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f93])).

fof(f93,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t118_tmap_1.p',abstractness_v1_pre_topc)).

fof(f9727,plain,
    ( v1_pre_topc(k6_tmap_1(sK2,o_0_0_xboole_0))
    | ~ spl15_1126 ),
    inference(avatar_component_clause,[],[f9726])).

fof(f10743,plain,
    ( ~ spl15_1125
    | spl15_1126
    | ~ spl15_1122 ),
    inference(avatar_split_clause,[],[f10484,f9662,f9726,f9720])).

fof(f9720,plain,
    ( spl15_1125
  <=> ~ m1_subset_1(k5_tmap_1(sK2,o_0_0_xboole_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1125])])).

fof(f9662,plain,
    ( spl15_1122
  <=> g1_pre_topc(u1_struct_0(sK2),k5_tmap_1(sK2,o_0_0_xboole_0)) = k6_tmap_1(sK2,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1122])])).

fof(f10484,plain,
    ( v1_pre_topc(k6_tmap_1(sK2,o_0_0_xboole_0))
    | ~ m1_subset_1(k5_tmap_1(sK2,o_0_0_xboole_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ spl15_1122 ),
    inference(superposition,[],[f284,f9663])).

fof(f9663,plain,
    ( g1_pre_topc(u1_struct_0(sK2),k5_tmap_1(sK2,o_0_0_xboole_0)) = k6_tmap_1(sK2,o_0_0_xboole_0)
    | ~ spl15_1122 ),
    inference(avatar_component_clause,[],[f9662])).

fof(f284,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f126])).

fof(f126,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t118_tmap_1.p',dt_g1_pre_topc)).

fof(f10742,plain,
    ( ~ spl15_1125
    | spl15_1128
    | ~ spl15_1122 ),
    inference(avatar_split_clause,[],[f10485,f9662,f9733,f9720])).

fof(f10485,plain,
    ( l1_pre_topc(k6_tmap_1(sK2,o_0_0_xboole_0))
    | ~ m1_subset_1(k5_tmap_1(sK2,o_0_0_xboole_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ spl15_1122 ),
    inference(superposition,[],[f285,f9663])).

fof(f285,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f126])).

fof(f10741,plain,
    ( ~ spl15_1125
    | spl15_1130
    | ~ spl15_1122 ),
    inference(avatar_split_clause,[],[f10486,f9662,f9737,f9720])).

fof(f10486,plain,
    ( ! [X0,X1] :
        ( g1_pre_topc(X0,X1) != k6_tmap_1(sK2,o_0_0_xboole_0)
        | u1_struct_0(sK2) = X0
        | ~ m1_subset_1(k5_tmap_1(sK2,o_0_0_xboole_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) )
    | ~ spl15_1122 ),
    inference(superposition,[],[f286,f9663])).

fof(f286,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X0 = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f127])).

fof(f127,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f49])).

fof(f49,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t118_tmap_1.p',free_g1_pre_topc)).

fof(f10737,plain,
    ( ~ spl15_12
    | ~ spl15_942
    | spl15_1125 ),
    inference(avatar_contradiction_clause,[],[f10736])).

fof(f10736,plain,
    ( $false
    | ~ spl15_12
    | ~ spl15_942
    | ~ spl15_1125 ),
    inference(resolution,[],[f10722,f272])).

fof(f272,plain,(
    ! [X0] : m1_subset_1(sK9(X0),X0) ),
    inference(cnf_transformation,[],[f207])).

fof(f207,plain,(
    ! [X0] : m1_subset_1(sK9(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f47,f206])).

fof(f206,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK9(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f47,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t118_tmap_1.p',existence_m1_subset_1)).

fof(f10722,plain,
    ( ! [X0] : ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl15_12
    | ~ spl15_942
    | ~ spl15_1125 ),
    inference(resolution,[],[f10714,f407])).

fof(f407,plain,(
    ! [X10,X11] :
      ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(X11))
      | ~ m1_subset_1(X10,k1_zfmisc_1(X11)) ) ),
    inference(superposition,[],[f400,f367])).

fof(f367,plain,(
    ! [X1] : k3_xboole_0(o_0_0_xboole_0,X1) = o_0_0_xboole_0 ),
    inference(superposition,[],[f275,f364])).

fof(f364,plain,(
    ! [X0] : k3_xboole_0(X0,o_0_0_xboole_0) = o_0_0_xboole_0 ),
    inference(backward_demodulation,[],[f362,f235])).

fof(f235,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f70])).

fof(f70,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t118_tmap_1.p',t2_boole)).

fof(f362,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[],[f248,f231])).

fof(f231,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t118_tmap_1.p',dt_o_0_0_xboole_0)).

fof(f248,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f99])).

fof(f99,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f77])).

fof(f77,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t118_tmap_1.p',t6_boole)).

fof(f275,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t118_tmap_1.p',commutativity_k3_xboole_0)).

fof(f400,plain,(
    ! [X4,X5,X3] :
      ( m1_subset_1(k3_xboole_0(X4,X5),k1_zfmisc_1(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X3)) ) ),
    inference(duplicate_literal_removal,[],[f399])).

fof(f399,plain,(
    ! [X4,X5,X3] :
      ( m1_subset_1(k3_xboole_0(X4,X5),k1_zfmisc_1(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X3)) ) ),
    inference(superposition,[],[f315,f316])).

fof(f316,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f149])).

fof(f149,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f59])).

fof(f59,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t118_tmap_1.p',redefinition_k9_subset_1)).

fof(f315,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f148])).

fof(f148,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t118_tmap_1.p',dt_k9_subset_1)).

fof(f10714,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl15_12
    | ~ spl15_942
    | ~ spl15_1125 ),
    inference(resolution,[],[f8016,f9721])).

fof(f9721,plain,
    ( ~ m1_subset_1(k5_tmap_1(sK2,o_0_0_xboole_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ spl15_1125 ),
    inference(avatar_component_clause,[],[f9720])).

fof(f8016,plain,
    ( ! [X3] :
        ( m1_subset_1(k5_tmap_1(sK2,X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
    | ~ spl15_12
    | ~ spl15_942 ),
    inference(subsumption_resolution,[],[f8015,f226])).

fof(f8015,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))
        | m1_subset_1(k5_tmap_1(sK2,X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
        | v2_struct_0(sK2) )
    | ~ spl15_12
    | ~ spl15_942 ),
    inference(subsumption_resolution,[],[f8008,f487])).

fof(f487,plain,
    ( l1_pre_topc(sK2)
    | ~ spl15_12 ),
    inference(avatar_component_clause,[],[f486])).

fof(f486,plain,
    ( spl15_12
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_12])])).

fof(f8008,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ l1_pre_topc(sK2)
        | m1_subset_1(k5_tmap_1(sK2,X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
        | v2_struct_0(sK2) )
    | ~ spl15_942 ),
    inference(resolution,[],[f7971,f297])).

fof(f297,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | m1_subset_1(k5_tmap_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f135])).

fof(f135,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_tmap_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f134])).

fof(f134,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_tmap_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_tmap_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t118_tmap_1.p',dt_k5_tmap_1)).

fof(f7971,plain,
    ( v2_pre_topc(sK2)
    | ~ spl15_942 ),
    inference(avatar_component_clause,[],[f7970])).

fof(f7970,plain,
    ( spl15_942
  <=> v2_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_942])])).

fof(f9680,plain,(
    ~ spl15_1120 ),
    inference(avatar_contradiction_clause,[],[f9679])).

fof(f9679,plain,
    ( $false
    | ~ spl15_1120 ),
    inference(resolution,[],[f9657,f272])).

fof(f9657,plain,
    ( ! [X15] : ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl15_1120 ),
    inference(avatar_component_clause,[],[f9656])).

fof(f9656,plain,
    ( spl15_1120
  <=> ! [X15] : ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1120])])).

fof(f9664,plain,
    ( spl15_1120
    | spl15_1122
    | ~ spl15_12
    | ~ spl15_942 ),
    inference(avatar_split_clause,[],[f9652,f7970,f486,f9662,f9656])).

fof(f9652,plain,
    ( ! [X15] :
        ( g1_pre_topc(u1_struct_0(sK2),k5_tmap_1(sK2,o_0_0_xboole_0)) = k6_tmap_1(sK2,o_0_0_xboole_0)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(sK2))) )
    | ~ spl15_12
    | ~ spl15_942 ),
    inference(resolution,[],[f8014,f407])).

fof(f8014,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
        | g1_pre_topc(u1_struct_0(sK2),k5_tmap_1(sK2,X2)) = k6_tmap_1(sK2,X2) )
    | ~ spl15_12
    | ~ spl15_942 ),
    inference(subsumption_resolution,[],[f8013,f226])).

fof(f8013,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
        | g1_pre_topc(u1_struct_0(sK2),k5_tmap_1(sK2,X2)) = k6_tmap_1(sK2,X2)
        | v2_struct_0(sK2) )
    | ~ spl15_12
    | ~ spl15_942 ),
    inference(subsumption_resolution,[],[f8007,f487])).

fof(f8007,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ l1_pre_topc(sK2)
        | g1_pre_topc(u1_struct_0(sK2),k5_tmap_1(sK2,X2)) = k6_tmap_1(sK2,X2)
        | v2_struct_0(sK2) )
    | ~ spl15_942 ),
    inference(resolution,[],[f7971,f258])).

fof(f258,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) = k6_tmap_1(X0,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f107])).

fof(f107,plain,(
    ! [X0] :
      ( ! [X1] :
          ( g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) = k6_tmap_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f106])).

fof(f106,plain,(
    ! [X0] :
      ( ! [X1] :
          ( g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) = k6_tmap_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) = k6_tmap_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t118_tmap_1.p',d9_tmap_1)).

fof(f9205,plain,
    ( ~ spl15_128
    | spl15_1079 ),
    inference(avatar_contradiction_clause,[],[f9204])).

fof(f9204,plain,
    ( $false
    | ~ spl15_128
    | ~ spl15_1079 ),
    inference(subsumption_resolution,[],[f9203,f221])).

fof(f9203,plain,
    ( v2_struct_0(sK0)
    | ~ spl15_128
    | ~ spl15_1079 ),
    inference(subsumption_resolution,[],[f9202,f222])).

fof(f9202,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_128
    | ~ spl15_1079 ),
    inference(subsumption_resolution,[],[f9201,f223])).

fof(f9201,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_128
    | ~ spl15_1079 ),
    inference(subsumption_resolution,[],[f9200,f1359])).

fof(f9200,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_1079 ),
    inference(resolution,[],[f9192,f304])).

fof(f304,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f141])).

fof(f141,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f140])).

fof(f140,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t118_tmap_1.p',dt_k7_tmap_1)).

fof(f9192,plain,
    ( ~ v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ spl15_1079 ),
    inference(avatar_component_clause,[],[f9191])).

fof(f9191,plain,
    ( spl15_1079
  <=> ~ v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1079])])).

fof(f9199,plain,
    ( ~ spl15_1079
    | spl15_1080
    | ~ spl15_14
    | ~ spl15_128
    | ~ spl15_952 ),
    inference(avatar_split_clause,[],[f9186,f8039,f1358,f495,f9197,f9191])).

fof(f495,plain,
    ( spl15_14
  <=> r2_hidden(sK3,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_14])])).

fof(f8039,plain,
    ( spl15_952
  <=> v1_funct_1(k9_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_952])])).

fof(f9186,plain,
    ( k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | ~ v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ spl15_14
    | ~ spl15_128
    | ~ spl15_952 ),
    inference(subsumption_resolution,[],[f9185,f599])).

fof(f599,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl15_14 ),
    inference(resolution,[],[f593,f313])).

fof(f313,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f146])).

fof(f146,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f78])).

fof(f78,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t118_tmap_1.p',t7_boole)).

fof(f593,plain,
    ( r2_hidden(sK9(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl15_14 ),
    inference(resolution,[],[f591,f272])).

fof(f591,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,u1_struct_0(sK0)) )
    | ~ spl15_14 ),
    inference(subsumption_resolution,[],[f590,f223])).

fof(f590,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,u1_struct_0(sK0))
        | ~ l1_pre_topc(sK0) )
    | ~ spl15_14 ),
    inference(resolution,[],[f557,f227])).

fof(f557,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(sK2,X1)
        | ~ m1_subset_1(X0,u1_struct_0(X1))
        | r2_hidden(X0,u1_struct_0(X1))
        | ~ l1_pre_topc(X1) )
    | ~ spl15_14 ),
    inference(resolution,[],[f525,f244])).

fof(f525,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X0))
        | r2_hidden(X1,X0)
        | ~ m1_subset_1(X1,X0) )
    | ~ spl15_14 ),
    inference(resolution,[],[f503,f283])).

fof(f283,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f125])).

fof(f125,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f124])).

fof(f124,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f71])).

fof(f71,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t118_tmap_1.p',t2_subset)).

fof(f503,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X0)) )
    | ~ spl15_14 ),
    inference(resolution,[],[f496,f331])).

fof(f331,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f165])).

fof(f165,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f76])).

fof(f76,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t118_tmap_1.p',t5_subset)).

fof(f496,plain,
    ( r2_hidden(sK3,u1_struct_0(sK2))
    | ~ spl15_14 ),
    inference(avatar_component_clause,[],[f495])).

fof(f9185,plain,
    ( k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | ~ v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl15_128
    | ~ spl15_952 ),
    inference(subsumption_resolution,[],[f9184,f8040])).

fof(f8040,plain,
    ( v1_funct_1(k9_tmap_1(sK0,sK1))
    | ~ spl15_952 ),
    inference(avatar_component_clause,[],[f8039])).

fof(f9184,plain,
    ( k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | ~ v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ v1_funct_1(k9_tmap_1(sK0,sK1))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl15_128 ),
    inference(subsumption_resolution,[],[f9183,f3733])).

fof(f3733,plain,(
    v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f3732,f3433])).

fof(f3433,plain,(
    u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f3432,f221])).

fof(f3432,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f3431,f222])).

fof(f3431,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f3430,f223])).

fof(f3430,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f3426,f224])).

fof(f224,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f188])).

fof(f3426,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f269,f225])).

fof(f269,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1))
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f115])).

fof(f115,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ! [X2] :
                ( u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f114])).

fof(f114,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ! [X2] :
                ( u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f66])).

fof(f66,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ( ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2) ) )
            & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t118_tmap_1.p',t114_tmap_1)).

fof(f3732,plain,(
    v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f3731,f221])).

fof(f3731,plain,
    ( v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f3730,f222])).

fof(f3730,plain,
    ( v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f3726,f223])).

fof(f3726,plain,
    ( v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f295,f225])).

fof(f295,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f133])).

fof(f133,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f132])).

fof(f132,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t118_tmap_1.p',dt_k9_tmap_1)).

fof(f9183,plain,
    ( k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | ~ v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k9_tmap_1(sK0,sK1))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl15_128 ),
    inference(subsumption_resolution,[],[f9182,f4200])).

fof(f4200,plain,(
    m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    inference(forward_demodulation,[],[f4199,f3433])).

fof(f4199,plain,(
    m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) ),
    inference(subsumption_resolution,[],[f4198,f221])).

fof(f4198,plain,
    ( m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f4197,f222])).

fof(f4197,plain,
    ( m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f4193,f223])).

fof(f4193,plain,
    ( m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f296,f225])).

fof(f296,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f133])).

fof(f9182,plain,
    ( k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | ~ v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k9_tmap_1(sK0,sK1))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl15_128 ),
    inference(subsumption_resolution,[],[f9181,f5836])).

fof(f5836,plain,
    ( v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl15_128 ),
    inference(forward_demodulation,[],[f5835,f3433])).

fof(f5835,plain,
    ( v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ spl15_128 ),
    inference(subsumption_resolution,[],[f5827,f1359])).

fof(f5827,plain,
    ( v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f4259,f5816])).

fof(f4259,plain,(
    ! [X9] :
      ( v1_funct_2(k7_tmap_1(sK0,X9),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X9)))
      | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f4258,f221])).

fof(f4258,plain,(
    ! [X9] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_funct_2(k7_tmap_1(sK0,X9),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X9)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f4252,f223])).

fof(f4252,plain,(
    ! [X9] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | v1_funct_2(k7_tmap_1(sK0,X9),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X9)))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f305,f222])).

fof(f305,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f141])).

fof(f9181,plain,
    ( k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | ~ v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k9_tmap_1(sK0,sK1))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl15_128 ),
    inference(subsumption_resolution,[],[f9180,f7311])).

fof(f7311,plain,
    ( m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl15_128 ),
    inference(forward_demodulation,[],[f7310,f3433])).

fof(f7310,plain,
    ( m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | ~ spl15_128 ),
    inference(subsumption_resolution,[],[f7308,f1359])).

fof(f7308,plain,
    ( m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f4359,f5816])).

fof(f4359,plain,(
    ! [X9] :
      ( m1_subset_1(k7_tmap_1(sK0,X9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X9)))))
      | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f4358,f221])).

fof(f4358,plain,(
    ! [X9] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(k7_tmap_1(sK0,X9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X9)))))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f4352,f223])).

fof(f4352,plain,(
    ! [X9] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | m1_subset_1(k7_tmap_1(sK0,X9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X9)))))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f306,f222])).

fof(f306,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f141])).

fof(f9180,plain,
    ( k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | ~ m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k9_tmap_1(sK0,sK1))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(duplicate_literal_removal,[],[f9179])).

fof(f9179,plain,
    ( k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | ~ m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k9_tmap_1(sK0,sK1))
    | v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f8357,f344])).

fof(f344,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
      | X4 = X5
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f216])).

fof(f216,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
          | X4 != X5 )
        & ( X4 = X5
          | ~ r1_funct_2(X0,X1,X2,X3,X4,X5) ) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(nnf_transformation,[],[f183])).

fof(f183,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f182])).

fof(f182,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f60])).

fof(f60,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_2(X5,X2,X3)
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X4,X0,X1)
        & v1_funct_1(X4)
        & ~ v1_xboole_0(X3)
        & ~ v1_xboole_0(X1) )
     => ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t118_tmap_1.p',redefinition_r1_funct_2)).

fof(f8357,plain,(
    r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1))) ),
    inference(forward_demodulation,[],[f8356,f3433])).

fof(f8356,plain,(
    r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1))) ),
    inference(forward_demodulation,[],[f8355,f5816])).

fof(f8355,plain,(
    r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f8354,f221])).

fof(f8354,plain,
    ( r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f8353,f222])).

fof(f8353,plain,
    ( r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f8349,f223])).

fof(f8349,plain,
    ( r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f8301,f225])).

fof(f8301,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f8300,f296])).

fof(f8300,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f8299,f295])).

fof(f8299,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ m1_pre_topc(X1,X0)
      | r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f360,f294])).

fof(f294,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k9_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f133])).

fof(f360,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(k9_tmap_1(X0,X1))
      | ~ v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ m1_pre_topc(X1,X0)
      | r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(global_subsumption,[],[f244,f353])).

fof(f353,plain,(
    ! [X0,X1] :
      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ v1_funct_1(k9_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f352])).

fof(f352,plain,(
    ! [X2,X0,X1] :
      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),X2,k7_tmap_1(X0,u1_struct_0(X1)))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | k9_tmap_1(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f254])).

fof(f254,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4))
      | u1_struct_0(X1) != X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | k9_tmap_1(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f200])).

fof(f200,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k9_tmap_1(X0,X1) = X2
                  | ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK6(X0,X1,X2))),X2,k7_tmap_1(X0,sK6(X0,X1,X2)))
                    & u1_struct_0(X1) = sK6(X0,X1,X2)
                    & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4))
                      | u1_struct_0(X1) != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k9_tmap_1(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f198,f199])).

fof(f199,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
          & u1_struct_0(X1) = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK6(X0,X1,X2))),X2,k7_tmap_1(X0,sK6(X0,X1,X2)))
        & u1_struct_0(X1) = sK6(X0,X1,X2)
        & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f198,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k9_tmap_1(X0,X1) = X2
                  | ? [X3] :
                      ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
                      & u1_struct_0(X1) = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4))
                      | u1_struct_0(X1) != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k9_tmap_1(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f197])).

fof(f197,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k9_tmap_1(X0,X1) = X2
                  | ? [X3] :
                      ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
                      & u1_struct_0(X1) = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X3] :
                      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
                      | u1_struct_0(X1) != X3
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k9_tmap_1(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f105])).

fof(f105,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k9_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f104])).

fof(f104,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k9_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
                & v1_funct_1(X2) )
             => ( k9_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( u1_struct_0(X1) = X3
                     => r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t118_tmap_1.p',d12_tmap_1)).

fof(f8059,plain,
    ( ~ spl15_12
    | spl15_955 ),
    inference(avatar_contradiction_clause,[],[f8058])).

fof(f8058,plain,
    ( $false
    | ~ spl15_12
    | ~ spl15_955 ),
    inference(subsumption_resolution,[],[f8057,f487])).

fof(f8057,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ spl15_955 ),
    inference(resolution,[],[f8049,f240])).

fof(f8049,plain,
    ( ~ l1_struct_0(sK2)
    | ~ spl15_955 ),
    inference(avatar_component_clause,[],[f8048])).

fof(f8048,plain,
    ( spl15_955
  <=> ~ l1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_955])])).

fof(f8056,plain,(
    spl15_953 ),
    inference(avatar_contradiction_clause,[],[f8055])).

fof(f8055,plain,
    ( $false
    | ~ spl15_953 ),
    inference(subsumption_resolution,[],[f8054,f221])).

fof(f8054,plain,
    ( v2_struct_0(sK0)
    | ~ spl15_953 ),
    inference(subsumption_resolution,[],[f8053,f222])).

fof(f8053,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_953 ),
    inference(subsumption_resolution,[],[f8052,f223])).

fof(f8052,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_953 ),
    inference(subsumption_resolution,[],[f8051,f225])).

fof(f8051,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_953 ),
    inference(resolution,[],[f8043,f294])).

fof(f8043,plain,
    ( ~ v1_funct_1(k9_tmap_1(sK0,sK1))
    | ~ spl15_953 ),
    inference(avatar_component_clause,[],[f8042])).

fof(f8042,plain,
    ( spl15_953
  <=> ~ v1_funct_1(k9_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_953])])).

fof(f8004,plain,(
    spl15_943 ),
    inference(avatar_contradiction_clause,[],[f8003])).

fof(f8003,plain,
    ( $false
    | ~ spl15_943 ),
    inference(subsumption_resolution,[],[f8002,f222])).

fof(f8002,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ spl15_943 ),
    inference(subsumption_resolution,[],[f8001,f223])).

fof(f8001,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl15_943 ),
    inference(resolution,[],[f8000,f227])).

fof(f8000,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl15_943 ),
    inference(resolution,[],[f7974,f271])).

fof(f271,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f117])).

fof(f117,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f116])).

fof(f116,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f81])).

fof(f81,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t118_tmap_1.p',cc1_pre_topc)).

fof(f7974,plain,
    ( ~ v2_pre_topc(sK2)
    | ~ spl15_943 ),
    inference(avatar_component_clause,[],[f7973])).

fof(f7973,plain,
    ( spl15_943
  <=> ~ v2_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_943])])).

fof(f1407,plain,(
    spl15_129 ),
    inference(avatar_contradiction_clause,[],[f1406])).

fof(f1406,plain,
    ( $false
    | ~ spl15_129 ),
    inference(subsumption_resolution,[],[f1405,f223])).

fof(f1405,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl15_129 ),
    inference(subsumption_resolution,[],[f1402,f225])).

fof(f1402,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl15_129 ),
    inference(resolution,[],[f1362,f244])).

fof(f1362,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_129 ),
    inference(avatar_component_clause,[],[f1361])).

fof(f1361,plain,
    ( spl15_129
  <=> ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_129])])).

fof(f1203,plain,
    ( spl15_79
    | ~ spl15_84 ),
    inference(avatar_contradiction_clause,[],[f1202])).

fof(f1202,plain,
    ( $false
    | ~ spl15_79
    | ~ spl15_84 ),
    inference(subsumption_resolution,[],[f1147,f1124])).

fof(f1124,plain,
    ( l1_pre_topc(sK1)
    | ~ spl15_84 ),
    inference(avatar_component_clause,[],[f1123])).

fof(f1123,plain,
    ( spl15_84
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_84])])).

fof(f1147,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ spl15_79 ),
    inference(resolution,[],[f1113,f240])).

fof(f1113,plain,
    ( ~ l1_struct_0(sK1)
    | ~ spl15_79 ),
    inference(avatar_component_clause,[],[f1112])).

fof(f1112,plain,
    ( spl15_79
  <=> ~ l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_79])])).

fof(f1201,plain,(
    spl15_85 ),
    inference(avatar_contradiction_clause,[],[f1200])).

fof(f1200,plain,
    ( $false
    | ~ spl15_85 ),
    inference(subsumption_resolution,[],[f1199,f223])).

fof(f1199,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl15_85 ),
    inference(resolution,[],[f1148,f225])).

fof(f1148,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK1,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl15_85 ),
    inference(resolution,[],[f1127,f243])).

fof(f243,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f95])).

fof(f95,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f39])).

fof(f39,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t118_tmap_1.p',dt_m1_pre_topc)).

fof(f1127,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ spl15_85 ),
    inference(avatar_component_clause,[],[f1126])).

fof(f1126,plain,
    ( spl15_85
  <=> ~ l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_85])])).

fof(f501,plain,(
    spl15_13 ),
    inference(avatar_contradiction_clause,[],[f500])).

fof(f500,plain,
    ( $false
    | ~ spl15_13 ),
    inference(subsumption_resolution,[],[f499,f223])).

fof(f499,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl15_13 ),
    inference(resolution,[],[f498,f227])).

fof(f498,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl15_13 ),
    inference(resolution,[],[f490,f243])).

fof(f490,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ spl15_13 ),
    inference(avatar_component_clause,[],[f489])).

fof(f489,plain,
    ( spl15_13
  <=> ~ l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_13])])).

fof(f497,plain,
    ( ~ spl15_13
    | spl15_14 ),
    inference(avatar_split_clause,[],[f484,f495,f489])).

fof(f484,plain,
    ( r2_hidden(sK3,u1_struct_0(sK2))
    | ~ l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f482,f226])).

fof(f482,plain,
    ( r2_hidden(sK3,u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f414,f229])).

fof(f414,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X2))
      | r2_hidden(X1,u1_struct_0(X2))
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X2) ) ),
    inference(resolution,[],[f386,f240])).

fof(f386,plain,(
    ! [X6,X5] :
      ( ~ l1_struct_0(X6)
      | ~ m1_subset_1(X5,u1_struct_0(X6))
      | r2_hidden(X5,u1_struct_0(X6))
      | v2_struct_0(X6) ) ),
    inference(resolution,[],[f283,f249])).

fof(f249,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f101])).

fof(f101,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f100])).

fof(f100,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f83])).

fof(f83,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t118_tmap_1.p',fc2_struct_0)).
%------------------------------------------------------------------------------
