%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tex_2__t50_tex_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n030.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:52 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 881 expanded)
%              Number of leaves         :   12 ( 253 expanded)
%              Depth                    :   16
%              Number of atoms          :  351 (7821 expanded)
%              Number of equality atoms :   20 (  98 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f207,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f103,f189,f206])).

fof(f206,plain,
    ( ~ spl7_0
    | spl7_3 ),
    inference(avatar_contradiction_clause,[],[f205])).

fof(f205,plain,
    ( $false
    | ~ spl7_0
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f196,f67])).

fof(f67,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,
    ( ( ~ v1_zfmisc_1(sK1)
      | ~ v3_tex_2(sK1,sK0) )
    & ( v1_zfmisc_1(sK1)
      | v3_tex_2(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & ~ v1_xboole_0(sK1)
    & l1_pre_topc(sK0)
    & v2_tdlat_3(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f43,f45,f44])).

fof(f44,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v1_zfmisc_1(X1)
              | ~ v3_tex_2(X1,X0) )
            & ( v1_zfmisc_1(X1)
              | v3_tex_2(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
        & l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v3_tex_2(X1,sK0) )
          & ( v1_zfmisc_1(X1)
            | v3_tex_2(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(sK0)
      & v2_tdlat_3(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v3_tex_2(X1,X0) )
          & ( v1_zfmisc_1(X1)
            | v3_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
     => ( ( ~ v1_zfmisc_1(sK1)
          | ~ v3_tex_2(sK1,X0) )
        & ( v1_zfmisc_1(sK1)
          | v3_tex_2(sK1,X0) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v3_tex_2(X1,X0) )
          & ( v1_zfmisc_1(X1)
            | v3_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v3_tex_2(X1,X0) )
          & ( v1_zfmisc_1(X1)
            | v3_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> v1_zfmisc_1(X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> v1_zfmisc_1(X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & ~ v1_xboole_0(X1) )
           => ( v3_tex_2(X1,X0)
            <=> v1_zfmisc_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ( v3_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t50_tex_2.p',t50_tex_2)).

fof(f196,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_0
    | ~ spl7_3 ),
    inference(unit_resulting_resolution,[],[f65,f96,f190,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tex_2(X1,X0)
      | v2_tex_2(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ( sK3(X0,X1) != X1
                & r1_tarski(X1,sK3(X0,X1))
                & v2_tex_2(sK3(X0,X1),X0)
                & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X3] :
                    ( X1 = X3
                    | ~ r1_tarski(X1,X3)
                    | ~ v2_tex_2(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f51,f52])).

fof(f52,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r1_tarski(X1,X2)
          & v2_tex_2(X2,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( sK3(X0,X1) != X1
        & r1_tarski(X1,sK3(X0,X1))
        & v2_tex_2(sK3(X0,X1),X0)
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X3] :
                    ( X1 = X3
                    | ~ r1_tarski(X1,X3)
                    | ~ v2_tex_2(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X2] :
                    ( X1 = X2
                    | ~ r1_tarski(X1,X2)
                    | ~ v2_tex_2(X2,X0)
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X2] :
                    ( X1 = X2
                    | ~ r1_tarski(X1,X2)
                    | ~ v2_tex_2(X2,X0)
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r1_tarski(X1,X2)
                      & v2_tex_2(X2,X0) )
                   => X1 = X2 ) )
              & v2_tex_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t50_tex_2.p',d7_tex_2)).

fof(f190,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | ~ spl7_3 ),
    inference(unit_resulting_resolution,[],[f62,f63,f64,f65,f66,f67,f99,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ~ v1_zfmisc_1(X1) )
            & ( v1_zfmisc_1(X1)
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ( v2_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t50_tex_2.p',t44_tex_2)).

fof(f99,plain,
    ( ~ v1_zfmisc_1(sK1)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl7_3
  <=> ~ v1_zfmisc_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f66,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f64,plain,(
    v2_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f63,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f62,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f96,plain,
    ( v3_tex_2(sK1,sK0)
    | ~ spl7_0 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl7_0
  <=> v3_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_0])])).

fof(f65,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f189,plain,(
    ~ spl7_2 ),
    inference(avatar_contradiction_clause,[],[f188])).

fof(f188,plain,
    ( $false
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f176,f150])).

fof(f150,plain,
    ( sK1 != sK3(sK0,sK1)
    | ~ spl7_2 ),
    inference(unit_resulting_resolution,[],[f65,f104,f67,f147,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( sK3(X0,X1) != X1
      | v3_tex_2(X1,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f147,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ spl7_2 ),
    inference(unit_resulting_resolution,[],[f62,f63,f64,f65,f66,f102,f67,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_zfmisc_1(X1)
      | v2_tex_2(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f102,plain,
    ( v1_zfmisc_1(sK1)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl7_2
  <=> v1_zfmisc_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f104,plain,
    ( ~ v3_tex_2(sK1,sK0)
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f69,f102])).

fof(f69,plain,
    ( ~ v1_zfmisc_1(sK1)
    | ~ v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f176,plain,
    ( sK1 = sK3(sK0,sK1)
    | ~ spl7_2 ),
    inference(unit_resulting_resolution,[],[f66,f165,f151,f171,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t50_tex_2.p',t1_tex_2)).

fof(f171,plain,
    ( v1_zfmisc_1(sK3(sK0,sK1))
    | ~ spl7_2 ),
    inference(unit_resulting_resolution,[],[f62,f63,f64,f65,f152,f149,f165,f82])).

fof(f149,plain,
    ( m1_subset_1(sK3(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_2 ),
    inference(unit_resulting_resolution,[],[f65,f104,f67,f147,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | v3_tex_2(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f152,plain,
    ( v2_tex_2(sK3(sK0,sK1),sK0)
    | ~ spl7_2 ),
    inference(unit_resulting_resolution,[],[f65,f104,f67,f147,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tex_2(sK3(X0,X1),X0)
      | ~ v2_tex_2(X1,X0)
      | v3_tex_2(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f151,plain,
    ( r1_tarski(sK1,sK3(sK0,sK1))
    | ~ spl7_2 ),
    inference(unit_resulting_resolution,[],[f65,f104,f67,f147,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(X1,sK3(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | v3_tex_2(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f165,plain,
    ( ~ v1_xboole_0(sK3(sK0,sK1))
    | ~ spl7_2 ),
    inference(unit_resulting_resolution,[],[f66,f153,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t50_tex_2.p',cc1_subset_1)).

fof(f153,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK3(sK0,sK1)))
    | ~ spl7_2 ),
    inference(unit_resulting_resolution,[],[f151,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t50_tex_2.p',t3_subset)).

fof(f103,plain,
    ( spl7_0
    | spl7_2 ),
    inference(avatar_split_clause,[],[f68,f101,f95])).

fof(f68,plain,
    ( v1_zfmisc_1(sK1)
    | v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f46])).
%------------------------------------------------------------------------------
