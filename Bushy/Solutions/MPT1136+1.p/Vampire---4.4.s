%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : orders_2__t24_orders_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:18 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  194 ( 445 expanded)
%              Number of leaves         :   57 ( 189 expanded)
%              Depth                    :    9
%              Number of atoms          :  491 (1110 expanded)
%              Number of equality atoms :   15 (  75 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f574,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f107,f114,f121,f128,f135,f142,f149,f156,f165,f172,f182,f195,f207,f222,f235,f243,f257,f281,f292,f302,f313,f325,f342,f386,f397,f407,f418,f482,f491,f541,f548,f555,f566,f573])).

fof(f573,plain,
    ( ~ spl6_4
    | ~ spl6_12
    | spl6_15
    | ~ spl6_24
    | ~ spl6_30
    | ~ spl6_64 ),
    inference(avatar_contradiction_clause,[],[f572])).

fof(f572,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_12
    | ~ spl6_15
    | ~ spl6_24
    | ~ spl6_30
    | ~ spl6_64 ),
    inference(subsumption_resolution,[],[f571,f567])).

fof(f567,plain,
    ( r2_hidden(k4_tarski(sK1,sK1),u1_orders_2(sK0))
    | ~ spl6_24
    | ~ spl6_30
    | ~ spl6_64 ),
    inference(unit_resulting_resolution,[],[f206,f242,f565,f77])).

fof(f77,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(X3,X1)
      | ~ r1_relat_2(X0,X1)
      | r2_hidden(k4_tarski(X3,X3),X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_relat_2(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK2(X0,X1),sK2(X0,X1)),X0)
              & r2_hidden(sK2(X0,X1),X1) ) )
          & ( ! [X3] :
                ( r2_hidden(k4_tarski(X3,X3),X0)
                | ~ r2_hidden(X3,X1) )
            | ~ r1_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f60,f61])).

fof(f61,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(k4_tarski(X2,X2),X0)
          & r2_hidden(X2,X1) )
     => ( ~ r2_hidden(k4_tarski(sK2(X0,X1),sK2(X0,X1)),X0)
        & r2_hidden(sK2(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_relat_2(X0,X1)
            | ? [X2] :
                ( ~ r2_hidden(k4_tarski(X2,X2),X0)
                & r2_hidden(X2,X1) ) )
          & ( ! [X3] :
                ( r2_hidden(k4_tarski(X3,X3),X0)
                | ~ r2_hidden(X3,X1) )
            | ~ r1_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_relat_2(X0,X1)
            | ? [X2] :
                ( ~ r2_hidden(k4_tarski(X2,X2),X0)
                & r2_hidden(X2,X1) ) )
          & ( ! [X2] :
                ( r2_hidden(k4_tarski(X2,X2),X0)
                | ~ r2_hidden(X2,X1) )
            | ~ r1_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_relat_2(X0,X1)
        <=> ! [X2] :
              ( r2_hidden(k4_tarski(X2,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_relat_2(X0,X1)
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
             => r2_hidden(k4_tarski(X2,X2),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t24_orders_2.p',d1_relat_2)).

fof(f565,plain,
    ( v1_relat_1(u1_orders_2(sK0))
    | ~ spl6_64 ),
    inference(avatar_component_clause,[],[f564])).

fof(f564,plain,
    ( spl6_64
  <=> v1_relat_1(u1_orders_2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_64])])).

fof(f242,plain,
    ( r1_relat_2(u1_orders_2(sK0),u1_struct_0(sK0))
    | ~ spl6_30 ),
    inference(avatar_component_clause,[],[f241])).

fof(f241,plain,
    ( spl6_30
  <=> r1_relat_2(u1_orders_2(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f206,plain,
    ( r2_hidden(sK1,u1_struct_0(sK0))
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f205])).

fof(f205,plain,
    ( spl6_24
  <=> r2_hidden(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f571,plain,
    ( ~ r2_hidden(k4_tarski(sK1,sK1),u1_orders_2(sK0))
    | ~ spl6_4
    | ~ spl6_12
    | ~ spl6_15 ),
    inference(unit_resulting_resolution,[],[f120,f148,f155,f148,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_orders_2(X0,X1,X2)
                  | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
                & ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
                  | ~ r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t24_orders_2.p',d9_orders_2)).

fof(f155,plain,
    ( ~ r1_orders_2(sK0,sK1,sK1)
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl6_15
  <=> ~ r1_orders_2(sK0,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f148,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl6_12
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f120,plain,
    ( l1_orders_2(sK0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl6_4
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f566,plain,
    ( spl6_64
    | ~ spl6_62 ),
    inference(avatar_split_clause,[],[f556,f553,f564])).

fof(f553,plain,
    ( spl6_62
  <=> m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_62])])).

fof(f556,plain,
    ( v1_relat_1(u1_orders_2(sK0))
    | ~ spl6_62 ),
    inference(unit_resulting_resolution,[],[f554,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t24_orders_2.p',cc1_relset_1)).

fof(f554,plain,
    ( m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl6_62 ),
    inference(avatar_component_clause,[],[f553])).

fof(f555,plain,
    ( spl6_62
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f326,f119,f553])).

fof(f326,plain,
    ( m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f120,f81])).

fof(f81,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t24_orders_2.p',dt_u1_orders_2)).

fof(f548,plain,
    ( spl6_54
    | spl6_44
    | ~ spl6_6
    | ~ spl6_34 ),
    inference(avatar_split_clause,[],[f284,f279,f126,f334,f416])).

fof(f416,plain,
    ( spl6_54
  <=> o_0_0_xboole_0 = k1_zfmisc_1(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_54])])).

fof(f334,plain,
    ( spl6_44
  <=> r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).

fof(f126,plain,
    ( spl6_6
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f279,plain,
    ( spl6_34
  <=> o_0_0_xboole_0 = sK3(k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f284,plain,
    ( r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | o_0_0_xboole_0 = k1_zfmisc_1(o_0_0_xboole_0)
    | ~ spl6_6
    | ~ spl6_34 ),
    inference(superposition,[],[f226,f280])).

fof(f280,plain,
    ( o_0_0_xboole_0 = sK3(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_34 ),
    inference(avatar_component_clause,[],[f279])).

fof(f226,plain,
    ( ! [X2] :
        ( r2_hidden(sK3(X2),X2)
        | o_0_0_xboole_0 = X2 )
    | ~ spl6_6 ),
    inference(resolution,[],[f200,f175])).

fof(f175,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | o_0_0_xboole_0 = X0 )
    | ~ spl6_6 ),
    inference(backward_demodulation,[],[f173,f86])).

fof(f86,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t24_orders_2.p',t6_boole)).

fof(f173,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f127,f86])).

fof(f127,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f126])).

fof(f200,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK3(X0),X0) ) ),
    inference(resolution,[],[f91,f88])).

fof(f88,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f65])).

fof(f65,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f20,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t24_orders_2.p',existence_m1_subset_1)).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t24_orders_2.p',t2_subset)).

fof(f541,plain,
    ( ~ spl6_61
    | spl6_57 ),
    inference(avatar_split_clause,[],[f483,f480,f539])).

fof(f539,plain,
    ( spl6_61
  <=> ~ r2_hidden(k1_zfmisc_1(o_0_0_xboole_0),sK3(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_61])])).

fof(f480,plain,
    ( spl6_57
  <=> ~ m1_subset_1(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_57])])).

fof(f483,plain,
    ( ~ r2_hidden(k1_zfmisc_1(o_0_0_xboole_0),sK3(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl6_57 ),
    inference(unit_resulting_resolution,[],[f88,f481,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t24_orders_2.p',t4_subset)).

fof(f481,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_57 ),
    inference(avatar_component_clause,[],[f480])).

fof(f491,plain,
    ( ~ spl6_59
    | spl6_57 ),
    inference(avatar_split_clause,[],[f484,f480,f489])).

fof(f489,plain,
    ( spl6_59
  <=> ~ r2_hidden(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_59])])).

fof(f484,plain,
    ( ~ r2_hidden(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_57 ),
    inference(unit_resulting_resolution,[],[f481,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t24_orders_2.p',t1_subset)).

fof(f482,plain,
    ( ~ spl6_57
    | ~ spl6_6
    | ~ spl6_44 ),
    inference(avatar_split_clause,[],[f436,f334,f126,f480])).

fof(f436,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_6
    | ~ spl6_44 ),
    inference(unit_resulting_resolution,[],[f127,f335,f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t24_orders_2.p',t5_subset)).

fof(f335,plain,
    ( r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_44 ),
    inference(avatar_component_clause,[],[f334])).

fof(f418,plain,
    ( spl6_54
    | ~ spl6_6
    | ~ spl6_46 ),
    inference(avatar_split_clause,[],[f351,f340,f126,f416])).

fof(f340,plain,
    ( spl6_46
  <=> v1_xboole_0(k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).

fof(f351,plain,
    ( o_0_0_xboole_0 = k1_zfmisc_1(o_0_0_xboole_0)
    | ~ spl6_6
    | ~ spl6_46 ),
    inference(unit_resulting_resolution,[],[f341,f175])).

fof(f341,plain,
    ( v1_xboole_0(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_46 ),
    inference(avatar_component_clause,[],[f340])).

fof(f407,plain,
    ( ~ spl6_53
    | ~ spl6_6
    | spl6_39
    | ~ spl6_46 ),
    inference(avatar_split_clause,[],[f358,f340,f300,f126,f405])).

fof(f405,plain,
    ( spl6_53
  <=> ~ m1_subset_1(u1_struct_0(sK0),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_53])])).

fof(f300,plain,
    ( spl6_39
  <=> ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).

fof(f358,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),o_0_0_xboole_0)
    | ~ spl6_6
    | ~ spl6_39
    | ~ spl6_46 ),
    inference(backward_demodulation,[],[f351,f301])).

fof(f301,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_39 ),
    inference(avatar_component_clause,[],[f300])).

fof(f397,plain,
    ( spl6_50
    | ~ spl6_6
    | ~ spl6_34
    | ~ spl6_46 ),
    inference(avatar_split_clause,[],[f356,f340,f279,f126,f395])).

fof(f395,plain,
    ( spl6_50
  <=> o_0_0_xboole_0 = sK3(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_50])])).

fof(f356,plain,
    ( o_0_0_xboole_0 = sK3(o_0_0_xboole_0)
    | ~ spl6_6
    | ~ spl6_34
    | ~ spl6_46 ),
    inference(backward_demodulation,[],[f351,f280])).

fof(f386,plain,
    ( spl6_48
    | ~ spl6_6
    | ~ spl6_36
    | ~ spl6_46 ),
    inference(avatar_split_clause,[],[f357,f340,f290,f126,f384])).

fof(f384,plain,
    ( spl6_48
  <=> m1_subset_1(o_0_0_xboole_0,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).

fof(f290,plain,
    ( spl6_36
  <=> m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f357,plain,
    ( m1_subset_1(o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ spl6_6
    | ~ spl6_36
    | ~ spl6_46 ),
    inference(backward_demodulation,[],[f351,f291])).

fof(f291,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_36 ),
    inference(avatar_component_clause,[],[f290])).

fof(f342,plain,
    ( spl6_44
    | spl6_46
    | ~ spl6_36 ),
    inference(avatar_split_clause,[],[f295,f290,f340,f334])).

fof(f295,plain,
    ( v1_xboole_0(k1_zfmisc_1(o_0_0_xboole_0))
    | r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_36 ),
    inference(resolution,[],[f291,f91])).

fof(f325,plain,
    ( ~ spl6_43
    | spl6_39 ),
    inference(avatar_split_clause,[],[f304,f300,f323])).

fof(f323,plain,
    ( spl6_43
  <=> ~ r2_hidden(u1_struct_0(sK0),sK3(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).

fof(f304,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK3(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl6_39 ),
    inference(unit_resulting_resolution,[],[f301,f88,f95])).

fof(f313,plain,
    ( ~ spl6_41
    | spl6_39 ),
    inference(avatar_split_clause,[],[f303,f300,f311])).

fof(f311,plain,
    ( spl6_41
  <=> ~ r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).

fof(f303,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_39 ),
    inference(unit_resulting_resolution,[],[f301,f90])).

fof(f302,plain,
    ( ~ spl6_39
    | ~ spl6_6
    | ~ spl6_28 ),
    inference(avatar_split_clause,[],[f265,f233,f126,f300])).

fof(f233,plain,
    ( spl6_28
  <=> r2_hidden(sK3(u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f265,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_6
    | ~ spl6_28 ),
    inference(unit_resulting_resolution,[],[f234,f127,f96])).

fof(f234,plain,
    ( r2_hidden(sK3(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f233])).

fof(f292,plain,
    ( spl6_36
    | ~ spl6_34 ),
    inference(avatar_split_clause,[],[f285,f279,f290])).

fof(f285,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_34 ),
    inference(superposition,[],[f88,f280])).

fof(f281,plain,
    ( spl6_34
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f269,f126,f279])).

fof(f269,plain,
    ( o_0_0_xboole_0 = sK3(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f266,f226])).

fof(f266,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK3(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f127,f88,f96])).

fof(f257,plain,
    ( ~ spl6_33
    | ~ spl6_28 ),
    inference(avatar_split_clause,[],[f246,f233,f255])).

fof(f255,plain,
    ( spl6_33
  <=> ~ r2_hidden(u1_struct_0(sK0),sK3(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f246,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK3(u1_struct_0(sK0)))
    | ~ spl6_28 ),
    inference(unit_resulting_resolution,[],[f234,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t24_orders_2.p',antisymmetry_r2_hidden)).

fof(f243,plain,
    ( spl6_30
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f236,f119,f112,f241])).

fof(f112,plain,
    ( spl6_2
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f236,plain,
    ( r1_relat_2(u1_orders_2(sK0),u1_struct_0(sK0))
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f120,f113,f82])).

fof(f82,plain,(
    ! [X0] :
      ( r1_relat_2(u1_orders_2(X0),u1_struct_0(X0))
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( ( ( v3_orders_2(X0)
          | ~ r1_relat_2(u1_orders_2(X0),u1_struct_0(X0)) )
        & ( r1_relat_2(u1_orders_2(X0),u1_struct_0(X0))
          | ~ v3_orders_2(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( v3_orders_2(X0)
      <=> r1_relat_2(u1_orders_2(X0),u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v3_orders_2(X0)
      <=> r1_relat_2(u1_orders_2(X0),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t24_orders_2.p',d4_orders_2)).

fof(f113,plain,
    ( v3_orders_2(sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f112])).

fof(f235,plain,
    ( spl6_28
    | spl6_23 ),
    inference(avatar_split_clause,[],[f197,f193,f233])).

fof(f193,plain,
    ( spl6_23
  <=> ~ v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f197,plain,
    ( r2_hidden(sK3(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl6_23 ),
    inference(unit_resulting_resolution,[],[f194,f88,f91])).

fof(f194,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f193])).

fof(f222,plain,
    ( ~ spl6_27
    | ~ spl6_24 ),
    inference(avatar_split_clause,[],[f210,f205,f220])).

fof(f220,plain,
    ( spl6_27
  <=> ~ r2_hidden(u1_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f210,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK1)
    | ~ spl6_24 ),
    inference(unit_resulting_resolution,[],[f206,f89])).

fof(f207,plain,
    ( spl6_24
    | ~ spl6_12
    | spl6_23 ),
    inference(avatar_split_clause,[],[f196,f193,f147,f205])).

fof(f196,plain,
    ( r2_hidden(sK1,u1_struct_0(sK0))
    | ~ spl6_12
    | ~ spl6_23 ),
    inference(unit_resulting_resolution,[],[f194,f148,f91])).

fof(f195,plain,
    ( ~ spl6_23
    | spl6_1
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f186,f163,f105,f193])).

fof(f105,plain,
    ( spl6_1
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f163,plain,
    ( spl6_16
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f186,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl6_1
    | ~ spl6_16 ),
    inference(unit_resulting_resolution,[],[f106,f164,f87])).

fof(f87,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t24_orders_2.p',fc2_struct_0)).

fof(f164,plain,
    ( l1_struct_0(sK0)
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f163])).

fof(f106,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f105])).

fof(f182,plain,
    ( spl6_20
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f173,f126,f180])).

fof(f180,plain,
    ( spl6_20
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f172,plain,
    ( spl6_18
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f158,f140,f170])).

fof(f170,plain,
    ( spl6_18
  <=> l1_struct_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f140,plain,
    ( spl6_10
  <=> l1_orders_2(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f158,plain,
    ( l1_struct_0(sK5)
    | ~ spl6_10 ),
    inference(unit_resulting_resolution,[],[f141,f80])).

fof(f80,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t24_orders_2.p',dt_l1_orders_2)).

fof(f141,plain,
    ( l1_orders_2(sK5)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f140])).

fof(f165,plain,
    ( spl6_16
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f157,f119,f163])).

fof(f157,plain,
    ( l1_struct_0(sK0)
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f120,f80])).

fof(f156,plain,(
    ~ spl6_15 ),
    inference(avatar_split_clause,[],[f75,f154])).

fof(f75,plain,(
    ~ r1_orders_2(sK0,sK1,sK1) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,
    ( ~ r1_orders_2(sK0,sK1,sK1)
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f33,f57,f56])).

fof(f56,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_orders_2(X0,X1,X1)
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ r1_orders_2(sK0,X1,X1)
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_orders_2(X0,X1,X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK1,sK1)
        & m1_subset_1(sK1,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_orders_2(X0,X1,X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_orders_2(X0,X1,X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => r1_orders_2(X0,X1,X1) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_orders_2(X0,X1,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t24_orders_2.p',t24_orders_2)).

fof(f149,plain,(
    spl6_12 ),
    inference(avatar_split_clause,[],[f74,f147])).

fof(f74,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f58])).

fof(f142,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f100,f140])).

fof(f100,plain,(
    l1_orders_2(sK5) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    l1_orders_2(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f18,f69])).

fof(f69,plain,
    ( ? [X0] : l1_orders_2(X0)
   => l1_orders_2(sK5) ),
    introduced(choice_axiom,[])).

fof(f18,axiom,(
    ? [X0] : l1_orders_2(X0) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t24_orders_2.p',existence_l1_orders_2)).

fof(f135,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f99,f133])).

fof(f133,plain,
    ( spl6_8
  <=> l1_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f99,plain,(
    l1_struct_0(sK4) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    l1_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f67])).

fof(f67,plain,
    ( ? [X0] : l1_struct_0(X0)
   => l1_struct_0(sK4) ),
    introduced(choice_axiom,[])).

fof(f19,axiom,(
    ? [X0] : l1_struct_0(X0) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t24_orders_2.p',existence_l1_struct_0)).

fof(f128,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f76,f126])).

fof(f76,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t24_orders_2.p',dt_o_0_0_xboole_0)).

fof(f121,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f73,f119])).

fof(f73,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f114,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f72,f112])).

fof(f72,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f107,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f71,f105])).

fof(f71,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f58])).
%------------------------------------------------------------------------------
