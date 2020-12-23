%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tex_2__t56_tex_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:54 EDT 2019

% Result     : Theorem 4.16s
% Output     : Refutation 4.16s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 338 expanded)
%              Number of leaves         :   27 ( 124 expanded)
%              Depth                    :   19
%              Number of atoms          :  484 (1973 expanded)
%              Number of equality atoms :   32 ( 260 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2440,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f337,f343,f626,f998,f1630,f2386,f2417,f2439])).

fof(f2439,plain,(
    ~ spl9_14 ),
    inference(avatar_contradiction_clause,[],[f2438])).

fof(f2438,plain,
    ( $false
    | ~ spl9_14 ),
    inference(subsumption_resolution,[],[f2428,f102])).

fof(f102,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t56_tex_2.p',fc1_xboole_0)).

fof(f2428,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl9_14 ),
    inference(resolution,[],[f625,f108])).

fof(f108,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f80,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f78,f79])).

fof(f79,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f78,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f77])).

fof(f77,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t56_tex_2.p',d1_xboole_0)).

fof(f625,plain,
    ( r2_hidden(sK5(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)),k1_xboole_0),k1_xboole_0)
    | ~ spl9_14 ),
    inference(avatar_component_clause,[],[f624])).

fof(f624,plain,
    ( spl9_14
  <=> r2_hidden(sK5(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)),k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f2417,plain,
    ( spl9_15
    | ~ spl9_28
    | ~ spl9_30 ),
    inference(avatar_contradiction_clause,[],[f2416])).

fof(f2416,plain,
    ( $false
    | ~ spl9_15
    | ~ spl9_28
    | ~ spl9_30 ),
    inference(unit_resulting_resolution,[],[f1629,f2410,f295])).

fof(f295,plain,(
    ! [X2] :
      ( ~ sQ8_eqProxy(X2,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
      | ~ sQ8_eqProxy(X2,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) ) ),
    inference(resolution,[],[f280,f181])).

fof(f181,plain,(
    ! [X0,X1] :
      ( sQ8_eqProxy(X1,X0)
      | ~ sQ8_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f142])).

fof(f142,plain,(
    ! [X1,X0] :
      ( sQ8_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ8_eqProxy])])).

fof(f280,plain,(
    ! [X6] :
      ( ~ sQ8_eqProxy(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),X6)
      | ~ sQ8_eqProxy(X6,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) ) ),
    inference(resolution,[],[f182,f143])).

fof(f143,plain,(
    ~ sQ8_eqProxy(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) ),
    inference(equality_proxy_replacement,[],[f100,f142])).

fof(f100,plain,(
    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,
    ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))
    & ~ r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v3_tdlat_3(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f44,f75,f74,f73])).

fof(f73,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))
                & ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))
              & ~ r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_pre_topc(sK0)
      & v3_tdlat_3(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f74,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))
              & ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK1)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))
            & ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK1,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))
          & ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK2)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
        & ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK2)))
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))
              & ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))
              & ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v3_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))
                  | r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))
                | r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t56_tex_2.p',t56_tex_2)).

fof(f182,plain,(
    ! [X2,X0,X1] :
      ( sQ8_eqProxy(X0,X2)
      | ~ sQ8_eqProxy(X1,X2)
      | ~ sQ8_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f142])).

fof(f2410,plain,
    ( sQ8_eqProxy(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK5(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)),k1_xboole_0))),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
    | ~ spl9_15
    | ~ spl9_28 ),
    inference(subsumption_resolution,[],[f661,f1620])).

fof(f1620,plain,
    ( m1_subset_1(sK5(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)),k1_xboole_0),u1_struct_0(sK0))
    | ~ spl9_28 ),
    inference(avatar_component_clause,[],[f1619])).

fof(f1619,plain,
    ( spl9_28
  <=> m1_subset_1(sK5(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)),k1_xboole_0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_28])])).

fof(f661,plain,
    ( sQ8_eqProxy(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK5(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)),k1_xboole_0))),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
    | ~ m1_subset_1(sK5(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)),k1_xboole_0),u1_struct_0(sK0))
    | ~ spl9_15 ),
    inference(subsumption_resolution,[],[f660,f93])).

fof(f93,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f76])).

fof(f660,plain,
    ( sQ8_eqProxy(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK5(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)),k1_xboole_0))),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
    | ~ m1_subset_1(sK5(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)),k1_xboole_0),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl9_15 ),
    inference(subsumption_resolution,[],[f659,f94])).

fof(f94,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f76])).

fof(f659,plain,
    ( sQ8_eqProxy(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK5(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)),k1_xboole_0))),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
    | ~ m1_subset_1(sK5(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)),k1_xboole_0),u1_struct_0(sK0))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_15 ),
    inference(subsumption_resolution,[],[f658,f95])).

fof(f95,plain,(
    v3_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f76])).

fof(f658,plain,
    ( sQ8_eqProxy(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK5(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)),k1_xboole_0))),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
    | ~ m1_subset_1(sK5(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)),k1_xboole_0),u1_struct_0(sK0))
    | ~ v3_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_15 ),
    inference(subsumption_resolution,[],[f657,f96])).

fof(f96,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f76])).

fof(f657,plain,
    ( sQ8_eqProxy(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK5(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)),k1_xboole_0))),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
    | ~ m1_subset_1(sK5(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)),k1_xboole_0),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v3_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_15 ),
    inference(subsumption_resolution,[],[f649,f97])).

fof(f97,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f76])).

fof(f649,plain,
    ( sQ8_eqProxy(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK5(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)),k1_xboole_0))),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK5(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)),k1_xboole_0),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v3_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_15 ),
    inference(resolution,[],[f643,f146])).

fof(f146,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
      | sQ8_eqProxy(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_proxy_replacement,[],[f106,f142])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))
      | ~ r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))
              | ~ r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))
              | ~ r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
               => k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t56_tex_2.p',t55_tex_2)).

fof(f643,plain,
    ( r2_hidden(sK5(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)),k1_xboole_0),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
    | ~ spl9_15 ),
    inference(subsumption_resolution,[],[f406,f622])).

fof(f622,plain,
    ( ~ r2_hidden(sK5(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)),k1_xboole_0),k1_xboole_0)
    | ~ spl9_15 ),
    inference(avatar_component_clause,[],[f621])).

fof(f621,plain,
    ( spl9_15
  <=> ~ r2_hidden(sK5(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)),k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f406,plain,
    ( r2_hidden(sK5(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)),k1_xboole_0),k1_xboole_0)
    | r2_hidden(sK5(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)),k1_xboole_0),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) ),
    inference(resolution,[],[f245,f99])).

fof(f99,plain,(
    ~ r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) ),
    inference(cnf_transformation,[],[f76])).

fof(f245,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK5(X0,X1,k1_xboole_0),k1_xboole_0)
      | r2_hidden(sK5(X0,X1,k1_xboole_0),X0) ) ),
    inference(resolution,[],[f159,f151])).

fof(f151,plain,(
    ! [X0,X1] :
      ( ~ sQ8_eqProxy(k3_xboole_0(X0,X1),k1_xboole_0)
      | r1_xboole_0(X0,X1) ) ),
    inference(equality_proxy_replacement,[],[f122,f142])).

fof(f122,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t56_tex_2.p',d7_xboole_0)).

fof(f159,plain,(
    ! [X2,X0,X1] :
      ( sQ8_eqProxy(k3_xboole_0(X0,X1),X2)
      | r2_hidden(sK5(X0,X1,X2),X0)
      | r2_hidden(sK5(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f133,f142])).

fof(f133,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK5(X0,X1,X2),X0)
      | r2_hidden(sK5(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f88])).

fof(f88,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
            | ~ r2_hidden(sK5(X0,X1,X2),X0)
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK5(X0,X1,X2),X1)
              & r2_hidden(sK5(X0,X1,X2),X0) )
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f86,f87])).

fof(f87,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
          | ~ r2_hidden(sK5(X0,X1,X2),X0)
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK5(X0,X1,X2),X1)
            & r2_hidden(sK5(X0,X1,X2),X0) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f86,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f85])).

fof(f85,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f84])).

fof(f84,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t56_tex_2.p',d4_xboole_0)).

fof(f1629,plain,
    ( sQ8_eqProxy(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK5(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)),k1_xboole_0))),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
    | ~ spl9_30 ),
    inference(avatar_component_clause,[],[f1628])).

fof(f1628,plain,
    ( spl9_30
  <=> sQ8_eqProxy(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK5(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)),k1_xboole_0))),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_30])])).

fof(f2386,plain,
    ( spl9_15
    | ~ spl9_20
    | spl9_29 ),
    inference(avatar_contradiction_clause,[],[f2385])).

fof(f2385,plain,
    ( $false
    | ~ spl9_15
    | ~ spl9_20
    | ~ spl9_29 ),
    inference(subsumption_resolution,[],[f1077,f1623])).

fof(f1623,plain,
    ( ~ m1_subset_1(sK5(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)),k1_xboole_0),u1_struct_0(sK0))
    | ~ spl9_29 ),
    inference(avatar_component_clause,[],[f1622])).

fof(f1622,plain,
    ( spl9_29
  <=> ~ m1_subset_1(sK5(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)),k1_xboole_0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_29])])).

fof(f1077,plain,
    ( m1_subset_1(sK5(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)),k1_xboole_0),u1_struct_0(sK0))
    | ~ spl9_15
    | ~ spl9_20 ),
    inference(subsumption_resolution,[],[f1076,f96])).

fof(f1076,plain,
    ( m1_subset_1(sK5(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)),k1_xboole_0),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ spl9_15
    | ~ spl9_20 ),
    inference(subsumption_resolution,[],[f1074,f974])).

fof(f974,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_20 ),
    inference(avatar_component_clause,[],[f973])).

fof(f973,plain,
    ( spl9_20
  <=> m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).

fof(f1074,plain,
    ( m1_subset_1(sK5(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)),k1_xboole_0),u1_struct_0(sK0))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl9_15 ),
    inference(resolution,[],[f653,f119])).

fof(f119,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
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
    file('/export/starexec/sandbox2/benchmark/tex_2__t56_tex_2.p',dt_k2_pre_topc)).

fof(f653,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(X0))
        | m1_subset_1(sK5(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)),k1_xboole_0),X0) )
    | ~ spl9_15 ),
    inference(resolution,[],[f643,f129])).

fof(f129,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f70])).

fof(f70,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t56_tex_2.p',t4_subset)).

fof(f1630,plain,
    ( ~ spl9_29
    | spl9_30
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f642,f618,f1628,f1622])).

fof(f618,plain,
    ( spl9_12
  <=> r2_hidden(sK5(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)),k1_xboole_0),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f642,plain,
    ( sQ8_eqProxy(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK5(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)),k1_xboole_0))),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
    | ~ m1_subset_1(sK5(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)),k1_xboole_0),u1_struct_0(sK0))
    | ~ spl9_12 ),
    inference(subsumption_resolution,[],[f641,f93])).

fof(f641,plain,
    ( sQ8_eqProxy(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK5(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)),k1_xboole_0))),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
    | ~ m1_subset_1(sK5(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)),k1_xboole_0),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl9_12 ),
    inference(subsumption_resolution,[],[f640,f94])).

fof(f640,plain,
    ( sQ8_eqProxy(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK5(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)),k1_xboole_0))),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
    | ~ m1_subset_1(sK5(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)),k1_xboole_0),u1_struct_0(sK0))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_12 ),
    inference(subsumption_resolution,[],[f639,f95])).

fof(f639,plain,
    ( sQ8_eqProxy(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK5(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)),k1_xboole_0))),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
    | ~ m1_subset_1(sK5(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)),k1_xboole_0),u1_struct_0(sK0))
    | ~ v3_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_12 ),
    inference(subsumption_resolution,[],[f638,f96])).

fof(f638,plain,
    ( sQ8_eqProxy(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK5(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)),k1_xboole_0))),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
    | ~ m1_subset_1(sK5(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)),k1_xboole_0),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v3_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_12 ),
    inference(subsumption_resolution,[],[f630,f98])).

fof(f98,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f76])).

fof(f630,plain,
    ( sQ8_eqProxy(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK5(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)),k1_xboole_0))),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK5(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)),k1_xboole_0),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v3_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_12 ),
    inference(resolution,[],[f619,f146])).

fof(f619,plain,
    ( r2_hidden(sK5(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)),k1_xboole_0),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
    | ~ spl9_12 ),
    inference(avatar_component_clause,[],[f618])).

fof(f998,plain,
    ( ~ spl9_4
    | spl9_21 ),
    inference(avatar_contradiction_clause,[],[f997])).

fof(f997,plain,
    ( $false
    | ~ spl9_4
    | ~ spl9_21 ),
    inference(subsumption_resolution,[],[f996,f354])).

fof(f354,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl9_4 ),
    inference(resolution,[],[f330,f108])).

fof(f330,plain,
    ( r2_hidden(sK3(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f329])).

fof(f329,plain,
    ( spl9_4
  <=> r2_hidden(sK3(u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f996,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl9_21 ),
    inference(subsumption_resolution,[],[f993,f97])).

fof(f993,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl9_21 ),
    inference(resolution,[],[f977,f118])).

fof(f118,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t56_tex_2.p',dt_k6_domain_1)).

fof(f977,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_21 ),
    inference(avatar_component_clause,[],[f976])).

fof(f976,plain,
    ( spl9_21
  <=> ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).

fof(f626,plain,
    ( spl9_12
    | spl9_14 ),
    inference(avatar_split_clause,[],[f398,f624,f618])).

fof(f398,plain,
    ( r2_hidden(sK5(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)),k1_xboole_0),k1_xboole_0)
    | r2_hidden(sK5(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)),k1_xboole_0),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) ),
    inference(resolution,[],[f236,f99])).

fof(f236,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK5(X0,X1,k1_xboole_0),k1_xboole_0)
      | r2_hidden(sK5(X0,X1,k1_xboole_0),X1) ) ),
    inference(resolution,[],[f158,f151])).

fof(f158,plain,(
    ! [X2,X0,X1] :
      ( sQ8_eqProxy(k3_xboole_0(X0,X1),X2)
      | r2_hidden(sK5(X0,X1,X2),X1)
      | r2_hidden(sK5(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f134,f142])).

fof(f134,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK5(X0,X1,X2),X1)
      | r2_hidden(sK5(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f88])).

fof(f343,plain,(
    spl9_7 ),
    inference(avatar_contradiction_clause,[],[f342])).

fof(f342,plain,
    ( $false
    | ~ spl9_7 ),
    inference(subsumption_resolution,[],[f340,f96])).

fof(f340,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl9_7 ),
    inference(resolution,[],[f336,f104])).

fof(f104,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t56_tex_2.p',dt_l1_pre_topc)).

fof(f336,plain,
    ( ~ l1_struct_0(sK0)
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f335])).

fof(f335,plain,
    ( spl9_7
  <=> ~ l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f337,plain,
    ( spl9_4
    | ~ spl9_7 ),
    inference(avatar_split_clause,[],[f323,f335,f329])).

fof(f323,plain,
    ( ~ l1_struct_0(sK0)
    | r2_hidden(sK3(u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    inference(resolution,[],[f183,f93])).

fof(f183,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | r2_hidden(sK3(u1_struct_0(X0)),u1_struct_0(X0)) ) ),
    inference(resolution,[],[f109,f107])).

fof(f107,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t56_tex_2.p',fc2_struct_0)).

fof(f109,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK3(X0),X0) ) ),
    inference(cnf_transformation,[],[f80])).
%------------------------------------------------------------------------------
