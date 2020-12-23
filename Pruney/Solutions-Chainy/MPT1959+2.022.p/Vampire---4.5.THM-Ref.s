%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:53 EST 2020

% Result     : Theorem 1.42s
% Output     : Refutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :  218 ( 432 expanded)
%              Number of leaves         :   51 ( 162 expanded)
%              Depth                    :   12
%              Number of atoms          :  834 (2968 expanded)
%              Number of equality atoms :   27 (  41 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f598,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f121,f122,f148,f153,f172,f174,f179,f182,f218,f282,f284,f286,f288,f290,f292,f377,f428,f490,f501,f507,f527,f537,f547,f558,f562,f592,f593,f597])).

fof(f597,plain,
    ( spl9_44
    | ~ spl9_45
    | ~ spl9_2
    | ~ spl9_42 ),
    inference(avatar_split_clause,[],[f594,f505,f118,f524,f521])).

fof(f521,plain,
    ( spl9_44
  <=> ! [X1] :
        ( ~ r1_tarski(k1_xboole_0,k5_waybel_0(sK2,X1))
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | r2_hidden(X1,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_44])])).

fof(f524,plain,
    ( spl9_45
  <=> sP0(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_45])])).

fof(f118,plain,
    ( spl9_2
  <=> r2_hidden(k3_yellow_0(sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f505,plain,
    ( spl9_42
  <=> ! [X1,X0] :
        ( ~ r1_tarski(k1_xboole_0,k5_waybel_0(sK2,X0))
        | ~ sP0(X1,sK2)
        | ~ r2_hidden(k3_yellow_0(sK2),X1)
        | r2_hidden(X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_42])])).

fof(f594,plain,
    ( ! [X0] :
        ( ~ sP0(sK3,sK2)
        | ~ r1_tarski(k1_xboole_0,k5_waybel_0(sK2,X0))
        | r2_hidden(X0,sK3)
        | ~ m1_subset_1(X0,u1_struct_0(sK2)) )
    | ~ spl9_2
    | ~ spl9_42 ),
    inference(resolution,[],[f120,f506])).

fof(f506,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k3_yellow_0(sK2),X1)
        | ~ sP0(X1,sK2)
        | ~ r1_tarski(k1_xboole_0,k5_waybel_0(sK2,X0))
        | r2_hidden(X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK2)) )
    | ~ spl9_42 ),
    inference(avatar_component_clause,[],[f505])).

fof(f120,plain,
    ( r2_hidden(k3_yellow_0(sK2),sK3)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f118])).

fof(f593,plain,
    ( spl9_7
    | spl9_4
    | ~ spl9_3 ),
    inference(avatar_split_clause,[],[f472,f141,f145,f211])).

fof(f211,plain,
    ( spl9_7
  <=> r2_hidden(sK7(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f145,plain,
    ( spl9_4
  <=> u1_struct_0(sK2) = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f141,plain,
    ( spl9_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f472,plain,
    ( u1_struct_0(sK2) = sK3
    | r2_hidden(sK7(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | ~ spl9_3 ),
    inference(resolution,[],[f394,f142])).

fof(f142,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f141])).

fof(f394,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | r2_hidden(sK7(X0,X1),X0) ) ),
    inference(factoring,[],[f203])).

fof(f203,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK7(X0,X1),X0)
      | X0 = X1
      | r2_hidden(sK7(X0,X1),X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ) ),
    inference(resolution,[],[f105,f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f105,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1),X1)
      | X0 = X1
      | r2_hidden(sK7(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK7(X0,X1),X1)
          | ~ r2_hidden(sK7(X0,X1),X0) )
        & ( r2_hidden(sK7(X0,X1),X1)
          | r2_hidden(sK7(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f60,f61])).

fof(f61,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK7(X0,X1),X1)
          | ~ r2_hidden(sK7(X0,X1),X0) )
        & ( r2_hidden(sK7(X0,X1),X1)
          | r2_hidden(sK7(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

fof(f592,plain,
    ( ~ spl9_7
    | spl9_8
    | ~ spl9_48 ),
    inference(avatar_contradiction_clause,[],[f588])).

fof(f588,plain,
    ( $false
    | ~ spl9_7
    | spl9_8
    | ~ spl9_48 ),
    inference(resolution,[],[f574,f217])).

fof(f217,plain,
    ( ~ r2_hidden(sK7(u1_struct_0(sK2),sK3),sK3)
    | spl9_8 ),
    inference(avatar_component_clause,[],[f215])).

fof(f215,plain,
    ( spl9_8
  <=> r2_hidden(sK7(u1_struct_0(sK2),sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f574,plain,
    ( r2_hidden(sK7(u1_struct_0(sK2),sK3),sK3)
    | ~ spl9_7
    | ~ spl9_48 ),
    inference(resolution,[],[f569,f212])).

fof(f212,plain,
    ( r2_hidden(sK7(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f211])).

fof(f569,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,u1_struct_0(sK2))
        | r2_hidden(X4,sK3) )
    | ~ spl9_48 ),
    inference(resolution,[],[f557,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f557,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK2))
        | r2_hidden(X2,sK3) )
    | ~ spl9_48 ),
    inference(avatar_component_clause,[],[f556])).

% (2049)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% (2073)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% (2075)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% (2074)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% (2061)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% (2079)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% (2065)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
fof(f556,plain,
    ( spl9_48
  <=> ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK2))
        | r2_hidden(X2,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_48])])).

fof(f562,plain,(
    ~ spl9_47 ),
    inference(avatar_contradiction_clause,[],[f559])).

fof(f559,plain,
    ( $false
    | ~ spl9_47 ),
    inference(resolution,[],[f554,f81])).

fof(f81,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f554,plain,
    ( ! [X3] : ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK6(X3)))
    | ~ spl9_47 ),
    inference(avatar_component_clause,[],[f553])).

fof(f553,plain,
    ( spl9_47
  <=> ! [X3] : ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK6(X3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_47])])).

fof(f558,plain,
    ( spl9_47
    | spl9_48
    | ~ spl9_44 ),
    inference(avatar_split_clause,[],[f550,f521,f556,f553])).

fof(f550,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK2))
        | r2_hidden(X2,sK3)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK6(X3))) )
    | ~ spl9_44 ),
    inference(resolution,[],[f522,f130])).

fof(f130,plain,(
    ! [X4,X5,X3] :
      ( r1_tarski(X3,X5)
      | ~ m1_subset_1(X3,k1_zfmisc_1(sK6(X4))) ) ),
    inference(resolution,[],[f127,f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK8(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK8(X0,X1),X1)
          & r2_hidden(sK8(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f64,f65])).

fof(f65,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK8(X0,X1),X1)
        & r2_hidden(sK8(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK6(X1))) ) ),
    inference(resolution,[],[f111,f99])).

fof(f99,plain,(
    ! [X0] : v1_xboole_0(sK6(X0)) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( v1_xboole_0(sK6(X0))
      & m1_subset_1(sK6(X0),k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f5,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( v1_xboole_0(sK6(X0))
        & m1_subset_1(sK6(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f5,axiom,(
    ! [X0] :
    ? [X1] :
      ( v1_xboole_0(X1)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_subset_1)).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f522,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k1_xboole_0,k5_waybel_0(sK2,X1))
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | r2_hidden(X1,sK3) )
    | ~ spl9_44 ),
    inference(avatar_component_clause,[],[f521])).

fof(f547,plain,(
    spl9_46 ),
    inference(avatar_contradiction_clause,[],[f542])).

fof(f542,plain,
    ( $false
    | spl9_46 ),
    inference(resolution,[],[f536,f75])).

fof(f75,plain,(
    v13_waybel_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,
    ( ( r2_hidden(k3_yellow_0(sK2),sK3)
      | ~ v1_subset_1(sK3,u1_struct_0(sK2)) )
    & ( ~ r2_hidden(k3_yellow_0(sK2),sK3)
      | v1_subset_1(sK3,u1_struct_0(sK2)) )
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & v13_waybel_0(sK3,sK2)
    & v2_waybel_0(sK3,sK2)
    & ~ v1_xboole_0(sK3)
    & l1_orders_2(sK2)
    & v1_yellow_0(sK2)
    & v5_orders_2(sK2)
    & v4_orders_2(sK2)
    & v3_orders_2(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f47,f49,f48])).

fof(f48,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( r2_hidden(k3_yellow_0(X0),X1)
              | ~ v1_subset_1(X1,u1_struct_0(X0)) )
            & ( ~ r2_hidden(k3_yellow_0(X0),X1)
              | v1_subset_1(X1,u1_struct_0(X0)) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
        & l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( r2_hidden(k3_yellow_0(sK2),X1)
            | ~ v1_subset_1(X1,u1_struct_0(sK2)) )
          & ( ~ r2_hidden(k3_yellow_0(sK2),X1)
            | v1_subset_1(X1,u1_struct_0(sK2)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
          & v13_waybel_0(X1,sK2)
          & v2_waybel_0(X1,sK2)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(sK2)
      & v1_yellow_0(sK2)
      & v5_orders_2(sK2)
      & v4_orders_2(sK2)
      & v3_orders_2(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ? [X1] :
        ( ( r2_hidden(k3_yellow_0(sK2),X1)
          | ~ v1_subset_1(X1,u1_struct_0(sK2)) )
        & ( ~ r2_hidden(k3_yellow_0(sK2),X1)
          | v1_subset_1(X1,u1_struct_0(sK2)) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
        & v13_waybel_0(X1,sK2)
        & v2_waybel_0(X1,sK2)
        & ~ v1_xboole_0(X1) )
   => ( ( r2_hidden(k3_yellow_0(sK2),sK3)
        | ~ v1_subset_1(sK3,u1_struct_0(sK2)) )
      & ( ~ r2_hidden(k3_yellow_0(sK2),sK3)
        | v1_subset_1(sK3,u1_struct_0(sK2)) )
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
      & v13_waybel_0(sK3,sK2)
      & v2_waybel_0(sK3,sK2)
      & ~ v1_xboole_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(k3_yellow_0(X0),X1)
            | ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & ( ~ r2_hidden(k3_yellow_0(X0),X1)
            | v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & v2_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(k3_yellow_0(X0),X1)
            | ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & ( ~ r2_hidden(k3_yellow_0(X0),X1)
            | v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & v2_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
          <~> ~ r2_hidden(k3_yellow_0(X0),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & v2_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
          <~> ~ r2_hidden(k3_yellow_0(X0),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & v2_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_yellow_0(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X1,X0)
              & v2_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ( v1_subset_1(X1,u1_struct_0(X0))
            <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ( v1_subset_1(X1,u1_struct_0(X0))
          <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_7)).

fof(f536,plain,
    ( ~ v13_waybel_0(sK3,sK2)
    | spl9_46 ),
    inference(avatar_component_clause,[],[f534])).

fof(f534,plain,
    ( spl9_46
  <=> v13_waybel_0(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_46])])).

fof(f537,plain,
    ( ~ spl9_3
    | ~ spl9_46
    | spl9_45 ),
    inference(avatar_split_clause,[],[f530,f524,f534,f141])).

fof(f530,plain,
    ( ~ v13_waybel_0(sK3,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | spl9_45 ),
    inference(resolution,[],[f526,f133])).

fof(f133,plain,(
    ! [X1] :
      ( sP0(X1,sK2)
      | ~ v13_waybel_0(X1,sK2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(resolution,[],[f131,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | ~ v13_waybel_0(X1,X0)
      | sP0(X1,X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( ( v13_waybel_0(X1,X0)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ v13_waybel_0(X1,X0) ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( v13_waybel_0(X1,X0)
      <=> sP0(X1,X0) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f131,plain,(
    ! [X0] :
      ( sP1(sK2,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(resolution,[],[f92,f72])).

fof(f72,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f26,f44,f43])).

fof(f43,plain,(
    ! [X1,X0] :
      ( sP0(X1,X0)
    <=> ! [X2] :
          ( ! [X3] :
              ( r2_hidden(X3,X1)
              | ~ r1_orders_2(X0,X2,X3)
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X2,X3)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X2,X3)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r1_orders_2(X0,X2,X3)
                        & r2_hidden(X2,X1) )
                     => r2_hidden(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_waybel_0)).

fof(f526,plain,
    ( ~ sP0(sK3,sK2)
    | spl9_45 ),
    inference(avatar_component_clause,[],[f524])).

fof(f527,plain,
    ( spl9_44
    | ~ spl9_45
    | ~ spl9_6
    | ~ spl9_42 ),
    inference(avatar_split_clause,[],[f519,f505,f169,f524,f521])).

fof(f169,plain,
    ( spl9_6
  <=> m1_subset_1(k3_yellow_0(sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f519,plain,
    ( ! [X1] :
        ( ~ sP0(sK3,sK2)
        | ~ r1_tarski(k1_xboole_0,k5_waybel_0(sK2,X1))
        | r2_hidden(X1,sK3)
        | ~ m1_subset_1(X1,u1_struct_0(sK2)) )
    | ~ spl9_6
    | ~ spl9_42 ),
    inference(resolution,[],[f506,f175])).

fof(f175,plain,
    ( r2_hidden(k3_yellow_0(sK2),sK3)
    | ~ spl9_6 ),
    inference(resolution,[],[f171,f124])).

fof(f124,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK3)
      | r2_hidden(X0,sK3) ) ),
    inference(resolution,[],[f101,f73])).

fof(f73,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f101,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f171,plain,
    ( m1_subset_1(k3_yellow_0(sK2),sK3)
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f169])).

fof(f507,plain,
    ( ~ spl9_26
    | spl9_42
    | ~ spl9_41 ),
    inference(avatar_split_clause,[],[f503,f499,f505,f350])).

fof(f350,plain,
    ( spl9_26
  <=> m1_subset_1(k3_yellow_0(sK2),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).

fof(f499,plain,
    ( spl9_41
  <=> ! [X0] :
        ( r1_orders_2(sK2,k3_yellow_0(sK2),X0)
        | ~ r1_tarski(k1_xboole_0,k5_waybel_0(sK2,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_41])])).

fof(f503,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k1_xboole_0,k5_waybel_0(sK2,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | r2_hidden(X0,X1)
        | ~ r2_hidden(k3_yellow_0(sK2),X1)
        | ~ m1_subset_1(k3_yellow_0(sK2),u1_struct_0(sK2))
        | ~ sP0(X1,sK2) )
    | ~ spl9_41 ),
    inference(duplicate_literal_removal,[],[f502])).

fof(f502,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k1_xboole_0,k5_waybel_0(sK2,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | r2_hidden(X0,X1)
        | ~ r2_hidden(k3_yellow_0(sK2),X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ m1_subset_1(k3_yellow_0(sK2),u1_struct_0(sK2))
        | ~ sP0(X1,sK2) )
    | ~ spl9_41 ),
    inference(resolution,[],[f500,f86])).

fof(f86,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ r1_orders_2(X1,X4,X5)
      | r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X0)
          & r1_orders_2(X1,sK4(X0,X1),sK5(X0,X1))
          & r2_hidden(sK4(X0,X1),X0)
          & m1_subset_1(sK5(X0,X1),u1_struct_0(X1))
          & m1_subset_1(sK4(X0,X1),u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( ! [X5] :
                ( r2_hidden(X5,X0)
                | ~ r1_orders_2(X1,X4,X5)
                | ~ r2_hidden(X4,X0)
                | ~ m1_subset_1(X5,u1_struct_0(X1)) )
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f53,f55,f54])).

fof(f54,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(X3,X0)
              & r1_orders_2(X1,X2,X3)
              & r2_hidden(X2,X0)
              & m1_subset_1(X3,u1_struct_0(X1)) )
          & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ? [X3] :
            ( ~ r2_hidden(X3,X0)
            & r1_orders_2(X1,sK4(X0,X1),X3)
            & r2_hidden(sK4(X0,X1),X0)
            & m1_subset_1(X3,u1_struct_0(X1)) )
        & m1_subset_1(sK4(X0,X1),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X0)
          & r1_orders_2(X1,sK4(X0,X1),X3)
          & r2_hidden(sK4(X0,X1),X0)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r2_hidden(sK5(X0,X1),X0)
        & r1_orders_2(X1,sK4(X0,X1),sK5(X0,X1))
        & r2_hidden(sK4(X0,X1),X0)
        & m1_subset_1(sK5(X0,X1),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ? [X3] :
                ( ~ r2_hidden(X3,X0)
                & r1_orders_2(X1,X2,X3)
                & r2_hidden(X2,X0)
                & m1_subset_1(X3,u1_struct_0(X1)) )
            & m1_subset_1(X2,u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( ! [X5] :
                ( r2_hidden(X5,X0)
                | ~ r1_orders_2(X1,X4,X5)
                | ~ r2_hidden(X4,X0)
                | ~ m1_subset_1(X5,u1_struct_0(X1)) )
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f52])).

fof(f52,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ? [X2] :
            ( ? [X3] :
                ( ~ r2_hidden(X3,X1)
                & r1_orders_2(X0,X2,X3)
                & r2_hidden(X2,X1)
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) ) )
      & ( ! [X2] :
            ( ! [X3] :
                ( r2_hidden(X3,X1)
                | ~ r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        | ~ sP0(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f500,plain,
    ( ! [X0] :
        ( r1_orders_2(sK2,k3_yellow_0(sK2),X0)
        | ~ r1_tarski(k1_xboole_0,k5_waybel_0(sK2,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK2)) )
    | ~ spl9_41 ),
    inference(avatar_component_clause,[],[f499])).

fof(f501,plain,
    ( ~ spl9_5
    | spl9_41
    | ~ spl9_39 ),
    inference(avatar_split_clause,[],[f492,f488,f499,f165])).

fof(f165,plain,
    ( spl9_5
  <=> l1_orders_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f488,plain,
    ( spl9_39
  <=> ! [X0] :
        ( r1_orders_2(sK2,k1_yellow_0(sK2,k1_xboole_0),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ r1_tarski(k1_xboole_0,k5_waybel_0(sK2,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_39])])).

fof(f492,plain,
    ( ! [X0] :
        ( r1_orders_2(sK2,k3_yellow_0(sK2),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ r1_tarski(k1_xboole_0,k5_waybel_0(sK2,X0))
        | ~ l1_orders_2(sK2) )
    | ~ spl9_39 ),
    inference(superposition,[],[f489,f83])).

fof(f83,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_yellow_0)).

fof(f489,plain,
    ( ! [X0] :
        ( r1_orders_2(sK2,k1_yellow_0(sK2,k1_xboole_0),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ r1_tarski(k1_xboole_0,k5_waybel_0(sK2,X0)) )
    | ~ spl9_39 ),
    inference(avatar_component_clause,[],[f488])).

fof(f490,plain,
    ( spl9_11
    | ~ spl9_15
    | ~ spl9_16
    | ~ spl9_12
    | ~ spl9_5
    | spl9_39
    | ~ spl9_31 ),
    inference(avatar_split_clause,[],[f478,f426,f488,f165,f260,f276,f272,f256])).

fof(f256,plain,
    ( spl9_11
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f272,plain,
    ( spl9_15
  <=> v3_orders_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f276,plain,
    ( spl9_16
  <=> v4_orders_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f260,plain,
    ( spl9_12
  <=> v5_orders_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f426,plain,
    ( spl9_31
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ r1_tarski(k1_xboole_0,k5_waybel_0(sK2,X0))
        | r1_orders_2(sK2,k1_yellow_0(sK2,k1_xboole_0),k1_yellow_0(sK2,k5_waybel_0(sK2,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_31])])).

fof(f478,plain,
    ( ! [X0] :
        ( r1_orders_2(sK2,k1_yellow_0(sK2,k1_xboole_0),X0)
        | ~ r1_tarski(k1_xboole_0,k5_waybel_0(sK2,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ l1_orders_2(sK2)
        | ~ v5_orders_2(sK2)
        | ~ v4_orders_2(sK2)
        | ~ v3_orders_2(sK2)
        | v2_struct_0(sK2) )
    | ~ spl9_31 ),
    inference(duplicate_literal_removal,[],[f477])).

fof(f477,plain,
    ( ! [X0] :
        ( r1_orders_2(sK2,k1_yellow_0(sK2,k1_xboole_0),X0)
        | ~ r1_tarski(k1_xboole_0,k5_waybel_0(sK2,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ l1_orders_2(sK2)
        | ~ v5_orders_2(sK2)
        | ~ v4_orders_2(sK2)
        | ~ v3_orders_2(sK2)
        | v2_struct_0(sK2) )
    | ~ spl9_31 ),
    inference(superposition,[],[f427,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1
            & r1_yellow_0(X0,k5_waybel_0(X0,X1)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1
            & r1_yellow_0(X0,k5_waybel_0(X0,X1)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1
            & r1_yellow_0(X0,k5_waybel_0(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_waybel_0)).

fof(f427,plain,
    ( ! [X0] :
        ( r1_orders_2(sK2,k1_yellow_0(sK2,k1_xboole_0),k1_yellow_0(sK2,k5_waybel_0(sK2,X0)))
        | ~ r1_tarski(k1_xboole_0,k5_waybel_0(sK2,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK2)) )
    | ~ spl9_31 ),
    inference(avatar_component_clause,[],[f426])).

fof(f428,plain,
    ( spl9_11
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_5
    | spl9_31
    | ~ spl9_17 ),
    inference(avatar_split_clause,[],[f423,f280,f426,f165,f264,f260,f256])).

fof(f264,plain,
    ( spl9_13
  <=> v1_yellow_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).

fof(f280,plain,
    ( spl9_17
  <=> ! [X1,X2] :
        ( ~ r1_yellow_0(sK2,X1)
        | ~ m1_subset_1(X2,u1_struct_0(sK2))
        | r1_orders_2(sK2,k1_yellow_0(sK2,X1),k1_yellow_0(sK2,k5_waybel_0(sK2,X2)))
        | ~ r1_tarski(X1,k5_waybel_0(sK2,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).

fof(f423,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK2))
        | r1_orders_2(sK2,k1_yellow_0(sK2,k1_xboole_0),k1_yellow_0(sK2,k5_waybel_0(sK2,X0)))
        | ~ r1_tarski(k1_xboole_0,k5_waybel_0(sK2,X0))
        | ~ l1_orders_2(sK2)
        | ~ v1_yellow_0(sK2)
        | ~ v5_orders_2(sK2)
        | v2_struct_0(sK2) )
    | ~ spl9_17 ),
    inference(resolution,[],[f281,f96])).

fof(f96,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( r2_yellow_0(X0,u1_struct_0(X0))
        & r1_yellow_0(X0,k1_xboole_0) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( r2_yellow_0(X0,u1_struct_0(X0))
        & r1_yellow_0(X0,k1_xboole_0) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r2_yellow_0(X0,u1_struct_0(X0))
        & r1_yellow_0(X0,k1_xboole_0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_yellow_0)).

fof(f281,plain,
    ( ! [X2,X1] :
        ( ~ r1_yellow_0(sK2,X1)
        | ~ m1_subset_1(X2,u1_struct_0(sK2))
        | r1_orders_2(sK2,k1_yellow_0(sK2,X1),k1_yellow_0(sK2,k5_waybel_0(sK2,X2)))
        | ~ r1_tarski(X1,k5_waybel_0(sK2,X2)) )
    | ~ spl9_17 ),
    inference(avatar_component_clause,[],[f280])).

fof(f377,plain,(
    spl9_26 ),
    inference(avatar_contradiction_clause,[],[f376])).

fof(f376,plain,
    ( $false
    | spl9_26 ),
    inference(resolution,[],[f373,f72])).

fof(f373,plain,
    ( ~ l1_orders_2(sK2)
    | spl9_26 ),
    inference(resolution,[],[f352,f82])).

fof(f82,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow_0)).

fof(f352,plain,
    ( ~ m1_subset_1(k3_yellow_0(sK2),u1_struct_0(sK2))
    | spl9_26 ),
    inference(avatar_component_clause,[],[f350])).

fof(f292,plain,(
    spl9_16 ),
    inference(avatar_contradiction_clause,[],[f291])).

fof(f291,plain,
    ( $false
    | spl9_16 ),
    inference(resolution,[],[f278,f69])).

fof(f69,plain,(
    v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f278,plain,
    ( ~ v4_orders_2(sK2)
    | spl9_16 ),
    inference(avatar_component_clause,[],[f276])).

fof(f290,plain,(
    spl9_15 ),
    inference(avatar_contradiction_clause,[],[f289])).

fof(f289,plain,
    ( $false
    | spl9_15 ),
    inference(resolution,[],[f274,f68])).

fof(f68,plain,(
    v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f274,plain,
    ( ~ v3_orders_2(sK2)
    | spl9_15 ),
    inference(avatar_component_clause,[],[f272])).

fof(f288,plain,(
    ~ spl9_11 ),
    inference(avatar_contradiction_clause,[],[f287])).

fof(f287,plain,
    ( $false
    | ~ spl9_11 ),
    inference(resolution,[],[f258,f67])).

fof(f67,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f258,plain,
    ( v2_struct_0(sK2)
    | ~ spl9_11 ),
    inference(avatar_component_clause,[],[f256])).

fof(f286,plain,(
    spl9_13 ),
    inference(avatar_contradiction_clause,[],[f285])).

fof(f285,plain,
    ( $false
    | spl9_13 ),
    inference(resolution,[],[f266,f71])).

fof(f71,plain,(
    v1_yellow_0(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f266,plain,
    ( ~ v1_yellow_0(sK2)
    | spl9_13 ),
    inference(avatar_component_clause,[],[f264])).

fof(f284,plain,(
    spl9_12 ),
    inference(avatar_contradiction_clause,[],[f283])).

fof(f283,plain,
    ( $false
    | spl9_12 ),
    inference(resolution,[],[f262,f70])).

fof(f70,plain,(
    v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f262,plain,
    ( ~ v5_orders_2(sK2)
    | spl9_12 ),
    inference(avatar_component_clause,[],[f260])).

fof(f282,plain,
    ( spl9_11
    | ~ spl9_15
    | ~ spl9_16
    | ~ spl9_12
    | ~ spl9_5
    | spl9_17 ),
    inference(avatar_split_clause,[],[f254,f280,f165,f260,f276,f272,f256])).

fof(f254,plain,(
    ! [X2,X1] :
      ( ~ r1_yellow_0(sK2,X1)
      | ~ r1_tarski(X1,k5_waybel_0(sK2,X2))
      | r1_orders_2(sK2,k1_yellow_0(sK2,X1),k1_yellow_0(sK2,k5_waybel_0(sK2,X2)))
      | ~ m1_subset_1(X2,u1_struct_0(sK2))
      | ~ l1_orders_2(sK2)
      | ~ v5_orders_2(sK2)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f230,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( r1_yellow_0(X0,k5_waybel_0(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f230,plain,(
    ! [X0,X1] :
      ( ~ r1_yellow_0(sK2,X0)
      | ~ r1_yellow_0(sK2,X1)
      | ~ r1_tarski(X1,X0)
      | r1_orders_2(sK2,k1_yellow_0(sK2,X1),k1_yellow_0(sK2,X0)) ) ),
    inference(resolution,[],[f93,f72])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_yellow_0(X0,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
          | ~ r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
          | ~ r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( ( r1_yellow_0(X0,X2)
            & r1_yellow_0(X0,X1)
            & r1_tarski(X1,X2) )
         => r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_yellow_0)).

fof(f218,plain,
    ( ~ spl9_7
    | ~ spl9_8
    | spl9_4 ),
    inference(avatar_split_clause,[],[f206,f145,f215,f211])).

fof(f206,plain,
    ( ~ r2_hidden(sK7(u1_struct_0(sK2),sK3),sK3)
    | ~ r2_hidden(sK7(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | spl9_4 ),
    inference(extensionality_resolution,[],[f106,f146])).

fof(f146,plain,
    ( u1_struct_0(sK2) != sK3
    | spl9_4 ),
    inference(avatar_component_clause,[],[f145])).

fof(f106,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK7(X0,X1),X1)
      | X0 = X1
      | ~ r2_hidden(sK7(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f182,plain,
    ( ~ spl9_1
    | ~ spl9_4 ),
    inference(avatar_contradiction_clause,[],[f181])).

fof(f181,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_4 ),
    inference(resolution,[],[f180,f123])).

fof(f123,plain,(
    ! [X0] : ~ v1_subset_1(X0,X0) ),
    inference(backward_demodulation,[],[f79,f80])).

fof(f80,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f79,plain,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_subset_1)).

fof(f180,plain,
    ( v1_subset_1(sK3,sK3)
    | ~ spl9_1
    | ~ spl9_4 ),
    inference(forward_demodulation,[],[f115,f147])).

fof(f147,plain,
    ( u1_struct_0(sK2) = sK3
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f145])).

fof(f115,plain,
    ( v1_subset_1(sK3,u1_struct_0(sK2))
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl9_1
  <=> v1_subset_1(sK3,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f179,plain,
    ( spl9_2
    | ~ spl9_6 ),
    inference(avatar_contradiction_clause,[],[f176])).

fof(f176,plain,
    ( $false
    | spl9_2
    | ~ spl9_6 ),
    inference(resolution,[],[f175,f119])).

fof(f119,plain,
    ( ~ r2_hidden(k3_yellow_0(sK2),sK3)
    | spl9_2 ),
    inference(avatar_component_clause,[],[f118])).

fof(f174,plain,(
    spl9_5 ),
    inference(avatar_contradiction_clause,[],[f173])).

fof(f173,plain,
    ( $false
    | spl9_5 ),
    inference(resolution,[],[f167,f72])).

fof(f167,plain,
    ( ~ l1_orders_2(sK2)
    | spl9_5 ),
    inference(avatar_component_clause,[],[f165])).

fof(f172,plain,
    ( ~ spl9_5
    | spl9_6
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f163,f145,f169,f165])).

fof(f163,plain,
    ( m1_subset_1(k3_yellow_0(sK2),sK3)
    | ~ l1_orders_2(sK2)
    | ~ spl9_4 ),
    inference(superposition,[],[f82,f147])).

fof(f153,plain,(
    spl9_3 ),
    inference(avatar_contradiction_clause,[],[f151])).

fof(f151,plain,
    ( $false
    | spl9_3 ),
    inference(resolution,[],[f143,f76])).

fof(f76,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f50])).

fof(f143,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | spl9_3 ),
    inference(avatar_component_clause,[],[f141])).

fof(f148,plain,
    ( ~ spl9_3
    | spl9_4
    | spl9_1 ),
    inference(avatar_split_clause,[],[f138,f114,f145,f141])).

fof(f138,plain,
    ( u1_struct_0(sK2) = sK3
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | spl9_1 ),
    inference(resolution,[],[f103,f116])).

fof(f116,plain,
    ( ~ v1_subset_1(sK3,u1_struct_0(sK2))
    | spl9_1 ),
    inference(avatar_component_clause,[],[f114])).

fof(f103,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

fof(f122,plain,
    ( spl9_1
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f77,f118,f114])).

fof(f77,plain,
    ( ~ r2_hidden(k3_yellow_0(sK2),sK3)
    | v1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f50])).

fof(f121,plain,
    ( ~ spl9_1
    | spl9_2 ),
    inference(avatar_split_clause,[],[f78,f118,f114])).

fof(f78,plain,
    ( r2_hidden(k3_yellow_0(sK2),sK3)
    | ~ v1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f50])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:19:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (2055)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (2063)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.28/0.53  % (2072)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.28/0.53  % (2078)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.42/0.54  % (2077)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.42/0.55  % (2054)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.42/0.56  % (2080)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.42/0.56  % (2071)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.42/0.56  % (2058)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.42/0.56  % (2064)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.42/0.57  % (2056)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.42/0.57  % (2068)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.42/0.57  % (2050)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.42/0.58  % (2076)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.42/0.58  % (2058)Refutation not found, incomplete strategy% (2058)------------------------------
% 1.42/0.58  % (2058)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.58  % (2058)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.58  
% 1.42/0.58  % (2058)Memory used [KB]: 10746
% 1.42/0.58  % (2058)Time elapsed: 0.120 s
% 1.42/0.58  % (2058)------------------------------
% 1.42/0.58  % (2058)------------------------------
% 1.42/0.58  % (2062)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.42/0.59  % (2053)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.42/0.60  % (2057)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.42/0.60  % (2052)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.42/0.61  % (2067)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.42/0.61  % (2062)Refutation found. Thanks to Tanya!
% 1.42/0.61  % SZS status Theorem for theBenchmark
% 1.42/0.61  % SZS output start Proof for theBenchmark
% 1.42/0.61  fof(f598,plain,(
% 1.42/0.61    $false),
% 1.42/0.61    inference(avatar_sat_refutation,[],[f121,f122,f148,f153,f172,f174,f179,f182,f218,f282,f284,f286,f288,f290,f292,f377,f428,f490,f501,f507,f527,f537,f547,f558,f562,f592,f593,f597])).
% 1.42/0.61  fof(f597,plain,(
% 1.42/0.61    spl9_44 | ~spl9_45 | ~spl9_2 | ~spl9_42),
% 1.42/0.61    inference(avatar_split_clause,[],[f594,f505,f118,f524,f521])).
% 1.42/0.61  fof(f521,plain,(
% 1.42/0.61    spl9_44 <=> ! [X1] : (~r1_tarski(k1_xboole_0,k5_waybel_0(sK2,X1)) | ~m1_subset_1(X1,u1_struct_0(sK2)) | r2_hidden(X1,sK3))),
% 1.42/0.61    introduced(avatar_definition,[new_symbols(naming,[spl9_44])])).
% 1.42/0.61  fof(f524,plain,(
% 1.42/0.61    spl9_45 <=> sP0(sK3,sK2)),
% 1.42/0.61    introduced(avatar_definition,[new_symbols(naming,[spl9_45])])).
% 1.42/0.61  fof(f118,plain,(
% 1.42/0.61    spl9_2 <=> r2_hidden(k3_yellow_0(sK2),sK3)),
% 1.42/0.61    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 1.42/0.61  fof(f505,plain,(
% 1.42/0.61    spl9_42 <=> ! [X1,X0] : (~r1_tarski(k1_xboole_0,k5_waybel_0(sK2,X0)) | ~sP0(X1,sK2) | ~r2_hidden(k3_yellow_0(sK2),X1) | r2_hidden(X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK2)))),
% 1.42/0.61    introduced(avatar_definition,[new_symbols(naming,[spl9_42])])).
% 1.42/0.61  fof(f594,plain,(
% 1.42/0.61    ( ! [X0] : (~sP0(sK3,sK2) | ~r1_tarski(k1_xboole_0,k5_waybel_0(sK2,X0)) | r2_hidden(X0,sK3) | ~m1_subset_1(X0,u1_struct_0(sK2))) ) | (~spl9_2 | ~spl9_42)),
% 1.42/0.61    inference(resolution,[],[f120,f506])).
% 1.42/0.61  fof(f506,plain,(
% 1.42/0.61    ( ! [X0,X1] : (~r2_hidden(k3_yellow_0(sK2),X1) | ~sP0(X1,sK2) | ~r1_tarski(k1_xboole_0,k5_waybel_0(sK2,X0)) | r2_hidden(X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK2))) ) | ~spl9_42),
% 1.42/0.61    inference(avatar_component_clause,[],[f505])).
% 1.42/0.61  fof(f120,plain,(
% 1.42/0.61    r2_hidden(k3_yellow_0(sK2),sK3) | ~spl9_2),
% 1.42/0.61    inference(avatar_component_clause,[],[f118])).
% 1.42/0.61  fof(f593,plain,(
% 1.42/0.61    spl9_7 | spl9_4 | ~spl9_3),
% 1.42/0.61    inference(avatar_split_clause,[],[f472,f141,f145,f211])).
% 1.42/0.61  fof(f211,plain,(
% 1.42/0.61    spl9_7 <=> r2_hidden(sK7(u1_struct_0(sK2),sK3),u1_struct_0(sK2))),
% 1.42/0.61    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 1.42/0.61  fof(f145,plain,(
% 1.42/0.61    spl9_4 <=> u1_struct_0(sK2) = sK3),
% 1.42/0.61    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 1.42/0.61  fof(f141,plain,(
% 1.42/0.61    spl9_3 <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 1.42/0.61    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 1.42/0.61  fof(f472,plain,(
% 1.42/0.61    u1_struct_0(sK2) = sK3 | r2_hidden(sK7(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) | ~spl9_3),
% 1.42/0.61    inference(resolution,[],[f394,f142])).
% 1.42/0.61  fof(f142,plain,(
% 1.42/0.61    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) | ~spl9_3),
% 1.42/0.61    inference(avatar_component_clause,[],[f141])).
% 1.42/0.61  fof(f394,plain,(
% 1.42/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | r2_hidden(sK7(X0,X1),X0)) )),
% 1.42/0.61    inference(factoring,[],[f203])).
% 1.42/0.61  fof(f203,plain,(
% 1.42/0.61    ( ! [X2,X0,X1] : (r2_hidden(sK7(X0,X1),X0) | X0 = X1 | r2_hidden(sK7(X0,X1),X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2))) )),
% 1.42/0.61    inference(resolution,[],[f105,f104])).
% 1.42/0.61  fof(f104,plain,(
% 1.42/0.61    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | r2_hidden(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.42/0.61    inference(cnf_transformation,[],[f37])).
% 1.42/0.61  fof(f37,plain,(
% 1.42/0.61    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.42/0.61    inference(ennf_transformation,[],[f4])).
% 1.42/0.61  fof(f4,axiom,(
% 1.42/0.61    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.42/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 1.42/0.61  fof(f105,plain,(
% 1.42/0.61    ( ! [X0,X1] : (r2_hidden(sK7(X0,X1),X1) | X0 = X1 | r2_hidden(sK7(X0,X1),X0)) )),
% 1.42/0.61    inference(cnf_transformation,[],[f62])).
% 1.42/0.61  fof(f62,plain,(
% 1.42/0.61    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK7(X0,X1),X1) | ~r2_hidden(sK7(X0,X1),X0)) & (r2_hidden(sK7(X0,X1),X1) | r2_hidden(sK7(X0,X1),X0))))),
% 1.42/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f60,f61])).
% 1.42/0.61  fof(f61,plain,(
% 1.42/0.61    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK7(X0,X1),X1) | ~r2_hidden(sK7(X0,X1),X0)) & (r2_hidden(sK7(X0,X1),X1) | r2_hidden(sK7(X0,X1),X0))))),
% 1.42/0.61    introduced(choice_axiom,[])).
% 1.42/0.61  fof(f60,plain,(
% 1.42/0.61    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 1.42/0.61    inference(nnf_transformation,[],[f38])).
% 1.42/0.61  fof(f38,plain,(
% 1.42/0.61    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 1.42/0.61    inference(ennf_transformation,[],[f2])).
% 1.42/0.61  fof(f2,axiom,(
% 1.42/0.61    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 1.42/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).
% 1.42/0.61  fof(f592,plain,(
% 1.42/0.61    ~spl9_7 | spl9_8 | ~spl9_48),
% 1.42/0.61    inference(avatar_contradiction_clause,[],[f588])).
% 1.42/0.61  fof(f588,plain,(
% 1.42/0.61    $false | (~spl9_7 | spl9_8 | ~spl9_48)),
% 1.42/0.61    inference(resolution,[],[f574,f217])).
% 1.42/0.61  fof(f217,plain,(
% 1.42/0.61    ~r2_hidden(sK7(u1_struct_0(sK2),sK3),sK3) | spl9_8),
% 1.42/0.61    inference(avatar_component_clause,[],[f215])).
% 1.42/0.61  fof(f215,plain,(
% 1.42/0.61    spl9_8 <=> r2_hidden(sK7(u1_struct_0(sK2),sK3),sK3)),
% 1.42/0.61    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).
% 1.42/0.61  fof(f574,plain,(
% 1.42/0.61    r2_hidden(sK7(u1_struct_0(sK2),sK3),sK3) | (~spl9_7 | ~spl9_48)),
% 1.42/0.61    inference(resolution,[],[f569,f212])).
% 1.42/0.61  fof(f212,plain,(
% 1.42/0.61    r2_hidden(sK7(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) | ~spl9_7),
% 1.42/0.61    inference(avatar_component_clause,[],[f211])).
% 1.42/0.61  fof(f569,plain,(
% 1.42/0.61    ( ! [X4] : (~r2_hidden(X4,u1_struct_0(sK2)) | r2_hidden(X4,sK3)) ) | ~spl9_48),
% 1.42/0.61    inference(resolution,[],[f557,f100])).
% 1.42/0.61  fof(f100,plain,(
% 1.42/0.61    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 1.42/0.61    inference(cnf_transformation,[],[f33])).
% 1.42/0.61  fof(f33,plain,(
% 1.42/0.61    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.42/0.61    inference(ennf_transformation,[],[f8])).
% 1.42/0.61  fof(f8,axiom,(
% 1.42/0.61    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.42/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 1.42/0.61  fof(f557,plain,(
% 1.42/0.61    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK2)) | r2_hidden(X2,sK3)) ) | ~spl9_48),
% 1.42/0.61    inference(avatar_component_clause,[],[f556])).
% 1.42/0.62  % (2049)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.42/0.62  % (2073)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.42/0.62  % (2075)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.42/0.62  % (2074)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 2.08/0.63  % (2061)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 2.08/0.63  % (2079)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 2.08/0.63  % (2065)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 2.08/0.63  fof(f556,plain,(
% 2.08/0.63    spl9_48 <=> ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK2)) | r2_hidden(X2,sK3))),
% 2.08/0.63    introduced(avatar_definition,[new_symbols(naming,[spl9_48])])).
% 2.08/0.63  fof(f562,plain,(
% 2.08/0.63    ~spl9_47),
% 2.08/0.63    inference(avatar_contradiction_clause,[],[f559])).
% 2.08/0.63  fof(f559,plain,(
% 2.08/0.63    $false | ~spl9_47),
% 2.08/0.63    inference(resolution,[],[f554,f81])).
% 2.08/0.63  fof(f81,plain,(
% 2.08/0.63    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.08/0.63    inference(cnf_transformation,[],[f6])).
% 2.08/0.63  fof(f6,axiom,(
% 2.08/0.63    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.08/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 2.08/0.63  fof(f554,plain,(
% 2.08/0.63    ( ! [X3] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK6(X3)))) ) | ~spl9_47),
% 2.08/0.63    inference(avatar_component_clause,[],[f553])).
% 2.08/0.63  fof(f553,plain,(
% 2.08/0.63    spl9_47 <=> ! [X3] : ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK6(X3)))),
% 2.08/0.63    introduced(avatar_definition,[new_symbols(naming,[spl9_47])])).
% 2.08/0.63  fof(f558,plain,(
% 2.08/0.63    spl9_47 | spl9_48 | ~spl9_44),
% 2.08/0.63    inference(avatar_split_clause,[],[f550,f521,f556,f553])).
% 2.08/0.63  fof(f550,plain,(
% 2.08/0.63    ( ! [X2,X3] : (~m1_subset_1(X2,u1_struct_0(sK2)) | r2_hidden(X2,sK3) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK6(X3)))) ) | ~spl9_44),
% 2.08/0.63    inference(resolution,[],[f522,f130])).
% 2.08/0.63  fof(f130,plain,(
% 2.08/0.63    ( ! [X4,X5,X3] : (r1_tarski(X3,X5) | ~m1_subset_1(X3,k1_zfmisc_1(sK6(X4)))) )),
% 2.08/0.63    inference(resolution,[],[f127,f108])).
% 2.08/0.63  fof(f108,plain,(
% 2.08/0.63    ( ! [X0,X1] : (r2_hidden(sK8(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 2.08/0.63    inference(cnf_transformation,[],[f66])).
% 2.08/0.63  fof(f66,plain,(
% 2.08/0.63    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK8(X0,X1),X1) & r2_hidden(sK8(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.08/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f64,f65])).
% 2.08/0.63  fof(f65,plain,(
% 2.08/0.63    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK8(X0,X1),X1) & r2_hidden(sK8(X0,X1),X0)))),
% 2.08/0.63    introduced(choice_axiom,[])).
% 2.08/0.63  fof(f64,plain,(
% 2.08/0.63    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.08/0.63    inference(rectify,[],[f63])).
% 2.08/0.63  fof(f63,plain,(
% 2.08/0.63    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.08/0.63    inference(nnf_transformation,[],[f39])).
% 2.08/0.63  fof(f39,plain,(
% 2.08/0.63    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.08/0.63    inference(ennf_transformation,[],[f1])).
% 2.08/0.63  fof(f1,axiom,(
% 2.08/0.63    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.08/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 2.08/0.63  fof(f127,plain,(
% 2.08/0.63    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK6(X1)))) )),
% 2.08/0.63    inference(resolution,[],[f111,f99])).
% 2.08/0.63  fof(f99,plain,(
% 2.08/0.63    ( ! [X0] : (v1_xboole_0(sK6(X0))) )),
% 2.08/0.63    inference(cnf_transformation,[],[f58])).
% 2.08/0.63  fof(f58,plain,(
% 2.08/0.63    ! [X0] : (v1_xboole_0(sK6(X0)) & m1_subset_1(sK6(X0),k1_zfmisc_1(X0)))),
% 2.08/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f5,f57])).
% 2.08/0.63  fof(f57,plain,(
% 2.08/0.63    ! [X0] : (? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (v1_xboole_0(sK6(X0)) & m1_subset_1(sK6(X0),k1_zfmisc_1(X0))))),
% 2.08/0.63    introduced(choice_axiom,[])).
% 2.08/0.63  fof(f5,axiom,(
% 2.08/0.63    ! [X0] : ? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.08/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_subset_1)).
% 2.08/0.63  fof(f111,plain,(
% 2.08/0.63    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.08/0.63    inference(cnf_transformation,[],[f42])).
% 2.08/0.63  fof(f42,plain,(
% 2.08/0.63    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.08/0.63    inference(ennf_transformation,[],[f11])).
% 2.08/0.63  fof(f11,axiom,(
% 2.08/0.63    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 2.08/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 2.08/0.63  fof(f522,plain,(
% 2.08/0.63    ( ! [X1] : (~r1_tarski(k1_xboole_0,k5_waybel_0(sK2,X1)) | ~m1_subset_1(X1,u1_struct_0(sK2)) | r2_hidden(X1,sK3)) ) | ~spl9_44),
% 2.08/0.63    inference(avatar_component_clause,[],[f521])).
% 2.08/0.63  fof(f547,plain,(
% 2.08/0.63    spl9_46),
% 2.08/0.63    inference(avatar_contradiction_clause,[],[f542])).
% 2.08/0.63  fof(f542,plain,(
% 2.08/0.63    $false | spl9_46),
% 2.08/0.63    inference(resolution,[],[f536,f75])).
% 2.08/0.63  fof(f75,plain,(
% 2.08/0.63    v13_waybel_0(sK3,sK2)),
% 2.08/0.63    inference(cnf_transformation,[],[f50])).
% 2.08/0.63  fof(f50,plain,(
% 2.08/0.63    ((r2_hidden(k3_yellow_0(sK2),sK3) | ~v1_subset_1(sK3,u1_struct_0(sK2))) & (~r2_hidden(k3_yellow_0(sK2),sK3) | v1_subset_1(sK3,u1_struct_0(sK2))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) & v13_waybel_0(sK3,sK2) & v2_waybel_0(sK3,sK2) & ~v1_xboole_0(sK3)) & l1_orders_2(sK2) & v1_yellow_0(sK2) & v5_orders_2(sK2) & v4_orders_2(sK2) & v3_orders_2(sK2) & ~v2_struct_0(sK2)),
% 2.08/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f47,f49,f48])).
% 2.08/0.63  fof(f48,plain,(
% 2.08/0.63    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : ((r2_hidden(k3_yellow_0(sK2),X1) | ~v1_subset_1(X1,u1_struct_0(sK2))) & (~r2_hidden(k3_yellow_0(sK2),X1) | v1_subset_1(X1,u1_struct_0(sK2))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) & v13_waybel_0(X1,sK2) & v2_waybel_0(X1,sK2) & ~v1_xboole_0(X1)) & l1_orders_2(sK2) & v1_yellow_0(sK2) & v5_orders_2(sK2) & v4_orders_2(sK2) & v3_orders_2(sK2) & ~v2_struct_0(sK2))),
% 2.08/0.63    introduced(choice_axiom,[])).
% 2.08/0.63  fof(f49,plain,(
% 2.08/0.63    ? [X1] : ((r2_hidden(k3_yellow_0(sK2),X1) | ~v1_subset_1(X1,u1_struct_0(sK2))) & (~r2_hidden(k3_yellow_0(sK2),X1) | v1_subset_1(X1,u1_struct_0(sK2))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) & v13_waybel_0(X1,sK2) & v2_waybel_0(X1,sK2) & ~v1_xboole_0(X1)) => ((r2_hidden(k3_yellow_0(sK2),sK3) | ~v1_subset_1(sK3,u1_struct_0(sK2))) & (~r2_hidden(k3_yellow_0(sK2),sK3) | v1_subset_1(sK3,u1_struct_0(sK2))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) & v13_waybel_0(sK3,sK2) & v2_waybel_0(sK3,sK2) & ~v1_xboole_0(sK3))),
% 2.08/0.63    introduced(choice_axiom,[])).
% 2.08/0.63  fof(f47,plain,(
% 2.08/0.63    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 2.08/0.63    inference(flattening,[],[f46])).
% 2.08/0.63  fof(f46,plain,(
% 2.08/0.63    ? [X0] : (? [X1] : (((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 2.08/0.63    inference(nnf_transformation,[],[f22])).
% 2.08/0.63  fof(f22,plain,(
% 2.08/0.63    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 2.08/0.63    inference(flattening,[],[f21])).
% 2.08/0.63  fof(f21,plain,(
% 2.08/0.63    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1))) & (l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 2.08/0.63    inference(ennf_transformation,[],[f20])).
% 2.08/0.63  fof(f20,negated_conjecture,(
% 2.08/0.63    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 2.08/0.63    inference(negated_conjecture,[],[f19])).
% 2.08/0.63  fof(f19,conjecture,(
% 2.08/0.63    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 2.08/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_7)).
% 2.08/0.63  fof(f536,plain,(
% 2.08/0.63    ~v13_waybel_0(sK3,sK2) | spl9_46),
% 2.08/0.63    inference(avatar_component_clause,[],[f534])).
% 2.08/0.63  fof(f534,plain,(
% 2.08/0.63    spl9_46 <=> v13_waybel_0(sK3,sK2)),
% 2.08/0.63    introduced(avatar_definition,[new_symbols(naming,[spl9_46])])).
% 2.08/0.63  fof(f537,plain,(
% 2.08/0.63    ~spl9_3 | ~spl9_46 | spl9_45),
% 2.08/0.63    inference(avatar_split_clause,[],[f530,f524,f534,f141])).
% 2.08/0.63  fof(f530,plain,(
% 2.08/0.63    ~v13_waybel_0(sK3,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) | spl9_45),
% 2.08/0.63    inference(resolution,[],[f526,f133])).
% 2.08/0.63  fof(f133,plain,(
% 2.08/0.63    ( ! [X1] : (sP0(X1,sK2) | ~v13_waybel_0(X1,sK2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 2.08/0.63    inference(resolution,[],[f131,f84])).
% 2.08/0.63  fof(f84,plain,(
% 2.08/0.63    ( ! [X0,X1] : (~sP1(X0,X1) | ~v13_waybel_0(X1,X0) | sP0(X1,X0)) )),
% 2.08/0.63    inference(cnf_transformation,[],[f51])).
% 2.08/0.63  fof(f51,plain,(
% 2.08/0.63    ! [X0,X1] : (((v13_waybel_0(X1,X0) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~v13_waybel_0(X1,X0))) | ~sP1(X0,X1))),
% 2.08/0.63    inference(nnf_transformation,[],[f44])).
% 2.08/0.63  fof(f44,plain,(
% 2.08/0.63    ! [X0,X1] : ((v13_waybel_0(X1,X0) <=> sP0(X1,X0)) | ~sP1(X0,X1))),
% 2.08/0.63    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 2.08/0.63  fof(f131,plain,(
% 2.08/0.63    ( ! [X0] : (sP1(sK2,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 2.08/0.63    inference(resolution,[],[f92,f72])).
% 2.08/0.63  fof(f72,plain,(
% 2.08/0.63    l1_orders_2(sK2)),
% 2.08/0.63    inference(cnf_transformation,[],[f50])).
% 2.08/0.63  fof(f92,plain,(
% 2.08/0.63    ( ! [X0,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | sP1(X0,X1)) )),
% 2.08/0.63    inference(cnf_transformation,[],[f45])).
% 2.08/0.63  fof(f45,plain,(
% 2.08/0.63    ! [X0] : (! [X1] : (sP1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 2.08/0.63    inference(definition_folding,[],[f26,f44,f43])).
% 2.08/0.63  fof(f43,plain,(
% 2.08/0.63    ! [X1,X0] : (sP0(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))))),
% 2.08/0.63    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.08/0.63  fof(f26,plain,(
% 2.08/0.63    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 2.08/0.63    inference(flattening,[],[f25])).
% 2.08/0.63  fof(f25,plain,(
% 2.08/0.63    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : ((r2_hidden(X3,X1) | (~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 2.08/0.63    inference(ennf_transformation,[],[f16])).
% 2.08/0.63  fof(f16,axiom,(
% 2.08/0.63    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v13_waybel_0(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1)) => r2_hidden(X3,X1)))))))),
% 2.08/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_waybel_0)).
% 2.08/0.63  fof(f526,plain,(
% 2.08/0.63    ~sP0(sK3,sK2) | spl9_45),
% 2.08/0.63    inference(avatar_component_clause,[],[f524])).
% 2.08/0.63  fof(f527,plain,(
% 2.08/0.63    spl9_44 | ~spl9_45 | ~spl9_6 | ~spl9_42),
% 2.08/0.63    inference(avatar_split_clause,[],[f519,f505,f169,f524,f521])).
% 2.08/0.63  fof(f169,plain,(
% 2.08/0.63    spl9_6 <=> m1_subset_1(k3_yellow_0(sK2),sK3)),
% 2.08/0.63    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 2.08/0.63  fof(f519,plain,(
% 2.08/0.63    ( ! [X1] : (~sP0(sK3,sK2) | ~r1_tarski(k1_xboole_0,k5_waybel_0(sK2,X1)) | r2_hidden(X1,sK3) | ~m1_subset_1(X1,u1_struct_0(sK2))) ) | (~spl9_6 | ~spl9_42)),
% 2.08/0.63    inference(resolution,[],[f506,f175])).
% 2.08/0.63  fof(f175,plain,(
% 2.08/0.63    r2_hidden(k3_yellow_0(sK2),sK3) | ~spl9_6),
% 2.08/0.63    inference(resolution,[],[f171,f124])).
% 2.08/0.63  fof(f124,plain,(
% 2.08/0.63    ( ! [X0] : (~m1_subset_1(X0,sK3) | r2_hidden(X0,sK3)) )),
% 2.08/0.63    inference(resolution,[],[f101,f73])).
% 2.08/0.63  fof(f73,plain,(
% 2.08/0.63    ~v1_xboole_0(sK3)),
% 2.08/0.63    inference(cnf_transformation,[],[f50])).
% 2.08/0.63  fof(f101,plain,(
% 2.08/0.63    ( ! [X0,X1] : (v1_xboole_0(X1) | r2_hidden(X0,X1) | ~m1_subset_1(X0,X1)) )),
% 2.08/0.63    inference(cnf_transformation,[],[f35])).
% 2.08/0.63  fof(f35,plain,(
% 2.08/0.63    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.08/0.63    inference(flattening,[],[f34])).
% 2.08/0.63  fof(f34,plain,(
% 2.08/0.63    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.08/0.63    inference(ennf_transformation,[],[f9])).
% 2.08/0.63  fof(f9,axiom,(
% 2.08/0.63    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.08/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 2.08/0.63  fof(f171,plain,(
% 2.08/0.63    m1_subset_1(k3_yellow_0(sK2),sK3) | ~spl9_6),
% 2.08/0.63    inference(avatar_component_clause,[],[f169])).
% 2.08/0.63  fof(f507,plain,(
% 2.08/0.63    ~spl9_26 | spl9_42 | ~spl9_41),
% 2.08/0.63    inference(avatar_split_clause,[],[f503,f499,f505,f350])).
% 2.08/0.63  fof(f350,plain,(
% 2.08/0.63    spl9_26 <=> m1_subset_1(k3_yellow_0(sK2),u1_struct_0(sK2))),
% 2.08/0.63    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).
% 2.08/0.63  fof(f499,plain,(
% 2.08/0.63    spl9_41 <=> ! [X0] : (r1_orders_2(sK2,k3_yellow_0(sK2),X0) | ~r1_tarski(k1_xboole_0,k5_waybel_0(sK2,X0)) | ~m1_subset_1(X0,u1_struct_0(sK2)))),
% 2.08/0.63    introduced(avatar_definition,[new_symbols(naming,[spl9_41])])).
% 2.08/0.63  fof(f503,plain,(
% 2.08/0.63    ( ! [X0,X1] : (~r1_tarski(k1_xboole_0,k5_waybel_0(sK2,X0)) | ~m1_subset_1(X0,u1_struct_0(sK2)) | r2_hidden(X0,X1) | ~r2_hidden(k3_yellow_0(sK2),X1) | ~m1_subset_1(k3_yellow_0(sK2),u1_struct_0(sK2)) | ~sP0(X1,sK2)) ) | ~spl9_41),
% 2.08/0.63    inference(duplicate_literal_removal,[],[f502])).
% 2.08/0.63  fof(f502,plain,(
% 2.08/0.63    ( ! [X0,X1] : (~r1_tarski(k1_xboole_0,k5_waybel_0(sK2,X0)) | ~m1_subset_1(X0,u1_struct_0(sK2)) | r2_hidden(X0,X1) | ~r2_hidden(k3_yellow_0(sK2),X1) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~m1_subset_1(k3_yellow_0(sK2),u1_struct_0(sK2)) | ~sP0(X1,sK2)) ) | ~spl9_41),
% 2.08/0.63    inference(resolution,[],[f500,f86])).
% 2.08/0.63  fof(f86,plain,(
% 2.08/0.63    ( ! [X4,X0,X5,X1] : (~r1_orders_2(X1,X4,X5) | r2_hidden(X5,X0) | ~r2_hidden(X4,X0) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~sP0(X0,X1)) )),
% 2.08/0.63    inference(cnf_transformation,[],[f56])).
% 2.08/0.63  fof(f56,plain,(
% 2.08/0.63    ! [X0,X1] : ((sP0(X0,X1) | ((~r2_hidden(sK5(X0,X1),X0) & r1_orders_2(X1,sK4(X0,X1),sK5(X0,X1)) & r2_hidden(sK4(X0,X1),X0) & m1_subset_1(sK5(X0,X1),u1_struct_0(X1))) & m1_subset_1(sK4(X0,X1),u1_struct_0(X1)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X0) | ~r1_orders_2(X1,X4,X5) | ~r2_hidden(X4,X0) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP0(X0,X1)))),
% 2.08/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f53,f55,f54])).
% 2.08/0.63  fof(f54,plain,(
% 2.08/0.63    ! [X1,X0] : (? [X2] : (? [X3] : (~r2_hidden(X3,X0) & r1_orders_2(X1,X2,X3) & r2_hidden(X2,X0) & m1_subset_1(X3,u1_struct_0(X1))) & m1_subset_1(X2,u1_struct_0(X1))) => (? [X3] : (~r2_hidden(X3,X0) & r1_orders_2(X1,sK4(X0,X1),X3) & r2_hidden(sK4(X0,X1),X0) & m1_subset_1(X3,u1_struct_0(X1))) & m1_subset_1(sK4(X0,X1),u1_struct_0(X1))))),
% 2.08/0.63    introduced(choice_axiom,[])).
% 2.08/0.63  fof(f55,plain,(
% 2.08/0.63    ! [X1,X0] : (? [X3] : (~r2_hidden(X3,X0) & r1_orders_2(X1,sK4(X0,X1),X3) & r2_hidden(sK4(X0,X1),X0) & m1_subset_1(X3,u1_struct_0(X1))) => (~r2_hidden(sK5(X0,X1),X0) & r1_orders_2(X1,sK4(X0,X1),sK5(X0,X1)) & r2_hidden(sK4(X0,X1),X0) & m1_subset_1(sK5(X0,X1),u1_struct_0(X1))))),
% 2.08/0.63    introduced(choice_axiom,[])).
% 2.08/0.63  fof(f53,plain,(
% 2.08/0.63    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : (? [X3] : (~r2_hidden(X3,X0) & r1_orders_2(X1,X2,X3) & r2_hidden(X2,X0) & m1_subset_1(X3,u1_struct_0(X1))) & m1_subset_1(X2,u1_struct_0(X1)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X0) | ~r1_orders_2(X1,X4,X5) | ~r2_hidden(X4,X0) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP0(X0,X1)))),
% 2.08/0.63    inference(rectify,[],[f52])).
% 2.08/0.63  fof(f52,plain,(
% 2.08/0.63    ! [X1,X0] : ((sP0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~sP0(X1,X0)))),
% 2.08/0.63    inference(nnf_transformation,[],[f43])).
% 2.08/0.63  fof(f500,plain,(
% 2.08/0.63    ( ! [X0] : (r1_orders_2(sK2,k3_yellow_0(sK2),X0) | ~r1_tarski(k1_xboole_0,k5_waybel_0(sK2,X0)) | ~m1_subset_1(X0,u1_struct_0(sK2))) ) | ~spl9_41),
% 2.08/0.63    inference(avatar_component_clause,[],[f499])).
% 2.08/0.63  fof(f501,plain,(
% 2.08/0.63    ~spl9_5 | spl9_41 | ~spl9_39),
% 2.08/0.63    inference(avatar_split_clause,[],[f492,f488,f499,f165])).
% 2.08/0.63  fof(f165,plain,(
% 2.08/0.63    spl9_5 <=> l1_orders_2(sK2)),
% 2.08/0.63    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 2.08/0.63  fof(f488,plain,(
% 2.08/0.63    spl9_39 <=> ! [X0] : (r1_orders_2(sK2,k1_yellow_0(sK2,k1_xboole_0),X0) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~r1_tarski(k1_xboole_0,k5_waybel_0(sK2,X0)))),
% 2.08/0.63    introduced(avatar_definition,[new_symbols(naming,[spl9_39])])).
% 2.08/0.63  fof(f492,plain,(
% 2.08/0.63    ( ! [X0] : (r1_orders_2(sK2,k3_yellow_0(sK2),X0) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~r1_tarski(k1_xboole_0,k5_waybel_0(sK2,X0)) | ~l1_orders_2(sK2)) ) | ~spl9_39),
% 2.08/0.63    inference(superposition,[],[f489,f83])).
% 2.08/0.63  fof(f83,plain,(
% 2.08/0.63    ( ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0)) )),
% 2.08/0.63    inference(cnf_transformation,[],[f24])).
% 2.08/0.63  fof(f24,plain,(
% 2.08/0.63    ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0))),
% 2.08/0.63    inference(ennf_transformation,[],[f12])).
% 2.08/0.63  fof(f12,axiom,(
% 2.08/0.63    ! [X0] : (l1_orders_2(X0) => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0))),
% 2.08/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_yellow_0)).
% 2.08/0.63  fof(f489,plain,(
% 2.08/0.63    ( ! [X0] : (r1_orders_2(sK2,k1_yellow_0(sK2,k1_xboole_0),X0) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~r1_tarski(k1_xboole_0,k5_waybel_0(sK2,X0))) ) | ~spl9_39),
% 2.08/0.63    inference(avatar_component_clause,[],[f488])).
% 2.08/0.63  fof(f490,plain,(
% 2.08/0.63    spl9_11 | ~spl9_15 | ~spl9_16 | ~spl9_12 | ~spl9_5 | spl9_39 | ~spl9_31),
% 2.08/0.63    inference(avatar_split_clause,[],[f478,f426,f488,f165,f260,f276,f272,f256])).
% 2.08/0.63  fof(f256,plain,(
% 2.08/0.63    spl9_11 <=> v2_struct_0(sK2)),
% 2.08/0.63    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).
% 2.08/0.63  fof(f272,plain,(
% 2.08/0.63    spl9_15 <=> v3_orders_2(sK2)),
% 2.08/0.63    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).
% 2.08/0.63  fof(f276,plain,(
% 2.08/0.63    spl9_16 <=> v4_orders_2(sK2)),
% 2.08/0.63    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).
% 2.08/0.63  fof(f260,plain,(
% 2.08/0.63    spl9_12 <=> v5_orders_2(sK2)),
% 2.08/0.63    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).
% 2.08/0.63  fof(f426,plain,(
% 2.08/0.63    spl9_31 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK2)) | ~r1_tarski(k1_xboole_0,k5_waybel_0(sK2,X0)) | r1_orders_2(sK2,k1_yellow_0(sK2,k1_xboole_0),k1_yellow_0(sK2,k5_waybel_0(sK2,X0))))),
% 2.08/0.63    introduced(avatar_definition,[new_symbols(naming,[spl9_31])])).
% 2.08/0.63  fof(f478,plain,(
% 2.08/0.63    ( ! [X0] : (r1_orders_2(sK2,k1_yellow_0(sK2,k1_xboole_0),X0) | ~r1_tarski(k1_xboole_0,k5_waybel_0(sK2,X0)) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~l1_orders_2(sK2) | ~v5_orders_2(sK2) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | v2_struct_0(sK2)) ) | ~spl9_31),
% 2.08/0.63    inference(duplicate_literal_removal,[],[f477])).
% 2.08/0.63  fof(f477,plain,(
% 2.08/0.63    ( ! [X0] : (r1_orders_2(sK2,k1_yellow_0(sK2,k1_xboole_0),X0) | ~r1_tarski(k1_xboole_0,k5_waybel_0(sK2,X0)) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~l1_orders_2(sK2) | ~v5_orders_2(sK2) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | v2_struct_0(sK2)) ) | ~spl9_31),
% 2.08/0.63    inference(superposition,[],[f427,f95])).
% 2.08/0.63  fof(f95,plain,(
% 2.08/0.63    ( ! [X0,X1] : (k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.08/0.63    inference(cnf_transformation,[],[f30])).
% 2.08/0.63  fof(f30,plain,(
% 2.08/0.63    ! [X0] : (! [X1] : ((k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1 & r1_yellow_0(X0,k5_waybel_0(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.08/0.63    inference(flattening,[],[f29])).
% 2.08/0.63  fof(f29,plain,(
% 2.08/0.63    ! [X0] : (! [X1] : ((k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1 & r1_yellow_0(X0,k5_waybel_0(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.08/0.63    inference(ennf_transformation,[],[f17])).
% 2.08/0.63  fof(f17,axiom,(
% 2.08/0.63    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1 & r1_yellow_0(X0,k5_waybel_0(X0,X1)))))),
% 2.08/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_waybel_0)).
% 2.08/0.63  fof(f427,plain,(
% 2.08/0.63    ( ! [X0] : (r1_orders_2(sK2,k1_yellow_0(sK2,k1_xboole_0),k1_yellow_0(sK2,k5_waybel_0(sK2,X0))) | ~r1_tarski(k1_xboole_0,k5_waybel_0(sK2,X0)) | ~m1_subset_1(X0,u1_struct_0(sK2))) ) | ~spl9_31),
% 2.08/0.63    inference(avatar_component_clause,[],[f426])).
% 2.08/0.63  fof(f428,plain,(
% 2.08/0.63    spl9_11 | ~spl9_12 | ~spl9_13 | ~spl9_5 | spl9_31 | ~spl9_17),
% 2.08/0.63    inference(avatar_split_clause,[],[f423,f280,f426,f165,f264,f260,f256])).
% 2.08/0.63  fof(f264,plain,(
% 2.08/0.63    spl9_13 <=> v1_yellow_0(sK2)),
% 2.08/0.63    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).
% 2.08/0.63  fof(f280,plain,(
% 2.08/0.63    spl9_17 <=> ! [X1,X2] : (~r1_yellow_0(sK2,X1) | ~m1_subset_1(X2,u1_struct_0(sK2)) | r1_orders_2(sK2,k1_yellow_0(sK2,X1),k1_yellow_0(sK2,k5_waybel_0(sK2,X2))) | ~r1_tarski(X1,k5_waybel_0(sK2,X2)))),
% 2.08/0.63    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).
% 2.08/0.63  fof(f423,plain,(
% 2.08/0.63    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK2)) | r1_orders_2(sK2,k1_yellow_0(sK2,k1_xboole_0),k1_yellow_0(sK2,k5_waybel_0(sK2,X0))) | ~r1_tarski(k1_xboole_0,k5_waybel_0(sK2,X0)) | ~l1_orders_2(sK2) | ~v1_yellow_0(sK2) | ~v5_orders_2(sK2) | v2_struct_0(sK2)) ) | ~spl9_17),
% 2.08/0.63    inference(resolution,[],[f281,f96])).
% 2.08/0.63  fof(f96,plain,(
% 2.08/0.63    ( ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 2.08/0.63    inference(cnf_transformation,[],[f32])).
% 2.08/0.63  fof(f32,plain,(
% 2.08/0.63    ! [X0] : ((r2_yellow_0(X0,u1_struct_0(X0)) & r1_yellow_0(X0,k1_xboole_0)) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.08/0.63    inference(flattening,[],[f31])).
% 2.08/0.63  fof(f31,plain,(
% 2.08/0.63    ! [X0] : ((r2_yellow_0(X0,u1_struct_0(X0)) & r1_yellow_0(X0,k1_xboole_0)) | (~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 2.08/0.63    inference(ennf_transformation,[],[f15])).
% 2.08/0.63  fof(f15,axiom,(
% 2.08/0.63    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => (r2_yellow_0(X0,u1_struct_0(X0)) & r1_yellow_0(X0,k1_xboole_0)))),
% 2.08/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_yellow_0)).
% 2.08/0.63  fof(f281,plain,(
% 2.08/0.63    ( ! [X2,X1] : (~r1_yellow_0(sK2,X1) | ~m1_subset_1(X2,u1_struct_0(sK2)) | r1_orders_2(sK2,k1_yellow_0(sK2,X1),k1_yellow_0(sK2,k5_waybel_0(sK2,X2))) | ~r1_tarski(X1,k5_waybel_0(sK2,X2))) ) | ~spl9_17),
% 2.08/0.63    inference(avatar_component_clause,[],[f280])).
% 2.08/0.63  fof(f377,plain,(
% 2.08/0.63    spl9_26),
% 2.08/0.63    inference(avatar_contradiction_clause,[],[f376])).
% 2.08/0.63  fof(f376,plain,(
% 2.08/0.63    $false | spl9_26),
% 2.08/0.63    inference(resolution,[],[f373,f72])).
% 2.08/0.63  fof(f373,plain,(
% 2.08/0.63    ~l1_orders_2(sK2) | spl9_26),
% 2.08/0.63    inference(resolution,[],[f352,f82])).
% 2.08/0.63  fof(f82,plain,(
% 2.08/0.63    ( ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 2.08/0.63    inference(cnf_transformation,[],[f23])).
% 2.08/0.63  fof(f23,plain,(
% 2.08/0.63    ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 2.08/0.63    inference(ennf_transformation,[],[f13])).
% 2.08/0.63  fof(f13,axiom,(
% 2.08/0.63    ! [X0] : (l1_orders_2(X0) => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)))),
% 2.08/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow_0)).
% 2.08/0.63  fof(f352,plain,(
% 2.08/0.63    ~m1_subset_1(k3_yellow_0(sK2),u1_struct_0(sK2)) | spl9_26),
% 2.08/0.63    inference(avatar_component_clause,[],[f350])).
% 2.08/0.63  fof(f292,plain,(
% 2.08/0.63    spl9_16),
% 2.08/0.63    inference(avatar_contradiction_clause,[],[f291])).
% 2.08/0.63  fof(f291,plain,(
% 2.08/0.63    $false | spl9_16),
% 2.08/0.63    inference(resolution,[],[f278,f69])).
% 2.08/0.63  fof(f69,plain,(
% 2.08/0.63    v4_orders_2(sK2)),
% 2.08/0.63    inference(cnf_transformation,[],[f50])).
% 2.08/0.63  fof(f278,plain,(
% 2.08/0.63    ~v4_orders_2(sK2) | spl9_16),
% 2.08/0.63    inference(avatar_component_clause,[],[f276])).
% 2.08/0.63  fof(f290,plain,(
% 2.08/0.63    spl9_15),
% 2.08/0.63    inference(avatar_contradiction_clause,[],[f289])).
% 2.08/0.63  fof(f289,plain,(
% 2.08/0.63    $false | spl9_15),
% 2.08/0.63    inference(resolution,[],[f274,f68])).
% 2.08/0.63  fof(f68,plain,(
% 2.08/0.63    v3_orders_2(sK2)),
% 2.08/0.63    inference(cnf_transformation,[],[f50])).
% 2.08/0.63  fof(f274,plain,(
% 2.08/0.63    ~v3_orders_2(sK2) | spl9_15),
% 2.08/0.63    inference(avatar_component_clause,[],[f272])).
% 2.08/0.63  fof(f288,plain,(
% 2.08/0.63    ~spl9_11),
% 2.08/0.63    inference(avatar_contradiction_clause,[],[f287])).
% 2.08/0.63  fof(f287,plain,(
% 2.08/0.63    $false | ~spl9_11),
% 2.08/0.63    inference(resolution,[],[f258,f67])).
% 2.08/0.63  fof(f67,plain,(
% 2.08/0.63    ~v2_struct_0(sK2)),
% 2.08/0.63    inference(cnf_transformation,[],[f50])).
% 2.08/0.63  fof(f258,plain,(
% 2.08/0.63    v2_struct_0(sK2) | ~spl9_11),
% 2.08/0.63    inference(avatar_component_clause,[],[f256])).
% 2.08/0.63  fof(f286,plain,(
% 2.08/0.63    spl9_13),
% 2.08/0.63    inference(avatar_contradiction_clause,[],[f285])).
% 2.08/0.63  fof(f285,plain,(
% 2.08/0.63    $false | spl9_13),
% 2.08/0.63    inference(resolution,[],[f266,f71])).
% 2.08/0.63  fof(f71,plain,(
% 2.08/0.63    v1_yellow_0(sK2)),
% 2.08/0.63    inference(cnf_transformation,[],[f50])).
% 2.08/0.63  fof(f266,plain,(
% 2.08/0.63    ~v1_yellow_0(sK2) | spl9_13),
% 2.08/0.63    inference(avatar_component_clause,[],[f264])).
% 2.08/0.63  fof(f284,plain,(
% 2.08/0.63    spl9_12),
% 2.08/0.63    inference(avatar_contradiction_clause,[],[f283])).
% 2.08/0.63  fof(f283,plain,(
% 2.08/0.63    $false | spl9_12),
% 2.08/0.63    inference(resolution,[],[f262,f70])).
% 2.08/0.63  fof(f70,plain,(
% 2.08/0.63    v5_orders_2(sK2)),
% 2.08/0.63    inference(cnf_transformation,[],[f50])).
% 2.08/0.63  fof(f262,plain,(
% 2.08/0.63    ~v5_orders_2(sK2) | spl9_12),
% 2.08/0.63    inference(avatar_component_clause,[],[f260])).
% 2.08/0.63  fof(f282,plain,(
% 2.08/0.63    spl9_11 | ~spl9_15 | ~spl9_16 | ~spl9_12 | ~spl9_5 | spl9_17),
% 2.08/0.63    inference(avatar_split_clause,[],[f254,f280,f165,f260,f276,f272,f256])).
% 2.08/0.63  fof(f254,plain,(
% 2.08/0.63    ( ! [X2,X1] : (~r1_yellow_0(sK2,X1) | ~r1_tarski(X1,k5_waybel_0(sK2,X2)) | r1_orders_2(sK2,k1_yellow_0(sK2,X1),k1_yellow_0(sK2,k5_waybel_0(sK2,X2))) | ~m1_subset_1(X2,u1_struct_0(sK2)) | ~l1_orders_2(sK2) | ~v5_orders_2(sK2) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | v2_struct_0(sK2)) )),
% 2.08/0.63    inference(resolution,[],[f230,f94])).
% 2.08/0.63  fof(f94,plain,(
% 2.08/0.63    ( ! [X0,X1] : (r1_yellow_0(X0,k5_waybel_0(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.08/0.63    inference(cnf_transformation,[],[f30])).
% 2.08/0.63  fof(f230,plain,(
% 2.08/0.63    ( ! [X0,X1] : (~r1_yellow_0(sK2,X0) | ~r1_yellow_0(sK2,X1) | ~r1_tarski(X1,X0) | r1_orders_2(sK2,k1_yellow_0(sK2,X1),k1_yellow_0(sK2,X0))) )),
% 2.08/0.63    inference(resolution,[],[f93,f72])).
% 2.08/0.63  fof(f93,plain,(
% 2.08/0.63    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~r1_yellow_0(X0,X2) | ~r1_yellow_0(X0,X1) | ~r1_tarski(X1,X2) | r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))) )),
% 2.08/0.63    inference(cnf_transformation,[],[f28])).
% 2.08/0.63  fof(f28,plain,(
% 2.08/0.63    ! [X0] : (! [X1,X2] : (r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) | ~r1_yellow_0(X0,X2) | ~r1_yellow_0(X0,X1) | ~r1_tarski(X1,X2)) | ~l1_orders_2(X0))),
% 2.08/0.63    inference(flattening,[],[f27])).
% 2.08/0.63  fof(f27,plain,(
% 2.08/0.63    ! [X0] : (! [X1,X2] : (r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) | (~r1_yellow_0(X0,X2) | ~r1_yellow_0(X0,X1) | ~r1_tarski(X1,X2))) | ~l1_orders_2(X0))),
% 2.08/0.63    inference(ennf_transformation,[],[f14])).
% 2.08/0.63  fof(f14,axiom,(
% 2.08/0.63    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : ((r1_yellow_0(X0,X2) & r1_yellow_0(X0,X1) & r1_tarski(X1,X2)) => r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))))),
% 2.08/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_yellow_0)).
% 2.08/0.63  fof(f218,plain,(
% 2.08/0.63    ~spl9_7 | ~spl9_8 | spl9_4),
% 2.08/0.63    inference(avatar_split_clause,[],[f206,f145,f215,f211])).
% 2.08/0.63  fof(f206,plain,(
% 2.08/0.63    ~r2_hidden(sK7(u1_struct_0(sK2),sK3),sK3) | ~r2_hidden(sK7(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) | spl9_4),
% 2.08/0.63    inference(extensionality_resolution,[],[f106,f146])).
% 2.08/0.63  fof(f146,plain,(
% 2.08/0.63    u1_struct_0(sK2) != sK3 | spl9_4),
% 2.08/0.63    inference(avatar_component_clause,[],[f145])).
% 2.08/0.63  fof(f106,plain,(
% 2.08/0.63    ( ! [X0,X1] : (~r2_hidden(sK7(X0,X1),X1) | X0 = X1 | ~r2_hidden(sK7(X0,X1),X0)) )),
% 2.08/0.63    inference(cnf_transformation,[],[f62])).
% 2.08/0.63  fof(f182,plain,(
% 2.08/0.63    ~spl9_1 | ~spl9_4),
% 2.08/0.63    inference(avatar_contradiction_clause,[],[f181])).
% 2.08/0.63  fof(f181,plain,(
% 2.08/0.63    $false | (~spl9_1 | ~spl9_4)),
% 2.08/0.63    inference(resolution,[],[f180,f123])).
% 2.08/0.63  fof(f123,plain,(
% 2.08/0.63    ( ! [X0] : (~v1_subset_1(X0,X0)) )),
% 2.08/0.63    inference(backward_demodulation,[],[f79,f80])).
% 2.08/0.63  fof(f80,plain,(
% 2.08/0.63    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 2.08/0.63    inference(cnf_transformation,[],[f3])).
% 2.08/0.63  fof(f3,axiom,(
% 2.08/0.63    ! [X0] : k2_subset_1(X0) = X0),
% 2.08/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 2.08/0.63  fof(f79,plain,(
% 2.08/0.63    ( ! [X0] : (~v1_subset_1(k2_subset_1(X0),X0)) )),
% 2.08/0.63    inference(cnf_transformation,[],[f7])).
% 2.08/0.63  fof(f7,axiom,(
% 2.08/0.63    ! [X0] : ~v1_subset_1(k2_subset_1(X0),X0)),
% 2.08/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_subset_1)).
% 2.08/0.63  fof(f180,plain,(
% 2.08/0.63    v1_subset_1(sK3,sK3) | (~spl9_1 | ~spl9_4)),
% 2.08/0.63    inference(forward_demodulation,[],[f115,f147])).
% 2.08/0.63  fof(f147,plain,(
% 2.08/0.63    u1_struct_0(sK2) = sK3 | ~spl9_4),
% 2.08/0.63    inference(avatar_component_clause,[],[f145])).
% 2.08/0.63  fof(f115,plain,(
% 2.08/0.63    v1_subset_1(sK3,u1_struct_0(sK2)) | ~spl9_1),
% 2.08/0.63    inference(avatar_component_clause,[],[f114])).
% 2.08/0.63  fof(f114,plain,(
% 2.08/0.63    spl9_1 <=> v1_subset_1(sK3,u1_struct_0(sK2))),
% 2.08/0.63    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 2.08/0.63  fof(f179,plain,(
% 2.08/0.63    spl9_2 | ~spl9_6),
% 2.08/0.63    inference(avatar_contradiction_clause,[],[f176])).
% 2.08/0.63  fof(f176,plain,(
% 2.08/0.63    $false | (spl9_2 | ~spl9_6)),
% 2.08/0.63    inference(resolution,[],[f175,f119])).
% 2.08/0.63  fof(f119,plain,(
% 2.08/0.63    ~r2_hidden(k3_yellow_0(sK2),sK3) | spl9_2),
% 2.08/0.63    inference(avatar_component_clause,[],[f118])).
% 2.08/0.63  fof(f174,plain,(
% 2.08/0.63    spl9_5),
% 2.08/0.63    inference(avatar_contradiction_clause,[],[f173])).
% 2.08/0.63  fof(f173,plain,(
% 2.08/0.63    $false | spl9_5),
% 2.08/0.63    inference(resolution,[],[f167,f72])).
% 2.08/0.63  fof(f167,plain,(
% 2.08/0.63    ~l1_orders_2(sK2) | spl9_5),
% 2.08/0.63    inference(avatar_component_clause,[],[f165])).
% 2.08/0.63  fof(f172,plain,(
% 2.08/0.63    ~spl9_5 | spl9_6 | ~spl9_4),
% 2.08/0.63    inference(avatar_split_clause,[],[f163,f145,f169,f165])).
% 2.08/0.63  fof(f163,plain,(
% 2.08/0.63    m1_subset_1(k3_yellow_0(sK2),sK3) | ~l1_orders_2(sK2) | ~spl9_4),
% 2.08/0.63    inference(superposition,[],[f82,f147])).
% 2.08/0.63  fof(f153,plain,(
% 2.08/0.63    spl9_3),
% 2.08/0.63    inference(avatar_contradiction_clause,[],[f151])).
% 2.08/0.63  fof(f151,plain,(
% 2.08/0.63    $false | spl9_3),
% 2.08/0.63    inference(resolution,[],[f143,f76])).
% 2.08/0.63  fof(f76,plain,(
% 2.08/0.63    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 2.08/0.63    inference(cnf_transformation,[],[f50])).
% 2.08/0.63  fof(f143,plain,(
% 2.08/0.63    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) | spl9_3),
% 2.08/0.63    inference(avatar_component_clause,[],[f141])).
% 2.08/0.63  fof(f148,plain,(
% 2.08/0.63    ~spl9_3 | spl9_4 | spl9_1),
% 2.08/0.63    inference(avatar_split_clause,[],[f138,f114,f145,f141])).
% 2.08/0.63  fof(f138,plain,(
% 2.08/0.63    u1_struct_0(sK2) = sK3 | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) | spl9_1),
% 2.08/0.63    inference(resolution,[],[f103,f116])).
% 2.08/0.63  fof(f116,plain,(
% 2.08/0.63    ~v1_subset_1(sK3,u1_struct_0(sK2)) | spl9_1),
% 2.08/0.63    inference(avatar_component_clause,[],[f114])).
% 2.08/0.63  fof(f103,plain,(
% 2.08/0.63    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.08/0.63    inference(cnf_transformation,[],[f59])).
% 2.08/0.63  fof(f59,plain,(
% 2.08/0.63    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.08/0.63    inference(nnf_transformation,[],[f36])).
% 2.08/0.63  fof(f36,plain,(
% 2.08/0.63    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.08/0.63    inference(ennf_transformation,[],[f18])).
% 2.08/0.63  fof(f18,axiom,(
% 2.08/0.63    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 2.08/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).
% 2.08/0.63  fof(f122,plain,(
% 2.08/0.63    spl9_1 | ~spl9_2),
% 2.08/0.63    inference(avatar_split_clause,[],[f77,f118,f114])).
% 2.08/0.63  fof(f77,plain,(
% 2.08/0.63    ~r2_hidden(k3_yellow_0(sK2),sK3) | v1_subset_1(sK3,u1_struct_0(sK2))),
% 2.08/0.63    inference(cnf_transformation,[],[f50])).
% 2.08/0.63  fof(f121,plain,(
% 2.08/0.63    ~spl9_1 | spl9_2),
% 2.08/0.63    inference(avatar_split_clause,[],[f78,f118,f114])).
% 2.08/0.63  fof(f78,plain,(
% 2.08/0.63    r2_hidden(k3_yellow_0(sK2),sK3) | ~v1_subset_1(sK3,u1_struct_0(sK2))),
% 2.08/0.63    inference(cnf_transformation,[],[f50])).
% 2.08/0.63  % SZS output end Proof for theBenchmark
% 2.08/0.63  % (2062)------------------------------
% 2.08/0.63  % (2062)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.08/0.63  % (2062)Termination reason: Refutation
% 2.08/0.63  
% 2.08/0.63  % (2062)Memory used [KB]: 6524
% 2.08/0.63  % (2062)Time elapsed: 0.193 s
% 2.08/0.63  % (2062)------------------------------
% 2.08/0.63  % (2062)------------------------------
% 2.08/0.63  % (2048)Success in time 0.273 s
%------------------------------------------------------------------------------
