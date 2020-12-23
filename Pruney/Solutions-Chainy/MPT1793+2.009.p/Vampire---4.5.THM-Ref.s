%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:27 EST 2020

% Result     : Theorem 1.74s
% Output     : Refutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :  196 ( 814 expanded)
%              Number of leaves         :   33 ( 342 expanded)
%              Depth                    :   26
%              Number of atoms          :  837 (6239 expanded)
%              Number of equality atoms :   13 (  14 expanded)
%              Maximal formula depth    :   23 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f807,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f121,f127,f130,f146,f301,f351,f419,f450,f794,f806])).

fof(f806,plain,
    ( ~ spl8_4
    | ~ spl8_21 ),
    inference(avatar_contradiction_clause,[],[f805])).

fof(f805,plain,
    ( $false
    | ~ spl8_4
    | ~ spl8_21 ),
    inference(subsumption_resolution,[],[f350,f455])).

fof(f455,plain,
    ( ~ r2_hidden(sK3,sK1)
    | ~ spl8_4 ),
    inference(resolution,[],[f141,f134])).

fof(f134,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,u1_struct_0(sK2))
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f71,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK6(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f35,f56])).

fof(f56,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f71,plain,(
    r1_xboole_0(u1_struct_0(sK2),sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,
    ( ~ r1_tmap_1(sK2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),sK3)
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & r1_xboole_0(u1_struct_0(sK2),sK1)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f48,f47,f46,f45])).

fof(f45,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
                    & m1_subset_1(X3,u1_struct_0(X2)) )
                & r1_xboole_0(u1_struct_0(X2),X1)
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tmap_1(X2,k6_tmap_1(sK0,X1),k2_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),X2),X3)
                  & m1_subset_1(X3,u1_struct_0(X2)) )
              & r1_xboole_0(u1_struct_0(X2),X1)
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ r1_tmap_1(X2,k6_tmap_1(sK0,X1),k2_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),X2),X3)
                & m1_subset_1(X3,u1_struct_0(X2)) )
            & r1_xboole_0(u1_struct_0(X2),X1)
            & m1_pre_topc(X2,sK0)
            & ~ v2_struct_0(X2) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tmap_1(X2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X2),X3)
              & m1_subset_1(X3,u1_struct_0(X2)) )
          & r1_xboole_0(u1_struct_0(X2),sK1)
          & m1_pre_topc(X2,sK0)
          & ~ v2_struct_0(X2) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ r1_tmap_1(X2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X2),X3)
            & m1_subset_1(X3,u1_struct_0(X2)) )
        & r1_xboole_0(u1_struct_0(X2),sK1)
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ~ r1_tmap_1(sK2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),X3)
          & m1_subset_1(X3,u1_struct_0(sK2)) )
      & r1_xboole_0(u1_struct_0(sK2),sK1)
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ? [X3] :
        ( ~ r1_tmap_1(sK2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),X3)
        & m1_subset_1(X3,u1_struct_0(sK2)) )
   => ( ~ r1_tmap_1(sK2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),sK3)
      & m1_subset_1(sK3,u1_struct_0(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
                  & m1_subset_1(X3,u1_struct_0(X2)) )
              & r1_xboole_0(u1_struct_0(X2),X1)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
                  & m1_subset_1(X3,u1_struct_0(X2)) )
              & r1_xboole_0(u1_struct_0(X2),X1)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
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
    inference(negated_conjecture,[],[f16])).

% (25198)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% (25200)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
fof(f16,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_tmap_1)).

fof(f141,plain,
    ( r2_hidden(sK3,u1_struct_0(sK2))
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl8_4
  <=> r2_hidden(sK3,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f350,plain,
    ( r2_hidden(sK3,sK1)
    | ~ spl8_21 ),
    inference(avatar_component_clause,[],[f348])).

fof(f348,plain,
    ( spl8_21
  <=> r2_hidden(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f794,plain,(
    ~ spl8_20 ),
    inference(avatar_contradiction_clause,[],[f793])).

fof(f793,plain,
    ( $false
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f792,f73])).

fof(f73,plain,(
    ~ r1_tmap_1(sK2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f792,plain,
    ( r1_tmap_1(sK2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),sK3)
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f791,f69])).

fof(f69,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f791,plain,
    ( v2_struct_0(sK2)
    | r1_tmap_1(sK2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),sK3)
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f789,f70])).

fof(f70,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f789,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | r1_tmap_1(sK2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),sK3)
    | ~ spl8_20 ),
    inference(resolution,[],[f534,f72])).

fof(f72,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f49])).

fof(f534,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | r1_tmap_1(X0,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X0),sK3) )
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f533,f307])).

fof(f307,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f306,f65])).

fof(f65,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f306,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f305,f67])).

fof(f67,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f305,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f137,f70])).

fof(f137,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK2,X0)
      | m1_subset_1(sK3,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f135,f69])).

fof(f135,plain,(
    ! [X0] :
      ( m1_subset_1(sK3,u1_struct_0(X0))
      | ~ m1_pre_topc(sK2,X0)
      | v2_struct_0(sK2)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f72,f75])).

% (25179)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X1))
      | m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_pre_topc)).

fof(f533,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,u1_struct_0(X0))
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | r1_tmap_1(X0,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X0),sK3) )
    | ~ spl8_20 ),
    inference(resolution,[],[f331,f346])).

fof(f346,plain,
    ( r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK3)
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f344])).

fof(f344,plain,
    ( spl8_20
  <=> r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f331,plain,(
    ! [X0,X1] :
      ( ~ r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | r1_tmap_1(X1,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X1),X0) ) ),
    inference(subsumption_resolution,[],[f330,f162])).

fof(f162,plain,(
    ~ v2_struct_0(k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f161,f65])).

fof(f161,plain,
    ( ~ v2_struct_0(k6_tmap_1(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f160,f66])).

fof(f66,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f160,plain,
    ( ~ v2_struct_0(k6_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f148,f67])).

fof(f148,plain,
    ( ~ v2_struct_0(k6_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f68,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_struct_0(k6_tmap_1(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( v2_pre_topc(k6_tmap_1(X0,X1))
        & ~ v2_struct_0(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( v2_pre_topc(k6_tmap_1(X0,X1))
        & ~ v2_struct_0(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_pre_topc(k6_tmap_1(X0,X1))
        & ~ v2_struct_0(k6_tmap_1(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1))
        & ~ v2_struct_0(k6_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_tmap_1)).

fof(f68,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f49])).

fof(f330,plain,(
    ! [X0,X1] :
      ( ~ r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | r1_tmap_1(X1,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X1),X0)
      | v2_struct_0(k6_tmap_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f329,f165])).

fof(f165,plain,(
    v2_pre_topc(k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f164,f65])).

fof(f164,plain,
    ( v2_pre_topc(k6_tmap_1(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f163,f66])).

fof(f163,plain,
    ( v2_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f149,f67])).

fof(f149,plain,
    ( v2_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f68,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_pre_topc(k6_tmap_1(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f329,plain,(
    ! [X0,X1] :
      ( ~ r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | r1_tmap_1(X1,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X1),X0)
      | ~ v2_pre_topc(k6_tmap_1(sK0,sK1))
      | v2_struct_0(k6_tmap_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f328,f177])).

fof(f177,plain,(
    l1_pre_topc(k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f176,f65])).

fof(f176,plain,
    ( l1_pre_topc(k6_tmap_1(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f175,f66])).

fof(f175,plain,
    ( l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f154,f67])).

fof(f154,plain,
    ( l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f68,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | l1_pre_topc(k6_tmap_1(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_tmap_1)).

fof(f328,plain,(
    ! [X0,X1] :
      ( ~ r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | r1_tmap_1(X1,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X1),X0)
      | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
      | ~ v2_pre_topc(k6_tmap_1(sK0,sK1))
      | v2_struct_0(k6_tmap_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f327,f65])).

fof(f327,plain,(
    ! [X0,X1] :
      ( ~ r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | r1_tmap_1(X1,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X1),X0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
      | ~ v2_pre_topc(k6_tmap_1(sK0,sK1))
      | v2_struct_0(k6_tmap_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f326,f66])).

fof(f326,plain,(
    ! [X0,X1] :
      ( ~ r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | r1_tmap_1(X1,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X1),X0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
      | ~ v2_pre_topc(k6_tmap_1(sK0,sK1))
      | v2_struct_0(k6_tmap_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f325,f67])).

fof(f325,plain,(
    ! [X0,X1] :
      ( ~ r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | r1_tmap_1(X1,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X1),X0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
      | ~ v2_pre_topc(k6_tmap_1(sK0,sK1))
      | v2_struct_0(k6_tmap_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f324,f168])).

fof(f168,plain,(
    v1_funct_1(k7_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f167,f65])).

fof(f167,plain,
    ( v1_funct_1(k7_tmap_1(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f166,f66])).

fof(f166,plain,
    ( v1_funct_1(k7_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f150,f67])).

fof(f150,plain,
    ( v1_funct_1(k7_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f68,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_funct_1(k7_tmap_1(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_tmap_1)).

fof(f324,plain,(
    ! [X0,X1] :
      ( ~ r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | r1_tmap_1(X1,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X1),X0)
      | ~ v1_funct_1(k7_tmap_1(sK0,sK1))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
      | ~ v2_pre_topc(k6_tmap_1(sK0,sK1))
      | v2_struct_0(k6_tmap_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f321,f171])).

fof(f171,plain,(
    v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f170,f65])).

fof(f170,plain,
    ( v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f169,f66])).

fof(f169,plain,
    ( v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f151,f67])).

fof(f151,plain,
    ( v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f68,f90])).

% (25180)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f90,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f321,plain,(
    ! [X0,X1] :
      ( ~ r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | r1_tmap_1(X1,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X1),X0)
      | ~ v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
      | ~ v1_funct_1(k7_tmap_1(sK0,sK1))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
      | ~ v2_pre_topc(k6_tmap_1(sK0,sK1))
      | v2_struct_0(k6_tmap_1(sK0,sK1)) ) ),
    inference(resolution,[],[f174,f102])).

fof(f102,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ r1_tmap_1(X1,X0,X2,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
      | ~ r1_tmap_1(X1,X0,X2,X4)
      | X4 != X5
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                          | ~ r1_tmap_1(X1,X0,X2,X4)
                          | X4 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                          | ~ r1_tmap_1(X1,X0,X2,X4)
                          | X4 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X3))
                         => ( ( r1_tmap_1(X1,X0,X2,X4)
                              & X4 = X5 )
                           => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tmap_1)).

fof(f174,plain,(
    m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) ),
    inference(subsumption_resolution,[],[f173,f65])).

fof(f173,plain,
    ( m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f172,f66])).

fof(f172,plain,
    ( m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f152,f67])).

fof(f152,plain,
    ( m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f68,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f450,plain,
    ( ~ spl8_5
    | ~ spl8_15 ),
    inference(avatar_contradiction_clause,[],[f449])).

fof(f449,plain,
    ( $false
    | ~ spl8_5
    | ~ spl8_15 ),
    inference(subsumption_resolution,[],[f448,f69])).

fof(f448,plain,
    ( v2_struct_0(sK2)
    | ~ spl8_5
    | ~ spl8_15 ),
    inference(subsumption_resolution,[],[f447,f132])).

fof(f132,plain,(
    v2_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f131,f66])).

fof(f131,plain,
    ( v2_pre_topc(sK2)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f122,f67])).

fof(f122,plain,
    ( v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f70,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f447,plain,
    ( ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_5
    | ~ spl8_15 ),
    inference(subsumption_resolution,[],[f446,f133])).

fof(f133,plain,(
    l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f123,f67])).

fof(f123,plain,
    ( l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f70,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f446,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_5
    | ~ spl8_15 ),
    inference(subsumption_resolution,[],[f445,f145])).

fof(f145,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl8_5
  <=> v1_xboole_0(u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f445,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK2))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_15 ),
    inference(superposition,[],[f79,f300])).

fof(f300,plain,
    ( u1_struct_0(sK2) = sK4(sK2)
    | ~ spl8_15 ),
    inference(avatar_component_clause,[],[f298])).

fof(f298,plain,
    ( spl8_15
  <=> u1_struct_0(sK2) = sK4(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f79,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK4(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ( ~ v1_xboole_0(sK4(X0))
        & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f32,f50])).

fof(f50,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_xboole_0(sK4(X0))
        & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v4_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc7_pre_topc)).

fof(f419,plain,
    ( ~ spl8_5
    | spl8_14 ),
    inference(avatar_contradiction_clause,[],[f418])).

fof(f418,plain,
    ( $false
    | ~ spl8_5
    | spl8_14 ),
    inference(subsumption_resolution,[],[f417,f145])).

fof(f417,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK2))
    | spl8_14 ),
    inference(resolution,[],[f354,f81])).

fof(f81,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK5(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f53,f54])).

fof(f54,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK5(X0),X0) ) ),
    introduced(choice_axiom,[])).

% (25182)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
fof(f53,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

% (25197)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f354,plain,
    ( r2_hidden(sK7(u1_struct_0(sK2),sK4(sK2)),u1_struct_0(sK2))
    | spl8_14 ),
    inference(resolution,[],[f296,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK7(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK7(X0,X1),X1)
          & r2_hidden(sK7(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f61,f62])).

fof(f62,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK7(X0,X1),X1)
        & r2_hidden(sK7(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f296,plain,
    ( ~ r1_tarski(u1_struct_0(sK2),sK4(sK2))
    | spl8_14 ),
    inference(avatar_component_clause,[],[f294])).

fof(f294,plain,
    ( spl8_14
  <=> r1_tarski(u1_struct_0(sK2),sK4(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f351,plain,
    ( spl8_20
    | spl8_21 ),
    inference(avatar_split_clause,[],[f342,f348,f344])).

fof(f342,plain,
    ( r2_hidden(sK3,sK1)
    | r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK3) ),
    inference(resolution,[],[f159,f307])).

fof(f159,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X0,sK1)
      | r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X0) ) ),
    inference(subsumption_resolution,[],[f158,f65])).

fof(f158,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f157,f66])).

fof(f157,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f147,f67])).

fof(f147,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f68,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)
              | r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)
              | r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
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
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ~ r2_hidden(X2,X1)
               => r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_tmap_1)).

fof(f301,plain,
    ( ~ spl8_14
    | spl8_15
    | ~ spl8_1 ),
    inference(avatar_split_clause,[],[f292,f110,f298,f294])).

fof(f110,plain,
    ( spl8_1
  <=> m1_subset_1(sK4(sK2),k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f292,plain,
    ( u1_struct_0(sK2) = sK4(sK2)
    | ~ r1_tarski(u1_struct_0(sK2),sK4(sK2))
    | ~ spl8_1 ),
    inference(resolution,[],[f258,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f258,plain,
    ( r1_tarski(sK4(sK2),u1_struct_0(sK2))
    | ~ spl8_1 ),
    inference(resolution,[],[f112,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f112,plain,
    ( m1_subset_1(sK4(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f110])).

fof(f146,plain,
    ( spl8_4
    | spl8_5 ),
    inference(avatar_split_clause,[],[f136,f143,f139])).

fof(f136,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | r2_hidden(sK3,u1_struct_0(sK2)) ),
    inference(resolution,[],[f72,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f130,plain,(
    spl8_3 ),
    inference(avatar_contradiction_clause,[],[f129])).

fof(f129,plain,
    ( $false
    | spl8_3 ),
    inference(subsumption_resolution,[],[f128,f67])).

fof(f128,plain,
    ( ~ l1_pre_topc(sK0)
    | spl8_3 ),
    inference(subsumption_resolution,[],[f123,f120])).

fof(f120,plain,
    ( ~ l1_pre_topc(sK2)
    | spl8_3 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl8_3
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f127,plain,(
    spl8_2 ),
    inference(avatar_contradiction_clause,[],[f126])).

fof(f126,plain,
    ( $false
    | spl8_2 ),
    inference(subsumption_resolution,[],[f125,f66])).

fof(f125,plain,
    ( ~ v2_pre_topc(sK0)
    | spl8_2 ),
    inference(subsumption_resolution,[],[f124,f67])).

fof(f124,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl8_2 ),
    inference(subsumption_resolution,[],[f122,f116])).

fof(f116,plain,
    ( ~ v2_pre_topc(sK2)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl8_2
  <=> v2_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f121,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f108,f118,f114,f110])).

fof(f108,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | m1_subset_1(sK4(sK2),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(resolution,[],[f69,f78])).

fof(f78,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f51])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:54:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.56  % (25185)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.57  % (25193)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.57  % (25184)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.44/0.58  % (25201)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.44/0.59  % (25183)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.74/0.60  % (25192)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.74/0.60  % (25185)Refutation found. Thanks to Tanya!
% 1.74/0.60  % SZS status Theorem for theBenchmark
% 1.74/0.60  % SZS output start Proof for theBenchmark
% 1.74/0.60  fof(f807,plain,(
% 1.74/0.60    $false),
% 1.74/0.60    inference(avatar_sat_refutation,[],[f121,f127,f130,f146,f301,f351,f419,f450,f794,f806])).
% 1.74/0.60  fof(f806,plain,(
% 1.74/0.60    ~spl8_4 | ~spl8_21),
% 1.74/0.60    inference(avatar_contradiction_clause,[],[f805])).
% 1.74/0.60  fof(f805,plain,(
% 1.74/0.60    $false | (~spl8_4 | ~spl8_21)),
% 1.74/0.60    inference(subsumption_resolution,[],[f350,f455])).
% 1.74/0.60  fof(f455,plain,(
% 1.74/0.60    ~r2_hidden(sK3,sK1) | ~spl8_4),
% 1.74/0.60    inference(resolution,[],[f141,f134])).
% 1.74/0.60  fof(f134,plain,(
% 1.74/0.60    ( ! [X0] : (~r2_hidden(X0,u1_struct_0(sK2)) | ~r2_hidden(X0,sK1)) )),
% 1.74/0.60    inference(resolution,[],[f71,f85])).
% 1.74/0.60  fof(f85,plain,(
% 1.74/0.60    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.74/0.60    inference(cnf_transformation,[],[f57])).
% 1.74/0.60  fof(f57,plain,(
% 1.74/0.60    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.74/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f35,f56])).
% 1.74/0.60  fof(f56,plain,(
% 1.74/0.60    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)))),
% 1.74/0.60    introduced(choice_axiom,[])).
% 1.74/0.60  fof(f35,plain,(
% 1.74/0.60    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.74/0.60    inference(ennf_transformation,[],[f18])).
% 1.74/0.60  fof(f18,plain,(
% 1.74/0.60    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.74/0.60    inference(rectify,[],[f3])).
% 1.74/0.60  fof(f3,axiom,(
% 1.74/0.60    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.74/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.74/0.60  fof(f71,plain,(
% 1.74/0.60    r1_xboole_0(u1_struct_0(sK2),sK1)),
% 1.74/0.60    inference(cnf_transformation,[],[f49])).
% 1.74/0.60  fof(f49,plain,(
% 1.74/0.60    (((~r1_tmap_1(sK2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),sK3) & m1_subset_1(sK3,u1_struct_0(sK2))) & r1_xboole_0(u1_struct_0(sK2),sK1) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.74/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f48,f47,f46,f45])).
% 1.74/0.60  fof(f45,plain,(
% 1.74/0.60    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_xboole_0(u1_struct_0(X2),X1) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~r1_tmap_1(X2,k6_tmap_1(sK0,X1),k2_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_xboole_0(u1_struct_0(X2),X1) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.74/0.60    introduced(choice_axiom,[])).
% 1.74/0.60  fof(f46,plain,(
% 1.74/0.60    ? [X1] : (? [X2] : (? [X3] : (~r1_tmap_1(X2,k6_tmap_1(sK0,X1),k2_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_xboole_0(u1_struct_0(X2),X1) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (? [X3] : (~r1_tmap_1(X2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_xboole_0(u1_struct_0(X2),sK1) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.74/0.60    introduced(choice_axiom,[])).
% 1.74/0.60  fof(f47,plain,(
% 1.74/0.60    ? [X2] : (? [X3] : (~r1_tmap_1(X2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_xboole_0(u1_struct_0(X2),sK1) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => (? [X3] : (~r1_tmap_1(sK2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),X3) & m1_subset_1(X3,u1_struct_0(sK2))) & r1_xboole_0(u1_struct_0(sK2),sK1) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 1.74/0.60    introduced(choice_axiom,[])).
% 1.74/0.60  fof(f48,plain,(
% 1.74/0.60    ? [X3] : (~r1_tmap_1(sK2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),X3) & m1_subset_1(X3,u1_struct_0(sK2))) => (~r1_tmap_1(sK2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),sK3) & m1_subset_1(sK3,u1_struct_0(sK2)))),
% 1.74/0.60    introduced(choice_axiom,[])).
% 1.74/0.60  fof(f23,plain,(
% 1.74/0.60    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_xboole_0(u1_struct_0(X2),X1) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.74/0.60    inference(flattening,[],[f22])).
% 1.74/0.60  fof(f22,plain,(
% 1.74/0.60    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (~r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_xboole_0(u1_struct_0(X2),X1)) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.74/0.60    inference(ennf_transformation,[],[f17])).
% 1.74/0.61  fof(f17,negated_conjecture,(
% 1.74/0.61    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r1_xboole_0(u1_struct_0(X2),X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X2)) => r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3))))))),
% 1.74/0.61    inference(negated_conjecture,[],[f16])).
% 1.74/0.61  % (25198)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.74/0.61  % (25200)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.74/0.61  fof(f16,conjecture,(
% 1.74/0.61    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r1_xboole_0(u1_struct_0(X2),X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X2)) => r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3))))))),
% 1.74/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_tmap_1)).
% 1.74/0.61  fof(f141,plain,(
% 1.74/0.61    r2_hidden(sK3,u1_struct_0(sK2)) | ~spl8_4),
% 1.74/0.61    inference(avatar_component_clause,[],[f139])).
% 1.74/0.61  fof(f139,plain,(
% 1.74/0.61    spl8_4 <=> r2_hidden(sK3,u1_struct_0(sK2))),
% 1.74/0.61    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 1.74/0.61  fof(f350,plain,(
% 1.74/0.61    r2_hidden(sK3,sK1) | ~spl8_21),
% 1.74/0.61    inference(avatar_component_clause,[],[f348])).
% 1.74/0.61  fof(f348,plain,(
% 1.74/0.61    spl8_21 <=> r2_hidden(sK3,sK1)),
% 1.74/0.61    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).
% 1.74/0.61  fof(f794,plain,(
% 1.74/0.61    ~spl8_20),
% 1.74/0.61    inference(avatar_contradiction_clause,[],[f793])).
% 1.74/0.61  fof(f793,plain,(
% 1.74/0.61    $false | ~spl8_20),
% 1.74/0.61    inference(subsumption_resolution,[],[f792,f73])).
% 1.74/0.61  fof(f73,plain,(
% 1.74/0.61    ~r1_tmap_1(sK2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),sK3)),
% 1.74/0.61    inference(cnf_transformation,[],[f49])).
% 1.74/0.61  fof(f792,plain,(
% 1.74/0.61    r1_tmap_1(sK2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),sK3) | ~spl8_20),
% 1.74/0.61    inference(subsumption_resolution,[],[f791,f69])).
% 1.74/0.61  fof(f69,plain,(
% 1.74/0.61    ~v2_struct_0(sK2)),
% 1.74/0.61    inference(cnf_transformation,[],[f49])).
% 1.74/0.61  fof(f791,plain,(
% 1.74/0.61    v2_struct_0(sK2) | r1_tmap_1(sK2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),sK3) | ~spl8_20),
% 1.74/0.61    inference(subsumption_resolution,[],[f789,f70])).
% 1.74/0.61  fof(f70,plain,(
% 1.74/0.61    m1_pre_topc(sK2,sK0)),
% 1.74/0.61    inference(cnf_transformation,[],[f49])).
% 1.74/0.61  fof(f789,plain,(
% 1.74/0.61    ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | r1_tmap_1(sK2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),sK3) | ~spl8_20),
% 1.74/0.61    inference(resolution,[],[f534,f72])).
% 1.74/0.61  fof(f72,plain,(
% 1.74/0.61    m1_subset_1(sK3,u1_struct_0(sK2))),
% 1.74/0.61    inference(cnf_transformation,[],[f49])).
% 1.74/0.61  fof(f534,plain,(
% 1.74/0.61    ( ! [X0] : (~m1_subset_1(sK3,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | r1_tmap_1(X0,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X0),sK3)) ) | ~spl8_20),
% 1.74/0.61    inference(subsumption_resolution,[],[f533,f307])).
% 1.74/0.61  fof(f307,plain,(
% 1.74/0.61    m1_subset_1(sK3,u1_struct_0(sK0))),
% 1.74/0.61    inference(subsumption_resolution,[],[f306,f65])).
% 1.74/0.61  fof(f65,plain,(
% 1.74/0.61    ~v2_struct_0(sK0)),
% 1.74/0.61    inference(cnf_transformation,[],[f49])).
% 1.74/0.61  fof(f306,plain,(
% 1.74/0.61    m1_subset_1(sK3,u1_struct_0(sK0)) | v2_struct_0(sK0)),
% 1.74/0.61    inference(subsumption_resolution,[],[f305,f67])).
% 1.74/0.61  fof(f67,plain,(
% 1.74/0.61    l1_pre_topc(sK0)),
% 1.74/0.61    inference(cnf_transformation,[],[f49])).
% 1.74/0.61  fof(f305,plain,(
% 1.74/0.61    m1_subset_1(sK3,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.74/0.61    inference(resolution,[],[f137,f70])).
% 1.74/0.61  fof(f137,plain,(
% 1.74/0.61    ( ! [X0] : (~m1_pre_topc(sK2,X0) | m1_subset_1(sK3,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.74/0.61    inference(subsumption_resolution,[],[f135,f69])).
% 1.74/0.61  fof(f135,plain,(
% 1.74/0.61    ( ! [X0] : (m1_subset_1(sK3,u1_struct_0(X0)) | ~m1_pre_topc(sK2,X0) | v2_struct_0(sK2) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.74/0.61    inference(resolution,[],[f72,f75])).
% 1.74/0.61  % (25179)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.74/0.61  fof(f75,plain,(
% 1.74/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X1)) | m1_subset_1(X2,u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.74/0.61    inference(cnf_transformation,[],[f26])).
% 1.74/0.61  fof(f26,plain,(
% 1.74/0.61    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.74/0.61    inference(flattening,[],[f25])).
% 1.74/0.61  fof(f25,plain,(
% 1.74/0.61    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.74/0.61    inference(ennf_transformation,[],[f10])).
% 1.74/0.61  fof(f10,axiom,(
% 1.74/0.61    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 1.74/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_pre_topc)).
% 1.74/0.61  fof(f533,plain,(
% 1.74/0.61    ( ! [X0] : (~m1_subset_1(sK3,u1_struct_0(X0)) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | r1_tmap_1(X0,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X0),sK3)) ) | ~spl8_20),
% 1.74/0.61    inference(resolution,[],[f331,f346])).
% 1.74/0.61  fof(f346,plain,(
% 1.74/0.61    r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK3) | ~spl8_20),
% 1.74/0.61    inference(avatar_component_clause,[],[f344])).
% 1.74/0.61  fof(f344,plain,(
% 1.74/0.61    spl8_20 <=> r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK3)),
% 1.74/0.61    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).
% 1.74/0.61  fof(f331,plain,(
% 1.74/0.61    ( ! [X0,X1] : (~r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X0) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | r1_tmap_1(X1,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X1),X0)) )),
% 1.74/0.61    inference(subsumption_resolution,[],[f330,f162])).
% 1.74/0.61  fof(f162,plain,(
% 1.74/0.61    ~v2_struct_0(k6_tmap_1(sK0,sK1))),
% 1.74/0.61    inference(subsumption_resolution,[],[f161,f65])).
% 1.74/0.61  fof(f161,plain,(
% 1.74/0.61    ~v2_struct_0(k6_tmap_1(sK0,sK1)) | v2_struct_0(sK0)),
% 1.74/0.61    inference(subsumption_resolution,[],[f160,f66])).
% 1.74/0.61  fof(f66,plain,(
% 1.74/0.61    v2_pre_topc(sK0)),
% 1.74/0.61    inference(cnf_transformation,[],[f49])).
% 1.74/0.61  fof(f160,plain,(
% 1.74/0.61    ~v2_struct_0(k6_tmap_1(sK0,sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.74/0.61    inference(subsumption_resolution,[],[f148,f67])).
% 1.74/0.61  fof(f148,plain,(
% 1.74/0.61    ~v2_struct_0(k6_tmap_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.74/0.61    inference(resolution,[],[f68,f87])).
% 1.74/0.61  fof(f87,plain,(
% 1.74/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_struct_0(k6_tmap_1(X0,X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.74/0.61    inference(cnf_transformation,[],[f39])).
% 1.74/0.61  fof(f39,plain,(
% 1.74/0.61    ! [X0,X1] : ((v2_pre_topc(k6_tmap_1(X0,X1)) & ~v2_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.74/0.61    inference(flattening,[],[f38])).
% 1.74/0.61  fof(f38,plain,(
% 1.74/0.61    ! [X0,X1] : ((v2_pre_topc(k6_tmap_1(X0,X1)) & ~v2_struct_0(k6_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.74/0.61    inference(ennf_transformation,[],[f19])).
% 1.74/0.61  fof(f19,plain,(
% 1.74/0.61    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v2_pre_topc(k6_tmap_1(X0,X1)) & ~v2_struct_0(k6_tmap_1(X0,X1))))),
% 1.74/0.61    inference(pure_predicate_removal,[],[f13])).
% 1.74/0.61  fof(f13,axiom,(
% 1.74/0.61    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1)) & ~v2_struct_0(k6_tmap_1(X0,X1))))),
% 1.74/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_tmap_1)).
% 1.74/0.61  fof(f68,plain,(
% 1.74/0.61    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.74/0.61    inference(cnf_transformation,[],[f49])).
% 1.74/0.61  fof(f330,plain,(
% 1.74/0.61    ( ! [X0,X1] : (~r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X0) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | r1_tmap_1(X1,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X1),X0) | v2_struct_0(k6_tmap_1(sK0,sK1))) )),
% 1.74/0.61    inference(subsumption_resolution,[],[f329,f165])).
% 1.74/0.61  fof(f165,plain,(
% 1.74/0.61    v2_pre_topc(k6_tmap_1(sK0,sK1))),
% 1.74/0.61    inference(subsumption_resolution,[],[f164,f65])).
% 1.74/0.61  fof(f164,plain,(
% 1.74/0.61    v2_pre_topc(k6_tmap_1(sK0,sK1)) | v2_struct_0(sK0)),
% 1.74/0.61    inference(subsumption_resolution,[],[f163,f66])).
% 1.74/0.61  fof(f163,plain,(
% 1.74/0.61    v2_pre_topc(k6_tmap_1(sK0,sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.74/0.61    inference(subsumption_resolution,[],[f149,f67])).
% 1.74/0.61  fof(f149,plain,(
% 1.74/0.61    v2_pre_topc(k6_tmap_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.74/0.61    inference(resolution,[],[f68,f88])).
% 1.74/0.61  fof(f88,plain,(
% 1.74/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_pre_topc(k6_tmap_1(X0,X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.74/0.61    inference(cnf_transformation,[],[f39])).
% 1.74/0.61  fof(f329,plain,(
% 1.74/0.61    ( ! [X0,X1] : (~r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X0) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | r1_tmap_1(X1,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X1),X0) | ~v2_pre_topc(k6_tmap_1(sK0,sK1)) | v2_struct_0(k6_tmap_1(sK0,sK1))) )),
% 1.74/0.61    inference(subsumption_resolution,[],[f328,f177])).
% 1.74/0.61  fof(f177,plain,(
% 1.74/0.61    l1_pre_topc(k6_tmap_1(sK0,sK1))),
% 1.74/0.61    inference(subsumption_resolution,[],[f176,f65])).
% 1.74/0.61  fof(f176,plain,(
% 1.74/0.61    l1_pre_topc(k6_tmap_1(sK0,sK1)) | v2_struct_0(sK0)),
% 1.74/0.61    inference(subsumption_resolution,[],[f175,f66])).
% 1.74/0.61  fof(f175,plain,(
% 1.74/0.61    l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.74/0.61    inference(subsumption_resolution,[],[f154,f67])).
% 1.74/0.61  fof(f154,plain,(
% 1.74/0.61    l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.74/0.61    inference(resolution,[],[f68,f93])).
% 1.74/0.61  fof(f93,plain,(
% 1.74/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | l1_pre_topc(k6_tmap_1(X0,X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.74/0.61    inference(cnf_transformation,[],[f43])).
% 1.74/0.61  fof(f43,plain,(
% 1.74/0.61    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.74/0.61    inference(flattening,[],[f42])).
% 1.74/0.61  fof(f42,plain,(
% 1.74/0.61    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.74/0.61    inference(ennf_transformation,[],[f20])).
% 1.74/0.61  fof(f20,plain,(
% 1.74/0.61    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1))))),
% 1.74/0.61    inference(pure_predicate_removal,[],[f11])).
% 1.74/0.61  fof(f11,axiom,(
% 1.74/0.61    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))))),
% 1.74/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_tmap_1)).
% 1.74/0.61  fof(f328,plain,(
% 1.74/0.61    ( ! [X0,X1] : (~r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X0) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | r1_tmap_1(X1,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X1),X0) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v2_pre_topc(k6_tmap_1(sK0,sK1)) | v2_struct_0(k6_tmap_1(sK0,sK1))) )),
% 1.74/0.61    inference(subsumption_resolution,[],[f327,f65])).
% 1.74/0.61  fof(f327,plain,(
% 1.74/0.61    ( ! [X0,X1] : (~r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X0) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | r1_tmap_1(X1,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X1),X0) | v2_struct_0(sK0) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v2_pre_topc(k6_tmap_1(sK0,sK1)) | v2_struct_0(k6_tmap_1(sK0,sK1))) )),
% 1.74/0.61    inference(subsumption_resolution,[],[f326,f66])).
% 1.74/0.61  fof(f326,plain,(
% 1.74/0.61    ( ! [X0,X1] : (~r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X0) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | r1_tmap_1(X1,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X1),X0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v2_pre_topc(k6_tmap_1(sK0,sK1)) | v2_struct_0(k6_tmap_1(sK0,sK1))) )),
% 1.74/0.61    inference(subsumption_resolution,[],[f325,f67])).
% 1.74/0.61  fof(f325,plain,(
% 1.74/0.61    ( ! [X0,X1] : (~r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X0) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | r1_tmap_1(X1,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X1),X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v2_pre_topc(k6_tmap_1(sK0,sK1)) | v2_struct_0(k6_tmap_1(sK0,sK1))) )),
% 1.74/0.61    inference(subsumption_resolution,[],[f324,f168])).
% 1.74/0.61  fof(f168,plain,(
% 1.74/0.61    v1_funct_1(k7_tmap_1(sK0,sK1))),
% 1.74/0.61    inference(subsumption_resolution,[],[f167,f65])).
% 1.74/0.61  fof(f167,plain,(
% 1.74/0.61    v1_funct_1(k7_tmap_1(sK0,sK1)) | v2_struct_0(sK0)),
% 1.74/0.61    inference(subsumption_resolution,[],[f166,f66])).
% 1.74/0.61  fof(f166,plain,(
% 1.74/0.61    v1_funct_1(k7_tmap_1(sK0,sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.74/0.61    inference(subsumption_resolution,[],[f150,f67])).
% 1.74/0.61  fof(f150,plain,(
% 1.74/0.61    v1_funct_1(k7_tmap_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.74/0.61    inference(resolution,[],[f68,f89])).
% 1.74/0.61  fof(f89,plain,(
% 1.74/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_funct_1(k7_tmap_1(X0,X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.74/0.61    inference(cnf_transformation,[],[f41])).
% 1.74/0.61  fof(f41,plain,(
% 1.74/0.61    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.74/0.61    inference(flattening,[],[f40])).
% 1.74/0.61  fof(f40,plain,(
% 1.74/0.61    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.74/0.61    inference(ennf_transformation,[],[f12])).
% 1.74/0.61  fof(f12,axiom,(
% 1.74/0.61    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))))),
% 1.74/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_tmap_1)).
% 1.74/0.61  fof(f324,plain,(
% 1.74/0.61    ( ! [X0,X1] : (~r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X0) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | r1_tmap_1(X1,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X1),X0) | ~v1_funct_1(k7_tmap_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v2_pre_topc(k6_tmap_1(sK0,sK1)) | v2_struct_0(k6_tmap_1(sK0,sK1))) )),
% 1.74/0.61    inference(subsumption_resolution,[],[f321,f171])).
% 1.74/0.61  fof(f171,plain,(
% 1.74/0.61    v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))),
% 1.74/0.61    inference(subsumption_resolution,[],[f170,f65])).
% 1.74/0.61  fof(f170,plain,(
% 1.74/0.61    v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | v2_struct_0(sK0)),
% 1.74/0.61    inference(subsumption_resolution,[],[f169,f66])).
% 1.74/0.61  fof(f169,plain,(
% 1.74/0.61    v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.74/0.61    inference(subsumption_resolution,[],[f151,f67])).
% 1.74/0.61  fof(f151,plain,(
% 1.74/0.61    v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.74/0.61    inference(resolution,[],[f68,f90])).
% 1.74/0.61  % (25180)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.74/0.61  fof(f90,plain,(
% 1.74/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.74/0.61    inference(cnf_transformation,[],[f41])).
% 1.74/0.61  fof(f321,plain,(
% 1.74/0.61    ( ! [X0,X1] : (~r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X0) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | r1_tmap_1(X1,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X1),X0) | ~v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~v1_funct_1(k7_tmap_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v2_pre_topc(k6_tmap_1(sK0,sK1)) | v2_struct_0(k6_tmap_1(sK0,sK1))) )),
% 1.74/0.61    inference(resolution,[],[f174,f102])).
% 1.74/0.61  fof(f102,plain,(
% 1.74/0.61    ( ! [X2,X0,X5,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~r1_tmap_1(X1,X0,X2,X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.74/0.61    inference(equality_resolution,[],[f77])).
% 1.74/0.61  fof(f77,plain,(
% 1.74/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.74/0.61    inference(cnf_transformation,[],[f30])).
% 1.74/0.61  fof(f30,plain,(
% 1.74/0.61    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.74/0.61    inference(flattening,[],[f29])).
% 1.74/0.61  fof(f29,plain,(
% 1.74/0.61    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | (~r1_tmap_1(X1,X0,X2,X4) | X4 != X5)) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.74/0.61    inference(ennf_transformation,[],[f15])).
% 1.74/0.61  fof(f15,axiom,(
% 1.74/0.61    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ((r1_tmap_1(X1,X0,X2,X4) & X4 = X5) => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5))))))))),
% 1.74/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tmap_1)).
% 1.74/0.61  fof(f174,plain,(
% 1.74/0.61    m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))),
% 1.74/0.61    inference(subsumption_resolution,[],[f173,f65])).
% 1.74/0.61  fof(f173,plain,(
% 1.74/0.61    m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | v2_struct_0(sK0)),
% 1.74/0.61    inference(subsumption_resolution,[],[f172,f66])).
% 1.74/0.61  fof(f172,plain,(
% 1.74/0.61    m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.74/0.61    inference(subsumption_resolution,[],[f152,f67])).
% 1.74/0.61  fof(f152,plain,(
% 1.74/0.61    m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.74/0.61    inference(resolution,[],[f68,f91])).
% 1.74/0.61  fof(f91,plain,(
% 1.74/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.74/0.61    inference(cnf_transformation,[],[f41])).
% 1.74/0.61  fof(f450,plain,(
% 1.74/0.61    ~spl8_5 | ~spl8_15),
% 1.74/0.61    inference(avatar_contradiction_clause,[],[f449])).
% 1.74/0.61  fof(f449,plain,(
% 1.74/0.61    $false | (~spl8_5 | ~spl8_15)),
% 1.74/0.61    inference(subsumption_resolution,[],[f448,f69])).
% 1.74/0.61  fof(f448,plain,(
% 1.74/0.61    v2_struct_0(sK2) | (~spl8_5 | ~spl8_15)),
% 1.74/0.61    inference(subsumption_resolution,[],[f447,f132])).
% 1.74/0.61  fof(f132,plain,(
% 1.74/0.61    v2_pre_topc(sK2)),
% 1.74/0.61    inference(subsumption_resolution,[],[f131,f66])).
% 1.74/0.61  fof(f131,plain,(
% 1.74/0.61    v2_pre_topc(sK2) | ~v2_pre_topc(sK0)),
% 1.74/0.61    inference(subsumption_resolution,[],[f122,f67])).
% 1.74/0.61  fof(f122,plain,(
% 1.74/0.61    v2_pre_topc(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 1.74/0.61    inference(resolution,[],[f70,f80])).
% 1.74/0.61  fof(f80,plain,(
% 1.74/0.61    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.74/0.61    inference(cnf_transformation,[],[f34])).
% 1.74/0.61  fof(f34,plain,(
% 1.74/0.61    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.74/0.61    inference(flattening,[],[f33])).
% 1.74/0.61  fof(f33,plain,(
% 1.74/0.61    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.74/0.61    inference(ennf_transformation,[],[f7])).
% 1.74/0.61  fof(f7,axiom,(
% 1.74/0.61    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 1.74/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).
% 1.74/0.61  fof(f447,plain,(
% 1.74/0.61    ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_5 | ~spl8_15)),
% 1.74/0.61    inference(subsumption_resolution,[],[f446,f133])).
% 1.74/0.61  fof(f133,plain,(
% 1.74/0.61    l1_pre_topc(sK2)),
% 1.74/0.61    inference(subsumption_resolution,[],[f123,f67])).
% 1.74/0.61  fof(f123,plain,(
% 1.74/0.61    l1_pre_topc(sK2) | ~l1_pre_topc(sK0)),
% 1.74/0.61    inference(resolution,[],[f70,f74])).
% 1.74/0.61  fof(f74,plain,(
% 1.74/0.61    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 1.74/0.61    inference(cnf_transformation,[],[f24])).
% 1.74/0.61  fof(f24,plain,(
% 1.74/0.61    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.74/0.61    inference(ennf_transformation,[],[f8])).
% 1.74/0.61  fof(f8,axiom,(
% 1.74/0.61    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.74/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.74/0.61  fof(f446,plain,(
% 1.74/0.61    ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_5 | ~spl8_15)),
% 1.74/0.61    inference(subsumption_resolution,[],[f445,f145])).
% 1.74/0.61  fof(f145,plain,(
% 1.74/0.61    v1_xboole_0(u1_struct_0(sK2)) | ~spl8_5),
% 1.74/0.61    inference(avatar_component_clause,[],[f143])).
% 1.74/0.61  fof(f143,plain,(
% 1.74/0.61    spl8_5 <=> v1_xboole_0(u1_struct_0(sK2))),
% 1.74/0.61    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 1.74/0.61  fof(f445,plain,(
% 1.74/0.61    ~v1_xboole_0(u1_struct_0(sK2)) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~spl8_15),
% 1.74/0.61    inference(superposition,[],[f79,f300])).
% 1.74/0.61  fof(f300,plain,(
% 1.74/0.61    u1_struct_0(sK2) = sK4(sK2) | ~spl8_15),
% 1.74/0.61    inference(avatar_component_clause,[],[f298])).
% 1.74/0.61  fof(f298,plain,(
% 1.74/0.61    spl8_15 <=> u1_struct_0(sK2) = sK4(sK2)),
% 1.74/0.61    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 1.74/0.61  fof(f79,plain,(
% 1.74/0.61    ( ! [X0] : (~v1_xboole_0(sK4(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.74/0.61    inference(cnf_transformation,[],[f51])).
% 1.74/0.61  fof(f51,plain,(
% 1.74/0.61    ! [X0] : ((~v1_xboole_0(sK4(X0)) & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.74/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f32,f50])).
% 1.74/0.61  fof(f50,plain,(
% 1.74/0.61    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_xboole_0(sK4(X0)) & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.74/0.61    introduced(choice_axiom,[])).
% 1.74/0.61  fof(f32,plain,(
% 1.74/0.61    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.74/0.61    inference(flattening,[],[f31])).
% 1.74/0.61  fof(f31,plain,(
% 1.74/0.61    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.74/0.61    inference(ennf_transformation,[],[f21])).
% 1.74/0.61  fof(f21,plain,(
% 1.74/0.61    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.74/0.61    inference(pure_predicate_removal,[],[f9])).
% 1.74/0.61  fof(f9,axiom,(
% 1.74/0.61    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v4_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.74/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc7_pre_topc)).
% 1.74/0.61  fof(f419,plain,(
% 1.74/0.61    ~spl8_5 | spl8_14),
% 1.74/0.61    inference(avatar_contradiction_clause,[],[f418])).
% 1.74/0.61  fof(f418,plain,(
% 1.74/0.61    $false | (~spl8_5 | spl8_14)),
% 1.74/0.61    inference(subsumption_resolution,[],[f417,f145])).
% 1.74/0.61  fof(f417,plain,(
% 1.74/0.61    ~v1_xboole_0(u1_struct_0(sK2)) | spl8_14),
% 1.74/0.61    inference(resolution,[],[f354,f81])).
% 1.74/0.61  fof(f81,plain,(
% 1.74/0.61    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 1.74/0.61    inference(cnf_transformation,[],[f55])).
% 1.74/0.61  fof(f55,plain,(
% 1.74/0.61    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK5(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.74/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f53,f54])).
% 1.74/0.61  fof(f54,plain,(
% 1.74/0.61    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK5(X0),X0))),
% 1.74/0.61    introduced(choice_axiom,[])).
% 1.74/0.61  % (25182)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.74/0.61  fof(f53,plain,(
% 1.74/0.61    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.74/0.61    inference(rectify,[],[f52])).
% 1.74/0.61  fof(f52,plain,(
% 1.74/0.61    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.74/0.61    inference(nnf_transformation,[],[f1])).
% 1.74/0.61  % (25197)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.74/0.61  fof(f1,axiom,(
% 1.74/0.61    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.74/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.74/0.61  fof(f354,plain,(
% 1.74/0.61    r2_hidden(sK7(u1_struct_0(sK2),sK4(sK2)),u1_struct_0(sK2)) | spl8_14),
% 1.74/0.61    inference(resolution,[],[f296,f98])).
% 1.74/0.61  fof(f98,plain,(
% 1.74/0.61    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK7(X0,X1),X0)) )),
% 1.74/0.61    inference(cnf_transformation,[],[f63])).
% 1.74/0.61  fof(f63,plain,(
% 1.74/0.61    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.74/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f61,f62])).
% 1.74/0.61  fof(f62,plain,(
% 1.74/0.61    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0)))),
% 1.74/0.61    introduced(choice_axiom,[])).
% 1.74/0.61  fof(f61,plain,(
% 1.74/0.61    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.74/0.61    inference(rectify,[],[f60])).
% 1.74/0.61  fof(f60,plain,(
% 1.74/0.61    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.74/0.61    inference(nnf_transformation,[],[f44])).
% 1.74/0.61  fof(f44,plain,(
% 1.74/0.61    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.74/0.61    inference(ennf_transformation,[],[f2])).
% 1.74/0.61  fof(f2,axiom,(
% 1.74/0.61    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.74/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.74/0.61  fof(f296,plain,(
% 1.74/0.61    ~r1_tarski(u1_struct_0(sK2),sK4(sK2)) | spl8_14),
% 1.74/0.61    inference(avatar_component_clause,[],[f294])).
% 1.74/0.61  fof(f294,plain,(
% 1.74/0.61    spl8_14 <=> r1_tarski(u1_struct_0(sK2),sK4(sK2))),
% 1.74/0.61    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 1.74/0.61  fof(f351,plain,(
% 1.74/0.61    spl8_20 | spl8_21),
% 1.74/0.61    inference(avatar_split_clause,[],[f342,f348,f344])).
% 1.74/0.61  fof(f342,plain,(
% 1.74/0.61    r2_hidden(sK3,sK1) | r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK3)),
% 1.74/0.61    inference(resolution,[],[f159,f307])).
% 1.74/0.61  fof(f159,plain,(
% 1.74/0.61    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,sK1) | r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X0)) )),
% 1.74/0.61    inference(subsumption_resolution,[],[f158,f65])).
% 1.74/0.61  fof(f158,plain,(
% 1.74/0.61    ( ! [X0] : (r2_hidden(X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X0) | v2_struct_0(sK0)) )),
% 1.74/0.61    inference(subsumption_resolution,[],[f157,f66])).
% 1.74/0.61  fof(f157,plain,(
% 1.74/0.61    ( ! [X0] : (r2_hidden(X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.74/0.61    inference(subsumption_resolution,[],[f147,f67])).
% 1.74/0.61  fof(f147,plain,(
% 1.74/0.61    ( ! [X0] : (r2_hidden(X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.74/0.61    inference(resolution,[],[f68,f76])).
% 1.74/0.61  fof(f76,plain,(
% 1.74/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.74/0.61    inference(cnf_transformation,[],[f28])).
% 1.74/0.61  fof(f28,plain,(
% 1.74/0.61    ! [X0] : (! [X1] : (! [X2] : (r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2) | r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.74/0.61    inference(flattening,[],[f27])).
% 1.74/0.61  fof(f27,plain,(
% 1.74/0.61    ! [X0] : (! [X1] : (! [X2] : ((r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2) | r2_hidden(X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.74/0.61    inference(ennf_transformation,[],[f14])).
% 1.74/0.61  fof(f14,axiom,(
% 1.74/0.61    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (~r2_hidden(X2,X1) => r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)))))),
% 1.74/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_tmap_1)).
% 1.74/0.61  fof(f301,plain,(
% 1.74/0.61    ~spl8_14 | spl8_15 | ~spl8_1),
% 1.74/0.61    inference(avatar_split_clause,[],[f292,f110,f298,f294])).
% 1.74/0.61  fof(f110,plain,(
% 1.74/0.61    spl8_1 <=> m1_subset_1(sK4(sK2),k1_zfmisc_1(u1_struct_0(sK2)))),
% 1.74/0.61    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 1.74/0.61  fof(f292,plain,(
% 1.74/0.61    u1_struct_0(sK2) = sK4(sK2) | ~r1_tarski(u1_struct_0(sK2),sK4(sK2)) | ~spl8_1),
% 1.74/0.61    inference(resolution,[],[f258,f96])).
% 1.74/0.61  fof(f96,plain,(
% 1.74/0.61    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.74/0.61    inference(cnf_transformation,[],[f59])).
% 1.74/0.61  fof(f59,plain,(
% 1.74/0.61    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.74/0.61    inference(flattening,[],[f58])).
% 1.74/0.61  fof(f58,plain,(
% 1.74/0.61    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.74/0.61    inference(nnf_transformation,[],[f4])).
% 1.74/0.61  fof(f4,axiom,(
% 1.74/0.61    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.74/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.74/0.61  fof(f258,plain,(
% 1.74/0.61    r1_tarski(sK4(sK2),u1_struct_0(sK2)) | ~spl8_1),
% 1.74/0.61    inference(resolution,[],[f112,f100])).
% 1.74/0.61  fof(f100,plain,(
% 1.74/0.61    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.74/0.61    inference(cnf_transformation,[],[f64])).
% 1.74/0.61  fof(f64,plain,(
% 1.74/0.61    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.74/0.61    inference(nnf_transformation,[],[f6])).
% 1.74/0.61  fof(f6,axiom,(
% 1.74/0.61    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.74/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.74/0.61  fof(f112,plain,(
% 1.74/0.61    m1_subset_1(sK4(sK2),k1_zfmisc_1(u1_struct_0(sK2))) | ~spl8_1),
% 1.74/0.61    inference(avatar_component_clause,[],[f110])).
% 1.74/0.61  fof(f146,plain,(
% 1.74/0.61    spl8_4 | spl8_5),
% 1.74/0.61    inference(avatar_split_clause,[],[f136,f143,f139])).
% 1.74/0.61  fof(f136,plain,(
% 1.74/0.61    v1_xboole_0(u1_struct_0(sK2)) | r2_hidden(sK3,u1_struct_0(sK2))),
% 1.74/0.61    inference(resolution,[],[f72,f86])).
% 1.74/0.61  fof(f86,plain,(
% 1.74/0.61    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 1.74/0.61    inference(cnf_transformation,[],[f37])).
% 1.74/0.61  fof(f37,plain,(
% 1.74/0.61    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.74/0.61    inference(flattening,[],[f36])).
% 1.74/0.61  fof(f36,plain,(
% 1.74/0.61    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.74/0.61    inference(ennf_transformation,[],[f5])).
% 1.74/0.61  fof(f5,axiom,(
% 1.74/0.61    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.74/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 1.74/0.61  fof(f130,plain,(
% 1.74/0.61    spl8_3),
% 1.74/0.61    inference(avatar_contradiction_clause,[],[f129])).
% 1.74/0.61  fof(f129,plain,(
% 1.74/0.61    $false | spl8_3),
% 1.74/0.61    inference(subsumption_resolution,[],[f128,f67])).
% 1.74/0.61  fof(f128,plain,(
% 1.74/0.61    ~l1_pre_topc(sK0) | spl8_3),
% 1.74/0.61    inference(subsumption_resolution,[],[f123,f120])).
% 1.74/0.61  fof(f120,plain,(
% 1.74/0.61    ~l1_pre_topc(sK2) | spl8_3),
% 1.74/0.61    inference(avatar_component_clause,[],[f118])).
% 1.74/0.61  fof(f118,plain,(
% 1.74/0.61    spl8_3 <=> l1_pre_topc(sK2)),
% 1.74/0.61    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 1.74/0.61  fof(f127,plain,(
% 1.74/0.61    spl8_2),
% 1.74/0.61    inference(avatar_contradiction_clause,[],[f126])).
% 1.74/0.61  fof(f126,plain,(
% 1.74/0.61    $false | spl8_2),
% 1.74/0.61    inference(subsumption_resolution,[],[f125,f66])).
% 1.74/0.61  fof(f125,plain,(
% 1.74/0.61    ~v2_pre_topc(sK0) | spl8_2),
% 1.74/0.61    inference(subsumption_resolution,[],[f124,f67])).
% 1.74/0.61  fof(f124,plain,(
% 1.74/0.61    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | spl8_2),
% 1.74/0.61    inference(subsumption_resolution,[],[f122,f116])).
% 1.74/0.61  fof(f116,plain,(
% 1.74/0.61    ~v2_pre_topc(sK2) | spl8_2),
% 1.74/0.61    inference(avatar_component_clause,[],[f114])).
% 1.74/0.61  fof(f114,plain,(
% 1.74/0.61    spl8_2 <=> v2_pre_topc(sK2)),
% 1.74/0.61    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 1.74/0.61  fof(f121,plain,(
% 1.74/0.61    spl8_1 | ~spl8_2 | ~spl8_3),
% 1.74/0.61    inference(avatar_split_clause,[],[f108,f118,f114,f110])).
% 1.74/0.61  fof(f108,plain,(
% 1.74/0.61    ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | m1_subset_1(sK4(sK2),k1_zfmisc_1(u1_struct_0(sK2)))),
% 1.74/0.61    inference(resolution,[],[f69,f78])).
% 1.74/0.61  fof(f78,plain,(
% 1.74/0.61    ( ! [X0] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 1.74/0.61    inference(cnf_transformation,[],[f51])).
% 1.74/0.61  % SZS output end Proof for theBenchmark
% 1.74/0.61  % (25185)------------------------------
% 1.74/0.61  % (25185)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.74/0.61  % (25185)Termination reason: Refutation
% 1.74/0.61  
% 1.74/0.61  % (25185)Memory used [KB]: 11257
% 1.74/0.61  % (25185)Time elapsed: 0.138 s
% 1.74/0.61  % (25185)------------------------------
% 1.74/0.61  % (25185)------------------------------
% 1.74/0.61  % (25190)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.74/0.61  % (25181)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.74/0.62  % (25176)Success in time 0.246 s
%------------------------------------------------------------------------------
