%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:27 EST 2020

% Result     : Theorem 1.57s
% Output     : Refutation 1.57s
% Verified   : 
% Statistics : Number of formulae       :  197 ( 816 expanded)
%              Number of leaves         :   33 ( 342 expanded)
%              Depth                    :   26
%              Number of atoms          :  844 (6253 expanded)
%              Number of equality atoms :   13 (  14 expanded)
%              Maximal formula depth    :   23 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f808,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f122,f128,f131,f147,f302,f352,f420,f451,f795,f807])).

fof(f807,plain,
    ( ~ spl8_4
    | ~ spl8_21 ),
    inference(avatar_contradiction_clause,[],[f806])).

% (30584)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
fof(f806,plain,
    ( $false
    | ~ spl8_4
    | ~ spl8_21 ),
    inference(subsumption_resolution,[],[f351,f456])).

fof(f456,plain,
    ( ~ r2_hidden(sK3,sK1)
    | ~ spl8_4 ),
    inference(resolution,[],[f142,f135])).

fof(f135,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,u1_struct_0(sK2))
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f72,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK6(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f36,f57])).

fof(f57,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
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

% (30589)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
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

fof(f72,plain,(
    r1_xboole_0(u1_struct_0(sK2),sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,
    ( ~ r1_tmap_1(sK2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),sK3)
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & r1_xboole_0(u1_struct_0(sK2),sK1)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f49,f48,f47,f46])).

% (30588)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
fof(f46,plain,
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

fof(f47,plain,
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

fof(f48,plain,
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

fof(f49,plain,
    ( ? [X3] :
        ( ~ r1_tmap_1(sK2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),X3)
        & m1_subset_1(X3,u1_struct_0(sK2)) )
   => ( ~ r1_tmap_1(sK2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),sK3)
      & m1_subset_1(sK3,u1_struct_0(sK2)) ) ),
    introduced(choice_axiom,[])).

% (30583)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
fof(f24,plain,(
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
    inference(flattening,[],[f23])).

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

fof(f142,plain,
    ( r2_hidden(sK3,u1_struct_0(sK2))
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl8_4
  <=> r2_hidden(sK3,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f351,plain,
    ( r2_hidden(sK3,sK1)
    | ~ spl8_21 ),
    inference(avatar_component_clause,[],[f349])).

fof(f349,plain,
    ( spl8_21
  <=> r2_hidden(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f795,plain,(
    ~ spl8_20 ),
    inference(avatar_contradiction_clause,[],[f794])).

fof(f794,plain,
    ( $false
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f793,f74])).

fof(f74,plain,(
    ~ r1_tmap_1(sK2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f793,plain,
    ( r1_tmap_1(sK2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),sK3)
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f792,f70])).

fof(f70,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f792,plain,
    ( v2_struct_0(sK2)
    | r1_tmap_1(sK2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),sK3)
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f790,f71])).

fof(f71,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f790,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | r1_tmap_1(sK2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),sK3)
    | ~ spl8_20 ),
    inference(resolution,[],[f535,f73])).

fof(f73,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f50])).

fof(f535,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | r1_tmap_1(X0,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X0),sK3) )
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f534,f308])).

fof(f308,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f307,f66])).

fof(f66,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f307,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f306,f68])).

fof(f68,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f306,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f138,f71])).

fof(f138,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK2,X0)
      | m1_subset_1(sK3,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f136,f70])).

fof(f136,plain,(
    ! [X0] :
      ( m1_subset_1(sK3,u1_struct_0(X0))
      | ~ m1_pre_topc(sK2,X0)
      | v2_struct_0(sK2)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f73,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X1))
      | m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f534,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,u1_struct_0(X0))
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | r1_tmap_1(X0,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X0),sK3) )
    | ~ spl8_20 ),
    inference(resolution,[],[f332,f347])).

fof(f347,plain,
    ( r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK3)
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f345])).

fof(f345,plain,
    ( spl8_20
  <=> r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f332,plain,(
    ! [X0,X1] :
      ( ~ r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | r1_tmap_1(X1,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X1),X0) ) ),
    inference(subsumption_resolution,[],[f331,f163])).

fof(f163,plain,(
    ~ v2_struct_0(k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f162,f66])).

fof(f162,plain,
    ( ~ v2_struct_0(k6_tmap_1(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f161,f67])).

fof(f67,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f161,plain,
    ( ~ v2_struct_0(k6_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f149,f68])).

fof(f149,plain,
    ( ~ v2_struct_0(k6_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f69,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_struct_0(k6_tmap_1(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( v2_pre_topc(k6_tmap_1(X0,X1))
        & ~ v2_struct_0(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
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

fof(f69,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f50])).

fof(f331,plain,(
    ! [X0,X1] :
      ( ~ r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | r1_tmap_1(X1,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X1),X0)
      | v2_struct_0(k6_tmap_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f330,f166])).

fof(f166,plain,(
    v2_pre_topc(k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f165,f66])).

fof(f165,plain,
    ( v2_pre_topc(k6_tmap_1(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f164,f67])).

fof(f164,plain,
    ( v2_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f150,f68])).

fof(f150,plain,
    ( v2_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f69,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_pre_topc(k6_tmap_1(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f330,plain,(
    ! [X0,X1] :
      ( ~ r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | r1_tmap_1(X1,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X1),X0)
      | ~ v2_pre_topc(k6_tmap_1(sK0,sK1))
      | v2_struct_0(k6_tmap_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f329,f178])).

fof(f178,plain,(
    l1_pre_topc(k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f177,f66])).

fof(f177,plain,
    ( l1_pre_topc(k6_tmap_1(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f176,f67])).

fof(f176,plain,
    ( l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f155,f68])).

fof(f155,plain,
    ( l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f69,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | l1_pre_topc(k6_tmap_1(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
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

fof(f329,plain,(
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
    inference(subsumption_resolution,[],[f328,f66])).

fof(f328,plain,(
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
    inference(subsumption_resolution,[],[f327,f67])).

fof(f327,plain,(
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
    inference(subsumption_resolution,[],[f326,f68])).

fof(f326,plain,(
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
    inference(subsumption_resolution,[],[f325,f169])).

fof(f169,plain,(
    v1_funct_1(k7_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f168,f66])).

fof(f168,plain,
    ( v1_funct_1(k7_tmap_1(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f167,f67])).

fof(f167,plain,
    ( v1_funct_1(k7_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f151,f68])).

fof(f151,plain,
    ( v1_funct_1(k7_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f69,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_funct_1(k7_tmap_1(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
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

fof(f325,plain,(
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
    inference(subsumption_resolution,[],[f322,f172])).

fof(f172,plain,(
    v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f171,f66])).

fof(f171,plain,
    ( v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f170,f67])).

fof(f170,plain,
    ( v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f152,f68])).

fof(f152,plain,
    ( v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f69,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f322,plain,(
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
    inference(resolution,[],[f175,f103])).

fof(f103,plain,(
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
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
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
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

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

fof(f175,plain,(
    m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) ),
    inference(subsumption_resolution,[],[f174,f66])).

fof(f174,plain,
    ( m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f173,f67])).

fof(f173,plain,
    ( m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f153,f68])).

fof(f153,plain,
    ( m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f69,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f451,plain,
    ( ~ spl8_5
    | ~ spl8_15 ),
    inference(avatar_contradiction_clause,[],[f450])).

fof(f450,plain,
    ( $false
    | ~ spl8_5
    | ~ spl8_15 ),
    inference(subsumption_resolution,[],[f449,f70])).

fof(f449,plain,
    ( v2_struct_0(sK2)
    | ~ spl8_5
    | ~ spl8_15 ),
    inference(subsumption_resolution,[],[f448,f133])).

fof(f133,plain,(
    v2_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f132,f67])).

fof(f132,plain,
    ( v2_pre_topc(sK2)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f123,f68])).

fof(f123,plain,
    ( v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f71,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
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

fof(f448,plain,
    ( ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_5
    | ~ spl8_15 ),
    inference(subsumption_resolution,[],[f447,f134])).

fof(f134,plain,(
    l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f124,f68])).

fof(f124,plain,
    ( l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f71,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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

fof(f447,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_5
    | ~ spl8_15 ),
    inference(subsumption_resolution,[],[f446,f146])).

% (30599)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
fof(f146,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl8_5
  <=> v1_xboole_0(u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f446,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK2))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_15 ),
    inference(superposition,[],[f80,f301])).

fof(f301,plain,
    ( u1_struct_0(sK2) = sK4(sK2)
    | ~ spl8_15 ),
    inference(avatar_component_clause,[],[f299])).

fof(f299,plain,
    ( spl8_15
  <=> u1_struct_0(sK2) = sK4(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f80,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK4(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ( ~ v1_xboole_0(sK4(X0))
        & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f33,f51])).

fof(f51,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_xboole_0(sK4(X0))
        & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

% (30576)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
fof(f22,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    inference(pure_predicate_removal,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v3_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_tops_1)).

fof(f420,plain,
    ( ~ spl8_5
    | spl8_14 ),
    inference(avatar_contradiction_clause,[],[f419])).

fof(f419,plain,
    ( $false
    | ~ spl8_5
    | spl8_14 ),
    inference(subsumption_resolution,[],[f418,f146])).

fof(f418,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK2))
    | spl8_14 ),
    inference(resolution,[],[f355,f82])).

fof(f82,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK5(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f54,f55])).

fof(f55,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK5(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f355,plain,
    ( r2_hidden(sK7(u1_struct_0(sK2),sK4(sK2)),u1_struct_0(sK2))
    | spl8_14 ),
    inference(resolution,[],[f297,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK7(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK7(X0,X1),X1)
          & r2_hidden(sK7(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f62,f63])).

fof(f63,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK7(X0,X1),X1)
        & r2_hidden(sK7(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f45,plain,(
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

fof(f297,plain,
    ( ~ r1_tarski(u1_struct_0(sK2),sK4(sK2))
    | spl8_14 ),
    inference(avatar_component_clause,[],[f295])).

fof(f295,plain,
    ( spl8_14
  <=> r1_tarski(u1_struct_0(sK2),sK4(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f352,plain,
    ( spl8_20
    | spl8_21 ),
    inference(avatar_split_clause,[],[f343,f349,f345])).

fof(f343,plain,
    ( r2_hidden(sK3,sK1)
    | r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK3) ),
    inference(resolution,[],[f160,f308])).

% (30597)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
fof(f160,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X0,sK1)
      | r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X0) ) ),
    inference(subsumption_resolution,[],[f159,f66])).

fof(f159,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f158,f67])).

fof(f158,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f148,f68])).

% (30596)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
fof(f148,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f69,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

% (30598)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
fof(f29,plain,(
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
    inference(flattening,[],[f28])).

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

fof(f302,plain,
    ( ~ spl8_14
    | spl8_15
    | ~ spl8_1 ),
    inference(avatar_split_clause,[],[f293,f111,f299,f295])).

fof(f111,plain,
    ( spl8_1
  <=> m1_subset_1(sK4(sK2),k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f293,plain,
    ( u1_struct_0(sK2) = sK4(sK2)
    | ~ r1_tarski(u1_struct_0(sK2),sK4(sK2))
    | ~ spl8_1 ),
    inference(resolution,[],[f259,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
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

% (30579)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
fof(f259,plain,
    ( r1_tarski(sK4(sK2),u1_struct_0(sK2))
    | ~ spl8_1 ),
    inference(resolution,[],[f113,f101])).

fof(f101,plain,(
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
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f113,plain,
    ( m1_subset_1(sK4(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f111])).

fof(f147,plain,
    ( spl8_4
    | spl8_5 ),
    inference(avatar_split_clause,[],[f137,f144,f140])).

fof(f137,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | r2_hidden(sK3,u1_struct_0(sK2)) ),
    inference(resolution,[],[f73,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f131,plain,(
    spl8_3 ),
    inference(avatar_contradiction_clause,[],[f130])).

fof(f130,plain,
    ( $false
    | spl8_3 ),
    inference(subsumption_resolution,[],[f129,f68])).

fof(f129,plain,
    ( ~ l1_pre_topc(sK0)
    | spl8_3 ),
    inference(subsumption_resolution,[],[f124,f121])).

fof(f121,plain,
    ( ~ l1_pre_topc(sK2)
    | spl8_3 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl8_3
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f128,plain,(
    spl8_2 ),
    inference(avatar_contradiction_clause,[],[f127])).

fof(f127,plain,
    ( $false
    | spl8_2 ),
    inference(subsumption_resolution,[],[f126,f67])).

fof(f126,plain,
    ( ~ v2_pre_topc(sK0)
    | spl8_2 ),
    inference(subsumption_resolution,[],[f125,f68])).

fof(f125,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl8_2 ),
    inference(subsumption_resolution,[],[f123,f117])).

fof(f117,plain,
    ( ~ v2_pre_topc(sK2)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl8_2
  <=> v2_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f122,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f109,f119,f115,f111])).

fof(f109,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | m1_subset_1(sK4(sK2),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(resolution,[],[f70,f79])).

fof(f79,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f52])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n010.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 09:53:59 EST 2020
% 0.15/0.36  % CPUTime    : 
% 1.41/0.57  % (30578)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.41/0.57  % (30577)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.57/0.58  % (30578)Refutation found. Thanks to Tanya!
% 1.57/0.58  % SZS status Theorem for theBenchmark
% 1.57/0.58  % (30586)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.57/0.58  % (30585)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.57/0.58  % (30593)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.57/0.59  % (30594)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.57/0.59  % (30575)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.57/0.59  % (30572)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.57/0.59  % (30582)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.57/0.60  % SZS output start Proof for theBenchmark
% 1.57/0.60  fof(f808,plain,(
% 1.57/0.60    $false),
% 1.57/0.60    inference(avatar_sat_refutation,[],[f122,f128,f131,f147,f302,f352,f420,f451,f795,f807])).
% 1.57/0.60  fof(f807,plain,(
% 1.57/0.60    ~spl8_4 | ~spl8_21),
% 1.57/0.60    inference(avatar_contradiction_clause,[],[f806])).
% 1.57/0.60  % (30584)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.57/0.60  fof(f806,plain,(
% 1.57/0.60    $false | (~spl8_4 | ~spl8_21)),
% 1.57/0.60    inference(subsumption_resolution,[],[f351,f456])).
% 1.57/0.60  fof(f456,plain,(
% 1.57/0.60    ~r2_hidden(sK3,sK1) | ~spl8_4),
% 1.57/0.60    inference(resolution,[],[f142,f135])).
% 1.57/0.60  fof(f135,plain,(
% 1.57/0.60    ( ! [X0] : (~r2_hidden(X0,u1_struct_0(sK2)) | ~r2_hidden(X0,sK1)) )),
% 1.57/0.60    inference(resolution,[],[f72,f86])).
% 1.57/0.60  fof(f86,plain,(
% 1.57/0.60    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.57/0.60    inference(cnf_transformation,[],[f58])).
% 1.57/0.60  fof(f58,plain,(
% 1.57/0.60    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.57/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f36,f57])).
% 1.57/0.60  fof(f57,plain,(
% 1.57/0.60    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)))),
% 1.57/0.60    introduced(choice_axiom,[])).
% 1.57/0.60  fof(f36,plain,(
% 1.57/0.60    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.57/0.60    inference(ennf_transformation,[],[f18])).
% 1.57/0.60  % (30589)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.57/0.60  fof(f18,plain,(
% 1.57/0.60    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.57/0.60    inference(rectify,[],[f3])).
% 1.57/0.60  fof(f3,axiom,(
% 1.57/0.60    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.57/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.57/0.60  fof(f72,plain,(
% 1.57/0.60    r1_xboole_0(u1_struct_0(sK2),sK1)),
% 1.57/0.60    inference(cnf_transformation,[],[f50])).
% 1.57/0.60  fof(f50,plain,(
% 1.57/0.60    (((~r1_tmap_1(sK2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),sK3) & m1_subset_1(sK3,u1_struct_0(sK2))) & r1_xboole_0(u1_struct_0(sK2),sK1) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.57/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f49,f48,f47,f46])).
% 1.57/0.60  % (30588)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.57/0.60  fof(f46,plain,(
% 1.57/0.60    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_xboole_0(u1_struct_0(X2),X1) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~r1_tmap_1(X2,k6_tmap_1(sK0,X1),k2_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_xboole_0(u1_struct_0(X2),X1) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.57/0.60    introduced(choice_axiom,[])).
% 1.57/0.60  fof(f47,plain,(
% 1.57/0.60    ? [X1] : (? [X2] : (? [X3] : (~r1_tmap_1(X2,k6_tmap_1(sK0,X1),k2_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_xboole_0(u1_struct_0(X2),X1) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (? [X3] : (~r1_tmap_1(X2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_xboole_0(u1_struct_0(X2),sK1) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.57/0.60    introduced(choice_axiom,[])).
% 1.57/0.60  fof(f48,plain,(
% 1.57/0.60    ? [X2] : (? [X3] : (~r1_tmap_1(X2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_xboole_0(u1_struct_0(X2),sK1) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => (? [X3] : (~r1_tmap_1(sK2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),X3) & m1_subset_1(X3,u1_struct_0(sK2))) & r1_xboole_0(u1_struct_0(sK2),sK1) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 1.57/0.60    introduced(choice_axiom,[])).
% 1.57/0.60  fof(f49,plain,(
% 1.57/0.60    ? [X3] : (~r1_tmap_1(sK2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),X3) & m1_subset_1(X3,u1_struct_0(sK2))) => (~r1_tmap_1(sK2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),sK3) & m1_subset_1(sK3,u1_struct_0(sK2)))),
% 1.57/0.60    introduced(choice_axiom,[])).
% 1.57/0.60  % (30583)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.57/0.60  fof(f24,plain,(
% 1.57/0.60    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_xboole_0(u1_struct_0(X2),X1) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.57/0.60    inference(flattening,[],[f23])).
% 1.57/0.60  fof(f23,plain,(
% 1.57/0.60    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (~r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_xboole_0(u1_struct_0(X2),X1)) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.57/0.60    inference(ennf_transformation,[],[f17])).
% 1.57/0.60  fof(f17,negated_conjecture,(
% 1.57/0.60    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r1_xboole_0(u1_struct_0(X2),X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X2)) => r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3))))))),
% 1.57/0.60    inference(negated_conjecture,[],[f16])).
% 1.57/0.60  fof(f16,conjecture,(
% 1.57/0.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r1_xboole_0(u1_struct_0(X2),X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X2)) => r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3))))))),
% 1.57/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_tmap_1)).
% 1.57/0.60  fof(f142,plain,(
% 1.57/0.60    r2_hidden(sK3,u1_struct_0(sK2)) | ~spl8_4),
% 1.57/0.60    inference(avatar_component_clause,[],[f140])).
% 1.57/0.60  fof(f140,plain,(
% 1.57/0.60    spl8_4 <=> r2_hidden(sK3,u1_struct_0(sK2))),
% 1.57/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 1.57/0.60  fof(f351,plain,(
% 1.57/0.60    r2_hidden(sK3,sK1) | ~spl8_21),
% 1.57/0.60    inference(avatar_component_clause,[],[f349])).
% 1.57/0.60  fof(f349,plain,(
% 1.57/0.60    spl8_21 <=> r2_hidden(sK3,sK1)),
% 1.57/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).
% 1.57/0.60  fof(f795,plain,(
% 1.57/0.60    ~spl8_20),
% 1.57/0.60    inference(avatar_contradiction_clause,[],[f794])).
% 1.57/0.60  fof(f794,plain,(
% 1.57/0.60    $false | ~spl8_20),
% 1.57/0.60    inference(subsumption_resolution,[],[f793,f74])).
% 1.57/0.60  fof(f74,plain,(
% 1.57/0.60    ~r1_tmap_1(sK2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),sK3)),
% 1.57/0.60    inference(cnf_transformation,[],[f50])).
% 1.57/0.60  fof(f793,plain,(
% 1.57/0.60    r1_tmap_1(sK2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),sK3) | ~spl8_20),
% 1.57/0.60    inference(subsumption_resolution,[],[f792,f70])).
% 1.57/0.60  fof(f70,plain,(
% 1.57/0.60    ~v2_struct_0(sK2)),
% 1.57/0.60    inference(cnf_transformation,[],[f50])).
% 1.57/0.60  fof(f792,plain,(
% 1.57/0.60    v2_struct_0(sK2) | r1_tmap_1(sK2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),sK3) | ~spl8_20),
% 1.57/0.60    inference(subsumption_resolution,[],[f790,f71])).
% 1.57/0.60  fof(f71,plain,(
% 1.57/0.60    m1_pre_topc(sK2,sK0)),
% 1.57/0.60    inference(cnf_transformation,[],[f50])).
% 1.57/0.60  fof(f790,plain,(
% 1.57/0.60    ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | r1_tmap_1(sK2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),sK3) | ~spl8_20),
% 1.57/0.60    inference(resolution,[],[f535,f73])).
% 1.57/0.60  fof(f73,plain,(
% 1.57/0.60    m1_subset_1(sK3,u1_struct_0(sK2))),
% 1.57/0.60    inference(cnf_transformation,[],[f50])).
% 1.57/0.60  fof(f535,plain,(
% 1.57/0.60    ( ! [X0] : (~m1_subset_1(sK3,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | r1_tmap_1(X0,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X0),sK3)) ) | ~spl8_20),
% 1.57/0.60    inference(subsumption_resolution,[],[f534,f308])).
% 1.57/0.60  fof(f308,plain,(
% 1.57/0.60    m1_subset_1(sK3,u1_struct_0(sK0))),
% 1.57/0.60    inference(subsumption_resolution,[],[f307,f66])).
% 1.57/0.60  fof(f66,plain,(
% 1.57/0.60    ~v2_struct_0(sK0)),
% 1.57/0.60    inference(cnf_transformation,[],[f50])).
% 1.57/0.60  fof(f307,plain,(
% 1.57/0.60    m1_subset_1(sK3,u1_struct_0(sK0)) | v2_struct_0(sK0)),
% 1.57/0.60    inference(subsumption_resolution,[],[f306,f68])).
% 1.57/0.60  fof(f68,plain,(
% 1.57/0.60    l1_pre_topc(sK0)),
% 1.57/0.60    inference(cnf_transformation,[],[f50])).
% 1.57/0.60  fof(f306,plain,(
% 1.57/0.60    m1_subset_1(sK3,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.57/0.60    inference(resolution,[],[f138,f71])).
% 1.57/0.60  fof(f138,plain,(
% 1.57/0.60    ( ! [X0] : (~m1_pre_topc(sK2,X0) | m1_subset_1(sK3,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.57/0.60    inference(subsumption_resolution,[],[f136,f70])).
% 1.57/0.60  fof(f136,plain,(
% 1.57/0.60    ( ! [X0] : (m1_subset_1(sK3,u1_struct_0(X0)) | ~m1_pre_topc(sK2,X0) | v2_struct_0(sK2) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.57/0.60    inference(resolution,[],[f73,f76])).
% 1.57/0.60  fof(f76,plain,(
% 1.57/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X1)) | m1_subset_1(X2,u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.57/0.60    inference(cnf_transformation,[],[f27])).
% 1.57/0.60  fof(f27,plain,(
% 1.57/0.60    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.57/0.60    inference(flattening,[],[f26])).
% 1.57/0.60  fof(f26,plain,(
% 1.57/0.60    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.57/0.60    inference(ennf_transformation,[],[f9])).
% 1.57/0.60  fof(f9,axiom,(
% 1.57/0.60    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 1.57/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_pre_topc)).
% 1.57/0.60  fof(f534,plain,(
% 1.57/0.60    ( ! [X0] : (~m1_subset_1(sK3,u1_struct_0(X0)) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | r1_tmap_1(X0,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X0),sK3)) ) | ~spl8_20),
% 1.57/0.60    inference(resolution,[],[f332,f347])).
% 1.57/0.60  fof(f347,plain,(
% 1.57/0.60    r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK3) | ~spl8_20),
% 1.57/0.60    inference(avatar_component_clause,[],[f345])).
% 1.57/0.60  fof(f345,plain,(
% 1.57/0.60    spl8_20 <=> r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK3)),
% 1.57/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).
% 1.57/0.60  fof(f332,plain,(
% 1.57/0.60    ( ! [X0,X1] : (~r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X0) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | r1_tmap_1(X1,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X1),X0)) )),
% 1.57/0.60    inference(subsumption_resolution,[],[f331,f163])).
% 1.57/0.60  fof(f163,plain,(
% 1.57/0.60    ~v2_struct_0(k6_tmap_1(sK0,sK1))),
% 1.57/0.60    inference(subsumption_resolution,[],[f162,f66])).
% 1.57/0.60  fof(f162,plain,(
% 1.57/0.60    ~v2_struct_0(k6_tmap_1(sK0,sK1)) | v2_struct_0(sK0)),
% 1.57/0.60    inference(subsumption_resolution,[],[f161,f67])).
% 1.57/0.60  fof(f67,plain,(
% 1.57/0.60    v2_pre_topc(sK0)),
% 1.57/0.60    inference(cnf_transformation,[],[f50])).
% 1.57/0.60  fof(f161,plain,(
% 1.57/0.60    ~v2_struct_0(k6_tmap_1(sK0,sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.57/0.60    inference(subsumption_resolution,[],[f149,f68])).
% 1.57/0.60  fof(f149,plain,(
% 1.57/0.60    ~v2_struct_0(k6_tmap_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.57/0.60    inference(resolution,[],[f69,f88])).
% 1.57/0.60  fof(f88,plain,(
% 1.57/0.60    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_struct_0(k6_tmap_1(X0,X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.57/0.60    inference(cnf_transformation,[],[f40])).
% 1.57/0.60  fof(f40,plain,(
% 1.57/0.60    ! [X0,X1] : ((v2_pre_topc(k6_tmap_1(X0,X1)) & ~v2_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.57/0.60    inference(flattening,[],[f39])).
% 1.57/0.60  fof(f39,plain,(
% 1.57/0.60    ! [X0,X1] : ((v2_pre_topc(k6_tmap_1(X0,X1)) & ~v2_struct_0(k6_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.57/0.60    inference(ennf_transformation,[],[f19])).
% 1.57/0.60  fof(f19,plain,(
% 1.57/0.60    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v2_pre_topc(k6_tmap_1(X0,X1)) & ~v2_struct_0(k6_tmap_1(X0,X1))))),
% 1.57/0.60    inference(pure_predicate_removal,[],[f13])).
% 1.57/0.60  fof(f13,axiom,(
% 1.57/0.60    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1)) & ~v2_struct_0(k6_tmap_1(X0,X1))))),
% 1.57/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_tmap_1)).
% 1.57/0.60  fof(f69,plain,(
% 1.57/0.60    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.57/0.60    inference(cnf_transformation,[],[f50])).
% 1.57/0.60  fof(f331,plain,(
% 1.57/0.60    ( ! [X0,X1] : (~r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X0) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | r1_tmap_1(X1,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X1),X0) | v2_struct_0(k6_tmap_1(sK0,sK1))) )),
% 1.57/0.60    inference(subsumption_resolution,[],[f330,f166])).
% 1.57/0.60  fof(f166,plain,(
% 1.57/0.60    v2_pre_topc(k6_tmap_1(sK0,sK1))),
% 1.57/0.60    inference(subsumption_resolution,[],[f165,f66])).
% 1.57/0.60  fof(f165,plain,(
% 1.57/0.60    v2_pre_topc(k6_tmap_1(sK0,sK1)) | v2_struct_0(sK0)),
% 1.57/0.60    inference(subsumption_resolution,[],[f164,f67])).
% 1.57/0.60  fof(f164,plain,(
% 1.57/0.60    v2_pre_topc(k6_tmap_1(sK0,sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.57/0.60    inference(subsumption_resolution,[],[f150,f68])).
% 1.57/0.60  fof(f150,plain,(
% 1.57/0.60    v2_pre_topc(k6_tmap_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.57/0.60    inference(resolution,[],[f69,f89])).
% 1.57/0.60  fof(f89,plain,(
% 1.57/0.60    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_pre_topc(k6_tmap_1(X0,X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.57/0.60    inference(cnf_transformation,[],[f40])).
% 1.57/0.60  fof(f330,plain,(
% 1.57/0.60    ( ! [X0,X1] : (~r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X0) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | r1_tmap_1(X1,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X1),X0) | ~v2_pre_topc(k6_tmap_1(sK0,sK1)) | v2_struct_0(k6_tmap_1(sK0,sK1))) )),
% 1.57/0.60    inference(subsumption_resolution,[],[f329,f178])).
% 1.57/0.60  fof(f178,plain,(
% 1.57/0.60    l1_pre_topc(k6_tmap_1(sK0,sK1))),
% 1.57/0.60    inference(subsumption_resolution,[],[f177,f66])).
% 1.57/0.60  fof(f177,plain,(
% 1.57/0.60    l1_pre_topc(k6_tmap_1(sK0,sK1)) | v2_struct_0(sK0)),
% 1.57/0.60    inference(subsumption_resolution,[],[f176,f67])).
% 1.57/0.60  fof(f176,plain,(
% 1.57/0.60    l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.57/0.60    inference(subsumption_resolution,[],[f155,f68])).
% 1.57/0.60  fof(f155,plain,(
% 1.57/0.60    l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.57/0.60    inference(resolution,[],[f69,f94])).
% 1.57/0.60  fof(f94,plain,(
% 1.57/0.60    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | l1_pre_topc(k6_tmap_1(X0,X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.57/0.60    inference(cnf_transformation,[],[f44])).
% 1.57/0.60  fof(f44,plain,(
% 1.57/0.60    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.57/0.60    inference(flattening,[],[f43])).
% 1.57/0.60  fof(f43,plain,(
% 1.57/0.60    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.57/0.60    inference(ennf_transformation,[],[f20])).
% 1.57/0.60  fof(f20,plain,(
% 1.57/0.60    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1))))),
% 1.57/0.60    inference(pure_predicate_removal,[],[f11])).
% 1.57/0.60  fof(f11,axiom,(
% 1.57/0.60    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))))),
% 1.57/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_tmap_1)).
% 1.57/0.60  fof(f329,plain,(
% 1.57/0.60    ( ! [X0,X1] : (~r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X0) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | r1_tmap_1(X1,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X1),X0) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v2_pre_topc(k6_tmap_1(sK0,sK1)) | v2_struct_0(k6_tmap_1(sK0,sK1))) )),
% 1.57/0.60    inference(subsumption_resolution,[],[f328,f66])).
% 1.57/0.60  fof(f328,plain,(
% 1.57/0.60    ( ! [X0,X1] : (~r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X0) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | r1_tmap_1(X1,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X1),X0) | v2_struct_0(sK0) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v2_pre_topc(k6_tmap_1(sK0,sK1)) | v2_struct_0(k6_tmap_1(sK0,sK1))) )),
% 1.57/0.60    inference(subsumption_resolution,[],[f327,f67])).
% 1.57/0.60  fof(f327,plain,(
% 1.57/0.60    ( ! [X0,X1] : (~r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X0) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | r1_tmap_1(X1,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X1),X0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v2_pre_topc(k6_tmap_1(sK0,sK1)) | v2_struct_0(k6_tmap_1(sK0,sK1))) )),
% 1.57/0.60    inference(subsumption_resolution,[],[f326,f68])).
% 1.57/0.60  fof(f326,plain,(
% 1.57/0.60    ( ! [X0,X1] : (~r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X0) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | r1_tmap_1(X1,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X1),X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v2_pre_topc(k6_tmap_1(sK0,sK1)) | v2_struct_0(k6_tmap_1(sK0,sK1))) )),
% 1.57/0.60    inference(subsumption_resolution,[],[f325,f169])).
% 1.57/0.60  fof(f169,plain,(
% 1.57/0.60    v1_funct_1(k7_tmap_1(sK0,sK1))),
% 1.57/0.60    inference(subsumption_resolution,[],[f168,f66])).
% 1.57/0.60  fof(f168,plain,(
% 1.57/0.60    v1_funct_1(k7_tmap_1(sK0,sK1)) | v2_struct_0(sK0)),
% 1.57/0.60    inference(subsumption_resolution,[],[f167,f67])).
% 1.57/0.60  fof(f167,plain,(
% 1.57/0.60    v1_funct_1(k7_tmap_1(sK0,sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.57/0.60    inference(subsumption_resolution,[],[f151,f68])).
% 1.57/0.60  fof(f151,plain,(
% 1.57/0.60    v1_funct_1(k7_tmap_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.57/0.60    inference(resolution,[],[f69,f90])).
% 1.57/0.60  fof(f90,plain,(
% 1.57/0.60    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_funct_1(k7_tmap_1(X0,X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.57/0.60    inference(cnf_transformation,[],[f42])).
% 1.57/0.60  fof(f42,plain,(
% 1.57/0.60    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.57/0.60    inference(flattening,[],[f41])).
% 1.57/0.60  fof(f41,plain,(
% 1.57/0.60    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.57/0.60    inference(ennf_transformation,[],[f12])).
% 1.57/0.60  fof(f12,axiom,(
% 1.57/0.60    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))))),
% 1.57/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_tmap_1)).
% 1.57/0.60  fof(f325,plain,(
% 1.57/0.60    ( ! [X0,X1] : (~r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X0) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | r1_tmap_1(X1,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X1),X0) | ~v1_funct_1(k7_tmap_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v2_pre_topc(k6_tmap_1(sK0,sK1)) | v2_struct_0(k6_tmap_1(sK0,sK1))) )),
% 1.57/0.60    inference(subsumption_resolution,[],[f322,f172])).
% 1.57/0.60  fof(f172,plain,(
% 1.57/0.60    v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))),
% 1.57/0.60    inference(subsumption_resolution,[],[f171,f66])).
% 1.57/0.60  fof(f171,plain,(
% 1.57/0.60    v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | v2_struct_0(sK0)),
% 1.57/0.60    inference(subsumption_resolution,[],[f170,f67])).
% 1.57/0.60  fof(f170,plain,(
% 1.57/0.60    v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.57/0.60    inference(subsumption_resolution,[],[f152,f68])).
% 1.57/0.60  fof(f152,plain,(
% 1.57/0.60    v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.57/0.60    inference(resolution,[],[f69,f91])).
% 1.57/0.60  fof(f91,plain,(
% 1.57/0.60    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.57/0.60    inference(cnf_transformation,[],[f42])).
% 1.57/0.60  fof(f322,plain,(
% 1.57/0.60    ( ! [X0,X1] : (~r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X0) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | r1_tmap_1(X1,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X1),X0) | ~v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~v1_funct_1(k7_tmap_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v2_pre_topc(k6_tmap_1(sK0,sK1)) | v2_struct_0(k6_tmap_1(sK0,sK1))) )),
% 1.57/0.60    inference(resolution,[],[f175,f103])).
% 1.57/0.60  fof(f103,plain,(
% 1.57/0.60    ( ! [X2,X0,X5,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~r1_tmap_1(X1,X0,X2,X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.57/0.60    inference(equality_resolution,[],[f78])).
% 1.57/0.60  fof(f78,plain,(
% 1.57/0.60    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.57/0.60    inference(cnf_transformation,[],[f31])).
% 1.57/0.60  fof(f31,plain,(
% 1.57/0.60    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.57/0.60    inference(flattening,[],[f30])).
% 1.57/0.60  fof(f30,plain,(
% 1.57/0.60    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | (~r1_tmap_1(X1,X0,X2,X4) | X4 != X5)) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.57/0.60    inference(ennf_transformation,[],[f15])).
% 1.57/0.60  fof(f15,axiom,(
% 1.57/0.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ((r1_tmap_1(X1,X0,X2,X4) & X4 = X5) => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5))))))))),
% 1.57/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tmap_1)).
% 1.57/0.60  fof(f175,plain,(
% 1.57/0.60    m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))),
% 1.57/0.60    inference(subsumption_resolution,[],[f174,f66])).
% 1.57/0.60  fof(f174,plain,(
% 1.57/0.60    m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | v2_struct_0(sK0)),
% 1.57/0.60    inference(subsumption_resolution,[],[f173,f67])).
% 1.57/0.60  fof(f173,plain,(
% 1.57/0.60    m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.57/0.60    inference(subsumption_resolution,[],[f153,f68])).
% 1.57/0.60  fof(f153,plain,(
% 1.57/0.60    m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.57/0.60    inference(resolution,[],[f69,f92])).
% 1.57/0.60  fof(f92,plain,(
% 1.57/0.60    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.57/0.60    inference(cnf_transformation,[],[f42])).
% 1.57/0.60  fof(f451,plain,(
% 1.57/0.60    ~spl8_5 | ~spl8_15),
% 1.57/0.60    inference(avatar_contradiction_clause,[],[f450])).
% 1.57/0.60  fof(f450,plain,(
% 1.57/0.60    $false | (~spl8_5 | ~spl8_15)),
% 1.57/0.60    inference(subsumption_resolution,[],[f449,f70])).
% 1.57/0.60  fof(f449,plain,(
% 1.57/0.60    v2_struct_0(sK2) | (~spl8_5 | ~spl8_15)),
% 1.57/0.60    inference(subsumption_resolution,[],[f448,f133])).
% 1.57/0.60  fof(f133,plain,(
% 1.57/0.60    v2_pre_topc(sK2)),
% 1.57/0.60    inference(subsumption_resolution,[],[f132,f67])).
% 1.57/0.60  fof(f132,plain,(
% 1.57/0.60    v2_pre_topc(sK2) | ~v2_pre_topc(sK0)),
% 1.57/0.60    inference(subsumption_resolution,[],[f123,f68])).
% 1.57/0.60  fof(f123,plain,(
% 1.57/0.60    v2_pre_topc(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 1.57/0.60    inference(resolution,[],[f71,f81])).
% 1.57/0.60  fof(f81,plain,(
% 1.57/0.60    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.57/0.60    inference(cnf_transformation,[],[f35])).
% 1.57/0.60  fof(f35,plain,(
% 1.57/0.60    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.57/0.60    inference(flattening,[],[f34])).
% 1.57/0.60  fof(f34,plain,(
% 1.57/0.60    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.57/0.60    inference(ennf_transformation,[],[f7])).
% 1.57/0.60  fof(f7,axiom,(
% 1.57/0.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 1.57/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).
% 1.57/0.60  fof(f448,plain,(
% 1.57/0.60    ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_5 | ~spl8_15)),
% 1.57/0.60    inference(subsumption_resolution,[],[f447,f134])).
% 1.57/0.60  fof(f134,plain,(
% 1.57/0.60    l1_pre_topc(sK2)),
% 1.57/0.60    inference(subsumption_resolution,[],[f124,f68])).
% 1.57/0.60  fof(f124,plain,(
% 1.57/0.60    l1_pre_topc(sK2) | ~l1_pre_topc(sK0)),
% 1.57/0.60    inference(resolution,[],[f71,f75])).
% 1.57/0.60  fof(f75,plain,(
% 1.57/0.60    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 1.57/0.60    inference(cnf_transformation,[],[f25])).
% 1.57/0.60  fof(f25,plain,(
% 1.57/0.60    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.57/0.60    inference(ennf_transformation,[],[f8])).
% 1.57/0.60  fof(f8,axiom,(
% 1.57/0.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.57/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.57/0.60  fof(f447,plain,(
% 1.57/0.60    ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_5 | ~spl8_15)),
% 1.57/0.60    inference(subsumption_resolution,[],[f446,f146])).
% 1.57/0.60  % (30599)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.57/0.60  fof(f146,plain,(
% 1.57/0.60    v1_xboole_0(u1_struct_0(sK2)) | ~spl8_5),
% 1.57/0.60    inference(avatar_component_clause,[],[f144])).
% 1.57/0.60  fof(f144,plain,(
% 1.57/0.60    spl8_5 <=> v1_xboole_0(u1_struct_0(sK2))),
% 1.57/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 1.57/0.60  fof(f446,plain,(
% 1.57/0.60    ~v1_xboole_0(u1_struct_0(sK2)) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~spl8_15),
% 1.57/0.60    inference(superposition,[],[f80,f301])).
% 1.57/0.60  fof(f301,plain,(
% 1.57/0.60    u1_struct_0(sK2) = sK4(sK2) | ~spl8_15),
% 1.57/0.60    inference(avatar_component_clause,[],[f299])).
% 1.57/0.60  fof(f299,plain,(
% 1.57/0.60    spl8_15 <=> u1_struct_0(sK2) = sK4(sK2)),
% 1.57/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 1.57/0.60  fof(f80,plain,(
% 1.57/0.60    ( ! [X0] : (~v1_xboole_0(sK4(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.57/0.60    inference(cnf_transformation,[],[f52])).
% 1.57/0.60  fof(f52,plain,(
% 1.57/0.60    ! [X0] : ((~v1_xboole_0(sK4(X0)) & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.57/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f33,f51])).
% 1.57/0.60  fof(f51,plain,(
% 1.57/0.60    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_xboole_0(sK4(X0)) & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.57/0.60    introduced(choice_axiom,[])).
% 1.57/0.60  fof(f33,plain,(
% 1.57/0.60    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.57/0.60    inference(flattening,[],[f32])).
% 1.57/0.60  fof(f32,plain,(
% 1.57/0.60    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.57/0.60    inference(ennf_transformation,[],[f22])).
% 1.57/0.60  % (30576)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.57/0.60  fof(f22,plain,(
% 1.57/0.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.57/0.60    inference(pure_predicate_removal,[],[f21])).
% 1.57/0.60  fof(f21,plain,(
% 1.57/0.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v3_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.57/0.60    inference(pure_predicate_removal,[],[f10])).
% 1.57/0.60  fof(f10,axiom,(
% 1.57/0.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.57/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_tops_1)).
% 1.57/0.60  fof(f420,plain,(
% 1.57/0.60    ~spl8_5 | spl8_14),
% 1.57/0.60    inference(avatar_contradiction_clause,[],[f419])).
% 1.57/0.60  fof(f419,plain,(
% 1.57/0.60    $false | (~spl8_5 | spl8_14)),
% 1.57/0.60    inference(subsumption_resolution,[],[f418,f146])).
% 1.57/0.60  fof(f418,plain,(
% 1.57/0.60    ~v1_xboole_0(u1_struct_0(sK2)) | spl8_14),
% 1.57/0.60    inference(resolution,[],[f355,f82])).
% 1.57/0.60  fof(f82,plain,(
% 1.57/0.60    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 1.57/0.60    inference(cnf_transformation,[],[f56])).
% 1.57/0.60  fof(f56,plain,(
% 1.57/0.60    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK5(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.57/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f54,f55])).
% 1.57/0.60  fof(f55,plain,(
% 1.57/0.60    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK5(X0),X0))),
% 1.57/0.60    introduced(choice_axiom,[])).
% 1.57/0.60  fof(f54,plain,(
% 1.57/0.60    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.57/0.60    inference(rectify,[],[f53])).
% 1.57/0.60  fof(f53,plain,(
% 1.57/0.60    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.57/0.60    inference(nnf_transformation,[],[f1])).
% 1.57/0.60  fof(f1,axiom,(
% 1.57/0.60    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.57/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.57/0.60  fof(f355,plain,(
% 1.57/0.60    r2_hidden(sK7(u1_struct_0(sK2),sK4(sK2)),u1_struct_0(sK2)) | spl8_14),
% 1.57/0.60    inference(resolution,[],[f297,f99])).
% 1.57/0.60  fof(f99,plain,(
% 1.57/0.60    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK7(X0,X1),X0)) )),
% 1.57/0.60    inference(cnf_transformation,[],[f64])).
% 1.57/0.60  fof(f64,plain,(
% 1.57/0.60    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.57/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f62,f63])).
% 1.57/0.60  fof(f63,plain,(
% 1.57/0.60    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0)))),
% 1.57/0.60    introduced(choice_axiom,[])).
% 1.57/0.60  fof(f62,plain,(
% 1.57/0.60    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.57/0.60    inference(rectify,[],[f61])).
% 1.57/0.60  fof(f61,plain,(
% 1.57/0.60    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.57/0.60    inference(nnf_transformation,[],[f45])).
% 1.57/0.60  fof(f45,plain,(
% 1.57/0.60    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.57/0.60    inference(ennf_transformation,[],[f2])).
% 1.57/0.60  fof(f2,axiom,(
% 1.57/0.60    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.57/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.57/0.60  fof(f297,plain,(
% 1.57/0.60    ~r1_tarski(u1_struct_0(sK2),sK4(sK2)) | spl8_14),
% 1.57/0.60    inference(avatar_component_clause,[],[f295])).
% 1.57/0.60  fof(f295,plain,(
% 1.57/0.60    spl8_14 <=> r1_tarski(u1_struct_0(sK2),sK4(sK2))),
% 1.57/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 1.57/0.60  fof(f352,plain,(
% 1.57/0.60    spl8_20 | spl8_21),
% 1.57/0.60    inference(avatar_split_clause,[],[f343,f349,f345])).
% 1.57/0.60  fof(f343,plain,(
% 1.57/0.60    r2_hidden(sK3,sK1) | r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK3)),
% 1.57/0.60    inference(resolution,[],[f160,f308])).
% 1.57/0.60  % (30597)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.57/0.60  fof(f160,plain,(
% 1.57/0.60    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,sK1) | r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X0)) )),
% 1.57/0.60    inference(subsumption_resolution,[],[f159,f66])).
% 1.57/0.60  fof(f159,plain,(
% 1.57/0.60    ( ! [X0] : (r2_hidden(X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X0) | v2_struct_0(sK0)) )),
% 1.57/0.60    inference(subsumption_resolution,[],[f158,f67])).
% 1.57/0.60  fof(f158,plain,(
% 1.57/0.60    ( ! [X0] : (r2_hidden(X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.57/0.60    inference(subsumption_resolution,[],[f148,f68])).
% 1.57/0.60  % (30596)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.57/0.60  fof(f148,plain,(
% 1.57/0.60    ( ! [X0] : (r2_hidden(X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.57/0.60    inference(resolution,[],[f69,f77])).
% 1.57/0.60  fof(f77,plain,(
% 1.57/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.57/0.60    inference(cnf_transformation,[],[f29])).
% 1.57/0.60  % (30598)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.57/0.60  fof(f29,plain,(
% 1.57/0.60    ! [X0] : (! [X1] : (! [X2] : (r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2) | r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.57/0.60    inference(flattening,[],[f28])).
% 1.57/0.60  fof(f28,plain,(
% 1.57/0.60    ! [X0] : (! [X1] : (! [X2] : ((r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2) | r2_hidden(X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.57/0.60    inference(ennf_transformation,[],[f14])).
% 1.57/0.60  fof(f14,axiom,(
% 1.57/0.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (~r2_hidden(X2,X1) => r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)))))),
% 1.57/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_tmap_1)).
% 1.57/0.60  fof(f302,plain,(
% 1.57/0.60    ~spl8_14 | spl8_15 | ~spl8_1),
% 1.57/0.60    inference(avatar_split_clause,[],[f293,f111,f299,f295])).
% 1.57/0.60  fof(f111,plain,(
% 1.57/0.60    spl8_1 <=> m1_subset_1(sK4(sK2),k1_zfmisc_1(u1_struct_0(sK2)))),
% 1.57/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 1.57/0.60  fof(f293,plain,(
% 1.57/0.60    u1_struct_0(sK2) = sK4(sK2) | ~r1_tarski(u1_struct_0(sK2),sK4(sK2)) | ~spl8_1),
% 1.57/0.60    inference(resolution,[],[f259,f97])).
% 1.57/0.60  fof(f97,plain,(
% 1.57/0.60    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.57/0.60    inference(cnf_transformation,[],[f60])).
% 1.57/0.60  fof(f60,plain,(
% 1.57/0.60    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.57/0.60    inference(flattening,[],[f59])).
% 1.57/0.60  fof(f59,plain,(
% 1.57/0.60    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.57/0.60    inference(nnf_transformation,[],[f4])).
% 1.57/0.60  fof(f4,axiom,(
% 1.57/0.60    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.57/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.57/0.60  % (30579)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.57/0.60  fof(f259,plain,(
% 1.57/0.60    r1_tarski(sK4(sK2),u1_struct_0(sK2)) | ~spl8_1),
% 1.57/0.60    inference(resolution,[],[f113,f101])).
% 1.57/0.60  fof(f101,plain,(
% 1.57/0.60    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.57/0.60    inference(cnf_transformation,[],[f65])).
% 1.57/0.60  fof(f65,plain,(
% 1.57/0.60    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.57/0.60    inference(nnf_transformation,[],[f6])).
% 1.57/0.60  fof(f6,axiom,(
% 1.57/0.60    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.57/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.57/0.60  fof(f113,plain,(
% 1.57/0.60    m1_subset_1(sK4(sK2),k1_zfmisc_1(u1_struct_0(sK2))) | ~spl8_1),
% 1.57/0.60    inference(avatar_component_clause,[],[f111])).
% 1.57/0.60  fof(f147,plain,(
% 1.57/0.60    spl8_4 | spl8_5),
% 1.57/0.60    inference(avatar_split_clause,[],[f137,f144,f140])).
% 1.57/0.60  fof(f137,plain,(
% 1.57/0.60    v1_xboole_0(u1_struct_0(sK2)) | r2_hidden(sK3,u1_struct_0(sK2))),
% 1.57/0.60    inference(resolution,[],[f73,f87])).
% 1.57/0.60  fof(f87,plain,(
% 1.57/0.60    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 1.57/0.60    inference(cnf_transformation,[],[f38])).
% 1.57/0.60  fof(f38,plain,(
% 1.57/0.60    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.57/0.60    inference(flattening,[],[f37])).
% 1.57/0.60  fof(f37,plain,(
% 1.57/0.60    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.57/0.60    inference(ennf_transformation,[],[f5])).
% 1.57/0.60  fof(f5,axiom,(
% 1.57/0.60    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.57/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 1.57/0.60  fof(f131,plain,(
% 1.57/0.60    spl8_3),
% 1.57/0.60    inference(avatar_contradiction_clause,[],[f130])).
% 1.57/0.60  fof(f130,plain,(
% 1.57/0.60    $false | spl8_3),
% 1.57/0.60    inference(subsumption_resolution,[],[f129,f68])).
% 1.57/0.60  fof(f129,plain,(
% 1.57/0.60    ~l1_pre_topc(sK0) | spl8_3),
% 1.57/0.60    inference(subsumption_resolution,[],[f124,f121])).
% 1.57/0.60  fof(f121,plain,(
% 1.57/0.60    ~l1_pre_topc(sK2) | spl8_3),
% 1.57/0.60    inference(avatar_component_clause,[],[f119])).
% 1.57/0.60  fof(f119,plain,(
% 1.57/0.60    spl8_3 <=> l1_pre_topc(sK2)),
% 1.57/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 1.57/0.60  fof(f128,plain,(
% 1.57/0.60    spl8_2),
% 1.57/0.60    inference(avatar_contradiction_clause,[],[f127])).
% 1.57/0.60  fof(f127,plain,(
% 1.57/0.60    $false | spl8_2),
% 1.57/0.60    inference(subsumption_resolution,[],[f126,f67])).
% 1.57/0.60  fof(f126,plain,(
% 1.57/0.60    ~v2_pre_topc(sK0) | spl8_2),
% 1.57/0.60    inference(subsumption_resolution,[],[f125,f68])).
% 1.57/0.60  fof(f125,plain,(
% 1.57/0.60    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | spl8_2),
% 1.57/0.60    inference(subsumption_resolution,[],[f123,f117])).
% 1.57/0.60  fof(f117,plain,(
% 1.57/0.60    ~v2_pre_topc(sK2) | spl8_2),
% 1.57/0.60    inference(avatar_component_clause,[],[f115])).
% 1.57/0.60  fof(f115,plain,(
% 1.57/0.60    spl8_2 <=> v2_pre_topc(sK2)),
% 1.57/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 1.57/0.60  fof(f122,plain,(
% 1.57/0.60    spl8_1 | ~spl8_2 | ~spl8_3),
% 1.57/0.60    inference(avatar_split_clause,[],[f109,f119,f115,f111])).
% 1.57/0.60  fof(f109,plain,(
% 1.57/0.60    ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | m1_subset_1(sK4(sK2),k1_zfmisc_1(u1_struct_0(sK2)))),
% 1.57/0.60    inference(resolution,[],[f70,f79])).
% 1.57/0.60  fof(f79,plain,(
% 1.57/0.60    ( ! [X0] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 1.57/0.60    inference(cnf_transformation,[],[f52])).
% 1.57/0.60  % SZS output end Proof for theBenchmark
% 1.57/0.60  % (30578)------------------------------
% 1.57/0.60  % (30578)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.60  % (30578)Termination reason: Refutation
% 1.57/0.60  
% 1.57/0.60  % (30578)Memory used [KB]: 11257
% 1.57/0.60  % (30578)Time elapsed: 0.135 s
% 1.57/0.60  % (30578)------------------------------
% 1.57/0.60  % (30578)------------------------------
% 1.57/0.60  % (30587)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.57/0.60  % (30569)Success in time 0.225 s
%------------------------------------------------------------------------------
