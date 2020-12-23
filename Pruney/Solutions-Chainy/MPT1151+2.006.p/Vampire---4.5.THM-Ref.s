%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:47 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 191 expanded)
%              Number of leaves         :   25 (  77 expanded)
%              Depth                    :   18
%              Number of atoms          :  459 ( 795 expanded)
%              Number of equality atoms :   45 (  92 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f246,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f71,f76,f81,f86,f93,f99,f118,f123,f162,f211,f245])).

fof(f245,plain,
    ( spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_8
    | ~ spl4_9
    | spl4_13 ),
    inference(avatar_contradiction_clause,[],[f244])).

fof(f244,plain,
    ( $false
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_8
    | ~ spl4_9
    | spl4_13 ),
    inference(subsumption_resolution,[],[f243,f241])).

fof(f241,plain,
    ( ~ r2_hidden(sK1(u1_struct_0(sK0),k2_orders_2(sK0,k1_xboole_0)),k2_orders_2(sK0,k1_xboole_0))
    | ~ spl4_9
    | spl4_13 ),
    inference(unit_resulting_resolution,[],[f122,f210,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK1(X0,X1),X1)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ~ r2_hidden(sK1(X0,X1),X1)
        & m1_subset_1(sK1(X0,X1),X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & m1_subset_1(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( ! [X2] :
            ( m1_subset_1(X2,X0)
           => r2_hidden(X2,X1) )
       => X0 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_subset_1)).

fof(f210,plain,
    ( u1_struct_0(sK0) != k2_orders_2(sK0,k1_xboole_0)
    | spl4_13 ),
    inference(avatar_component_clause,[],[f208])).

fof(f208,plain,
    ( spl4_13
  <=> u1_struct_0(sK0) = k2_orders_2(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f122,plain,
    ( m1_subset_1(k2_orders_2(sK0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl4_9
  <=> m1_subset_1(k2_orders_2(sK0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f243,plain,
    ( r2_hidden(sK1(u1_struct_0(sK0),k2_orders_2(sK0,k1_xboole_0)),k2_orders_2(sK0,k1_xboole_0))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_8
    | ~ spl4_9
    | spl4_13 ),
    inference(forward_demodulation,[],[f240,f117])).

fof(f117,plain,
    ( k2_orders_2(sK0,k1_xboole_0) = a_2_1_orders_2(sK0,k1_xboole_0)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl4_8
  <=> k2_orders_2(sK0,k1_xboole_0) = a_2_1_orders_2(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f240,plain,
    ( r2_hidden(sK1(u1_struct_0(sK0),k2_orders_2(sK0,k1_xboole_0)),a_2_1_orders_2(sK0,k1_xboole_0))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_9
    | spl4_13 ),
    inference(unit_resulting_resolution,[],[f44,f122,f94,f210,f145])).

fof(f145,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(sK1(u1_struct_0(sK0),X1),a_2_1_orders_2(sK0,X0))
        | u1_struct_0(sK0) = X1
        | r2_hidden(sK2(sK0,X0,sK1(u1_struct_0(sK0),X1)),X0) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(resolution,[],[f111,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK1(X0,X1),X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f111,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_hidden(sK2(sK0,X0,X1),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X1,a_2_1_orders_2(sK0,X0)) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f110,f65])).

fof(f65,plain,
    ( ~ v2_struct_0(sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl4_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f110,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK2(sK0,X0,X1),X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X1,a_2_1_orders_2(sK0,X0))
        | v2_struct_0(sK0) )
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f109,f70])).

fof(f70,plain,
    ( v3_orders_2(sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl4_2
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f109,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK2(sK0,X0,X1),X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X1,a_2_1_orders_2(sK0,X0))
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f108,f75])).

fof(f75,plain,
    ( v4_orders_2(sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl4_3
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f108,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK2(sK0,X0,X1),X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X1,a_2_1_orders_2(sK0,X0))
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f107,f80])).

fof(f80,plain,
    ( v5_orders_2(sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl4_4
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f107,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK2(sK0,X0,X1),X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X1,a_2_1_orders_2(sK0,X0))
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_5 ),
    inference(resolution,[],[f60,f85])).

fof(f85,plain,
    ( l1_orders_2(sK0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl4_5
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f60,plain,(
    ! [X2,X3,X1] :
      ( ~ l1_orders_2(X1)
      | r2_hidden(sK2(X1,X2,X3),X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | r2_hidden(X3,a_2_1_orders_2(X1,X2))
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      | r2_hidden(sK2(X1,X2,X3),X2)
      | X0 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
          | ! [X3] :
              ( ( ~ r2_orders_2(X1,X3,sK2(X1,X2,X3))
                & r2_hidden(sK2(X1,X2,X3),X2)
                & m1_subset_1(sK2(X1,X2,X3),u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( ! [X6] :
                ( r2_orders_2(X1,sK3(X0,X1,X2),X6)
                | ~ r2_hidden(X6,X2)
                | ~ m1_subset_1(X6,u1_struct_0(X1)) )
            & sK3(X0,X1,X2) = X0
            & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f33,f35,f34])).

fof(f34,plain,(
    ! [X3,X2,X1] :
      ( ? [X4] :
          ( ~ r2_orders_2(X1,X3,X4)
          & r2_hidden(X4,X2)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r2_orders_2(X1,X3,sK2(X1,X2,X3))
        & r2_hidden(sK2(X1,X2,X3),X2)
        & m1_subset_1(sK2(X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r2_orders_2(X1,X5,X6)
              | ~ r2_hidden(X6,X2)
              | ~ m1_subset_1(X6,u1_struct_0(X1)) )
          & X0 = X5
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ! [X6] :
            ( r2_orders_2(X1,sK3(X0,X1,X2),X6)
            | ~ r2_hidden(X6,X2)
            | ~ m1_subset_1(X6,u1_struct_0(X1)) )
        & sK3(X0,X1,X2) = X0
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
          | ! [X3] :
              ( ? [X4] :
                  ( ~ r2_orders_2(X1,X3,X4)
                  & r2_hidden(X4,X2)
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X5] :
              ( ! [X6] :
                  ( r2_orders_2(X1,X5,X6)
                  | ~ r2_hidden(X6,X2)
                  | ~ m1_subset_1(X6,u1_struct_0(X1)) )
              & X0 = X5
              & m1_subset_1(X5,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
          | ! [X3] :
              ( ? [X4] :
                  ( ~ r2_orders_2(X1,X3,X4)
                  & r2_hidden(X4,X2)
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X3] :
              ( ! [X4] :
                  ( r2_orders_2(X1,X3,X4)
                  | ~ r2_hidden(X4,X2)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              & X0 = X3
              & m1_subset_1(X3,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r2_orders_2(X1,X3,X4)
                | ~ r2_hidden(X4,X2)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r2_orders_2(X1,X3,X4)
                | ~ r2_hidden(X4,X2)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f10])).

% (15302)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & l1_orders_2(X1)
        & v5_orders_2(X1)
        & v4_orders_2(X1)
        & v3_orders_2(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_hidden(X4,X2)
                 => r2_orders_2(X1,X3,X4) ) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_1_orders_2)).

fof(f94,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f43,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f43,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f44,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f211,plain,
    ( ~ spl4_13
    | spl4_6
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f163,f159,f90,f208])).

fof(f90,plain,
    ( spl4_6
  <=> u1_struct_0(sK0) = k2_orders_2(sK0,k1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f159,plain,
    ( spl4_10
  <=> k1_xboole_0 = k1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f163,plain,
    ( u1_struct_0(sK0) != k2_orders_2(sK0,k1_xboole_0)
    | spl4_6
    | ~ spl4_10 ),
    inference(superposition,[],[f92,f161])).

fof(f161,plain,
    ( k1_xboole_0 = k1_struct_0(sK0)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f159])).

fof(f92,plain,
    ( u1_struct_0(sK0) != k2_orders_2(sK0,k1_struct_0(sK0))
    | spl4_6 ),
    inference(avatar_component_clause,[],[f90])).

fof(f162,plain,
    ( spl4_10
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f112,f96,f159])).

fof(f96,plain,
    ( spl4_7
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f112,plain,
    ( k1_xboole_0 = k1_struct_0(sK0)
    | ~ spl4_7 ),
    inference(unit_resulting_resolution,[],[f98,f45])).

fof(f45,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k1_xboole_0 = k1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k1_xboole_0 = k1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_struct_0)).

fof(f98,plain,
    ( l1_struct_0(sK0)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f96])).

fof(f123,plain,
    ( spl4_9
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f106,f83,f78,f73,f68,f63,f120])).

fof(f106,plain,
    ( m1_subset_1(k2_orders_2(sK0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f65,f70,f75,f80,f85,f44,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_orders_2)).

fof(f118,plain,
    ( spl4_8
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f100,f83,f78,f73,f68,f63,f115])).

fof(f100,plain,
    ( k2_orders_2(sK0,k1_xboole_0) = a_2_1_orders_2(sK0,k1_xboole_0)
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f65,f70,f75,f80,f85,f44,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_orders_2)).

fof(f99,plain,
    ( spl4_7
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f87,f83,f96])).

fof(f87,plain,
    ( l1_struct_0(sK0)
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f85,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f93,plain,(
    ~ spl4_6 ),
    inference(avatar_split_clause,[],[f42,f90])).

fof(f42,plain,(
    u1_struct_0(sK0) != k2_orders_2(sK0,k1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( u1_struct_0(sK0) != k2_orders_2(sK0,k1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f28])).

fof(f28,plain,
    ( ? [X0] :
        ( u1_struct_0(X0) != k2_orders_2(X0,k1_struct_0(X0))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( u1_struct_0(sK0) != k2_orders_2(sK0,k1_struct_0(sK0))
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( u1_struct_0(X0) != k2_orders_2(X0,k1_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( u1_struct_0(X0) != k2_orders_2(X0,k1_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => u1_struct_0(X0) = k2_orders_2(X0,k1_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => u1_struct_0(X0) = k2_orders_2(X0,k1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_orders_2)).

fof(f86,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f41,f83])).

fof(f41,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f81,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f40,f78])).

fof(f40,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f76,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f39,f73])).

fof(f39,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f71,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f38,f68])).

fof(f38,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f66,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f37,f63])).

fof(f37,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:15:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (15280)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.50  % (15292)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.50  % (15290)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.50  % (15300)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.50  % (15286)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.50  % (15282)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.51  % (15305)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.51  % (15285)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.51  % (15299)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.51  % (15296)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.51  % (15286)Refutation not found, incomplete strategy% (15286)------------------------------
% 0.22/0.51  % (15286)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (15286)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (15286)Memory used [KB]: 10618
% 0.22/0.51  % (15286)Time elapsed: 0.093 s
% 0.22/0.51  % (15286)------------------------------
% 0.22/0.51  % (15286)------------------------------
% 0.22/0.51  % (15283)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.51  % (15305)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % (15293)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (15287)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.52  % (15285)Refutation not found, incomplete strategy% (15285)------------------------------
% 0.22/0.52  % (15285)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (15285)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (15285)Memory used [KB]: 6140
% 0.22/0.52  % (15285)Time elapsed: 0.095 s
% 0.22/0.52  % (15285)------------------------------
% 0.22/0.52  % (15285)------------------------------
% 0.22/0.52  % (15304)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.52  % (15289)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.52  % (15303)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.52  % (15291)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.52  % (15295)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f246,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(avatar_sat_refutation,[],[f66,f71,f76,f81,f86,f93,f99,f118,f123,f162,f211,f245])).
% 0.22/0.53  fof(f245,plain,(
% 0.22/0.53    spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_8 | ~spl4_9 | spl4_13),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f244])).
% 0.22/0.53  fof(f244,plain,(
% 0.22/0.53    $false | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_8 | ~spl4_9 | spl4_13)),
% 0.22/0.53    inference(subsumption_resolution,[],[f243,f241])).
% 0.22/0.53  fof(f241,plain,(
% 0.22/0.53    ~r2_hidden(sK1(u1_struct_0(sK0),k2_orders_2(sK0,k1_xboole_0)),k2_orders_2(sK0,k1_xboole_0)) | (~spl4_9 | spl4_13)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f122,f210,f49])).
% 0.22/0.53  fof(f49,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r2_hidden(sK1(X0,X1),X1) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f31])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    ! [X0,X1] : (X0 = X1 | (~r2_hidden(sK1(X0,X1),X1) & m1_subset_1(sK1(X0,X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f30])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & m1_subset_1(sK1(X0,X1),X0)))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    ! [X0,X1] : (X0 = X1 | ? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.53    inference(flattening,[],[f19])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ! [X0,X1] : ((X0 = X1 | ? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (! [X2] : (m1_subset_1(X2,X0) => r2_hidden(X2,X1)) => X0 = X1))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_subset_1)).
% 0.22/0.53  fof(f210,plain,(
% 0.22/0.53    u1_struct_0(sK0) != k2_orders_2(sK0,k1_xboole_0) | spl4_13),
% 0.22/0.53    inference(avatar_component_clause,[],[f208])).
% 0.22/0.53  fof(f208,plain,(
% 0.22/0.53    spl4_13 <=> u1_struct_0(sK0) = k2_orders_2(sK0,k1_xboole_0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.22/0.53  fof(f122,plain,(
% 0.22/0.53    m1_subset_1(k2_orders_2(sK0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_9),
% 0.22/0.53    inference(avatar_component_clause,[],[f120])).
% 0.22/0.53  fof(f120,plain,(
% 0.22/0.53    spl4_9 <=> m1_subset_1(k2_orders_2(sK0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.22/0.53  fof(f243,plain,(
% 0.22/0.53    r2_hidden(sK1(u1_struct_0(sK0),k2_orders_2(sK0,k1_xboole_0)),k2_orders_2(sK0,k1_xboole_0)) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_8 | ~spl4_9 | spl4_13)),
% 0.22/0.53    inference(forward_demodulation,[],[f240,f117])).
% 0.22/0.53  fof(f117,plain,(
% 0.22/0.53    k2_orders_2(sK0,k1_xboole_0) = a_2_1_orders_2(sK0,k1_xboole_0) | ~spl4_8),
% 0.22/0.53    inference(avatar_component_clause,[],[f115])).
% 0.22/0.53  fof(f115,plain,(
% 0.22/0.53    spl4_8 <=> k2_orders_2(sK0,k1_xboole_0) = a_2_1_orders_2(sK0,k1_xboole_0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.22/0.53  fof(f240,plain,(
% 0.22/0.53    r2_hidden(sK1(u1_struct_0(sK0),k2_orders_2(sK0,k1_xboole_0)),a_2_1_orders_2(sK0,k1_xboole_0)) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_9 | spl4_13)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f44,f122,f94,f210,f145])).
% 0.22/0.53  fof(f145,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK1(u1_struct_0(sK0),X1),a_2_1_orders_2(sK0,X0)) | u1_struct_0(sK0) = X1 | r2_hidden(sK2(sK0,X0,sK1(u1_struct_0(sK0),X1)),X0)) ) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5)),
% 0.22/0.53    inference(resolution,[],[f111,f48])).
% 0.22/0.53  fof(f48,plain,(
% 0.22/0.53    ( ! [X0,X1] : (m1_subset_1(sK1(X0,X1),X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f31])).
% 0.22/0.53  fof(f111,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | r2_hidden(sK2(sK0,X0,X1),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X1,a_2_1_orders_2(sK0,X0))) ) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5)),
% 0.22/0.53    inference(subsumption_resolution,[],[f110,f65])).
% 0.22/0.53  fof(f65,plain,(
% 0.22/0.53    ~v2_struct_0(sK0) | spl4_1),
% 0.22/0.53    inference(avatar_component_clause,[],[f63])).
% 0.22/0.53  fof(f63,plain,(
% 0.22/0.53    spl4_1 <=> v2_struct_0(sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.53  fof(f110,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r2_hidden(sK2(sK0,X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X1,a_2_1_orders_2(sK0,X0)) | v2_struct_0(sK0)) ) | (~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5)),
% 0.22/0.53    inference(subsumption_resolution,[],[f109,f70])).
% 0.22/0.53  fof(f70,plain,(
% 0.22/0.53    v3_orders_2(sK0) | ~spl4_2),
% 0.22/0.53    inference(avatar_component_clause,[],[f68])).
% 0.22/0.53  fof(f68,plain,(
% 0.22/0.53    spl4_2 <=> v3_orders_2(sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.53  fof(f109,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r2_hidden(sK2(sK0,X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X1,a_2_1_orders_2(sK0,X0)) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl4_3 | ~spl4_4 | ~spl4_5)),
% 0.22/0.53    inference(subsumption_resolution,[],[f108,f75])).
% 0.22/0.53  fof(f75,plain,(
% 0.22/0.53    v4_orders_2(sK0) | ~spl4_3),
% 0.22/0.53    inference(avatar_component_clause,[],[f73])).
% 0.22/0.53  fof(f73,plain,(
% 0.22/0.53    spl4_3 <=> v4_orders_2(sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.53  fof(f108,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r2_hidden(sK2(sK0,X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X1,a_2_1_orders_2(sK0,X0)) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl4_4 | ~spl4_5)),
% 0.22/0.53    inference(subsumption_resolution,[],[f107,f80])).
% 0.22/0.53  fof(f80,plain,(
% 0.22/0.53    v5_orders_2(sK0) | ~spl4_4),
% 0.22/0.53    inference(avatar_component_clause,[],[f78])).
% 0.22/0.53  fof(f78,plain,(
% 0.22/0.53    spl4_4 <=> v5_orders_2(sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.53  fof(f107,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r2_hidden(sK2(sK0,X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X1,a_2_1_orders_2(sK0,X0)) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl4_5),
% 0.22/0.53    inference(resolution,[],[f60,f85])).
% 0.22/0.53  fof(f85,plain,(
% 0.22/0.53    l1_orders_2(sK0) | ~spl4_5),
% 0.22/0.53    inference(avatar_component_clause,[],[f83])).
% 0.22/0.53  fof(f83,plain,(
% 0.22/0.53    spl4_5 <=> l1_orders_2(sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.22/0.53  fof(f60,plain,(
% 0.22/0.53    ( ! [X2,X3,X1] : (~l1_orders_2(X1) | r2_hidden(sK2(X1,X2,X3),X2) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | r2_hidden(X3,a_2_1_orders_2(X1,X2)) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 0.22/0.53    inference(equality_resolution,[],[f56])).
% 0.22/0.53  fof(f56,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,a_2_1_orders_2(X1,X2)) | r2_hidden(sK2(X1,X2,X3),X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f36])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : ((~r2_orders_2(X1,X3,sK2(X1,X2,X3)) & r2_hidden(sK2(X1,X2,X3),X2) & m1_subset_1(sK2(X1,X2,X3),u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((! [X6] : (r2_orders_2(X1,sK3(X0,X1,X2),X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK3(X0,X1,X2) = X0 & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f33,f35,f34])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    ! [X3,X2,X1] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) => (~r2_orders_2(X1,X3,sK2(X1,X2,X3)) & r2_hidden(sK2(X1,X2,X3),X2) & m1_subset_1(sK2(X1,X2,X3),u1_struct_0(X1))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    ! [X2,X1,X0] : (? [X5] : (! [X6] : (r2_orders_2(X1,X5,X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) => (! [X6] : (r2_orders_2(X1,sK3(X0,X1,X2),X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK3(X0,X1,X2) = X0 & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X5] : (! [X6] : (r2_orders_2(X1,X5,X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 0.22/0.53    inference(rectify,[],[f32])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 0.22/0.53    inference(nnf_transformation,[],[f25])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 0.22/0.53    inference(flattening,[],[f24])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : ((r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)))),
% 0.22/0.53    inference(ennf_transformation,[],[f10])).
% 0.22/0.53  % (15302)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.53  fof(f10,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) & l1_orders_2(X1) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r2_hidden(X4,X2) => r2_orders_2(X1,X3,X4))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_1_orders_2)).
% 0.22/0.53  fof(f94,plain,(
% 0.22/0.53    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f43,f51])).
% 0.22/0.53  fof(f51,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f23])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.22/0.53  fof(f43,plain,(
% 0.22/0.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.53  fof(f44,plain,(
% 0.22/0.53    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.22/0.53  fof(f211,plain,(
% 0.22/0.53    ~spl4_13 | spl4_6 | ~spl4_10),
% 0.22/0.53    inference(avatar_split_clause,[],[f163,f159,f90,f208])).
% 0.22/0.53  fof(f90,plain,(
% 0.22/0.53    spl4_6 <=> u1_struct_0(sK0) = k2_orders_2(sK0,k1_struct_0(sK0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.22/0.53  fof(f159,plain,(
% 0.22/0.53    spl4_10 <=> k1_xboole_0 = k1_struct_0(sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.22/0.53  fof(f163,plain,(
% 0.22/0.53    u1_struct_0(sK0) != k2_orders_2(sK0,k1_xboole_0) | (spl4_6 | ~spl4_10)),
% 0.22/0.53    inference(superposition,[],[f92,f161])).
% 0.22/0.53  fof(f161,plain,(
% 0.22/0.53    k1_xboole_0 = k1_struct_0(sK0) | ~spl4_10),
% 0.22/0.53    inference(avatar_component_clause,[],[f159])).
% 0.22/0.53  fof(f92,plain,(
% 0.22/0.53    u1_struct_0(sK0) != k2_orders_2(sK0,k1_struct_0(sK0)) | spl4_6),
% 0.22/0.53    inference(avatar_component_clause,[],[f90])).
% 0.22/0.53  fof(f162,plain,(
% 0.22/0.53    spl4_10 | ~spl4_7),
% 0.22/0.53    inference(avatar_split_clause,[],[f112,f96,f159])).
% 0.22/0.53  fof(f96,plain,(
% 0.22/0.53    spl4_7 <=> l1_struct_0(sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.22/0.53  fof(f112,plain,(
% 0.22/0.53    k1_xboole_0 = k1_struct_0(sK0) | ~spl4_7),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f98,f45])).
% 0.22/0.53  fof(f45,plain,(
% 0.22/0.53    ( ! [X0] : (~l1_struct_0(X0) | k1_xboole_0 = k1_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f15])).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    ! [X0] : (k1_xboole_0 = k1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0] : (l1_struct_0(X0) => k1_xboole_0 = k1_struct_0(X0))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_struct_0)).
% 0.22/0.53  fof(f98,plain,(
% 0.22/0.53    l1_struct_0(sK0) | ~spl4_7),
% 0.22/0.53    inference(avatar_component_clause,[],[f96])).
% 0.22/0.53  fof(f123,plain,(
% 0.22/0.53    spl4_9 | spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5),
% 0.22/0.53    inference(avatar_split_clause,[],[f106,f83,f78,f73,f68,f63,f120])).
% 0.22/0.53  fof(f106,plain,(
% 0.22/0.53    m1_subset_1(k2_orders_2(sK0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0))) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f65,f70,f75,f80,f85,f44,f50])).
% 0.22/0.53  fof(f50,plain,(
% 0.22/0.53    ( ! [X0,X1] : (m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f22])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f21])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,axiom,(
% 0.22/0.53    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_orders_2)).
% 0.22/0.53  fof(f118,plain,(
% 0.22/0.53    spl4_8 | spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5),
% 0.22/0.53    inference(avatar_split_clause,[],[f100,f83,f78,f73,f68,f63,f115])).
% 0.22/0.53  fof(f100,plain,(
% 0.22/0.53    k2_orders_2(sK0,k1_xboole_0) = a_2_1_orders_2(sK0,k1_xboole_0) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f65,f70,f75,f80,f85,f44,f47])).
% 0.22/0.53  fof(f47,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f18])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f17])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,axiom,(
% 0.22/0.53    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_orders_2)).
% 0.22/0.53  fof(f99,plain,(
% 0.22/0.53    spl4_7 | ~spl4_5),
% 0.22/0.53    inference(avatar_split_clause,[],[f87,f83,f96])).
% 0.22/0.53  fof(f87,plain,(
% 0.22/0.53    l1_struct_0(sK0) | ~spl4_5),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f85,f46])).
% 0.22/0.53  fof(f46,plain,(
% 0.22/0.53    ( ! [X0] : (~l1_orders_2(X0) | l1_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f16])).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f9])).
% 0.22/0.53  fof(f9,axiom,(
% 0.22/0.53    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 0.22/0.53  fof(f93,plain,(
% 0.22/0.53    ~spl4_6),
% 0.22/0.53    inference(avatar_split_clause,[],[f42,f90])).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    u1_struct_0(sK0) != k2_orders_2(sK0,k1_struct_0(sK0))),
% 0.22/0.53    inference(cnf_transformation,[],[f29])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    u1_struct_0(sK0) != k2_orders_2(sK0,k1_struct_0(sK0)) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f28])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    ? [X0] : (u1_struct_0(X0) != k2_orders_2(X0,k1_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (u1_struct_0(sK0) != k2_orders_2(sK0,k1_struct_0(sK0)) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f14,plain,(
% 0.22/0.53    ? [X0] : (u1_struct_0(X0) != k2_orders_2(X0,k1_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f13])).
% 0.22/0.53  fof(f13,plain,(
% 0.22/0.53    ? [X0] : (u1_struct_0(X0) != k2_orders_2(X0,k1_struct_0(X0)) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f12])).
% 0.22/0.53  fof(f12,negated_conjecture,(
% 0.22/0.53    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => u1_struct_0(X0) = k2_orders_2(X0,k1_struct_0(X0)))),
% 0.22/0.53    inference(negated_conjecture,[],[f11])).
% 0.22/0.53  fof(f11,conjecture,(
% 0.22/0.53    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => u1_struct_0(X0) = k2_orders_2(X0,k1_struct_0(X0)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_orders_2)).
% 0.22/0.53  fof(f86,plain,(
% 0.22/0.53    spl4_5),
% 0.22/0.53    inference(avatar_split_clause,[],[f41,f83])).
% 0.22/0.53  fof(f41,plain,(
% 0.22/0.53    l1_orders_2(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f29])).
% 0.22/0.53  fof(f81,plain,(
% 0.22/0.53    spl4_4),
% 0.22/0.53    inference(avatar_split_clause,[],[f40,f78])).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    v5_orders_2(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f29])).
% 0.22/0.53  fof(f76,plain,(
% 0.22/0.53    spl4_3),
% 0.22/0.53    inference(avatar_split_clause,[],[f39,f73])).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    v4_orders_2(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f29])).
% 0.22/0.53  fof(f71,plain,(
% 0.22/0.53    spl4_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f38,f68])).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    v3_orders_2(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f29])).
% 0.22/0.53  fof(f66,plain,(
% 0.22/0.53    ~spl4_1),
% 0.22/0.53    inference(avatar_split_clause,[],[f37,f63])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    ~v2_struct_0(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f29])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (15305)------------------------------
% 0.22/0.53  % (15305)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (15305)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (15305)Memory used [KB]: 10746
% 0.22/0.53  % (15305)Time elapsed: 0.061 s
% 0.22/0.53  % (15305)------------------------------
% 0.22/0.53  % (15305)------------------------------
% 0.22/0.53  % (15275)Success in time 0.166 s
%------------------------------------------------------------------------------
