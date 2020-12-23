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
% DateTime   : Thu Dec  3 13:11:35 EST 2020

% Result     : Theorem 2.42s
% Output     : Refutation 2.42s
% Verified   : 
% Statistics : Number of formulae       :  169 (1356 expanded)
%              Number of leaves         :   27 ( 358 expanded)
%              Depth                    :   39
%              Number of atoms          :  576 (7768 expanded)
%              Number of equality atoms :  120 (1817 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3228,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f142,f200,f2206,f3179,f3227])).

fof(f3227,plain,
    ( spl4_2
    | ~ spl4_3 ),
    inference(avatar_contradiction_clause,[],[f3226])).

fof(f3226,plain,
    ( $false
    | spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f3225,f140])).

fof(f140,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl4_2
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f3225,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f129,f195])).

fof(f195,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f193])).

fof(f193,plain,
    ( spl4_3
  <=> sK1 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f129,plain,(
    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f122,f65])).

fof(f65,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | ~ v3_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | v3_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f47,f49,f48])).

fof(f48,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
              | ~ v3_pre_topc(X1,X0) )
            & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
              | v3_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
            | ~ v3_pre_topc(X1,sK0) )
          & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
            | v3_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ? [X1] :
        ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
          | ~ v3_pre_topc(X1,sK0) )
        & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
          | v3_pre_topc(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
        | ~ v3_pre_topc(sK1,sK0) )
      & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
        | v3_pre_topc(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f25,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).

fof(f122,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f66,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

fof(f66,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f50])).

fof(f3179,plain,(
    ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f3178])).

fof(f3178,plain,
    ( $false
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f3177,f64])).

fof(f64,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f3177,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f3176,f65])).

fof(f3176,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f3175,f66])).

fof(f3175,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f3172,f170])).

fof(f170,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f68,f141])).

fof(f141,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f139])).

fof(f68,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f3172,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl4_2 ),
    inference(superposition,[],[f76,f3141])).

fof(f3141,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f185,f3139])).

fof(f3139,plain,
    ( sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f3138,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X2)
      | r2_hidden(sK3(X0,X1,X2),X0)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f61,f62])).

fof(f62,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f3138,plain,
    ( sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ r2_hidden(sK3(sK1,k2_tops_1(sK0,sK1),sK1),sK1)
    | ~ spl4_2 ),
    inference(duplicate_literal_removal,[],[f3133])).

fof(f3133,plain,
    ( sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ r2_hidden(sK3(sK1,k2_tops_1(sK0,sK1),sK1),sK1)
    | ~ r2_hidden(sK3(sK1,k2_tops_1(sK0,sK1),sK1),sK1)
    | ~ spl4_2 ),
    inference(resolution,[],[f2191,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X1)
      | k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK3(X0,X1,X2),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f2191,plain,
    ( ! [X25] :
        ( ~ r2_hidden(sK3(sK1,X25,sK1),k2_tops_1(sK0,sK1))
        | sK1 = k4_xboole_0(sK1,X25) )
    | ~ spl4_2 ),
    inference(duplicate_literal_removal,[],[f2190])).

fof(f2190,plain,
    ( ! [X25] :
        ( ~ r2_hidden(sK3(sK1,X25,sK1),k2_tops_1(sK0,sK1))
        | sK1 = k4_xboole_0(sK1,X25)
        | ~ r2_hidden(sK3(sK1,X25,sK1),k2_tops_1(sK0,sK1)) )
    | ~ spl4_2 ),
    inference(resolution,[],[f2017,f1985])).

fof(f1985,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,k2_tops_1(sK0,sK1)) )
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f1968,f273])).

fof(f273,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f256,f110])).

fof(f110,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f89,f69])).

fof(f69,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f89,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f256,plain,(
    ! [X4,X5] : ~ r2_hidden(X4,k4_xboole_0(k4_xboole_0(k1_tops_1(sK0,sK1),sK1),X5)) ),
    inference(resolution,[],[f253,f118])).

fof(f118,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f96])).

fof(f96,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f63])).

fof(f253,plain,(
    ! [X1] : ~ r2_hidden(X1,k4_xboole_0(k1_tops_1(sK0,sK1),sK1)) ),
    inference(subsumption_resolution,[],[f252,f118])).

fof(f252,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k4_xboole_0(k1_tops_1(sK0,sK1),sK1))
      | ~ r2_hidden(X1,k1_tops_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f250,f117])).

fof(f117,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f97])).

fof(f97,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f63])).

fof(f250,plain,(
    ! [X1] :
      ( r2_hidden(X1,k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)))
      | ~ r2_hidden(X1,k4_xboole_0(k1_tops_1(sK0,sK1),sK1))
      | ~ r2_hidden(X1,k1_tops_1(sK0,sK1)) ) ),
    inference(superposition,[],[f111,f191])).

fof(f191,plain,(
    k1_tops_1(sK0,sK1) = k4_xboole_0(k1_tops_1(sK0,sK1),k4_xboole_0(k1_tops_1(sK0,sK1),sK1)) ),
    inference(resolution,[],[f188,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f88,f69])).

fof(f88,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f188,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(superposition,[],[f81,f185])).

fof(f81,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f111,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f106])).

fof(f106,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f84,f69])).

fof(f84,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            | ~ r2_hidden(sK2(X0,X1,X2),X0)
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK2(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f54,f55])).

fof(f55,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X0)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(sK2(X0,X1,X2),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
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
    inference(rectify,[],[f53])).

fof(f53,plain,(
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
    inference(flattening,[],[f52])).

fof(f52,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f1968,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k1_xboole_0)
        | ~ r2_hidden(X0,k2_tops_1(sK0,sK1))
        | ~ r2_hidden(X0,sK1) )
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f187,f1963])).

fof(f1963,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f1945,f185])).

fof(f1945,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl4_2 ),
    inference(superposition,[],[f1920,f235])).

fof(f235,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl4_2 ),
    inference(superposition,[],[f180,f141])).

fof(f180,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0) = k4_xboole_0(k2_pre_topc(sK0,sK1),X0) ),
    inference(resolution,[],[f173,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f173,plain,(
    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f172,f66])).

fof(f172,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f171,f158])).

fof(f158,plain,(
    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f157,f65])).

fof(f157,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f156,f133])).

fof(f133,plain,(
    m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f132,f66])).

fof(f132,plain,
    ( m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f92,f124])).

fof(f124,plain,(
    k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1) ),
    inference(resolution,[],[f66,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f92,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f156,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(superposition,[],[f74,f155])).

fof(f155,plain,(
    k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) ),
    inference(forward_demodulation,[],[f126,f124])).

fof(f126,plain,(
    k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f119,f65])).

fof(f119,plain,
    ( k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f66,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_1)).

fof(f74,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f171,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f90,f127])).

fof(f127,plain,(
    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f120,f65])).

fof(f120,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f66,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(f1920,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(duplicate_literal_removal,[],[f1884])).

fof(f1884,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) ) ),
    inference(resolution,[],[f1101,f277])).

fof(f277,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK2(X2,X3,k1_xboole_0),X3)
      | k1_xboole_0 = k4_xboole_0(X2,k4_xboole_0(X2,X3)) ) ),
    inference(resolution,[],[f273,f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X2)
      | r2_hidden(sK2(X0,X1,X2),X1)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f86,f69])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f1101,plain,(
    ! [X6,X7,X5] :
      ( ~ r2_hidden(sK2(X5,X6,k1_xboole_0),k4_xboole_0(X7,X5))
      | k1_xboole_0 = k4_xboole_0(X5,k4_xboole_0(X5,X6)) ) ),
    inference(resolution,[],[f276,f117])).

fof(f276,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1,k1_xboole_0),X0)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(resolution,[],[f273,f105])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X2)
      | r2_hidden(sK2(X0,X1,X2),X0)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f85,f69])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f187,plain,(
    ! [X0] :
      ( r2_hidden(X0,k4_xboole_0(sK1,k1_tops_1(sK0,sK1)))
      | ~ r2_hidden(X0,k2_tops_1(sK0,sK1))
      | ~ r2_hidden(X0,sK1) ) ),
    inference(superposition,[],[f111,f185])).

fof(f2017,plain,
    ( ! [X17,X16] :
        ( r2_hidden(sK3(X16,X17,sK1),X16)
        | ~ r2_hidden(sK3(X16,X17,sK1),k2_tops_1(sK0,sK1))
        | sK1 = k4_xboole_0(X16,X17) )
    | ~ spl4_2 ),
    inference(resolution,[],[f1985,f99])).

fof(f185,plain,(
    k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(superposition,[],[f128,f125])).

fof(f125,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
    inference(resolution,[],[f66,f70])).

fof(f128,plain,(
    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f121,f65])).

fof(f121,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f66,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

fof(f76,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f2206,plain,
    ( ~ spl4_1
    | spl4_4 ),
    inference(avatar_contradiction_clause,[],[f2205])).

fof(f2205,plain,
    ( $false
    | ~ spl4_1
    | spl4_4 ),
    inference(subsumption_resolution,[],[f2203,f137])).

fof(f137,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl4_1
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f2203,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | spl4_4 ),
    inference(subsumption_resolution,[],[f2202,f65])).

fof(f2202,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | spl4_4 ),
    inference(subsumption_resolution,[],[f2201,f66])).

fof(f2201,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl4_4 ),
    inference(subsumption_resolution,[],[f203,f115])).

fof(f115,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f203,plain,
    ( ~ r1_tarski(sK1,sK1)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl4_4 ),
    inference(duplicate_literal_removal,[],[f201])).

fof(f201,plain,
    ( ~ r1_tarski(sK1,sK1)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl4_4 ),
    inference(resolution,[],[f199,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X1,X2)
                  & v3_pre_topc(X1,X0) )
               => r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).

fof(f199,plain,
    ( ~ r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | spl4_4 ),
    inference(avatar_component_clause,[],[f197])).

fof(f197,plain,
    ( spl4_4
  <=> r1_tarski(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f200,plain,
    ( spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f189,f197,f193])).

fof(f189,plain,
    ( ~ r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | sK1 = k1_tops_1(sK0,sK1) ),
    inference(resolution,[],[f188,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f58])).

fof(f142,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f67,f139,f135])).

fof(f67,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f50])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:38:54 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.48  % (14011)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.51  % (14035)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.51  % (14019)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.51  % (14014)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.26/0.53  % (14009)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.26/0.53  % (14023)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.26/0.53  % (14037)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.26/0.53  % (14029)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.26/0.54  % (14015)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.26/0.54  % (14021)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.26/0.54  % (14020)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.26/0.54  % (14032)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.26/0.54  % (14022)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.26/0.54  % (14030)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.41/0.54  % (14031)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.41/0.54  % (14013)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.41/0.54  % (14010)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.41/0.55  % (14024)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.41/0.55  % (14034)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.41/0.55  % (14016)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.41/0.55  % (14025)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.41/0.55  % (14028)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.41/0.55  % (14026)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.41/0.55  % (14008)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.41/0.55  % (14017)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.41/0.56  % (14012)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.41/0.56  % (14018)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.41/0.56  % (14033)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.41/0.57  % (14036)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.41/0.57  % (14027)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.41/0.57  % (14024)Refutation not found, incomplete strategy% (14024)------------------------------
% 1.41/0.57  % (14024)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.57  % (14024)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.57  
% 1.41/0.57  % (14024)Memory used [KB]: 10746
% 1.41/0.57  % (14024)Time elapsed: 0.155 s
% 1.41/0.57  % (14024)------------------------------
% 1.41/0.57  % (14024)------------------------------
% 1.41/0.57  % (14036)Refutation not found, incomplete strategy% (14036)------------------------------
% 1.41/0.57  % (14036)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.57  % (14036)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.57  
% 1.41/0.57  % (14036)Memory used [KB]: 10874
% 1.41/0.57  % (14036)Time elapsed: 0.163 s
% 1.41/0.57  % (14036)------------------------------
% 1.41/0.57  % (14036)------------------------------
% 1.41/0.58  % (14018)Refutation not found, incomplete strategy% (14018)------------------------------
% 1.41/0.58  % (14018)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.58  % (14018)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.58  
% 1.41/0.58  % (14018)Memory used [KB]: 10874
% 1.41/0.58  % (14018)Time elapsed: 0.170 s
% 1.41/0.58  % (14018)------------------------------
% 1.41/0.58  % (14018)------------------------------
% 2.42/0.72  % (14032)Refutation found. Thanks to Tanya!
% 2.42/0.72  % SZS status Theorem for theBenchmark
% 2.42/0.72  % (14038)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.42/0.72  % SZS output start Proof for theBenchmark
% 2.42/0.72  fof(f3228,plain,(
% 2.42/0.72    $false),
% 2.42/0.72    inference(avatar_sat_refutation,[],[f142,f200,f2206,f3179,f3227])).
% 2.42/0.72  fof(f3227,plain,(
% 2.42/0.72    spl4_2 | ~spl4_3),
% 2.42/0.72    inference(avatar_contradiction_clause,[],[f3226])).
% 2.42/0.72  fof(f3226,plain,(
% 2.42/0.72    $false | (spl4_2 | ~spl4_3)),
% 2.42/0.72    inference(subsumption_resolution,[],[f3225,f140])).
% 2.42/0.72  fof(f140,plain,(
% 2.42/0.72    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | spl4_2),
% 2.42/0.72    inference(avatar_component_clause,[],[f139])).
% 2.42/0.72  fof(f139,plain,(
% 2.42/0.72    spl4_2 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)),
% 2.42/0.72    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 2.42/0.72  fof(f3225,plain,(
% 2.42/0.72    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~spl4_3),
% 2.42/0.72    inference(forward_demodulation,[],[f129,f195])).
% 2.42/0.72  fof(f195,plain,(
% 2.42/0.72    sK1 = k1_tops_1(sK0,sK1) | ~spl4_3),
% 2.42/0.72    inference(avatar_component_clause,[],[f193])).
% 2.42/0.72  fof(f193,plain,(
% 2.42/0.72    spl4_3 <=> sK1 = k1_tops_1(sK0,sK1)),
% 2.42/0.72    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 2.42/0.72  fof(f129,plain,(
% 2.42/0.72    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 2.42/0.72    inference(subsumption_resolution,[],[f122,f65])).
% 2.42/0.72  fof(f65,plain,(
% 2.42/0.72    l1_pre_topc(sK0)),
% 2.42/0.72    inference(cnf_transformation,[],[f50])).
% 2.42/0.72  fof(f50,plain,(
% 2.42/0.72    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 2.42/0.72    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f47,f49,f48])).
% 2.42/0.72  fof(f48,plain,(
% 2.42/0.72    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 2.42/0.72    introduced(choice_axiom,[])).
% 2.42/0.72  fof(f49,plain,(
% 2.42/0.72    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.42/0.72    introduced(choice_axiom,[])).
% 2.42/0.72  fof(f47,plain,(
% 2.42/0.72    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.42/0.72    inference(flattening,[],[f46])).
% 2.42/0.72  fof(f46,plain,(
% 2.42/0.72    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.42/0.72    inference(nnf_transformation,[],[f28])).
% 2.42/0.72  fof(f28,plain,(
% 2.42/0.72    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.42/0.72    inference(flattening,[],[f27])).
% 2.42/0.72  fof(f27,plain,(
% 2.42/0.72    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.42/0.72    inference(ennf_transformation,[],[f26])).
% 2.42/0.72  fof(f26,negated_conjecture,(
% 2.42/0.72    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 2.42/0.72    inference(negated_conjecture,[],[f25])).
% 2.42/0.72  fof(f25,conjecture,(
% 2.42/0.72    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 2.42/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).
% 2.42/0.72  fof(f122,plain,(
% 2.42/0.72    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 2.42/0.72    inference(resolution,[],[f66,f71])).
% 2.42/0.72  fof(f71,plain,(
% 2.42/0.72    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~l1_pre_topc(X0)) )),
% 2.42/0.72    inference(cnf_transformation,[],[f30])).
% 2.42/0.72  fof(f30,plain,(
% 2.42/0.72    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.42/0.72    inference(ennf_transformation,[],[f20])).
% 2.42/0.72  fof(f20,axiom,(
% 2.42/0.72    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 2.42/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).
% 2.42/0.72  fof(f66,plain,(
% 2.42/0.72    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.42/0.72    inference(cnf_transformation,[],[f50])).
% 2.42/0.72  fof(f3179,plain,(
% 2.42/0.72    ~spl4_2),
% 2.42/0.72    inference(avatar_contradiction_clause,[],[f3178])).
% 2.42/0.72  fof(f3178,plain,(
% 2.42/0.72    $false | ~spl4_2),
% 2.42/0.72    inference(subsumption_resolution,[],[f3177,f64])).
% 2.42/0.72  fof(f64,plain,(
% 2.42/0.72    v2_pre_topc(sK0)),
% 2.42/0.72    inference(cnf_transformation,[],[f50])).
% 2.42/0.72  fof(f3177,plain,(
% 2.42/0.72    ~v2_pre_topc(sK0) | ~spl4_2),
% 2.42/0.72    inference(subsumption_resolution,[],[f3176,f65])).
% 2.42/0.72  fof(f3176,plain,(
% 2.42/0.72    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl4_2),
% 2.42/0.72    inference(subsumption_resolution,[],[f3175,f66])).
% 2.42/0.72  fof(f3175,plain,(
% 2.42/0.72    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl4_2),
% 2.42/0.72    inference(subsumption_resolution,[],[f3172,f170])).
% 2.42/0.72  fof(f170,plain,(
% 2.42/0.72    ~v3_pre_topc(sK1,sK0) | ~spl4_2),
% 2.42/0.72    inference(subsumption_resolution,[],[f68,f141])).
% 2.42/0.72  fof(f141,plain,(
% 2.42/0.72    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~spl4_2),
% 2.42/0.72    inference(avatar_component_clause,[],[f139])).
% 2.42/0.72  fof(f68,plain,(
% 2.42/0.72    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)),
% 2.42/0.72    inference(cnf_transformation,[],[f50])).
% 2.42/0.72  fof(f3172,plain,(
% 2.42/0.72    v3_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl4_2),
% 2.42/0.72    inference(superposition,[],[f76,f3141])).
% 2.42/0.72  fof(f3141,plain,(
% 2.42/0.72    sK1 = k1_tops_1(sK0,sK1) | ~spl4_2),
% 2.42/0.72    inference(backward_demodulation,[],[f185,f3139])).
% 2.42/0.72  fof(f3139,plain,(
% 2.42/0.72    sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl4_2),
% 2.42/0.72    inference(subsumption_resolution,[],[f3138,f99])).
% 2.42/0.72  fof(f99,plain,(
% 2.42/0.72    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) )),
% 2.42/0.72    inference(cnf_transformation,[],[f63])).
% 2.42/0.72  fof(f63,plain,(
% 2.42/0.72    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.42/0.72    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f61,f62])).
% 2.42/0.72  fof(f62,plain,(
% 2.42/0.72    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 2.42/0.72    introduced(choice_axiom,[])).
% 2.42/0.72  fof(f61,plain,(
% 2.42/0.72    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.42/0.72    inference(rectify,[],[f60])).
% 2.42/0.72  fof(f60,plain,(
% 2.42/0.72    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.42/0.72    inference(flattening,[],[f59])).
% 2.42/0.72  fof(f59,plain,(
% 2.42/0.72    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.42/0.72    inference(nnf_transformation,[],[f2])).
% 2.42/0.72  fof(f2,axiom,(
% 2.42/0.72    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.42/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 2.42/0.72  fof(f3138,plain,(
% 2.42/0.72    sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~r2_hidden(sK3(sK1,k2_tops_1(sK0,sK1),sK1),sK1) | ~spl4_2),
% 2.42/0.72    inference(duplicate_literal_removal,[],[f3133])).
% 2.42/0.72  fof(f3133,plain,(
% 2.42/0.72    sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~r2_hidden(sK3(sK1,k2_tops_1(sK0,sK1),sK1),sK1) | ~r2_hidden(sK3(sK1,k2_tops_1(sK0,sK1),sK1),sK1) | ~spl4_2),
% 2.42/0.72    inference(resolution,[],[f2191,f101])).
% 2.42/0.72  fof(f101,plain,(
% 2.42/0.72    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X1) | k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) )),
% 2.42/0.72    inference(cnf_transformation,[],[f63])).
% 2.42/0.72  fof(f2191,plain,(
% 2.42/0.72    ( ! [X25] : (~r2_hidden(sK3(sK1,X25,sK1),k2_tops_1(sK0,sK1)) | sK1 = k4_xboole_0(sK1,X25)) ) | ~spl4_2),
% 2.42/0.72    inference(duplicate_literal_removal,[],[f2190])).
% 2.42/0.72  fof(f2190,plain,(
% 2.42/0.72    ( ! [X25] : (~r2_hidden(sK3(sK1,X25,sK1),k2_tops_1(sK0,sK1)) | sK1 = k4_xboole_0(sK1,X25) | ~r2_hidden(sK3(sK1,X25,sK1),k2_tops_1(sK0,sK1))) ) | ~spl4_2),
% 2.42/0.72    inference(resolution,[],[f2017,f1985])).
% 2.42/0.72  fof(f1985,plain,(
% 2.42/0.72    ( ! [X0] : (~r2_hidden(X0,sK1) | ~r2_hidden(X0,k2_tops_1(sK0,sK1))) ) | ~spl4_2),
% 2.42/0.72    inference(subsumption_resolution,[],[f1968,f273])).
% 2.42/0.72  fof(f273,plain,(
% 2.42/0.72    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 2.42/0.72    inference(superposition,[],[f256,f110])).
% 2.42/0.72  fof(f110,plain,(
% 2.42/0.72    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 2.42/0.72    inference(definition_unfolding,[],[f89,f69])).
% 2.42/0.72  fof(f69,plain,(
% 2.42/0.72    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.42/0.72    inference(cnf_transformation,[],[f9])).
% 2.42/0.72  fof(f9,axiom,(
% 2.42/0.72    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.42/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.42/0.72  fof(f89,plain,(
% 2.42/0.72    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 2.42/0.72    inference(cnf_transformation,[],[f6])).
% 2.42/0.72  fof(f6,axiom,(
% 2.42/0.72    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 2.42/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 2.42/0.72  fof(f256,plain,(
% 2.42/0.72    ( ! [X4,X5] : (~r2_hidden(X4,k4_xboole_0(k4_xboole_0(k1_tops_1(sK0,sK1),sK1),X5))) )),
% 2.42/0.72    inference(resolution,[],[f253,f118])).
% 2.42/0.72  fof(f118,plain,(
% 2.42/0.72    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 2.42/0.72    inference(equality_resolution,[],[f96])).
% 2.42/0.72  fof(f96,plain,(
% 2.42/0.72    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.42/0.72    inference(cnf_transformation,[],[f63])).
% 2.42/0.72  fof(f253,plain,(
% 2.42/0.72    ( ! [X1] : (~r2_hidden(X1,k4_xboole_0(k1_tops_1(sK0,sK1),sK1))) )),
% 2.42/0.72    inference(subsumption_resolution,[],[f252,f118])).
% 2.42/0.72  fof(f252,plain,(
% 2.42/0.72    ( ! [X1] : (~r2_hidden(X1,k4_xboole_0(k1_tops_1(sK0,sK1),sK1)) | ~r2_hidden(X1,k1_tops_1(sK0,sK1))) )),
% 2.42/0.72    inference(subsumption_resolution,[],[f250,f117])).
% 2.42/0.72  fof(f117,plain,(
% 2.42/0.72    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 2.42/0.72    inference(equality_resolution,[],[f97])).
% 2.42/0.72  fof(f97,plain,(
% 2.42/0.72    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.42/0.72    inference(cnf_transformation,[],[f63])).
% 2.42/0.72  fof(f250,plain,(
% 2.42/0.72    ( ! [X1] : (r2_hidden(X1,k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))) | ~r2_hidden(X1,k4_xboole_0(k1_tops_1(sK0,sK1),sK1)) | ~r2_hidden(X1,k1_tops_1(sK0,sK1))) )),
% 2.42/0.72    inference(superposition,[],[f111,f191])).
% 2.42/0.72  fof(f191,plain,(
% 2.42/0.72    k1_tops_1(sK0,sK1) = k4_xboole_0(k1_tops_1(sK0,sK1),k4_xboole_0(k1_tops_1(sK0,sK1),sK1))),
% 2.42/0.72    inference(resolution,[],[f188,f109])).
% 2.42/0.72  fof(f109,plain,(
% 2.42/0.72    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0) )),
% 2.42/0.72    inference(definition_unfolding,[],[f88,f69])).
% 2.42/0.72  fof(f88,plain,(
% 2.42/0.72    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 2.42/0.72    inference(cnf_transformation,[],[f41])).
% 2.42/0.72  fof(f41,plain,(
% 2.42/0.72    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.42/0.72    inference(ennf_transformation,[],[f5])).
% 2.42/0.72  fof(f5,axiom,(
% 2.42/0.72    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.42/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.42/0.72  fof(f188,plain,(
% 2.42/0.72    r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 2.42/0.72    inference(superposition,[],[f81,f185])).
% 2.42/0.72  fof(f81,plain,(
% 2.42/0.72    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.42/0.72    inference(cnf_transformation,[],[f7])).
% 2.42/0.72  fof(f7,axiom,(
% 2.42/0.72    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.42/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.42/0.72  fof(f111,plain,(
% 2.42/0.72    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 2.42/0.72    inference(equality_resolution,[],[f106])).
% 2.42/0.72  fof(f106,plain,(
% 2.42/0.72    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2) )),
% 2.42/0.72    inference(definition_unfolding,[],[f84,f69])).
% 2.42/0.72  fof(f84,plain,(
% 2.42/0.72    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 2.42/0.72    inference(cnf_transformation,[],[f56])).
% 2.42/0.72  fof(f56,plain,(
% 2.42/0.72    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.42/0.72    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f54,f55])).
% 2.42/0.72  fof(f55,plain,(
% 2.42/0.72    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 2.42/0.72    introduced(choice_axiom,[])).
% 2.42/0.72  fof(f54,plain,(
% 2.42/0.72    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.42/0.72    inference(rectify,[],[f53])).
% 2.42/0.72  fof(f53,plain,(
% 2.42/0.72    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.42/0.72    inference(flattening,[],[f52])).
% 2.42/0.72  fof(f52,plain,(
% 2.42/0.72    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.42/0.72    inference(nnf_transformation,[],[f1])).
% 2.42/0.72  fof(f1,axiom,(
% 2.42/0.72    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.42/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 2.42/0.72  fof(f1968,plain,(
% 2.42/0.72    ( ! [X0] : (r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X0,k2_tops_1(sK0,sK1)) | ~r2_hidden(X0,sK1)) ) | ~spl4_2),
% 2.42/0.72    inference(backward_demodulation,[],[f187,f1963])).
% 2.42/0.72  fof(f1963,plain,(
% 2.42/0.72    k1_xboole_0 = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~spl4_2),
% 2.42/0.72    inference(forward_demodulation,[],[f1945,f185])).
% 2.42/0.72  fof(f1945,plain,(
% 2.42/0.72    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_tops_1(sK0,sK1))) | ~spl4_2),
% 2.42/0.72    inference(superposition,[],[f1920,f235])).
% 2.42/0.72  fof(f235,plain,(
% 2.42/0.72    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~spl4_2),
% 2.42/0.72    inference(superposition,[],[f180,f141])).
% 2.42/0.72  fof(f180,plain,(
% 2.42/0.72    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0) = k4_xboole_0(k2_pre_topc(sK0,sK1),X0)) )),
% 2.42/0.72    inference(resolution,[],[f173,f70])).
% 2.42/0.72  fof(f70,plain,(
% 2.42/0.72    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)) )),
% 2.42/0.72    inference(cnf_transformation,[],[f29])).
% 2.42/0.72  fof(f29,plain,(
% 2.42/0.72    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.42/0.72    inference(ennf_transformation,[],[f15])).
% 2.42/0.72  fof(f15,axiom,(
% 2.42/0.72    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 2.42/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 2.42/0.72  fof(f173,plain,(
% 2.42/0.72    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.42/0.72    inference(subsumption_resolution,[],[f172,f66])).
% 2.42/0.72  fof(f172,plain,(
% 2.42/0.72    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.42/0.72    inference(subsumption_resolution,[],[f171,f158])).
% 2.42/0.72  fof(f158,plain,(
% 2.42/0.72    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.42/0.72    inference(subsumption_resolution,[],[f157,f65])).
% 2.42/0.72  fof(f157,plain,(
% 2.42/0.72    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 2.42/0.72    inference(subsumption_resolution,[],[f156,f133])).
% 2.42/0.72  fof(f133,plain,(
% 2.42/0.72    m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.42/0.72    inference(subsumption_resolution,[],[f132,f66])).
% 2.42/0.72  fof(f132,plain,(
% 2.42/0.72    m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.42/0.72    inference(superposition,[],[f92,f124])).
% 2.42/0.72  fof(f124,plain,(
% 2.42/0.72    k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1)),
% 2.42/0.72    inference(resolution,[],[f66,f80])).
% 2.42/0.72  fof(f80,plain,(
% 2.42/0.72    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 2.42/0.72    inference(cnf_transformation,[],[f40])).
% 2.42/0.72  fof(f40,plain,(
% 2.42/0.72    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.42/0.72    inference(ennf_transformation,[],[f11])).
% 2.42/0.72  fof(f11,axiom,(
% 2.42/0.72    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.42/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 2.42/0.72  fof(f92,plain,(
% 2.42/0.72    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.42/0.72    inference(cnf_transformation,[],[f45])).
% 2.42/0.72  fof(f45,plain,(
% 2.42/0.72    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.42/0.72    inference(ennf_transformation,[],[f12])).
% 2.42/0.72  fof(f12,axiom,(
% 2.42/0.72    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.42/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 2.42/0.72  fof(f156,plain,(
% 2.42/0.72    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 2.42/0.72    inference(superposition,[],[f74,f155])).
% 2.42/0.72  fof(f155,plain,(
% 2.42/0.72    k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))),
% 2.42/0.72    inference(forward_demodulation,[],[f126,f124])).
% 2.42/0.72  fof(f126,plain,(
% 2.42/0.72    k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),
% 2.42/0.72    inference(subsumption_resolution,[],[f119,f65])).
% 2.42/0.72  fof(f119,plain,(
% 2.42/0.72    k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | ~l1_pre_topc(sK0)),
% 2.42/0.72    inference(resolution,[],[f66,f75])).
% 2.42/0.72  fof(f75,plain,(
% 2.42/0.72    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) | ~l1_pre_topc(X0)) )),
% 2.42/0.72    inference(cnf_transformation,[],[f35])).
% 2.42/0.72  fof(f35,plain,(
% 2.42/0.72    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.42/0.72    inference(ennf_transformation,[],[f22])).
% 2.42/0.72  fof(f22,axiom,(
% 2.42/0.72    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))))),
% 2.42/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_1)).
% 2.42/0.72  fof(f74,plain,(
% 2.42/0.72    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.42/0.72    inference(cnf_transformation,[],[f34])).
% 2.42/0.72  fof(f34,plain,(
% 2.42/0.72    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.42/0.72    inference(flattening,[],[f33])).
% 2.42/0.72  fof(f33,plain,(
% 2.42/0.72    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.42/0.72    inference(ennf_transformation,[],[f18])).
% 2.42/0.72  fof(f18,axiom,(
% 2.42/0.72    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.42/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 2.42/0.72  fof(f171,plain,(
% 2.42/0.72    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.42/0.72    inference(superposition,[],[f90,f127])).
% 2.42/0.72  fof(f127,plain,(
% 2.42/0.72    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 2.42/0.72    inference(subsumption_resolution,[],[f120,f65])).
% 2.42/0.72  fof(f120,plain,(
% 2.42/0.72    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 2.42/0.72    inference(resolution,[],[f66,f73])).
% 2.42/0.72  fof(f73,plain,(
% 2.42/0.72    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~l1_pre_topc(X0)) )),
% 2.42/0.72    inference(cnf_transformation,[],[f32])).
% 2.42/0.72  fof(f32,plain,(
% 2.42/0.72    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.42/0.72    inference(ennf_transformation,[],[f23])).
% 2.42/0.72  fof(f23,axiom,(
% 2.42/0.72    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 2.42/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).
% 2.42/0.72  fof(f90,plain,(
% 2.42/0.72    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.42/0.72    inference(cnf_transformation,[],[f43])).
% 2.42/0.72  fof(f43,plain,(
% 2.42/0.72    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.42/0.72    inference(flattening,[],[f42])).
% 2.42/0.73  fof(f42,plain,(
% 2.42/0.73    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 2.42/0.73    inference(ennf_transformation,[],[f13])).
% 2.42/0.73  fof(f13,axiom,(
% 2.42/0.73    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 2.42/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).
% 2.42/0.73  fof(f1920,plain,(
% 2.42/0.73    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 2.42/0.73    inference(duplicate_literal_removal,[],[f1884])).
% 2.42/0.73  fof(f1884,plain,(
% 2.42/0.73    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 2.42/0.73    inference(resolution,[],[f1101,f277])).
% 2.42/0.73  fof(f277,plain,(
% 2.42/0.73    ( ! [X2,X3] : (r2_hidden(sK2(X2,X3,k1_xboole_0),X3) | k1_xboole_0 = k4_xboole_0(X2,k4_xboole_0(X2,X3))) )),
% 2.42/0.73    inference(resolution,[],[f273,f104])).
% 2.42/0.73  fof(f104,plain,(
% 2.42/0.73    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X2) | r2_hidden(sK2(X0,X1,X2),X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2) )),
% 2.42/0.73    inference(definition_unfolding,[],[f86,f69])).
% 2.42/0.73  fof(f86,plain,(
% 2.42/0.73    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 2.42/0.73    inference(cnf_transformation,[],[f56])).
% 2.42/0.73  fof(f1101,plain,(
% 2.42/0.73    ( ! [X6,X7,X5] : (~r2_hidden(sK2(X5,X6,k1_xboole_0),k4_xboole_0(X7,X5)) | k1_xboole_0 = k4_xboole_0(X5,k4_xboole_0(X5,X6))) )),
% 2.42/0.73    inference(resolution,[],[f276,f117])).
% 2.42/0.73  fof(f276,plain,(
% 2.42/0.73    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1,k1_xboole_0),X0) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.42/0.73    inference(resolution,[],[f273,f105])).
% 2.42/0.73  fof(f105,plain,(
% 2.42/0.73    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X2) | r2_hidden(sK2(X0,X1,X2),X0) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2) )),
% 2.42/0.73    inference(definition_unfolding,[],[f85,f69])).
% 2.42/0.73  fof(f85,plain,(
% 2.42/0.73    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 2.42/0.73    inference(cnf_transformation,[],[f56])).
% 2.42/0.73  fof(f187,plain,(
% 2.42/0.73    ( ! [X0] : (r2_hidden(X0,k4_xboole_0(sK1,k1_tops_1(sK0,sK1))) | ~r2_hidden(X0,k2_tops_1(sK0,sK1)) | ~r2_hidden(X0,sK1)) )),
% 2.42/0.73    inference(superposition,[],[f111,f185])).
% 2.42/0.73  fof(f2017,plain,(
% 2.42/0.73    ( ! [X17,X16] : (r2_hidden(sK3(X16,X17,sK1),X16) | ~r2_hidden(sK3(X16,X17,sK1),k2_tops_1(sK0,sK1)) | sK1 = k4_xboole_0(X16,X17)) ) | ~spl4_2),
% 2.42/0.73    inference(resolution,[],[f1985,f99])).
% 2.42/0.73  fof(f185,plain,(
% 2.42/0.73    k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 2.42/0.73    inference(superposition,[],[f128,f125])).
% 2.42/0.73  fof(f125,plain,(
% 2.42/0.73    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)) )),
% 2.42/0.73    inference(resolution,[],[f66,f70])).
% 2.42/0.73  fof(f128,plain,(
% 2.42/0.73    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 2.42/0.73    inference(subsumption_resolution,[],[f121,f65])).
% 2.42/0.73  fof(f121,plain,(
% 2.42/0.73    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 2.42/0.73    inference(resolution,[],[f66,f72])).
% 2.42/0.73  fof(f72,plain,(
% 2.42/0.73    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~l1_pre_topc(X0)) )),
% 2.42/0.73    inference(cnf_transformation,[],[f31])).
% 2.42/0.73  fof(f31,plain,(
% 2.42/0.73    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.42/0.73    inference(ennf_transformation,[],[f24])).
% 2.42/0.73  fof(f24,axiom,(
% 2.42/0.73    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 2.42/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).
% 2.42/0.73  fof(f76,plain,(
% 2.42/0.73    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.42/0.73    inference(cnf_transformation,[],[f37])).
% 2.42/0.73  fof(f37,plain,(
% 2.42/0.73    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.42/0.73    inference(flattening,[],[f36])).
% 2.42/0.73  fof(f36,plain,(
% 2.42/0.73    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.42/0.73    inference(ennf_transformation,[],[f19])).
% 2.42/0.73  fof(f19,axiom,(
% 2.42/0.73    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 2.42/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).
% 2.42/0.73  fof(f2206,plain,(
% 2.42/0.73    ~spl4_1 | spl4_4),
% 2.42/0.73    inference(avatar_contradiction_clause,[],[f2205])).
% 2.42/0.73  fof(f2205,plain,(
% 2.42/0.73    $false | (~spl4_1 | spl4_4)),
% 2.42/0.73    inference(subsumption_resolution,[],[f2203,f137])).
% 2.42/0.73  fof(f137,plain,(
% 2.42/0.73    v3_pre_topc(sK1,sK0) | ~spl4_1),
% 2.42/0.73    inference(avatar_component_clause,[],[f135])).
% 2.42/0.73  fof(f135,plain,(
% 2.42/0.73    spl4_1 <=> v3_pre_topc(sK1,sK0)),
% 2.42/0.73    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 2.42/0.73  fof(f2203,plain,(
% 2.42/0.73    ~v3_pre_topc(sK1,sK0) | spl4_4),
% 2.42/0.73    inference(subsumption_resolution,[],[f2202,f65])).
% 2.42/0.73  fof(f2202,plain,(
% 2.42/0.73    ~v3_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | spl4_4),
% 2.42/0.73    inference(subsumption_resolution,[],[f2201,f66])).
% 2.42/0.73  fof(f2201,plain,(
% 2.42/0.73    ~v3_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl4_4),
% 2.42/0.73    inference(subsumption_resolution,[],[f203,f115])).
% 2.42/0.73  fof(f115,plain,(
% 2.42/0.73    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.42/0.73    inference(equality_resolution,[],[f93])).
% 2.42/0.73  fof(f93,plain,(
% 2.42/0.73    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.42/0.73    inference(cnf_transformation,[],[f58])).
% 2.42/0.73  fof(f58,plain,(
% 2.42/0.73    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.42/0.73    inference(flattening,[],[f57])).
% 2.42/0.73  fof(f57,plain,(
% 2.42/0.73    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.42/0.73    inference(nnf_transformation,[],[f3])).
% 2.42/0.73  fof(f3,axiom,(
% 2.42/0.73    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.42/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.42/0.73  fof(f203,plain,(
% 2.42/0.73    ~r1_tarski(sK1,sK1) | ~v3_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl4_4),
% 2.42/0.73    inference(duplicate_literal_removal,[],[f201])).
% 2.42/0.73  fof(f201,plain,(
% 2.42/0.73    ~r1_tarski(sK1,sK1) | ~v3_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl4_4),
% 2.42/0.73    inference(resolution,[],[f199,f77])).
% 2.42/0.73  fof(f77,plain,(
% 2.42/0.73    ( ! [X2,X0,X1] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.42/0.73    inference(cnf_transformation,[],[f39])).
% 2.42/0.73  fof(f39,plain,(
% 2.42/0.73    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.42/0.73    inference(flattening,[],[f38])).
% 2.42/0.73  fof(f38,plain,(
% 2.42/0.73    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.42/0.73    inference(ennf_transformation,[],[f21])).
% 2.42/0.73  fof(f21,axiom,(
% 2.42/0.73    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 2.42/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).
% 2.42/0.73  fof(f199,plain,(
% 2.42/0.73    ~r1_tarski(sK1,k1_tops_1(sK0,sK1)) | spl4_4),
% 2.42/0.73    inference(avatar_component_clause,[],[f197])).
% 2.42/0.73  fof(f197,plain,(
% 2.42/0.73    spl4_4 <=> r1_tarski(sK1,k1_tops_1(sK0,sK1))),
% 2.42/0.73    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 2.42/0.73  fof(f200,plain,(
% 2.42/0.73    spl4_3 | ~spl4_4),
% 2.42/0.73    inference(avatar_split_clause,[],[f189,f197,f193])).
% 2.42/0.73  fof(f189,plain,(
% 2.42/0.73    ~r1_tarski(sK1,k1_tops_1(sK0,sK1)) | sK1 = k1_tops_1(sK0,sK1)),
% 2.42/0.73    inference(resolution,[],[f188,f95])).
% 2.42/0.73  fof(f95,plain,(
% 2.42/0.73    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 2.42/0.73    inference(cnf_transformation,[],[f58])).
% 2.42/0.73  fof(f142,plain,(
% 2.42/0.73    spl4_1 | spl4_2),
% 2.42/0.73    inference(avatar_split_clause,[],[f67,f139,f135])).
% 2.42/0.73  fof(f67,plain,(
% 2.42/0.73    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)),
% 2.42/0.73    inference(cnf_transformation,[],[f50])).
% 2.42/0.73  % SZS output end Proof for theBenchmark
% 2.42/0.73  % (14032)------------------------------
% 2.42/0.73  % (14032)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.42/0.73  % (14032)Termination reason: Refutation
% 2.42/0.73  
% 2.42/0.73  % (14032)Memory used [KB]: 12537
% 2.42/0.73  % (14032)Time elapsed: 0.318 s
% 2.42/0.73  % (14032)------------------------------
% 2.42/0.73  % (14032)------------------------------
% 2.42/0.73  % (14007)Success in time 0.369 s
%------------------------------------------------------------------------------
