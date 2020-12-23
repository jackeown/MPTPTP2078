%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:42 EST 2020

% Result     : Theorem 2.93s
% Output     : Refutation 2.93s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 294 expanded)
%              Number of leaves         :   22 (  84 expanded)
%              Depth                    :   16
%              Number of atoms          :  295 (1424 expanded)
%              Number of equality atoms :   81 ( 397 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3282,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f74,f75,f3189,f3205,f3209,f3281])).

fof(f3281,plain,
    ( spl2_2
    | ~ spl2_4 ),
    inference(avatar_contradiction_clause,[],[f3280])).

fof(f3280,plain,
    ( $false
    | spl2_2
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f3279,f73])).

fof(f73,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl2_2
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f3279,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ spl2_4 ),
    inference(forward_demodulation,[],[f295,f234])).

fof(f234,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f232])).

fof(f232,plain,
    ( spl2_4
  <=> sK1 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f295,plain,(
    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f292,f40])).

fof(f40,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | ~ v3_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | v3_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f34,f33])).

fof(f33,plain,
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

fof(f34,plain,
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

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).

fof(f292,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f47,f41])).

fof(f41,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f35])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

fof(f3209,plain,
    ( ~ spl2_3
    | spl2_4 ),
    inference(avatar_split_clause,[],[f3206,f232,f228])).

fof(f228,plain,
    ( spl2_3
  <=> r1_tarski(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f3206,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ r1_tarski(sK1,k1_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f223,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f223,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f222,f40])).

fof(f222,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f45,f41])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(f3205,plain,
    ( spl2_3
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f3204,f67,f228])).

fof(f67,plain,
    ( spl2_1
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f3204,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | r1_tarski(sK1,k1_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f632,f64])).

fof(f64,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f632,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ r1_tarski(sK1,sK1) ),
    inference(resolution,[],[f303,f41])).

fof(f303,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X0,sK0)
      | r1_tarski(X0,k1_tops_1(sK0,sK1))
      | ~ r1_tarski(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f300,f40])).

fof(f300,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | ~ v3_pre_topc(X0,sK0)
      | r1_tarski(X0,k1_tops_1(sK0,sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f48,f41])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,X2)
      | ~ v3_pre_topc(X1,X0)
      | r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X1,X2)
                  & v3_pre_topc(X1,X0) )
               => r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).

fof(f3189,plain,
    ( spl2_1
    | ~ spl2_2 ),
    inference(avatar_contradiction_clause,[],[f3188])).

fof(f3188,plain,
    ( $false
    | spl2_1
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f3154,f69])).

fof(f69,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f67])).

fof(f3154,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl2_2 ),
    inference(backward_demodulation,[],[f249,f3120])).

fof(f3120,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl2_2 ),
    inference(backward_demodulation,[],[f278,f3079])).

fof(f3079,plain,
    ( sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_2 ),
    inference(superposition,[],[f2404,f3054])).

fof(f3054,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl2_2 ),
    inference(superposition,[],[f2806,f72])).

fof(f72,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f71])).

fof(f2806,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0) = k4_xboole_0(k2_pre_topc(sK0,sK1),X0) ),
    inference(subsumption_resolution,[],[f2803,f40])).

fof(f2803,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0) = k4_xboole_0(k2_pre_topc(sK0,sK1),X0) ) ),
    inference(resolution,[],[f254,f41])).

fof(f254,plain,(
    ! [X6,X4,X5] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X5)))
      | ~ l1_pre_topc(X5)
      | k7_subset_1(u1_struct_0(X5),k2_pre_topc(X5,X4),X6) = k4_xboole_0(k2_pre_topc(X5,X4),X6) ) ),
    inference(resolution,[],[f54,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f2404,plain,(
    ! [X10,X9] : k4_xboole_0(X9,k4_xboole_0(X10,X9)) = X9 ),
    inference(forward_demodulation,[],[f2337,f44])).

fof(f44,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f2337,plain,(
    ! [X10,X9] : k4_xboole_0(X9,k1_xboole_0) = k4_xboole_0(X9,k4_xboole_0(X10,X9)) ),
    inference(superposition,[],[f63,f1424])).

fof(f1424,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(forward_demodulation,[],[f1315,f79])).

fof(f79,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(resolution,[],[f59,f64])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f1315,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) = k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X1,X0)) ),
    inference(superposition,[],[f108,f76])).

fof(f76,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(resolution,[],[f52,f64])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f108,plain,(
    ! [X10,X8,X9] : k4_xboole_0(X10,k4_xboole_0(X10,k4_xboole_0(X8,X9))) = k4_xboole_0(k4_xboole_0(X8,X9),k4_xboole_0(X8,k2_xboole_0(X9,X10))) ),
    inference(superposition,[],[f62,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f62,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f49,f50,f50])).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f49,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f63,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f51,f50])).

fof(f51,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f278,plain,(
    k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(superposition,[],[f276,f236])).

fof(f236,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
    inference(resolution,[],[f61,f41])).

fof(f276,plain,(
    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f273,f40])).

fof(f273,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f46,f41])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

fof(f249,plain,(
    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f248,f39])).

fof(f39,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f248,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f247,f40])).

fof(f247,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f53,f41])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f75,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f42,f71,f67])).

fof(f42,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f74,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f43,f71,f67])).

fof(f43,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:08:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (2042)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.51  % (2034)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.51  % (2026)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.52  % (2031)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.53  % (2022)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.53  % (2025)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.29/0.53  % (2021)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.29/0.54  % (2044)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.29/0.54  % (2048)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.29/0.54  % (2048)Refutation not found, incomplete strategy% (2048)------------------------------
% 1.29/0.54  % (2048)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.54  % (2048)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.54  
% 1.29/0.54  % (2048)Memory used [KB]: 1663
% 1.29/0.54  % (2048)Time elapsed: 0.001 s
% 1.29/0.54  % (2048)------------------------------
% 1.29/0.54  % (2048)------------------------------
% 1.29/0.54  % (2019)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.29/0.54  % (2023)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.29/0.54  % (2038)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.29/0.54  % (2037)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.29/0.54  % (2024)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.29/0.54  % (2046)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.29/0.54  % (2045)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.29/0.54  % (2046)Refutation not found, incomplete strategy% (2046)------------------------------
% 1.29/0.54  % (2046)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.54  % (2046)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.54  
% 1.29/0.54  % (2046)Memory used [KB]: 6268
% 1.29/0.54  % (2046)Time elapsed: 0.128 s
% 1.29/0.54  % (2046)------------------------------
% 1.29/0.54  % (2046)------------------------------
% 1.29/0.55  % (2047)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.29/0.55  % (2030)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.29/0.55  % (2036)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.29/0.55  % (2040)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.29/0.55  % (2029)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.29/0.55  % (2020)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.29/0.55  % (2027)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.29/0.55  % (2039)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.52/0.56  % (2032)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.52/0.56  % (2033)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.52/0.56  % (2043)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.52/0.56  % (2035)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.52/0.56  % (2041)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.52/0.56  % (2035)Refutation not found, incomplete strategy% (2035)------------------------------
% 1.52/0.56  % (2035)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.56  % (2035)Termination reason: Refutation not found, incomplete strategy
% 1.52/0.56  
% 1.52/0.56  % (2035)Memory used [KB]: 10618
% 1.52/0.56  % (2035)Time elapsed: 0.146 s
% 1.52/0.56  % (2035)------------------------------
% 1.52/0.56  % (2035)------------------------------
% 1.52/0.57  % (2028)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 2.42/0.70  % (2052)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.42/0.72  % (2053)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.93/0.77  % (2054)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.93/0.79  % (2025)Refutation found. Thanks to Tanya!
% 2.93/0.79  % SZS status Theorem for theBenchmark
% 2.93/0.79  % SZS output start Proof for theBenchmark
% 2.93/0.79  fof(f3282,plain,(
% 2.93/0.79    $false),
% 2.93/0.79    inference(avatar_sat_refutation,[],[f74,f75,f3189,f3205,f3209,f3281])).
% 2.93/0.79  fof(f3281,plain,(
% 2.93/0.79    spl2_2 | ~spl2_4),
% 2.93/0.79    inference(avatar_contradiction_clause,[],[f3280])).
% 2.93/0.79  fof(f3280,plain,(
% 2.93/0.79    $false | (spl2_2 | ~spl2_4)),
% 2.93/0.79    inference(subsumption_resolution,[],[f3279,f73])).
% 2.93/0.79  fof(f73,plain,(
% 2.93/0.79    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | spl2_2),
% 2.93/0.79    inference(avatar_component_clause,[],[f71])).
% 2.93/0.79  fof(f71,plain,(
% 2.93/0.79    spl2_2 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)),
% 2.93/0.79    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 2.93/0.79  fof(f3279,plain,(
% 2.93/0.79    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~spl2_4),
% 2.93/0.79    inference(forward_demodulation,[],[f295,f234])).
% 2.93/0.79  fof(f234,plain,(
% 2.93/0.79    sK1 = k1_tops_1(sK0,sK1) | ~spl2_4),
% 2.93/0.79    inference(avatar_component_clause,[],[f232])).
% 2.93/0.79  fof(f232,plain,(
% 2.93/0.79    spl2_4 <=> sK1 = k1_tops_1(sK0,sK1)),
% 2.93/0.79    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 2.93/0.79  fof(f295,plain,(
% 2.93/0.79    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 2.93/0.79    inference(subsumption_resolution,[],[f292,f40])).
% 2.93/0.79  fof(f40,plain,(
% 2.93/0.79    l1_pre_topc(sK0)),
% 2.93/0.79    inference(cnf_transformation,[],[f35])).
% 2.93/0.79  fof(f35,plain,(
% 2.93/0.79    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 2.93/0.79    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f34,f33])).
% 2.93/0.79  fof(f33,plain,(
% 2.93/0.79    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 2.93/0.79    introduced(choice_axiom,[])).
% 2.93/0.79  fof(f34,plain,(
% 2.93/0.79    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.93/0.79    introduced(choice_axiom,[])).
% 2.93/0.79  fof(f32,plain,(
% 2.93/0.79    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.93/0.79    inference(flattening,[],[f31])).
% 2.93/0.79  fof(f31,plain,(
% 2.93/0.79    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.93/0.79    inference(nnf_transformation,[],[f19])).
% 2.93/0.79  fof(f19,plain,(
% 2.93/0.79    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.93/0.79    inference(flattening,[],[f18])).
% 2.93/0.79  fof(f18,plain,(
% 2.93/0.79    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.93/0.79    inference(ennf_transformation,[],[f17])).
% 2.93/0.79  fof(f17,negated_conjecture,(
% 2.93/0.79    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 2.93/0.79    inference(negated_conjecture,[],[f16])).
% 2.93/0.79  fof(f16,conjecture,(
% 2.93/0.79    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 2.93/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).
% 2.93/0.79  fof(f292,plain,(
% 2.93/0.79    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 2.93/0.79    inference(resolution,[],[f47,f41])).
% 2.93/0.79  fof(f41,plain,(
% 2.93/0.79    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.93/0.79    inference(cnf_transformation,[],[f35])).
% 2.93/0.79  fof(f47,plain,(
% 2.93/0.79    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~l1_pre_topc(X0)) )),
% 2.93/0.79    inference(cnf_transformation,[],[f22])).
% 2.93/0.79  fof(f22,plain,(
% 2.93/0.79    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.93/0.79    inference(ennf_transformation,[],[f12])).
% 2.93/0.79  fof(f12,axiom,(
% 2.93/0.79    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 2.93/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).
% 2.93/0.79  fof(f3209,plain,(
% 2.93/0.79    ~spl2_3 | spl2_4),
% 2.93/0.79    inference(avatar_split_clause,[],[f3206,f232,f228])).
% 2.93/0.79  fof(f228,plain,(
% 2.93/0.79    spl2_3 <=> r1_tarski(sK1,k1_tops_1(sK0,sK1))),
% 2.93/0.79    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 2.93/0.79  fof(f3206,plain,(
% 2.93/0.79    sK1 = k1_tops_1(sK0,sK1) | ~r1_tarski(sK1,k1_tops_1(sK0,sK1))),
% 2.93/0.79    inference(resolution,[],[f223,f57])).
% 2.93/0.79  fof(f57,plain,(
% 2.93/0.79    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.93/0.79    inference(cnf_transformation,[],[f37])).
% 2.93/0.79  fof(f37,plain,(
% 2.93/0.79    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.93/0.79    inference(flattening,[],[f36])).
% 2.93/0.79  fof(f36,plain,(
% 2.93/0.79    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.93/0.79    inference(nnf_transformation,[],[f2])).
% 2.93/0.79  fof(f2,axiom,(
% 2.93/0.79    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.93/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.93/0.79  fof(f223,plain,(
% 2.93/0.79    r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 2.93/0.79    inference(subsumption_resolution,[],[f222,f40])).
% 2.93/0.79  fof(f222,plain,(
% 2.93/0.79    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~l1_pre_topc(sK0)),
% 2.93/0.79    inference(resolution,[],[f45,f41])).
% 2.93/0.79  fof(f45,plain,(
% 2.93/0.79    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),X1) | ~l1_pre_topc(X0)) )),
% 2.93/0.79    inference(cnf_transformation,[],[f20])).
% 2.93/0.79  fof(f20,plain,(
% 2.93/0.79    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.93/0.79    inference(ennf_transformation,[],[f13])).
% 2.93/0.79  fof(f13,axiom,(
% 2.93/0.79    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 2.93/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).
% 2.93/0.79  fof(f3205,plain,(
% 2.93/0.79    spl2_3 | ~spl2_1),
% 2.93/0.79    inference(avatar_split_clause,[],[f3204,f67,f228])).
% 2.93/0.79  fof(f67,plain,(
% 2.93/0.79    spl2_1 <=> v3_pre_topc(sK1,sK0)),
% 2.93/0.79    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 2.93/0.79  fof(f3204,plain,(
% 2.93/0.79    ~v3_pre_topc(sK1,sK0) | r1_tarski(sK1,k1_tops_1(sK0,sK1))),
% 2.93/0.79    inference(subsumption_resolution,[],[f632,f64])).
% 2.93/0.79  fof(f64,plain,(
% 2.93/0.79    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.93/0.79    inference(equality_resolution,[],[f56])).
% 2.93/0.79  fof(f56,plain,(
% 2.93/0.79    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.93/0.79    inference(cnf_transformation,[],[f37])).
% 2.93/0.79  fof(f632,plain,(
% 2.93/0.79    ~v3_pre_topc(sK1,sK0) | r1_tarski(sK1,k1_tops_1(sK0,sK1)) | ~r1_tarski(sK1,sK1)),
% 2.93/0.79    inference(resolution,[],[f303,f41])).
% 2.93/0.79  fof(f303,plain,(
% 2.93/0.79    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | r1_tarski(X0,k1_tops_1(sK0,sK1)) | ~r1_tarski(X0,sK1)) )),
% 2.93/0.79    inference(subsumption_resolution,[],[f300,f40])).
% 2.93/0.79  fof(f300,plain,(
% 2.93/0.79    ( ! [X0] : (~r1_tarski(X0,sK1) | ~v3_pre_topc(X0,sK0) | r1_tarski(X0,k1_tops_1(sK0,sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 2.93/0.79    inference(resolution,[],[f48,f41])).
% 2.93/0.79  fof(f48,plain,(
% 2.93/0.79    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | r1_tarski(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.93/0.79    inference(cnf_transformation,[],[f24])).
% 2.93/0.79  fof(f24,plain,(
% 2.93/0.79    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.93/0.79    inference(flattening,[],[f23])).
% 2.93/0.79  fof(f23,plain,(
% 2.93/0.79    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.93/0.79    inference(ennf_transformation,[],[f14])).
% 2.93/0.79  fof(f14,axiom,(
% 2.93/0.79    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 2.93/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).
% 2.93/0.79  fof(f3189,plain,(
% 2.93/0.79    spl2_1 | ~spl2_2),
% 2.93/0.79    inference(avatar_contradiction_clause,[],[f3188])).
% 2.93/0.79  fof(f3188,plain,(
% 2.93/0.79    $false | (spl2_1 | ~spl2_2)),
% 2.93/0.79    inference(subsumption_resolution,[],[f3154,f69])).
% 2.93/0.79  fof(f69,plain,(
% 2.93/0.79    ~v3_pre_topc(sK1,sK0) | spl2_1),
% 2.93/0.79    inference(avatar_component_clause,[],[f67])).
% 2.93/0.79  fof(f3154,plain,(
% 2.93/0.79    v3_pre_topc(sK1,sK0) | ~spl2_2),
% 2.93/0.79    inference(backward_demodulation,[],[f249,f3120])).
% 2.93/0.79  fof(f3120,plain,(
% 2.93/0.79    sK1 = k1_tops_1(sK0,sK1) | ~spl2_2),
% 2.93/0.79    inference(backward_demodulation,[],[f278,f3079])).
% 2.93/0.79  fof(f3079,plain,(
% 2.93/0.79    sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl2_2),
% 2.93/0.79    inference(superposition,[],[f2404,f3054])).
% 2.93/0.79  fof(f3054,plain,(
% 2.93/0.79    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~spl2_2),
% 2.93/0.79    inference(superposition,[],[f2806,f72])).
% 2.93/0.79  fof(f72,plain,(
% 2.93/0.79    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~spl2_2),
% 2.93/0.79    inference(avatar_component_clause,[],[f71])).
% 2.93/0.79  fof(f2806,plain,(
% 2.93/0.79    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0) = k4_xboole_0(k2_pre_topc(sK0,sK1),X0)) )),
% 2.93/0.79    inference(subsumption_resolution,[],[f2803,f40])).
% 2.93/0.79  fof(f2803,plain,(
% 2.93/0.79    ( ! [X0] : (~l1_pre_topc(sK0) | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0) = k4_xboole_0(k2_pre_topc(sK0,sK1),X0)) )),
% 2.93/0.79    inference(resolution,[],[f254,f41])).
% 2.93/0.79  fof(f254,plain,(
% 2.93/0.79    ( ! [X6,X4,X5] : (~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X5))) | ~l1_pre_topc(X5) | k7_subset_1(u1_struct_0(X5),k2_pre_topc(X5,X4),X6) = k4_xboole_0(k2_pre_topc(X5,X4),X6)) )),
% 2.93/0.79    inference(resolution,[],[f54,f61])).
% 2.93/0.79  fof(f61,plain,(
% 2.93/0.79    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)) )),
% 2.93/0.79    inference(cnf_transformation,[],[f30])).
% 2.93/0.79  fof(f30,plain,(
% 2.93/0.79    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.93/0.79    inference(ennf_transformation,[],[f9])).
% 2.93/0.79  fof(f9,axiom,(
% 2.93/0.79    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 2.93/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 2.93/0.79  fof(f54,plain,(
% 2.93/0.79    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.93/0.79    inference(cnf_transformation,[],[f29])).
% 2.93/0.79  fof(f29,plain,(
% 2.93/0.79    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.93/0.79    inference(flattening,[],[f28])).
% 2.93/0.79  fof(f28,plain,(
% 2.93/0.79    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.93/0.79    inference(ennf_transformation,[],[f10])).
% 2.93/0.79  fof(f10,axiom,(
% 2.93/0.79    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.93/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 2.93/0.79  fof(f2404,plain,(
% 2.93/0.79    ( ! [X10,X9] : (k4_xboole_0(X9,k4_xboole_0(X10,X9)) = X9) )),
% 2.93/0.79    inference(forward_demodulation,[],[f2337,f44])).
% 2.93/0.79  fof(f44,plain,(
% 2.93/0.79    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.93/0.79    inference(cnf_transformation,[],[f5])).
% 2.93/0.79  fof(f5,axiom,(
% 2.93/0.79    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.93/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 2.93/0.79  fof(f2337,plain,(
% 2.93/0.79    ( ! [X10,X9] : (k4_xboole_0(X9,k1_xboole_0) = k4_xboole_0(X9,k4_xboole_0(X10,X9))) )),
% 2.93/0.79    inference(superposition,[],[f63,f1424])).
% 2.93/0.79  fof(f1424,plain,(
% 2.93/0.79    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 2.93/0.79    inference(forward_demodulation,[],[f1315,f79])).
% 2.93/0.79  fof(f79,plain,(
% 2.93/0.79    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 2.93/0.79    inference(resolution,[],[f59,f64])).
% 2.93/0.79  fof(f59,plain,(
% 2.93/0.79    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 2.93/0.79    inference(cnf_transformation,[],[f38])).
% 2.93/0.79  fof(f38,plain,(
% 2.93/0.79    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 2.93/0.79    inference(nnf_transformation,[],[f3])).
% 2.93/0.79  fof(f3,axiom,(
% 2.93/0.79    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 2.93/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 2.93/0.79  fof(f1315,plain,(
% 2.93/0.79    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) = k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X1,X0))) )),
% 2.93/0.79    inference(superposition,[],[f108,f76])).
% 2.93/0.79  fof(f76,plain,(
% 2.93/0.79    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 2.93/0.79    inference(resolution,[],[f52,f64])).
% 2.93/0.79  fof(f52,plain,(
% 2.93/0.79    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 2.93/0.79    inference(cnf_transformation,[],[f25])).
% 2.93/0.79  fof(f25,plain,(
% 2.93/0.79    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.93/0.79    inference(ennf_transformation,[],[f4])).
% 2.93/0.79  fof(f4,axiom,(
% 2.93/0.79    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.93/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 2.93/0.79  fof(f108,plain,(
% 2.93/0.79    ( ! [X10,X8,X9] : (k4_xboole_0(X10,k4_xboole_0(X10,k4_xboole_0(X8,X9))) = k4_xboole_0(k4_xboole_0(X8,X9),k4_xboole_0(X8,k2_xboole_0(X9,X10)))) )),
% 2.93/0.79    inference(superposition,[],[f62,f60])).
% 2.93/0.79  fof(f60,plain,(
% 2.93/0.79    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 2.93/0.79    inference(cnf_transformation,[],[f6])).
% 2.93/0.79  fof(f6,axiom,(
% 2.93/0.79    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 2.93/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 2.93/0.79  fof(f62,plain,(
% 2.93/0.79    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 2.93/0.79    inference(definition_unfolding,[],[f49,f50,f50])).
% 2.93/0.79  fof(f50,plain,(
% 2.93/0.79    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.93/0.79    inference(cnf_transformation,[],[f8])).
% 2.93/0.79  fof(f8,axiom,(
% 2.93/0.79    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.93/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.93/0.79  fof(f49,plain,(
% 2.93/0.79    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.93/0.79    inference(cnf_transformation,[],[f1])).
% 2.93/0.79  fof(f1,axiom,(
% 2.93/0.79    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.93/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.93/0.79  fof(f63,plain,(
% 2.93/0.79    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 2.93/0.79    inference(definition_unfolding,[],[f51,f50])).
% 2.93/0.79  fof(f51,plain,(
% 2.93/0.79    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.93/0.79    inference(cnf_transformation,[],[f7])).
% 2.93/0.79  fof(f7,axiom,(
% 2.93/0.79    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.93/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 2.93/0.79  fof(f278,plain,(
% 2.93/0.79    k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 2.93/0.79    inference(superposition,[],[f276,f236])).
% 2.93/0.79  fof(f236,plain,(
% 2.93/0.79    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)) )),
% 2.93/0.79    inference(resolution,[],[f61,f41])).
% 2.93/0.79  fof(f276,plain,(
% 2.93/0.79    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 2.93/0.79    inference(subsumption_resolution,[],[f273,f40])).
% 2.93/0.79  fof(f273,plain,(
% 2.93/0.79    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 2.93/0.79    inference(resolution,[],[f46,f41])).
% 2.93/0.79  fof(f46,plain,(
% 2.93/0.79    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~l1_pre_topc(X0)) )),
% 2.93/0.79    inference(cnf_transformation,[],[f21])).
% 2.93/0.79  fof(f21,plain,(
% 2.93/0.79    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.93/0.79    inference(ennf_transformation,[],[f15])).
% 2.93/0.79  fof(f15,axiom,(
% 2.93/0.79    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 2.93/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).
% 2.93/0.79  fof(f249,plain,(
% 2.93/0.79    v3_pre_topc(k1_tops_1(sK0,sK1),sK0)),
% 2.93/0.79    inference(subsumption_resolution,[],[f248,f39])).
% 2.93/0.79  fof(f39,plain,(
% 2.93/0.79    v2_pre_topc(sK0)),
% 2.93/0.79    inference(cnf_transformation,[],[f35])).
% 2.93/0.79  fof(f248,plain,(
% 2.93/0.79    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | ~v2_pre_topc(sK0)),
% 2.93/0.79    inference(subsumption_resolution,[],[f247,f40])).
% 2.93/0.79  fof(f247,plain,(
% 2.93/0.79    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 2.93/0.79    inference(resolution,[],[f53,f41])).
% 2.93/0.79  fof(f53,plain,(
% 2.93/0.79    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(k1_tops_1(X0,X1),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.93/0.79    inference(cnf_transformation,[],[f27])).
% 2.93/0.79  fof(f27,plain,(
% 2.93/0.79    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.93/0.79    inference(flattening,[],[f26])).
% 2.93/0.79  fof(f26,plain,(
% 2.93/0.79    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.93/0.79    inference(ennf_transformation,[],[f11])).
% 2.93/0.79  fof(f11,axiom,(
% 2.93/0.79    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 2.93/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).
% 2.93/0.79  fof(f75,plain,(
% 2.93/0.79    spl2_1 | spl2_2),
% 2.93/0.79    inference(avatar_split_clause,[],[f42,f71,f67])).
% 2.93/0.79  fof(f42,plain,(
% 2.93/0.79    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)),
% 2.93/0.79    inference(cnf_transformation,[],[f35])).
% 2.93/0.79  fof(f74,plain,(
% 2.93/0.79    ~spl2_1 | ~spl2_2),
% 2.93/0.79    inference(avatar_split_clause,[],[f43,f71,f67])).
% 2.93/0.79  fof(f43,plain,(
% 2.93/0.79    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)),
% 2.93/0.79    inference(cnf_transformation,[],[f35])).
% 2.93/0.79  % SZS output end Proof for theBenchmark
% 2.93/0.79  % (2025)------------------------------
% 2.93/0.79  % (2025)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.93/0.79  % (2025)Termination reason: Refutation
% 2.93/0.79  
% 2.93/0.79  % (2025)Memory used [KB]: 12792
% 2.93/0.79  % (2025)Time elapsed: 0.379 s
% 2.93/0.79  % (2025)------------------------------
% 2.93/0.79  % (2025)------------------------------
% 2.93/0.79  % (2018)Success in time 0.43 s
%------------------------------------------------------------------------------
