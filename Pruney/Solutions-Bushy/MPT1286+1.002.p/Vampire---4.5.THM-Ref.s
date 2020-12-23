%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1286+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:38 EST 2020

% Result     : Theorem 0.12s
% Output     : Refutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :  180 (1104 expanded)
%              Number of leaves         :   27 ( 400 expanded)
%              Depth                    :   21
%              Number of atoms          :  553 (6586 expanded)
%              Number of equality atoms :   58 ( 212 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1391,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f76,f134,f138,f159,f167,f195,f208,f229,f238,f701,f746,f750,f1278,f1325,f1382])).

fof(f1382,plain,
    ( spl3_1
    | ~ spl3_8
    | ~ spl3_14
    | ~ spl3_44
    | ~ spl3_67 ),
    inference(avatar_contradiction_clause,[],[f1381])).

fof(f1381,plain,
    ( $false
    | spl3_1
    | ~ spl3_8
    | ~ spl3_14
    | ~ spl3_44
    | ~ spl3_67 ),
    inference(subsumption_resolution,[],[f1380,f778])).

fof(f778,plain,
    ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k2_pre_topc(sK0,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))))
    | spl3_1
    | ~ spl3_44 ),
    inference(subsumption_resolution,[],[f763,f71])).

fof(f71,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_pre_topc(sK0,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl3_1
  <=> k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_pre_topc(sK0,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f763,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_pre_topc(sK0,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k2_pre_topc(sK0,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))))
    | ~ spl3_44 ),
    inference(resolution,[],[f745,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f745,plain,
    ( r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))),k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ spl3_44 ),
    inference(avatar_component_clause,[],[f743])).

fof(f743,plain,
    ( spl3_44
  <=> r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))),k4_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).

fof(f1380,plain,
    ( r1_tarski(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k2_pre_topc(sK0,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))))
    | ~ spl3_8
    | ~ spl3_14
    | ~ spl3_67 ),
    inference(forward_demodulation,[],[f1379,f158])).

fof(f158,plain,
    ( sK1 = k2_pre_topc(sK0,k1_tops_1(sK0,sK1))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f156])).

fof(f156,plain,
    ( spl3_8
  <=> sK1 = k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f1379,plain,
    ( r1_tarski(k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),sK2),k2_pre_topc(sK0,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))))
    | ~ spl3_14
    | ~ spl3_67 ),
    inference(subsumption_resolution,[],[f1366,f38])).

fof(f38,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ~ v5_tops_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    & v5_tops_1(sK2,sK0)
    & v5_tops_1(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f31,f30,f29])).

fof(f29,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v5_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
                & v5_tops_1(X2,X0)
                & v5_tops_1(X1,X0)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v5_tops_1(k4_subset_1(u1_struct_0(sK0),X1,X2),sK0)
              & v5_tops_1(X2,sK0)
              & v5_tops_1(X1,sK0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v5_tops_1(k4_subset_1(u1_struct_0(sK0),X1,X2),sK0)
            & v5_tops_1(X2,sK0)
            & v5_tops_1(X1,sK0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ~ v5_tops_1(k4_subset_1(u1_struct_0(sK0),sK1,X2),sK0)
          & v5_tops_1(X2,sK0)
          & v5_tops_1(sK1,sK0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X2] :
        ( ~ v5_tops_1(k4_subset_1(u1_struct_0(sK0),sK1,X2),sK0)
        & v5_tops_1(X2,sK0)
        & v5_tops_1(sK1,sK0)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ v5_tops_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
      & v5_tops_1(sK2,sK0)
      & v5_tops_1(sK1,sK0)
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v5_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v5_tops_1(X2,X0)
              & v5_tops_1(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v5_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v5_tops_1(X2,X0)
              & v5_tops_1(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v5_tops_1(X2,X0)
                    & v5_tops_1(X1,X0) )
                 => v5_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v5_tops_1(X2,X0)
                  & v5_tops_1(X1,X0) )
               => v5_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_tops_1)).

fof(f1366,plain,
    ( r1_tarski(k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),sK2),k2_pre_topc(sK0,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_14
    | ~ spl3_67 ),
    inference(superposition,[],[f1273,f1146])).

fof(f1146,plain,
    ( ! [X3] :
        ( k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X3),k1_tops_1(sK0,sK2))) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_tops_1(sK0,X3)),sK2)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f1139,f39])).

fof(f39,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f32])).

fof(f1139,plain,
    ( ! [X3] :
        ( k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X3),k1_tops_1(sK0,sK2))) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_tops_1(sK0,X3)),sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_14 ),
    inference(superposition,[],[f404,f228])).

fof(f228,plain,
    ( sK2 = k2_pre_topc(sK0,k1_tops_1(sK0,sK2))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f226])).

fof(f226,plain,
    ( spl3_14
  <=> sK2 = k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f404,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X0),k1_tops_1(sK0,X1))) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_tops_1(sK0,X0)),k2_pre_topc(sK0,k1_tops_1(sK0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f396,f37])).

fof(f37,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f396,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X0),k1_tops_1(sK0,X1))) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_tops_1(sK0,X0)),k2_pre_topc(sK0,k1_tops_1(sK0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f114,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

fof(f114,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),X0,k1_tops_1(sK0,X1))) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k2_pre_topc(sK0,k1_tops_1(sK0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f110,f37])).

fof(f110,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),X0,k1_tops_1(sK0,X1))) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k2_pre_topc(sK0,k1_tops_1(sK0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f58,f53])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),X1,X0)) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f57,f37])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),X1,X0)) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X0)) ) ),
    inference(resolution,[],[f36,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2)) = k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2)) = k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2)) = k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2)) = k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_pre_topc)).

fof(f36,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f1273,plain,
    ( r1_tarski(k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))),k2_pre_topc(sK0,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))))
    | ~ spl3_67 ),
    inference(avatar_component_clause,[],[f1271])).

fof(f1271,plain,
    ( spl3_67
  <=> r1_tarski(k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))),k2_pre_topc(sK0,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_67])])).

fof(f1325,plain,
    ( ~ spl3_4
    | ~ spl3_10
    | spl3_68 ),
    inference(avatar_contradiction_clause,[],[f1324])).

fof(f1324,plain,
    ( $false
    | ~ spl3_4
    | ~ spl3_10
    | spl3_68 ),
    inference(subsumption_resolution,[],[f1323,f132])).

fof(f132,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl3_4
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f1323,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_10
    | spl3_68 ),
    inference(subsumption_resolution,[],[f1322,f193])).

fof(f193,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f192])).

fof(f192,plain,
    ( spl3_10
  <=> m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f1322,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_68 ),
    inference(resolution,[],[f1277,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(f1277,plain,
    ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_68 ),
    inference(avatar_component_clause,[],[f1275])).

fof(f1275,plain,
    ( spl3_68
  <=> m1_subset_1(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_68])])).

fof(f1278,plain,
    ( spl3_67
    | ~ spl3_68
    | ~ spl3_43 ),
    inference(avatar_split_clause,[],[f1269,f739,f1275,f1271])).

fof(f739,plain,
    ( spl3_43
  <=> m1_subset_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).

fof(f1269,plain,
    ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))),k2_pre_topc(sK0,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))))
    | ~ spl3_43 ),
    inference(subsumption_resolution,[],[f1268,f37])).

fof(f1268,plain,
    ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))),k2_pre_topc(sK0,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_43 ),
    inference(subsumption_resolution,[],[f1267,f38])).

fof(f1267,plain,
    ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))),k2_pre_topc(sK0,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_43 ),
    inference(subsumption_resolution,[],[f1256,f39])).

fof(f1256,plain,
    ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))),k2_pre_topc(sK0,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_43 ),
    inference(resolution,[],[f753,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tops_1)).

fof(f753,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(k2_pre_topc(sK0,X1),k2_pre_topc(sK0,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))) )
    | ~ spl3_43 ),
    inference(resolution,[],[f740,f61])).

fof(f61,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(k2_pre_topc(sK0,X2),k2_pre_topc(sK0,X3)) ) ),
    inference(resolution,[],[f37,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_pre_topc)).

fof(f740,plain,
    ( m1_subset_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_43 ),
    inference(avatar_component_clause,[],[f739])).

fof(f750,plain,
    ( ~ spl3_2
    | spl3_43 ),
    inference(avatar_contradiction_clause,[],[f749])).

fof(f749,plain,
    ( $false
    | ~ spl3_2
    | spl3_43 ),
    inference(subsumption_resolution,[],[f748,f37])).

fof(f748,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl3_2
    | spl3_43 ),
    inference(subsumption_resolution,[],[f747,f74])).

fof(f74,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl3_2
  <=> m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f747,plain,
    ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_43 ),
    inference(resolution,[],[f741,f53])).

fof(f741,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_43 ),
    inference(avatar_component_clause,[],[f739])).

fof(f746,plain,
    ( ~ spl3_43
    | spl3_44
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f737,f73,f743,f739])).

fof(f737,plain,
    ( r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))),k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ m1_subset_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f732,f74])).

fof(f732,plain,
    ( r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))),k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ m1_subset_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2 ),
    inference(resolution,[],[f712,f60])).

fof(f60,plain,(
    ! [X1] :
      ( r1_tarski(k1_tops_1(sK0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f37,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(f712,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
        | r1_tarski(k2_pre_topc(sK0,X1),k4_subset_1(u1_struct_0(sK0),sK1,sK2))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f703,f279])).

fof(f279,plain,(
    k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
    inference(forward_demodulation,[],[f274,f97])).

fof(f97,plain,(
    sK1 = k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f93,f38])).

fof(f93,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 = k2_pre_topc(sK0,sK1) ),
    inference(resolution,[],[f92,f40])).

fof(f40,plain,(
    v5_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f92,plain,(
    ! [X0] :
      ( ~ v5_tops_1(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,X0) = X0 ) ),
    inference(subsumption_resolution,[],[f91,f37])).

fof(f91,plain,(
    ! [X0] :
      ( k2_pre_topc(sK0,X0) = X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v5_tops_1(X0,sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(duplicate_literal_removal,[],[f90])).

fof(f90,plain,(
    ! [X0] :
      ( k2_pre_topc(sK0,X0) = X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v5_tops_1(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f66,f53])).

fof(f66,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,X0) = X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v5_tops_1(X0,sK0) ) ),
    inference(superposition,[],[f59,f62])).

fof(f62,plain,(
    ! [X4] :
      ( k2_pre_topc(sK0,k1_tops_1(sK0,X4)) = X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v5_tops_1(X4,sK0) ) ),
    inference(resolution,[],[f37,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v5_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_tops_1(X1,X0)
              | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1 )
            & ( k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1
              | ~ v5_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tops_1)).

fof(f59,plain,(
    ! [X0] :
      ( k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,k2_pre_topc(sK0,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f37,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',projectivity_k2_pre_topc)).

fof(f274,plain,(
    k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK2) ),
    inference(resolution,[],[f116,f38])).

fof(f116,plain,(
    ! [X6] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),X6,sK2)) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X6),sK2) ) ),
    inference(forward_demodulation,[],[f113,f103])).

fof(f103,plain,(
    sK2 = k2_pre_topc(sK0,sK2) ),
    inference(subsumption_resolution,[],[f94,f39])).

fof(f94,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | sK2 = k2_pre_topc(sK0,sK2) ),
    inference(resolution,[],[f92,f41])).

fof(f41,plain,(
    v5_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f113,plain,(
    ! [X6] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),X6,sK2)) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X6),k2_pre_topc(sK0,sK2)) ) ),
    inference(resolution,[],[f58,f39])).

fof(f703,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(k2_pre_topc(sK0,X1),k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) )
    | ~ spl3_2 ),
    inference(resolution,[],[f74,f61])).

fof(f701,plain,
    ( spl3_2
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f700,f226,f73])).

fof(f700,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f699,f604])).

fof(f604,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK2)))
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f598,f39])).

fof(f598,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK2)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_14 ),
    inference(superposition,[],[f407,f228])).

fof(f407,plain,(
    ! [X9] :
      ( k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,X9))) = k4_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k1_tops_1(sK0,X9)))
      | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(forward_demodulation,[],[f402,f97])).

fof(f402,plain,(
    ! [X9] :
      ( k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,X9))) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,X9)))
      | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f114,f38])).

fof(f699,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK2))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f694,f39])).

fof(f694,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK2))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_14 ),
    inference(duplicate_literal_removal,[],[f693])).

fof(f693,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK2))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_14 ),
    inference(superposition,[],[f608,f228])).

fof(f608,plain,(
    ! [X3] :
      ( ~ m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,X3)),k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,X3))),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f601,f38])).

fof(f601,plain,(
    ! [X3] :
      ( m1_subset_1(k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,X3))),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,X3)),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(superposition,[],[f43,f407])).

fof(f238,plain,(
    spl3_13 ),
    inference(avatar_contradiction_clause,[],[f237])).

fof(f237,plain,
    ( $false
    | spl3_13 ),
    inference(subsumption_resolution,[],[f236,f41])).

fof(f236,plain,
    ( ~ v5_tops_1(sK2,sK0)
    | spl3_13 ),
    inference(subsumption_resolution,[],[f235,f39])).

fof(f235,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v5_tops_1(sK2,sK0)
    | spl3_13 ),
    inference(subsumption_resolution,[],[f234,f56])).

fof(f56,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f234,plain,
    ( ~ r1_tarski(sK2,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v5_tops_1(sK2,sK0)
    | spl3_13 ),
    inference(superposition,[],[f224,f62])).

fof(f224,plain,
    ( ~ r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2)))
    | spl3_13 ),
    inference(avatar_component_clause,[],[f222])).

fof(f222,plain,
    ( spl3_13
  <=> r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f229,plain,
    ( ~ spl3_13
    | spl3_14
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f210,f188,f226,f222])).

fof(f188,plain,
    ( spl3_9
  <=> r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f210,plain,
    ( sK2 = k2_pre_topc(sK0,k1_tops_1(sK0,sK2))
    | ~ r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2)))
    | ~ spl3_9 ),
    inference(resolution,[],[f190,f50])).

fof(f190,plain,
    ( r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),sK2)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f188])).

fof(f208,plain,(
    spl3_10 ),
    inference(avatar_contradiction_clause,[],[f207])).

fof(f207,plain,
    ( $false
    | spl3_10 ),
    inference(subsumption_resolution,[],[f206,f37])).

fof(f206,plain,
    ( ~ l1_pre_topc(sK0)
    | spl3_10 ),
    inference(subsumption_resolution,[],[f205,f39])).

fof(f205,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_10 ),
    inference(resolution,[],[f194,f53])).

fof(f194,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_10 ),
    inference(avatar_component_clause,[],[f192])).

fof(f195,plain,
    ( spl3_9
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f186,f192,f188])).

fof(f186,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),sK2) ),
    inference(subsumption_resolution,[],[f181,f39])).

fof(f181,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f107,f60])).

fof(f107,plain,(
    ! [X6] :
      ( ~ r1_tarski(X6,sK2)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(k2_pre_topc(sK0,X6),sK2) ) ),
    inference(backward_demodulation,[],[f82,f103])).

fof(f82,plain,(
    ! [X6] :
      ( r1_tarski(k2_pre_topc(sK0,X6),k2_pre_topc(sK0,sK2))
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X6,sK2) ) ),
    inference(resolution,[],[f61,f39])).

fof(f167,plain,(
    spl3_7 ),
    inference(avatar_contradiction_clause,[],[f166])).

fof(f166,plain,
    ( $false
    | spl3_7 ),
    inference(subsumption_resolution,[],[f165,f40])).

fof(f165,plain,
    ( ~ v5_tops_1(sK1,sK0)
    | spl3_7 ),
    inference(subsumption_resolution,[],[f164,f38])).

fof(f164,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v5_tops_1(sK1,sK0)
    | spl3_7 ),
    inference(subsumption_resolution,[],[f163,f56])).

fof(f163,plain,
    ( ~ r1_tarski(sK1,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v5_tops_1(sK1,sK0)
    | spl3_7 ),
    inference(superposition,[],[f154,f62])).

fof(f154,plain,
    ( ~ r1_tarski(sK1,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
    | spl3_7 ),
    inference(avatar_component_clause,[],[f152])).

fof(f152,plain,
    ( spl3_7
  <=> r1_tarski(sK1,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f159,plain,
    ( ~ spl3_7
    | spl3_8
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f140,f127,f156,f152])).

fof(f127,plain,
    ( spl3_3
  <=> r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f140,plain,
    ( sK1 = k2_pre_topc(sK0,k1_tops_1(sK0,sK1))
    | ~ r1_tarski(sK1,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
    | ~ spl3_3 ),
    inference(resolution,[],[f129,f50])).

fof(f129,plain,
    ( r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f127])).

fof(f138,plain,(
    spl3_4 ),
    inference(avatar_contradiction_clause,[],[f137])).

fof(f137,plain,
    ( $false
    | spl3_4 ),
    inference(subsumption_resolution,[],[f136,f37])).

fof(f136,plain,
    ( ~ l1_pre_topc(sK0)
    | spl3_4 ),
    inference(subsumption_resolution,[],[f135,f38])).

fof(f135,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_4 ),
    inference(resolution,[],[f133,f53])).

fof(f133,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f131])).

fof(f134,plain,
    ( spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f125,f131,f127])).

fof(f125,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),sK1) ),
    inference(subsumption_resolution,[],[f120,f38])).

fof(f120,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f101,f60])).

fof(f101,plain,(
    ! [X5] :
      ( ~ r1_tarski(X5,sK1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(k2_pre_topc(sK0,X5),sK1) ) ),
    inference(backward_demodulation,[],[f81,f97])).

fof(f81,plain,(
    ! [X5] :
      ( r1_tarski(k2_pre_topc(sK0,X5),k2_pre_topc(sK0,sK1))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X5,sK1) ) ),
    inference(resolution,[],[f61,f38])).

fof(f76,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f67,f73,f69])).

fof(f67,plain,
    ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_pre_topc(sK0,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(resolution,[],[f63,f42])).

fof(f42,plain,(
    ~ v5_tops_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f63,plain,(
    ! [X5] :
      ( v5_tops_1(X5,sK0)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,k1_tops_1(sK0,X5)) != X5 ) ),
    inference(resolution,[],[f37,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v5_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

%------------------------------------------------------------------------------
