%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:30 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  236 (1475 expanded)
%              Number of leaves         :   37 ( 481 expanded)
%              Depth                    :   30
%              Number of atoms          : 1172 (12990 expanded)
%              Number of equality atoms :   27 ( 186 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f344,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f117,f118,f128,f131,f150,f185,f196,f200,f207,f244,f269,f278,f291,f298,f306,f311,f337,f343])).

fof(f343,plain,
    ( ~ spl6_8
    | ~ spl6_14 ),
    inference(avatar_contradiction_clause,[],[f342])).

fof(f342,plain,
    ( $false
    | ~ spl6_8
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f341,f135])).

fof(f135,plain,(
    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f133,f134])).

fof(f134,plain,(
    k2_struct_0(sK0) = u1_struct_0(sK0) ),
    inference(resolution,[],[f129,f73])).

fof(f73,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f129,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f62,f72])).

fof(f72,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f62,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,
    ( ( ~ r1_waybel_7(sK0,sK1,sK2)
      | ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) )
    & ( r1_waybel_7(sK0,sK1,sK2)
      | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) )
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    & ~ v1_xboole_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f41,f44,f43,f42])).

fof(f42,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ r1_waybel_7(X0,X1,X2)
                  | ~ r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) )
                & ( r1_waybel_7(X0,X1,X2)
                  | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            & ~ v1_xboole_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_waybel_7(sK0,X1,X2)
                | ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1),X2) )
              & ( r1_waybel_7(sK0,X1,X2)
                | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1),X2) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ r1_waybel_7(sK0,X1,X2)
              | ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1),X2) )
            & ( r1_waybel_7(sK0,X1,X2)
              | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1),X2) )
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
        & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
        & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
        & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
        & ~ v1_xboole_0(X1) )
   => ( ? [X2] :
          ( ( ~ r1_waybel_7(sK0,sK1,X2)
            | ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X2) )
          & ( r1_waybel_7(sK0,sK1,X2)
            | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X2) )
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
      & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
      & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
      & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X2] :
        ( ( ~ r1_waybel_7(sK0,sK1,X2)
          | ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X2) )
        & ( r1_waybel_7(sK0,sK1,X2)
          | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X2) )
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ( ~ r1_waybel_7(sK0,sK1,sK2)
        | ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) )
      & ( r1_waybel_7(sK0,sK1,sK2)
        | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) )
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_waybel_7(X0,X1,X2)
                | ~ r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) )
              & ( r1_waybel_7(X0,X1,X2)
                | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_waybel_7(X0,X1,X2)
                | ~ r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) )
              & ( r1_waybel_7(X0,X1,X2)
                | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)
              <~> r1_waybel_7(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)
              <~> r1_waybel_7(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
              & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
              & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
              & ~ v1_xboole_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)
                <=> r1_waybel_7(X0,X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            & ~ v1_xboole_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)
              <=> r1_waybel_7(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_yellow19)).

fof(f133,plain,(
    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f129,f74])).

fof(f74,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).

fof(f341,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl6_8
    | ~ spl6_14 ),
    inference(forward_demodulation,[],[f340,f134])).

fof(f340,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_8
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f339,f129])).

fof(f339,plain,
    ( ~ l1_struct_0(sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_8
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f338,f60])).

fof(f60,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f338,plain,
    ( v2_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_8
    | ~ spl6_14 ),
    inference(resolution,[],[f228,f176])).

fof(f176,plain,
    ( ! [X0] :
        ( ~ v2_struct_0(k3_yellow19(X0,k2_struct_0(sK0),sK1))
        | v2_struct_0(X0)
        | ~ l1_struct_0(X0)
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X0))) )
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl6_8
  <=> ! [X0] :
        ( ~ v2_struct_0(k3_yellow19(X0,k2_struct_0(sK0),sK1))
        | v2_struct_0(X0)
        | ~ l1_struct_0(X0)
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f228,plain,
    ( v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f226])).

fof(f226,plain,
    ( spl6_14
  <=> v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f337,plain,
    ( ~ spl6_1
    | spl6_2
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(avatar_contradiction_clause,[],[f336])).

fof(f336,plain,
    ( $false
    | ~ spl6_1
    | spl6_2
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f335,f135])).

fof(f335,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl6_1
    | spl6_2
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(forward_demodulation,[],[f334,f134])).

fof(f334,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_1
    | spl6_2
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f333,f129])).

fof(f333,plain,
    ( ~ l1_struct_0(sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_1
    | spl6_2
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f332,f60])).

fof(f332,plain,
    ( v2_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_1
    | spl6_2
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(resolution,[],[f331,f176])).

fof(f331,plain,
    ( v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ spl6_1
    | spl6_2
    | ~ spl6_10
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f330,f137])).

fof(f137,plain,(
    m1_subset_1(sK2,k2_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f68,f134])).

fof(f68,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f45])).

fof(f330,plain,
    ( ~ m1_subset_1(sK2,k2_struct_0(sK0))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ spl6_1
    | spl6_2
    | ~ spl6_10
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(forward_demodulation,[],[f329,f134])).

fof(f329,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ spl6_1
    | spl6_2
    | ~ spl6_10
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f328,f116])).

fof(f116,plain,
    ( ~ r1_waybel_7(sK0,sK1,sK2)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl6_2
  <=> r1_waybel_7(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f328,plain,
    ( r1_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ spl6_1
    | ~ spl6_10
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(forward_demodulation,[],[f327,f165])).

fof(f165,plain,(
    sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f164,f60])).

fof(f164,plain,
    ( sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f163,f129])).

fof(f163,plain,
    ( sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f162,f63])).

fof(f63,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f162,plain,
    ( sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v1_xboole_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f161,f99])).

fof(f99,plain,(
    v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) ),
    inference(definition_unfolding,[],[f64,f71])).

fof(f71,plain,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_yellow_1)).

fof(f64,plain,(
    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f45])).

fof(f161,plain,
    ( sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))
    | v1_xboole_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f160,f98])).

fof(f98,plain,(
    v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(definition_unfolding,[],[f65,f71])).

fof(f65,plain,(
    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f45])).

fof(f160,plain,
    ( sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))
    | v1_xboole_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f152,f97])).

fof(f97,plain,(
    v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(definition_unfolding,[],[f66,f71])).

fof(f66,plain,(
    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f45])).

fof(f152,plain,
    ( sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))
    | v1_xboole_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f96,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | ~ v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f77,f71,f71,f71,f71])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            & ~ v1_xboole_0(X1) )
         => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_yellow19)).

fof(f96,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) ),
    inference(definition_unfolding,[],[f67,f71])).

fof(f67,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    inference(cnf_transformation,[],[f45])).

fof(f327,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ spl6_1
    | ~ spl6_10
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f326,f60])).

fof(f326,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(sK0)
    | ~ spl6_1
    | ~ spl6_10
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f325,f61])).

fof(f61,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f325,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_1
    | ~ spl6_10
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f315,f62])).

fof(f315,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_1
    | ~ spl6_10
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f314,f231])).

fof(f231,plain,
    ( v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f230])).

fof(f230,plain,
    ( spl6_15
  <=> v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f314,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_1
    | ~ spl6_10
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f313,f235])).

fof(f235,plain,
    ( v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f234])).

fof(f234,plain,
    ( spl6_16
  <=> v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f313,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_1
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f312,f304])).

fof(f304,plain,
    ( l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f303,f129])).

fof(f303,plain,
    ( ~ l1_struct_0(sK0)
    | l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f302,f60])).

fof(f302,plain,
    ( v2_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f301,f135])).

fof(f301,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ spl6_10 ),
    inference(superposition,[],[f195,f134])).

fof(f195,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X3)))
        | v2_struct_0(X3)
        | ~ l1_struct_0(X3)
        | l1_waybel_0(k3_yellow19(X3,k2_struct_0(sK0),sK1),X3) )
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f194])).

fof(f194,plain,
    ( spl6_10
  <=> ! [X3] :
        ( l1_waybel_0(k3_yellow19(X3,k2_struct_0(sK0),sK1),X3)
        | v2_struct_0(X3)
        | ~ l1_struct_0(X3)
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X3))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f312,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_1 ),
    inference(resolution,[],[f111,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_waybel_9(X0,X1,X2)
      | r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_waybel_9(X0,X1,X2)
                  | ~ r1_waybel_7(X0,k2_yellow19(X0,X1),X2) )
                & ( r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
                  | ~ r3_waybel_9(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_waybel_9(X0,X1,X2)
              <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_waybel_9(X0,X1,X2)
              <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r3_waybel_9(X0,X1,X2)
              <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_yellow19)).

fof(f111,plain,
    ( r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl6_1
  <=> r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f311,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_18 ),
    inference(avatar_contradiction_clause,[],[f310])).

fof(f310,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f309,f137])).

fof(f309,plain,
    ( ~ m1_subset_1(sK2,k2_struct_0(sK0))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f308,f112])).

fof(f112,plain,
    ( ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f110])).

fof(f308,plain,
    ( r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)
    | ~ m1_subset_1(sK2,k2_struct_0(sK0))
    | ~ spl6_2
    | ~ spl6_18 ),
    inference(resolution,[],[f243,f115])).

fof(f115,plain,
    ( r1_waybel_7(sK0,sK1,sK2)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f114])).

fof(f243,plain,
    ( ! [X0] :
        ( ~ r1_waybel_7(sK0,sK1,X0)
        | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
        | ~ m1_subset_1(X0,k2_struct_0(sK0)) )
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f242])).

fof(f242,plain,
    ( spl6_18
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k2_struct_0(sK0))
        | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
        | ~ r1_waybel_7(sK0,sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f306,plain,
    ( ~ spl6_10
    | spl6_17 ),
    inference(avatar_contradiction_clause,[],[f305])).

fof(f305,plain,
    ( $false
    | ~ spl6_10
    | spl6_17 ),
    inference(subsumption_resolution,[],[f304,f240])).

fof(f240,plain,
    ( ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | spl6_17 ),
    inference(avatar_component_clause,[],[f238])).

fof(f238,plain,
    ( spl6_17
  <=> l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f298,plain,
    ( ~ spl6_11
    | spl6_15 ),
    inference(avatar_contradiction_clause,[],[f297])).

fof(f297,plain,
    ( $false
    | ~ spl6_11
    | spl6_15 ),
    inference(subsumption_resolution,[],[f296,f135])).

fof(f296,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl6_11
    | spl6_15 ),
    inference(forward_demodulation,[],[f295,f134])).

fof(f295,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_11
    | spl6_15 ),
    inference(subsumption_resolution,[],[f294,f129])).

fof(f294,plain,
    ( ~ l1_struct_0(sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_11
    | spl6_15 ),
    inference(subsumption_resolution,[],[f293,f60])).

fof(f293,plain,
    ( v2_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_11
    | spl6_15 ),
    inference(resolution,[],[f206,f232])).

fof(f232,plain,
    ( ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | spl6_15 ),
    inference(avatar_component_clause,[],[f230])).

fof(f206,plain,
    ( ! [X5] :
        ( v4_orders_2(k3_yellow19(X5,k2_struct_0(sK0),sK1))
        | v2_struct_0(X5)
        | ~ l1_struct_0(X5)
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X5))) )
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f205])).

fof(f205,plain,
    ( spl6_11
  <=> ! [X5] :
        ( v4_orders_2(k3_yellow19(X5,k2_struct_0(sK0),sK1))
        | v2_struct_0(X5)
        | ~ l1_struct_0(X5)
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X5))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f291,plain,
    ( ~ spl6_9
    | spl6_16 ),
    inference(avatar_contradiction_clause,[],[f290])).

fof(f290,plain,
    ( $false
    | ~ spl6_9
    | spl6_16 ),
    inference(subsumption_resolution,[],[f289,f135])).

fof(f289,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl6_9
    | spl6_16 ),
    inference(forward_demodulation,[],[f288,f134])).

fof(f288,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_9
    | spl6_16 ),
    inference(subsumption_resolution,[],[f287,f129])).

fof(f287,plain,
    ( ~ l1_struct_0(sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_9
    | spl6_16 ),
    inference(subsumption_resolution,[],[f286,f60])).

fof(f286,plain,
    ( v2_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_9
    | spl6_16 ),
    inference(resolution,[],[f184,f236])).

fof(f236,plain,
    ( ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | spl6_16 ),
    inference(avatar_component_clause,[],[f234])).

fof(f184,plain,
    ( ! [X1] :
        ( v7_waybel_0(k3_yellow19(X1,k2_struct_0(sK0),sK1))
        | v2_struct_0(X1)
        | ~ l1_struct_0(X1)
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X1))) )
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f183])).

fof(f183,plain,
    ( spl6_9
  <=> ! [X1] :
        ( v7_waybel_0(k3_yellow19(X1,k2_struct_0(sK0),sK1))
        | v2_struct_0(X1)
        | ~ l1_struct_0(X1)
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f278,plain,
    ( ~ spl6_6
    | ~ spl6_7 ),
    inference(avatar_contradiction_clause,[],[f277])).

fof(f277,plain,
    ( $false
    | ~ spl6_6
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f276,f60])).

fof(f276,plain,
    ( v2_struct_0(sK0)
    | ~ spl6_6
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f275,f129])).

fof(f275,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_6
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f274,f173])).

fof(f173,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f171])).

fof(f171,plain,
    ( spl6_7
  <=> v1_xboole_0(k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f274,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_6 ),
    inference(superposition,[],[f79,f149])).

fof(f149,plain,
    ( k2_struct_0(sK0) = sK3(sK0)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl6_6
  <=> k2_struct_0(sK0) = sK3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f79,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK3(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ( ~ v1_xboole_0(sK3(X0))
        & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f32,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_xboole_0(sK3(X0))
        & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc20_struct_0)).

fof(f269,plain,
    ( spl6_5
    | ~ spl6_7 ),
    inference(avatar_contradiction_clause,[],[f268])).

fof(f268,plain,
    ( $false
    | spl6_5
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f267,f173])).

fof(f267,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK0))
    | spl6_5 ),
    inference(resolution,[],[f151,f80])).

fof(f80,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK4(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f50,f51])).

fof(f51,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f49])).

fof(f49,plain,(
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

fof(f151,plain,
    ( r2_hidden(sK5(k2_struct_0(sK0),sK3(sK0)),k2_struct_0(sK0))
    | spl6_5 ),
    inference(resolution,[],[f145,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK5(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f56,f57])).

fof(f57,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
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

fof(f145,plain,
    ( ~ r1_tarski(k2_struct_0(sK0),sK3(sK0))
    | spl6_5 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl6_5
  <=> r1_tarski(k2_struct_0(sK0),sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f244,plain,
    ( spl6_14
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_17
    | spl6_18 ),
    inference(avatar_split_clause,[],[f224,f242,f238,f234,f230,f226])).

fof(f224,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k2_struct_0(sK0))
      | ~ r1_waybel_7(sK0,sK1,X0)
      | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
      | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ) ),
    inference(forward_demodulation,[],[f223,f134])).

fof(f223,plain,(
    ! [X0] :
      ( ~ r1_waybel_7(sK0,sK1,X0)
      | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ) ),
    inference(subsumption_resolution,[],[f222,f60])).

fof(f222,plain,(
    ! [X0] :
      ( ~ r1_waybel_7(sK0,sK1,X0)
      | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f221,f61])).

fof(f221,plain,(
    ! [X0] :
      ( ~ r1_waybel_7(sK0,sK1,X0)
      | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f220,f62])).

fof(f220,plain,(
    ! [X0] :
      ( ~ r1_waybel_7(sK0,sK1,X0)
      | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f76,f165])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
      | r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f207,plain,
    ( spl6_7
    | spl6_11 ),
    inference(avatar_split_clause,[],[f203,f205,f171])).

fof(f203,plain,(
    ! [X5] :
      ( v4_orders_2(k3_yellow19(X5,k2_struct_0(sK0),sK1))
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X5)))
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ l1_struct_0(X5)
      | v2_struct_0(X5) ) ),
    inference(subsumption_resolution,[],[f202,f63])).

fof(f202,plain,(
    ! [X5] :
      ( v4_orders_2(k3_yellow19(X5,k2_struct_0(sK0),sK1))
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X5)))
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ l1_struct_0(X5)
      | v2_struct_0(X5) ) ),
    inference(subsumption_resolution,[],[f201,f98])).

fof(f201,plain,(
    ! [X5] :
      ( v4_orders_2(k3_yellow19(X5,k2_struct_0(sK0),sK1))
      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X5)))
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ l1_struct_0(X5)
      | v2_struct_0(X5) ) ),
    inference(subsumption_resolution,[],[f158,f97])).

fof(f158,plain,(
    ! [X5] :
      ( v4_orders_2(k3_yellow19(X5,k2_struct_0(sK0),sK1))
      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X5)))
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ l1_struct_0(X5)
      | v2_struct_0(X5) ) ),
    inference(resolution,[],[f96,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
      | v4_orders_2(k3_yellow19(X0,X1,X2))
      | ~ v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | ~ v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f91,f71,f71,f71])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( v4_orders_2(k3_yellow19(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( v4_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( v4_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v4_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v4_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v4_orders_2(k3_yellow19(X0,X1,X2))
        & v3_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_yellow19)).

fof(f200,plain,
    ( spl6_7
    | spl6_8 ),
    inference(avatar_split_clause,[],[f199,f175,f171])).

fof(f199,plain,(
    ! [X4] :
      ( ~ v2_struct_0(k3_yellow19(X4,k2_struct_0(sK0),sK1))
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X4)))
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ l1_struct_0(X4)
      | v2_struct_0(X4) ) ),
    inference(subsumption_resolution,[],[f198,f63])).

fof(f198,plain,(
    ! [X4] :
      ( ~ v2_struct_0(k3_yellow19(X4,k2_struct_0(sK0),sK1))
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X4)))
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ l1_struct_0(X4)
      | v2_struct_0(X4) ) ),
    inference(subsumption_resolution,[],[f197,f98])).

fof(f197,plain,(
    ! [X4] :
      ( ~ v2_struct_0(k3_yellow19(X4,k2_struct_0(sK0),sK1))
      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X4)))
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ l1_struct_0(X4)
      | v2_struct_0(X4) ) ),
    inference(subsumption_resolution,[],[f157,f97])).

fof(f157,plain,(
    ! [X4] :
      ( ~ v2_struct_0(k3_yellow19(X4,k2_struct_0(sK0),sK1))
      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X4)))
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ l1_struct_0(X4)
      | v2_struct_0(X4) ) ),
    inference(resolution,[],[f96,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
      | ~ v2_struct_0(k3_yellow19(X0,X1,X2))
      | ~ v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | ~ v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f90,f71,f71,f71])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k3_yellow19(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f196,plain,
    ( spl6_7
    | spl6_10 ),
    inference(avatar_split_clause,[],[f192,f194,f171])).

fof(f192,plain,(
    ! [X3] :
      ( l1_waybel_0(k3_yellow19(X3,k2_struct_0(sK0),sK1),X3)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X3)))
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ l1_struct_0(X3)
      | v2_struct_0(X3) ) ),
    inference(subsumption_resolution,[],[f191,f63])).

fof(f191,plain,(
    ! [X3] :
      ( l1_waybel_0(k3_yellow19(X3,k2_struct_0(sK0),sK1),X3)
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X3)))
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ l1_struct_0(X3)
      | v2_struct_0(X3) ) ),
    inference(subsumption_resolution,[],[f190,f98])).

fof(f190,plain,(
    ! [X3] :
      ( l1_waybel_0(k3_yellow19(X3,k2_struct_0(sK0),sK1),X3)
      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X3)))
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ l1_struct_0(X3)
      | v2_struct_0(X3) ) ),
    inference(subsumption_resolution,[],[f156,f97])).

fof(f156,plain,(
    ! [X3] :
      ( l1_waybel_0(k3_yellow19(X3,k2_struct_0(sK0),sK1),X3)
      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X3)))
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ l1_struct_0(X3)
      | v2_struct_0(X3) ) ),
    inference(resolution,[],[f96,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
      | l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
      | ~ v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | ~ v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f93,f71,f71,f71])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow19)).

fof(f185,plain,
    ( spl6_7
    | spl6_9 ),
    inference(avatar_split_clause,[],[f181,f183,f171])).

fof(f181,plain,(
    ! [X1] :
      ( v7_waybel_0(k3_yellow19(X1,k2_struct_0(sK0),sK1))
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X1)))
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f180,f63])).

fof(f180,plain,(
    ! [X1] :
      ( v7_waybel_0(k3_yellow19(X1,k2_struct_0(sK0),sK1))
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X1)))
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f179,f99])).

fof(f179,plain,(
    ! [X1] :
      ( v7_waybel_0(k3_yellow19(X1,k2_struct_0(sK0),sK1))
      | ~ v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X1)))
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f178,f98])).

fof(f178,plain,(
    ! [X1] :
      ( v7_waybel_0(k3_yellow19(X1,k2_struct_0(sK0),sK1))
      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | ~ v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X1)))
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f154,f97])).

fof(f154,plain,(
    ! [X1] :
      ( v7_waybel_0(k3_yellow19(X1,k2_struct_0(sK0),sK1))
      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | ~ v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X1)))
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f96,f105])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
      | v7_waybel_0(k3_yellow19(X0,X1,X2))
      | ~ v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | ~ v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | ~ v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f95,f71,f71,f71,f71])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( v7_waybel_0(k3_yellow19(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( v7_waybel_0(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( v7_waybel_0(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_waybel_0(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_waybel_0(k3_yellow19(X0,X1,X2))
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow19)).

fof(f150,plain,
    ( ~ spl6_5
    | spl6_6
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f141,f121,f147,f143])).

fof(f121,plain,
    ( spl6_3
  <=> m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f141,plain,
    ( k2_struct_0(sK0) = sK3(sK0)
    | ~ r1_tarski(k2_struct_0(sK0),sK3(sK0))
    | ~ spl6_3 ),
    inference(resolution,[],[f139,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
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

fof(f139,plain,
    ( r1_tarski(sK3(sK0),k2_struct_0(sK0))
    | ~ spl6_3 ),
    inference(resolution,[],[f136,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f136,plain,
    ( m1_subset_1(sK3(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl6_3 ),
    inference(backward_demodulation,[],[f123,f134])).

fof(f123,plain,
    ( m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f121])).

fof(f131,plain,(
    spl6_4 ),
    inference(avatar_contradiction_clause,[],[f130])).

fof(f130,plain,
    ( $false
    | spl6_4 ),
    inference(subsumption_resolution,[],[f129,f127])).

fof(f127,plain,
    ( ~ l1_struct_0(sK0)
    | spl6_4 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl6_4
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f128,plain,
    ( spl6_3
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f119,f125,f121])).

fof(f119,plain,
    ( ~ l1_struct_0(sK0)
    | m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f60,f78])).

fof(f78,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f118,plain,
    ( spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f69,f114,f110])).

fof(f69,plain,
    ( r1_waybel_7(sK0,sK1,sK2)
    | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f117,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f70,f114,f110])).

fof(f70,plain,
    ( ~ r1_waybel_7(sK0,sK1,sK2)
    | ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
    inference(cnf_transformation,[],[f45])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:08:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (6825)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.51  % (6843)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.51  % (6832)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.51  % (6841)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.52  % (6841)Refutation not found, incomplete strategy% (6841)------------------------------
% 0.22/0.52  % (6841)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (6835)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.52  % (6837)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.52  % (6841)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  % (6836)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  
% 0.22/0.52  % (6841)Memory used [KB]: 10746
% 0.22/0.52  % (6841)Time elapsed: 0.104 s
% 0.22/0.52  % (6833)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.52  % (6841)------------------------------
% 0.22/0.52  % (6841)------------------------------
% 0.22/0.52  % (6835)Refutation not found, incomplete strategy% (6835)------------------------------
% 0.22/0.52  % (6835)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (6835)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (6835)Memory used [KB]: 10746
% 0.22/0.52  % (6835)Time elapsed: 0.117 s
% 0.22/0.52  % (6835)------------------------------
% 0.22/0.52  % (6835)------------------------------
% 0.22/0.52  % (6834)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.53  % (6850)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.53  % (6849)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.53  % (6832)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f344,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(avatar_sat_refutation,[],[f117,f118,f128,f131,f150,f185,f196,f200,f207,f244,f269,f278,f291,f298,f306,f311,f337,f343])).
% 0.22/0.53  fof(f343,plain,(
% 0.22/0.53    ~spl6_8 | ~spl6_14),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f342])).
% 0.22/0.53  fof(f342,plain,(
% 0.22/0.53    $false | (~spl6_8 | ~spl6_14)),
% 0.22/0.53    inference(subsumption_resolution,[],[f341,f135])).
% 0.22/0.53  fof(f135,plain,(
% 0.22/0.53    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.22/0.53    inference(backward_demodulation,[],[f133,f134])).
% 0.22/0.53  fof(f134,plain,(
% 0.22/0.53    k2_struct_0(sK0) = u1_struct_0(sK0)),
% 0.22/0.53    inference(resolution,[],[f129,f73])).
% 0.22/0.53  fof(f73,plain,(
% 0.22/0.53    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f25])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.22/0.53  fof(f129,plain,(
% 0.22/0.53    l1_struct_0(sK0)),
% 0.22/0.53    inference(resolution,[],[f62,f72])).
% 0.22/0.53  fof(f72,plain,(
% 0.22/0.53    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f24])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,axiom,(
% 0.22/0.53    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.53  fof(f62,plain,(
% 0.22/0.53    l1_pre_topc(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f45])).
% 0.22/0.53  fof(f45,plain,(
% 0.22/0.53    (((~r1_waybel_7(sK0,sK1,sK2) | ~r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)) & (r1_waybel_7(sK0,sK1,sK2) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)) & m1_subset_1(sK2,u1_struct_0(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f41,f44,f43,f42])).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (? [X2] : ((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~r1_waybel_7(sK0,X1,X2) | ~r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1),X2)) & (r1_waybel_7(sK0,X1,X2) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1),X2)) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f43,plain,(
% 0.22/0.53    ? [X1] : (? [X2] : ((~r1_waybel_7(sK0,X1,X2) | ~r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1),X2)) & (r1_waybel_7(sK0,X1,X2) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1),X2)) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(X1)) => (? [X2] : ((~r1_waybel_7(sK0,sK1,X2) | ~r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X2)) & (r1_waybel_7(sK0,sK1,X2) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X2)) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(sK1))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f44,plain,(
% 0.22/0.53    ? [X2] : ((~r1_waybel_7(sK0,sK1,X2) | ~r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X2)) & (r1_waybel_7(sK0,sK1,X2) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X2)) & m1_subset_1(X2,u1_struct_0(sK0))) => ((~r1_waybel_7(sK0,sK1,sK2) | ~r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)) & (r1_waybel_7(sK0,sK1,sK2) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)) & m1_subset_1(sK2,u1_struct_0(sK0)))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f41,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (? [X2] : ((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f40])).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (? [X2] : (((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.53    inference(nnf_transformation,[],[f23])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (? [X2] : ((r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <~> r1_waybel_7(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f22])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (? [X2] : ((r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <~> r1_waybel_7(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f16])).
% 0.22/0.53  fof(f16,negated_conjecture,(
% 0.22/0.53    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <=> r1_waybel_7(X0,X1,X2)))))),
% 0.22/0.53    inference(negated_conjecture,[],[f15])).
% 0.22/0.53  fof(f15,conjecture,(
% 0.22/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <=> r1_waybel_7(X0,X1,X2)))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_yellow19)).
% 0.22/0.53  fof(f133,plain,(
% 0.22/0.53    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.53    inference(resolution,[],[f129,f74])).
% 0.22/0.53  fof(f74,plain,(
% 0.22/0.53    ( ! [X0] : (~l1_struct_0(X0) | m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f26])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0] : (l1_struct_0(X0) => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).
% 0.22/0.53  fof(f341,plain,(
% 0.22/0.53    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | (~spl6_8 | ~spl6_14)),
% 0.22/0.53    inference(forward_demodulation,[],[f340,f134])).
% 0.22/0.53  fof(f340,plain,(
% 0.22/0.53    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl6_8 | ~spl6_14)),
% 0.22/0.53    inference(subsumption_resolution,[],[f339,f129])).
% 0.22/0.53  fof(f339,plain,(
% 0.22/0.53    ~l1_struct_0(sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl6_8 | ~spl6_14)),
% 0.22/0.53    inference(subsumption_resolution,[],[f338,f60])).
% 0.22/0.53  fof(f60,plain,(
% 0.22/0.53    ~v2_struct_0(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f45])).
% 0.22/0.53  fof(f338,plain,(
% 0.22/0.53    v2_struct_0(sK0) | ~l1_struct_0(sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl6_8 | ~spl6_14)),
% 0.22/0.53    inference(resolution,[],[f228,f176])).
% 0.22/0.53  fof(f176,plain,(
% 0.22/0.53    ( ! [X0] : (~v2_struct_0(k3_yellow19(X0,k2_struct_0(sK0),sK1)) | v2_struct_0(X0) | ~l1_struct_0(X0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X0)))) ) | ~spl6_8),
% 0.22/0.53    inference(avatar_component_clause,[],[f175])).
% 0.22/0.53  fof(f175,plain,(
% 0.22/0.53    spl6_8 <=> ! [X0] : (~v2_struct_0(k3_yellow19(X0,k2_struct_0(sK0),sK1)) | v2_struct_0(X0) | ~l1_struct_0(X0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.22/0.53  fof(f228,plain,(
% 0.22/0.53    v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~spl6_14),
% 0.22/0.53    inference(avatar_component_clause,[],[f226])).
% 0.22/0.53  fof(f226,plain,(
% 0.22/0.53    spl6_14 <=> v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.22/0.53  fof(f337,plain,(
% 0.22/0.53    ~spl6_1 | spl6_2 | ~spl6_8 | ~spl6_10 | ~spl6_15 | ~spl6_16),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f336])).
% 0.22/0.53  fof(f336,plain,(
% 0.22/0.53    $false | (~spl6_1 | spl6_2 | ~spl6_8 | ~spl6_10 | ~spl6_15 | ~spl6_16)),
% 0.22/0.53    inference(subsumption_resolution,[],[f335,f135])).
% 0.22/0.53  fof(f335,plain,(
% 0.22/0.53    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | (~spl6_1 | spl6_2 | ~spl6_8 | ~spl6_10 | ~spl6_15 | ~spl6_16)),
% 0.22/0.53    inference(forward_demodulation,[],[f334,f134])).
% 0.22/0.53  fof(f334,plain,(
% 0.22/0.53    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl6_1 | spl6_2 | ~spl6_8 | ~spl6_10 | ~spl6_15 | ~spl6_16)),
% 0.22/0.53    inference(subsumption_resolution,[],[f333,f129])).
% 0.22/0.53  fof(f333,plain,(
% 0.22/0.53    ~l1_struct_0(sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl6_1 | spl6_2 | ~spl6_8 | ~spl6_10 | ~spl6_15 | ~spl6_16)),
% 0.22/0.53    inference(subsumption_resolution,[],[f332,f60])).
% 0.22/0.53  fof(f332,plain,(
% 0.22/0.53    v2_struct_0(sK0) | ~l1_struct_0(sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl6_1 | spl6_2 | ~spl6_8 | ~spl6_10 | ~spl6_15 | ~spl6_16)),
% 0.22/0.53    inference(resolution,[],[f331,f176])).
% 0.22/0.53  fof(f331,plain,(
% 0.22/0.53    v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | (~spl6_1 | spl6_2 | ~spl6_10 | ~spl6_15 | ~spl6_16)),
% 0.22/0.53    inference(subsumption_resolution,[],[f330,f137])).
% 0.22/0.53  fof(f137,plain,(
% 0.22/0.53    m1_subset_1(sK2,k2_struct_0(sK0))),
% 0.22/0.53    inference(backward_demodulation,[],[f68,f134])).
% 0.22/0.53  fof(f68,plain,(
% 0.22/0.53    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.22/0.53    inference(cnf_transformation,[],[f45])).
% 0.22/0.53  fof(f330,plain,(
% 0.22/0.53    ~m1_subset_1(sK2,k2_struct_0(sK0)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | (~spl6_1 | spl6_2 | ~spl6_10 | ~spl6_15 | ~spl6_16)),
% 0.22/0.53    inference(forward_demodulation,[],[f329,f134])).
% 0.22/0.53  fof(f329,plain,(
% 0.22/0.53    ~m1_subset_1(sK2,u1_struct_0(sK0)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | (~spl6_1 | spl6_2 | ~spl6_10 | ~spl6_15 | ~spl6_16)),
% 0.22/0.53    inference(subsumption_resolution,[],[f328,f116])).
% 0.22/0.53  fof(f116,plain,(
% 0.22/0.53    ~r1_waybel_7(sK0,sK1,sK2) | spl6_2),
% 0.22/0.53    inference(avatar_component_clause,[],[f114])).
% 0.22/0.53  fof(f114,plain,(
% 0.22/0.53    spl6_2 <=> r1_waybel_7(sK0,sK1,sK2)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.22/0.53  fof(f328,plain,(
% 0.22/0.53    r1_waybel_7(sK0,sK1,sK2) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | (~spl6_1 | ~spl6_10 | ~spl6_15 | ~spl6_16)),
% 0.22/0.53    inference(forward_demodulation,[],[f327,f165])).
% 0.22/0.53  fof(f165,plain,(
% 0.22/0.53    sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.22/0.53    inference(subsumption_resolution,[],[f164,f60])).
% 0.22/0.53  fof(f164,plain,(
% 0.22/0.53    sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(sK0)),
% 0.22/0.53    inference(subsumption_resolution,[],[f163,f129])).
% 0.22/0.53  fof(f163,plain,(
% 0.22/0.53    sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.22/0.53    inference(subsumption_resolution,[],[f162,f63])).
% 0.22/0.53  fof(f63,plain,(
% 0.22/0.53    ~v1_xboole_0(sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f45])).
% 0.22/0.53  fof(f162,plain,(
% 0.22/0.53    sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v1_xboole_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.22/0.53    inference(subsumption_resolution,[],[f161,f99])).
% 0.22/0.53  fof(f99,plain,(
% 0.22/0.53    v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))),
% 0.22/0.53    inference(definition_unfolding,[],[f64,f71])).
% 0.22/0.53  fof(f71,plain,(
% 0.22/0.53    ( ! [X0] : (k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f9])).
% 0.22/0.53  fof(f9,axiom,(
% 0.22/0.53    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_yellow_1)).
% 0.22/0.53  fof(f64,plain,(
% 0.22/0.53    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))),
% 0.22/0.53    inference(cnf_transformation,[],[f45])).
% 0.22/0.53  fof(f161,plain,(
% 0.22/0.53    sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) | v1_xboole_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.22/0.53    inference(subsumption_resolution,[],[f160,f98])).
% 0.22/0.53  fof(f98,plain,(
% 0.22/0.53    v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))),
% 0.22/0.53    inference(definition_unfolding,[],[f65,f71])).
% 0.22/0.53  fof(f65,plain,(
% 0.22/0.53    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 0.22/0.53    inference(cnf_transformation,[],[f45])).
% 0.22/0.53  fof(f160,plain,(
% 0.22/0.53    sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) | v1_xboole_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.22/0.53    inference(subsumption_resolution,[],[f152,f97])).
% 0.22/0.53  fof(f97,plain,(
% 0.22/0.53    v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))),
% 0.22/0.53    inference(definition_unfolding,[],[f66,f71])).
% 0.22/0.53  fof(f66,plain,(
% 0.22/0.53    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 0.22/0.53    inference(cnf_transformation,[],[f45])).
% 0.22/0.53  fof(f152,plain,(
% 0.22/0.53    sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) | v1_xboole_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.22/0.53    inference(resolution,[],[f96,f100])).
% 0.22/0.53  fof(f100,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))) | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(definition_unfolding,[],[f77,f71,f71,f71,f71])).
% 0.22/0.53  fof(f77,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f30])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f29])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f14])).
% 0.22/0.53  fof(f14,axiom,(
% 0.22/0.53    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_yellow19)).
% 0.22/0.53  fof(f96,plain,(
% 0.22/0.53    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))),
% 0.22/0.53    inference(definition_unfolding,[],[f67,f71])).
% 0.22/0.53  fof(f67,plain,(
% 0.22/0.53    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))),
% 0.22/0.53    inference(cnf_transformation,[],[f45])).
% 0.22/0.53  fof(f327,plain,(
% 0.22/0.53    r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | (~spl6_1 | ~spl6_10 | ~spl6_15 | ~spl6_16)),
% 0.22/0.53    inference(subsumption_resolution,[],[f326,f60])).
% 0.22/0.53  fof(f326,plain,(
% 0.22/0.53    r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(sK0) | (~spl6_1 | ~spl6_10 | ~spl6_15 | ~spl6_16)),
% 0.22/0.53    inference(subsumption_resolution,[],[f325,f61])).
% 0.22/0.53  fof(f61,plain,(
% 0.22/0.53    v2_pre_topc(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f45])).
% 0.22/0.53  fof(f325,plain,(
% 0.22/0.53    r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_1 | ~spl6_10 | ~spl6_15 | ~spl6_16)),
% 0.22/0.53    inference(subsumption_resolution,[],[f315,f62])).
% 0.22/0.53  fof(f315,plain,(
% 0.22/0.53    r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_1 | ~spl6_10 | ~spl6_15 | ~spl6_16)),
% 0.22/0.53    inference(subsumption_resolution,[],[f314,f231])).
% 0.22/0.53  fof(f231,plain,(
% 0.22/0.53    v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~spl6_15),
% 0.22/0.53    inference(avatar_component_clause,[],[f230])).
% 0.22/0.53  fof(f230,plain,(
% 0.22/0.53    spl6_15 <=> v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.22/0.53  fof(f314,plain,(
% 0.22/0.53    r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_1 | ~spl6_10 | ~spl6_16)),
% 0.22/0.53    inference(subsumption_resolution,[],[f313,f235])).
% 0.22/0.53  fof(f235,plain,(
% 0.22/0.53    v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~spl6_16),
% 0.22/0.53    inference(avatar_component_clause,[],[f234])).
% 0.22/0.53  fof(f234,plain,(
% 0.22/0.53    spl6_16 <=> v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.22/0.53  fof(f313,plain,(
% 0.22/0.53    r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_1 | ~spl6_10)),
% 0.22/0.53    inference(subsumption_resolution,[],[f312,f304])).
% 0.22/0.53  fof(f304,plain,(
% 0.22/0.53    l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | ~spl6_10),
% 0.22/0.53    inference(subsumption_resolution,[],[f303,f129])).
% 0.22/0.53  fof(f303,plain,(
% 0.22/0.53    ~l1_struct_0(sK0) | l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | ~spl6_10),
% 0.22/0.53    inference(subsumption_resolution,[],[f302,f60])).
% 0.22/0.53  fof(f302,plain,(
% 0.22/0.53    v2_struct_0(sK0) | ~l1_struct_0(sK0) | l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | ~spl6_10),
% 0.22/0.53    inference(subsumption_resolution,[],[f301,f135])).
% 0.22/0.53  fof(f301,plain,(
% 0.22/0.53    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | v2_struct_0(sK0) | ~l1_struct_0(sK0) | l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | ~spl6_10),
% 0.22/0.53    inference(superposition,[],[f195,f134])).
% 0.22/0.53  fof(f195,plain,(
% 0.22/0.53    ( ! [X3] : (~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X3))) | v2_struct_0(X3) | ~l1_struct_0(X3) | l1_waybel_0(k3_yellow19(X3,k2_struct_0(sK0),sK1),X3)) ) | ~spl6_10),
% 0.22/0.53    inference(avatar_component_clause,[],[f194])).
% 0.22/0.53  fof(f194,plain,(
% 0.22/0.53    spl6_10 <=> ! [X3] : (l1_waybel_0(k3_yellow19(X3,k2_struct_0(sK0),sK1),X3) | v2_struct_0(X3) | ~l1_struct_0(X3) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X3))))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.22/0.53  fof(f312,plain,(
% 0.22/0.53    r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | ~v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl6_1),
% 0.22/0.53    inference(resolution,[],[f111,f75])).
% 0.22/0.53  fof(f75,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r3_waybel_9(X0,X1,X2) | r1_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f46])).
% 0.22/0.53  fof(f46,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (((r3_waybel_9(X0,X1,X2) | ~r1_waybel_7(X0,k2_yellow19(X0,X1),X2)) & (r1_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~r3_waybel_9(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(nnf_transformation,[],[f28])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f27])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f13])).
% 0.22/0.53  fof(f13,axiom,(
% 0.22/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,X1,X2) <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2)))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_yellow19)).
% 0.22/0.53  fof(f111,plain,(
% 0.22/0.53    r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) | ~spl6_1),
% 0.22/0.53    inference(avatar_component_clause,[],[f110])).
% 0.22/0.53  fof(f110,plain,(
% 0.22/0.53    spl6_1 <=> r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.22/0.53  fof(f311,plain,(
% 0.22/0.53    spl6_1 | ~spl6_2 | ~spl6_18),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f310])).
% 0.22/0.53  fof(f310,plain,(
% 0.22/0.53    $false | (spl6_1 | ~spl6_2 | ~spl6_18)),
% 0.22/0.53    inference(subsumption_resolution,[],[f309,f137])).
% 0.22/0.53  fof(f309,plain,(
% 0.22/0.53    ~m1_subset_1(sK2,k2_struct_0(sK0)) | (spl6_1 | ~spl6_2 | ~spl6_18)),
% 0.22/0.53    inference(subsumption_resolution,[],[f308,f112])).
% 0.22/0.53  fof(f112,plain,(
% 0.22/0.53    ~r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) | spl6_1),
% 0.22/0.53    inference(avatar_component_clause,[],[f110])).
% 0.22/0.53  fof(f308,plain,(
% 0.22/0.53    r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) | ~m1_subset_1(sK2,k2_struct_0(sK0)) | (~spl6_2 | ~spl6_18)),
% 0.22/0.53    inference(resolution,[],[f243,f115])).
% 0.22/0.53  fof(f115,plain,(
% 0.22/0.53    r1_waybel_7(sK0,sK1,sK2) | ~spl6_2),
% 0.22/0.53    inference(avatar_component_clause,[],[f114])).
% 0.22/0.53  fof(f243,plain,(
% 0.22/0.53    ( ! [X0] : (~r1_waybel_7(sK0,sK1,X0) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) | ~m1_subset_1(X0,k2_struct_0(sK0))) ) | ~spl6_18),
% 0.22/0.53    inference(avatar_component_clause,[],[f242])).
% 0.22/0.53  fof(f242,plain,(
% 0.22/0.53    spl6_18 <=> ! [X0] : (~m1_subset_1(X0,k2_struct_0(sK0)) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) | ~r1_waybel_7(sK0,sK1,X0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.22/0.53  fof(f306,plain,(
% 0.22/0.53    ~spl6_10 | spl6_17),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f305])).
% 0.22/0.53  fof(f305,plain,(
% 0.22/0.53    $false | (~spl6_10 | spl6_17)),
% 0.22/0.53    inference(subsumption_resolution,[],[f304,f240])).
% 0.22/0.53  fof(f240,plain,(
% 0.22/0.53    ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | spl6_17),
% 0.22/0.53    inference(avatar_component_clause,[],[f238])).
% 0.22/0.53  fof(f238,plain,(
% 0.22/0.53    spl6_17 <=> l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.22/0.53  fof(f298,plain,(
% 0.22/0.53    ~spl6_11 | spl6_15),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f297])).
% 0.22/0.53  fof(f297,plain,(
% 0.22/0.53    $false | (~spl6_11 | spl6_15)),
% 0.22/0.53    inference(subsumption_resolution,[],[f296,f135])).
% 0.22/0.53  fof(f296,plain,(
% 0.22/0.53    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | (~spl6_11 | spl6_15)),
% 0.22/0.53    inference(forward_demodulation,[],[f295,f134])).
% 0.22/0.53  fof(f295,plain,(
% 0.22/0.53    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl6_11 | spl6_15)),
% 0.22/0.53    inference(subsumption_resolution,[],[f294,f129])).
% 0.22/0.53  fof(f294,plain,(
% 0.22/0.53    ~l1_struct_0(sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl6_11 | spl6_15)),
% 0.22/0.53    inference(subsumption_resolution,[],[f293,f60])).
% 0.22/0.53  fof(f293,plain,(
% 0.22/0.53    v2_struct_0(sK0) | ~l1_struct_0(sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl6_11 | spl6_15)),
% 0.22/0.53    inference(resolution,[],[f206,f232])).
% 0.22/0.53  fof(f232,plain,(
% 0.22/0.53    ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | spl6_15),
% 0.22/0.53    inference(avatar_component_clause,[],[f230])).
% 0.22/0.53  fof(f206,plain,(
% 0.22/0.53    ( ! [X5] : (v4_orders_2(k3_yellow19(X5,k2_struct_0(sK0),sK1)) | v2_struct_0(X5) | ~l1_struct_0(X5) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X5)))) ) | ~spl6_11),
% 0.22/0.53    inference(avatar_component_clause,[],[f205])).
% 0.22/0.53  fof(f205,plain,(
% 0.22/0.53    spl6_11 <=> ! [X5] : (v4_orders_2(k3_yellow19(X5,k2_struct_0(sK0),sK1)) | v2_struct_0(X5) | ~l1_struct_0(X5) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X5))))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.22/0.53  fof(f291,plain,(
% 0.22/0.53    ~spl6_9 | spl6_16),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f290])).
% 0.22/0.53  fof(f290,plain,(
% 0.22/0.53    $false | (~spl6_9 | spl6_16)),
% 0.22/0.53    inference(subsumption_resolution,[],[f289,f135])).
% 0.22/0.53  fof(f289,plain,(
% 0.22/0.53    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | (~spl6_9 | spl6_16)),
% 0.22/0.53    inference(forward_demodulation,[],[f288,f134])).
% 0.22/0.53  fof(f288,plain,(
% 0.22/0.53    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl6_9 | spl6_16)),
% 0.22/0.53    inference(subsumption_resolution,[],[f287,f129])).
% 0.22/0.53  fof(f287,plain,(
% 0.22/0.53    ~l1_struct_0(sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl6_9 | spl6_16)),
% 0.22/0.53    inference(subsumption_resolution,[],[f286,f60])).
% 0.22/0.53  fof(f286,plain,(
% 0.22/0.53    v2_struct_0(sK0) | ~l1_struct_0(sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl6_9 | spl6_16)),
% 0.22/0.53    inference(resolution,[],[f184,f236])).
% 0.22/0.53  fof(f236,plain,(
% 0.22/0.53    ~v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | spl6_16),
% 0.22/0.53    inference(avatar_component_clause,[],[f234])).
% 0.22/0.53  fof(f184,plain,(
% 0.22/0.53    ( ! [X1] : (v7_waybel_0(k3_yellow19(X1,k2_struct_0(sK0),sK1)) | v2_struct_0(X1) | ~l1_struct_0(X1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X1)))) ) | ~spl6_9),
% 0.22/0.53    inference(avatar_component_clause,[],[f183])).
% 0.22/0.53  fof(f183,plain,(
% 0.22/0.53    spl6_9 <=> ! [X1] : (v7_waybel_0(k3_yellow19(X1,k2_struct_0(sK0),sK1)) | v2_struct_0(X1) | ~l1_struct_0(X1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X1))))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.22/0.53  fof(f278,plain,(
% 0.22/0.53    ~spl6_6 | ~spl6_7),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f277])).
% 0.22/0.53  fof(f277,plain,(
% 0.22/0.53    $false | (~spl6_6 | ~spl6_7)),
% 0.22/0.53    inference(subsumption_resolution,[],[f276,f60])).
% 0.22/0.53  fof(f276,plain,(
% 0.22/0.53    v2_struct_0(sK0) | (~spl6_6 | ~spl6_7)),
% 0.22/0.53    inference(subsumption_resolution,[],[f275,f129])).
% 0.22/0.53  fof(f275,plain,(
% 0.22/0.53    ~l1_struct_0(sK0) | v2_struct_0(sK0) | (~spl6_6 | ~spl6_7)),
% 0.22/0.53    inference(subsumption_resolution,[],[f274,f173])).
% 0.22/0.53  fof(f173,plain,(
% 0.22/0.53    v1_xboole_0(k2_struct_0(sK0)) | ~spl6_7),
% 0.22/0.53    inference(avatar_component_clause,[],[f171])).
% 0.22/0.53  fof(f171,plain,(
% 0.22/0.53    spl6_7 <=> v1_xboole_0(k2_struct_0(sK0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.22/0.53  fof(f274,plain,(
% 0.22/0.53    ~v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~spl6_6),
% 0.22/0.53    inference(superposition,[],[f79,f149])).
% 0.22/0.53  fof(f149,plain,(
% 0.22/0.53    k2_struct_0(sK0) = sK3(sK0) | ~spl6_6),
% 0.22/0.53    inference(avatar_component_clause,[],[f147])).
% 0.22/0.53  fof(f147,plain,(
% 0.22/0.53    spl6_6 <=> k2_struct_0(sK0) = sK3(sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.22/0.53  fof(f79,plain,(
% 0.22/0.53    ( ! [X0] : (~v1_xboole_0(sK3(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f48])).
% 0.22/0.53  fof(f48,plain,(
% 0.22/0.53    ! [X0] : ((~v1_xboole_0(sK3(X0)) & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f32,f47])).
% 0.22/0.53  fof(f47,plain,(
% 0.22/0.53    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_xboole_0(sK3(X0)) & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f31])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f21])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.53    inference(pure_predicate_removal,[],[f8])).
% 0.22/0.53  fof(f8,axiom,(
% 0.22/0.53    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ? [X1] : (v1_zfmisc_1(X1) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc20_struct_0)).
% 0.22/0.53  fof(f269,plain,(
% 0.22/0.53    spl6_5 | ~spl6_7),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f268])).
% 0.22/0.53  fof(f268,plain,(
% 0.22/0.53    $false | (spl6_5 | ~spl6_7)),
% 0.22/0.53    inference(subsumption_resolution,[],[f267,f173])).
% 0.22/0.53  fof(f267,plain,(
% 0.22/0.53    ~v1_xboole_0(k2_struct_0(sK0)) | spl6_5),
% 0.22/0.53    inference(resolution,[],[f151,f80])).
% 0.22/0.53  fof(f80,plain,(
% 0.22/0.53    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f52])).
% 0.22/0.53  fof(f52,plain,(
% 0.22/0.53    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK4(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f50,f51])).
% 0.22/0.53  fof(f51,plain,(
% 0.22/0.53    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f50,plain,(
% 0.22/0.53    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.53    inference(rectify,[],[f49])).
% 0.22/0.53  fof(f49,plain,(
% 0.22/0.53    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.53    inference(nnf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.22/0.53  fof(f151,plain,(
% 0.22/0.53    r2_hidden(sK5(k2_struct_0(sK0),sK3(sK0)),k2_struct_0(sK0)) | spl6_5),
% 0.22/0.53    inference(resolution,[],[f145,f86])).
% 0.22/0.53  fof(f86,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK5(X0,X1),X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f58])).
% 0.22/0.53  fof(f58,plain,(
% 0.22/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f56,f57])).
% 0.22/0.53  fof(f57,plain,(
% 0.22/0.53    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f56,plain,(
% 0.22/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.53    inference(rectify,[],[f55])).
% 0.22/0.53  fof(f55,plain,(
% 0.22/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.53    inference(nnf_transformation,[],[f33])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.53  fof(f145,plain,(
% 0.22/0.53    ~r1_tarski(k2_struct_0(sK0),sK3(sK0)) | spl6_5),
% 0.22/0.53    inference(avatar_component_clause,[],[f143])).
% 0.22/0.53  fof(f143,plain,(
% 0.22/0.53    spl6_5 <=> r1_tarski(k2_struct_0(sK0),sK3(sK0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.22/0.53  fof(f244,plain,(
% 0.22/0.53    spl6_14 | ~spl6_15 | ~spl6_16 | ~spl6_17 | spl6_18),
% 0.22/0.53    inference(avatar_split_clause,[],[f224,f242,f238,f234,f230,f226])).
% 0.22/0.53  fof(f224,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_subset_1(X0,k2_struct_0(sK0)) | ~r1_waybel_7(sK0,sK1,X0) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | ~v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))) )),
% 0.22/0.53    inference(forward_demodulation,[],[f223,f134])).
% 0.22/0.53  fof(f223,plain,(
% 0.22/0.53    ( ! [X0] : (~r1_waybel_7(sK0,sK1,X0) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | ~v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f222,f60])).
% 0.22/0.53  fof(f222,plain,(
% 0.22/0.53    ( ! [X0] : (~r1_waybel_7(sK0,sK1,X0) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | ~v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(sK0)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f221,f61])).
% 0.22/0.53  fof(f221,plain,(
% 0.22/0.53    ( ! [X0] : (~r1_waybel_7(sK0,sK1,X0) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | ~v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f220,f62])).
% 0.22/0.53  fof(f220,plain,(
% 0.22/0.53    ( ! [X0] : (~r1_waybel_7(sK0,sK1,X0) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | ~v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.53    inference(superposition,[],[f76,f165])).
% 0.22/0.53  fof(f76,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r1_waybel_7(X0,k2_yellow19(X0,X1),X2) | r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f46])).
% 0.22/0.53  fof(f207,plain,(
% 0.22/0.53    spl6_7 | spl6_11),
% 0.22/0.53    inference(avatar_split_clause,[],[f203,f205,f171])).
% 0.22/0.53  fof(f203,plain,(
% 0.22/0.53    ( ! [X5] : (v4_orders_2(k3_yellow19(X5,k2_struct_0(sK0),sK1)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X5))) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(X5) | v2_struct_0(X5)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f202,f63])).
% 0.22/0.53  fof(f202,plain,(
% 0.22/0.53    ( ! [X5] : (v4_orders_2(k3_yellow19(X5,k2_struct_0(sK0),sK1)) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X5))) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(X5) | v2_struct_0(X5)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f201,f98])).
% 0.22/0.53  fof(f201,plain,(
% 0.22/0.53    ( ! [X5] : (v4_orders_2(k3_yellow19(X5,k2_struct_0(sK0),sK1)) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X5))) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(X5) | v2_struct_0(X5)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f158,f97])).
% 0.22/0.53  fof(f158,plain,(
% 0.22/0.53    ( ! [X5] : (v4_orders_2(k3_yellow19(X5,k2_struct_0(sK0),sK1)) | ~v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X5))) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(X5) | v2_struct_0(X5)) )),
% 0.22/0.53    inference(resolution,[],[f96,f101])).
% 0.22/0.53  fof(f101,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | v4_orders_2(k3_yellow19(X0,X1,X2)) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(definition_unfolding,[],[f91,f71,f71,f71])).
% 0.22/0.53  fof(f91,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (v4_orders_2(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f35])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f34])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f20])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 0.22/0.53    inference(pure_predicate_removal,[],[f17])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 0.22/0.53    inference(pure_predicate_removal,[],[f11])).
% 0.22/0.53  fof(f11,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & v4_orders_2(k3_yellow19(X0,X1,X2)) & v3_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_yellow19)).
% 0.22/0.53  fof(f200,plain,(
% 0.22/0.53    spl6_7 | spl6_8),
% 0.22/0.53    inference(avatar_split_clause,[],[f199,f175,f171])).
% 0.22/0.53  fof(f199,plain,(
% 0.22/0.53    ( ! [X4] : (~v2_struct_0(k3_yellow19(X4,k2_struct_0(sK0),sK1)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X4))) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(X4) | v2_struct_0(X4)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f198,f63])).
% 0.22/0.53  fof(f198,plain,(
% 0.22/0.53    ( ! [X4] : (~v2_struct_0(k3_yellow19(X4,k2_struct_0(sK0),sK1)) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X4))) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(X4) | v2_struct_0(X4)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f197,f98])).
% 0.22/0.53  fof(f197,plain,(
% 0.22/0.53    ( ! [X4] : (~v2_struct_0(k3_yellow19(X4,k2_struct_0(sK0),sK1)) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X4))) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(X4) | v2_struct_0(X4)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f157,f97])).
% 0.22/0.53  fof(f157,plain,(
% 0.22/0.53    ( ! [X4] : (~v2_struct_0(k3_yellow19(X4,k2_struct_0(sK0),sK1)) | ~v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X4))) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(X4) | v2_struct_0(X4)) )),
% 0.22/0.53    inference(resolution,[],[f96,f102])).
% 0.22/0.53  fof(f102,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v2_struct_0(k3_yellow19(X0,X1,X2)) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(definition_unfolding,[],[f90,f71,f71,f71])).
% 0.22/0.53  fof(f90,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~v2_struct_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f35])).
% 0.22/0.53  fof(f196,plain,(
% 0.22/0.53    spl6_7 | spl6_10),
% 0.22/0.53    inference(avatar_split_clause,[],[f192,f194,f171])).
% 0.22/0.53  fof(f192,plain,(
% 0.22/0.53    ( ! [X3] : (l1_waybel_0(k3_yellow19(X3,k2_struct_0(sK0),sK1),X3) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X3))) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(X3) | v2_struct_0(X3)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f191,f63])).
% 0.22/0.53  fof(f191,plain,(
% 0.22/0.53    ( ! [X3] : (l1_waybel_0(k3_yellow19(X3,k2_struct_0(sK0),sK1),X3) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X3))) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(X3) | v2_struct_0(X3)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f190,f98])).
% 0.22/0.53  fof(f190,plain,(
% 0.22/0.53    ( ! [X3] : (l1_waybel_0(k3_yellow19(X3,k2_struct_0(sK0),sK1),X3) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X3))) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(X3) | v2_struct_0(X3)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f156,f97])).
% 0.22/0.53  fof(f156,plain,(
% 0.22/0.53    ( ! [X3] : (l1_waybel_0(k3_yellow19(X3,k2_struct_0(sK0),sK1),X3) | ~v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X3))) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(X3) | v2_struct_0(X3)) )),
% 0.22/0.53    inference(resolution,[],[f96,f103])).
% 0.22/0.53  fof(f103,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | l1_waybel_0(k3_yellow19(X0,X1,X2),X0) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(definition_unfolding,[],[f93,f71,f71,f71])).
% 0.22/0.53  fof(f93,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f37])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f36])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f19])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 0.22/0.53    inference(pure_predicate_removal,[],[f10])).
% 0.22/0.53  fof(f10,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow19)).
% 0.22/0.53  fof(f185,plain,(
% 0.22/0.53    spl6_7 | spl6_9),
% 0.22/0.53    inference(avatar_split_clause,[],[f181,f183,f171])).
% 0.22/0.53  fof(f181,plain,(
% 0.22/0.53    ( ! [X1] : (v7_waybel_0(k3_yellow19(X1,k2_struct_0(sK0),sK1)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X1))) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(X1) | v2_struct_0(X1)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f180,f63])).
% 0.22/0.53  fof(f180,plain,(
% 0.22/0.53    ( ! [X1] : (v7_waybel_0(k3_yellow19(X1,k2_struct_0(sK0),sK1)) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X1))) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(X1) | v2_struct_0(X1)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f179,f99])).
% 0.22/0.53  fof(f179,plain,(
% 0.22/0.53    ( ! [X1] : (v7_waybel_0(k3_yellow19(X1,k2_struct_0(sK0),sK1)) | ~v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X1))) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(X1) | v2_struct_0(X1)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f178,f98])).
% 0.22/0.53  fof(f178,plain,(
% 0.22/0.53    ( ! [X1] : (v7_waybel_0(k3_yellow19(X1,k2_struct_0(sK0),sK1)) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X1))) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(X1) | v2_struct_0(X1)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f154,f97])).
% 0.22/0.53  fof(f154,plain,(
% 0.22/0.53    ( ! [X1] : (v7_waybel_0(k3_yellow19(X1,k2_struct_0(sK0),sK1)) | ~v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X1))) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(X1) | v2_struct_0(X1)) )),
% 0.22/0.53    inference(resolution,[],[f96,f105])).
% 0.22/0.53  fof(f105,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | v7_waybel_0(k3_yellow19(X0,X1,X2)) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1)))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(definition_unfolding,[],[f95,f71,f71,f71,f71])).
% 0.22/0.53  fof(f95,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (v7_waybel_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f39])).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((v7_waybel_0(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f38])).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((v7_waybel_0(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f18])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v7_waybel_0(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 0.22/0.53    inference(pure_predicate_removal,[],[f12])).
% 0.22/0.53  fof(f12,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v7_waybel_0(k3_yellow19(X0,X1,X2)) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow19)).
% 0.22/0.53  fof(f150,plain,(
% 0.22/0.53    ~spl6_5 | spl6_6 | ~spl6_3),
% 0.22/0.53    inference(avatar_split_clause,[],[f141,f121,f147,f143])).
% 0.22/0.53  fof(f121,plain,(
% 0.22/0.53    spl6_3 <=> m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.22/0.53  fof(f141,plain,(
% 0.22/0.53    k2_struct_0(sK0) = sK3(sK0) | ~r1_tarski(k2_struct_0(sK0),sK3(sK0)) | ~spl6_3),
% 0.22/0.53    inference(resolution,[],[f139,f84])).
% 0.22/0.53  fof(f84,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f54])).
% 0.22/0.53  fof(f54,plain,(
% 0.22/0.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.53    inference(flattening,[],[f53])).
% 0.22/0.53  fof(f53,plain,(
% 0.22/0.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.53    inference(nnf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.53  fof(f139,plain,(
% 0.22/0.53    r1_tarski(sK3(sK0),k2_struct_0(sK0)) | ~spl6_3),
% 0.22/0.53    inference(resolution,[],[f136,f88])).
% 0.22/0.53  fof(f88,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f59])).
% 0.22/0.53  fof(f59,plain,(
% 0.22/0.53    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.53    inference(nnf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.53  fof(f136,plain,(
% 0.22/0.53    m1_subset_1(sK3(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~spl6_3),
% 0.22/0.53    inference(backward_demodulation,[],[f123,f134])).
% 0.22/0.53  fof(f123,plain,(
% 0.22/0.53    m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_3),
% 0.22/0.53    inference(avatar_component_clause,[],[f121])).
% 0.22/0.53  fof(f131,plain,(
% 0.22/0.53    spl6_4),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f130])).
% 0.22/0.53  fof(f130,plain,(
% 0.22/0.53    $false | spl6_4),
% 0.22/0.53    inference(subsumption_resolution,[],[f129,f127])).
% 0.22/0.53  fof(f127,plain,(
% 0.22/0.53    ~l1_struct_0(sK0) | spl6_4),
% 0.22/0.53    inference(avatar_component_clause,[],[f125])).
% 0.22/0.53  fof(f125,plain,(
% 0.22/0.53    spl6_4 <=> l1_struct_0(sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.22/0.53  fof(f128,plain,(
% 0.22/0.53    spl6_3 | ~spl6_4),
% 0.22/0.53    inference(avatar_split_clause,[],[f119,f125,f121])).
% 0.22/0.53  fof(f119,plain,(
% 0.22/0.53    ~l1_struct_0(sK0) | m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.53    inference(resolution,[],[f60,f78])).
% 0.22/0.53  fof(f78,plain,(
% 0.22/0.53    ( ! [X0] : (v2_struct_0(X0) | ~l1_struct_0(X0) | m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f48])).
% 0.22/0.53  fof(f118,plain,(
% 0.22/0.53    spl6_1 | spl6_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f69,f114,f110])).
% 0.22/0.53  fof(f69,plain,(
% 0.22/0.53    r1_waybel_7(sK0,sK1,sK2) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)),
% 0.22/0.53    inference(cnf_transformation,[],[f45])).
% 0.22/0.53  fof(f117,plain,(
% 0.22/0.53    ~spl6_1 | ~spl6_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f70,f114,f110])).
% 0.22/0.53  fof(f70,plain,(
% 0.22/0.53    ~r1_waybel_7(sK0,sK1,sK2) | ~r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)),
% 0.22/0.53    inference(cnf_transformation,[],[f45])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (6832)------------------------------
% 0.22/0.53  % (6832)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (6832)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (6832)Memory used [KB]: 10874
% 0.22/0.53  % (6832)Time elapsed: 0.121 s
% 0.22/0.53  % (6832)------------------------------
% 0.22/0.53  % (6832)------------------------------
% 0.22/0.53  % (6824)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.53  % (6838)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.53  % (6823)Success in time 0.169 s
%------------------------------------------------------------------------------
