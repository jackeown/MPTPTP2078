%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:53 EST 2020

% Result     : Theorem 1.48s
% Output     : Refutation 1.48s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 929 expanded)
%              Number of leaves         :   19 ( 238 expanded)
%              Depth                    :   21
%              Number of atoms          :  492 (5119 expanded)
%              Number of equality atoms :   25 ( 139 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1077,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f88,f91,f173,f507,f825,f943,f1076])).

fof(f1076,plain,
    ( spl2_2
    | ~ spl2_4
    | ~ spl2_7 ),
    inference(avatar_contradiction_clause,[],[f1075])).

fof(f1075,plain,
    ( $false
    | spl2_2
    | ~ spl2_4
    | ~ spl2_7 ),
    inference(subsumption_resolution,[],[f1074,f78])).

fof(f78,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl2_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f1074,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_4
    | ~ spl2_7 ),
    inference(forward_demodulation,[],[f1073,f978])).

fof(f978,plain,
    ( sK1 = u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f974,f101])).

fof(f101,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(resolution,[],[f95,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(f95,plain,(
    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(resolution,[],[f50,f43])).

fof(f43,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
      | ~ v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_compts_1(sK1,sK0) )
    & ( ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
        & v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
      | ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        & v2_compts_1(sK1,sK0) ) )
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f37,f39,f38])).

fof(f38,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              | ~ v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v2_compts_1(X1,X0) )
            & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
                & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
              | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
                & v2_compts_1(X1,X0) ) ) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
            | ~ v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
            | ~ v2_compts_1(X1,sK0) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
              & v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
            | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
              & v2_compts_1(X1,sK0) ) ) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X1] :
        ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
          | ~ v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
          | ~ v2_compts_1(X1,sK0) )
        & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
            & v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
          | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
            & v2_compts_1(X1,sK0) ) ) )
   => ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
        | ~ v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_compts_1(sK1,sK0) )
      & ( ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
          & v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
        | ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
          & v2_compts_1(sK1,sK0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            | ~ v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v2_compts_1(X1,X0) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v2_compts_1(X1,X0) ) ) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            | ~ v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v2_compts_1(X1,X0) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v2_compts_1(X1,X0) ) ) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v2_compts_1(X1,X0) )
        <~> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v2_compts_1(X1,X0) )
          <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f17,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v2_compts_1(X1,X0) )
          <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v2_compts_1(X1,X0) )
          <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v2_compts_1(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_compts_1)).

fof(f50,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f974,plain,
    ( sK1 = u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_4 ),
    inference(resolution,[],[f85,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_pre_topc)).

fof(f85,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl2_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f1073,plain,
    ( m1_subset_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_4
    | ~ spl2_7 ),
    inference(subsumption_resolution,[],[f1070,f43])).

fof(f1070,plain,
    ( m1_subset_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_4
    | ~ spl2_7 ),
    inference(resolution,[],[f1053,f164])).

fof(f164,plain,(
    ! [X12,X13] :
      ( ~ m1_pre_topc(X12,X13)
      | m1_subset_1(u1_struct_0(X12),k1_zfmisc_1(u1_struct_0(X13)))
      | ~ l1_pre_topc(X13) ) ),
    inference(resolution,[],[f99,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).

fof(f99,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f98,f94])).

fof(f94,plain,(
    ! [X0] : k8_setfam_1(X0,k1_xboole_0) = X0 ),
    inference(subsumption_resolution,[],[f70,f49])).

fof(f49,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f70,plain,(
    ! [X0] :
      ( k8_setfam_1(X0,k1_xboole_0) = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ( k8_setfam_1(X0,X1) = X0
          | k1_xboole_0 != X1 )
        & ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
          | k1_xboole_0 = X1 ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ( k1_xboole_0 = X1
         => k8_setfam_1(X0,X1) = X0 )
        & ( k1_xboole_0 != X1
         => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).

fof(f98,plain,(
    ! [X0] : m1_subset_1(k8_setfam_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f59,f49])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_setfam_1)).

fof(f1053,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK0)
    | ~ spl2_4
    | ~ spl2_7 ),
    inference(subsumption_resolution,[],[f1052,f139])).

fof(f139,plain,
    ( l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl2_7
  <=> l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f1052,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK0)
    | ~ l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f1048,f43])).

fof(f1048,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))
    | ~ spl2_4 ),
    inference(resolution,[],[f980,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

fof(f980,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f975,f101])).

fof(f975,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_4 ),
    inference(resolution,[],[f85,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_pre_topc)).

fof(f943,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_contradiction_clause,[],[f942])).

fof(f942,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f941,f101])).

fof(f941,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f940,f826])).

fof(f826,plain,
    ( ~ v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(global_subsumption,[],[f48,f77,f73,f505])).

fof(f505,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f504,f339])).

fof(f339,plain,
    ( sK1 = u1_struct_0(k1_pre_topc(sK0,sK1))
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f335,f43])).

fof(f335,plain,
    ( sK1 = u1_struct_0(k1_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_2 ),
    inference(resolution,[],[f77,f58])).

fof(f504,plain,
    ( m1_subset_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f498,f101])).

fof(f498,plain,
    ( m1_subset_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_2 ),
    inference(resolution,[],[f164,f360])).

fof(f360,plain,
    ( m1_pre_topc(k1_pre_topc(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f359,f358])).

fof(f358,plain,
    ( l1_pre_topc(k1_pre_topc(sK0,sK1))
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f354,f43])).

fof(f354,plain,
    ( l1_pre_topc(k1_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_2 ),
    inference(resolution,[],[f340,f54])).

fof(f54,plain,(
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

fof(f340,plain,
    ( m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f336,f43])).

fof(f336,plain,
    ( m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl2_2 ),
    inference(resolution,[],[f77,f67])).

fof(f359,plain,
    ( m1_pre_topc(k1_pre_topc(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(k1_pre_topc(sK0,sK1))
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f353,f43])).

fof(f353,plain,
    ( m1_pre_topc(k1_pre_topc(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(k1_pre_topc(sK0,sK1))
    | ~ spl2_2 ),
    inference(resolution,[],[f340,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,X1)
      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f73,plain,
    ( v2_compts_1(sK1,sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl2_1
  <=> v2_compts_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f77,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f76])).

fof(f48,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_compts_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f940,plain,
    ( v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(resolution,[],[f870,f360])).

fof(f870,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(k1_pre_topc(sK0,sK1),X1)
        | v2_compts_1(sK1,X1)
        | ~ l1_pre_topc(X1) )
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f526,f851])).

fof(f851,plain,
    ( v2_compts_1(sK1,k1_pre_topc(sK0,sK1))
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f850,f340])).

fof(f850,plain,
    ( v2_compts_1(sK1,k1_pre_topc(sK0,sK1))
    | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f843,f99])).

fof(f843,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | v2_compts_1(sK1,k1_pre_topc(sK0,sK1))
    | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(superposition,[],[f839,f339])).

fof(f839,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | v2_compts_1(sK1,X0)
        | ~ m1_pre_topc(X0,sK0) )
    | ~ spl2_1 ),
    inference(subsumption_resolution,[],[f838,f43])).

fof(f838,plain,
    ( ! [X0] :
        ( v2_compts_1(sK1,X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(X0,sK0)
        | ~ l1_pre_topc(sK0) )
    | ~ spl2_1 ),
    inference(resolution,[],[f73,f93])).

fof(f93,plain,(
    ! [X0,X3,X1] :
      ( ~ v2_compts_1(X3,X0)
      | v2_compts_1(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f69,f55])).

fof(f69,plain,(
    ! [X0,X3,X1] :
      ( v2_compts_1(X3,X1)
      | ~ v2_compts_1(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_compts_1(X3,X1)
      | ~ v2_compts_1(X2,X0)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v2_compts_1(X2,X0)
                      | ~ v2_compts_1(X3,X1) )
                    & ( v2_compts_1(X3,X1)
                      | ~ v2_compts_1(X2,X0) ) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v2_compts_1(X2,X0)
                  <=> v2_compts_1(X3,X1) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v2_compts_1(X2,X0)
                  <=> v2_compts_1(X3,X1) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( X2 = X3
                   => ( v2_compts_1(X2,X0)
                    <=> v2_compts_1(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_compts_1)).

fof(f526,plain,
    ( ! [X1] :
        ( ~ v2_compts_1(sK1,k1_pre_topc(sK0,sK1))
        | v2_compts_1(sK1,X1)
        | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),X1)
        | ~ l1_pre_topc(X1) )
    | ~ spl2_2 ),
    inference(superposition,[],[f163,f339])).

fof(f163,plain,(
    ! [X10,X11] :
      ( ~ v2_compts_1(u1_struct_0(X10),X10)
      | v2_compts_1(u1_struct_0(X10),X11)
      | ~ m1_pre_topc(X10,X11)
      | ~ l1_pre_topc(X11) ) ),
    inference(resolution,[],[f99,f92])).

fof(f92,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_compts_1(X3,X1)
      | v2_compts_1(X3,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f68,f55])).

fof(f68,plain,(
    ! [X0,X3,X1] :
      ( v2_compts_1(X3,X0)
      | ~ v2_compts_1(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_compts_1(X2,X0)
      | ~ v2_compts_1(X3,X1)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f825,plain,
    ( ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_contradiction_clause,[],[f824])).

fof(f824,plain,
    ( $false
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f823,f43])).

fof(f823,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f821,f512])).

fof(f512,plain,
    ( ~ v2_compts_1(sK1,sK0)
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(global_subsumption,[],[f48,f85,f81,f77])).

fof(f81,plain,
    ( v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl2_3
  <=> v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f821,plain,
    ( v2_compts_1(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(resolution,[],[f528,f340])).

fof(f528,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(k1_pre_topc(sK0,sK1),X1)
        | v2_compts_1(sK1,X1)
        | ~ l1_pre_topc(X1) )
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f526,f511])).

fof(f511,plain,
    ( v2_compts_1(sK1,k1_pre_topc(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f510,f99])).

fof(f510,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | v2_compts_1(sK1,k1_pre_topc(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(forward_demodulation,[],[f401,f339])).

fof(f401,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))
    | v2_compts_1(sK1,k1_pre_topc(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(resolution,[],[f360,f134])).

fof(f134,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | v2_compts_1(sK1,X0) )
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f133,f101])).

fof(f133,plain,
    ( ! [X0] :
        ( v2_compts_1(sK1,X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
    | ~ spl2_3 ),
    inference(resolution,[],[f93,f81])).

fof(f507,plain,
    ( ~ spl2_2
    | spl2_4 ),
    inference(avatar_contradiction_clause,[],[f506])).

fof(f506,plain,
    ( $false
    | ~ spl2_2
    | spl2_4 ),
    inference(subsumption_resolution,[],[f505,f86])).

fof(f86,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | spl2_4 ),
    inference(avatar_component_clause,[],[f84])).

fof(f173,plain,
    ( ~ spl2_4
    | spl2_7 ),
    inference(avatar_contradiction_clause,[],[f172])).

fof(f172,plain,
    ( $false
    | ~ spl2_4
    | spl2_7 ),
    inference(subsumption_resolution,[],[f171,f101])).

fof(f171,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_4
    | spl2_7 ),
    inference(subsumption_resolution,[],[f170,f140])).

fof(f140,plain,
    ( ~ l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))
    | spl2_7 ),
    inference(avatar_component_clause,[],[f138])).

fof(f170,plain,
    ( l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_4 ),
    inference(resolution,[],[f108,f54])).

fof(f108,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f106,f101])).

fof(f106,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_4 ),
    inference(resolution,[],[f67,f85])).

fof(f91,plain,
    ( spl2_1
    | spl2_3 ),
    inference(avatar_split_clause,[],[f44,f80,f72])).

fof(f44,plain,
    ( v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v2_compts_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f88,plain,
    ( spl2_2
    | spl2_4 ),
    inference(avatar_split_clause,[],[f47,f84,f76])).

fof(f47,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n020.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 15:55:37 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.50  % (1151)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.50  % (1153)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.50  % (1171)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.50  % (1154)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.51  % (1159)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.51  % (1166)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.51  % (1169)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.51  % (1163)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.51  % (1152)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.51  % (1170)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.51  % (1172)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.51  % (1150)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (1155)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.52  % (1154)Refutation not found, incomplete strategy% (1154)------------------------------
% 0.22/0.52  % (1154)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (1150)Refutation not found, incomplete strategy% (1150)------------------------------
% 0.22/0.52  % (1150)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (1150)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  % (1154)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  
% 0.22/0.52  % (1150)Memory used [KB]: 10618
% 0.22/0.52  % (1154)Memory used [KB]: 6268
% 0.22/0.52  % (1150)Time elapsed: 0.100 s
% 0.22/0.52  % (1154)Time elapsed: 0.097 s
% 0.22/0.52  % (1150)------------------------------
% 0.22/0.52  % (1150)------------------------------
% 0.22/0.52  % (1154)------------------------------
% 0.22/0.52  % (1154)------------------------------
% 0.22/0.52  % (1161)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.52  % (1158)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.52  % (1156)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.52  % (1149)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.52  % (1162)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.24/0.53  % (1174)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.24/0.53  % (1167)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.24/0.53  % (1164)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.24/0.53  % (1160)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.24/0.54  % (1149)Refutation not found, incomplete strategy% (1149)------------------------------
% 1.24/0.54  % (1149)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.54  % (1149)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.54  
% 1.24/0.54  % (1149)Memory used [KB]: 10618
% 1.24/0.54  % (1149)Time elapsed: 0.115 s
% 1.24/0.54  % (1149)------------------------------
% 1.24/0.54  % (1149)------------------------------
% 1.24/0.54  % (1168)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.24/0.54  % (1155)Refutation not found, incomplete strategy% (1155)------------------------------
% 1.24/0.54  % (1155)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.54  % (1155)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.54  
% 1.24/0.54  % (1155)Memory used [KB]: 10746
% 1.24/0.54  % (1155)Time elapsed: 0.131 s
% 1.24/0.54  % (1155)------------------------------
% 1.24/0.54  % (1155)------------------------------
% 1.24/0.54  % (1173)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.48/0.55  % (1165)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.48/0.56  % (1159)Refutation found. Thanks to Tanya!
% 1.48/0.56  % SZS status Theorem for theBenchmark
% 1.48/0.56  % SZS output start Proof for theBenchmark
% 1.48/0.56  fof(f1077,plain,(
% 1.48/0.56    $false),
% 1.48/0.56    inference(avatar_sat_refutation,[],[f88,f91,f173,f507,f825,f943,f1076])).
% 1.48/0.56  fof(f1076,plain,(
% 1.48/0.56    spl2_2 | ~spl2_4 | ~spl2_7),
% 1.48/0.56    inference(avatar_contradiction_clause,[],[f1075])).
% 1.48/0.56  fof(f1075,plain,(
% 1.48/0.56    $false | (spl2_2 | ~spl2_4 | ~spl2_7)),
% 1.48/0.56    inference(subsumption_resolution,[],[f1074,f78])).
% 1.48/0.56  fof(f78,plain,(
% 1.48/0.56    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl2_2),
% 1.48/0.56    inference(avatar_component_clause,[],[f76])).
% 1.48/0.56  fof(f76,plain,(
% 1.48/0.56    spl2_2 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.48/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 1.48/0.56  fof(f1074,plain,(
% 1.48/0.56    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_4 | ~spl2_7)),
% 1.48/0.56    inference(forward_demodulation,[],[f1073,f978])).
% 1.48/0.56  fof(f978,plain,(
% 1.48/0.56    sK1 = u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) | ~spl2_4),
% 1.48/0.56    inference(subsumption_resolution,[],[f974,f101])).
% 1.48/0.56  fof(f101,plain,(
% 1.48/0.56    l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 1.48/0.56    inference(resolution,[],[f95,f61])).
% 1.48/0.56  fof(f61,plain,(
% 1.48/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | l1_pre_topc(g1_pre_topc(X0,X1))) )),
% 1.48/0.56    inference(cnf_transformation,[],[f31])).
% 1.48/0.56  fof(f31,plain,(
% 1.48/0.56    ! [X0,X1] : ((l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.48/0.56    inference(ennf_transformation,[],[f6])).
% 1.48/0.56  fof(f6,axiom,(
% 1.48/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 1.48/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).
% 1.48/0.56  fof(f95,plain,(
% 1.48/0.56    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.48/0.56    inference(resolution,[],[f50,f43])).
% 1.48/0.56  fof(f43,plain,(
% 1.48/0.56    l1_pre_topc(sK0)),
% 1.48/0.56    inference(cnf_transformation,[],[f40])).
% 1.48/0.56  fof(f40,plain,(
% 1.48/0.56    ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | ~v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_compts_1(sK1,sK0)) & ((m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) & v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | (m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & v2_compts_1(sK1,sK0)))) & l1_pre_topc(sK0)),
% 1.48/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f37,f39,f38])).
% 1.48/0.56  fof(f38,plain,(
% 1.48/0.56    ? [X0] : (? [X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_compts_1(X1,X0)) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)))) & l1_pre_topc(X0)) => (? [X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | ~v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_compts_1(X1,sK0)) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & v2_compts_1(X1,sK0)))) & l1_pre_topc(sK0))),
% 1.48/0.56    introduced(choice_axiom,[])).
% 1.48/0.56  fof(f39,plain,(
% 1.48/0.56    ? [X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | ~v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_compts_1(X1,sK0)) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & v2_compts_1(X1,sK0)))) => ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | ~v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_compts_1(sK1,sK0)) & ((m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) & v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | (m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & v2_compts_1(sK1,sK0))))),
% 1.48/0.56    introduced(choice_axiom,[])).
% 1.48/0.56  fof(f37,plain,(
% 1.48/0.56    ? [X0] : (? [X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_compts_1(X1,X0)) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)))) & l1_pre_topc(X0))),
% 1.48/0.56    inference(flattening,[],[f36])).
% 1.48/0.56  fof(f36,plain,(
% 1.48/0.56    ? [X0] : (? [X1] : (((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_compts_1(X1,X0))) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)))) & l1_pre_topc(X0))),
% 1.48/0.56    inference(nnf_transformation,[],[f20])).
% 1.48/0.56  fof(f20,plain,(
% 1.48/0.56    ? [X0] : (? [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)) <~> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & l1_pre_topc(X0))),
% 1.48/0.56    inference(ennf_transformation,[],[f18])).
% 1.48/0.56  fof(f18,plain,(
% 1.48/0.56    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 1.48/0.56    inference(pure_predicate_removal,[],[f17])).
% 1.48/0.56  fof(f17,plain,(
% 1.48/0.56    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 1.48/0.56    inference(pure_predicate_removal,[],[f16])).
% 1.48/0.56  fof(f16,negated_conjecture,(
% 1.48/0.56    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 1.48/0.56    inference(negated_conjecture,[],[f15])).
% 1.48/0.56  fof(f15,conjecture,(
% 1.48/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 1.48/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_compts_1)).
% 1.48/0.56  fof(f50,plain,(
% 1.48/0.56    ( ! [X0] : (~l1_pre_topc(X0) | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) )),
% 1.48/0.56    inference(cnf_transformation,[],[f21])).
% 1.48/0.56  fof(f21,plain,(
% 1.48/0.56    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.48/0.56    inference(ennf_transformation,[],[f9])).
% 1.48/0.56  fof(f9,axiom,(
% 1.48/0.56    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.48/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 1.48/0.56  fof(f974,plain,(
% 1.48/0.56    sK1 = u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl2_4),
% 1.48/0.56    inference(resolution,[],[f85,f58])).
% 1.48/0.56  fof(f58,plain,(
% 1.48/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~l1_pre_topc(X0)) )),
% 1.48/0.56    inference(cnf_transformation,[],[f29])).
% 1.48/0.56  fof(f29,plain,(
% 1.48/0.56    ! [X0] : (! [X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.48/0.56    inference(ennf_transformation,[],[f11])).
% 1.48/0.56  fof(f11,axiom,(
% 1.48/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => u1_struct_0(k1_pre_topc(X0,X1)) = X1))),
% 1.48/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_pre_topc)).
% 1.48/0.56  fof(f85,plain,(
% 1.48/0.56    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | ~spl2_4),
% 1.48/0.56    inference(avatar_component_clause,[],[f84])).
% 1.48/0.56  fof(f84,plain,(
% 1.48/0.56    spl2_4 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))),
% 1.48/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 1.48/0.56  fof(f1073,plain,(
% 1.48/0.56    m1_subset_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_4 | ~spl2_7)),
% 1.48/0.56    inference(subsumption_resolution,[],[f1070,f43])).
% 1.48/0.56  fof(f1070,plain,(
% 1.48/0.56    m1_subset_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl2_4 | ~spl2_7)),
% 1.48/0.56    inference(resolution,[],[f1053,f164])).
% 1.48/0.56  fof(f164,plain,(
% 1.48/0.56    ( ! [X12,X13] : (~m1_pre_topc(X12,X13) | m1_subset_1(u1_struct_0(X12),k1_zfmisc_1(u1_struct_0(X13))) | ~l1_pre_topc(X13)) )),
% 1.48/0.56    inference(resolution,[],[f99,f55])).
% 1.48/0.56  fof(f55,plain,(
% 1.48/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.48/0.56    inference(cnf_transformation,[],[f26])).
% 1.48/0.56  fof(f26,plain,(
% 1.48/0.56    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.48/0.56    inference(ennf_transformation,[],[f12])).
% 1.48/0.56  fof(f12,axiom,(
% 1.48/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))))),
% 1.48/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).
% 1.48/0.56  fof(f99,plain,(
% 1.48/0.56    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.48/0.56    inference(forward_demodulation,[],[f98,f94])).
% 1.48/0.56  fof(f94,plain,(
% 1.48/0.56    ( ! [X0] : (k8_setfam_1(X0,k1_xboole_0) = X0) )),
% 1.48/0.56    inference(subsumption_resolution,[],[f70,f49])).
% 1.48/0.56  fof(f49,plain,(
% 1.48/0.56    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.48/0.56    inference(cnf_transformation,[],[f1])).
% 1.48/0.56  fof(f1,axiom,(
% 1.48/0.56    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.48/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 1.48/0.56  fof(f70,plain,(
% 1.48/0.56    ( ! [X0] : (k8_setfam_1(X0,k1_xboole_0) = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.48/0.56    inference(equality_resolution,[],[f63])).
% 1.48/0.56  fof(f63,plain,(
% 1.48/0.56    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.48/0.56    inference(cnf_transformation,[],[f32])).
% 1.48/0.56  fof(f32,plain,(
% 1.48/0.56    ! [X0,X1] : (((k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1) & (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.48/0.56    inference(ennf_transformation,[],[f2])).
% 1.48/0.56  fof(f2,axiom,(
% 1.48/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ((k1_xboole_0 = X1 => k8_setfam_1(X0,X1) = X0) & (k1_xboole_0 != X1 => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1))))),
% 1.48/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).
% 1.48/0.56  fof(f98,plain,(
% 1.48/0.56    ( ! [X0] : (m1_subset_1(k8_setfam_1(X0,k1_xboole_0),k1_zfmisc_1(X0))) )),
% 1.48/0.56    inference(resolution,[],[f59,f49])).
% 1.48/0.56  fof(f59,plain,(
% 1.48/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))) )),
% 1.48/0.56    inference(cnf_transformation,[],[f30])).
% 1.48/0.56  fof(f30,plain,(
% 1.48/0.56    ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.48/0.56    inference(ennf_transformation,[],[f3])).
% 1.48/0.56  fof(f3,axiom,(
% 1.48/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.48/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_setfam_1)).
% 1.48/0.56  fof(f1053,plain,(
% 1.48/0.56    m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK0) | (~spl2_4 | ~spl2_7)),
% 1.48/0.56    inference(subsumption_resolution,[],[f1052,f139])).
% 1.48/0.56  fof(f139,plain,(
% 1.48/0.56    l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) | ~spl2_7),
% 1.48/0.56    inference(avatar_component_clause,[],[f138])).
% 1.48/0.56  fof(f138,plain,(
% 1.48/0.56    spl2_7 <=> l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))),
% 1.48/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 1.48/0.56  fof(f1052,plain,(
% 1.48/0.56    m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK0) | ~l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) | ~spl2_4),
% 1.48/0.56    inference(subsumption_resolution,[],[f1048,f43])).
% 1.48/0.56  fof(f1048,plain,(
% 1.48/0.56    m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK0) | ~l1_pre_topc(sK0) | ~l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) | ~spl2_4),
% 1.48/0.56    inference(resolution,[],[f980,f53])).
% 1.48/0.56  fof(f53,plain,(
% 1.48/0.56    ( ! [X0,X1] : (~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 1.48/0.56    inference(cnf_transformation,[],[f41])).
% 1.48/0.56  fof(f41,plain,(
% 1.48/0.56    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.48/0.56    inference(nnf_transformation,[],[f24])).
% 1.48/0.56  fof(f24,plain,(
% 1.48/0.56    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.48/0.56    inference(ennf_transformation,[],[f13])).
% 1.48/0.56  fof(f13,axiom,(
% 1.48/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 1.48/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).
% 1.48/0.56  fof(f980,plain,(
% 1.48/0.56    m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl2_4),
% 1.48/0.56    inference(subsumption_resolution,[],[f975,f101])).
% 1.48/0.56  fof(f975,plain,(
% 1.48/0.56    m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl2_4),
% 1.48/0.56    inference(resolution,[],[f85,f67])).
% 1.48/0.56  fof(f67,plain,(
% 1.48/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~l1_pre_topc(X0)) )),
% 1.48/0.56    inference(cnf_transformation,[],[f35])).
% 1.48/0.56  fof(f35,plain,(
% 1.48/0.56    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.48/0.56    inference(flattening,[],[f34])).
% 1.48/0.56  fof(f34,plain,(
% 1.48/0.56    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.48/0.56    inference(ennf_transformation,[],[f7])).
% 1.48/0.56  fof(f7,axiom,(
% 1.48/0.56    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => (m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))))),
% 1.48/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_pre_topc)).
% 1.48/0.56  fof(f943,plain,(
% 1.48/0.56    ~spl2_1 | ~spl2_2),
% 1.48/0.56    inference(avatar_contradiction_clause,[],[f942])).
% 1.48/0.56  fof(f942,plain,(
% 1.48/0.56    $false | (~spl2_1 | ~spl2_2)),
% 1.48/0.56    inference(subsumption_resolution,[],[f941,f101])).
% 1.48/0.56  fof(f941,plain,(
% 1.48/0.56    ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl2_1 | ~spl2_2)),
% 1.48/0.56    inference(subsumption_resolution,[],[f940,f826])).
% 1.48/0.56  fof(f826,plain,(
% 1.48/0.56    ~v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl2_1 | ~spl2_2)),
% 1.48/0.56    inference(global_subsumption,[],[f48,f77,f73,f505])).
% 1.48/0.56  fof(f505,plain,(
% 1.48/0.56    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | ~spl2_2),
% 1.48/0.56    inference(forward_demodulation,[],[f504,f339])).
% 1.48/0.56  fof(f339,plain,(
% 1.48/0.56    sK1 = u1_struct_0(k1_pre_topc(sK0,sK1)) | ~spl2_2),
% 1.48/0.56    inference(subsumption_resolution,[],[f335,f43])).
% 1.48/0.56  fof(f335,plain,(
% 1.48/0.56    sK1 = u1_struct_0(k1_pre_topc(sK0,sK1)) | ~l1_pre_topc(sK0) | ~spl2_2),
% 1.48/0.56    inference(resolution,[],[f77,f58])).
% 1.48/0.56  fof(f504,plain,(
% 1.48/0.56    m1_subset_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | ~spl2_2),
% 1.48/0.56    inference(subsumption_resolution,[],[f498,f101])).
% 1.48/0.56  fof(f498,plain,(
% 1.48/0.56    m1_subset_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl2_2),
% 1.48/0.56    inference(resolution,[],[f164,f360])).
% 1.48/0.56  fof(f360,plain,(
% 1.48/0.56    m1_pre_topc(k1_pre_topc(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl2_2),
% 1.48/0.56    inference(subsumption_resolution,[],[f359,f358])).
% 1.48/0.56  fof(f358,plain,(
% 1.48/0.56    l1_pre_topc(k1_pre_topc(sK0,sK1)) | ~spl2_2),
% 1.48/0.56    inference(subsumption_resolution,[],[f354,f43])).
% 1.48/0.56  fof(f354,plain,(
% 1.48/0.56    l1_pre_topc(k1_pre_topc(sK0,sK1)) | ~l1_pre_topc(sK0) | ~spl2_2),
% 1.48/0.56    inference(resolution,[],[f340,f54])).
% 1.48/0.56  fof(f54,plain,(
% 1.48/0.56    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 1.48/0.56    inference(cnf_transformation,[],[f25])).
% 1.48/0.56  fof(f25,plain,(
% 1.48/0.56    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.48/0.56    inference(ennf_transformation,[],[f8])).
% 1.48/0.56  fof(f8,axiom,(
% 1.48/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.48/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.48/0.56  fof(f340,plain,(
% 1.48/0.56    m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) | ~spl2_2),
% 1.48/0.56    inference(subsumption_resolution,[],[f336,f43])).
% 1.48/0.56  fof(f336,plain,(
% 1.48/0.56    m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | ~spl2_2),
% 1.48/0.56    inference(resolution,[],[f77,f67])).
% 1.48/0.56  fof(f359,plain,(
% 1.48/0.56    m1_pre_topc(k1_pre_topc(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(k1_pre_topc(sK0,sK1)) | ~spl2_2),
% 1.48/0.56    inference(subsumption_resolution,[],[f353,f43])).
% 1.48/0.56  fof(f353,plain,(
% 1.48/0.56    m1_pre_topc(k1_pre_topc(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(sK0) | ~l1_pre_topc(k1_pre_topc(sK0,sK1)) | ~spl2_2),
% 1.48/0.56    inference(resolution,[],[f340,f52])).
% 1.48/0.56  fof(f52,plain,(
% 1.48/0.56    ( ! [X0,X1] : (~m1_pre_topc(X0,X1) | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 1.48/0.56    inference(cnf_transformation,[],[f41])).
% 1.48/0.56  fof(f73,plain,(
% 1.48/0.56    v2_compts_1(sK1,sK0) | ~spl2_1),
% 1.48/0.56    inference(avatar_component_clause,[],[f72])).
% 1.48/0.56  fof(f72,plain,(
% 1.48/0.56    spl2_1 <=> v2_compts_1(sK1,sK0)),
% 1.48/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.48/0.56  fof(f77,plain,(
% 1.48/0.56    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_2),
% 1.48/0.56    inference(avatar_component_clause,[],[f76])).
% 1.48/0.56  fof(f48,plain,(
% 1.48/0.56    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | ~v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_compts_1(sK1,sK0)),
% 1.48/0.56    inference(cnf_transformation,[],[f40])).
% 1.48/0.56  fof(f940,plain,(
% 1.48/0.56    v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl2_1 | ~spl2_2)),
% 1.48/0.56    inference(resolution,[],[f870,f360])).
% 1.48/0.56  fof(f870,plain,(
% 1.48/0.56    ( ! [X1] : (~m1_pre_topc(k1_pre_topc(sK0,sK1),X1) | v2_compts_1(sK1,X1) | ~l1_pre_topc(X1)) ) | (~spl2_1 | ~spl2_2)),
% 1.48/0.56    inference(subsumption_resolution,[],[f526,f851])).
% 1.48/0.56  fof(f851,plain,(
% 1.48/0.56    v2_compts_1(sK1,k1_pre_topc(sK0,sK1)) | (~spl2_1 | ~spl2_2)),
% 1.48/0.56    inference(subsumption_resolution,[],[f850,f340])).
% 1.48/0.56  fof(f850,plain,(
% 1.48/0.56    v2_compts_1(sK1,k1_pre_topc(sK0,sK1)) | ~m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) | (~spl2_1 | ~spl2_2)),
% 1.48/0.56    inference(subsumption_resolution,[],[f843,f99])).
% 1.48/0.56  fof(f843,plain,(
% 1.48/0.56    ~m1_subset_1(sK1,k1_zfmisc_1(sK1)) | v2_compts_1(sK1,k1_pre_topc(sK0,sK1)) | ~m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) | (~spl2_1 | ~spl2_2)),
% 1.48/0.56    inference(superposition,[],[f839,f339])).
% 1.48/0.56  fof(f839,plain,(
% 1.48/0.56    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | v2_compts_1(sK1,X0) | ~m1_pre_topc(X0,sK0)) ) | ~spl2_1),
% 1.48/0.56    inference(subsumption_resolution,[],[f838,f43])).
% 1.48/0.56  fof(f838,plain,(
% 1.48/0.56    ( ! [X0] : (v2_compts_1(sK1,X0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X0,sK0) | ~l1_pre_topc(sK0)) ) | ~spl2_1),
% 1.48/0.56    inference(resolution,[],[f73,f93])).
% 1.48/0.56  fof(f93,plain,(
% 1.48/0.56    ( ! [X0,X3,X1] : (~v2_compts_1(X3,X0) | v2_compts_1(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.48/0.56    inference(subsumption_resolution,[],[f69,f55])).
% 1.48/0.56  fof(f69,plain,(
% 1.48/0.56    ( ! [X0,X3,X1] : (v2_compts_1(X3,X1) | ~v2_compts_1(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.48/0.56    inference(equality_resolution,[],[f56])).
% 1.48/0.56  fof(f56,plain,(
% 1.48/0.56    ( ! [X2,X0,X3,X1] : (v2_compts_1(X3,X1) | ~v2_compts_1(X2,X0) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.48/0.56    inference(cnf_transformation,[],[f42])).
% 1.48/0.56  fof(f42,plain,(
% 1.48/0.56    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v2_compts_1(X2,X0) | ~v2_compts_1(X3,X1)) & (v2_compts_1(X3,X1) | ~v2_compts_1(X2,X0))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.48/0.56    inference(nnf_transformation,[],[f28])).
% 1.48/0.56  fof(f28,plain,(
% 1.48/0.56    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v2_compts_1(X2,X0) <=> v2_compts_1(X3,X1)) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.48/0.56    inference(flattening,[],[f27])).
% 1.48/0.56  fof(f27,plain,(
% 1.48/0.56    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v2_compts_1(X2,X0) <=> v2_compts_1(X3,X1)) | X2 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.48/0.56    inference(ennf_transformation,[],[f14])).
% 1.48/0.56  fof(f14,axiom,(
% 1.48/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (X2 = X3 => (v2_compts_1(X2,X0) <=> v2_compts_1(X3,X1)))))))),
% 1.48/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_compts_1)).
% 1.48/0.56  fof(f526,plain,(
% 1.48/0.56    ( ! [X1] : (~v2_compts_1(sK1,k1_pre_topc(sK0,sK1)) | v2_compts_1(sK1,X1) | ~m1_pre_topc(k1_pre_topc(sK0,sK1),X1) | ~l1_pre_topc(X1)) ) | ~spl2_2),
% 1.48/0.56    inference(superposition,[],[f163,f339])).
% 1.48/0.56  fof(f163,plain,(
% 1.48/0.56    ( ! [X10,X11] : (~v2_compts_1(u1_struct_0(X10),X10) | v2_compts_1(u1_struct_0(X10),X11) | ~m1_pre_topc(X10,X11) | ~l1_pre_topc(X11)) )),
% 1.48/0.56    inference(resolution,[],[f99,f92])).
% 1.48/0.56  fof(f92,plain,(
% 1.48/0.56    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~v2_compts_1(X3,X1) | v2_compts_1(X3,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.48/0.56    inference(subsumption_resolution,[],[f68,f55])).
% 1.48/0.56  fof(f68,plain,(
% 1.48/0.56    ( ! [X0,X3,X1] : (v2_compts_1(X3,X0) | ~v2_compts_1(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.48/0.56    inference(equality_resolution,[],[f57])).
% 1.48/0.56  fof(f57,plain,(
% 1.48/0.56    ( ! [X2,X0,X3,X1] : (v2_compts_1(X2,X0) | ~v2_compts_1(X3,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.48/0.56    inference(cnf_transformation,[],[f42])).
% 1.48/0.56  fof(f825,plain,(
% 1.48/0.56    ~spl2_2 | ~spl2_3 | ~spl2_4),
% 1.48/0.56    inference(avatar_contradiction_clause,[],[f824])).
% 1.48/0.56  fof(f824,plain,(
% 1.48/0.56    $false | (~spl2_2 | ~spl2_3 | ~spl2_4)),
% 1.48/0.56    inference(subsumption_resolution,[],[f823,f43])).
% 1.48/0.56  fof(f823,plain,(
% 1.48/0.56    ~l1_pre_topc(sK0) | (~spl2_2 | ~spl2_3 | ~spl2_4)),
% 1.48/0.56    inference(subsumption_resolution,[],[f821,f512])).
% 1.48/0.56  fof(f512,plain,(
% 1.48/0.56    ~v2_compts_1(sK1,sK0) | (~spl2_2 | ~spl2_3 | ~spl2_4)),
% 1.48/0.56    inference(global_subsumption,[],[f48,f85,f81,f77])).
% 1.48/0.56  fof(f81,plain,(
% 1.48/0.56    v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl2_3),
% 1.48/0.56    inference(avatar_component_clause,[],[f80])).
% 1.48/0.56  fof(f80,plain,(
% 1.48/0.56    spl2_3 <=> v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 1.48/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 1.48/0.56  fof(f821,plain,(
% 1.48/0.56    v2_compts_1(sK1,sK0) | ~l1_pre_topc(sK0) | (~spl2_2 | ~spl2_3)),
% 1.48/0.56    inference(resolution,[],[f528,f340])).
% 1.48/0.56  fof(f528,plain,(
% 1.48/0.56    ( ! [X1] : (~m1_pre_topc(k1_pre_topc(sK0,sK1),X1) | v2_compts_1(sK1,X1) | ~l1_pre_topc(X1)) ) | (~spl2_2 | ~spl2_3)),
% 1.48/0.56    inference(subsumption_resolution,[],[f526,f511])).
% 1.48/0.56  fof(f511,plain,(
% 1.48/0.56    v2_compts_1(sK1,k1_pre_topc(sK0,sK1)) | (~spl2_2 | ~spl2_3)),
% 1.48/0.56    inference(subsumption_resolution,[],[f510,f99])).
% 1.48/0.56  fof(f510,plain,(
% 1.48/0.56    ~m1_subset_1(sK1,k1_zfmisc_1(sK1)) | v2_compts_1(sK1,k1_pre_topc(sK0,sK1)) | (~spl2_2 | ~spl2_3)),
% 1.48/0.56    inference(forward_demodulation,[],[f401,f339])).
% 1.48/0.56  fof(f401,plain,(
% 1.48/0.56    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1)))) | v2_compts_1(sK1,k1_pre_topc(sK0,sK1)) | (~spl2_2 | ~spl2_3)),
% 1.48/0.56    inference(resolution,[],[f360,f134])).
% 1.48/0.56  fof(f134,plain,(
% 1.48/0.56    ( ! [X0] : (~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | v2_compts_1(sK1,X0)) ) | ~spl2_3),
% 1.48/0.56    inference(subsumption_resolution,[],[f133,f101])).
% 1.48/0.56  fof(f133,plain,(
% 1.48/0.56    ( ! [X0] : (v2_compts_1(sK1,X0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ) | ~spl2_3),
% 1.48/0.56    inference(resolution,[],[f93,f81])).
% 1.48/0.56  fof(f507,plain,(
% 1.48/0.56    ~spl2_2 | spl2_4),
% 1.48/0.56    inference(avatar_contradiction_clause,[],[f506])).
% 1.48/0.56  fof(f506,plain,(
% 1.48/0.56    $false | (~spl2_2 | spl2_4)),
% 1.48/0.56    inference(subsumption_resolution,[],[f505,f86])).
% 1.48/0.56  fof(f86,plain,(
% 1.48/0.56    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | spl2_4),
% 1.48/0.56    inference(avatar_component_clause,[],[f84])).
% 1.48/0.56  fof(f173,plain,(
% 1.48/0.56    ~spl2_4 | spl2_7),
% 1.48/0.56    inference(avatar_contradiction_clause,[],[f172])).
% 1.48/0.56  fof(f172,plain,(
% 1.48/0.56    $false | (~spl2_4 | spl2_7)),
% 1.48/0.56    inference(subsumption_resolution,[],[f171,f101])).
% 1.48/0.56  fof(f171,plain,(
% 1.48/0.56    ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl2_4 | spl2_7)),
% 1.48/0.56    inference(subsumption_resolution,[],[f170,f140])).
% 1.48/0.56  fof(f140,plain,(
% 1.48/0.56    ~l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) | spl2_7),
% 1.48/0.56    inference(avatar_component_clause,[],[f138])).
% 1.48/0.56  fof(f170,plain,(
% 1.48/0.56    l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl2_4),
% 1.48/0.56    inference(resolution,[],[f108,f54])).
% 1.48/0.56  fof(f108,plain,(
% 1.48/0.56    m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl2_4),
% 1.48/0.56    inference(subsumption_resolution,[],[f106,f101])).
% 1.48/0.56  fof(f106,plain,(
% 1.48/0.56    m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl2_4),
% 1.48/0.56    inference(resolution,[],[f67,f85])).
% 1.48/0.56  fof(f91,plain,(
% 1.48/0.56    spl2_1 | spl2_3),
% 1.48/0.56    inference(avatar_split_clause,[],[f44,f80,f72])).
% 1.48/0.56  fof(f44,plain,(
% 1.48/0.56    v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | v2_compts_1(sK1,sK0)),
% 1.48/0.56    inference(cnf_transformation,[],[f40])).
% 1.48/0.56  fof(f88,plain,(
% 1.48/0.56    spl2_2 | spl2_4),
% 1.48/0.56    inference(avatar_split_clause,[],[f47,f84,f76])).
% 1.48/0.56  fof(f47,plain,(
% 1.48/0.56    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.48/0.56    inference(cnf_transformation,[],[f40])).
% 1.48/0.56  % SZS output end Proof for theBenchmark
% 1.48/0.56  % (1159)------------------------------
% 1.48/0.56  % (1159)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.56  % (1159)Termination reason: Refutation
% 1.48/0.56  
% 1.48/0.56  % (1159)Memory used [KB]: 11385
% 1.48/0.56  % (1159)Time elapsed: 0.132 s
% 1.48/0.56  % (1159)------------------------------
% 1.48/0.56  % (1159)------------------------------
% 1.48/0.56  % (1157)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.48/0.58  % (1148)Success in time 0.216 s
%------------------------------------------------------------------------------
