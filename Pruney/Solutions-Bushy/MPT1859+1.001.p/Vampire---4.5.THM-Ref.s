%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1859+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:46 EST 2020

% Result     : Theorem 2.97s
% Output     : Refutation 2.97s
% Verified   : 
% Statistics : Number of formulae       :  189 (2097 expanded)
%              Number of leaves         :   27 ( 574 expanded)
%              Depth                    :   23
%              Number of atoms          :  685 (11210 expanded)
%              Number of equality atoms :   82 (2011 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2500,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f144,f145,f695,f716,f718,f2499])).

fof(f2499,plain,
    ( ~ spl8_1
    | spl8_8 ),
    inference(avatar_contradiction_clause,[],[f2498])).

fof(f2498,plain,
    ( $false
    | ~ spl8_1
    | spl8_8 ),
    inference(subsumption_resolution,[],[f2496,f2390])).

fof(f2390,plain,
    ( ~ r1_tarski(sK6(k9_setfam_1(sK1),u1_pre_topc(sK0)),sK1)
    | ~ spl8_1
    | spl8_8 ),
    inference(unit_resulting_resolution,[],[f789,f1435])).

fof(f1435,plain,
    ( ! [X0] :
        ( r2_hidden(X0,u1_pre_topc(sK0))
        | ~ r1_tarski(X0,sK1) )
    | ~ spl8_1 ),
    inference(superposition,[],[f1371,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f1371,plain,
    ( ! [X0] : r2_hidden(k3_xboole_0(X0,sK1),u1_pre_topc(sK0))
    | ~ spl8_1 ),
    inference(backward_demodulation,[],[f1016,f1367])).

fof(f1367,plain,
    ( ! [X0] : k3_xboole_0(X0,sK1) = sK3(sK0,sK1,k3_xboole_0(X0,sK1))
    | ~ spl8_1 ),
    inference(forward_demodulation,[],[f1357,f1128])).

fof(f1128,plain,
    ( ! [X1] : k3_xboole_0(X1,sK1) = k3_xboole_0(sK3(sK0,sK1,k3_xboole_0(X1,sK1)),sK1)
    | ~ spl8_1 ),
    inference(superposition,[],[f767,f728])).

fof(f728,plain,(
    ! [X0] : k3_xboole_0(X0,sK1) = k9_subset_1(sK1,sK1,X0) ),
    inference(forward_demodulation,[],[f722,f723])).

fof(f723,plain,(
    ! [X0] : k9_subset_1(sK1,X0,sK1) = k3_xboole_0(X0,sK1) ),
    inference(unit_resulting_resolution,[],[f146,f128])).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k9_setfam_1(X0)) ) ),
    inference(definition_unfolding,[],[f108,f77])).

fof(f77,plain,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f146,plain,(
    m1_subset_1(sK1,k9_setfam_1(sK1)) ),
    inference(forward_demodulation,[],[f112,f74])).

fof(f74,plain,(
    u1_struct_0(sK0) = sK1 ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,
    ( ( ~ v1_tdlat_3(sK0)
      | ~ v2_tex_2(sK1,sK0) )
    & ( v1_tdlat_3(sK0)
      | v2_tex_2(sK1,sK0) )
    & u1_struct_0(sK0) = sK1
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f48,f50,f49])).

fof(f49,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v1_tdlat_3(X0)
              | ~ v2_tex_2(X1,X0) )
            & ( v1_tdlat_3(X0)
              | v2_tex_2(X1,X0) )
            & u1_struct_0(X0) = X1
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ v1_tdlat_3(sK0)
            | ~ v2_tex_2(X1,sK0) )
          & ( v1_tdlat_3(sK0)
            | v2_tex_2(X1,sK0) )
          & u1_struct_0(sK0) = X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ? [X1] :
        ( ( ~ v1_tdlat_3(sK0)
          | ~ v2_tex_2(X1,sK0) )
        & ( v1_tdlat_3(sK0)
          | v2_tex_2(X1,sK0) )
        & u1_struct_0(sK0) = X1
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( ~ v1_tdlat_3(sK0)
        | ~ v2_tex_2(sK1,sK0) )
      & ( v1_tdlat_3(sK0)
        | v2_tex_2(sK1,sK0) )
      & u1_struct_0(sK0) = sK1
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_tdlat_3(X0)
            | ~ v2_tex_2(X1,X0) )
          & ( v1_tdlat_3(X0)
            | v2_tex_2(X1,X0) )
          & u1_struct_0(X0) = X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_tdlat_3(X0)
            | ~ v2_tex_2(X1,X0) )
          & ( v1_tdlat_3(X0)
            | v2_tex_2(X1,X0) )
          & u1_struct_0(X0) = X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tex_2(X1,X0)
          <~> v1_tdlat_3(X0) )
          & u1_struct_0(X0) = X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tex_2(X1,X0)
          <~> v1_tdlat_3(X0) )
          & u1_struct_0(X0) = X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,plain,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( u1_struct_0(X0) = X1
             => ( v2_tex_2(X1,X0)
              <=> v1_tdlat_3(X0) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( u1_struct_0(X0) = X1
             => ( v2_tex_2(X1,X0)
              <=> v1_tdlat_3(X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( u1_struct_0(X0) = X1
           => ( v2_tex_2(X1,X0)
            <=> v1_tdlat_3(X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_tex_2)).

fof(f112,plain,(
    m1_subset_1(sK1,k9_setfam_1(u1_struct_0(sK0))) ),
    inference(definition_unfolding,[],[f73,f77])).

fof(f73,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f51])).

fof(f722,plain,(
    ! [X0] : k9_subset_1(sK1,X0,sK1) = k9_subset_1(sK1,sK1,X0) ),
    inference(unit_resulting_resolution,[],[f146,f129])).

fof(f129,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k9_setfam_1(X0)) ) ),
    inference(definition_unfolding,[],[f109,f77])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(f767,plain,
    ( ! [X0] : k3_xboole_0(X0,sK1) = k9_subset_1(sK1,sK1,sK3(sK0,sK1,k3_xboole_0(X0,sK1)))
    | ~ spl8_1 ),
    inference(unit_resulting_resolution,[],[f138,f146,f727,f739,f200])).

fof(f200,plain,(
    ! [X14,X13] :
      ( ~ r1_tarski(X13,X14)
      | k9_subset_1(sK1,X14,sK3(sK0,X14,X13)) = X13
      | ~ m1_subset_1(X13,k9_setfam_1(sK1))
      | ~ v2_tex_2(X14,sK0)
      | ~ m1_subset_1(X14,k9_setfam_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f165,f72])).

fof(f72,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f165,plain,(
    ! [X14,X13] :
      ( ~ m1_subset_1(X13,k9_setfam_1(sK1))
      | k9_subset_1(sK1,X14,sK3(sK0,X14,X13)) = X13
      | ~ r1_tarski(X13,X14)
      | ~ v2_tex_2(X14,sK0)
      | ~ m1_subset_1(X14,k9_setfam_1(sK1))
      | ~ l1_pre_topc(sK0) ) ),
    inference(superposition,[],[f118,f74])).

fof(f118,plain,(
    ! [X4,X0,X1] :
      ( k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X4)) = X4
      | ~ r1_tarski(X4,X1)
      | ~ m1_subset_1(X4,k9_setfam_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f85,f77,f77])).

fof(f85,plain,(
    ! [X4,X0,X1] :
      ( k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X4)) = X4
      | ~ r1_tarski(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ( ! [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & r1_tarski(sK2(X0,X1),X1)
                & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X4] :
                  ( ( k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X4)) = X4
                    & v3_pre_topc(sK3(X0,X1,X4),X0)
                    & m1_subset_1(sK3(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X4,X1)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f54,f56,f55])).

fof(f55,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
              | ~ v3_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ! [X3] :
            ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1)
            | ~ v3_pre_topc(X3,X0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & r1_tarski(sK2(X0,X1),X1)
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( k9_subset_1(u1_struct_0(X0),X1,X5) = X4
          & v3_pre_topc(X5,X0)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X4)) = X4
        & v3_pre_topc(sK3(X0,X1,X4),X0)
        & m1_subset_1(sK3(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( ! [X3] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X4] :
                  ( ? [X5] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X5) = X4
                      & v3_pre_topc(X5,X0)
                      & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X4,X1)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( ! [X3] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( ? [X3] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                            & v3_pre_topc(X3,X0) ) )
                    & r1_tarski(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tex_2)).

fof(f739,plain,(
    ! [X0] : r1_tarski(k3_xboole_0(X0,sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f727,f126])).

fof(f126,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k9_setfam_1(X1)) ) ),
    inference(definition_unfolding,[],[f105,f77])).

fof(f105,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f727,plain,(
    ! [X0] : m1_subset_1(k3_xboole_0(X0,sK1),k9_setfam_1(sK1)) ),
    inference(backward_demodulation,[],[f724,f723])).

fof(f724,plain,(
    ! [X0] : m1_subset_1(k9_subset_1(sK1,X0,sK1),k9_setfam_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f146,f127])).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k9_setfam_1(X0))
      | ~ m1_subset_1(X2,k9_setfam_1(X0)) ) ),
    inference(definition_unfolding,[],[f107,f77,f77])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f138,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl8_1
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f1357,plain,
    ( ! [X0] : sK3(sK0,sK1,k3_xboole_0(X0,sK1)) = k3_xboole_0(sK3(sK0,sK1,k3_xboole_0(X0,sK1)),sK1)
    | ~ spl8_1 ),
    inference(unit_resulting_resolution,[],[f1020,f97])).

fof(f1020,plain,
    ( ! [X0] : r1_tarski(sK3(sK0,sK1,k3_xboole_0(X0,sK1)),sK1)
    | ~ spl8_1 ),
    inference(unit_resulting_resolution,[],[f769,f126])).

fof(f769,plain,
    ( ! [X0] : m1_subset_1(sK3(sK0,sK1,k3_xboole_0(X0,sK1)),k9_setfam_1(sK1))
    | ~ spl8_1 ),
    inference(unit_resulting_resolution,[],[f138,f146,f727,f739,f217])).

fof(f217,plain,(
    ! [X24,X23] :
      ( ~ r1_tarski(X24,X23)
      | m1_subset_1(sK3(sK0,X23,X24),k9_setfam_1(sK1))
      | ~ m1_subset_1(X24,k9_setfam_1(sK1))
      | ~ v2_tex_2(X23,sK0)
      | ~ m1_subset_1(X23,k9_setfam_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f170,f72])).

fof(f170,plain,(
    ! [X24,X23] :
      ( m1_subset_1(sK3(sK0,X23,X24),k9_setfam_1(sK1))
      | ~ r1_tarski(X24,X23)
      | ~ m1_subset_1(X24,k9_setfam_1(sK1))
      | ~ v2_tex_2(X23,sK0)
      | ~ m1_subset_1(X23,k9_setfam_1(sK1))
      | ~ l1_pre_topc(sK0) ) ),
    inference(superposition,[],[f120,f74])).

fof(f120,plain,(
    ! [X4,X0,X1] :
      ( m1_subset_1(sK3(X0,X1,X4),k9_setfam_1(u1_struct_0(X0)))
      | ~ r1_tarski(X4,X1)
      | ~ m1_subset_1(X4,k9_setfam_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f83,f77,f77,f77])).

fof(f83,plain,(
    ! [X4,X0,X1] :
      ( m1_subset_1(sK3(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f1016,plain,
    ( ! [X0] : r2_hidden(sK3(sK0,sK1,k3_xboole_0(X0,sK1)),u1_pre_topc(sK0))
    | ~ spl8_1 ),
    inference(unit_resulting_resolution,[],[f768,f769,f223])).

fof(f223,plain,(
    ! [X26] :
      ( ~ v3_pre_topc(X26,sK0)
      | r2_hidden(X26,u1_pre_topc(sK0))
      | ~ m1_subset_1(X26,k9_setfam_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f172,f72])).

fof(f172,plain,(
    ! [X26] :
      ( ~ m1_subset_1(X26,k9_setfam_1(sK1))
      | r2_hidden(X26,u1_pre_topc(sK0))
      | ~ v3_pre_topc(X26,sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(superposition,[],[f122,f74])).

fof(f122,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,u1_pre_topc(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f89,f77])).

fof(f89,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,u1_pre_topc(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

fof(f768,plain,
    ( ! [X0] : v3_pre_topc(sK3(sK0,sK1,k3_xboole_0(X0,sK1)),sK0)
    | ~ spl8_1 ),
    inference(unit_resulting_resolution,[],[f138,f146,f727,f739,f206])).

fof(f206,plain,(
    ! [X17,X18] :
      ( v3_pre_topc(sK3(sK0,X18,X17),sK0)
      | ~ m1_subset_1(X17,k9_setfam_1(sK1))
      | ~ r1_tarski(X17,X18)
      | ~ v2_tex_2(X18,sK0)
      | ~ m1_subset_1(X18,k9_setfam_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f167,f72])).

fof(f167,plain,(
    ! [X17,X18] :
      ( ~ m1_subset_1(X17,k9_setfam_1(sK1))
      | v3_pre_topc(sK3(sK0,X18,X17),sK0)
      | ~ r1_tarski(X17,X18)
      | ~ v2_tex_2(X18,sK0)
      | ~ m1_subset_1(X18,k9_setfam_1(sK1))
      | ~ l1_pre_topc(sK0) ) ),
    inference(superposition,[],[f119,f74])).

fof(f119,plain,(
    ! [X4,X0,X1] :
      ( v3_pre_topc(sK3(X0,X1,X4),X0)
      | ~ r1_tarski(X4,X1)
      | ~ m1_subset_1(X4,k9_setfam_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f84,f77,f77])).

fof(f84,plain,(
    ! [X4,X0,X1] :
      ( v3_pre_topc(sK3(X0,X1,X4),X0)
      | ~ r1_tarski(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f789,plain,
    ( ~ r2_hidden(sK6(k9_setfam_1(sK1),u1_pre_topc(sK0)),u1_pre_topc(sK0))
    | spl8_8 ),
    inference(unit_resulting_resolution,[],[f760,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK6(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK6(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f68,f69])).

fof(f69,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f760,plain,
    ( ~ r1_tarski(k9_setfam_1(sK1),u1_pre_topc(sK0))
    | spl8_8 ),
    inference(unit_resulting_resolution,[],[f715,f733,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f65])).

fof(f65,plain,(
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

fof(f733,plain,(
    r1_tarski(u1_pre_topc(sK0),k9_setfam_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f175,f126])).

fof(f175,plain,(
    m1_subset_1(u1_pre_topc(sK0),k9_setfam_1(k9_setfam_1(sK1))) ),
    inference(subsumption_resolution,[],[f156,f72])).

fof(f156,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k9_setfam_1(k9_setfam_1(sK1)))
    | ~ l1_pre_topc(sK0) ),
    inference(superposition,[],[f114,f74])).

fof(f114,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k9_setfam_1(k9_setfam_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f79,f77,f77])).

fof(f79,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f715,plain,
    ( k9_setfam_1(sK1) != u1_pre_topc(sK0)
    | spl8_8 ),
    inference(avatar_component_clause,[],[f713])).

fof(f713,plain,
    ( spl8_8
  <=> k9_setfam_1(sK1) = u1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f2496,plain,
    ( r1_tarski(sK6(k9_setfam_1(sK1),u1_pre_topc(sK0)),sK1)
    | spl8_8 ),
    inference(unit_resulting_resolution,[],[f1295,f126])).

fof(f1295,plain,
    ( m1_subset_1(sK6(k9_setfam_1(sK1),u1_pre_topc(sK0)),k9_setfam_1(sK1))
    | spl8_8 ),
    inference(unit_resulting_resolution,[],[f113,f788,f130])).

fof(f130,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k9_setfam_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f110,f77])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f788,plain,
    ( r2_hidden(sK6(k9_setfam_1(sK1),u1_pre_topc(sK0)),k9_setfam_1(sK1))
    | spl8_8 ),
    inference(unit_resulting_resolution,[],[f760,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK6(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f113,plain,(
    ! [X0] : m1_subset_1(k9_setfam_1(X0),k9_setfam_1(k9_setfam_1(X0))) ),
    inference(definition_unfolding,[],[f78,f77,f77])).

fof(f78,plain,(
    ! [X0] : m1_subset_1(k9_setfam_1(X0),k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : m1_subset_1(k9_setfam_1(X0),k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_setfam_1)).

fof(f718,plain,
    ( ~ spl8_2
    | spl8_8 ),
    inference(avatar_split_clause,[],[f717,f713,f141])).

fof(f141,plain,
    ( spl8_2
  <=> v1_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f717,plain,
    ( k9_setfam_1(sK1) = u1_pre_topc(sK0)
    | ~ v1_tdlat_3(sK0) ),
    inference(subsumption_resolution,[],[f154,f72])).

fof(f154,plain,
    ( k9_setfam_1(sK1) = u1_pre_topc(sK0)
    | ~ v1_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(superposition,[],[f81,f74])).

fof(f81,plain,(
    ! [X0] :
      ( u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(X0))
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | u1_pre_topc(X0) != k9_setfam_1(u1_struct_0(X0)) )
        & ( u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(X0))
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_tdlat_3(X0)
      <=> u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tdlat_3)).

fof(f716,plain,
    ( spl8_2
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f711,f713,f141])).

fof(f711,plain,
    ( k9_setfam_1(sK1) != u1_pre_topc(sK0)
    | v1_tdlat_3(sK0) ),
    inference(subsumption_resolution,[],[f155,f72])).

fof(f155,plain,
    ( k9_setfam_1(sK1) != u1_pre_topc(sK0)
    | v1_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(superposition,[],[f82,f74])).

fof(f82,plain,(
    ! [X0] :
      ( v1_tdlat_3(X0)
      | u1_pre_topc(X0) != k9_setfam_1(u1_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f695,plain,
    ( spl8_1
    | ~ spl8_2 ),
    inference(avatar_contradiction_clause,[],[f694])).

fof(f694,plain,
    ( $false
    | spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f693,f259])).

fof(f259,plain,
    ( m1_subset_1(sK2(sK0,sK1),u1_pre_topc(sK0))
    | spl8_1
    | ~ spl8_2 ),
    inference(unit_resulting_resolution,[],[f139,f153,f190])).

fof(f190,plain,
    ( ! [X7] :
        ( v2_tex_2(X7,sK0)
        | ~ m1_subset_1(X7,u1_pre_topc(sK0))
        | m1_subset_1(sK2(sK0,X7),u1_pre_topc(sK0)) )
    | ~ spl8_2 ),
    inference(forward_demodulation,[],[f189,f151])).

fof(f151,plain,
    ( k9_setfam_1(sK1) = u1_pre_topc(sK0)
    | ~ spl8_2 ),
    inference(forward_demodulation,[],[f149,f74])).

fof(f149,plain,
    ( k9_setfam_1(u1_struct_0(sK0)) = u1_pre_topc(sK0)
    | ~ spl8_2 ),
    inference(unit_resulting_resolution,[],[f72,f142,f81])).

fof(f142,plain,
    ( v1_tdlat_3(sK0)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f141])).

fof(f189,plain,
    ( ! [X7] :
        ( ~ m1_subset_1(X7,u1_pre_topc(sK0))
        | v2_tex_2(X7,sK0)
        | m1_subset_1(sK2(sK0,X7),k9_setfam_1(sK1)) )
    | ~ spl8_2 ),
    inference(forward_demodulation,[],[f188,f151])).

fof(f188,plain,(
    ! [X7] :
      ( ~ m1_subset_1(X7,k9_setfam_1(sK1))
      | v2_tex_2(X7,sK0)
      | m1_subset_1(sK2(sK0,X7),k9_setfam_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f161,f72])).

fof(f161,plain,(
    ! [X7] :
      ( ~ m1_subset_1(X7,k9_setfam_1(sK1))
      | v2_tex_2(X7,sK0)
      | m1_subset_1(sK2(sK0,X7),k9_setfam_1(sK1))
      | ~ l1_pre_topc(sK0) ) ),
    inference(superposition,[],[f117,f74])).

fof(f117,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | m1_subset_1(sK2(X0,X1),k9_setfam_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f86,f77,f77])).

fof(f86,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f153,plain,
    ( m1_subset_1(sK1,u1_pre_topc(sK0))
    | ~ spl8_2 ),
    inference(backward_demodulation,[],[f146,f151])).

fof(f139,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f137])).

fof(f693,plain,
    ( ~ m1_subset_1(sK2(sK0,sK1),u1_pre_topc(sK0))
    | spl8_1
    | ~ spl8_2 ),
    inference(forward_demodulation,[],[f692,f151])).

fof(f692,plain,
    ( ~ m1_subset_1(sK2(sK0,sK1),k9_setfam_1(sK1))
    | spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f687,f405])).

fof(f405,plain,
    ( sK2(sK0,sK1) = k3_xboole_0(sK1,sK2(sK0,sK1))
    | spl8_1
    | ~ spl8_2 ),
    inference(superposition,[],[f267,f96])).

fof(f96,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f267,plain,
    ( sK2(sK0,sK1) = k3_xboole_0(sK2(sK0,sK1),sK1)
    | spl8_1
    | ~ spl8_2 ),
    inference(unit_resulting_resolution,[],[f258,f97])).

fof(f258,plain,
    ( r1_tarski(sK2(sK0,sK1),sK1)
    | spl8_1
    | ~ spl8_2 ),
    inference(unit_resulting_resolution,[],[f139,f153,f187])).

fof(f187,plain,
    ( ! [X6] :
        ( v2_tex_2(X6,sK0)
        | ~ m1_subset_1(X6,u1_pre_topc(sK0))
        | r1_tarski(sK2(sK0,X6),X6) )
    | ~ spl8_2 ),
    inference(forward_demodulation,[],[f186,f151])).

fof(f186,plain,(
    ! [X6] :
      ( v2_tex_2(X6,sK0)
      | ~ m1_subset_1(X6,k9_setfam_1(sK1))
      | r1_tarski(sK2(sK0,X6),X6) ) ),
    inference(subsumption_resolution,[],[f160,f72])).

fof(f160,plain,(
    ! [X6] :
      ( ~ m1_subset_1(X6,k9_setfam_1(sK1))
      | v2_tex_2(X6,sK0)
      | r1_tarski(sK2(sK0,X6),X6)
      | ~ l1_pre_topc(sK0) ) ),
    inference(superposition,[],[f116,f74])).

fof(f116,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | r1_tarski(sK2(X0,X1),X1)
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f87,f77])).

fof(f87,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | r1_tarski(sK2(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f687,plain,
    ( sK2(sK0,sK1) != k3_xboole_0(sK1,sK2(sK0,sK1))
    | ~ m1_subset_1(sK2(sK0,sK1),k9_setfam_1(sK1))
    | spl8_1
    | ~ spl8_2 ),
    inference(superposition,[],[f322,f128])).

fof(f322,plain,
    ( sK2(sK0,sK1) != k9_subset_1(sK1,sK1,sK2(sK0,sK1))
    | spl8_1
    | ~ spl8_2 ),
    inference(unit_resulting_resolution,[],[f139,f153,f259,f270,f179])).

fof(f179,plain,
    ( ! [X0,X1] :
        ( v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X1,u1_pre_topc(sK0))
        | sK2(sK0,X0) != k9_subset_1(sK1,X0,X1)
        | ~ m1_subset_1(X0,u1_pre_topc(sK0))
        | ~ v3_pre_topc(X1,sK0) )
    | ~ spl8_2 ),
    inference(forward_demodulation,[],[f178,f151])).

fof(f178,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,u1_pre_topc(sK0))
        | sK2(sK0,X0) != k9_subset_1(sK1,X0,X1)
        | v2_tex_2(X0,sK0)
        | ~ v3_pre_topc(X1,sK0)
        | ~ m1_subset_1(X0,k9_setfam_1(sK1)) )
    | ~ spl8_2 ),
    inference(forward_demodulation,[],[f177,f151])).

fof(f177,plain,(
    ! [X0,X1] :
      ( sK2(sK0,X0) != k9_subset_1(sK1,X0,X1)
      | v2_tex_2(X0,sK0)
      | ~ v3_pre_topc(X1,sK0)
      | ~ m1_subset_1(X1,k9_setfam_1(sK1))
      | ~ m1_subset_1(X0,k9_setfam_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f157,f72])).

fof(f157,plain,(
    ! [X0,X1] :
      ( sK2(sK0,X0) != k9_subset_1(sK1,X0,X1)
      | v2_tex_2(X0,sK0)
      | ~ v3_pre_topc(X1,sK0)
      | ~ m1_subset_1(X1,k9_setfam_1(sK1))
      | ~ m1_subset_1(X0,k9_setfam_1(sK1))
      | ~ l1_pre_topc(sK0) ) ),
    inference(superposition,[],[f115,f74])).

fof(f115,plain,(
    ! [X0,X3,X1] :
      ( v2_tex_2(X1,X0)
      | k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1)
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k9_setfam_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f88,f77,f77])).

fof(f88,plain,(
    ! [X0,X3,X1] :
      ( v2_tex_2(X1,X0)
      | k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1)
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f270,plain,
    ( v3_pre_topc(sK2(sK0,sK1),sK0)
    | spl8_1
    | ~ spl8_2 ),
    inference(unit_resulting_resolution,[],[f259,f228])).

fof(f228,plain,
    ( ! [X27] :
        ( v3_pre_topc(X27,sK0)
        | ~ m1_subset_1(X27,u1_pre_topc(sK0)) )
    | ~ spl8_2 ),
    inference(forward_demodulation,[],[f227,f151])).

fof(f227,plain,
    ( ! [X27] :
        ( ~ m1_subset_1(X27,k9_setfam_1(sK1))
        | v3_pre_topc(X27,sK0) )
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f226,f150])).

fof(f150,plain,
    ( v2_pre_topc(sK0)
    | ~ spl8_2 ),
    inference(unit_resulting_resolution,[],[f72,f142,f80])).

fof(f80,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tdlat_3)).

fof(f226,plain,
    ( ! [X27] :
        ( ~ m1_subset_1(X27,k9_setfam_1(sK1))
        | v3_pre_topc(X27,sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f225,f72])).

fof(f225,plain,
    ( ! [X27] :
        ( ~ m1_subset_1(X27,k9_setfam_1(sK1))
        | v3_pre_topc(X27,sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f174,f142])).

fof(f174,plain,(
    ! [X27] :
      ( ~ m1_subset_1(X27,k9_setfam_1(sK1))
      | v3_pre_topc(X27,sK0)
      | ~ v1_tdlat_3(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(superposition,[],[f124,f74])).

fof(f124,plain,(
    ! [X2,X0] :
      ( v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k9_setfam_1(u1_struct_0(X0)))
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f91,f77])).

fof(f91,plain,(
    ! [X2,X0] :
      ( v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ( ~ v3_pre_topc(sK4(X0),X0)
            & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f60,f61])).

fof(f61,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK4(X0),X0)
        & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ? [X1] :
              ( ~ v3_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ? [X1] :
              ( ~ v3_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X1] :
              ( v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => v3_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_tdlat_3)).

fof(f145,plain,
    ( spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f75,f141,f137])).

fof(f75,plain,
    ( v1_tdlat_3(sK0)
    | v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f144,plain,
    ( ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f76,f141,f137])).

fof(f76,plain,
    ( ~ v1_tdlat_3(sK0)
    | ~ v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f51])).

%------------------------------------------------------------------------------
