%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1799+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:33 EST 2020

% Result     : Theorem 43.28s
% Output     : Refutation 43.28s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 268 expanded)
%              Number of leaves         :   25 ( 118 expanded)
%              Depth                    :   14
%              Number of atoms          :  608 (1452 expanded)
%              Number of equality atoms :   80 ( 163 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17113,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f6050,f6055,f6060,f6065,f6070,f6080,f6090,f6105,f6410,f6428,f6433,f6549,f15073,f17102,f17112])).

fof(f17112,plain,
    ( spl241_1
    | ~ spl241_2
    | ~ spl241_3
    | ~ spl241_43
    | ~ spl241_56
    | spl241_289
    | ~ spl241_353 ),
    inference(avatar_contradiction_clause,[],[f17111])).

fof(f17111,plain,
    ( $false
    | spl241_1
    | ~ spl241_2
    | ~ spl241_3
    | ~ spl241_43
    | ~ spl241_56
    | spl241_289
    | ~ spl241_353 ),
    inference(subsumption_resolution,[],[f17110,f6409])).

fof(f6409,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl241_43 ),
    inference(avatar_component_clause,[],[f6407])).

fof(f6407,plain,
    ( spl241_43
  <=> m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl241_43])])).

fof(f17110,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl241_1
    | ~ spl241_2
    | ~ spl241_3
    | ~ spl241_43
    | ~ spl241_56
    | spl241_289
    | ~ spl241_353 ),
    inference(forward_demodulation,[],[f17109,f6548])).

fof(f6548,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1))
    | ~ spl241_56 ),
    inference(avatar_component_clause,[],[f6546])).

fof(f6546,plain,
    ( spl241_56
  <=> u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl241_56])])).

fof(f17109,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK0,sK1))))
    | spl241_1
    | ~ spl241_2
    | ~ spl241_3
    | ~ spl241_43
    | spl241_289
    | ~ spl241_353 ),
    inference(subsumption_resolution,[],[f17108,f6049])).

fof(f6049,plain,
    ( ~ v2_struct_0(sK0)
    | spl241_1 ),
    inference(avatar_component_clause,[],[f6047])).

fof(f6047,plain,
    ( spl241_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl241_1])])).

fof(f17108,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK0,sK1))))
    | v2_struct_0(sK0)
    | ~ spl241_2
    | ~ spl241_3
    | ~ spl241_43
    | spl241_289
    | ~ spl241_353 ),
    inference(subsumption_resolution,[],[f17107,f6054])).

fof(f6054,plain,
    ( v2_pre_topc(sK0)
    | ~ spl241_2 ),
    inference(avatar_component_clause,[],[f6052])).

fof(f6052,plain,
    ( spl241_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl241_2])])).

fof(f17107,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK0,sK1))))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl241_3
    | ~ spl241_43
    | spl241_289
    | ~ spl241_353 ),
    inference(subsumption_resolution,[],[f17106,f6059])).

fof(f6059,plain,
    ( l1_pre_topc(sK0)
    | ~ spl241_3 ),
    inference(avatar_component_clause,[],[f6057])).

fof(f6057,plain,
    ( spl241_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl241_3])])).

fof(f17106,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK0,sK1))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl241_43
    | spl241_289
    | ~ spl241_353 ),
    inference(subsumption_resolution,[],[f17105,f6409])).

fof(f17105,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK0,sK1))))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl241_289
    | ~ spl241_353 ),
    inference(subsumption_resolution,[],[f17103,f15072])).

fof(f15072,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK1),k8_tmap_1(sK0,sK1))
    | spl241_289 ),
    inference(avatar_component_clause,[],[f15070])).

fof(f15070,plain,
    ( spl241_289
  <=> v3_pre_topc(u1_struct_0(sK1),k8_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl241_289])])).

fof(f17103,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK0,sK1))))
    | v3_pre_topc(u1_struct_0(sK1),k8_tmap_1(sK0,sK1))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl241_353 ),
    inference(superposition,[],[f5624,f17101])).

fof(f17101,plain,
    ( k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl241_353 ),
    inference(avatar_component_clause,[],[f17099])).

fof(f17099,plain,
    ( spl241_353
  <=> k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl241_353])])).

fof(f5624,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X2))))
      | v3_pre_topc(X2,k6_tmap_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f4959])).

fof(f4959,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(X2,k6_tmap_1(X0,X1))
      | X1 != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3783])).

fof(f3783,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v3_pre_topc(X2,k6_tmap_1(X0,X1))
              | X1 != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3782])).

fof(f3782,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v3_pre_topc(X2,k6_tmap_1(X0,X1))
              | X1 != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3372])).

fof(f3372,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1))))
             => ( X1 = X2
               => v3_pre_topc(X2,k6_tmap_1(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_tmap_1)).

fof(f17102,plain,
    ( spl241_353
    | spl241_1
    | ~ spl241_2
    | ~ spl241_3
    | ~ spl241_5
    | ~ spl241_43 ),
    inference(avatar_split_clause,[],[f6412,f6407,f6067,f6057,f6052,f6047,f17099])).

fof(f6067,plain,
    ( spl241_5
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl241_5])])).

fof(f6412,plain,
    ( k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | spl241_1
    | ~ spl241_2
    | ~ spl241_3
    | ~ spl241_5
    | ~ spl241_43 ),
    inference(unit_resulting_resolution,[],[f6049,f6054,f6059,f6069,f6409,f5923])).

fof(f5923,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f5922,f4559])).

fof(f4559,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3521])).

fof(f3521,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3520])).

fof(f3520,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3349])).

fof(f3349,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_tmap_1)).

fof(f5922,plain,(
    ! [X0,X1] :
      ( k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f5921,f4560])).

fof(f4560,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3521])).

fof(f5921,plain,(
    ! [X0,X1] :
      ( k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f5532,f4561])).

fof(f4561,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3521])).

fof(f5532,plain,(
    ! [X0,X1] :
      ( k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f5531])).

fof(f5531,plain,(
    ! [X2,X0,X1] :
      ( k6_tmap_1(X0,u1_struct_0(X1)) = X2
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | k8_tmap_1(X0,X1) != X2
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f4567])).

fof(f4567,plain,(
    ! [X4,X2,X0,X1] :
      ( k6_tmap_1(X0,X4) = X2
      | u1_struct_0(X1) != X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | k8_tmap_1(X0,X1) != X2
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4184])).

fof(f4184,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k8_tmap_1(X0,X1) = X2
                  | ( k6_tmap_1(X0,sK5(X0,X1,X2)) != X2
                    & u1_struct_0(X1) = sK5(X0,X1,X2)
                    & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( k6_tmap_1(X0,X4) = X2
                      | u1_struct_0(X1) != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k8_tmap_1(X0,X1) != X2 ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f4182,f4183])).

fof(f4183,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k6_tmap_1(X0,X3) != X2
          & u1_struct_0(X1) = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k6_tmap_1(X0,sK5(X0,X1,X2)) != X2
        & u1_struct_0(X1) = sK5(X0,X1,X2)
        & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f4182,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k8_tmap_1(X0,X1) = X2
                  | ? [X3] :
                      ( k6_tmap_1(X0,X3) != X2
                      & u1_struct_0(X1) = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( k6_tmap_1(X0,X4) = X2
                      | u1_struct_0(X1) != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k8_tmap_1(X0,X1) != X2 ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f4181])).

fof(f4181,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k8_tmap_1(X0,X1) = X2
                  | ? [X3] :
                      ( k6_tmap_1(X0,X3) != X2
                      & u1_struct_0(X1) = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X3] :
                      ( k6_tmap_1(X0,X3) = X2
                      | u1_struct_0(X1) != X3
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k8_tmap_1(X0,X1) != X2 ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f3527])).

fof(f3527,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k8_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( k6_tmap_1(X0,X3) = X2
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3526])).

fof(f3526,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k8_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( k6_tmap_1(X0,X3) = X2
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3326])).

fof(f3326,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2)
                & v1_pre_topc(X2) )
             => ( k8_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( u1_struct_0(X1) = X3
                     => k6_tmap_1(X0,X3) = X2 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_tmap_1)).

fof(f6069,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl241_5 ),
    inference(avatar_component_clause,[],[f6067])).

fof(f15073,plain,
    ( ~ spl241_289
    | ~ spl241_7
    | ~ spl241_9
    | spl241_12
    | ~ spl241_46
    | ~ spl241_47 ),
    inference(avatar_split_clause,[],[f6643,f6430,f6425,f6102,f6087,f6077,f15070])).

fof(f6077,plain,
    ( spl241_7
  <=> m1_pre_topc(sK2,k8_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl241_7])])).

fof(f6087,plain,
    ( spl241_9
  <=> u1_struct_0(sK1) = u1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl241_9])])).

fof(f6102,plain,
    ( spl241_12
  <=> v1_tsep_1(sK2,k8_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl241_12])])).

fof(f6425,plain,
    ( spl241_46
  <=> v2_pre_topc(k8_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl241_46])])).

fof(f6430,plain,
    ( spl241_47
  <=> l1_pre_topc(k8_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl241_47])])).

fof(f6643,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK1),k8_tmap_1(sK0,sK1))
    | ~ spl241_7
    | ~ spl241_9
    | spl241_12
    | ~ spl241_46
    | ~ spl241_47 ),
    inference(unit_resulting_resolution,[],[f6427,f6432,f6079,f6104,f6183])).

fof(f6183,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(u1_struct_0(sK1),X0)
        | v1_tsep_1(sK2,X0)
        | ~ m1_pre_topc(sK2,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl241_9 ),
    inference(subsumption_resolution,[],[f6182,f6146])).

fof(f6146,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl241_9 ),
    inference(superposition,[],[f4581,f6089])).

fof(f6089,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK2)
    | ~ spl241_9 ),
    inference(avatar_component_clause,[],[f6087])).

fof(f4581,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3541])).

fof(f3541,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3396])).

fof(f3396,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f6182,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(u1_struct_0(sK1),X0)
        | v1_tsep_1(sK2,X0)
        | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(sK2,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl241_9 ),
    inference(superposition,[],[f5522,f6089])).

fof(f5522,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(u1_struct_0(X1),X0)
      | v1_tsep_1(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f4538])).

fof(f4538,plain,(
    ! [X2,X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f4175])).

fof(f4175,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                  | ~ v3_pre_topc(X2,X0) )
                & ( v3_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_tsep_1(X1,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f4174])).

fof(f4174,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                  | ~ v3_pre_topc(X2,X0) )
                & ( v3_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_tsep_1(X1,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f3505])).

fof(f3505,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> v3_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f3504])).

fof(f3504,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> v3_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3391])).

fof(f3391,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                <=> v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tsep_1)).

fof(f6104,plain,
    ( ~ v1_tsep_1(sK2,k8_tmap_1(sK0,sK1))
    | spl241_12 ),
    inference(avatar_component_clause,[],[f6102])).

fof(f6079,plain,
    ( m1_pre_topc(sK2,k8_tmap_1(sK0,sK1))
    | ~ spl241_7 ),
    inference(avatar_component_clause,[],[f6077])).

fof(f6432,plain,
    ( l1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ spl241_47 ),
    inference(avatar_component_clause,[],[f6430])).

fof(f6427,plain,
    ( v2_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ spl241_46 ),
    inference(avatar_component_clause,[],[f6425])).

fof(f6549,plain,
    ( spl241_56
    | spl241_1
    | ~ spl241_2
    | ~ spl241_3
    | spl241_4
    | ~ spl241_5 ),
    inference(avatar_split_clause,[],[f6171,f6067,f6062,f6057,f6052,f6047,f6546])).

fof(f6062,plain,
    ( spl241_4
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl241_4])])).

fof(f6171,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1))
    | spl241_1
    | ~ spl241_2
    | ~ spl241_3
    | spl241_4
    | ~ spl241_5 ),
    inference(unit_resulting_resolution,[],[f6049,f6054,f6059,f6064,f6069,f4565])).

fof(f4565,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3525])).

fof(f3525,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ! [X2] :
                ( u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3524])).

fof(f3524,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ! [X2] :
                ( u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3381])).

fof(f3381,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ( ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2) ) )
            & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t114_tmap_1)).

fof(f6064,plain,
    ( ~ v2_struct_0(sK1)
    | spl241_4 ),
    inference(avatar_component_clause,[],[f6062])).

fof(f6433,plain,
    ( spl241_47
    | spl241_1
    | ~ spl241_2
    | ~ spl241_3
    | ~ spl241_5 ),
    inference(avatar_split_clause,[],[f6157,f6067,f6057,f6052,f6047,f6430])).

fof(f6157,plain,
    ( l1_pre_topc(k8_tmap_1(sK0,sK1))
    | spl241_1
    | ~ spl241_2
    | ~ spl241_3
    | ~ spl241_5 ),
    inference(unit_resulting_resolution,[],[f6049,f6054,f6059,f6069,f4561])).

fof(f6428,plain,
    ( spl241_46
    | spl241_1
    | ~ spl241_2
    | ~ spl241_3
    | ~ spl241_5 ),
    inference(avatar_split_clause,[],[f6150,f6067,f6057,f6052,f6047,f6425])).

fof(f6150,plain,
    ( v2_pre_topc(k8_tmap_1(sK0,sK1))
    | spl241_1
    | ~ spl241_2
    | ~ spl241_3
    | ~ spl241_5 ),
    inference(unit_resulting_resolution,[],[f6049,f6054,f6059,f6069,f4560])).

fof(f6410,plain,
    ( spl241_43
    | ~ spl241_3
    | ~ spl241_5 ),
    inference(avatar_split_clause,[],[f6144,f6067,f6057,f6407])).

fof(f6144,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl241_3
    | ~ spl241_5 ),
    inference(unit_resulting_resolution,[],[f6059,f6069,f4581])).

fof(f6105,plain,
    ( ~ spl241_12
    | ~ spl241_7 ),
    inference(avatar_split_clause,[],[f4528,f6077,f6102])).

fof(f4528,plain,
    ( ~ m1_pre_topc(sK2,k8_tmap_1(sK0,sK1))
    | ~ v1_tsep_1(sK2,k8_tmap_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f4169])).

fof(f4169,plain,
    ( ( ~ m1_pre_topc(sK2,k8_tmap_1(sK0,sK1))
      | ~ v1_tsep_1(sK2,k8_tmap_1(sK0,sK1)) )
    & u1_struct_0(sK1) = u1_struct_0(sK2)
    & m1_pre_topc(sK2,k8_tmap_1(sK0,sK1))
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f3499,f4168,f4167,f4166])).

fof(f4166,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ m1_pre_topc(X2,k8_tmap_1(X0,X1))
                  | ~ v1_tsep_1(X2,k8_tmap_1(X0,X1)) )
                & u1_struct_0(X1) = u1_struct_0(X2)
                & m1_pre_topc(X2,k8_tmap_1(X0,X1)) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_pre_topc(X2,k8_tmap_1(sK0,X1))
                | ~ v1_tsep_1(X2,k8_tmap_1(sK0,X1)) )
              & u1_struct_0(X1) = u1_struct_0(X2)
              & m1_pre_topc(X2,k8_tmap_1(sK0,X1)) )
          & m1_pre_topc(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f4167,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ m1_pre_topc(X2,k8_tmap_1(sK0,X1))
              | ~ v1_tsep_1(X2,k8_tmap_1(sK0,X1)) )
            & u1_struct_0(X1) = u1_struct_0(X2)
            & m1_pre_topc(X2,k8_tmap_1(sK0,X1)) )
        & m1_pre_topc(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ( ~ m1_pre_topc(X2,k8_tmap_1(sK0,sK1))
            | ~ v1_tsep_1(X2,k8_tmap_1(sK0,sK1)) )
          & u1_struct_0(X2) = u1_struct_0(sK1)
          & m1_pre_topc(X2,k8_tmap_1(sK0,sK1)) )
      & m1_pre_topc(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f4168,plain,
    ( ? [X2] :
        ( ( ~ m1_pre_topc(X2,k8_tmap_1(sK0,sK1))
          | ~ v1_tsep_1(X2,k8_tmap_1(sK0,sK1)) )
        & u1_struct_0(X2) = u1_struct_0(sK1)
        & m1_pre_topc(X2,k8_tmap_1(sK0,sK1)) )
   => ( ( ~ m1_pre_topc(sK2,k8_tmap_1(sK0,sK1))
        | ~ v1_tsep_1(sK2,k8_tmap_1(sK0,sK1)) )
      & u1_struct_0(sK1) = u1_struct_0(sK2)
      & m1_pre_topc(sK2,k8_tmap_1(sK0,sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f3499,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_pre_topc(X2,k8_tmap_1(X0,X1))
                | ~ v1_tsep_1(X2,k8_tmap_1(X0,X1)) )
              & u1_struct_0(X1) = u1_struct_0(X2)
              & m1_pre_topc(X2,k8_tmap_1(X0,X1)) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3498])).

fof(f3498,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_pre_topc(X2,k8_tmap_1(X0,X1))
                | ~ v1_tsep_1(X2,k8_tmap_1(X0,X1)) )
              & u1_struct_0(X1) = u1_struct_0(X2)
              & m1_pre_topc(X2,k8_tmap_1(X0,X1)) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3383])).

fof(f3383,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( m1_pre_topc(X2,k8_tmap_1(X0,X1))
               => ( u1_struct_0(X1) = u1_struct_0(X2)
                 => ( m1_pre_topc(X2,k8_tmap_1(X0,X1))
                    & v1_tsep_1(X2,k8_tmap_1(X0,X1)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f3382])).

fof(f3382,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_pre_topc(X2,k8_tmap_1(X0,X1))
             => ( u1_struct_0(X1) = u1_struct_0(X2)
               => ( m1_pre_topc(X2,k8_tmap_1(X0,X1))
                  & v1_tsep_1(X2,k8_tmap_1(X0,X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t115_tmap_1)).

fof(f6090,plain,(
    spl241_9 ),
    inference(avatar_split_clause,[],[f4527,f6087])).

fof(f4527,plain,(
    u1_struct_0(sK1) = u1_struct_0(sK2) ),
    inference(cnf_transformation,[],[f4169])).

fof(f6080,plain,(
    spl241_7 ),
    inference(avatar_split_clause,[],[f4526,f6077])).

fof(f4526,plain,(
    m1_pre_topc(sK2,k8_tmap_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f4169])).

fof(f6070,plain,(
    spl241_5 ),
    inference(avatar_split_clause,[],[f4525,f6067])).

fof(f4525,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f4169])).

fof(f6065,plain,(
    ~ spl241_4 ),
    inference(avatar_split_clause,[],[f4524,f6062])).

fof(f4524,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f4169])).

fof(f6060,plain,(
    spl241_3 ),
    inference(avatar_split_clause,[],[f4523,f6057])).

fof(f4523,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f4169])).

fof(f6055,plain,(
    spl241_2 ),
    inference(avatar_split_clause,[],[f4522,f6052])).

fof(f4522,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f4169])).

fof(f6050,plain,(
    ~ spl241_1 ),
    inference(avatar_split_clause,[],[f4521,f6047])).

fof(f4521,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f4169])).
%------------------------------------------------------------------------------
