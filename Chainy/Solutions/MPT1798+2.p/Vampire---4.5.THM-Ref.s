%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1798+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:33 EST 2020

% Result     : Theorem 2.64s
% Output     : Refutation 2.64s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 494 expanded)
%              Number of leaves         :    9 ( 167 expanded)
%              Depth                    :   21
%              Number of atoms          :  356 (3944 expanded)
%              Number of equality atoms :  109 (1301 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4052,plain,(
    $false ),
    inference(subsumption_resolution,[],[f4050,f4028])).

fof(f4028,plain,(
    u1_pre_topc(k8_tmap_1(sK2,sK3)) != k5_tmap_1(sK2,sK4) ),
    inference(subsumption_resolution,[],[f3591,f4025])).

fof(f4025,plain,(
    u1_struct_0(sK2) = u1_struct_0(k8_tmap_1(sK2,sK3)) ),
    inference(forward_demodulation,[],[f4024,f3782])).

fof(f3782,plain,(
    k8_tmap_1(sK2,sK3) = k6_tmap_1(sK2,u1_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f3781,f3584])).

fof(f3584,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f3545])).

fof(f3545,plain,
    ( ( ( u1_pre_topc(k8_tmap_1(sK2,sK3)) != k5_tmap_1(sK2,sK4)
        & u1_struct_0(sK3) = sK4
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) )
      | u1_struct_0(sK2) != u1_struct_0(k8_tmap_1(sK2,sK3)) )
    & m1_pre_topc(sK3,sK2)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f3493,f3544,f3543,f3542])).

fof(f3542,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ? [X2] :
                  ( u1_pre_topc(k8_tmap_1(X0,X1)) != k5_tmap_1(X0,X2)
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | u1_struct_0(X0) != u1_struct_0(k8_tmap_1(X0,X1)) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ? [X2] :
                ( u1_pre_topc(k8_tmap_1(sK2,X1)) != k5_tmap_1(sK2,X2)
                & u1_struct_0(X1) = X2
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
            | u1_struct_0(sK2) != u1_struct_0(k8_tmap_1(sK2,X1)) )
          & m1_pre_topc(X1,sK2)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f3543,plain,
    ( ? [X1] :
        ( ( ? [X2] :
              ( u1_pre_topc(k8_tmap_1(sK2,X1)) != k5_tmap_1(sK2,X2)
              & u1_struct_0(X1) = X2
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
          | u1_struct_0(sK2) != u1_struct_0(k8_tmap_1(sK2,X1)) )
        & m1_pre_topc(X1,sK2)
        & ~ v2_struct_0(X1) )
   => ( ( ? [X2] :
            ( k5_tmap_1(sK2,X2) != u1_pre_topc(k8_tmap_1(sK2,sK3))
            & u1_struct_0(sK3) = X2
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
        | u1_struct_0(sK2) != u1_struct_0(k8_tmap_1(sK2,sK3)) )
      & m1_pre_topc(sK3,sK2)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f3544,plain,
    ( ? [X2] :
        ( k5_tmap_1(sK2,X2) != u1_pre_topc(k8_tmap_1(sK2,sK3))
        & u1_struct_0(sK3) = X2
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
   => ( u1_pre_topc(k8_tmap_1(sK2,sK3)) != k5_tmap_1(sK2,sK4)
      & u1_struct_0(sK3) = sK4
      & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f3493,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( u1_pre_topc(k8_tmap_1(X0,X1)) != k5_tmap_1(X0,X2)
                & u1_struct_0(X1) = X2
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | u1_struct_0(X0) != u1_struct_0(k8_tmap_1(X0,X1)) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3492])).

fof(f3492,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( u1_pre_topc(k8_tmap_1(X0,X1)) != k5_tmap_1(X0,X2)
                & u1_struct_0(X1) = X2
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | u1_struct_0(X0) != u1_struct_0(k8_tmap_1(X0,X1)) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3382])).

fof(f3382,negated_conjecture,(
    ~ ! [X0] :
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
    inference(negated_conjecture,[],[f3381])).

fof(f3381,conjecture,(
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

fof(f3781,plain,
    ( k8_tmap_1(sK2,sK3) = k6_tmap_1(sK2,u1_struct_0(sK3))
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f3780,f3585])).

fof(f3585,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f3545])).

fof(f3780,plain,
    ( k8_tmap_1(sK2,sK3) = k6_tmap_1(sK2,u1_struct_0(sK3))
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f3774,f3586])).

fof(f3586,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f3545])).

fof(f3774,plain,
    ( k8_tmap_1(sK2,sK3) = k6_tmap_1(sK2,u1_struct_0(sK3))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f3679,f3588])).

fof(f3588,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f3545])).

fof(f3679,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f3675,f3661])).

fof(f3661,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3534])).

fof(f3534,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3395])).

fof(f3395,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f3675,plain,(
    ! [X0,X1] :
      ( k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f3674,f3641])).

fof(f3641,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3516])).

fof(f3516,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3515])).

fof(f3515,plain,(
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

fof(f3674,plain,(
    ! [X0,X1] :
      ( k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f3673,f3642])).

fof(f3642,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3516])).

fof(f3673,plain,(
    ! [X0,X1] :
      ( k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f3672,f3643])).

fof(f3643,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3516])).

fof(f3672,plain,(
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
    inference(equality_resolution,[],[f3671])).

fof(f3671,plain,(
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
    inference(equality_resolution,[],[f3647])).

fof(f3647,plain,(
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
    inference(cnf_transformation,[],[f3576])).

fof(f3576,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k8_tmap_1(X0,X1) = X2
                  | ( k6_tmap_1(X0,sK19(X0,X1,X2)) != X2
                    & u1_struct_0(X1) = sK19(X0,X1,X2)
                    & m1_subset_1(sK19(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK19])],[f3574,f3575])).

fof(f3575,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k6_tmap_1(X0,X3) != X2
          & u1_struct_0(X1) = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k6_tmap_1(X0,sK19(X0,X1,X2)) != X2
        & u1_struct_0(X1) = sK19(X0,X1,X2)
        & m1_subset_1(sK19(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f3574,plain,(
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
    inference(rectify,[],[f3573])).

fof(f3573,plain,(
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
    inference(nnf_transformation,[],[f3520])).

fof(f3520,plain,(
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
    inference(flattening,[],[f3519])).

fof(f3519,plain,(
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

fof(f4024,plain,(
    u1_struct_0(sK2) = u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))) ),
    inference(subsumption_resolution,[],[f4023,f3584])).

fof(f4023,plain,
    ( v2_struct_0(sK2)
    | u1_struct_0(sK2) = u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))) ),
    inference(subsumption_resolution,[],[f4022,f3585])).

fof(f4022,plain,
    ( ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | u1_struct_0(sK2) = u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))) ),
    inference(subsumption_resolution,[],[f4014,f3586])).

fof(f4014,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | u1_struct_0(sK2) = u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))) ),
    inference(resolution,[],[f3789,f3588])).

fof(f3789,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))) ) ),
    inference(duplicate_literal_removal,[],[f3786])).

fof(f3786,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f3595,f3661])).

fof(f3595,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3499])).

fof(f3499,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3498])).

fof(f3498,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3371])).

fof(f3371,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_tmap_1)).

fof(f3591,plain,
    ( u1_pre_topc(k8_tmap_1(sK2,sK3)) != k5_tmap_1(sK2,sK4)
    | u1_struct_0(sK2) != u1_struct_0(k8_tmap_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f3545])).

fof(f4050,plain,(
    u1_pre_topc(k8_tmap_1(sK2,sK3)) = k5_tmap_1(sK2,sK4) ),
    inference(backward_demodulation,[],[f4033,f4037])).

fof(f4037,plain,(
    k8_tmap_1(sK2,sK3) = k6_tmap_1(sK2,sK4) ),
    inference(backward_demodulation,[],[f3782,f4027])).

fof(f4027,plain,(
    u1_struct_0(sK3) = sK4 ),
    inference(subsumption_resolution,[],[f3590,f4025])).

fof(f3590,plain,
    ( u1_struct_0(sK2) != u1_struct_0(k8_tmap_1(sK2,sK3))
    | u1_struct_0(sK3) = sK4 ),
    inference(cnf_transformation,[],[f3545])).

fof(f4033,plain,(
    k5_tmap_1(sK2,sK4) = u1_pre_topc(k6_tmap_1(sK2,sK4)) ),
    inference(subsumption_resolution,[],[f3806,f4025])).

fof(f3806,plain,
    ( u1_struct_0(sK2) != u1_struct_0(k8_tmap_1(sK2,sK3))
    | k5_tmap_1(sK2,sK4) = u1_pre_topc(k6_tmap_1(sK2,sK4)) ),
    inference(subsumption_resolution,[],[f3805,f3584])).

fof(f3805,plain,
    ( k5_tmap_1(sK2,sK4) = u1_pre_topc(k6_tmap_1(sK2,sK4))
    | v2_struct_0(sK2)
    | u1_struct_0(sK2) != u1_struct_0(k8_tmap_1(sK2,sK3)) ),
    inference(subsumption_resolution,[],[f3804,f3585])).

fof(f3804,plain,
    ( k5_tmap_1(sK2,sK4) = u1_pre_topc(k6_tmap_1(sK2,sK4))
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | u1_struct_0(sK2) != u1_struct_0(k8_tmap_1(sK2,sK3)) ),
    inference(subsumption_resolution,[],[f3801,f3586])).

fof(f3801,plain,
    ( k5_tmap_1(sK2,sK4) = u1_pre_topc(k6_tmap_1(sK2,sK4))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | u1_struct_0(sK2) != u1_struct_0(k8_tmap_1(sK2,sK3)) ),
    inference(resolution,[],[f3596,f3589])).

fof(f3589,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | u1_struct_0(sK2) != u1_struct_0(k8_tmap_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f3545])).

fof(f3596,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3499])).
%------------------------------------------------------------------------------
