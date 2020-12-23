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
% DateTime   : Thu Dec  3 13:19:29 EST 2020

% Result     : Theorem 5.45s
% Output     : Refutation 5.45s
% Verified   : 
% Statistics : Number of formulae       :  258 (29751 expanded)
%              Number of leaves         :   19 (7874 expanded)
%              Depth                    :   57
%              Number of atoms          : 1018 (295383 expanded)
%              Number of equality atoms :  147 (5275 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12914,plain,(
    $false ),
    inference(subsumption_resolution,[],[f12913,f8881])).

fof(f8881,plain,(
    m1_subset_1(sK6(sK4,k6_partfun1(k2_struct_0(sK4)),k6_tmap_1(sK4,sK5)),k1_zfmisc_1(k2_struct_0(sK4))) ),
    inference(resolution,[],[f8870,f619])).

fof(f619,plain,(
    ! [X10,X9] :
      ( sP0(X9,X10,k6_tmap_1(sK4,sK5))
      | m1_subset_1(sK6(X9,X10,k6_tmap_1(sK4,sK5)),k1_zfmisc_1(k2_struct_0(sK4))) ) ),
    inference(superposition,[],[f88,f574])).

fof(f574,plain,(
    u1_struct_0(k6_tmap_1(sK4,sK5)) = k2_struct_0(sK4) ),
    inference(forward_demodulation,[],[f247,f215])).

fof(f215,plain,(
    u1_struct_0(sK4) = k2_struct_0(sK4) ),
    inference(resolution,[],[f166,f83])).

fof(f83,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f166,plain,(
    l1_struct_0(sK4) ),
    inference(resolution,[],[f76,f84])).

fof(f84,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f76,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,
    ( ( ~ m1_subset_1(k7_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK5)))))
      | ~ v5_pre_topc(k7_tmap_1(sK4,sK5),sK4,k6_tmap_1(sK4,sK5))
      | ~ v1_funct_2(k7_tmap_1(sK4,sK5),u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK5)))
      | ~ v1_funct_1(k7_tmap_1(sK4,sK5))
      | ~ v3_pre_topc(sK5,sK4) )
    & ( ( m1_subset_1(k7_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK5)))))
        & v5_pre_topc(k7_tmap_1(sK4,sK5),sK4,k6_tmap_1(sK4,sK5))
        & v1_funct_2(k7_tmap_1(sK4,sK5),u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK5)))
        & v1_funct_1(k7_tmap_1(sK4,sK5)) )
      | v3_pre_topc(sK5,sK4) )
    & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f55,f57,f56])).

fof(f56,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
              | ~ v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
              | ~ v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
              | ~ v1_funct_1(k7_tmap_1(X0,X1))
              | ~ v3_pre_topc(X1,X0) )
            & ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
                & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
                & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
                & v1_funct_1(k7_tmap_1(X0,X1)) )
              | v3_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ m1_subset_1(k7_tmap_1(sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,X1)))))
            | ~ v5_pre_topc(k7_tmap_1(sK4,X1),sK4,k6_tmap_1(sK4,X1))
            | ~ v1_funct_2(k7_tmap_1(sK4,X1),u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,X1)))
            | ~ v1_funct_1(k7_tmap_1(sK4,X1))
            | ~ v3_pre_topc(X1,sK4) )
          & ( ( m1_subset_1(k7_tmap_1(sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,X1)))))
              & v5_pre_topc(k7_tmap_1(sK4,X1),sK4,k6_tmap_1(sK4,X1))
              & v1_funct_2(k7_tmap_1(sK4,X1),u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,X1)))
              & v1_funct_1(k7_tmap_1(sK4,X1)) )
            | v3_pre_topc(X1,sK4) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) )
      & l1_pre_topc(sK4)
      & v2_pre_topc(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,
    ( ? [X1] :
        ( ( ~ m1_subset_1(k7_tmap_1(sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,X1)))))
          | ~ v5_pre_topc(k7_tmap_1(sK4,X1),sK4,k6_tmap_1(sK4,X1))
          | ~ v1_funct_2(k7_tmap_1(sK4,X1),u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,X1)))
          | ~ v1_funct_1(k7_tmap_1(sK4,X1))
          | ~ v3_pre_topc(X1,sK4) )
        & ( ( m1_subset_1(k7_tmap_1(sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,X1)))))
            & v5_pre_topc(k7_tmap_1(sK4,X1),sK4,k6_tmap_1(sK4,X1))
            & v1_funct_2(k7_tmap_1(sK4,X1),u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,X1)))
            & v1_funct_1(k7_tmap_1(sK4,X1)) )
          | v3_pre_topc(X1,sK4) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) )
   => ( ( ~ m1_subset_1(k7_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK5)))))
        | ~ v5_pre_topc(k7_tmap_1(sK4,sK5),sK4,k6_tmap_1(sK4,sK5))
        | ~ v1_funct_2(k7_tmap_1(sK4,sK5),u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK5)))
        | ~ v1_funct_1(k7_tmap_1(sK4,sK5))
        | ~ v3_pre_topc(sK5,sK4) )
      & ( ( m1_subset_1(k7_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK5)))))
          & v5_pre_topc(k7_tmap_1(sK4,sK5),sK4,k6_tmap_1(sK4,sK5))
          & v1_funct_2(k7_tmap_1(sK4,sK5),u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK5)))
          & v1_funct_1(k7_tmap_1(sK4,sK5)) )
        | v3_pre_topc(sK5,sK4) )
      & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
            | ~ v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
            | ~ v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
            | ~ v1_funct_1(k7_tmap_1(X0,X1))
            | ~ v3_pre_topc(X1,X0) )
          & ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
              & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
              & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
              & v1_funct_1(k7_tmap_1(X0,X1)) )
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
            | ~ v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
            | ~ v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
            | ~ v1_funct_1(k7_tmap_1(X0,X1))
            | ~ v3_pre_topc(X1,X0) )
          & ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
              & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
              & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
              & v1_funct_1(k7_tmap_1(X0,X1)) )
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
              & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
              & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
              & v1_funct_1(k7_tmap_1(X0,X1)) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
              & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
              & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
              & v1_funct_1(k7_tmap_1(X0,X1)) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
                & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
                & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
                & v1_funct_1(k7_tmap_1(X0,X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
              & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
              & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
              & v1_funct_1(k7_tmap_1(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_tmap_1)).

fof(f247,plain,(
    u1_struct_0(sK4) = u1_struct_0(k6_tmap_1(sK4,sK5)) ),
    inference(subsumption_resolution,[],[f246,f74])).

fof(f74,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f58])).

fof(f246,plain,
    ( u1_struct_0(sK4) = u1_struct_0(k6_tmap_1(sK4,sK5))
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f245,f75])).

fof(f75,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f58])).

fof(f245,plain,
    ( u1_struct_0(sK4) = u1_struct_0(k6_tmap_1(sK4,sK5))
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f225,f76])).

fof(f225,plain,
    ( u1_struct_0(sK4) = u1_struct_0(k6_tmap_1(sK4,sK5))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4) ),
    inference(resolution,[],[f77,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
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
         => ( k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_tmap_1)).

fof(f77,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f58])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,sK6(X0,X1,X2)),X0)
          & v3_pre_topc(sK6(X0,X1,X2),X2)
          & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) ) )
      & ( ! [X4] :
            ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,X4),X0)
            | ~ v3_pre_topc(X4,X2)
            | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2))) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f62,f63])).

fof(f63,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,X3),X0)
          & v3_pre_topc(X3,X2)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
     => ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,sK6(X0,X1,X2)),X0)
        & v3_pre_topc(sK6(X0,X1,X2),X2)
        & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,X3),X0)
            & v3_pre_topc(X3,X2)
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) )
      & ( ! [X4] :
            ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,X4),X0)
            | ~ v3_pre_topc(X4,X2)
            | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2))) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f61])).

fof(f61,plain,(
    ! [X0,X2,X1] :
      ( ( sP0(X0,X2,X1)
        | ? [X3] :
            ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
            & v3_pre_topc(X3,X1)
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
      & ( ! [X3] :
            ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
            | ~ v3_pre_topc(X3,X1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ sP0(X0,X2,X1) ) ) ),
    inference(nnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X2,X1] :
      ( sP0(X0,X2,X1)
    <=> ! [X3] :
          ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
          | ~ v3_pre_topc(X3,X1)
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f8870,plain,(
    ~ sP0(sK4,k6_partfun1(k2_struct_0(sK4)),k6_tmap_1(sK4,sK5)) ),
    inference(subsumption_resolution,[],[f8869,f656])).

fof(f656,plain,(
    m1_subset_1(k6_partfun1(k2_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK4),k2_struct_0(sK4)))) ),
    inference(forward_demodulation,[],[f655,f573])).

fof(f573,plain,(
    k7_tmap_1(sK4,sK5) = k6_partfun1(k2_struct_0(sK4)) ),
    inference(forward_demodulation,[],[f244,f215])).

fof(f244,plain,(
    k7_tmap_1(sK4,sK5) = k6_partfun1(u1_struct_0(sK4)) ),
    inference(subsumption_resolution,[],[f243,f74])).

fof(f243,plain,
    ( k7_tmap_1(sK4,sK5) = k6_partfun1(u1_struct_0(sK4))
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f242,f75])).

fof(f242,plain,
    ( k7_tmap_1(sK4,sK5) = k6_partfun1(u1_struct_0(sK4))
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f224,f76])).

fof(f224,plain,
    ( k7_tmap_1(sK4,sK5) = k6_partfun1(u1_struct_0(sK4))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4) ),
    inference(resolution,[],[f77,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_tmap_1)).

fof(f655,plain,(
    m1_subset_1(k7_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK4),k2_struct_0(sK4)))) ),
    inference(forward_demodulation,[],[f654,f215])).

fof(f654,plain,(
    m1_subset_1(k7_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),k2_struct_0(sK4)))) ),
    inference(subsumption_resolution,[],[f612,f277])).

fof(f277,plain,(
    sP3(sK5,sK4) ),
    inference(subsumption_resolution,[],[f276,f74])).

fof(f276,plain,
    ( sP3(sK5,sK4)
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f275,f75])).

fof(f275,plain,
    ( sP3(sK5,sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f235,f76])).

fof(f235,plain,
    ( sP3(sK5,sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4) ),
    inference(resolution,[],[f77,f115])).

fof(f115,plain,(
    ! [X0,X1] :
      ( sP3(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( sP3(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f46,f52])).

fof(f52,plain,(
    ! [X1,X0] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ sP3(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_tmap_1)).

fof(f612,plain,
    ( m1_subset_1(k7_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),k2_struct_0(sK4))))
    | ~ sP3(sK5,sK4) ),
    inference(superposition,[],[f114,f574])).

fof(f114,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
      | ~ sP3(X0,X1) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
        & v1_funct_2(k7_tmap_1(X1,X0),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))
        & v1_funct_1(k7_tmap_1(X1,X0)) )
      | ~ sP3(X0,X1) ) ),
    inference(rectify,[],[f69])).

fof(f69,plain,(
    ! [X1,X0] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ sP3(X1,X0) ) ),
    inference(nnf_transformation,[],[f52])).

fof(f8869,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK4),k2_struct_0(sK4))))
    | ~ sP0(sK4,k6_partfun1(k2_struct_0(sK4)),k6_tmap_1(sK4,sK5)) ),
    inference(forward_demodulation,[],[f8868,f215])).

fof(f8868,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),k2_struct_0(sK4))))
    | ~ sP0(sK4,k6_partfun1(k2_struct_0(sK4)),k6_tmap_1(sK4,sK5)) ),
    inference(subsumption_resolution,[],[f8867,f653])).

fof(f653,plain,(
    v1_funct_2(k6_partfun1(k2_struct_0(sK4)),k2_struct_0(sK4),k2_struct_0(sK4)) ),
    inference(forward_demodulation,[],[f652,f573])).

fof(f652,plain,(
    v1_funct_2(k7_tmap_1(sK4,sK5),k2_struct_0(sK4),k2_struct_0(sK4)) ),
    inference(forward_demodulation,[],[f651,f215])).

fof(f651,plain,(
    v1_funct_2(k7_tmap_1(sK4,sK5),u1_struct_0(sK4),k2_struct_0(sK4)) ),
    inference(subsumption_resolution,[],[f611,f277])).

fof(f611,plain,
    ( v1_funct_2(k7_tmap_1(sK4,sK5),u1_struct_0(sK4),k2_struct_0(sK4))
    | ~ sP3(sK5,sK4) ),
    inference(superposition,[],[f113,f574])).

fof(f113,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k7_tmap_1(X1,X0),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))
      | ~ sP3(X0,X1) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f8867,plain,
    ( ~ v1_funct_2(k6_partfun1(k2_struct_0(sK4)),k2_struct_0(sK4),k2_struct_0(sK4))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),k2_struct_0(sK4))))
    | ~ sP0(sK4,k6_partfun1(k2_struct_0(sK4)),k6_tmap_1(sK4,sK5)) ),
    inference(forward_demodulation,[],[f8866,f215])).

fof(f8866,plain,
    ( ~ v1_funct_2(k6_partfun1(k2_struct_0(sK4)),u1_struct_0(sK4),k2_struct_0(sK4))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),k2_struct_0(sK4))))
    | ~ sP0(sK4,k6_partfun1(k2_struct_0(sK4)),k6_tmap_1(sK4,sK5)) ),
    inference(subsumption_resolution,[],[f8865,f7842])).

fof(f7842,plain,
    ( ~ sP0(sK4,k6_partfun1(k2_struct_0(sK4)),k6_tmap_1(sK4,sK5))
    | k1_xboole_0 = k2_struct_0(sK4) ),
    inference(forward_demodulation,[],[f7841,f650])).

fof(f650,plain,(
    k2_struct_0(sK4) = k2_struct_0(k6_tmap_1(sK4,sK5)) ),
    inference(subsumption_resolution,[],[f610,f342])).

fof(f342,plain,(
    l1_struct_0(k6_tmap_1(sK4,sK5)) ),
    inference(resolution,[],[f274,f84])).

fof(f274,plain,(
    l1_pre_topc(k6_tmap_1(sK4,sK5)) ),
    inference(subsumption_resolution,[],[f273,f74])).

fof(f273,plain,
    ( l1_pre_topc(k6_tmap_1(sK4,sK5))
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f272,f75])).

fof(f272,plain,
    ( l1_pre_topc(k6_tmap_1(sK4,sK5))
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f234,f76])).

fof(f234,plain,
    ( l1_pre_topc(k6_tmap_1(sK4,sK5))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4) ),
    inference(resolution,[],[f77,f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
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
    inference(pure_predicate_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_tmap_1)).

fof(f610,plain,
    ( k2_struct_0(sK4) = k2_struct_0(k6_tmap_1(sK4,sK5))
    | ~ l1_struct_0(k6_tmap_1(sK4,sK5)) ),
    inference(superposition,[],[f574,f83])).

fof(f7841,plain,
    ( ~ sP0(sK4,k6_partfun1(k2_struct_0(sK4)),k6_tmap_1(sK4,sK5))
    | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK4,sK5)) ),
    inference(subsumption_resolution,[],[f7840,f653])).

fof(f7840,plain,
    ( ~ v1_funct_2(k6_partfun1(k2_struct_0(sK4)),k2_struct_0(sK4),k2_struct_0(sK4))
    | ~ sP0(sK4,k6_partfun1(k2_struct_0(sK4)),k6_tmap_1(sK4,sK5))
    | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK4,sK5)) ),
    inference(forward_demodulation,[],[f7839,f574])).

fof(f7839,plain,
    ( ~ sP0(sK4,k6_partfun1(k2_struct_0(sK4)),k6_tmap_1(sK4,sK5))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK4)),k2_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK5)))
    | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK4,sK5)) ),
    inference(subsumption_resolution,[],[f7838,f656])).

fof(f7838,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK4),k2_struct_0(sK4))))
    | ~ sP0(sK4,k6_partfun1(k2_struct_0(sK4)),k6_tmap_1(sK4,sK5))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK4)),k2_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK5)))
    | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK4,sK5)) ),
    inference(forward_demodulation,[],[f7837,f574])).

fof(f7837,plain,
    ( ~ sP0(sK4,k6_partfun1(k2_struct_0(sK4)),k6_tmap_1(sK4,sK5))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK5)))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK4)),k2_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK5)))
    | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK4,sK5)) ),
    inference(subsumption_resolution,[],[f7836,f274])).

fof(f7836,plain,
    ( ~ sP0(sK4,k6_partfun1(k2_struct_0(sK4)),k6_tmap_1(sK4,sK5))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK5)))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK4)),k2_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK5)))
    | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK4,sK5))
    | ~ l1_pre_topc(k6_tmap_1(sK4,sK5)) ),
    inference(subsumption_resolution,[],[f7831,f420])).

fof(f420,plain,(
    v1_funct_1(k6_partfun1(k2_struct_0(sK4))) ),
    inference(subsumption_resolution,[],[f419,f166])).

fof(f419,plain,
    ( v1_funct_1(k6_partfun1(k2_struct_0(sK4)))
    | ~ l1_struct_0(sK4) ),
    inference(superposition,[],[f397,f83])).

fof(f397,plain,(
    v1_funct_1(k6_partfun1(u1_struct_0(sK4))) ),
    inference(subsumption_resolution,[],[f396,f74])).

fof(f396,plain,
    ( v1_funct_1(k6_partfun1(u1_struct_0(sK4)))
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f395,f75])).

fof(f395,plain,
    ( v1_funct_1(k6_partfun1(u1_struct_0(sK4)))
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f394,f76])).

fof(f394,plain,
    ( v1_funct_1(k6_partfun1(u1_struct_0(sK4)))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f393,f77])).

fof(f393,plain,
    ( v1_funct_1(k6_partfun1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4) ),
    inference(superposition,[],[f282,f99])).

fof(f282,plain,(
    v1_funct_1(k7_tmap_1(sK4,sK5)) ),
    inference(resolution,[],[f277,f112])).

fof(f112,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_tmap_1(X1,X0))
      | ~ sP3(X0,X1) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f7831,plain,
    ( ~ sP0(sK4,k6_partfun1(k2_struct_0(sK4)),k6_tmap_1(sK4,sK5))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK5)))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK4)),k2_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK5)))
    | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK4,sK5))
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK4)))
    | ~ l1_pre_topc(k6_tmap_1(sK4,sK5)) ),
    inference(resolution,[],[f7720,f4243])).

fof(f4243,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1,sK4)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK4),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,k2_struct_0(sK4),u1_struct_0(X0))
      | k2_struct_0(X0) = k1_xboole_0
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(forward_demodulation,[],[f4242,f215])).

fof(f4242,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK4),u1_struct_0(X0))))
      | sP1(X0,X1,sK4)
      | k2_struct_0(X0) = k1_xboole_0
      | ~ v1_funct_2(X1,u1_struct_0(sK4),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(forward_demodulation,[],[f167,f215])).

fof(f167,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1,sK4)
      | k2_struct_0(X0) = k1_xboole_0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK4),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f76,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( sP1(X1,X2,X0)
      | k2_struct_0(X1) = k1_xboole_0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP1(X1,X2,X0)
              | ( k2_struct_0(X0) != k1_xboole_0
                & k2_struct_0(X1) = k1_xboole_0 )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f26,f48,f47])).

fof(f48,plain,(
    ! [X1,X2,X0] :
      ( ( v5_pre_topc(X2,X0,X1)
      <=> sP0(X0,X2,X1) )
      | ~ sP1(X1,X2,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v3_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ( k2_struct_0(X0) != k1_xboole_0
                & k2_struct_0(X1) = k1_xboole_0 )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v3_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ( k2_struct_0(X0) != k1_xboole_0
                & k2_struct_0(X1) = k1_xboole_0 )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( k2_struct_0(X1) = k1_xboole_0
                 => k2_struct_0(X0) = k1_xboole_0 )
               => ( v5_pre_topc(X2,X0,X1)
                <=> ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                     => ( v3_pre_topc(X3,X1)
                       => v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_2)).

fof(f7720,plain,
    ( ~ sP1(k6_tmap_1(sK4,sK5),k6_partfun1(k2_struct_0(sK4)),sK4)
    | ~ sP0(sK4,k6_partfun1(k2_struct_0(sK4)),k6_tmap_1(sK4,sK5)) ),
    inference(subsumption_resolution,[],[f4657,f7589])).

fof(f7589,plain,
    ( ~ sP1(k6_tmap_1(sK4,sK5),k6_partfun1(k2_struct_0(sK4)),sK4)
    | k6_tmap_1(sK4,sK5) = g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4)) ),
    inference(subsumption_resolution,[],[f7588,f1437])).

fof(f1437,plain,
    ( k6_tmap_1(sK4,sK5) = g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4))
    | ~ v3_pre_topc(sK5,sK4) ),
    inference(forward_demodulation,[],[f253,f215])).

fof(f253,plain,
    ( k6_tmap_1(sK4,sK5) = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))
    | ~ v3_pre_topc(sK5,sK4) ),
    inference(subsumption_resolution,[],[f252,f74])).

fof(f252,plain,
    ( k6_tmap_1(sK4,sK5) = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))
    | ~ v3_pre_topc(sK5,sK4)
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f251,f75])).

fof(f251,plain,
    ( k6_tmap_1(sK4,sK5) = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))
    | ~ v3_pre_topc(sK5,sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f227,f76])).

fof(f227,plain,
    ( k6_tmap_1(sK4,sK5) = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))
    | ~ v3_pre_topc(sK5,sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4) ),
    inference(resolution,[],[f77,f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | k6_tmap_1(X0,X1) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) )
            & ( k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_tmap_1)).

fof(f7588,plain,
    ( v3_pre_topc(sK5,sK4)
    | k6_tmap_1(sK4,sK5) = g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4))
    | ~ sP1(k6_tmap_1(sK4,sK5),k6_partfun1(k2_struct_0(sK4)),sK4) ),
    inference(forward_demodulation,[],[f7587,f1172])).

fof(f1172,plain,(
    sK5 = k8_relset_1(k2_struct_0(sK4),k2_struct_0(sK4),k6_partfun1(k2_struct_0(sK4)),sK5) ),
    inference(forward_demodulation,[],[f238,f215])).

fof(f238,plain,(
    sK5 = k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK4),k6_partfun1(u1_struct_0(sK4)),sK5) ),
    inference(resolution,[],[f77,f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_2)).

fof(f7587,plain,
    ( v3_pre_topc(k8_relset_1(k2_struct_0(sK4),k2_struct_0(sK4),k6_partfun1(k2_struct_0(sK4)),sK5),sK4)
    | k6_tmap_1(sK4,sK5) = g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4))
    | ~ sP1(k6_tmap_1(sK4,sK5),k6_partfun1(k2_struct_0(sK4)),sK4) ),
    inference(forward_demodulation,[],[f7582,f215])).

fof(f7582,plain,
    ( k6_tmap_1(sK4,sK5) = g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4))
    | ~ sP1(k6_tmap_1(sK4,sK5),k6_partfun1(k2_struct_0(sK4)),sK4)
    | v3_pre_topc(k8_relset_1(u1_struct_0(sK4),k2_struct_0(sK4),k6_partfun1(k2_struct_0(sK4)),sK5),sK4) ),
    inference(resolution,[],[f3272,f734])).

fof(f734,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1,k6_tmap_1(sK4,sK5))
      | v3_pre_topc(k8_relset_1(u1_struct_0(X0),k2_struct_0(sK4),X1,sK5),X0) ) ),
    inference(subsumption_resolution,[],[f733,f281])).

fof(f281,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_struct_0(sK4))) ),
    inference(subsumption_resolution,[],[f239,f166])).

fof(f239,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_struct_0(sK4)))
    | ~ l1_struct_0(sK4) ),
    inference(superposition,[],[f77,f83])).

fof(f733,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_struct_0(sK4)))
      | v3_pre_topc(k8_relset_1(u1_struct_0(X0),k2_struct_0(sK4),X1,sK5),X0)
      | ~ sP0(X0,X1,k6_tmap_1(sK4,sK5)) ) ),
    inference(forward_demodulation,[],[f732,f574])).

fof(f732,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),k2_struct_0(sK4),X1,sK5),X0)
      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK4,sK5))))
      | ~ sP0(X0,X1,k6_tmap_1(sK4,sK5)) ) ),
    inference(forward_demodulation,[],[f722,f574])).

fof(f722,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(sK4,sK5)),X1,sK5),X0)
      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK4,sK5))))
      | ~ sP0(X0,X1,k6_tmap_1(sK4,sK5)) ) ),
    inference(resolution,[],[f662,f87])).

fof(f87,plain,(
    ! [X4,X2,X0,X1] :
      ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,X4),X0)
      | ~ v3_pre_topc(X4,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f662,plain,(
    v3_pre_topc(sK5,k6_tmap_1(sK4,sK5)) ),
    inference(subsumption_resolution,[],[f661,f281])).

fof(f661,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_struct_0(sK4)))
    | v3_pre_topc(sK5,k6_tmap_1(sK4,sK5)) ),
    inference(forward_demodulation,[],[f660,f215])).

fof(f660,plain,
    ( v3_pre_topc(sK5,k6_tmap_1(sK4,sK5))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(subsumption_resolution,[],[f659,f74])).

fof(f659,plain,
    ( v3_pre_topc(sK5,k6_tmap_1(sK4,sK5))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f658,f75])).

fof(f658,plain,
    ( v3_pre_topc(sK5,k6_tmap_1(sK4,sK5))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f657,f76])).

fof(f657,plain,
    ( v3_pre_topc(sK5,k6_tmap_1(sK4,sK5))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f613,f281])).

fof(f613,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_struct_0(sK4)))
    | v3_pre_topc(sK5,k6_tmap_1(sK4,sK5))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4) ),
    inference(superposition,[],[f121,f574])).

fof(f121,plain,(
    ! [X2,X0] :
      ( v3_pre_topc(X2,k6_tmap_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X2))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f106])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(X2,k6_tmap_1(X0,X1))
      | X1 != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f38,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_tmap_1)).

fof(f3272,plain,
    ( sP0(sK4,k6_partfun1(k2_struct_0(sK4)),k6_tmap_1(sK4,sK5))
    | k6_tmap_1(sK4,sK5) = g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4))
    | ~ sP1(k6_tmap_1(sK4,sK5),k6_partfun1(k2_struct_0(sK4)),sK4) ),
    inference(resolution,[],[f602,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X1,X0)
      | ~ v5_pre_topc(X1,X2,X0)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( ( ( v5_pre_topc(X1,X2,X0)
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | ~ v5_pre_topc(X1,X2,X0) ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f59])).

fof(f59,plain,(
    ! [X1,X2,X0] :
      ( ( ( v5_pre_topc(X2,X0,X1)
          | ~ sP0(X0,X2,X1) )
        & ( sP0(X0,X2,X1)
          | ~ v5_pre_topc(X2,X0,X1) ) )
      | ~ sP1(X1,X2,X0) ) ),
    inference(nnf_transformation,[],[f48])).

fof(f602,plain,
    ( v5_pre_topc(k6_partfun1(k2_struct_0(sK4)),sK4,k6_tmap_1(sK4,sK5))
    | k6_tmap_1(sK4,sK5) = g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4)) ),
    inference(subsumption_resolution,[],[f601,f281])).

fof(f601,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_struct_0(sK4)))
    | k6_tmap_1(sK4,sK5) = g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4))
    | v5_pre_topc(k6_partfun1(k2_struct_0(sK4)),sK4,k6_tmap_1(sK4,sK5)) ),
    inference(forward_demodulation,[],[f600,f215])).

fof(f600,plain,
    ( k6_tmap_1(sK4,sK5) = g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4))
    | v5_pre_topc(k6_partfun1(k2_struct_0(sK4)),sK4,k6_tmap_1(sK4,sK5))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(forward_demodulation,[],[f599,f215])).

fof(f599,plain,
    ( v5_pre_topc(k6_partfun1(k2_struct_0(sK4)),sK4,k6_tmap_1(sK4,sK5))
    | k6_tmap_1(sK4,sK5) = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(subsumption_resolution,[],[f598,f74])).

fof(f598,plain,
    ( v5_pre_topc(k6_partfun1(k2_struct_0(sK4)),sK4,k6_tmap_1(sK4,sK5))
    | k6_tmap_1(sK4,sK5) = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f597,f75])).

fof(f597,plain,
    ( v5_pre_topc(k6_partfun1(k2_struct_0(sK4)),sK4,k6_tmap_1(sK4,sK5))
    | k6_tmap_1(sK4,sK5) = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f594,f76])).

fof(f594,plain,
    ( v5_pre_topc(k6_partfun1(k2_struct_0(sK4)),sK4,k6_tmap_1(sK4,sK5))
    | k6_tmap_1(sK4,sK5) = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4) ),
    inference(resolution,[],[f576,f102])).

fof(f576,plain,
    ( v3_pre_topc(sK5,sK4)
    | v5_pre_topc(k6_partfun1(k2_struct_0(sK4)),sK4,k6_tmap_1(sK4,sK5)) ),
    inference(backward_demodulation,[],[f80,f573])).

fof(f80,plain,
    ( v3_pre_topc(sK5,sK4)
    | v5_pre_topc(k7_tmap_1(sK4,sK5),sK4,k6_tmap_1(sK4,sK5)) ),
    inference(cnf_transformation,[],[f58])).

fof(f4657,plain,
    ( k6_tmap_1(sK4,sK5) != g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4))
    | ~ sP0(sK4,k6_partfun1(k2_struct_0(sK4)),k6_tmap_1(sK4,sK5))
    | ~ sP1(k6_tmap_1(sK4,sK5),k6_partfun1(k2_struct_0(sK4)),sK4) ),
    inference(resolution,[],[f4631,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X1,X2,X0)
      | ~ sP0(X2,X1,X0)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f4631,plain,
    ( ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK4)),sK4,k6_tmap_1(sK4,sK5))
    | k6_tmap_1(sK4,sK5) != g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4)) ),
    inference(subsumption_resolution,[],[f860,f656])).

fof(f860,plain,
    ( k6_tmap_1(sK4,sK5) != g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK4),k2_struct_0(sK4))))
    | ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK4)),sK4,k6_tmap_1(sK4,sK5)) ),
    inference(subsumption_resolution,[],[f859,f281])).

fof(f859,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_struct_0(sK4)))
    | k6_tmap_1(sK4,sK5) != g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK4),k2_struct_0(sK4))))
    | ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK4)),sK4,k6_tmap_1(sK4,sK5)) ),
    inference(forward_demodulation,[],[f858,f215])).

fof(f858,plain,
    ( k6_tmap_1(sK4,sK5) != g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK4),k2_struct_0(sK4))))
    | ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK4)),sK4,k6_tmap_1(sK4,sK5))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(forward_demodulation,[],[f857,f215])).

fof(f857,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK4),k2_struct_0(sK4))))
    | ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK4)),sK4,k6_tmap_1(sK4,sK5))
    | k6_tmap_1(sK4,sK5) != g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(subsumption_resolution,[],[f856,f74])).

fof(f856,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK4),k2_struct_0(sK4))))
    | ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK4)),sK4,k6_tmap_1(sK4,sK5))
    | k6_tmap_1(sK4,sK5) != g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f855,f75])).

fof(f855,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK4),k2_struct_0(sK4))))
    | ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK4)),sK4,k6_tmap_1(sK4,sK5))
    | k6_tmap_1(sK4,sK5) != g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f853,f76])).

fof(f853,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK4),k2_struct_0(sK4))))
    | ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK4)),sK4,k6_tmap_1(sK4,sK5))
    | k6_tmap_1(sK4,sK5) != g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4) ),
    inference(resolution,[],[f847,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | k6_tmap_1(X0,X1) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f847,plain,
    ( ~ v3_pre_topc(sK5,sK4)
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK4),k2_struct_0(sK4))))
    | ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK4)),sK4,k6_tmap_1(sK4,sK5)) ),
    inference(subsumption_resolution,[],[f846,f420])).

fof(f846,plain,
    ( ~ v1_funct_1(k6_partfun1(k2_struct_0(sK4)))
    | ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK4)),sK4,k6_tmap_1(sK4,sK5))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK4),k2_struct_0(sK4))))
    | ~ v3_pre_topc(sK5,sK4) ),
    inference(forward_demodulation,[],[f845,f573])).

fof(f845,plain,
    ( ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK4)),sK4,k6_tmap_1(sK4,sK5))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK4),k2_struct_0(sK4))))
    | ~ v1_funct_1(k7_tmap_1(sK4,sK5))
    | ~ v3_pre_topc(sK5,sK4) ),
    inference(subsumption_resolution,[],[f844,f653])).

fof(f844,plain,
    ( ~ v1_funct_2(k6_partfun1(k2_struct_0(sK4)),k2_struct_0(sK4),k2_struct_0(sK4))
    | ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK4)),sK4,k6_tmap_1(sK4,sK5))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK4),k2_struct_0(sK4))))
    | ~ v1_funct_1(k7_tmap_1(sK4,sK5))
    | ~ v3_pre_topc(sK5,sK4) ),
    inference(forward_demodulation,[],[f843,f573])).

fof(f843,plain,
    ( ~ v1_funct_2(k7_tmap_1(sK4,sK5),k2_struct_0(sK4),k2_struct_0(sK4))
    | ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK4)),sK4,k6_tmap_1(sK4,sK5))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK4),k2_struct_0(sK4))))
    | ~ v1_funct_1(k7_tmap_1(sK4,sK5))
    | ~ v3_pre_topc(sK5,sK4) ),
    inference(forward_demodulation,[],[f842,f215])).

fof(f842,plain,
    ( ~ v1_funct_2(k7_tmap_1(sK4,sK5),u1_struct_0(sK4),k2_struct_0(sK4))
    | ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK4)),sK4,k6_tmap_1(sK4,sK5))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK4),k2_struct_0(sK4))))
    | ~ v1_funct_1(k7_tmap_1(sK4,sK5))
    | ~ v3_pre_topc(sK5,sK4) ),
    inference(forward_demodulation,[],[f841,f574])).

fof(f841,plain,
    ( ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK4)),sK4,k6_tmap_1(sK4,sK5))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK4),k2_struct_0(sK4))))
    | ~ v1_funct_2(k7_tmap_1(sK4,sK5),u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK5)))
    | ~ v1_funct_1(k7_tmap_1(sK4,sK5))
    | ~ v3_pre_topc(sK5,sK4) ),
    inference(forward_demodulation,[],[f840,f573])).

fof(f840,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK4),k2_struct_0(sK4))))
    | ~ v5_pre_topc(k7_tmap_1(sK4,sK5),sK4,k6_tmap_1(sK4,sK5))
    | ~ v1_funct_2(k7_tmap_1(sK4,sK5),u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK5)))
    | ~ v1_funct_1(k7_tmap_1(sK4,sK5))
    | ~ v3_pre_topc(sK5,sK4) ),
    inference(forward_demodulation,[],[f839,f573])).

fof(f839,plain,
    ( ~ m1_subset_1(k7_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK4),k2_struct_0(sK4))))
    | ~ v5_pre_topc(k7_tmap_1(sK4,sK5),sK4,k6_tmap_1(sK4,sK5))
    | ~ v1_funct_2(k7_tmap_1(sK4,sK5),u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK5)))
    | ~ v1_funct_1(k7_tmap_1(sK4,sK5))
    | ~ v3_pre_topc(sK5,sK4) ),
    inference(forward_demodulation,[],[f838,f215])).

fof(f838,plain,
    ( ~ m1_subset_1(k7_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),k2_struct_0(sK4))))
    | ~ v5_pre_topc(k7_tmap_1(sK4,sK5),sK4,k6_tmap_1(sK4,sK5))
    | ~ v1_funct_2(k7_tmap_1(sK4,sK5),u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK5)))
    | ~ v1_funct_1(k7_tmap_1(sK4,sK5))
    | ~ v3_pre_topc(sK5,sK4) ),
    inference(forward_demodulation,[],[f82,f574])).

fof(f82,plain,
    ( ~ m1_subset_1(k7_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK5)))))
    | ~ v5_pre_topc(k7_tmap_1(sK4,sK5),sK4,k6_tmap_1(sK4,sK5))
    | ~ v1_funct_2(k7_tmap_1(sK4,sK5),u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK5)))
    | ~ v1_funct_1(k7_tmap_1(sK4,sK5))
    | ~ v3_pre_topc(sK5,sK4) ),
    inference(cnf_transformation,[],[f58])).

fof(f8865,plain,
    ( ~ v1_funct_2(k6_partfun1(k2_struct_0(sK4)),u1_struct_0(sK4),k2_struct_0(sK4))
    | k1_xboole_0 != k2_struct_0(sK4)
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),k2_struct_0(sK4))))
    | ~ sP0(sK4,k6_partfun1(k2_struct_0(sK4)),k6_tmap_1(sK4,sK5)) ),
    inference(subsumption_resolution,[],[f8864,f76])).

fof(f8864,plain,
    ( ~ v1_funct_2(k6_partfun1(k2_struct_0(sK4)),u1_struct_0(sK4),k2_struct_0(sK4))
    | k1_xboole_0 != k2_struct_0(sK4)
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),k2_struct_0(sK4))))
    | ~ l1_pre_topc(sK4)
    | ~ sP0(sK4,k6_partfun1(k2_struct_0(sK4)),k6_tmap_1(sK4,sK5)) ),
    inference(subsumption_resolution,[],[f8860,f420])).

fof(f8860,plain,
    ( ~ v1_funct_2(k6_partfun1(k2_struct_0(sK4)),u1_struct_0(sK4),k2_struct_0(sK4))
    | k1_xboole_0 != k2_struct_0(sK4)
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),k2_struct_0(sK4))))
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK4)))
    | ~ l1_pre_topc(sK4)
    | ~ sP0(sK4,k6_partfun1(k2_struct_0(sK4)),k6_tmap_1(sK4,sK5)) ),
    inference(resolution,[],[f669,f7720])).

fof(f669,plain,(
    ! [X26,X25] :
      ( sP1(k6_tmap_1(sK4,sK5),X25,X26)
      | ~ v1_funct_2(X25,u1_struct_0(X26),k2_struct_0(sK4))
      | k1_xboole_0 != k2_struct_0(X26)
      | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X26),k2_struct_0(sK4))))
      | ~ v1_funct_1(X25)
      | ~ l1_pre_topc(X26) ) ),
    inference(subsumption_resolution,[],[f627,f274])).

fof(f627,plain,(
    ! [X26,X25] :
      ( ~ v1_funct_2(X25,u1_struct_0(X26),k2_struct_0(sK4))
      | sP1(k6_tmap_1(sK4,sK5),X25,X26)
      | k1_xboole_0 != k2_struct_0(X26)
      | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X26),k2_struct_0(sK4))))
      | ~ v1_funct_1(X25)
      | ~ l1_pre_topc(k6_tmap_1(sK4,sK5))
      | ~ l1_pre_topc(X26) ) ),
    inference(superposition,[],[f92,f574])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( sP1(X1,X2,X0)
      | k2_struct_0(X0) != k1_xboole_0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f12913,plain,(
    ~ m1_subset_1(sK6(sK4,k6_partfun1(k2_struct_0(sK4)),k6_tmap_1(sK4,sK5)),k1_zfmisc_1(k2_struct_0(sK4))) ),
    inference(subsumption_resolution,[],[f12901,f9611])).

fof(f9611,plain,(
    v3_pre_topc(sK6(sK4,k6_partfun1(k2_struct_0(sK4)),k6_tmap_1(sK4,sK5)),sK4) ),
    inference(subsumption_resolution,[],[f9610,f8881])).

fof(f9610,plain,
    ( ~ m1_subset_1(sK6(sK4,k6_partfun1(k2_struct_0(sK4)),k6_tmap_1(sK4,sK5)),k1_zfmisc_1(k2_struct_0(sK4)))
    | v3_pre_topc(sK6(sK4,k6_partfun1(k2_struct_0(sK4)),k6_tmap_1(sK4,sK5)),sK4) ),
    inference(forward_demodulation,[],[f9609,f215])).

fof(f9609,plain,
    ( v3_pre_topc(sK6(sK4,k6_partfun1(k2_struct_0(sK4)),k6_tmap_1(sK4,sK5)),sK4)
    | ~ m1_subset_1(sK6(sK4,k6_partfun1(k2_struct_0(sK4)),k6_tmap_1(sK4,sK5)),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(subsumption_resolution,[],[f9602,f76])).

fof(f9602,plain,
    ( v3_pre_topc(sK6(sK4,k6_partfun1(k2_struct_0(sK4)),k6_tmap_1(sK4,sK5)),sK4)
    | ~ m1_subset_1(sK6(sK4,k6_partfun1(k2_struct_0(sK4)),k6_tmap_1(sK4,sK5)),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_pre_topc(sK4) ),
    inference(resolution,[],[f9594,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

fof(f9594,plain,(
    r2_hidden(sK6(sK4,k6_partfun1(k2_struct_0(sK4)),k6_tmap_1(sK4,sK5)),u1_pre_topc(sK4)) ),
    inference(subsumption_resolution,[],[f9593,f8881])).

fof(f9593,plain,
    ( ~ m1_subset_1(sK6(sK4,k6_partfun1(k2_struct_0(sK4)),k6_tmap_1(sK4,sK5)),k1_zfmisc_1(k2_struct_0(sK4)))
    | r2_hidden(sK6(sK4,k6_partfun1(k2_struct_0(sK4)),k6_tmap_1(sK4,sK5)),u1_pre_topc(sK4)) ),
    inference(forward_demodulation,[],[f9592,f574])).

fof(f9592,plain,
    ( r2_hidden(sK6(sK4,k6_partfun1(k2_struct_0(sK4)),k6_tmap_1(sK4,sK5)),u1_pre_topc(sK4))
    | ~ m1_subset_1(sK6(sK4,k6_partfun1(k2_struct_0(sK4)),k6_tmap_1(sK4,sK5)),k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK4,sK5)))) ),
    inference(forward_demodulation,[],[f9591,f8963])).

fof(f8963,plain,(
    u1_pre_topc(sK4) = u1_pre_topc(k6_tmap_1(sK4,sK5)) ),
    inference(backward_demodulation,[],[f250,f8931])).

fof(f8931,plain,(
    u1_pre_topc(sK4) = k5_tmap_1(sK4,sK5) ),
    inference(resolution,[],[f8921,f559])).

fof(f559,plain,
    ( ~ v3_pre_topc(sK5,sK4)
    | u1_pre_topc(sK4) = k5_tmap_1(sK4,sK5) ),
    inference(subsumption_resolution,[],[f558,f281])).

fof(f558,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_struct_0(sK4)))
    | ~ v3_pre_topc(sK5,sK4)
    | u1_pre_topc(sK4) = k5_tmap_1(sK4,sK5) ),
    inference(forward_demodulation,[],[f557,f215])).

fof(f557,plain,
    ( ~ v3_pre_topc(sK5,sK4)
    | u1_pre_topc(sK4) = k5_tmap_1(sK4,sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(subsumption_resolution,[],[f556,f74])).

fof(f556,plain,
    ( ~ v3_pre_topc(sK5,sK4)
    | u1_pre_topc(sK4) = k5_tmap_1(sK4,sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f555,f75])).

fof(f555,plain,
    ( ~ v3_pre_topc(sK5,sK4)
    | u1_pre_topc(sK4) = k5_tmap_1(sK4,sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f553,f76])).

fof(f553,plain,
    ( ~ v3_pre_topc(sK5,sK4)
    | u1_pre_topc(sK4) = k5_tmap_1(sK4,sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4) ),
    inference(resolution,[],[f240,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( u1_pre_topc(X0) = k5_tmap_1(X0,X1)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r2_hidden(X1,u1_pre_topc(X0))
              | u1_pre_topc(X0) != k5_tmap_1(X0,X1) )
            & ( u1_pre_topc(X0) = k5_tmap_1(X0,X1)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
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
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_tmap_1)).

fof(f240,plain,
    ( r2_hidden(sK5,u1_pre_topc(sK4))
    | ~ v3_pre_topc(sK5,sK4) ),
    inference(subsumption_resolution,[],[f222,f76])).

fof(f222,plain,
    ( r2_hidden(sK5,u1_pre_topc(sK4))
    | ~ v3_pre_topc(sK5,sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(resolution,[],[f77,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,u1_pre_topc(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f8921,plain,(
    v3_pre_topc(sK5,sK4) ),
    inference(trivial_inequality_removal,[],[f8895])).

fof(f8895,plain,
    ( k6_tmap_1(sK4,sK5) != k6_tmap_1(sK4,sK5)
    | v3_pre_topc(sK5,sK4) ),
    inference(backward_demodulation,[],[f1457,f8877])).

fof(f8877,plain,(
    k6_tmap_1(sK4,sK5) = g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4)) ),
    inference(subsumption_resolution,[],[f8876,f656])).

fof(f8876,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK4),k2_struct_0(sK4))))
    | k6_tmap_1(sK4,sK5) = g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4)) ),
    inference(forward_demodulation,[],[f8875,f215])).

fof(f8875,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),k2_struct_0(sK4))))
    | k6_tmap_1(sK4,sK5) = g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4)) ),
    inference(subsumption_resolution,[],[f8874,f653])).

fof(f8874,plain,
    ( ~ v1_funct_2(k6_partfun1(k2_struct_0(sK4)),k2_struct_0(sK4),k2_struct_0(sK4))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),k2_struct_0(sK4))))
    | k6_tmap_1(sK4,sK5) = g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4)) ),
    inference(forward_demodulation,[],[f8873,f215])).

fof(f8873,plain,
    ( ~ v1_funct_2(k6_partfun1(k2_struct_0(sK4)),u1_struct_0(sK4),k2_struct_0(sK4))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),k2_struct_0(sK4))))
    | k6_tmap_1(sK4,sK5) = g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4)) ),
    inference(subsumption_resolution,[],[f8872,f7613])).

fof(f7613,plain,
    ( k6_tmap_1(sK4,sK5) = g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4))
    | k1_xboole_0 = k2_struct_0(sK4) ),
    inference(forward_demodulation,[],[f7612,f650])).

fof(f7612,plain,
    ( k6_tmap_1(sK4,sK5) = g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4))
    | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK4,sK5)) ),
    inference(subsumption_resolution,[],[f7611,f653])).

fof(f7611,plain,
    ( ~ v1_funct_2(k6_partfun1(k2_struct_0(sK4)),k2_struct_0(sK4),k2_struct_0(sK4))
    | k6_tmap_1(sK4,sK5) = g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4))
    | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK4,sK5)) ),
    inference(forward_demodulation,[],[f7610,f574])).

fof(f7610,plain,
    ( k6_tmap_1(sK4,sK5) = g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK4)),k2_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK5)))
    | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK4,sK5)) ),
    inference(subsumption_resolution,[],[f7609,f656])).

fof(f7609,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK4),k2_struct_0(sK4))))
    | k6_tmap_1(sK4,sK5) = g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK4)),k2_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK5)))
    | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK4,sK5)) ),
    inference(forward_demodulation,[],[f7608,f574])).

fof(f7608,plain,
    ( k6_tmap_1(sK4,sK5) = g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK5)))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK4)),k2_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK5)))
    | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK4,sK5)) ),
    inference(subsumption_resolution,[],[f7607,f274])).

fof(f7607,plain,
    ( k6_tmap_1(sK4,sK5) = g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK5)))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK4)),k2_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK5)))
    | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK4,sK5))
    | ~ l1_pre_topc(k6_tmap_1(sK4,sK5)) ),
    inference(subsumption_resolution,[],[f7602,f420])).

fof(f7602,plain,
    ( k6_tmap_1(sK4,sK5) = g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK5)))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK4)),k2_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK5)))
    | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK4,sK5))
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK4)))
    | ~ l1_pre_topc(k6_tmap_1(sK4,sK5)) ),
    inference(resolution,[],[f7589,f4243])).

fof(f8872,plain,
    ( ~ v1_funct_2(k6_partfun1(k2_struct_0(sK4)),u1_struct_0(sK4),k2_struct_0(sK4))
    | k1_xboole_0 != k2_struct_0(sK4)
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),k2_struct_0(sK4))))
    | k6_tmap_1(sK4,sK5) = g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4)) ),
    inference(subsumption_resolution,[],[f8871,f76])).

fof(f8871,plain,
    ( ~ v1_funct_2(k6_partfun1(k2_struct_0(sK4)),u1_struct_0(sK4),k2_struct_0(sK4))
    | k1_xboole_0 != k2_struct_0(sK4)
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),k2_struct_0(sK4))))
    | ~ l1_pre_topc(sK4)
    | k6_tmap_1(sK4,sK5) = g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4)) ),
    inference(subsumption_resolution,[],[f8861,f420])).

fof(f8861,plain,
    ( ~ v1_funct_2(k6_partfun1(k2_struct_0(sK4)),u1_struct_0(sK4),k2_struct_0(sK4))
    | k1_xboole_0 != k2_struct_0(sK4)
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),k2_struct_0(sK4))))
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK4)))
    | ~ l1_pre_topc(sK4)
    | k6_tmap_1(sK4,sK5) = g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4)) ),
    inference(resolution,[],[f669,f7589])).

fof(f1457,plain,
    ( v3_pre_topc(sK5,sK4)
    | k6_tmap_1(sK4,sK5) != g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4)) ),
    inference(forward_demodulation,[],[f256,f215])).

fof(f256,plain,
    ( v3_pre_topc(sK5,sK4)
    | k6_tmap_1(sK4,sK5) != g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) ),
    inference(subsumption_resolution,[],[f255,f74])).

fof(f255,plain,
    ( v3_pre_topc(sK5,sK4)
    | k6_tmap_1(sK4,sK5) != g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f254,f75])).

fof(f254,plain,
    ( v3_pre_topc(sK5,sK4)
    | k6_tmap_1(sK4,sK5) != g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f228,f76])).

fof(f228,plain,
    ( v3_pre_topc(sK5,sK4)
    | k6_tmap_1(sK4,sK5) != g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4) ),
    inference(resolution,[],[f77,f103])).

fof(f250,plain,(
    k5_tmap_1(sK4,sK5) = u1_pre_topc(k6_tmap_1(sK4,sK5)) ),
    inference(subsumption_resolution,[],[f249,f74])).

fof(f249,plain,
    ( k5_tmap_1(sK4,sK5) = u1_pre_topc(k6_tmap_1(sK4,sK5))
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f248,f75])).

fof(f248,plain,
    ( k5_tmap_1(sK4,sK5) = u1_pre_topc(k6_tmap_1(sK4,sK5))
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f226,f76])).

fof(f226,plain,
    ( k5_tmap_1(sK4,sK5) = u1_pre_topc(k6_tmap_1(sK4,sK5))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4) ),
    inference(resolution,[],[f77,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f9591,plain,
    ( r2_hidden(sK6(sK4,k6_partfun1(k2_struct_0(sK4)),k6_tmap_1(sK4,sK5)),u1_pre_topc(k6_tmap_1(sK4,sK5)))
    | ~ m1_subset_1(sK6(sK4,k6_partfun1(k2_struct_0(sK4)),k6_tmap_1(sK4,sK5)),k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK4,sK5)))) ),
    inference(subsumption_resolution,[],[f9580,f274])).

fof(f9580,plain,
    ( r2_hidden(sK6(sK4,k6_partfun1(k2_struct_0(sK4)),k6_tmap_1(sK4,sK5)),u1_pre_topc(k6_tmap_1(sK4,sK5)))
    | ~ m1_subset_1(sK6(sK4,k6_partfun1(k2_struct_0(sK4)),k6_tmap_1(sK4,sK5)),k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK4,sK5))))
    | ~ l1_pre_topc(k6_tmap_1(sK4,sK5)) ),
    inference(resolution,[],[f8883,f93])).

fof(f8883,plain,(
    v3_pre_topc(sK6(sK4,k6_partfun1(k2_struct_0(sK4)),k6_tmap_1(sK4,sK5)),k6_tmap_1(sK4,sK5)) ),
    inference(resolution,[],[f8870,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | v3_pre_topc(sK6(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f12901,plain,
    ( ~ v3_pre_topc(sK6(sK4,k6_partfun1(k2_struct_0(sK4)),k6_tmap_1(sK4,sK5)),sK4)
    | ~ m1_subset_1(sK6(sK4,k6_partfun1(k2_struct_0(sK4)),k6_tmap_1(sK4,sK5)),k1_zfmisc_1(k2_struct_0(sK4))) ),
    inference(superposition,[],[f8887,f107])).

fof(f8887,plain,(
    ~ v3_pre_topc(k8_relset_1(k2_struct_0(sK4),k2_struct_0(sK4),k6_partfun1(k2_struct_0(sK4)),sK6(sK4,k6_partfun1(k2_struct_0(sK4)),k6_tmap_1(sK4,sK5))),sK4) ),
    inference(forward_demodulation,[],[f8879,f574])).

fof(f8879,plain,(
    ~ v3_pre_topc(k8_relset_1(k2_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK5)),k6_partfun1(k2_struct_0(sK4)),sK6(sK4,k6_partfun1(k2_struct_0(sK4)),k6_tmap_1(sK4,sK5))),sK4) ),
    inference(resolution,[],[f8870,f447])).

fof(f447,plain,(
    ! [X12,X11] :
      ( sP0(sK4,X12,X11)
      | ~ v3_pre_topc(k8_relset_1(k2_struct_0(sK4),u1_struct_0(X11),X12,sK6(sK4,X12,X11)),sK4) ) ),
    inference(superposition,[],[f90,f215])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,sK6(X0,X1,X2)),X0) ) ),
    inference(cnf_transformation,[],[f64])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:00:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (6979)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.48  % (6979)Refutation not found, incomplete strategy% (6979)------------------------------
% 0.21/0.48  % (6979)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (6987)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.49  % (6979)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (6979)Memory used [KB]: 6140
% 0.21/0.49  % (6979)Time elapsed: 0.061 s
% 0.21/0.49  % (6979)------------------------------
% 0.21/0.49  % (6979)------------------------------
% 0.21/0.49  % (6987)Refutation not found, incomplete strategy% (6987)------------------------------
% 0.21/0.49  % (6987)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (6987)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (6987)Memory used [KB]: 6140
% 0.21/0.49  % (6987)Time elapsed: 0.073 s
% 0.21/0.49  % (6987)------------------------------
% 0.21/0.49  % (6987)------------------------------
% 0.21/0.49  % (6986)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.50  % (6978)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (6994)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.51  % (6993)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.51  % (6974)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.51  % (6984)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.51  % (6988)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.51  % (6995)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.51  % (6980)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.51  % (6981)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.52  % (6983)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.52  % (6980)Refutation not found, incomplete strategy% (6980)------------------------------
% 0.21/0.52  % (6980)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (6980)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (6980)Memory used [KB]: 10618
% 0.21/0.52  % (6980)Time elapsed: 0.075 s
% 0.21/0.52  % (6980)------------------------------
% 0.21/0.52  % (6980)------------------------------
% 0.21/0.52  % (6996)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.52  % (6985)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.52  % (6989)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.52  % (6998)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.52  % (6985)Refutation not found, incomplete strategy% (6985)------------------------------
% 0.21/0.52  % (6985)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (6985)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (6985)Memory used [KB]: 10618
% 0.21/0.52  % (6985)Time elapsed: 0.106 s
% 0.21/0.52  % (6985)------------------------------
% 0.21/0.52  % (6985)------------------------------
% 1.21/0.52  % (6976)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.21/0.52  % (6975)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.21/0.52  % (6982)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.21/0.52  % (6997)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.21/0.53  % (6974)Refutation not found, incomplete strategy% (6974)------------------------------
% 1.21/0.53  % (6974)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.21/0.53  % (6974)Termination reason: Refutation not found, incomplete strategy
% 1.21/0.53  
% 1.21/0.53  % (6974)Memory used [KB]: 10618
% 1.21/0.53  % (6974)Time elapsed: 0.117 s
% 1.21/0.53  % (6974)------------------------------
% 1.21/0.53  % (6974)------------------------------
% 1.21/0.53  % (6992)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.21/0.54  % (6977)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.41/0.54  % (6999)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.41/0.55  % (6990)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.41/0.56  % (6991)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 2.13/0.64  % (6983)Refutation not found, incomplete strategy% (6983)------------------------------
% 2.13/0.64  % (6983)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.13/0.65  % (6983)Termination reason: Refutation not found, incomplete strategy
% 2.13/0.65  
% 2.13/0.65  % (6983)Memory used [KB]: 6140
% 2.13/0.65  % (6983)Time elapsed: 0.227 s
% 2.13/0.65  % (6983)------------------------------
% 2.13/0.65  % (6983)------------------------------
% 4.44/0.96  % (6988)Time limit reached!
% 4.44/0.96  % (6988)------------------------------
% 4.44/0.96  % (6988)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.44/0.96  % (6988)Termination reason: Time limit
% 4.44/0.96  
% 4.44/0.96  % (6988)Memory used [KB]: 8443
% 4.44/0.96  % (6988)Time elapsed: 0.512 s
% 4.44/0.96  % (6988)------------------------------
% 4.44/0.96  % (6988)------------------------------
% 5.45/1.06  % (6982)Refutation found. Thanks to Tanya!
% 5.45/1.06  % SZS status Theorem for theBenchmark
% 5.45/1.06  % SZS output start Proof for theBenchmark
% 5.45/1.06  fof(f12914,plain,(
% 5.45/1.06    $false),
% 5.45/1.06    inference(subsumption_resolution,[],[f12913,f8881])).
% 5.45/1.07  fof(f8881,plain,(
% 5.45/1.07    m1_subset_1(sK6(sK4,k6_partfun1(k2_struct_0(sK4)),k6_tmap_1(sK4,sK5)),k1_zfmisc_1(k2_struct_0(sK4)))),
% 5.45/1.07    inference(resolution,[],[f8870,f619])).
% 5.45/1.07  fof(f619,plain,(
% 5.45/1.07    ( ! [X10,X9] : (sP0(X9,X10,k6_tmap_1(sK4,sK5)) | m1_subset_1(sK6(X9,X10,k6_tmap_1(sK4,sK5)),k1_zfmisc_1(k2_struct_0(sK4)))) )),
% 5.45/1.07    inference(superposition,[],[f88,f574])).
% 5.45/1.07  fof(f574,plain,(
% 5.45/1.07    u1_struct_0(k6_tmap_1(sK4,sK5)) = k2_struct_0(sK4)),
% 5.45/1.07    inference(forward_demodulation,[],[f247,f215])).
% 5.45/1.07  fof(f215,plain,(
% 5.45/1.07    u1_struct_0(sK4) = k2_struct_0(sK4)),
% 5.45/1.07    inference(resolution,[],[f166,f83])).
% 5.45/1.07  fof(f83,plain,(
% 5.45/1.07    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 5.45/1.07    inference(cnf_transformation,[],[f23])).
% 5.45/1.07  fof(f23,plain,(
% 5.45/1.07    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 5.45/1.07    inference(ennf_transformation,[],[f4])).
% 5.45/1.07  fof(f4,axiom,(
% 5.45/1.07    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 5.45/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 5.45/1.07  fof(f166,plain,(
% 5.45/1.07    l1_struct_0(sK4)),
% 5.45/1.07    inference(resolution,[],[f76,f84])).
% 5.45/1.07  fof(f84,plain,(
% 5.45/1.07    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 5.45/1.07    inference(cnf_transformation,[],[f24])).
% 5.45/1.07  fof(f24,plain,(
% 5.45/1.07    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 5.45/1.07    inference(ennf_transformation,[],[f6])).
% 5.45/1.07  fof(f6,axiom,(
% 5.45/1.07    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 5.45/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 5.45/1.07  fof(f76,plain,(
% 5.45/1.07    l1_pre_topc(sK4)),
% 5.45/1.07    inference(cnf_transformation,[],[f58])).
% 5.45/1.07  fof(f58,plain,(
% 5.45/1.07    ((~m1_subset_1(k7_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK5))))) | ~v5_pre_topc(k7_tmap_1(sK4,sK5),sK4,k6_tmap_1(sK4,sK5)) | ~v1_funct_2(k7_tmap_1(sK4,sK5),u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK5))) | ~v1_funct_1(k7_tmap_1(sK4,sK5)) | ~v3_pre_topc(sK5,sK4)) & ((m1_subset_1(k7_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK5))))) & v5_pre_topc(k7_tmap_1(sK4,sK5),sK4,k6_tmap_1(sK4,sK5)) & v1_funct_2(k7_tmap_1(sK4,sK5),u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK5))) & v1_funct_1(k7_tmap_1(sK4,sK5))) | v3_pre_topc(sK5,sK4)) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4)),
% 5.45/1.07    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f55,f57,f56])).
% 5.45/1.07  fof(f56,plain,(
% 5.45/1.07    ? [X0] : (? [X1] : ((~m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) | ~v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~v1_funct_1(k7_tmap_1(X0,X1)) | ~v3_pre_topc(X1,X0)) & ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~m1_subset_1(k7_tmap_1(sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,X1))))) | ~v5_pre_topc(k7_tmap_1(sK4,X1),sK4,k6_tmap_1(sK4,X1)) | ~v1_funct_2(k7_tmap_1(sK4,X1),u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,X1))) | ~v1_funct_1(k7_tmap_1(sK4,X1)) | ~v3_pre_topc(X1,sK4)) & ((m1_subset_1(k7_tmap_1(sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,X1))))) & v5_pre_topc(k7_tmap_1(sK4,X1),sK4,k6_tmap_1(sK4,X1)) & v1_funct_2(k7_tmap_1(sK4,X1),u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,X1))) & v1_funct_1(k7_tmap_1(sK4,X1))) | v3_pre_topc(X1,sK4)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4))),
% 5.45/1.07    introduced(choice_axiom,[])).
% 5.45/1.07  fof(f57,plain,(
% 5.45/1.07    ? [X1] : ((~m1_subset_1(k7_tmap_1(sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,X1))))) | ~v5_pre_topc(k7_tmap_1(sK4,X1),sK4,k6_tmap_1(sK4,X1)) | ~v1_funct_2(k7_tmap_1(sK4,X1),u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,X1))) | ~v1_funct_1(k7_tmap_1(sK4,X1)) | ~v3_pre_topc(X1,sK4)) & ((m1_subset_1(k7_tmap_1(sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,X1))))) & v5_pre_topc(k7_tmap_1(sK4,X1),sK4,k6_tmap_1(sK4,X1)) & v1_funct_2(k7_tmap_1(sK4,X1),u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,X1))) & v1_funct_1(k7_tmap_1(sK4,X1))) | v3_pre_topc(X1,sK4)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))) => ((~m1_subset_1(k7_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK5))))) | ~v5_pre_topc(k7_tmap_1(sK4,sK5),sK4,k6_tmap_1(sK4,sK5)) | ~v1_funct_2(k7_tmap_1(sK4,sK5),u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK5))) | ~v1_funct_1(k7_tmap_1(sK4,sK5)) | ~v3_pre_topc(sK5,sK4)) & ((m1_subset_1(k7_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK5))))) & v5_pre_topc(k7_tmap_1(sK4,sK5),sK4,k6_tmap_1(sK4,sK5)) & v1_funct_2(k7_tmap_1(sK4,sK5),u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK5))) & v1_funct_1(k7_tmap_1(sK4,sK5))) | v3_pre_topc(sK5,sK4)) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))))),
% 5.45/1.07    introduced(choice_axiom,[])).
% 5.45/1.07  fof(f55,plain,(
% 5.45/1.07    ? [X0] : (? [X1] : ((~m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) | ~v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~v1_funct_1(k7_tmap_1(X0,X1)) | ~v3_pre_topc(X1,X0)) & ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 5.45/1.07    inference(flattening,[],[f54])).
% 5.45/1.07  fof(f54,plain,(
% 5.45/1.07    ? [X0] : (? [X1] : ((((~m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) | ~v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~v1_funct_1(k7_tmap_1(X0,X1))) | ~v3_pre_topc(X1,X0)) & ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 5.45/1.07    inference(nnf_transformation,[],[f22])).
% 5.45/1.07  fof(f22,plain,(
% 5.45/1.07    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 5.45/1.07    inference(flattening,[],[f21])).
% 5.45/1.07  fof(f21,plain,(
% 5.45/1.07    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 5.45/1.07    inference(ennf_transformation,[],[f18])).
% 5.45/1.07  fof(f18,negated_conjecture,(
% 5.45/1.07    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))))))),
% 5.45/1.07    inference(negated_conjecture,[],[f17])).
% 5.45/1.07  fof(f17,conjecture,(
% 5.45/1.07    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))))))),
% 5.45/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_tmap_1)).
% 5.45/1.07  fof(f247,plain,(
% 5.45/1.07    u1_struct_0(sK4) = u1_struct_0(k6_tmap_1(sK4,sK5))),
% 5.45/1.07    inference(subsumption_resolution,[],[f246,f74])).
% 5.45/1.07  fof(f74,plain,(
% 5.45/1.07    ~v2_struct_0(sK4)),
% 5.45/1.07    inference(cnf_transformation,[],[f58])).
% 5.45/1.07  fof(f246,plain,(
% 5.45/1.07    u1_struct_0(sK4) = u1_struct_0(k6_tmap_1(sK4,sK5)) | v2_struct_0(sK4)),
% 5.45/1.07    inference(subsumption_resolution,[],[f245,f75])).
% 5.45/1.07  fof(f75,plain,(
% 5.45/1.07    v2_pre_topc(sK4)),
% 5.45/1.07    inference(cnf_transformation,[],[f58])).
% 5.45/1.07  fof(f245,plain,(
% 5.45/1.07    u1_struct_0(sK4) = u1_struct_0(k6_tmap_1(sK4,sK5)) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)),
% 5.45/1.07    inference(subsumption_resolution,[],[f225,f76])).
% 5.45/1.07  fof(f225,plain,(
% 5.45/1.07    u1_struct_0(sK4) = u1_struct_0(k6_tmap_1(sK4,sK5)) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)),
% 5.45/1.07    inference(resolution,[],[f77,f100])).
% 5.45/1.07  fof(f100,plain,(
% 5.45/1.07    ( ! [X0,X1] : (u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 5.45/1.07    inference(cnf_transformation,[],[f33])).
% 5.45/1.07  fof(f33,plain,(
% 5.45/1.07    ! [X0] : (! [X1] : ((k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1)) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 5.45/1.07    inference(flattening,[],[f32])).
% 5.45/1.07  fof(f32,plain,(
% 5.45/1.07    ! [X0] : (! [X1] : ((k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1)) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 5.45/1.07    inference(ennf_transformation,[],[f14])).
% 5.45/1.07  fof(f14,axiom,(
% 5.45/1.07    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1)) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)))))),
% 5.45/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_tmap_1)).
% 5.45/1.07  fof(f77,plain,(
% 5.45/1.07    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))),
% 5.45/1.07    inference(cnf_transformation,[],[f58])).
% 5.45/1.07  fof(f88,plain,(
% 5.45/1.07    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2)))) )),
% 5.45/1.07    inference(cnf_transformation,[],[f64])).
% 5.45/1.07  fof(f64,plain,(
% 5.45/1.07    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,sK6(X0,X1,X2)),X0) & v3_pre_topc(sK6(X0,X1,X2),X2) & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))))) & (! [X4] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,X4),X0) | ~v3_pre_topc(X4,X2) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))) | ~sP0(X0,X1,X2)))),
% 5.45/1.07    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f62,f63])).
% 5.45/1.07  fof(f63,plain,(
% 5.45/1.07    ! [X2,X1,X0] : (? [X3] : (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,X3),X0) & v3_pre_topc(X3,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) => (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,sK6(X0,X1,X2)),X0) & v3_pre_topc(sK6(X0,X1,X2),X2) & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2)))))),
% 5.45/1.07    introduced(choice_axiom,[])).
% 5.45/1.07  fof(f62,plain,(
% 5.45/1.07    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,X3),X0) & v3_pre_topc(X3,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))))) & (! [X4] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,X4),X0) | ~v3_pre_topc(X4,X2) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))) | ~sP0(X0,X1,X2)))),
% 5.45/1.07    inference(rectify,[],[f61])).
% 5.45/1.07  fof(f61,plain,(
% 5.45/1.07    ! [X0,X2,X1] : ((sP0(X0,X2,X1) | ? [X3] : (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v3_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~sP0(X0,X2,X1)))),
% 5.45/1.07    inference(nnf_transformation,[],[f47])).
% 5.45/1.07  fof(f47,plain,(
% 5.45/1.07    ! [X0,X2,X1] : (sP0(X0,X2,X1) <=> ! [X3] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))))),
% 5.45/1.07    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 5.45/1.07  fof(f8870,plain,(
% 5.45/1.07    ~sP0(sK4,k6_partfun1(k2_struct_0(sK4)),k6_tmap_1(sK4,sK5))),
% 5.45/1.07    inference(subsumption_resolution,[],[f8869,f656])).
% 5.45/1.07  fof(f656,plain,(
% 5.45/1.07    m1_subset_1(k6_partfun1(k2_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK4),k2_struct_0(sK4))))),
% 5.45/1.07    inference(forward_demodulation,[],[f655,f573])).
% 5.45/1.07  fof(f573,plain,(
% 5.45/1.07    k7_tmap_1(sK4,sK5) = k6_partfun1(k2_struct_0(sK4))),
% 5.45/1.07    inference(forward_demodulation,[],[f244,f215])).
% 5.45/1.07  fof(f244,plain,(
% 5.45/1.07    k7_tmap_1(sK4,sK5) = k6_partfun1(u1_struct_0(sK4))),
% 5.45/1.07    inference(subsumption_resolution,[],[f243,f74])).
% 5.45/1.07  fof(f243,plain,(
% 5.45/1.07    k7_tmap_1(sK4,sK5) = k6_partfun1(u1_struct_0(sK4)) | v2_struct_0(sK4)),
% 5.45/1.07    inference(subsumption_resolution,[],[f242,f75])).
% 5.45/1.07  fof(f242,plain,(
% 5.45/1.07    k7_tmap_1(sK4,sK5) = k6_partfun1(u1_struct_0(sK4)) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)),
% 5.45/1.07    inference(subsumption_resolution,[],[f224,f76])).
% 5.45/1.07  fof(f224,plain,(
% 5.45/1.07    k7_tmap_1(sK4,sK5) = k6_partfun1(u1_struct_0(sK4)) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)),
% 5.45/1.07    inference(resolution,[],[f77,f99])).
% 5.45/1.07  fof(f99,plain,(
% 5.45/1.07    ( ! [X0,X1] : (k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 5.45/1.07    inference(cnf_transformation,[],[f31])).
% 5.45/1.07  fof(f31,plain,(
% 5.45/1.07    ! [X0] : (! [X1] : (k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 5.45/1.07    inference(flattening,[],[f30])).
% 5.45/1.07  fof(f30,plain,(
% 5.45/1.07    ! [X0] : (! [X1] : (k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 5.45/1.07    inference(ennf_transformation,[],[f8])).
% 5.45/1.07  fof(f8,axiom,(
% 5.45/1.07    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))))),
% 5.45/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_tmap_1)).
% 5.45/1.07  fof(f655,plain,(
% 5.45/1.07    m1_subset_1(k7_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK4),k2_struct_0(sK4))))),
% 5.45/1.07    inference(forward_demodulation,[],[f654,f215])).
% 5.45/1.07  fof(f654,plain,(
% 5.45/1.07    m1_subset_1(k7_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),k2_struct_0(sK4))))),
% 5.45/1.07    inference(subsumption_resolution,[],[f612,f277])).
% 5.45/1.07  fof(f277,plain,(
% 5.45/1.07    sP3(sK5,sK4)),
% 5.45/1.07    inference(subsumption_resolution,[],[f276,f74])).
% 5.45/1.07  fof(f276,plain,(
% 5.45/1.07    sP3(sK5,sK4) | v2_struct_0(sK4)),
% 5.45/1.07    inference(subsumption_resolution,[],[f275,f75])).
% 5.45/1.07  fof(f275,plain,(
% 5.45/1.07    sP3(sK5,sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)),
% 5.45/1.07    inference(subsumption_resolution,[],[f235,f76])).
% 5.45/1.07  fof(f235,plain,(
% 5.45/1.07    sP3(sK5,sK4) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)),
% 5.45/1.07    inference(resolution,[],[f77,f115])).
% 5.45/1.07  fof(f115,plain,(
% 5.45/1.07    ( ! [X0,X1] : (sP3(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 5.45/1.07    inference(cnf_transformation,[],[f53])).
% 5.45/1.07  fof(f53,plain,(
% 5.45/1.07    ! [X0,X1] : (sP3(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 5.45/1.07    inference(definition_folding,[],[f46,f52])).
% 5.45/1.07  fof(f52,plain,(
% 5.45/1.07    ! [X1,X0] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | ~sP3(X1,X0))),
% 5.45/1.07    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 5.45/1.07  fof(f46,plain,(
% 5.45/1.07    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 5.45/1.07    inference(flattening,[],[f45])).
% 5.45/1.07  fof(f45,plain,(
% 5.45/1.07    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 5.45/1.07    inference(ennf_transformation,[],[f10])).
% 5.45/1.07  fof(f10,axiom,(
% 5.45/1.07    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))))),
% 5.45/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_tmap_1)).
% 5.45/1.07  fof(f612,plain,(
% 5.45/1.07    m1_subset_1(k7_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),k2_struct_0(sK4)))) | ~sP3(sK5,sK4)),
% 5.45/1.07    inference(superposition,[],[f114,f574])).
% 5.45/1.07  fof(f114,plain,(
% 5.45/1.07    ( ! [X0,X1] : (m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0))))) | ~sP3(X0,X1)) )),
% 5.45/1.07    inference(cnf_transformation,[],[f70])).
% 5.45/1.07  fof(f70,plain,(
% 5.45/1.07    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0))))) & v1_funct_2(k7_tmap_1(X1,X0),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0))) & v1_funct_1(k7_tmap_1(X1,X0))) | ~sP3(X0,X1))),
% 5.45/1.07    inference(rectify,[],[f69])).
% 5.45/1.07  fof(f69,plain,(
% 5.45/1.07    ! [X1,X0] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | ~sP3(X1,X0))),
% 5.45/1.07    inference(nnf_transformation,[],[f52])).
% 5.45/1.07  fof(f8869,plain,(
% 5.45/1.07    ~m1_subset_1(k6_partfun1(k2_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK4),k2_struct_0(sK4)))) | ~sP0(sK4,k6_partfun1(k2_struct_0(sK4)),k6_tmap_1(sK4,sK5))),
% 5.45/1.07    inference(forward_demodulation,[],[f8868,f215])).
% 5.45/1.07  fof(f8868,plain,(
% 5.45/1.07    ~m1_subset_1(k6_partfun1(k2_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),k2_struct_0(sK4)))) | ~sP0(sK4,k6_partfun1(k2_struct_0(sK4)),k6_tmap_1(sK4,sK5))),
% 5.45/1.07    inference(subsumption_resolution,[],[f8867,f653])).
% 5.45/1.07  fof(f653,plain,(
% 5.45/1.07    v1_funct_2(k6_partfun1(k2_struct_0(sK4)),k2_struct_0(sK4),k2_struct_0(sK4))),
% 5.45/1.07    inference(forward_demodulation,[],[f652,f573])).
% 5.45/1.07  fof(f652,plain,(
% 5.45/1.07    v1_funct_2(k7_tmap_1(sK4,sK5),k2_struct_0(sK4),k2_struct_0(sK4))),
% 5.45/1.07    inference(forward_demodulation,[],[f651,f215])).
% 5.45/1.07  fof(f651,plain,(
% 5.45/1.07    v1_funct_2(k7_tmap_1(sK4,sK5),u1_struct_0(sK4),k2_struct_0(sK4))),
% 5.45/1.07    inference(subsumption_resolution,[],[f611,f277])).
% 5.45/1.07  fof(f611,plain,(
% 5.45/1.07    v1_funct_2(k7_tmap_1(sK4,sK5),u1_struct_0(sK4),k2_struct_0(sK4)) | ~sP3(sK5,sK4)),
% 5.45/1.07    inference(superposition,[],[f113,f574])).
% 5.45/1.07  fof(f113,plain,(
% 5.45/1.07    ( ! [X0,X1] : (v1_funct_2(k7_tmap_1(X1,X0),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0))) | ~sP3(X0,X1)) )),
% 5.45/1.07    inference(cnf_transformation,[],[f70])).
% 5.45/1.07  fof(f8867,plain,(
% 5.45/1.07    ~v1_funct_2(k6_partfun1(k2_struct_0(sK4)),k2_struct_0(sK4),k2_struct_0(sK4)) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),k2_struct_0(sK4)))) | ~sP0(sK4,k6_partfun1(k2_struct_0(sK4)),k6_tmap_1(sK4,sK5))),
% 5.45/1.07    inference(forward_demodulation,[],[f8866,f215])).
% 5.45/1.07  fof(f8866,plain,(
% 5.45/1.07    ~v1_funct_2(k6_partfun1(k2_struct_0(sK4)),u1_struct_0(sK4),k2_struct_0(sK4)) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),k2_struct_0(sK4)))) | ~sP0(sK4,k6_partfun1(k2_struct_0(sK4)),k6_tmap_1(sK4,sK5))),
% 5.45/1.07    inference(subsumption_resolution,[],[f8865,f7842])).
% 5.45/1.07  fof(f7842,plain,(
% 5.45/1.07    ~sP0(sK4,k6_partfun1(k2_struct_0(sK4)),k6_tmap_1(sK4,sK5)) | k1_xboole_0 = k2_struct_0(sK4)),
% 5.45/1.07    inference(forward_demodulation,[],[f7841,f650])).
% 5.45/1.07  fof(f650,plain,(
% 5.45/1.07    k2_struct_0(sK4) = k2_struct_0(k6_tmap_1(sK4,sK5))),
% 5.45/1.07    inference(subsumption_resolution,[],[f610,f342])).
% 5.45/1.07  fof(f342,plain,(
% 5.45/1.07    l1_struct_0(k6_tmap_1(sK4,sK5))),
% 5.45/1.07    inference(resolution,[],[f274,f84])).
% 5.45/1.07  fof(f274,plain,(
% 5.45/1.07    l1_pre_topc(k6_tmap_1(sK4,sK5))),
% 5.45/1.07    inference(subsumption_resolution,[],[f273,f74])).
% 5.45/1.07  fof(f273,plain,(
% 5.45/1.07    l1_pre_topc(k6_tmap_1(sK4,sK5)) | v2_struct_0(sK4)),
% 5.45/1.07    inference(subsumption_resolution,[],[f272,f75])).
% 5.45/1.07  fof(f272,plain,(
% 5.45/1.07    l1_pre_topc(k6_tmap_1(sK4,sK5)) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)),
% 5.45/1.07    inference(subsumption_resolution,[],[f234,f76])).
% 5.45/1.07  fof(f234,plain,(
% 5.45/1.07    l1_pre_topc(k6_tmap_1(sK4,sK5)) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)),
% 5.45/1.07    inference(resolution,[],[f77,f111])).
% 5.45/1.07  fof(f111,plain,(
% 5.45/1.07    ( ! [X0,X1] : (l1_pre_topc(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 5.45/1.07    inference(cnf_transformation,[],[f44])).
% 5.45/1.07  fof(f44,plain,(
% 5.45/1.07    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 5.45/1.07    inference(flattening,[],[f43])).
% 5.45/1.07  fof(f43,plain,(
% 5.45/1.07    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 5.45/1.07    inference(ennf_transformation,[],[f20])).
% 5.45/1.07  fof(f20,plain,(
% 5.45/1.07    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1))))),
% 5.45/1.07    inference(pure_predicate_removal,[],[f9])).
% 5.45/1.07  fof(f9,axiom,(
% 5.45/1.07    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))))),
% 5.45/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_tmap_1)).
% 5.45/1.07  fof(f610,plain,(
% 5.45/1.07    k2_struct_0(sK4) = k2_struct_0(k6_tmap_1(sK4,sK5)) | ~l1_struct_0(k6_tmap_1(sK4,sK5))),
% 5.45/1.07    inference(superposition,[],[f574,f83])).
% 5.45/1.07  fof(f7841,plain,(
% 5.45/1.07    ~sP0(sK4,k6_partfun1(k2_struct_0(sK4)),k6_tmap_1(sK4,sK5)) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK4,sK5))),
% 5.45/1.07    inference(subsumption_resolution,[],[f7840,f653])).
% 5.45/1.07  fof(f7840,plain,(
% 5.45/1.07    ~v1_funct_2(k6_partfun1(k2_struct_0(sK4)),k2_struct_0(sK4),k2_struct_0(sK4)) | ~sP0(sK4,k6_partfun1(k2_struct_0(sK4)),k6_tmap_1(sK4,sK5)) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK4,sK5))),
% 5.45/1.07    inference(forward_demodulation,[],[f7839,f574])).
% 5.45/1.07  fof(f7839,plain,(
% 5.45/1.07    ~sP0(sK4,k6_partfun1(k2_struct_0(sK4)),k6_tmap_1(sK4,sK5)) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK4)),k2_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK5))) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK4,sK5))),
% 5.45/1.07    inference(subsumption_resolution,[],[f7838,f656])).
% 5.45/1.07  fof(f7838,plain,(
% 5.45/1.07    ~m1_subset_1(k6_partfun1(k2_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK4),k2_struct_0(sK4)))) | ~sP0(sK4,k6_partfun1(k2_struct_0(sK4)),k6_tmap_1(sK4,sK5)) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK4)),k2_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK5))) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK4,sK5))),
% 5.45/1.07    inference(forward_demodulation,[],[f7837,f574])).
% 5.45/1.07  fof(f7837,plain,(
% 5.45/1.07    ~sP0(sK4,k6_partfun1(k2_struct_0(sK4)),k6_tmap_1(sK4,sK5)) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK5))))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK4)),k2_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK5))) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK4,sK5))),
% 5.45/1.07    inference(subsumption_resolution,[],[f7836,f274])).
% 5.45/1.07  fof(f7836,plain,(
% 5.45/1.07    ~sP0(sK4,k6_partfun1(k2_struct_0(sK4)),k6_tmap_1(sK4,sK5)) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK5))))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK4)),k2_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK5))) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK4,sK5)) | ~l1_pre_topc(k6_tmap_1(sK4,sK5))),
% 5.45/1.07    inference(subsumption_resolution,[],[f7831,f420])).
% 5.45/1.07  fof(f420,plain,(
% 5.45/1.07    v1_funct_1(k6_partfun1(k2_struct_0(sK4)))),
% 5.45/1.07    inference(subsumption_resolution,[],[f419,f166])).
% 5.45/1.07  fof(f419,plain,(
% 5.45/1.07    v1_funct_1(k6_partfun1(k2_struct_0(sK4))) | ~l1_struct_0(sK4)),
% 5.45/1.07    inference(superposition,[],[f397,f83])).
% 5.45/1.07  fof(f397,plain,(
% 5.45/1.07    v1_funct_1(k6_partfun1(u1_struct_0(sK4)))),
% 5.45/1.07    inference(subsumption_resolution,[],[f396,f74])).
% 5.45/1.07  fof(f396,plain,(
% 5.45/1.07    v1_funct_1(k6_partfun1(u1_struct_0(sK4))) | v2_struct_0(sK4)),
% 5.45/1.07    inference(subsumption_resolution,[],[f395,f75])).
% 5.45/1.07  fof(f395,plain,(
% 5.45/1.07    v1_funct_1(k6_partfun1(u1_struct_0(sK4))) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)),
% 5.45/1.07    inference(subsumption_resolution,[],[f394,f76])).
% 5.45/1.07  fof(f394,plain,(
% 5.45/1.07    v1_funct_1(k6_partfun1(u1_struct_0(sK4))) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)),
% 5.45/1.07    inference(subsumption_resolution,[],[f393,f77])).
% 5.45/1.07  fof(f393,plain,(
% 5.45/1.07    v1_funct_1(k6_partfun1(u1_struct_0(sK4))) | ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)),
% 5.45/1.07    inference(superposition,[],[f282,f99])).
% 5.45/1.07  fof(f282,plain,(
% 5.45/1.07    v1_funct_1(k7_tmap_1(sK4,sK5))),
% 5.45/1.07    inference(resolution,[],[f277,f112])).
% 5.45/1.07  fof(f112,plain,(
% 5.45/1.07    ( ! [X0,X1] : (v1_funct_1(k7_tmap_1(X1,X0)) | ~sP3(X0,X1)) )),
% 5.45/1.07    inference(cnf_transformation,[],[f70])).
% 5.45/1.07  fof(f7831,plain,(
% 5.45/1.07    ~sP0(sK4,k6_partfun1(k2_struct_0(sK4)),k6_tmap_1(sK4,sK5)) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK5))))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK4)),k2_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK5))) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK4,sK5)) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK4))) | ~l1_pre_topc(k6_tmap_1(sK4,sK5))),
% 5.45/1.07    inference(resolution,[],[f7720,f4243])).
% 5.45/1.07  fof(f4243,plain,(
% 5.45/1.07    ( ! [X0,X1] : (sP1(X0,X1,sK4) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK4),u1_struct_0(X0)))) | ~v1_funct_2(X1,k2_struct_0(sK4),u1_struct_0(X0)) | k2_struct_0(X0) = k1_xboole_0 | ~v1_funct_1(X1) | ~l1_pre_topc(X0)) )),
% 5.45/1.07    inference(forward_demodulation,[],[f4242,f215])).
% 5.45/1.07  fof(f4242,plain,(
% 5.45/1.07    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK4),u1_struct_0(X0)))) | sP1(X0,X1,sK4) | k2_struct_0(X0) = k1_xboole_0 | ~v1_funct_2(X1,u1_struct_0(sK4),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0)) )),
% 5.45/1.07    inference(forward_demodulation,[],[f167,f215])).
% 5.45/1.07  fof(f167,plain,(
% 5.45/1.07    ( ! [X0,X1] : (sP1(X0,X1,sK4) | k2_struct_0(X0) = k1_xboole_0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK4),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0)) )),
% 5.45/1.07    inference(resolution,[],[f76,f91])).
% 5.45/1.07  fof(f91,plain,(
% 5.45/1.07    ( ! [X2,X0,X1] : (sP1(X1,X2,X0) | k2_struct_0(X1) = k1_xboole_0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 5.45/1.07    inference(cnf_transformation,[],[f49])).
% 5.45/1.07  fof(f49,plain,(
% 5.45/1.07    ! [X0] : (! [X1] : (! [X2] : (sP1(X1,X2,X0) | (k2_struct_0(X0) != k1_xboole_0 & k2_struct_0(X1) = k1_xboole_0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 5.45/1.07    inference(definition_folding,[],[f26,f48,f47])).
% 5.45/1.07  fof(f48,plain,(
% 5.45/1.07    ! [X1,X2,X0] : ((v5_pre_topc(X2,X0,X1) <=> sP0(X0,X2,X1)) | ~sP1(X1,X2,X0))),
% 5.45/1.07    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 5.45/1.07  fof(f26,plain,(
% 5.45/1.07    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (k2_struct_0(X0) != k1_xboole_0 & k2_struct_0(X1) = k1_xboole_0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 5.45/1.07    inference(flattening,[],[f25])).
% 5.45/1.07  fof(f25,plain,(
% 5.45/1.07    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) <=> ! [X3] : ((v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v3_pre_topc(X3,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (k2_struct_0(X0) != k1_xboole_0 & k2_struct_0(X1) = k1_xboole_0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 5.45/1.07    inference(ennf_transformation,[],[f7])).
% 5.45/1.07  fof(f7,axiom,(
% 5.45/1.07    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k2_struct_0(X1) = k1_xboole_0 => k2_struct_0(X0) = k1_xboole_0) => (v5_pre_topc(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (v3_pre_topc(X3,X1) => v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0))))))))),
% 5.45/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_2)).
% 5.45/1.07  fof(f7720,plain,(
% 5.45/1.07    ~sP1(k6_tmap_1(sK4,sK5),k6_partfun1(k2_struct_0(sK4)),sK4) | ~sP0(sK4,k6_partfun1(k2_struct_0(sK4)),k6_tmap_1(sK4,sK5))),
% 5.45/1.07    inference(subsumption_resolution,[],[f4657,f7589])).
% 5.45/1.07  fof(f7589,plain,(
% 5.45/1.07    ~sP1(k6_tmap_1(sK4,sK5),k6_partfun1(k2_struct_0(sK4)),sK4) | k6_tmap_1(sK4,sK5) = g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4))),
% 5.45/1.07    inference(subsumption_resolution,[],[f7588,f1437])).
% 5.45/1.07  fof(f1437,plain,(
% 5.45/1.07    k6_tmap_1(sK4,sK5) = g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4)) | ~v3_pre_topc(sK5,sK4)),
% 5.45/1.07    inference(forward_demodulation,[],[f253,f215])).
% 5.45/1.07  fof(f253,plain,(
% 5.45/1.07    k6_tmap_1(sK4,sK5) = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) | ~v3_pre_topc(sK5,sK4)),
% 5.45/1.07    inference(subsumption_resolution,[],[f252,f74])).
% 5.45/1.07  fof(f252,plain,(
% 5.45/1.07    k6_tmap_1(sK4,sK5) = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) | ~v3_pre_topc(sK5,sK4) | v2_struct_0(sK4)),
% 5.45/1.07    inference(subsumption_resolution,[],[f251,f75])).
% 5.45/1.07  fof(f251,plain,(
% 5.45/1.07    k6_tmap_1(sK4,sK5) = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) | ~v3_pre_topc(sK5,sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)),
% 5.45/1.07    inference(subsumption_resolution,[],[f227,f76])).
% 5.45/1.07  fof(f227,plain,(
% 5.45/1.07    k6_tmap_1(sK4,sK5) = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) | ~v3_pre_topc(sK5,sK4) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)),
% 5.45/1.07    inference(resolution,[],[f77,f102])).
% 5.45/1.07  fof(f102,plain,(
% 5.45/1.07    ( ! [X0,X1] : (k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 5.45/1.07    inference(cnf_transformation,[],[f67])).
% 5.45/1.07  fof(f67,plain,(
% 5.45/1.07    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | k6_tmap_1(X0,X1) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & (k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 5.45/1.07    inference(nnf_transformation,[],[f35])).
% 5.45/1.07  fof(f35,plain,(
% 5.45/1.07    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 5.45/1.07    inference(flattening,[],[f34])).
% 5.45/1.07  fof(f34,plain,(
% 5.45/1.07    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 5.45/1.07    inference(ennf_transformation,[],[f16])).
% 5.45/1.07  fof(f16,axiom,(
% 5.45/1.07    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 5.45/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_tmap_1)).
% 5.45/1.07  fof(f7588,plain,(
% 5.45/1.07    v3_pre_topc(sK5,sK4) | k6_tmap_1(sK4,sK5) = g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4)) | ~sP1(k6_tmap_1(sK4,sK5),k6_partfun1(k2_struct_0(sK4)),sK4)),
% 5.45/1.07    inference(forward_demodulation,[],[f7587,f1172])).
% 5.45/1.07  fof(f1172,plain,(
% 5.45/1.07    sK5 = k8_relset_1(k2_struct_0(sK4),k2_struct_0(sK4),k6_partfun1(k2_struct_0(sK4)),sK5)),
% 5.45/1.07    inference(forward_demodulation,[],[f238,f215])).
% 5.45/1.07  fof(f238,plain,(
% 5.45/1.07    sK5 = k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK4),k6_partfun1(u1_struct_0(sK4)),sK5)),
% 5.45/1.07    inference(resolution,[],[f77,f107])).
% 5.45/1.07  fof(f107,plain,(
% 5.45/1.07    ( ! [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 5.45/1.07    inference(cnf_transformation,[],[f40])).
% 5.45/1.07  fof(f40,plain,(
% 5.45/1.07    ! [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 5.45/1.07    inference(ennf_transformation,[],[f3])).
% 5.45/1.07  fof(f3,axiom,(
% 5.45/1.07    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1)),
% 5.45/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_2)).
% 5.45/1.07  fof(f7587,plain,(
% 5.45/1.07    v3_pre_topc(k8_relset_1(k2_struct_0(sK4),k2_struct_0(sK4),k6_partfun1(k2_struct_0(sK4)),sK5),sK4) | k6_tmap_1(sK4,sK5) = g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4)) | ~sP1(k6_tmap_1(sK4,sK5),k6_partfun1(k2_struct_0(sK4)),sK4)),
% 5.45/1.07    inference(forward_demodulation,[],[f7582,f215])).
% 5.45/1.07  fof(f7582,plain,(
% 5.45/1.07    k6_tmap_1(sK4,sK5) = g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4)) | ~sP1(k6_tmap_1(sK4,sK5),k6_partfun1(k2_struct_0(sK4)),sK4) | v3_pre_topc(k8_relset_1(u1_struct_0(sK4),k2_struct_0(sK4),k6_partfun1(k2_struct_0(sK4)),sK5),sK4)),
% 5.45/1.07    inference(resolution,[],[f3272,f734])).
% 5.45/1.07  fof(f734,plain,(
% 5.45/1.07    ( ! [X0,X1] : (~sP0(X0,X1,k6_tmap_1(sK4,sK5)) | v3_pre_topc(k8_relset_1(u1_struct_0(X0),k2_struct_0(sK4),X1,sK5),X0)) )),
% 5.45/1.07    inference(subsumption_resolution,[],[f733,f281])).
% 5.45/1.07  fof(f281,plain,(
% 5.45/1.07    m1_subset_1(sK5,k1_zfmisc_1(k2_struct_0(sK4)))),
% 5.45/1.07    inference(subsumption_resolution,[],[f239,f166])).
% 5.45/1.07  fof(f239,plain,(
% 5.45/1.07    m1_subset_1(sK5,k1_zfmisc_1(k2_struct_0(sK4))) | ~l1_struct_0(sK4)),
% 5.45/1.07    inference(superposition,[],[f77,f83])).
% 5.45/1.07  fof(f733,plain,(
% 5.45/1.07    ( ! [X0,X1] : (~m1_subset_1(sK5,k1_zfmisc_1(k2_struct_0(sK4))) | v3_pre_topc(k8_relset_1(u1_struct_0(X0),k2_struct_0(sK4),X1,sK5),X0) | ~sP0(X0,X1,k6_tmap_1(sK4,sK5))) )),
% 5.45/1.07    inference(forward_demodulation,[],[f732,f574])).
% 5.45/1.07  fof(f732,plain,(
% 5.45/1.07    ( ! [X0,X1] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),k2_struct_0(sK4),X1,sK5),X0) | ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK4,sK5)))) | ~sP0(X0,X1,k6_tmap_1(sK4,sK5))) )),
% 5.45/1.07    inference(forward_demodulation,[],[f722,f574])).
% 5.45/1.07  fof(f722,plain,(
% 5.45/1.07    ( ! [X0,X1] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(sK4,sK5)),X1,sK5),X0) | ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK4,sK5)))) | ~sP0(X0,X1,k6_tmap_1(sK4,sK5))) )),
% 5.45/1.07    inference(resolution,[],[f662,f87])).
% 5.45/1.07  fof(f87,plain,(
% 5.45/1.07    ( ! [X4,X2,X0,X1] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,X4),X0) | ~v3_pre_topc(X4,X2) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2))) | ~sP0(X0,X1,X2)) )),
% 5.45/1.07    inference(cnf_transformation,[],[f64])).
% 5.45/1.07  fof(f662,plain,(
% 5.45/1.07    v3_pre_topc(sK5,k6_tmap_1(sK4,sK5))),
% 5.45/1.07    inference(subsumption_resolution,[],[f661,f281])).
% 5.45/1.07  fof(f661,plain,(
% 5.45/1.07    ~m1_subset_1(sK5,k1_zfmisc_1(k2_struct_0(sK4))) | v3_pre_topc(sK5,k6_tmap_1(sK4,sK5))),
% 5.45/1.07    inference(forward_demodulation,[],[f660,f215])).
% 5.45/1.07  fof(f660,plain,(
% 5.45/1.07    v3_pre_topc(sK5,k6_tmap_1(sK4,sK5)) | ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))),
% 5.45/1.07    inference(subsumption_resolution,[],[f659,f74])).
% 5.45/1.07  fof(f659,plain,(
% 5.45/1.07    v3_pre_topc(sK5,k6_tmap_1(sK4,sK5)) | ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) | v2_struct_0(sK4)),
% 5.45/1.07    inference(subsumption_resolution,[],[f658,f75])).
% 5.45/1.07  fof(f658,plain,(
% 5.45/1.07    v3_pre_topc(sK5,k6_tmap_1(sK4,sK5)) | ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)),
% 5.45/1.07    inference(subsumption_resolution,[],[f657,f76])).
% 5.45/1.07  fof(f657,plain,(
% 5.45/1.07    v3_pre_topc(sK5,k6_tmap_1(sK4,sK5)) | ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)),
% 5.45/1.07    inference(subsumption_resolution,[],[f613,f281])).
% 5.45/1.07  fof(f613,plain,(
% 5.45/1.07    ~m1_subset_1(sK5,k1_zfmisc_1(k2_struct_0(sK4))) | v3_pre_topc(sK5,k6_tmap_1(sK4,sK5)) | ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)),
% 5.45/1.07    inference(superposition,[],[f121,f574])).
% 5.45/1.07  fof(f121,plain,(
% 5.45/1.07    ( ! [X2,X0] : (v3_pre_topc(X2,k6_tmap_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 5.45/1.07    inference(equality_resolution,[],[f106])).
% 5.45/1.07  fof(f106,plain,(
% 5.45/1.07    ( ! [X2,X0,X1] : (v3_pre_topc(X2,k6_tmap_1(X0,X1)) | X1 != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 5.45/1.07    inference(cnf_transformation,[],[f39])).
% 5.45/1.07  fof(f39,plain,(
% 5.45/1.07    ! [X0] : (! [X1] : (! [X2] : (v3_pre_topc(X2,k6_tmap_1(X0,X1)) | X1 != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 5.45/1.07    inference(flattening,[],[f38])).
% 5.45/1.07  fof(f38,plain,(
% 5.45/1.07    ! [X0] : (! [X1] : (! [X2] : ((v3_pre_topc(X2,k6_tmap_1(X0,X1)) | X1 != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 5.45/1.07    inference(ennf_transformation,[],[f15])).
% 5.45/1.07  fof(f15,axiom,(
% 5.45/1.07    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1)))) => (X1 = X2 => v3_pre_topc(X2,k6_tmap_1(X0,X1))))))),
% 5.45/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_tmap_1)).
% 5.45/1.07  fof(f3272,plain,(
% 5.45/1.07    sP0(sK4,k6_partfun1(k2_struct_0(sK4)),k6_tmap_1(sK4,sK5)) | k6_tmap_1(sK4,sK5) = g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4)) | ~sP1(k6_tmap_1(sK4,sK5),k6_partfun1(k2_struct_0(sK4)),sK4)),
% 5.45/1.07    inference(resolution,[],[f602,f85])).
% 5.45/1.07  fof(f85,plain,(
% 5.45/1.07    ( ! [X2,X0,X1] : (sP0(X2,X1,X0) | ~v5_pre_topc(X1,X2,X0) | ~sP1(X0,X1,X2)) )),
% 5.45/1.07    inference(cnf_transformation,[],[f60])).
% 5.45/1.07  fof(f60,plain,(
% 5.45/1.07    ! [X0,X1,X2] : (((v5_pre_topc(X1,X2,X0) | ~sP0(X2,X1,X0)) & (sP0(X2,X1,X0) | ~v5_pre_topc(X1,X2,X0))) | ~sP1(X0,X1,X2))),
% 5.45/1.07    inference(rectify,[],[f59])).
% 5.45/1.07  fof(f59,plain,(
% 5.45/1.07    ! [X1,X2,X0] : (((v5_pre_topc(X2,X0,X1) | ~sP0(X0,X2,X1)) & (sP0(X0,X2,X1) | ~v5_pre_topc(X2,X0,X1))) | ~sP1(X1,X2,X0))),
% 5.45/1.07    inference(nnf_transformation,[],[f48])).
% 5.45/1.07  fof(f602,plain,(
% 5.45/1.07    v5_pre_topc(k6_partfun1(k2_struct_0(sK4)),sK4,k6_tmap_1(sK4,sK5)) | k6_tmap_1(sK4,sK5) = g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4))),
% 5.45/1.07    inference(subsumption_resolution,[],[f601,f281])).
% 5.45/1.07  fof(f601,plain,(
% 5.45/1.07    ~m1_subset_1(sK5,k1_zfmisc_1(k2_struct_0(sK4))) | k6_tmap_1(sK4,sK5) = g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4)) | v5_pre_topc(k6_partfun1(k2_struct_0(sK4)),sK4,k6_tmap_1(sK4,sK5))),
% 5.45/1.07    inference(forward_demodulation,[],[f600,f215])).
% 5.45/1.07  fof(f600,plain,(
% 5.45/1.07    k6_tmap_1(sK4,sK5) = g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4)) | v5_pre_topc(k6_partfun1(k2_struct_0(sK4)),sK4,k6_tmap_1(sK4,sK5)) | ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))),
% 5.45/1.07    inference(forward_demodulation,[],[f599,f215])).
% 5.45/1.07  fof(f599,plain,(
% 5.45/1.07    v5_pre_topc(k6_partfun1(k2_struct_0(sK4)),sK4,k6_tmap_1(sK4,sK5)) | k6_tmap_1(sK4,sK5) = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) | ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))),
% 5.45/1.07    inference(subsumption_resolution,[],[f598,f74])).
% 5.45/1.07  fof(f598,plain,(
% 5.45/1.07    v5_pre_topc(k6_partfun1(k2_struct_0(sK4)),sK4,k6_tmap_1(sK4,sK5)) | k6_tmap_1(sK4,sK5) = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) | ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) | v2_struct_0(sK4)),
% 5.45/1.07    inference(subsumption_resolution,[],[f597,f75])).
% 5.45/1.07  fof(f597,plain,(
% 5.45/1.07    v5_pre_topc(k6_partfun1(k2_struct_0(sK4)),sK4,k6_tmap_1(sK4,sK5)) | k6_tmap_1(sK4,sK5) = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) | ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)),
% 5.45/1.07    inference(subsumption_resolution,[],[f594,f76])).
% 5.45/1.07  fof(f594,plain,(
% 5.45/1.07    v5_pre_topc(k6_partfun1(k2_struct_0(sK4)),sK4,k6_tmap_1(sK4,sK5)) | k6_tmap_1(sK4,sK5) = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) | ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)),
% 5.45/1.07    inference(resolution,[],[f576,f102])).
% 5.45/1.07  fof(f576,plain,(
% 5.45/1.07    v3_pre_topc(sK5,sK4) | v5_pre_topc(k6_partfun1(k2_struct_0(sK4)),sK4,k6_tmap_1(sK4,sK5))),
% 5.45/1.07    inference(backward_demodulation,[],[f80,f573])).
% 5.45/1.07  fof(f80,plain,(
% 5.45/1.07    v3_pre_topc(sK5,sK4) | v5_pre_topc(k7_tmap_1(sK4,sK5),sK4,k6_tmap_1(sK4,sK5))),
% 5.45/1.07    inference(cnf_transformation,[],[f58])).
% 5.45/1.07  fof(f4657,plain,(
% 5.45/1.07    k6_tmap_1(sK4,sK5) != g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4)) | ~sP0(sK4,k6_partfun1(k2_struct_0(sK4)),k6_tmap_1(sK4,sK5)) | ~sP1(k6_tmap_1(sK4,sK5),k6_partfun1(k2_struct_0(sK4)),sK4)),
% 5.45/1.07    inference(resolution,[],[f4631,f86])).
% 5.45/1.07  fof(f86,plain,(
% 5.45/1.07    ( ! [X2,X0,X1] : (v5_pre_topc(X1,X2,X0) | ~sP0(X2,X1,X0) | ~sP1(X0,X1,X2)) )),
% 5.45/1.07    inference(cnf_transformation,[],[f60])).
% 5.45/1.07  fof(f4631,plain,(
% 5.45/1.07    ~v5_pre_topc(k6_partfun1(k2_struct_0(sK4)),sK4,k6_tmap_1(sK4,sK5)) | k6_tmap_1(sK4,sK5) != g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4))),
% 5.45/1.07    inference(subsumption_resolution,[],[f860,f656])).
% 5.45/1.07  fof(f860,plain,(
% 5.45/1.07    k6_tmap_1(sK4,sK5) != g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4)) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK4),k2_struct_0(sK4)))) | ~v5_pre_topc(k6_partfun1(k2_struct_0(sK4)),sK4,k6_tmap_1(sK4,sK5))),
% 5.45/1.07    inference(subsumption_resolution,[],[f859,f281])).
% 5.45/1.07  fof(f859,plain,(
% 5.45/1.07    ~m1_subset_1(sK5,k1_zfmisc_1(k2_struct_0(sK4))) | k6_tmap_1(sK4,sK5) != g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4)) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK4),k2_struct_0(sK4)))) | ~v5_pre_topc(k6_partfun1(k2_struct_0(sK4)),sK4,k6_tmap_1(sK4,sK5))),
% 5.45/1.07    inference(forward_demodulation,[],[f858,f215])).
% 5.45/1.07  fof(f858,plain,(
% 5.45/1.07    k6_tmap_1(sK4,sK5) != g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4)) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK4),k2_struct_0(sK4)))) | ~v5_pre_topc(k6_partfun1(k2_struct_0(sK4)),sK4,k6_tmap_1(sK4,sK5)) | ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))),
% 5.45/1.07    inference(forward_demodulation,[],[f857,f215])).
% 5.45/1.07  fof(f857,plain,(
% 5.45/1.07    ~m1_subset_1(k6_partfun1(k2_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK4),k2_struct_0(sK4)))) | ~v5_pre_topc(k6_partfun1(k2_struct_0(sK4)),sK4,k6_tmap_1(sK4,sK5)) | k6_tmap_1(sK4,sK5) != g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) | ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))),
% 5.45/1.07    inference(subsumption_resolution,[],[f856,f74])).
% 5.45/1.07  fof(f856,plain,(
% 5.45/1.07    ~m1_subset_1(k6_partfun1(k2_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK4),k2_struct_0(sK4)))) | ~v5_pre_topc(k6_partfun1(k2_struct_0(sK4)),sK4,k6_tmap_1(sK4,sK5)) | k6_tmap_1(sK4,sK5) != g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) | ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) | v2_struct_0(sK4)),
% 5.45/1.07    inference(subsumption_resolution,[],[f855,f75])).
% 5.45/1.07  fof(f855,plain,(
% 5.45/1.07    ~m1_subset_1(k6_partfun1(k2_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK4),k2_struct_0(sK4)))) | ~v5_pre_topc(k6_partfun1(k2_struct_0(sK4)),sK4,k6_tmap_1(sK4,sK5)) | k6_tmap_1(sK4,sK5) != g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) | ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)),
% 5.45/1.07    inference(subsumption_resolution,[],[f853,f76])).
% 5.45/1.07  fof(f853,plain,(
% 5.45/1.07    ~m1_subset_1(k6_partfun1(k2_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK4),k2_struct_0(sK4)))) | ~v5_pre_topc(k6_partfun1(k2_struct_0(sK4)),sK4,k6_tmap_1(sK4,sK5)) | k6_tmap_1(sK4,sK5) != g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) | ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)),
% 5.45/1.07    inference(resolution,[],[f847,f103])).
% 5.45/1.07  fof(f103,plain,(
% 5.45/1.07    ( ! [X0,X1] : (v3_pre_topc(X1,X0) | k6_tmap_1(X0,X1) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 5.45/1.07    inference(cnf_transformation,[],[f67])).
% 5.45/1.07  fof(f847,plain,(
% 5.45/1.07    ~v3_pre_topc(sK5,sK4) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK4),k2_struct_0(sK4)))) | ~v5_pre_topc(k6_partfun1(k2_struct_0(sK4)),sK4,k6_tmap_1(sK4,sK5))),
% 5.45/1.07    inference(subsumption_resolution,[],[f846,f420])).
% 5.45/1.07  fof(f846,plain,(
% 5.45/1.07    ~v1_funct_1(k6_partfun1(k2_struct_0(sK4))) | ~v5_pre_topc(k6_partfun1(k2_struct_0(sK4)),sK4,k6_tmap_1(sK4,sK5)) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK4),k2_struct_0(sK4)))) | ~v3_pre_topc(sK5,sK4)),
% 5.45/1.07    inference(forward_demodulation,[],[f845,f573])).
% 5.45/1.07  fof(f845,plain,(
% 5.45/1.07    ~v5_pre_topc(k6_partfun1(k2_struct_0(sK4)),sK4,k6_tmap_1(sK4,sK5)) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK4),k2_struct_0(sK4)))) | ~v1_funct_1(k7_tmap_1(sK4,sK5)) | ~v3_pre_topc(sK5,sK4)),
% 5.45/1.07    inference(subsumption_resolution,[],[f844,f653])).
% 5.45/1.07  fof(f844,plain,(
% 5.45/1.07    ~v1_funct_2(k6_partfun1(k2_struct_0(sK4)),k2_struct_0(sK4),k2_struct_0(sK4)) | ~v5_pre_topc(k6_partfun1(k2_struct_0(sK4)),sK4,k6_tmap_1(sK4,sK5)) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK4),k2_struct_0(sK4)))) | ~v1_funct_1(k7_tmap_1(sK4,sK5)) | ~v3_pre_topc(sK5,sK4)),
% 5.45/1.07    inference(forward_demodulation,[],[f843,f573])).
% 5.45/1.07  fof(f843,plain,(
% 5.45/1.07    ~v1_funct_2(k7_tmap_1(sK4,sK5),k2_struct_0(sK4),k2_struct_0(sK4)) | ~v5_pre_topc(k6_partfun1(k2_struct_0(sK4)),sK4,k6_tmap_1(sK4,sK5)) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK4),k2_struct_0(sK4)))) | ~v1_funct_1(k7_tmap_1(sK4,sK5)) | ~v3_pre_topc(sK5,sK4)),
% 5.45/1.07    inference(forward_demodulation,[],[f842,f215])).
% 5.45/1.07  fof(f842,plain,(
% 5.45/1.07    ~v1_funct_2(k7_tmap_1(sK4,sK5),u1_struct_0(sK4),k2_struct_0(sK4)) | ~v5_pre_topc(k6_partfun1(k2_struct_0(sK4)),sK4,k6_tmap_1(sK4,sK5)) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK4),k2_struct_0(sK4)))) | ~v1_funct_1(k7_tmap_1(sK4,sK5)) | ~v3_pre_topc(sK5,sK4)),
% 5.45/1.07    inference(forward_demodulation,[],[f841,f574])).
% 5.45/1.07  fof(f841,plain,(
% 5.45/1.07    ~v5_pre_topc(k6_partfun1(k2_struct_0(sK4)),sK4,k6_tmap_1(sK4,sK5)) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK4),k2_struct_0(sK4)))) | ~v1_funct_2(k7_tmap_1(sK4,sK5),u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK5))) | ~v1_funct_1(k7_tmap_1(sK4,sK5)) | ~v3_pre_topc(sK5,sK4)),
% 5.45/1.07    inference(forward_demodulation,[],[f840,f573])).
% 5.45/1.07  fof(f840,plain,(
% 5.45/1.07    ~m1_subset_1(k6_partfun1(k2_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK4),k2_struct_0(sK4)))) | ~v5_pre_topc(k7_tmap_1(sK4,sK5),sK4,k6_tmap_1(sK4,sK5)) | ~v1_funct_2(k7_tmap_1(sK4,sK5),u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK5))) | ~v1_funct_1(k7_tmap_1(sK4,sK5)) | ~v3_pre_topc(sK5,sK4)),
% 5.45/1.07    inference(forward_demodulation,[],[f839,f573])).
% 5.45/1.07  fof(f839,plain,(
% 5.45/1.07    ~m1_subset_1(k7_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK4),k2_struct_0(sK4)))) | ~v5_pre_topc(k7_tmap_1(sK4,sK5),sK4,k6_tmap_1(sK4,sK5)) | ~v1_funct_2(k7_tmap_1(sK4,sK5),u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK5))) | ~v1_funct_1(k7_tmap_1(sK4,sK5)) | ~v3_pre_topc(sK5,sK4)),
% 5.45/1.07    inference(forward_demodulation,[],[f838,f215])).
% 5.45/1.07  fof(f838,plain,(
% 5.45/1.07    ~m1_subset_1(k7_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),k2_struct_0(sK4)))) | ~v5_pre_topc(k7_tmap_1(sK4,sK5),sK4,k6_tmap_1(sK4,sK5)) | ~v1_funct_2(k7_tmap_1(sK4,sK5),u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK5))) | ~v1_funct_1(k7_tmap_1(sK4,sK5)) | ~v3_pre_topc(sK5,sK4)),
% 5.45/1.07    inference(forward_demodulation,[],[f82,f574])).
% 5.45/1.07  fof(f82,plain,(
% 5.45/1.07    ~m1_subset_1(k7_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK5))))) | ~v5_pre_topc(k7_tmap_1(sK4,sK5),sK4,k6_tmap_1(sK4,sK5)) | ~v1_funct_2(k7_tmap_1(sK4,sK5),u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK5))) | ~v1_funct_1(k7_tmap_1(sK4,sK5)) | ~v3_pre_topc(sK5,sK4)),
% 5.45/1.07    inference(cnf_transformation,[],[f58])).
% 5.45/1.07  fof(f8865,plain,(
% 5.45/1.07    ~v1_funct_2(k6_partfun1(k2_struct_0(sK4)),u1_struct_0(sK4),k2_struct_0(sK4)) | k1_xboole_0 != k2_struct_0(sK4) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),k2_struct_0(sK4)))) | ~sP0(sK4,k6_partfun1(k2_struct_0(sK4)),k6_tmap_1(sK4,sK5))),
% 5.45/1.07    inference(subsumption_resolution,[],[f8864,f76])).
% 5.45/1.07  fof(f8864,plain,(
% 5.45/1.07    ~v1_funct_2(k6_partfun1(k2_struct_0(sK4)),u1_struct_0(sK4),k2_struct_0(sK4)) | k1_xboole_0 != k2_struct_0(sK4) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),k2_struct_0(sK4)))) | ~l1_pre_topc(sK4) | ~sP0(sK4,k6_partfun1(k2_struct_0(sK4)),k6_tmap_1(sK4,sK5))),
% 5.45/1.07    inference(subsumption_resolution,[],[f8860,f420])).
% 5.45/1.07  fof(f8860,plain,(
% 5.45/1.07    ~v1_funct_2(k6_partfun1(k2_struct_0(sK4)),u1_struct_0(sK4),k2_struct_0(sK4)) | k1_xboole_0 != k2_struct_0(sK4) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),k2_struct_0(sK4)))) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK4))) | ~l1_pre_topc(sK4) | ~sP0(sK4,k6_partfun1(k2_struct_0(sK4)),k6_tmap_1(sK4,sK5))),
% 5.45/1.07    inference(resolution,[],[f669,f7720])).
% 5.45/1.07  fof(f669,plain,(
% 5.45/1.07    ( ! [X26,X25] : (sP1(k6_tmap_1(sK4,sK5),X25,X26) | ~v1_funct_2(X25,u1_struct_0(X26),k2_struct_0(sK4)) | k1_xboole_0 != k2_struct_0(X26) | ~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X26),k2_struct_0(sK4)))) | ~v1_funct_1(X25) | ~l1_pre_topc(X26)) )),
% 5.45/1.07    inference(subsumption_resolution,[],[f627,f274])).
% 5.45/1.07  fof(f627,plain,(
% 5.45/1.07    ( ! [X26,X25] : (~v1_funct_2(X25,u1_struct_0(X26),k2_struct_0(sK4)) | sP1(k6_tmap_1(sK4,sK5),X25,X26) | k1_xboole_0 != k2_struct_0(X26) | ~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X26),k2_struct_0(sK4)))) | ~v1_funct_1(X25) | ~l1_pre_topc(k6_tmap_1(sK4,sK5)) | ~l1_pre_topc(X26)) )),
% 5.45/1.07    inference(superposition,[],[f92,f574])).
% 5.45/1.07  fof(f92,plain,(
% 5.45/1.07    ( ! [X2,X0,X1] : (sP1(X1,X2,X0) | k2_struct_0(X0) != k1_xboole_0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 5.45/1.07    inference(cnf_transformation,[],[f49])).
% 5.45/1.07  fof(f12913,plain,(
% 5.45/1.07    ~m1_subset_1(sK6(sK4,k6_partfun1(k2_struct_0(sK4)),k6_tmap_1(sK4,sK5)),k1_zfmisc_1(k2_struct_0(sK4)))),
% 5.45/1.07    inference(subsumption_resolution,[],[f12901,f9611])).
% 5.45/1.07  fof(f9611,plain,(
% 5.45/1.07    v3_pre_topc(sK6(sK4,k6_partfun1(k2_struct_0(sK4)),k6_tmap_1(sK4,sK5)),sK4)),
% 5.45/1.07    inference(subsumption_resolution,[],[f9610,f8881])).
% 5.45/1.07  fof(f9610,plain,(
% 5.45/1.07    ~m1_subset_1(sK6(sK4,k6_partfun1(k2_struct_0(sK4)),k6_tmap_1(sK4,sK5)),k1_zfmisc_1(k2_struct_0(sK4))) | v3_pre_topc(sK6(sK4,k6_partfun1(k2_struct_0(sK4)),k6_tmap_1(sK4,sK5)),sK4)),
% 5.45/1.07    inference(forward_demodulation,[],[f9609,f215])).
% 5.45/1.07  fof(f9609,plain,(
% 5.45/1.07    v3_pre_topc(sK6(sK4,k6_partfun1(k2_struct_0(sK4)),k6_tmap_1(sK4,sK5)),sK4) | ~m1_subset_1(sK6(sK4,k6_partfun1(k2_struct_0(sK4)),k6_tmap_1(sK4,sK5)),k1_zfmisc_1(u1_struct_0(sK4)))),
% 5.45/1.07    inference(subsumption_resolution,[],[f9602,f76])).
% 5.45/1.07  fof(f9602,plain,(
% 5.45/1.07    v3_pre_topc(sK6(sK4,k6_partfun1(k2_struct_0(sK4)),k6_tmap_1(sK4,sK5)),sK4) | ~m1_subset_1(sK6(sK4,k6_partfun1(k2_struct_0(sK4)),k6_tmap_1(sK4,sK5)),k1_zfmisc_1(u1_struct_0(sK4))) | ~l1_pre_topc(sK4)),
% 5.45/1.07    inference(resolution,[],[f9594,f94])).
% 5.45/1.07  fof(f94,plain,(
% 5.45/1.07    ( ! [X0,X1] : (v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 5.45/1.07    inference(cnf_transformation,[],[f65])).
% 5.45/1.07  fof(f65,plain,(
% 5.45/1.07    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0))) & (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 5.45/1.07    inference(nnf_transformation,[],[f27])).
% 5.45/1.07  fof(f27,plain,(
% 5.45/1.07    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 5.45/1.07    inference(ennf_transformation,[],[f5])).
% 5.45/1.07  fof(f5,axiom,(
% 5.45/1.07    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 5.45/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).
% 5.45/1.07  fof(f9594,plain,(
% 5.45/1.07    r2_hidden(sK6(sK4,k6_partfun1(k2_struct_0(sK4)),k6_tmap_1(sK4,sK5)),u1_pre_topc(sK4))),
% 5.45/1.07    inference(subsumption_resolution,[],[f9593,f8881])).
% 5.45/1.07  fof(f9593,plain,(
% 5.45/1.07    ~m1_subset_1(sK6(sK4,k6_partfun1(k2_struct_0(sK4)),k6_tmap_1(sK4,sK5)),k1_zfmisc_1(k2_struct_0(sK4))) | r2_hidden(sK6(sK4,k6_partfun1(k2_struct_0(sK4)),k6_tmap_1(sK4,sK5)),u1_pre_topc(sK4))),
% 5.45/1.07    inference(forward_demodulation,[],[f9592,f574])).
% 5.45/1.07  fof(f9592,plain,(
% 5.45/1.07    r2_hidden(sK6(sK4,k6_partfun1(k2_struct_0(sK4)),k6_tmap_1(sK4,sK5)),u1_pre_topc(sK4)) | ~m1_subset_1(sK6(sK4,k6_partfun1(k2_struct_0(sK4)),k6_tmap_1(sK4,sK5)),k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK4,sK5))))),
% 5.45/1.07    inference(forward_demodulation,[],[f9591,f8963])).
% 5.45/1.07  fof(f8963,plain,(
% 5.45/1.07    u1_pre_topc(sK4) = u1_pre_topc(k6_tmap_1(sK4,sK5))),
% 5.45/1.07    inference(backward_demodulation,[],[f250,f8931])).
% 5.45/1.07  fof(f8931,plain,(
% 5.45/1.07    u1_pre_topc(sK4) = k5_tmap_1(sK4,sK5)),
% 5.45/1.07    inference(resolution,[],[f8921,f559])).
% 5.45/1.07  fof(f559,plain,(
% 5.45/1.07    ~v3_pre_topc(sK5,sK4) | u1_pre_topc(sK4) = k5_tmap_1(sK4,sK5)),
% 5.45/1.07    inference(subsumption_resolution,[],[f558,f281])).
% 5.45/1.07  fof(f558,plain,(
% 5.45/1.07    ~m1_subset_1(sK5,k1_zfmisc_1(k2_struct_0(sK4))) | ~v3_pre_topc(sK5,sK4) | u1_pre_topc(sK4) = k5_tmap_1(sK4,sK5)),
% 5.45/1.07    inference(forward_demodulation,[],[f557,f215])).
% 5.45/1.07  fof(f557,plain,(
% 5.45/1.07    ~v3_pre_topc(sK5,sK4) | u1_pre_topc(sK4) = k5_tmap_1(sK4,sK5) | ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))),
% 5.45/1.07    inference(subsumption_resolution,[],[f556,f74])).
% 5.45/1.07  fof(f556,plain,(
% 5.45/1.07    ~v3_pre_topc(sK5,sK4) | u1_pre_topc(sK4) = k5_tmap_1(sK4,sK5) | ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) | v2_struct_0(sK4)),
% 5.45/1.07    inference(subsumption_resolution,[],[f555,f75])).
% 5.45/1.07  fof(f555,plain,(
% 5.45/1.07    ~v3_pre_topc(sK5,sK4) | u1_pre_topc(sK4) = k5_tmap_1(sK4,sK5) | ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)),
% 5.45/1.07    inference(subsumption_resolution,[],[f553,f76])).
% 5.45/1.07  fof(f553,plain,(
% 5.45/1.07    ~v3_pre_topc(sK5,sK4) | u1_pre_topc(sK4) = k5_tmap_1(sK4,sK5) | ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)),
% 5.45/1.07    inference(resolution,[],[f240,f104])).
% 5.45/1.07  fof(f104,plain,(
% 5.45/1.07    ( ! [X0,X1] : (u1_pre_topc(X0) = k5_tmap_1(X0,X1) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 5.45/1.07    inference(cnf_transformation,[],[f68])).
% 5.45/1.07  fof(f68,plain,(
% 5.45/1.07    ! [X0] : (! [X1] : (((r2_hidden(X1,u1_pre_topc(X0)) | u1_pre_topc(X0) != k5_tmap_1(X0,X1)) & (u1_pre_topc(X0) = k5_tmap_1(X0,X1) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 5.45/1.07    inference(nnf_transformation,[],[f37])).
% 5.45/1.07  fof(f37,plain,(
% 5.45/1.07    ! [X0] : (! [X1] : ((r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 5.45/1.07    inference(flattening,[],[f36])).
% 5.45/1.07  fof(f36,plain,(
% 5.45/1.07    ! [X0] : (! [X1] : ((r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 5.45/1.07    inference(ennf_transformation,[],[f13])).
% 5.45/1.07  fof(f13,axiom,(
% 5.45/1.07    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1))))),
% 5.45/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_tmap_1)).
% 5.45/1.07  fof(f240,plain,(
% 5.45/1.07    r2_hidden(sK5,u1_pre_topc(sK4)) | ~v3_pre_topc(sK5,sK4)),
% 5.45/1.07    inference(subsumption_resolution,[],[f222,f76])).
% 5.45/1.07  fof(f222,plain,(
% 5.45/1.07    r2_hidden(sK5,u1_pre_topc(sK4)) | ~v3_pre_topc(sK5,sK4) | ~l1_pre_topc(sK4)),
% 5.45/1.07    inference(resolution,[],[f77,f93])).
% 5.45/1.07  fof(f93,plain,(
% 5.45/1.07    ( ! [X0,X1] : (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 5.45/1.07    inference(cnf_transformation,[],[f65])).
% 5.45/1.07  fof(f8921,plain,(
% 5.45/1.07    v3_pre_topc(sK5,sK4)),
% 5.45/1.07    inference(trivial_inequality_removal,[],[f8895])).
% 5.45/1.07  fof(f8895,plain,(
% 5.45/1.07    k6_tmap_1(sK4,sK5) != k6_tmap_1(sK4,sK5) | v3_pre_topc(sK5,sK4)),
% 5.45/1.07    inference(backward_demodulation,[],[f1457,f8877])).
% 5.45/1.07  fof(f8877,plain,(
% 5.45/1.07    k6_tmap_1(sK4,sK5) = g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4))),
% 5.45/1.07    inference(subsumption_resolution,[],[f8876,f656])).
% 5.45/1.07  fof(f8876,plain,(
% 5.45/1.07    ~m1_subset_1(k6_partfun1(k2_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK4),k2_struct_0(sK4)))) | k6_tmap_1(sK4,sK5) = g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4))),
% 5.45/1.07    inference(forward_demodulation,[],[f8875,f215])).
% 5.45/1.07  fof(f8875,plain,(
% 5.45/1.07    ~m1_subset_1(k6_partfun1(k2_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),k2_struct_0(sK4)))) | k6_tmap_1(sK4,sK5) = g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4))),
% 5.45/1.07    inference(subsumption_resolution,[],[f8874,f653])).
% 5.45/1.07  fof(f8874,plain,(
% 5.45/1.07    ~v1_funct_2(k6_partfun1(k2_struct_0(sK4)),k2_struct_0(sK4),k2_struct_0(sK4)) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),k2_struct_0(sK4)))) | k6_tmap_1(sK4,sK5) = g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4))),
% 5.45/1.07    inference(forward_demodulation,[],[f8873,f215])).
% 5.45/1.07  fof(f8873,plain,(
% 5.45/1.07    ~v1_funct_2(k6_partfun1(k2_struct_0(sK4)),u1_struct_0(sK4),k2_struct_0(sK4)) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),k2_struct_0(sK4)))) | k6_tmap_1(sK4,sK5) = g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4))),
% 5.45/1.07    inference(subsumption_resolution,[],[f8872,f7613])).
% 5.45/1.07  fof(f7613,plain,(
% 5.45/1.07    k6_tmap_1(sK4,sK5) = g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4)) | k1_xboole_0 = k2_struct_0(sK4)),
% 5.45/1.07    inference(forward_demodulation,[],[f7612,f650])).
% 5.45/1.07  fof(f7612,plain,(
% 5.45/1.07    k6_tmap_1(sK4,sK5) = g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4)) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK4,sK5))),
% 5.45/1.07    inference(subsumption_resolution,[],[f7611,f653])).
% 5.45/1.07  fof(f7611,plain,(
% 5.45/1.07    ~v1_funct_2(k6_partfun1(k2_struct_0(sK4)),k2_struct_0(sK4),k2_struct_0(sK4)) | k6_tmap_1(sK4,sK5) = g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4)) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK4,sK5))),
% 5.45/1.07    inference(forward_demodulation,[],[f7610,f574])).
% 5.45/1.07  fof(f7610,plain,(
% 5.45/1.07    k6_tmap_1(sK4,sK5) = g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4)) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK4)),k2_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK5))) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK4,sK5))),
% 5.45/1.07    inference(subsumption_resolution,[],[f7609,f656])).
% 5.45/1.07  fof(f7609,plain,(
% 5.45/1.07    ~m1_subset_1(k6_partfun1(k2_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK4),k2_struct_0(sK4)))) | k6_tmap_1(sK4,sK5) = g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4)) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK4)),k2_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK5))) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK4,sK5))),
% 5.45/1.07    inference(forward_demodulation,[],[f7608,f574])).
% 5.45/1.07  fof(f7608,plain,(
% 5.45/1.07    k6_tmap_1(sK4,sK5) = g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4)) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK5))))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK4)),k2_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK5))) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK4,sK5))),
% 5.45/1.07    inference(subsumption_resolution,[],[f7607,f274])).
% 5.45/1.07  fof(f7607,plain,(
% 5.45/1.07    k6_tmap_1(sK4,sK5) = g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4)) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK5))))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK4)),k2_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK5))) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK4,sK5)) | ~l1_pre_topc(k6_tmap_1(sK4,sK5))),
% 5.45/1.07    inference(subsumption_resolution,[],[f7602,f420])).
% 5.45/1.07  fof(f7602,plain,(
% 5.45/1.07    k6_tmap_1(sK4,sK5) = g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4)) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK5))))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK4)),k2_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK5))) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK4,sK5)) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK4))) | ~l1_pre_topc(k6_tmap_1(sK4,sK5))),
% 5.45/1.07    inference(resolution,[],[f7589,f4243])).
% 5.45/1.07  fof(f8872,plain,(
% 5.45/1.07    ~v1_funct_2(k6_partfun1(k2_struct_0(sK4)),u1_struct_0(sK4),k2_struct_0(sK4)) | k1_xboole_0 != k2_struct_0(sK4) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),k2_struct_0(sK4)))) | k6_tmap_1(sK4,sK5) = g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4))),
% 5.45/1.07    inference(subsumption_resolution,[],[f8871,f76])).
% 5.45/1.07  fof(f8871,plain,(
% 5.45/1.07    ~v1_funct_2(k6_partfun1(k2_struct_0(sK4)),u1_struct_0(sK4),k2_struct_0(sK4)) | k1_xboole_0 != k2_struct_0(sK4) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),k2_struct_0(sK4)))) | ~l1_pre_topc(sK4) | k6_tmap_1(sK4,sK5) = g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4))),
% 5.45/1.07    inference(subsumption_resolution,[],[f8861,f420])).
% 5.45/1.07  fof(f8861,plain,(
% 5.45/1.07    ~v1_funct_2(k6_partfun1(k2_struct_0(sK4)),u1_struct_0(sK4),k2_struct_0(sK4)) | k1_xboole_0 != k2_struct_0(sK4) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),k2_struct_0(sK4)))) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK4))) | ~l1_pre_topc(sK4) | k6_tmap_1(sK4,sK5) = g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4))),
% 5.45/1.07    inference(resolution,[],[f669,f7589])).
% 5.45/1.07  fof(f1457,plain,(
% 5.45/1.07    v3_pre_topc(sK5,sK4) | k6_tmap_1(sK4,sK5) != g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4))),
% 5.45/1.07    inference(forward_demodulation,[],[f256,f215])).
% 5.45/1.07  fof(f256,plain,(
% 5.45/1.07    v3_pre_topc(sK5,sK4) | k6_tmap_1(sK4,sK5) != g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),
% 5.45/1.07    inference(subsumption_resolution,[],[f255,f74])).
% 5.45/1.07  fof(f255,plain,(
% 5.45/1.07    v3_pre_topc(sK5,sK4) | k6_tmap_1(sK4,sK5) != g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) | v2_struct_0(sK4)),
% 5.45/1.07    inference(subsumption_resolution,[],[f254,f75])).
% 5.45/1.07  fof(f254,plain,(
% 5.45/1.07    v3_pre_topc(sK5,sK4) | k6_tmap_1(sK4,sK5) != g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)),
% 5.45/1.07    inference(subsumption_resolution,[],[f228,f76])).
% 5.45/1.07  fof(f228,plain,(
% 5.45/1.07    v3_pre_topc(sK5,sK4) | k6_tmap_1(sK4,sK5) != g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)),
% 5.45/1.07    inference(resolution,[],[f77,f103])).
% 5.45/1.07  fof(f250,plain,(
% 5.45/1.07    k5_tmap_1(sK4,sK5) = u1_pre_topc(k6_tmap_1(sK4,sK5))),
% 5.45/1.07    inference(subsumption_resolution,[],[f249,f74])).
% 5.45/1.07  fof(f249,plain,(
% 5.45/1.07    k5_tmap_1(sK4,sK5) = u1_pre_topc(k6_tmap_1(sK4,sK5)) | v2_struct_0(sK4)),
% 5.45/1.07    inference(subsumption_resolution,[],[f248,f75])).
% 5.45/1.07  fof(f248,plain,(
% 5.45/1.07    k5_tmap_1(sK4,sK5) = u1_pre_topc(k6_tmap_1(sK4,sK5)) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)),
% 5.45/1.07    inference(subsumption_resolution,[],[f226,f76])).
% 5.45/1.07  fof(f226,plain,(
% 5.45/1.07    k5_tmap_1(sK4,sK5) = u1_pre_topc(k6_tmap_1(sK4,sK5)) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)),
% 5.45/1.07    inference(resolution,[],[f77,f101])).
% 5.45/1.07  fof(f101,plain,(
% 5.45/1.07    ( ! [X0,X1] : (k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 5.45/1.07    inference(cnf_transformation,[],[f33])).
% 5.45/1.07  fof(f9591,plain,(
% 5.45/1.07    r2_hidden(sK6(sK4,k6_partfun1(k2_struct_0(sK4)),k6_tmap_1(sK4,sK5)),u1_pre_topc(k6_tmap_1(sK4,sK5))) | ~m1_subset_1(sK6(sK4,k6_partfun1(k2_struct_0(sK4)),k6_tmap_1(sK4,sK5)),k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK4,sK5))))),
% 5.45/1.07    inference(subsumption_resolution,[],[f9580,f274])).
% 5.45/1.07  fof(f9580,plain,(
% 5.45/1.07    r2_hidden(sK6(sK4,k6_partfun1(k2_struct_0(sK4)),k6_tmap_1(sK4,sK5)),u1_pre_topc(k6_tmap_1(sK4,sK5))) | ~m1_subset_1(sK6(sK4,k6_partfun1(k2_struct_0(sK4)),k6_tmap_1(sK4,sK5)),k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK4,sK5)))) | ~l1_pre_topc(k6_tmap_1(sK4,sK5))),
% 5.45/1.07    inference(resolution,[],[f8883,f93])).
% 5.45/1.07  fof(f8883,plain,(
% 5.45/1.07    v3_pre_topc(sK6(sK4,k6_partfun1(k2_struct_0(sK4)),k6_tmap_1(sK4,sK5)),k6_tmap_1(sK4,sK5))),
% 5.45/1.07    inference(resolution,[],[f8870,f89])).
% 5.45/1.07  fof(f89,plain,(
% 5.45/1.07    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | v3_pre_topc(sK6(X0,X1,X2),X2)) )),
% 5.45/1.07    inference(cnf_transformation,[],[f64])).
% 5.45/1.07  fof(f12901,plain,(
% 5.45/1.07    ~v3_pre_topc(sK6(sK4,k6_partfun1(k2_struct_0(sK4)),k6_tmap_1(sK4,sK5)),sK4) | ~m1_subset_1(sK6(sK4,k6_partfun1(k2_struct_0(sK4)),k6_tmap_1(sK4,sK5)),k1_zfmisc_1(k2_struct_0(sK4)))),
% 5.45/1.07    inference(superposition,[],[f8887,f107])).
% 5.45/1.07  fof(f8887,plain,(
% 5.45/1.07    ~v3_pre_topc(k8_relset_1(k2_struct_0(sK4),k2_struct_0(sK4),k6_partfun1(k2_struct_0(sK4)),sK6(sK4,k6_partfun1(k2_struct_0(sK4)),k6_tmap_1(sK4,sK5))),sK4)),
% 5.45/1.07    inference(forward_demodulation,[],[f8879,f574])).
% 5.45/1.07  fof(f8879,plain,(
% 5.45/1.07    ~v3_pre_topc(k8_relset_1(k2_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK5)),k6_partfun1(k2_struct_0(sK4)),sK6(sK4,k6_partfun1(k2_struct_0(sK4)),k6_tmap_1(sK4,sK5))),sK4)),
% 5.45/1.07    inference(resolution,[],[f8870,f447])).
% 5.45/1.07  fof(f447,plain,(
% 5.45/1.07    ( ! [X12,X11] : (sP0(sK4,X12,X11) | ~v3_pre_topc(k8_relset_1(k2_struct_0(sK4),u1_struct_0(X11),X12,sK6(sK4,X12,X11)),sK4)) )),
% 5.45/1.07    inference(superposition,[],[f90,f215])).
% 5.45/1.07  fof(f90,plain,(
% 5.45/1.07    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | ~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,sK6(X0,X1,X2)),X0)) )),
% 5.45/1.07    inference(cnf_transformation,[],[f64])).
% 5.45/1.07  % SZS output end Proof for theBenchmark
% 5.45/1.07  % (6982)------------------------------
% 5.45/1.07  % (6982)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.45/1.07  % (6982)Termination reason: Refutation
% 5.45/1.07  
% 5.45/1.07  % (6982)Memory used [KB]: 5117
% 5.45/1.07  % (6982)Time elapsed: 0.658 s
% 5.45/1.07  % (6982)------------------------------
% 5.45/1.07  % (6982)------------------------------
% 5.45/1.07  % (6973)Success in time 0.702 s
%------------------------------------------------------------------------------
