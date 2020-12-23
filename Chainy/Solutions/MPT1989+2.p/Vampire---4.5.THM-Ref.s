%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1989+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:38 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 417 expanded)
%              Number of leaves         :   13 ( 143 expanded)
%              Depth                    :   13
%              Number of atoms          :  390 (3332 expanded)
%              Number of equality atoms :   18 (  19 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6155,plain,(
    $false ),
    inference(subsumption_resolution,[],[f6154,f5518])).

fof(f5518,plain,(
    ~ sP0(sK28,sK27) ),
    inference(unit_resulting_resolution,[],[f4696,f5503,f4698])).

fof(f4698,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | ~ sP0(X1,X0)
      | v4_waybel_7(X1,X0) ) ),
    inference(cnf_transformation,[],[f4475])).

fof(f4475,plain,(
    ! [X0,X1] :
      ( ( ( v4_waybel_7(X1,X0)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ v4_waybel_7(X1,X0) ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f4432])).

fof(f4432,plain,(
    ! [X0,X1] :
      ( ( v4_waybel_7(X1,X0)
      <=> sP0(X1,X0) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f5503,plain,(
    sP1(sK27,sK28) ),
    inference(unit_resulting_resolution,[],[f4688,f4689,f4690,f4691,f4692,f4693,f4694,f4706])).

fof(f4706,plain,(
    ! [X0,X1] :
      ( ~ v2_lattice3(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | sP1(X0,X1)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f4433])).

fof(f4433,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(definition_folding,[],[f4246,f4432,f4431])).

fof(f4431,plain,(
    ! [X1,X0] :
      ( sP0(X1,X0)
    <=> ? [X2] :
          ( k1_yellow_0(X0,X2) = X1
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_waybel_7(X2,X0)
          & v12_waybel_0(X2,X0)
          & v1_waybel_0(X2,X0)
          & ~ v1_xboole_0(X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f4246,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_waybel_7(X1,X0)
          <=> ? [X2] :
                ( k1_yellow_0(X0,X2) = X1
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & v1_waybel_7(X2,X0)
                & v12_waybel_0(X2,X0)
                & v1_waybel_0(X2,X0)
                & ~ v1_xboole_0(X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f4245])).

fof(f4245,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_waybel_7(X1,X0)
          <=> ? [X2] :
                ( k1_yellow_0(X0,X2) = X1
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & v1_waybel_7(X2,X0)
                & v12_waybel_0(X2,X0)
                & v1_waybel_0(X2,X0)
                & ~ v1_xboole_0(X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4128])).

fof(f4128,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v4_waybel_7(X1,X0)
          <=> ? [X2] :
                ( k1_yellow_0(X0,X2) = X1
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & v1_waybel_7(X2,X0)
                & v12_waybel_0(X2,X0)
                & v1_waybel_0(X2,X0)
                & ~ v1_xboole_0(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_waybel_7)).

fof(f4694,plain,(
    m1_subset_1(sK28,u1_struct_0(sK27)) ),
    inference(cnf_transformation,[],[f4474])).

fof(f4474,plain,
    ( ~ v4_waybel_7(sK28,sK27)
    & v5_waybel_6(sK28,sK27)
    & m1_subset_1(sK28,u1_struct_0(sK27))
    & l1_orders_2(sK27)
    & v2_lattice3(sK27)
    & v1_lattice3(sK27)
    & v5_orders_2(sK27)
    & v4_orders_2(sK27)
    & v3_orders_2(sK27) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK27,sK28])],[f4244,f4473,f4472])).

fof(f4472,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v4_waybel_7(X1,X0)
            & v5_waybel_6(X1,X0)
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
   => ( ? [X1] :
          ( ~ v4_waybel_7(X1,sK27)
          & v5_waybel_6(X1,sK27)
          & m1_subset_1(X1,u1_struct_0(sK27)) )
      & l1_orders_2(sK27)
      & v2_lattice3(sK27)
      & v1_lattice3(sK27)
      & v5_orders_2(sK27)
      & v4_orders_2(sK27)
      & v3_orders_2(sK27) ) ),
    introduced(choice_axiom,[])).

fof(f4473,plain,
    ( ? [X1] :
        ( ~ v4_waybel_7(X1,sK27)
        & v5_waybel_6(X1,sK27)
        & m1_subset_1(X1,u1_struct_0(sK27)) )
   => ( ~ v4_waybel_7(sK28,sK27)
      & v5_waybel_6(sK28,sK27)
      & m1_subset_1(sK28,u1_struct_0(sK27)) ) ),
    introduced(choice_axiom,[])).

fof(f4244,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v4_waybel_7(X1,X0)
          & v5_waybel_6(X1,X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f4243])).

fof(f4243,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v4_waybel_7(X1,X0)
          & v5_waybel_6(X1,X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4226])).

fof(f4226,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( v5_waybel_6(X1,X0)
             => v4_waybel_7(X1,X0) ) ) ) ),
    inference(negated_conjecture,[],[f4225])).

fof(f4225,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v5_waybel_6(X1,X0)
           => v4_waybel_7(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_waybel_7)).

fof(f4693,plain,(
    l1_orders_2(sK27) ),
    inference(cnf_transformation,[],[f4474])).

fof(f4692,plain,(
    v2_lattice3(sK27) ),
    inference(cnf_transformation,[],[f4474])).

fof(f4691,plain,(
    v1_lattice3(sK27) ),
    inference(cnf_transformation,[],[f4474])).

fof(f4690,plain,(
    v5_orders_2(sK27) ),
    inference(cnf_transformation,[],[f4474])).

fof(f4689,plain,(
    v4_orders_2(sK27) ),
    inference(cnf_transformation,[],[f4474])).

fof(f4688,plain,(
    v3_orders_2(sK27) ),
    inference(cnf_transformation,[],[f4474])).

fof(f4696,plain,(
    ~ v4_waybel_7(sK28,sK27) ),
    inference(cnf_transformation,[],[f4474])).

fof(f6154,plain,(
    sP0(sK28,sK27) ),
    inference(forward_demodulation,[],[f6153,f5540])).

fof(f5540,plain,(
    sK28 = k1_yellow_0(sK27,k5_waybel_0(sK27,sK28)) ),
    inference(unit_resulting_resolution,[],[f5121,f4688,f4689,f4690,f4693,f4694,f4952])).

fof(f4952,plain,(
    ! [X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4356])).

fof(f4356,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1
            & r1_yellow_0(X0,k5_waybel_0(X0,X1)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f4355])).

fof(f4355,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1
            & r1_yellow_0(X0,k5_waybel_0(X0,X1)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3274])).

fof(f3274,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1
            & r1_yellow_0(X0,k5_waybel_0(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_waybel_0)).

fof(f5121,plain,(
    ~ v2_struct_0(sK27) ),
    inference(unit_resulting_resolution,[],[f4693,f4692,f4731])).

fof(f4731,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f4256])).

fof(f4256,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f4255])).

fof(f4255,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2807])).

fof(f2807,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_lattice3)).

fof(f6153,plain,(
    sP0(k1_yellow_0(sK27,k5_waybel_0(sK27,sK28)),sK27) ),
    inference(subsumption_resolution,[],[f6152,f5383])).

fof(f5383,plain,(
    ~ v1_xboole_0(k5_waybel_0(sK27,sK28)) ),
    inference(unit_resulting_resolution,[],[f5121,f4688,f4693,f4694,f4947])).

fof(f4947,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k5_waybel_0(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4350])).

fof(f4350,plain,(
    ! [X0,X1] :
      ( ( v1_waybel_0(k5_waybel_0(X0,X1),X0)
        & ~ v1_xboole_0(k5_waybel_0(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f4349])).

fof(f4349,plain,(
    ! [X0,X1] :
      ( ( v1_waybel_0(k5_waybel_0(X0,X1),X0)
        & ~ v1_xboole_0(k5_waybel_0(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3219])).

fof(f3219,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_waybel_0(k5_waybel_0(X0,X1),X0)
        & ~ v1_xboole_0(k5_waybel_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_waybel_0)).

fof(f6152,plain,
    ( sP0(k1_yellow_0(sK27,k5_waybel_0(sK27,sK28)),sK27)
    | v1_xboole_0(k5_waybel_0(sK27,sK28)) ),
    inference(subsumption_resolution,[],[f6151,f5413])).

fof(f5413,plain,(
    v1_waybel_0(k5_waybel_0(sK27,sK28),sK27) ),
    inference(unit_resulting_resolution,[],[f5121,f4688,f4693,f4694,f4948])).

fof(f4948,plain,(
    ! [X0,X1] :
      ( v1_waybel_0(k5_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4350])).

fof(f6151,plain,
    ( sP0(k1_yellow_0(sK27,k5_waybel_0(sK27,sK28)),sK27)
    | ~ v1_waybel_0(k5_waybel_0(sK27,sK28),sK27)
    | v1_xboole_0(k5_waybel_0(sK27,sK28)) ),
    inference(subsumption_resolution,[],[f6150,f5411])).

fof(f5411,plain,(
    v12_waybel_0(k5_waybel_0(sK27,sK28),sK27) ),
    inference(unit_resulting_resolution,[],[f5121,f4689,f4693,f4694,f4946])).

fof(f4946,plain,(
    ! [X0,X1] :
      ( v12_waybel_0(k5_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4348])).

fof(f4348,plain,(
    ! [X0,X1] :
      ( v12_waybel_0(k5_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f4347])).

fof(f4347,plain,(
    ! [X0,X1] :
      ( v12_waybel_0(k5_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3207])).

fof(f3207,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v4_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => v12_waybel_0(k5_waybel_0(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc12_waybel_0)).

fof(f6150,plain,
    ( sP0(k1_yellow_0(sK27,k5_waybel_0(sK27,sK28)),sK27)
    | ~ v12_waybel_0(k5_waybel_0(sK27,sK28),sK27)
    | ~ v1_waybel_0(k5_waybel_0(sK27,sK28),sK27)
    | v1_xboole_0(k5_waybel_0(sK27,sK28)) ),
    inference(subsumption_resolution,[],[f6149,f5415])).

fof(f5415,plain,(
    m1_subset_1(k5_waybel_0(sK27,sK28),k1_zfmisc_1(u1_struct_0(sK27))) ),
    inference(unit_resulting_resolution,[],[f5121,f4693,f4694,f4949])).

fof(f4949,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4352])).

fof(f4352,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f4351])).

fof(f4351,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3194])).

fof(f3194,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_waybel_0)).

fof(f6149,plain,
    ( ~ m1_subset_1(k5_waybel_0(sK27,sK28),k1_zfmisc_1(u1_struct_0(sK27)))
    | sP0(k1_yellow_0(sK27,k5_waybel_0(sK27,sK28)),sK27)
    | ~ v12_waybel_0(k5_waybel_0(sK27,sK28),sK27)
    | ~ v1_waybel_0(k5_waybel_0(sK27,sK28),sK27)
    | v1_xboole_0(k5_waybel_0(sK27,sK28)) ),
    inference(resolution,[],[f5665,f5064])).

fof(f5064,plain,(
    ! [X2,X1] :
      ( ~ v1_waybel_7(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | sP0(k1_yellow_0(X1,X2),X1)
      | ~ v12_waybel_0(X2,X1)
      | ~ v1_waybel_0(X2,X1)
      | v1_xboole_0(X2) ) ),
    inference(equality_resolution,[],[f4705])).

fof(f4705,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1)
      | k1_yellow_0(X1,X2) != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v1_waybel_7(X2,X1)
      | ~ v12_waybel_0(X2,X1)
      | ~ v1_waybel_0(X2,X1)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f4479])).

fof(f4479,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ! [X2] :
            ( k1_yellow_0(X1,X2) != X0
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
            | ~ v1_waybel_7(X2,X1)
            | ~ v12_waybel_0(X2,X1)
            | ~ v1_waybel_0(X2,X1)
            | v1_xboole_0(X2) ) )
      & ( ( k1_yellow_0(X1,sK29(X0,X1)) = X0
          & m1_subset_1(sK29(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))
          & v1_waybel_7(sK29(X0,X1),X1)
          & v12_waybel_0(sK29(X0,X1),X1)
          & v1_waybel_0(sK29(X0,X1),X1)
          & ~ v1_xboole_0(sK29(X0,X1)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK29])],[f4477,f4478])).

fof(f4478,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( k1_yellow_0(X1,X3) = X0
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
          & v1_waybel_7(X3,X1)
          & v12_waybel_0(X3,X1)
          & v1_waybel_0(X3,X1)
          & ~ v1_xboole_0(X3) )
     => ( k1_yellow_0(X1,sK29(X0,X1)) = X0
        & m1_subset_1(sK29(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))
        & v1_waybel_7(sK29(X0,X1),X1)
        & v12_waybel_0(sK29(X0,X1),X1)
        & v1_waybel_0(sK29(X0,X1),X1)
        & ~ v1_xboole_0(sK29(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f4477,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ! [X2] :
            ( k1_yellow_0(X1,X2) != X0
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
            | ~ v1_waybel_7(X2,X1)
            | ~ v12_waybel_0(X2,X1)
            | ~ v1_waybel_0(X2,X1)
            | v1_xboole_0(X2) ) )
      & ( ? [X3] :
            ( k1_yellow_0(X1,X3) = X0
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
            & v1_waybel_7(X3,X1)
            & v12_waybel_0(X3,X1)
            & v1_waybel_0(X3,X1)
            & ~ v1_xboole_0(X3) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f4476])).

fof(f4476,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ! [X2] :
            ( k1_yellow_0(X0,X2) != X1
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v1_waybel_7(X2,X0)
            | ~ v12_waybel_0(X2,X0)
            | ~ v1_waybel_0(X2,X0)
            | v1_xboole_0(X2) ) )
      & ( ? [X2] :
            ( k1_yellow_0(X0,X2) = X1
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_waybel_7(X2,X0)
            & v12_waybel_0(X2,X0)
            & v1_waybel_0(X2,X0)
            & ~ v1_xboole_0(X2) )
        | ~ sP0(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f4431])).

fof(f5665,plain,(
    v1_waybel_7(k5_waybel_0(sK27,sK28),sK27) ),
    inference(unit_resulting_resolution,[],[f4688,f4689,f4690,f4691,f4692,f4693,f4695,f4694,f4707])).

fof(f4707,plain,(
    ! [X0,X1] :
      ( ~ v2_lattice3(X0)
      | ~ v5_waybel_6(X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v1_waybel_7(k5_waybel_0(X0,X1),X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f4248])).

fof(f4248,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_waybel_7(k5_waybel_0(X0,X1),X0)
          | ~ v5_waybel_6(X1,X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f4247])).

fof(f4247,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_waybel_7(k5_waybel_0(X0,X1),X0)
          | ~ v5_waybel_6(X1,X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4223])).

fof(f4223,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v5_waybel_6(X1,X0)
           => v1_waybel_7(k5_waybel_0(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_waybel_7)).

fof(f4695,plain,(
    v5_waybel_6(sK28,sK27) ),
    inference(cnf_transformation,[],[f4474])).
%------------------------------------------------------------------------------
