%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:38 EST 2020

% Result     : Theorem 2.04s
% Output     : Refutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :  165 (2597 expanded)
%              Number of leaves         :   22 ( 700 expanded)
%              Depth                    :   39
%              Number of atoms          :  649 (21827 expanded)
%              Number of equality atoms :   27 ( 175 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1300,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1239,f452])).

fof(f452,plain,(
    ~ v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f451,f71])).

fof(f71,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | ~ v1_zfmisc_1(sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,
    ( ( ~ v1_zfmisc_1(sK1)
      | ~ v2_tex_2(sK1,sK0) )
    & ( v1_zfmisc_1(sK1)
      | v2_tex_2(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & ~ v1_xboole_0(sK1)
    & l1_pre_topc(sK0)
    & v2_tdlat_3(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f48,f50,f49])).

fof(f49,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v1_zfmisc_1(X1)
              | ~ v2_tex_2(X1,X0) )
            & ( v1_zfmisc_1(X1)
              | v2_tex_2(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
        & l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v2_tex_2(X1,sK0) )
          & ( v1_zfmisc_1(X1)
            | v2_tex_2(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(sK0)
      & v2_tdlat_3(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ? [X1] :
        ( ( ~ v1_zfmisc_1(X1)
          | ~ v2_tex_2(X1,sK0) )
        & ( v1_zfmisc_1(X1)
          | v2_tex_2(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        & ~ v1_xboole_0(X1) )
   => ( ( ~ v1_zfmisc_1(sK1)
        | ~ v2_tex_2(sK1,sK0) )
      & ( v1_zfmisc_1(sK1)
        | v2_tex_2(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v2_tex_2(X1,X0) )
          & ( v1_zfmisc_1(X1)
            | v2_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v2_tex_2(X1,X0) )
          & ( v1_zfmisc_1(X1)
            | v2_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tex_2(X1,X0)
          <~> v1_zfmisc_1(X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tex_2(X1,X0)
          <~> v1_zfmisc_1(X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & ~ v1_xboole_0(X1) )
           => ( v2_tex_2(X1,X0)
            <=> v1_zfmisc_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ( v2_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tex_2)).

fof(f451,plain,
    ( v1_zfmisc_1(sK1)
    | ~ v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f450,f64])).

fof(f64,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f450,plain,
    ( v1_zfmisc_1(sK1)
    | ~ v2_tex_2(sK1,sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f449,f65])).

fof(f65,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f449,plain,
    ( v1_zfmisc_1(sK1)
    | ~ v2_tex_2(sK1,sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f448,f67])).

fof(f67,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f448,plain,
    ( v1_zfmisc_1(sK1)
    | ~ v2_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f447,f68])).

fof(f68,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f447,plain,
    ( v1_zfmisc_1(sK1)
    | ~ v2_tex_2(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f446,f69])).

fof(f69,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f51])).

fof(f446,plain,
    ( v1_zfmisc_1(sK1)
    | ~ v2_tex_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f445])).

fof(f445,plain,
    ( v1_zfmisc_1(sK1)
    | v1_zfmisc_1(sK1)
    | ~ v2_tex_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f337,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( u1_struct_0(sK2(X0,X1)) = X1
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_struct_0(sK2(X0,X1)) = X1
            & m1_pre_topc(sK2(X0,X1),X0)
            & v1_tdlat_3(sK2(X0,X1))
            & v1_pre_topc(sK2(X0,X1))
            & ~ v2_struct_0(sK2(X0,X1)) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f39,f52])).

fof(f52,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( u1_struct_0(X2) = X1
          & m1_pre_topc(X2,X0)
          & v1_tdlat_3(X2)
          & v1_pre_topc(X2)
          & ~ v2_struct_0(X2) )
     => ( u1_struct_0(sK2(X0,X1)) = X1
        & m1_pre_topc(sK2(X0,X1),X0)
        & v1_tdlat_3(sK2(X0,X1))
        & v1_pre_topc(sK2(X0,X1))
        & ~ v2_struct_0(sK2(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_tdlat_3(X2)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_tdlat_3(X2)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ~ ( ! [X2] :
                  ( ( m1_pre_topc(X2,X0)
                    & v1_tdlat_3(X2)
                    & v1_pre_topc(X2)
                    & ~ v2_struct_0(X2) )
                 => u1_struct_0(X2) != X1 )
              & v2_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_tex_2)).

fof(f337,plain,
    ( v1_zfmisc_1(u1_struct_0(sK2(sK0,sK1)))
    | v1_zfmisc_1(sK1) ),
    inference(subsumption_resolution,[],[f336,f319])).

fof(f319,plain,
    ( v7_struct_0(sK2(sK0,sK1))
    | v1_zfmisc_1(sK1) ),
    inference(subsumption_resolution,[],[f318,f208])).

fof(f208,plain,
    ( ~ v2_struct_0(sK2(sK0,sK1))
    | v1_zfmisc_1(sK1) ),
    inference(subsumption_resolution,[],[f207,f64])).

fof(f207,plain,
    ( v1_zfmisc_1(sK1)
    | ~ v2_struct_0(sK2(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f206,f65])).

fof(f206,plain,
    ( v1_zfmisc_1(sK1)
    | ~ v2_struct_0(sK2(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f205,f67])).

fof(f205,plain,
    ( v1_zfmisc_1(sK1)
    | ~ v2_struct_0(sK2(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f204,f68])).

fof(f204,plain,
    ( v1_zfmisc_1(sK1)
    | ~ v2_struct_0(sK2(sK0,sK1))
    | v1_xboole_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f200,f69])).

fof(f200,plain,
    ( v1_zfmisc_1(sK1)
    | ~ v2_struct_0(sK2(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f70,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(sK2(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f70,plain,
    ( v2_tex_2(sK1,sK0)
    | v1_zfmisc_1(sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f318,plain,
    ( v1_zfmisc_1(sK1)
    | v7_struct_0(sK2(sK0,sK1))
    | v2_struct_0(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f317,f315])).

fof(f315,plain,
    ( v2_pre_topc(sK2(sK0,sK1))
    | v1_zfmisc_1(sK1) ),
    inference(subsumption_resolution,[],[f306,f302])).

fof(f302,plain,
    ( v2_tdlat_3(sK2(sK0,sK1))
    | v1_zfmisc_1(sK1) ),
    inference(resolution,[],[f218,f115])).

fof(f115,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | v2_tdlat_3(X0) ) ),
    inference(subsumption_resolution,[],[f114,f65])).

fof(f114,plain,(
    ! [X0] :
      ( v2_tdlat_3(X0)
      | ~ m1_pre_topc(X0,sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f113,f66])).

fof(f66,plain,(
    v2_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f113,plain,(
    ! [X0] :
      ( v2_tdlat_3(X0)
      | ~ m1_pre_topc(X0,sK0)
      | ~ v2_tdlat_3(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f104,f67])).

fof(f104,plain,(
    ! [X0] :
      ( v2_tdlat_3(X0)
      | ~ m1_pre_topc(X0,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_tdlat_3(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(resolution,[],[f64,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( v2_tdlat_3(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_tdlat_3(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc6_tdlat_3)).

fof(f218,plain,
    ( m1_pre_topc(sK2(sK0,sK1),sK0)
    | v1_zfmisc_1(sK1) ),
    inference(subsumption_resolution,[],[f217,f64])).

fof(f217,plain,
    ( v1_zfmisc_1(sK1)
    | m1_pre_topc(sK2(sK0,sK1),sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f216,f65])).

fof(f216,plain,
    ( v1_zfmisc_1(sK1)
    | m1_pre_topc(sK2(sK0,sK1),sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f215,f67])).

fof(f215,plain,
    ( v1_zfmisc_1(sK1)
    | m1_pre_topc(sK2(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f214,f68])).

fof(f214,plain,
    ( v1_zfmisc_1(sK1)
    | m1_pre_topc(sK2(sK0,sK1),sK0)
    | v1_xboole_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f202,f69])).

fof(f202,plain,
    ( v1_zfmisc_1(sK1)
    | m1_pre_topc(sK2(sK0,sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f70,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(sK2(X0,X1),X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f306,plain,
    ( v1_zfmisc_1(sK1)
    | v2_pre_topc(sK2(sK0,sK1))
    | ~ v2_tdlat_3(sK2(sK0,sK1)) ),
    inference(resolution,[],[f301,f76])).

fof(f76,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tdlat_3)).

fof(f301,plain,
    ( l1_pre_topc(sK2(sK0,sK1))
    | v1_zfmisc_1(sK1) ),
    inference(resolution,[],[f218,f139])).

fof(f139,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | l1_pre_topc(X0) ) ),
    inference(resolution,[],[f67,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f317,plain,
    ( v1_zfmisc_1(sK1)
    | v7_struct_0(sK2(sK0,sK1))
    | ~ v2_pre_topc(sK2(sK0,sK1))
    | v2_struct_0(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f316,f213])).

fof(f213,plain,
    ( v1_tdlat_3(sK2(sK0,sK1))
    | v1_zfmisc_1(sK1) ),
    inference(subsumption_resolution,[],[f212,f64])).

fof(f212,plain,
    ( v1_zfmisc_1(sK1)
    | v1_tdlat_3(sK2(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f211,f65])).

fof(f211,plain,
    ( v1_zfmisc_1(sK1)
    | v1_tdlat_3(sK2(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f210,f67])).

fof(f210,plain,
    ( v1_zfmisc_1(sK1)
    | v1_tdlat_3(sK2(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f209,f68])).

fof(f209,plain,
    ( v1_zfmisc_1(sK1)
    | v1_tdlat_3(sK2(sK0,sK1))
    | v1_xboole_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f201,f69])).

fof(f201,plain,
    ( v1_zfmisc_1(sK1)
    | v1_tdlat_3(sK2(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f70,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( v1_tdlat_3(sK2(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f316,plain,
    ( v1_zfmisc_1(sK1)
    | v7_struct_0(sK2(sK0,sK1))
    | ~ v1_tdlat_3(sK2(sK0,sK1))
    | ~ v2_pre_topc(sK2(sK0,sK1))
    | v2_struct_0(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f307,f302])).

fof(f307,plain,
    ( v1_zfmisc_1(sK1)
    | v7_struct_0(sK2(sK0,sK1))
    | ~ v2_tdlat_3(sK2(sK0,sK1))
    | ~ v1_tdlat_3(sK2(sK0,sK1))
    | ~ v2_pre_topc(sK2(sK0,sK1))
    | v2_struct_0(sK2(sK0,sK1)) ),
    inference(resolution,[],[f301,f78])).

fof(f78,plain,(
    ! [X0] :
      ( v7_struct_0(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
        & v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
      | ~ v2_tdlat_3(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
        & v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
      | ~ v2_tdlat_3(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( ( v2_tdlat_3(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ( v2_pre_topc(X0)
          & v7_struct_0(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_1)).

fof(f336,plain,
    ( v1_zfmisc_1(sK1)
    | v1_zfmisc_1(u1_struct_0(sK2(sK0,sK1)))
    | ~ v7_struct_0(sK2(sK0,sK1)) ),
    inference(resolution,[],[f305,f89])).

fof(f89,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).

fof(f305,plain,
    ( l1_struct_0(sK2(sK0,sK1))
    | v1_zfmisc_1(sK1) ),
    inference(resolution,[],[f301,f75])).

fof(f75,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f1239,plain,(
    v2_tex_2(sK1,sK0) ),
    inference(backward_demodulation,[],[f939,f1206])).

fof(f1206,plain,(
    sK1 = k1_tarski(sK3(sK1)) ),
    inference(duplicate_literal_removal,[],[f1196])).

fof(f1196,plain,
    ( sK1 = k1_tarski(sK3(sK1))
    | sK1 = k1_tarski(sK3(sK1)) ),
    inference(resolution,[],[f1182,f682])).

fof(f682,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k1_tarski(sK3(sK1)))
      | sK1 = k1_tarski(sK3(sK1)) ) ),
    inference(resolution,[],[f517,f90])).

fof(f90,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f55,f56])).

fof(f56,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f54])).

fof(f54,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f517,plain,
    ( v1_xboole_0(k1_tarski(sK3(sK1)))
    | sK1 = k1_tarski(sK3(sK1)) ),
    inference(resolution,[],[f455,f156])).

fof(f156,plain,(
    r1_tarski(k1_tarski(sK3(sK1)),sK1) ),
    inference(resolution,[],[f153,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f153,plain,(
    r2_hidden(sK3(sK1),sK1) ),
    inference(resolution,[],[f68,f91])).

fof(f91,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK3(X0),X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f455,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | sK1 = X0
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f454,f68])).

fof(f454,plain,(
    ! [X0] :
      ( sK1 = X0
      | ~ r1_tarski(X0,sK1)
      | v1_xboole_0(sK1)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f453,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X0,X1)
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

fof(f453,plain,(
    v1_zfmisc_1(sK1) ),
    inference(resolution,[],[f452,f70])).

fof(f1182,plain,(
    ! [X0] :
      ( r2_hidden(sK3(sK1),X0)
      | sK1 = k1_tarski(sK3(sK1)) ) ),
    inference(resolution,[],[f1127,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f1127,plain,(
    ! [X0] :
      ( r1_tarski(k1_tarski(sK3(sK1)),X0)
      | sK1 = k1_tarski(sK3(sK1)) ) ),
    inference(resolution,[],[f682,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f59,f60])).

fof(f60,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f45,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f939,plain,(
    v2_tex_2(k1_tarski(sK3(sK1)),sK0) ),
    inference(forward_demodulation,[],[f938,f867])).

fof(f867,plain,(
    k1_tarski(sK3(sK1)) = k6_domain_1(u1_struct_0(sK0),sK3(sK1)) ),
    inference(resolution,[],[f433,f153])).

fof(f433,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK1)
      | k1_tarski(X1) = k6_domain_1(u1_struct_0(sK0),X1) ) ),
    inference(subsumption_resolution,[],[f429,f185])).

fof(f185,plain,(
    ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f167,f68])).

fof(f167,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f69,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f429,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK1)
      | k1_tarski(X1) = k6_domain_1(u1_struct_0(sK0),X1)
      | v1_xboole_0(u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f357,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f357,plain,(
    ! [X3] :
      ( m1_subset_1(X3,u1_struct_0(sK0))
      | ~ r2_hidden(X3,sK1) ) ),
    inference(resolution,[],[f196,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f196,plain,(
    ! [X0] :
      ( r2_hidden(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f166,f95])).

fof(f95,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f166,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f69,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f938,plain,(
    v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK3(sK1)),sK0) ),
    inference(subsumption_resolution,[],[f937,f64])).

fof(f937,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK3(sK1)),sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f936,f65])).

fof(f936,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK3(sK1)),sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f934,f67])).

fof(f934,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK3(sK1)),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f932,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).

fof(f932,plain,(
    m1_subset_1(sK3(sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f929,f93])).

fof(f929,plain,(
    r2_hidden(sK3(sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f924,f730])).

fof(f730,plain,(
    ! [X6] :
      ( ~ r1_tarski(u1_struct_0(sK0),X6)
      | r2_hidden(sK3(sK1),X6) ) ),
    inference(resolution,[],[f347,f166])).

fof(f347,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(sK1,X1)
      | r2_hidden(sK3(sK1),X2)
      | ~ r1_tarski(X1,X2) ) ),
    inference(resolution,[],[f157,f95])).

fof(f157,plain,(
    ! [X0] :
      ( r2_hidden(sK3(sK1),X0)
      | ~ r1_tarski(sK1,X0) ) ),
    inference(resolution,[],[f153,f95])).

fof(f924,plain,
    ( r2_hidden(sK3(sK1),u1_struct_0(sK0))
    | r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0)) ),
    inference(resolution,[],[f733,f96])).

fof(f733,plain,(
    ! [X2] :
      ( ~ r2_hidden(sK4(u1_struct_0(sK0),X2),X2)
      | r2_hidden(sK3(sK1),X2) ) ),
    inference(resolution,[],[f730,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK4(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f61])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:52:29 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.54  % (31679)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.54  % (31683)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.54  % (31675)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.55  % (31687)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.55  % (31671)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.56  % (31672)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.56  % (31665)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.57  % (31664)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.57  % (31666)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.57  % (31669)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.57  % (31662)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.58  % (31668)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.58  % (31662)Refutation not found, incomplete strategy% (31662)------------------------------
% 0.22/0.58  % (31662)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (31662)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.58  
% 0.22/0.58  % (31662)Memory used [KB]: 10746
% 0.22/0.58  % (31662)Time elapsed: 0.152 s
% 0.22/0.58  % (31662)------------------------------
% 0.22/0.58  % (31662)------------------------------
% 0.22/0.58  % (31660)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.59  % (31663)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.59  % (31682)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.59  % (31661)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.60  % (31690)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.60  % (31668)Refutation not found, incomplete strategy% (31668)------------------------------
% 0.22/0.60  % (31668)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.60  % (31668)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.60  
% 0.22/0.60  % (31668)Memory used [KB]: 10746
% 0.22/0.60  % (31668)Time elapsed: 0.154 s
% 0.22/0.60  % (31668)------------------------------
% 0.22/0.60  % (31668)------------------------------
% 0.22/0.60  % (31682)Refutation not found, incomplete strategy% (31682)------------------------------
% 0.22/0.60  % (31682)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.60  % (31681)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.60  % (31674)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.60  % (31680)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.60  % (31676)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.61  % (31673)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.61  % (31678)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.61  % (31688)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.61  % (31682)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.61  
% 0.22/0.61  % (31682)Memory used [KB]: 10746
% 0.22/0.61  % (31682)Time elapsed: 0.176 s
% 0.22/0.61  % (31682)------------------------------
% 0.22/0.61  % (31682)------------------------------
% 0.22/0.61  % (31685)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.61  % (31677)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.61  % (31684)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.61  % (31686)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.62  % (31670)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.62  % (31667)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.62  % (31670)Refutation not found, incomplete strategy% (31670)------------------------------
% 0.22/0.62  % (31670)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.62  % (31670)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.62  
% 0.22/0.62  % (31670)Memory used [KB]: 10618
% 0.22/0.62  % (31670)Time elapsed: 0.200 s
% 0.22/0.62  % (31670)------------------------------
% 0.22/0.62  % (31670)------------------------------
% 2.04/0.64  % (31683)Refutation found. Thanks to Tanya!
% 2.04/0.64  % SZS status Theorem for theBenchmark
% 2.04/0.64  % SZS output start Proof for theBenchmark
% 2.04/0.64  fof(f1300,plain,(
% 2.04/0.64    $false),
% 2.04/0.64    inference(subsumption_resolution,[],[f1239,f452])).
% 2.04/0.64  fof(f452,plain,(
% 2.04/0.64    ~v2_tex_2(sK1,sK0)),
% 2.04/0.64    inference(subsumption_resolution,[],[f451,f71])).
% 2.04/0.64  fof(f71,plain,(
% 2.04/0.64    ~v2_tex_2(sK1,sK0) | ~v1_zfmisc_1(sK1)),
% 2.04/0.64    inference(cnf_transformation,[],[f51])).
% 2.04/0.64  fof(f51,plain,(
% 2.04/0.64    ((~v1_zfmisc_1(sK1) | ~v2_tex_2(sK1,sK0)) & (v1_zfmisc_1(sK1) | v2_tex_2(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(sK1)) & l1_pre_topc(sK0) & v2_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 2.04/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f48,f50,f49])).
% 2.04/0.64  fof(f49,plain,(
% 2.04/0.64    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,sK0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK0) & v2_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 2.04/0.64    introduced(choice_axiom,[])).
% 2.04/0.64  fof(f50,plain,(
% 2.04/0.64    ? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,sK0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(X1)) => ((~v1_zfmisc_1(sK1) | ~v2_tex_2(sK1,sK0)) & (v1_zfmisc_1(sK1) | v2_tex_2(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(sK1))),
% 2.04/0.64    introduced(choice_axiom,[])).
% 2.04/0.64  fof(f48,plain,(
% 2.04/0.64    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.04/0.64    inference(flattening,[],[f47])).
% 2.04/0.64  fof(f47,plain,(
% 2.04/0.64    ? [X0] : (? [X1] : (((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.04/0.64    inference(nnf_transformation,[],[f24])).
% 2.04/0.64  fof(f24,plain,(
% 2.04/0.64    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.04/0.64    inference(flattening,[],[f23])).
% 2.04/0.64  fof(f23,plain,(
% 2.04/0.64    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.04/0.64    inference(ennf_transformation,[],[f22])).
% 2.04/0.64  fof(f22,negated_conjecture,(
% 2.04/0.64    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 2.04/0.64    inference(negated_conjecture,[],[f21])).
% 2.04/0.64  fof(f21,conjecture,(
% 2.04/0.64    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 2.04/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tex_2)).
% 2.04/0.64  fof(f451,plain,(
% 2.04/0.64    v1_zfmisc_1(sK1) | ~v2_tex_2(sK1,sK0)),
% 2.04/0.64    inference(subsumption_resolution,[],[f450,f64])).
% 2.04/0.64  fof(f64,plain,(
% 2.04/0.64    ~v2_struct_0(sK0)),
% 2.04/0.64    inference(cnf_transformation,[],[f51])).
% 2.04/0.64  fof(f450,plain,(
% 2.04/0.64    v1_zfmisc_1(sK1) | ~v2_tex_2(sK1,sK0) | v2_struct_0(sK0)),
% 2.04/0.64    inference(subsumption_resolution,[],[f449,f65])).
% 2.04/0.64  fof(f65,plain,(
% 2.04/0.64    v2_pre_topc(sK0)),
% 2.04/0.64    inference(cnf_transformation,[],[f51])).
% 2.04/0.64  fof(f449,plain,(
% 2.04/0.64    v1_zfmisc_1(sK1) | ~v2_tex_2(sK1,sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 2.04/0.64    inference(subsumption_resolution,[],[f448,f67])).
% 2.04/0.64  fof(f67,plain,(
% 2.04/0.64    l1_pre_topc(sK0)),
% 2.04/0.64    inference(cnf_transformation,[],[f51])).
% 2.04/0.64  fof(f448,plain,(
% 2.04/0.64    v1_zfmisc_1(sK1) | ~v2_tex_2(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 2.04/0.64    inference(subsumption_resolution,[],[f447,f68])).
% 2.04/0.64  fof(f68,plain,(
% 2.04/0.64    ~v1_xboole_0(sK1)),
% 2.04/0.64    inference(cnf_transformation,[],[f51])).
% 2.04/0.64  fof(f447,plain,(
% 2.04/0.64    v1_zfmisc_1(sK1) | ~v2_tex_2(sK1,sK0) | v1_xboole_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 2.04/0.64    inference(subsumption_resolution,[],[f446,f69])).
% 2.04/0.64  fof(f69,plain,(
% 2.04/0.64    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.04/0.64    inference(cnf_transformation,[],[f51])).
% 2.04/0.64  fof(f446,plain,(
% 2.04/0.64    v1_zfmisc_1(sK1) | ~v2_tex_2(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 2.04/0.64    inference(duplicate_literal_removal,[],[f445])).
% 2.04/0.64  fof(f445,plain,(
% 2.04/0.64    v1_zfmisc_1(sK1) | v1_zfmisc_1(sK1) | ~v2_tex_2(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 2.04/0.64    inference(superposition,[],[f337,f88])).
% 2.04/0.64  fof(f88,plain,(
% 2.04/0.64    ( ! [X0,X1] : (u1_struct_0(sK2(X0,X1)) = X1 | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.04/0.64    inference(cnf_transformation,[],[f53])).
% 2.04/0.64  fof(f53,plain,(
% 2.04/0.64    ! [X0] : (! [X1] : ((u1_struct_0(sK2(X0,X1)) = X1 & m1_pre_topc(sK2(X0,X1),X0) & v1_tdlat_3(sK2(X0,X1)) & v1_pre_topc(sK2(X0,X1)) & ~v2_struct_0(sK2(X0,X1))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.04/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f39,f52])).
% 2.04/0.64  fof(f52,plain,(
% 2.04/0.64    ! [X1,X0] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => (u1_struct_0(sK2(X0,X1)) = X1 & m1_pre_topc(sK2(X0,X1),X0) & v1_tdlat_3(sK2(X0,X1)) & v1_pre_topc(sK2(X0,X1)) & ~v2_struct_0(sK2(X0,X1))))),
% 2.04/0.64    introduced(choice_axiom,[])).
% 2.04/0.64  fof(f39,plain,(
% 2.04/0.64    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & v1_pre_topc(X2) & ~v2_struct_0(X2)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.04/0.64    inference(flattening,[],[f38])).
% 2.04/0.64  fof(f38,plain,(
% 2.04/0.64    ! [X0] : (! [X1] : ((? [X2] : (u1_struct_0(X2) = X1 & (m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & v1_pre_topc(X2) & ~v2_struct_0(X2))) | ~v2_tex_2(X1,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.04/0.64    inference(ennf_transformation,[],[f19])).
% 2.04/0.64  fof(f19,axiom,(
% 2.04/0.64    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => u1_struct_0(X2) != X1) & v2_tex_2(X1,X0))))),
% 2.04/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_tex_2)).
% 2.04/0.64  fof(f337,plain,(
% 2.04/0.64    v1_zfmisc_1(u1_struct_0(sK2(sK0,sK1))) | v1_zfmisc_1(sK1)),
% 2.04/0.64    inference(subsumption_resolution,[],[f336,f319])).
% 2.04/0.64  fof(f319,plain,(
% 2.04/0.64    v7_struct_0(sK2(sK0,sK1)) | v1_zfmisc_1(sK1)),
% 2.04/0.64    inference(subsumption_resolution,[],[f318,f208])).
% 2.04/0.64  fof(f208,plain,(
% 2.04/0.64    ~v2_struct_0(sK2(sK0,sK1)) | v1_zfmisc_1(sK1)),
% 2.04/0.64    inference(subsumption_resolution,[],[f207,f64])).
% 2.04/0.64  fof(f207,plain,(
% 2.04/0.64    v1_zfmisc_1(sK1) | ~v2_struct_0(sK2(sK0,sK1)) | v2_struct_0(sK0)),
% 2.04/0.64    inference(subsumption_resolution,[],[f206,f65])).
% 2.04/0.64  fof(f206,plain,(
% 2.04/0.64    v1_zfmisc_1(sK1) | ~v2_struct_0(sK2(sK0,sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 2.04/0.64    inference(subsumption_resolution,[],[f205,f67])).
% 2.04/0.64  fof(f205,plain,(
% 2.04/0.64    v1_zfmisc_1(sK1) | ~v2_struct_0(sK2(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 2.04/0.64    inference(subsumption_resolution,[],[f204,f68])).
% 2.04/0.64  fof(f204,plain,(
% 2.04/0.64    v1_zfmisc_1(sK1) | ~v2_struct_0(sK2(sK0,sK1)) | v1_xboole_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 2.04/0.64    inference(subsumption_resolution,[],[f200,f69])).
% 2.04/0.64  fof(f200,plain,(
% 2.04/0.64    v1_zfmisc_1(sK1) | ~v2_struct_0(sK2(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 2.04/0.64    inference(resolution,[],[f70,f84])).
% 2.04/0.64  fof(f84,plain,(
% 2.04/0.64    ( ! [X0,X1] : (~v2_struct_0(sK2(X0,X1)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.04/0.64    inference(cnf_transformation,[],[f53])).
% 2.04/0.64  fof(f70,plain,(
% 2.04/0.64    v2_tex_2(sK1,sK0) | v1_zfmisc_1(sK1)),
% 2.04/0.64    inference(cnf_transformation,[],[f51])).
% 2.04/0.64  fof(f318,plain,(
% 2.04/0.64    v1_zfmisc_1(sK1) | v7_struct_0(sK2(sK0,sK1)) | v2_struct_0(sK2(sK0,sK1))),
% 2.04/0.64    inference(subsumption_resolution,[],[f317,f315])).
% 2.04/0.64  fof(f315,plain,(
% 2.04/0.64    v2_pre_topc(sK2(sK0,sK1)) | v1_zfmisc_1(sK1)),
% 2.04/0.64    inference(subsumption_resolution,[],[f306,f302])).
% 2.04/0.64  fof(f302,plain,(
% 2.04/0.64    v2_tdlat_3(sK2(sK0,sK1)) | v1_zfmisc_1(sK1)),
% 2.04/0.64    inference(resolution,[],[f218,f115])).
% 2.04/0.64  fof(f115,plain,(
% 2.04/0.64    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v2_tdlat_3(X0)) )),
% 2.04/0.64    inference(subsumption_resolution,[],[f114,f65])).
% 2.04/0.64  fof(f114,plain,(
% 2.04/0.64    ( ! [X0] : (v2_tdlat_3(X0) | ~m1_pre_topc(X0,sK0) | ~v2_pre_topc(sK0)) )),
% 2.04/0.64    inference(subsumption_resolution,[],[f113,f66])).
% 2.04/0.64  fof(f66,plain,(
% 2.04/0.64    v2_tdlat_3(sK0)),
% 2.04/0.64    inference(cnf_transformation,[],[f51])).
% 2.04/0.64  fof(f113,plain,(
% 2.04/0.64    ( ! [X0] : (v2_tdlat_3(X0) | ~m1_pre_topc(X0,sK0) | ~v2_tdlat_3(sK0) | ~v2_pre_topc(sK0)) )),
% 2.04/0.64    inference(subsumption_resolution,[],[f104,f67])).
% 2.04/0.64  fof(f104,plain,(
% 2.04/0.64    ( ! [X0] : (v2_tdlat_3(X0) | ~m1_pre_topc(X0,sK0) | ~l1_pre_topc(sK0) | ~v2_tdlat_3(sK0) | ~v2_pre_topc(sK0)) )),
% 2.04/0.64    inference(resolution,[],[f64,f82])).
% 2.04/0.64  fof(f82,plain,(
% 2.04/0.64    ( ! [X0,X1] : (v2_tdlat_3(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.04/0.64    inference(cnf_transformation,[],[f35])).
% 2.04/0.64  fof(f35,plain,(
% 2.04/0.64    ! [X0] : (! [X1] : (v2_tdlat_3(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.04/0.64    inference(flattening,[],[f34])).
% 2.04/0.64  fof(f34,plain,(
% 2.04/0.64    ! [X0] : (! [X1] : (v2_tdlat_3(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.04/0.64    inference(ennf_transformation,[],[f17])).
% 2.04/0.64  fof(f17,axiom,(
% 2.04/0.64    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_tdlat_3(X1)))),
% 2.04/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc6_tdlat_3)).
% 2.04/0.64  fof(f218,plain,(
% 2.04/0.64    m1_pre_topc(sK2(sK0,sK1),sK0) | v1_zfmisc_1(sK1)),
% 2.04/0.64    inference(subsumption_resolution,[],[f217,f64])).
% 2.04/0.64  fof(f217,plain,(
% 2.04/0.64    v1_zfmisc_1(sK1) | m1_pre_topc(sK2(sK0,sK1),sK0) | v2_struct_0(sK0)),
% 2.04/0.64    inference(subsumption_resolution,[],[f216,f65])).
% 2.04/0.64  fof(f216,plain,(
% 2.04/0.64    v1_zfmisc_1(sK1) | m1_pre_topc(sK2(sK0,sK1),sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 2.04/0.64    inference(subsumption_resolution,[],[f215,f67])).
% 2.04/0.64  fof(f215,plain,(
% 2.04/0.64    v1_zfmisc_1(sK1) | m1_pre_topc(sK2(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 2.04/0.64    inference(subsumption_resolution,[],[f214,f68])).
% 2.04/0.64  fof(f214,plain,(
% 2.04/0.64    v1_zfmisc_1(sK1) | m1_pre_topc(sK2(sK0,sK1),sK0) | v1_xboole_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 2.04/0.64    inference(subsumption_resolution,[],[f202,f69])).
% 2.04/0.64  fof(f202,plain,(
% 2.04/0.64    v1_zfmisc_1(sK1) | m1_pre_topc(sK2(sK0,sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 2.04/0.64    inference(resolution,[],[f70,f87])).
% 2.04/0.64  fof(f87,plain,(
% 2.04/0.64    ( ! [X0,X1] : (m1_pre_topc(sK2(X0,X1),X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.04/0.64    inference(cnf_transformation,[],[f53])).
% 2.04/0.64  fof(f306,plain,(
% 2.04/0.64    v1_zfmisc_1(sK1) | v2_pre_topc(sK2(sK0,sK1)) | ~v2_tdlat_3(sK2(sK0,sK1))),
% 2.04/0.64    inference(resolution,[],[f301,f76])).
% 2.04/0.64  fof(f76,plain,(
% 2.04/0.64    ( ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 2.04/0.64    inference(cnf_transformation,[],[f29])).
% 2.04/0.64  fof(f29,plain,(
% 2.04/0.64    ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 2.04/0.64    inference(flattening,[],[f28])).
% 2.04/0.64  fof(f28,plain,(
% 2.04/0.64    ! [X0] : ((v2_pre_topc(X0) | ~v2_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 2.04/0.64    inference(ennf_transformation,[],[f15])).
% 2.04/0.64  fof(f15,axiom,(
% 2.04/0.64    ! [X0] : (l1_pre_topc(X0) => (v2_tdlat_3(X0) => v2_pre_topc(X0)))),
% 2.04/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tdlat_3)).
% 2.04/0.64  fof(f301,plain,(
% 2.04/0.64    l1_pre_topc(sK2(sK0,sK1)) | v1_zfmisc_1(sK1)),
% 2.04/0.64    inference(resolution,[],[f218,f139])).
% 2.04/0.64  fof(f139,plain,(
% 2.04/0.64    ( ! [X0] : (~m1_pre_topc(X0,sK0) | l1_pre_topc(X0)) )),
% 2.04/0.64    inference(resolution,[],[f67,f80])).
% 2.04/0.64  fof(f80,plain,(
% 2.04/0.64    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.04/0.64    inference(cnf_transformation,[],[f32])).
% 2.04/0.64  fof(f32,plain,(
% 2.04/0.64    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.04/0.64    inference(ennf_transformation,[],[f12])).
% 2.04/0.64  fof(f12,axiom,(
% 2.04/0.64    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.04/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 2.04/0.64  fof(f317,plain,(
% 2.04/0.64    v1_zfmisc_1(sK1) | v7_struct_0(sK2(sK0,sK1)) | ~v2_pre_topc(sK2(sK0,sK1)) | v2_struct_0(sK2(sK0,sK1))),
% 2.04/0.64    inference(subsumption_resolution,[],[f316,f213])).
% 2.04/0.64  fof(f213,plain,(
% 2.04/0.64    v1_tdlat_3(sK2(sK0,sK1)) | v1_zfmisc_1(sK1)),
% 2.04/0.64    inference(subsumption_resolution,[],[f212,f64])).
% 2.04/0.64  fof(f212,plain,(
% 2.04/0.64    v1_zfmisc_1(sK1) | v1_tdlat_3(sK2(sK0,sK1)) | v2_struct_0(sK0)),
% 2.04/0.64    inference(subsumption_resolution,[],[f211,f65])).
% 2.04/0.64  fof(f211,plain,(
% 2.04/0.64    v1_zfmisc_1(sK1) | v1_tdlat_3(sK2(sK0,sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 2.04/0.64    inference(subsumption_resolution,[],[f210,f67])).
% 2.04/0.64  fof(f210,plain,(
% 2.04/0.64    v1_zfmisc_1(sK1) | v1_tdlat_3(sK2(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 2.04/0.64    inference(subsumption_resolution,[],[f209,f68])).
% 2.04/0.64  fof(f209,plain,(
% 2.04/0.64    v1_zfmisc_1(sK1) | v1_tdlat_3(sK2(sK0,sK1)) | v1_xboole_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 2.04/0.64    inference(subsumption_resolution,[],[f201,f69])).
% 2.04/0.64  fof(f201,plain,(
% 2.04/0.64    v1_zfmisc_1(sK1) | v1_tdlat_3(sK2(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 2.04/0.64    inference(resolution,[],[f70,f86])).
% 2.04/0.64  fof(f86,plain,(
% 2.04/0.64    ( ! [X0,X1] : (v1_tdlat_3(sK2(X0,X1)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.04/0.64    inference(cnf_transformation,[],[f53])).
% 2.04/0.64  fof(f316,plain,(
% 2.04/0.64    v1_zfmisc_1(sK1) | v7_struct_0(sK2(sK0,sK1)) | ~v1_tdlat_3(sK2(sK0,sK1)) | ~v2_pre_topc(sK2(sK0,sK1)) | v2_struct_0(sK2(sK0,sK1))),
% 2.04/0.64    inference(subsumption_resolution,[],[f307,f302])).
% 2.04/0.64  fof(f307,plain,(
% 2.04/0.64    v1_zfmisc_1(sK1) | v7_struct_0(sK2(sK0,sK1)) | ~v2_tdlat_3(sK2(sK0,sK1)) | ~v1_tdlat_3(sK2(sK0,sK1)) | ~v2_pre_topc(sK2(sK0,sK1)) | v2_struct_0(sK2(sK0,sK1))),
% 2.04/0.64    inference(resolution,[],[f301,f78])).
% 2.04/0.64  fof(f78,plain,(
% 2.04/0.64    ( ! [X0] : (v7_struct_0(X0) | ~v2_tdlat_3(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.04/0.64    inference(cnf_transformation,[],[f31])).
% 2.04/0.64  fof(f31,plain,(
% 2.04/0.64    ! [X0] : ((v2_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0)) | ~v2_tdlat_3(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.04/0.64    inference(flattening,[],[f30])).
% 2.04/0.64  fof(f30,plain,(
% 2.04/0.64    ! [X0] : (((v2_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0)) | (~v2_tdlat_3(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.04/0.64    inference(ennf_transformation,[],[f16])).
% 2.04/0.65  fof(f16,axiom,(
% 2.04/0.65    ! [X0] : (l1_pre_topc(X0) => ((v2_tdlat_3(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v2_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0))))),
% 2.04/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_1)).
% 2.04/0.65  fof(f336,plain,(
% 2.04/0.65    v1_zfmisc_1(sK1) | v1_zfmisc_1(u1_struct_0(sK2(sK0,sK1))) | ~v7_struct_0(sK2(sK0,sK1))),
% 2.04/0.65    inference(resolution,[],[f305,f89])).
% 2.04/0.65  fof(f89,plain,(
% 2.04/0.65    ( ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0)) )),
% 2.04/0.65    inference(cnf_transformation,[],[f41])).
% 2.04/0.65  fof(f41,plain,(
% 2.04/0.65    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0))),
% 2.04/0.65    inference(flattening,[],[f40])).
% 2.04/0.65  fof(f40,plain,(
% 2.04/0.65    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v7_struct_0(X0)))),
% 2.04/0.65    inference(ennf_transformation,[],[f13])).
% 2.04/0.65  fof(f13,axiom,(
% 2.04/0.65    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0)) => v1_zfmisc_1(u1_struct_0(X0)))),
% 2.04/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).
% 2.04/0.65  fof(f305,plain,(
% 2.04/0.65    l1_struct_0(sK2(sK0,sK1)) | v1_zfmisc_1(sK1)),
% 2.04/0.65    inference(resolution,[],[f301,f75])).
% 2.04/0.65  fof(f75,plain,(
% 2.04/0.65    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.04/0.65    inference(cnf_transformation,[],[f27])).
% 2.04/0.65  fof(f27,plain,(
% 2.04/0.65    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.04/0.65    inference(ennf_transformation,[],[f11])).
% 2.04/0.65  fof(f11,axiom,(
% 2.04/0.65    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.04/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 2.04/0.65  fof(f1239,plain,(
% 2.04/0.65    v2_tex_2(sK1,sK0)),
% 2.04/0.65    inference(backward_demodulation,[],[f939,f1206])).
% 2.04/0.65  fof(f1206,plain,(
% 2.04/0.65    sK1 = k1_tarski(sK3(sK1))),
% 2.04/0.65    inference(duplicate_literal_removal,[],[f1196])).
% 2.04/0.65  fof(f1196,plain,(
% 2.04/0.65    sK1 = k1_tarski(sK3(sK1)) | sK1 = k1_tarski(sK3(sK1))),
% 2.04/0.65    inference(resolution,[],[f1182,f682])).
% 2.04/0.65  fof(f682,plain,(
% 2.04/0.65    ( ! [X2] : (~r2_hidden(X2,k1_tarski(sK3(sK1))) | sK1 = k1_tarski(sK3(sK1))) )),
% 2.04/0.65    inference(resolution,[],[f517,f90])).
% 2.04/0.65  fof(f90,plain,(
% 2.04/0.65    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 2.04/0.65    inference(cnf_transformation,[],[f57])).
% 2.04/0.65  fof(f57,plain,(
% 2.04/0.65    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.04/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f55,f56])).
% 2.04/0.65  fof(f56,plain,(
% 2.04/0.65    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 2.04/0.65    introduced(choice_axiom,[])).
% 2.04/0.65  fof(f55,plain,(
% 2.04/0.65    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.04/0.65    inference(rectify,[],[f54])).
% 2.04/0.65  fof(f54,plain,(
% 2.04/0.65    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.04/0.65    inference(nnf_transformation,[],[f1])).
% 2.04/0.65  fof(f1,axiom,(
% 2.04/0.65    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.04/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 2.04/0.65  fof(f517,plain,(
% 2.04/0.65    v1_xboole_0(k1_tarski(sK3(sK1))) | sK1 = k1_tarski(sK3(sK1))),
% 2.04/0.65    inference(resolution,[],[f455,f156])).
% 2.04/0.65  fof(f156,plain,(
% 2.04/0.65    r1_tarski(k1_tarski(sK3(sK1)),sK1)),
% 2.04/0.65    inference(resolution,[],[f153,f99])).
% 2.04/0.65  fof(f99,plain,(
% 2.04/0.65    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 2.04/0.65    inference(cnf_transformation,[],[f62])).
% 2.04/0.65  fof(f62,plain,(
% 2.04/0.65    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 2.04/0.65    inference(nnf_transformation,[],[f6])).
% 2.04/0.65  fof(f6,axiom,(
% 2.04/0.65    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 2.04/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 2.04/0.65  fof(f153,plain,(
% 2.04/0.65    r2_hidden(sK3(sK1),sK1)),
% 2.04/0.65    inference(resolution,[],[f68,f91])).
% 2.04/0.65  fof(f91,plain,(
% 2.04/0.65    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) )),
% 2.04/0.65    inference(cnf_transformation,[],[f57])).
% 2.04/0.65  fof(f455,plain,(
% 2.04/0.65    ( ! [X0] : (~r1_tarski(X0,sK1) | sK1 = X0 | v1_xboole_0(X0)) )),
% 2.04/0.65    inference(subsumption_resolution,[],[f454,f68])).
% 2.04/0.65  fof(f454,plain,(
% 2.04/0.65    ( ! [X0] : (sK1 = X0 | ~r1_tarski(X0,sK1) | v1_xboole_0(sK1) | v1_xboole_0(X0)) )),
% 2.04/0.65    inference(resolution,[],[f453,f74])).
% 2.04/0.65  fof(f74,plain,(
% 2.04/0.65    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.04/0.65    inference(cnf_transformation,[],[f26])).
% 2.04/0.65  fof(f26,plain,(
% 2.04/0.65    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.04/0.65    inference(flattening,[],[f25])).
% 2.04/0.65  fof(f25,plain,(
% 2.04/0.65    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 2.04/0.65    inference(ennf_transformation,[],[f18])).
% 2.04/0.65  fof(f18,axiom,(
% 2.04/0.65    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 2.04/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).
% 2.04/0.65  fof(f453,plain,(
% 2.04/0.65    v1_zfmisc_1(sK1)),
% 2.04/0.65    inference(resolution,[],[f452,f70])).
% 2.04/0.65  fof(f1182,plain,(
% 2.04/0.65    ( ! [X0] : (r2_hidden(sK3(sK1),X0) | sK1 = k1_tarski(sK3(sK1))) )),
% 2.04/0.65    inference(resolution,[],[f1127,f98])).
% 2.04/0.65  fof(f98,plain,(
% 2.04/0.65    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)) )),
% 2.04/0.65    inference(cnf_transformation,[],[f62])).
% 2.04/0.65  fof(f1127,plain,(
% 2.04/0.65    ( ! [X0] : (r1_tarski(k1_tarski(sK3(sK1)),X0) | sK1 = k1_tarski(sK3(sK1))) )),
% 2.04/0.65    inference(resolution,[],[f682,f96])).
% 2.04/0.65  fof(f96,plain,(
% 2.04/0.65    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK4(X0,X1),X0)) )),
% 2.04/0.65    inference(cnf_transformation,[],[f61])).
% 2.04/0.65  fof(f61,plain,(
% 2.04/0.65    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.04/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f59,f60])).
% 2.04/0.65  fof(f60,plain,(
% 2.04/0.65    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 2.04/0.65    introduced(choice_axiom,[])).
% 2.04/0.65  fof(f59,plain,(
% 2.04/0.65    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.04/0.65    inference(rectify,[],[f58])).
% 2.04/0.65  fof(f58,plain,(
% 2.04/0.65    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.04/0.65    inference(nnf_transformation,[],[f45])).
% 2.04/0.65  fof(f45,plain,(
% 2.04/0.65    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.04/0.65    inference(ennf_transformation,[],[f2])).
% 2.04/0.65  fof(f2,axiom,(
% 2.04/0.65    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.04/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 2.04/0.65  fof(f939,plain,(
% 2.04/0.65    v2_tex_2(k1_tarski(sK3(sK1)),sK0)),
% 2.04/0.65    inference(forward_demodulation,[],[f938,f867])).
% 2.04/0.65  fof(f867,plain,(
% 2.04/0.65    k1_tarski(sK3(sK1)) = k6_domain_1(u1_struct_0(sK0),sK3(sK1))),
% 2.04/0.65    inference(resolution,[],[f433,f153])).
% 2.04/0.65  fof(f433,plain,(
% 2.04/0.65    ( ! [X1] : (~r2_hidden(X1,sK1) | k1_tarski(X1) = k6_domain_1(u1_struct_0(sK0),X1)) )),
% 2.04/0.65    inference(subsumption_resolution,[],[f429,f185])).
% 2.04/0.65  fof(f185,plain,(
% 2.04/0.65    ~v1_xboole_0(u1_struct_0(sK0))),
% 2.04/0.65    inference(subsumption_resolution,[],[f167,f68])).
% 2.04/0.65  fof(f167,plain,(
% 2.04/0.65    v1_xboole_0(sK1) | ~v1_xboole_0(u1_struct_0(sK0))),
% 2.04/0.65    inference(resolution,[],[f69,f81])).
% 2.04/0.65  fof(f81,plain,(
% 2.04/0.65    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 2.04/0.65    inference(cnf_transformation,[],[f33])).
% 2.04/0.65  fof(f33,plain,(
% 2.04/0.65    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 2.04/0.65    inference(ennf_transformation,[],[f8])).
% 2.04/0.65  fof(f8,axiom,(
% 2.04/0.65    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 2.04/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).
% 2.04/0.65  fof(f429,plain,(
% 2.04/0.65    ( ! [X1] : (~r2_hidden(X1,sK1) | k1_tarski(X1) = k6_domain_1(u1_struct_0(sK0),X1) | v1_xboole_0(u1_struct_0(sK0))) )),
% 2.04/0.65    inference(resolution,[],[f357,f94])).
% 2.04/0.65  fof(f94,plain,(
% 2.04/0.65    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.04/0.65    inference(cnf_transformation,[],[f44])).
% 2.04/0.65  fof(f44,plain,(
% 2.04/0.65    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 2.04/0.65    inference(flattening,[],[f43])).
% 2.04/0.65  fof(f43,plain,(
% 2.04/0.65    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 2.04/0.65    inference(ennf_transformation,[],[f14])).
% 2.04/0.65  fof(f14,axiom,(
% 2.04/0.65    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 2.04/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 2.04/0.65  fof(f357,plain,(
% 2.04/0.65    ( ! [X3] : (m1_subset_1(X3,u1_struct_0(sK0)) | ~r2_hidden(X3,sK1)) )),
% 2.04/0.65    inference(resolution,[],[f196,f93])).
% 2.04/0.65  fof(f93,plain,(
% 2.04/0.65    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 2.04/0.65    inference(cnf_transformation,[],[f42])).
% 2.04/0.65  fof(f42,plain,(
% 2.04/0.65    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 2.04/0.65    inference(ennf_transformation,[],[f9])).
% 2.04/0.65  fof(f9,axiom,(
% 2.04/0.65    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 2.04/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 2.04/0.65  fof(f196,plain,(
% 2.04/0.65    ( ! [X0] : (r2_hidden(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,sK1)) )),
% 2.04/0.65    inference(resolution,[],[f166,f95])).
% 2.04/0.65  fof(f95,plain,(
% 2.04/0.65    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 2.04/0.65    inference(cnf_transformation,[],[f61])).
% 2.04/0.65  fof(f166,plain,(
% 2.04/0.65    r1_tarski(sK1,u1_struct_0(sK0))),
% 2.04/0.65    inference(resolution,[],[f69,f100])).
% 2.04/0.65  fof(f100,plain,(
% 2.04/0.65    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.04/0.65    inference(cnf_transformation,[],[f63])).
% 2.04/0.65  fof(f63,plain,(
% 2.04/0.65    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.04/0.65    inference(nnf_transformation,[],[f10])).
% 2.04/0.65  fof(f10,axiom,(
% 2.04/0.65    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.04/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 2.04/0.65  fof(f938,plain,(
% 2.04/0.65    v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK3(sK1)),sK0)),
% 2.04/0.65    inference(subsumption_resolution,[],[f937,f64])).
% 2.04/0.65  fof(f937,plain,(
% 2.04/0.65    v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK3(sK1)),sK0) | v2_struct_0(sK0)),
% 2.04/0.65    inference(subsumption_resolution,[],[f936,f65])).
% 2.04/0.65  fof(f936,plain,(
% 2.04/0.65    v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK3(sK1)),sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 2.04/0.65    inference(subsumption_resolution,[],[f934,f67])).
% 2.04/0.65  fof(f934,plain,(
% 2.04/0.65    v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK3(sK1)),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 2.04/0.65    inference(resolution,[],[f932,f83])).
% 2.04/0.65  fof(f83,plain,(
% 2.04/0.65    ( ! [X0,X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.04/0.65    inference(cnf_transformation,[],[f37])).
% 2.04/0.65  fof(f37,plain,(
% 2.04/0.65    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.04/0.65    inference(flattening,[],[f36])).
% 2.04/0.65  fof(f36,plain,(
% 2.04/0.65    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.04/0.65    inference(ennf_transformation,[],[f20])).
% 2.04/0.65  fof(f20,axiom,(
% 2.04/0.65    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)))),
% 2.04/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).
% 2.04/0.65  fof(f932,plain,(
% 2.04/0.65    m1_subset_1(sK3(sK1),u1_struct_0(sK0))),
% 2.04/0.65    inference(resolution,[],[f929,f93])).
% 2.04/0.65  fof(f929,plain,(
% 2.04/0.65    r2_hidden(sK3(sK1),u1_struct_0(sK0))),
% 2.04/0.65    inference(subsumption_resolution,[],[f924,f730])).
% 2.04/0.65  fof(f730,plain,(
% 2.04/0.65    ( ! [X6] : (~r1_tarski(u1_struct_0(sK0),X6) | r2_hidden(sK3(sK1),X6)) )),
% 2.04/0.65    inference(resolution,[],[f347,f166])).
% 2.04/0.65  fof(f347,plain,(
% 2.04/0.65    ( ! [X2,X1] : (~r1_tarski(sK1,X1) | r2_hidden(sK3(sK1),X2) | ~r1_tarski(X1,X2)) )),
% 2.04/0.65    inference(resolution,[],[f157,f95])).
% 2.04/0.65  fof(f157,plain,(
% 2.04/0.65    ( ! [X0] : (r2_hidden(sK3(sK1),X0) | ~r1_tarski(sK1,X0)) )),
% 2.04/0.65    inference(resolution,[],[f153,f95])).
% 2.04/0.65  fof(f924,plain,(
% 2.04/0.65    r2_hidden(sK3(sK1),u1_struct_0(sK0)) | r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0))),
% 2.04/0.65    inference(resolution,[],[f733,f96])).
% 2.04/0.65  fof(f733,plain,(
% 2.04/0.65    ( ! [X2] : (~r2_hidden(sK4(u1_struct_0(sK0),X2),X2) | r2_hidden(sK3(sK1),X2)) )),
% 2.04/0.65    inference(resolution,[],[f730,f97])).
% 2.04/0.65  fof(f97,plain,(
% 2.04/0.65    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK4(X0,X1),X1)) )),
% 2.04/0.65    inference(cnf_transformation,[],[f61])).
% 2.04/0.65  % SZS output end Proof for theBenchmark
% 2.04/0.65  % (31683)------------------------------
% 2.04/0.65  % (31683)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.04/0.65  % (31683)Termination reason: Refutation
% 2.04/0.65  
% 2.04/0.65  % (31683)Memory used [KB]: 2302
% 2.04/0.65  % (31683)Time elapsed: 0.164 s
% 2.04/0.65  % (31683)------------------------------
% 2.04/0.65  % (31683)------------------------------
% 2.24/0.65  % (31659)Success in time 0.289 s
%------------------------------------------------------------------------------
