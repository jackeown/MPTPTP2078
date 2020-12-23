%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1970+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:58 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  282 (7147 expanded)
%              Number of leaves         :   20 (2580 expanded)
%              Depth                    :   62
%              Number of atoms          : 1690 (132852 expanded)
%              Number of equality atoms :  159 (7218 expanded)
%              Maximal formula depth    :   20 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f926,plain,(
    $false ),
    inference(subsumption_resolution,[],[f925,f528])).

fof(f528,plain,(
    v2_waybel_0(sK2,sK1) ),
    inference(subsumption_resolution,[],[f527,f66])).

fof(f66,plain,(
    v2_waybel_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v2_waybel_7(sK2,sK1)
      | ~ v13_waybel_0(sK2,sK1)
      | ~ v2_waybel_0(sK2,sK1)
      | v1_xboole_0(sK2) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & v2_waybel_7(sK2,sK0)
    & v13_waybel_0(sK2,sK0)
    & v2_waybel_0(sK2,sK0)
    & ~ v1_xboole_0(sK2)
    & g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
    & l1_orders_2(sK1)
    & v2_lattice3(sK1)
    & v1_lattice3(sK1)
    & v5_orders_2(sK1)
    & v4_orders_2(sK1)
    & v3_orders_2(sK1)
    & l1_orders_2(sK0)
    & v2_lattice3(sK0)
    & v1_lattice3(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f40,f39,f38])).

fof(f38,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                  | ~ v2_waybel_7(X2,X1)
                  | ~ v13_waybel_0(X2,X1)
                  | ~ v2_waybel_0(X2,X1)
                  | v1_xboole_0(X2) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & v2_waybel_7(X2,X0)
                & v13_waybel_0(X2,X0)
                & v2_waybel_0(X2,X0)
                & ~ v1_xboole_0(X2) )
            & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
            & l1_orders_2(X1)
            & v2_lattice3(X1)
            & v1_lattice3(X1)
            & v5_orders_2(X1)
            & v4_orders_2(X1)
            & v3_orders_2(X1) )
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                | ~ v2_waybel_7(X2,X1)
                | ~ v13_waybel_0(X2,X1)
                | ~ v2_waybel_0(X2,X1)
                | v1_xboole_0(X2) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
              & v2_waybel_7(X2,sK0)
              & v13_waybel_0(X2,sK0)
              & v2_waybel_0(X2,sK0)
              & ~ v1_xboole_0(X2) )
          & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
          & l1_orders_2(X1)
          & v2_lattice3(X1)
          & v1_lattice3(X1)
          & v5_orders_2(X1)
          & v4_orders_2(X1)
          & v3_orders_2(X1) )
      & l1_orders_2(sK0)
      & v2_lattice3(sK0)
      & v1_lattice3(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
              | ~ v2_waybel_7(X2,X1)
              | ~ v13_waybel_0(X2,X1)
              | ~ v2_waybel_0(X2,X1)
              | v1_xboole_0(X2) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
            & v2_waybel_7(X2,sK0)
            & v13_waybel_0(X2,sK0)
            & v2_waybel_0(X2,sK0)
            & ~ v1_xboole_0(X2) )
        & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        & l1_orders_2(X1)
        & v2_lattice3(X1)
        & v1_lattice3(X1)
        & v5_orders_2(X1)
        & v4_orders_2(X1)
        & v3_orders_2(X1) )
   => ( ? [X2] :
          ( ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
            | ~ v2_waybel_7(X2,sK1)
            | ~ v13_waybel_0(X2,sK1)
            | ~ v2_waybel_0(X2,sK1)
            | v1_xboole_0(X2) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
          & v2_waybel_7(X2,sK0)
          & v13_waybel_0(X2,sK0)
          & v2_waybel_0(X2,sK0)
          & ~ v1_xboole_0(X2) )
      & g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
      & l1_orders_2(sK1)
      & v2_lattice3(sK1)
      & v1_lattice3(sK1)
      & v5_orders_2(sK1)
      & v4_orders_2(sK1)
      & v3_orders_2(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X2] :
        ( ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
          | ~ v2_waybel_7(X2,sK1)
          | ~ v13_waybel_0(X2,sK1)
          | ~ v2_waybel_0(X2,sK1)
          | v1_xboole_0(X2) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        & v2_waybel_7(X2,sK0)
        & v13_waybel_0(X2,sK0)
        & v2_waybel_0(X2,sK0)
        & ~ v1_xboole_0(X2) )
   => ( ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v2_waybel_7(sK2,sK1)
        | ~ v13_waybel_0(sK2,sK1)
        | ~ v2_waybel_0(sK2,sK1)
        | v1_xboole_0(sK2) )
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
      & v2_waybel_7(sK2,sK0)
      & v13_waybel_0(sK2,sK0)
      & v2_waybel_0(sK2,sK0)
      & ~ v1_xboole_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                | ~ v2_waybel_7(X2,X1)
                | ~ v13_waybel_0(X2,X1)
                | ~ v2_waybel_0(X2,X1)
                | v1_xboole_0(X2) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              & v2_waybel_7(X2,X0)
              & v13_waybel_0(X2,X0)
              & v2_waybel_0(X2,X0)
              & ~ v1_xboole_0(X2) )
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1)
          & v2_lattice3(X1)
          & v1_lattice3(X1)
          & v5_orders_2(X1)
          & v4_orders_2(X1)
          & v3_orders_2(X1) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                | ~ v2_waybel_7(X2,X1)
                | ~ v13_waybel_0(X2,X1)
                | ~ v2_waybel_0(X2,X1)
                | v1_xboole_0(X2) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              & v2_waybel_7(X2,X0)
              & v13_waybel_0(X2,X0)
              & v2_waybel_0(X2,X0)
              & ~ v1_xboole_0(X2) )
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1)
          & v2_lattice3(X1)
          & v1_lattice3(X1)
          & v5_orders_2(X1)
          & v4_orders_2(X1)
          & v3_orders_2(X1) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( ( l1_orders_2(X1)
              & v2_lattice3(X1)
              & v1_lattice3(X1)
              & v5_orders_2(X1)
              & v4_orders_2(X1)
              & v3_orders_2(X1) )
           => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
             => ! [X2] :
                  ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                    & v2_waybel_7(X2,X0)
                    & v13_waybel_0(X2,X0)
                    & v2_waybel_0(X2,X0)
                    & ~ v1_xboole_0(X2) )
                 => ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                    & v2_waybel_7(X2,X1)
                    & v13_waybel_0(X2,X1)
                    & v2_waybel_0(X2,X1)
                    & ~ v1_xboole_0(X2) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( ( l1_orders_2(X1)
            & v2_lattice3(X1)
            & v1_lattice3(X1)
            & v5_orders_2(X1)
            & v4_orders_2(X1)
            & v3_orders_2(X1) )
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  & v2_waybel_7(X2,X0)
                  & v13_waybel_0(X2,X0)
                  & v2_waybel_0(X2,X0)
                  & ~ v1_xboole_0(X2) )
               => ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                  & v2_waybel_7(X2,X1)
                  & v13_waybel_0(X2,X1)
                  & v2_waybel_0(X2,X1)
                  & ~ v1_xboole_0(X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_waybel_7)).

fof(f527,plain,
    ( ~ v2_waybel_0(sK2,sK0)
    | v2_waybel_0(sK2,sK1) ),
    inference(resolution,[],[f524,f69])).

fof(f69,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f41])).

fof(f524,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_waybel_0(X0,sK0)
      | v2_waybel_0(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f522,f57])).

% (6965)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
fof(f57,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f522,plain,(
    ! [X0] :
      ( ~ v2_waybel_0(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_waybel_0(X0,sK1)
      | ~ l1_orders_2(sK0) ) ),
    inference(duplicate_literal_removal,[],[f521])).

fof(f521,plain,(
    ! [X0] :
      ( ~ v2_waybel_0(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_waybel_0(X0,sK1)
      | ~ l1_orders_2(sK0) ) ),
    inference(equality_resolution,[],[f208])).

fof(f208,plain,(
    ! [X0,X1] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
      | ~ v2_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_waybel_0(X1,sK1)
      | ~ l1_orders_2(X0) ) ),
    inference(forward_demodulation,[],[f207,f163])).

fof(f163,plain,(
    g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK1)) ),
    inference(superposition,[],[f64,f153])).

fof(f153,plain,(
    u1_struct_0(sK0) = u1_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f152,f57])).

fof(f152,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK1)
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f131,f72])).

fof(f72,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(f131,plain,
    ( ~ m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | u1_struct_0(sK0) = u1_struct_0(sK1) ),
    inference(equality_resolution,[],[f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
      | u1_struct_0(sK1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(superposition,[],[f90,f64])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X0 = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2,X3] :
          ( g1_orders_2(X0,X1) = g1_orders_2(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_orders_2)).

fof(f64,plain,(
    g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) ),
    inference(cnf_transformation,[],[f41])).

fof(f207,plain,(
    ! [X0,X1] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK1))
      | ~ v2_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_waybel_0(X1,sK1)
      | ~ l1_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f199,f63])).

fof(f63,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f199,plain,(
    ! [X0,X1] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK1))
      | ~ v2_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_waybel_0(X1,sK1)
      | ~ l1_orders_2(sK1)
      | ~ l1_orders_2(X0) ) ),
    inference(superposition,[],[f95,f153])).

fof(f95,plain,(
    ! [X0,X3,X1] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ v2_waybel_0(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_waybel_0(X3,X1)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_waybel_0(X3,X1)
      | ~ v2_waybel_0(X2,X0)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v2_waybel_0(X3,X1)
                  | ~ v2_waybel_0(X2,X0)
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v2_waybel_0(X3,X1)
                  | ~ v2_waybel_0(X2,X0)
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( ( v2_waybel_0(X2,X0)
                        & X2 = X3 )
                     => v2_waybel_0(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_waybel_0)).

fof(f925,plain,(
    ~ v2_waybel_0(sK2,sK1) ),
    inference(subsumption_resolution,[],[f924,f435])).

fof(f435,plain,(
    v13_waybel_0(sK2,sK1) ),
    inference(subsumption_resolution,[],[f434,f67])).

fof(f67,plain,(
    v13_waybel_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f434,plain,
    ( ~ v13_waybel_0(sK2,sK0)
    | v13_waybel_0(sK2,sK1) ),
    inference(resolution,[],[f426,f69])).

fof(f426,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X0,sK0)
      | v13_waybel_0(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f424,f57])).

fof(f424,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X0,sK0)
      | v13_waybel_0(X0,sK1)
      | ~ l1_orders_2(sK0) ) ),
    inference(duplicate_literal_removal,[],[f423])).

fof(f423,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v13_waybel_0(X0,sK1)
      | ~ l1_orders_2(sK0) ) ),
    inference(equality_resolution,[],[f161])).

fof(f161,plain,(
    ! [X0,X1] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v13_waybel_0(X1,sK1)
      | ~ l1_orders_2(X0) ) ),
    inference(forward_demodulation,[],[f160,f153])).

fof(f160,plain,(
    ! [X0,X1] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v13_waybel_0(X1,sK1)
      | ~ l1_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f155,f63])).

fof(f155,plain,(
    ! [X0,X1] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v13_waybel_0(X1,sK1)
      | ~ l1_orders_2(sK1)
      | ~ l1_orders_2(X0) ) ),
    inference(superposition,[],[f93,f64])).

fof(f93,plain,(
    ! [X0,X3,X1] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ v13_waybel_0(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | v13_waybel_0(X3,X1)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( v13_waybel_0(X3,X1)
      | ~ v13_waybel_0(X2,X0)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v13_waybel_0(X3,X1)
                      | ~ v13_waybel_0(X2,X0) )
                    & ( v12_waybel_0(X3,X1)
                      | ~ v12_waybel_0(X2,X0) ) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v13_waybel_0(X3,X1)
                      | ~ v13_waybel_0(X2,X0) )
                    & ( v12_waybel_0(X3,X1)
                      | ~ v12_waybel_0(X2,X0) ) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( X2 = X3
                     => ( ( v13_waybel_0(X2,X0)
                         => v13_waybel_0(X3,X1) )
                        & ( v12_waybel_0(X2,X0)
                         => v12_waybel_0(X3,X1) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_waybel_0)).

fof(f924,plain,
    ( ~ v13_waybel_0(sK2,sK1)
    | ~ v2_waybel_0(sK2,sK1) ),
    inference(resolution,[],[f921,f173])).

fof(f173,plain,
    ( ~ v2_waybel_7(sK2,sK1)
    | ~ v13_waybel_0(sK2,sK1)
    | ~ v2_waybel_0(sK2,sK1) ),
    inference(subsumption_resolution,[],[f172,f65])).

fof(f65,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f172,plain,
    ( ~ v2_waybel_7(sK2,sK1)
    | ~ v13_waybel_0(sK2,sK1)
    | ~ v2_waybel_0(sK2,sK1)
    | v1_xboole_0(sK2) ),
    inference(subsumption_resolution,[],[f162,f69])).

fof(f162,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_waybel_7(sK2,sK1)
    | ~ v13_waybel_0(sK2,sK1)
    | ~ v2_waybel_0(sK2,sK1)
    | v1_xboole_0(sK2) ),
    inference(superposition,[],[f70,f153])).

fof(f70,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_waybel_7(sK2,sK1)
    | ~ v13_waybel_0(sK2,sK1)
    | ~ v2_waybel_0(sK2,sK1)
    | v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f921,plain,(
    v2_waybel_7(sK2,sK1) ),
    inference(subsumption_resolution,[],[f920,f528])).

fof(f920,plain,
    ( v2_waybel_7(sK2,sK1)
    | ~ v2_waybel_0(sK2,sK1) ),
    inference(subsumption_resolution,[],[f919,f435])).

fof(f919,plain,
    ( v2_waybel_7(sK2,sK1)
    | ~ v13_waybel_0(sK2,sK1)
    | ~ v2_waybel_0(sK2,sK1) ),
    inference(resolution,[],[f915,f361])).

fof(f361,plain,
    ( ~ r2_hidden(sK3(sK1,sK2),sK2)
    | ~ v13_waybel_0(sK2,sK1)
    | ~ v2_waybel_0(sK2,sK1) ),
    inference(subsumption_resolution,[],[f360,f173])).

fof(f360,plain,
    ( ~ r2_hidden(sK3(sK1,sK2),sK2)
    | ~ v13_waybel_0(sK2,sK1)
    | ~ v2_waybel_0(sK2,sK1)
    | v2_waybel_7(sK2,sK1) ),
    inference(subsumption_resolution,[],[f359,f65])).

fof(f359,plain,
    ( ~ r2_hidden(sK3(sK1,sK2),sK2)
    | ~ v13_waybel_0(sK2,sK1)
    | ~ v2_waybel_0(sK2,sK1)
    | v1_xboole_0(sK2)
    | v2_waybel_7(sK2,sK1) ),
    inference(resolution,[],[f342,f69])).

fof(f342,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK3(sK1,X0),X0)
      | ~ v13_waybel_0(X0,sK1)
      | ~ v2_waybel_0(X0,sK1)
      | v1_xboole_0(X0)
      | v2_waybel_7(X0,sK1) ) ),
    inference(superposition,[],[f141,f153])).

fof(f141,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ r2_hidden(sK3(sK1,X1),X1)
      | ~ v13_waybel_0(X1,sK1)
      | ~ v2_waybel_0(X1,sK1)
      | v1_xboole_0(X1)
      | v2_waybel_7(X1,sK1) ) ),
    inference(subsumption_resolution,[],[f140,f58])).

fof(f58,plain,(
    v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f140,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK3(sK1,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v13_waybel_0(X1,sK1)
      | ~ v2_waybel_0(X1,sK1)
      | v1_xboole_0(X1)
      | v2_waybel_7(X1,sK1)
      | ~ v3_orders_2(sK1) ) ),
    inference(subsumption_resolution,[],[f139,f59])).

fof(f59,plain,(
    v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f139,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK3(sK1,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v13_waybel_0(X1,sK1)
      | ~ v2_waybel_0(X1,sK1)
      | v1_xboole_0(X1)
      | v2_waybel_7(X1,sK1)
      | ~ v4_orders_2(sK1)
      | ~ v3_orders_2(sK1) ) ),
    inference(subsumption_resolution,[],[f138,f60])).

fof(f60,plain,(
    v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f138,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK3(sK1,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v13_waybel_0(X1,sK1)
      | ~ v2_waybel_0(X1,sK1)
      | v1_xboole_0(X1)
      | v2_waybel_7(X1,sK1)
      | ~ v5_orders_2(sK1)
      | ~ v4_orders_2(sK1)
      | ~ v3_orders_2(sK1) ) ),
    inference(subsumption_resolution,[],[f133,f63])).

fof(f133,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK3(sK1,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v13_waybel_0(X1,sK1)
      | ~ v2_waybel_0(X1,sK1)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(sK1)
      | v2_waybel_7(X1,sK1)
      | ~ v5_orders_2(sK1)
      | ~ v4_orders_2(sK1)
      | ~ v3_orders_2(sK1) ) ),
    inference(resolution,[],[f84,f61])).

fof(f61,plain,(
    v1_lattice3(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ v1_lattice3(X0)
      | ~ r2_hidden(sK3(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | v2_waybel_7(X1,X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_waybel_7(X1,X0)
              | ( ~ r2_hidden(sK4(X0,X1),X1)
                & ~ r2_hidden(sK3(X0,X1),X1)
                & r2_hidden(k13_lattice3(X0,sK3(X0,X1),sK4(X0,X1)),X1)
                & m1_subset_1(sK4(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | r2_hidden(X4,X1)
                      | ~ r2_hidden(k13_lattice3(X0,X4,X5),X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v2_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f43,f45,f44])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X2,X1)
              & r2_hidden(k13_lattice3(X0,X2,X3),X1)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ~ r2_hidden(X3,X1)
            & ~ r2_hidden(sK3(X0,X1),X1)
            & r2_hidden(k13_lattice3(X0,sK3(X0,X1),X3),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X1)
          & ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(k13_lattice3(X0,sK3(X0,X1),X3),X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(k13_lattice3(X0,sK3(X0,X1),sK4(X0,X1)),X1)
        & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_waybel_7(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & ~ r2_hidden(X2,X1)
                      & r2_hidden(k13_lattice3(X0,X2,X3),X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | r2_hidden(X4,X1)
                      | ~ r2_hidden(k13_lattice3(X0,X4,X5),X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v2_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_waybel_7(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & ~ r2_hidden(X2,X1)
                      & r2_hidden(k13_lattice3(X0,X2,X3),X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ! [X3] :
                      ( r2_hidden(X3,X1)
                      | r2_hidden(X2,X1)
                      | ~ r2_hidden(k13_lattice3(X0,X2,X3),X1)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v2_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_waybel_7(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | r2_hidden(X2,X1)
                    | ~ r2_hidden(k13_lattice3(X0,X2,X3),X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_waybel_7(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | r2_hidden(X2,X1)
                    | ~ r2_hidden(k13_lattice3(X0,X2,X3),X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ( v2_waybel_7(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ~ ( ~ r2_hidden(X3,X1)
                        & ~ r2_hidden(X2,X1)
                        & r2_hidden(k13_lattice3(X0,X2,X3),X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_waybel_7)).

fof(f915,plain,
    ( r2_hidden(sK3(sK1,sK2),sK2)
    | v2_waybel_7(sK2,sK1) ),
    inference(subsumption_resolution,[],[f914,f528])).

fof(f914,plain,
    ( r2_hidden(sK3(sK1,sK2),sK2)
    | v2_waybel_7(sK2,sK1)
    | ~ v2_waybel_0(sK2,sK1) ),
    inference(subsumption_resolution,[],[f913,f435])).

fof(f913,plain,
    ( r2_hidden(sK3(sK1,sK2),sK2)
    | v2_waybel_7(sK2,sK1)
    | ~ v13_waybel_0(sK2,sK1)
    | ~ v2_waybel_0(sK2,sK1) ),
    inference(resolution,[],[f906,f376])).

fof(f376,plain,
    ( ~ r2_hidden(sK4(sK1,sK2),sK2)
    | ~ v13_waybel_0(sK2,sK1)
    | ~ v2_waybel_0(sK2,sK1) ),
    inference(subsumption_resolution,[],[f375,f173])).

fof(f375,plain,
    ( ~ r2_hidden(sK4(sK1,sK2),sK2)
    | ~ v13_waybel_0(sK2,sK1)
    | ~ v2_waybel_0(sK2,sK1)
    | v2_waybel_7(sK2,sK1) ),
    inference(subsumption_resolution,[],[f374,f65])).

fof(f374,plain,
    ( ~ r2_hidden(sK4(sK1,sK2),sK2)
    | ~ v13_waybel_0(sK2,sK1)
    | ~ v2_waybel_0(sK2,sK1)
    | v1_xboole_0(sK2)
    | v2_waybel_7(sK2,sK1) ),
    inference(resolution,[],[f358,f69])).

fof(f358,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK4(sK1,X0),X0)
      | ~ v13_waybel_0(X0,sK1)
      | ~ v2_waybel_0(X0,sK1)
      | v1_xboole_0(X0)
      | v2_waybel_7(X0,sK1) ) ),
    inference(superposition,[],[f151,f153])).

fof(f151,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ r2_hidden(sK4(sK1,X1),X1)
      | ~ v13_waybel_0(X1,sK1)
      | ~ v2_waybel_0(X1,sK1)
      | v1_xboole_0(X1)
      | v2_waybel_7(X1,sK1) ) ),
    inference(subsumption_resolution,[],[f150,f58])).

fof(f150,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK4(sK1,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v13_waybel_0(X1,sK1)
      | ~ v2_waybel_0(X1,sK1)
      | v1_xboole_0(X1)
      | v2_waybel_7(X1,sK1)
      | ~ v3_orders_2(sK1) ) ),
    inference(subsumption_resolution,[],[f149,f59])).

fof(f149,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK4(sK1,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v13_waybel_0(X1,sK1)
      | ~ v2_waybel_0(X1,sK1)
      | v1_xboole_0(X1)
      | v2_waybel_7(X1,sK1)
      | ~ v4_orders_2(sK1)
      | ~ v3_orders_2(sK1) ) ),
    inference(subsumption_resolution,[],[f148,f60])).

fof(f148,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK4(sK1,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v13_waybel_0(X1,sK1)
      | ~ v2_waybel_0(X1,sK1)
      | v1_xboole_0(X1)
      | v2_waybel_7(X1,sK1)
      | ~ v5_orders_2(sK1)
      | ~ v4_orders_2(sK1)
      | ~ v3_orders_2(sK1) ) ),
    inference(subsumption_resolution,[],[f143,f63])).

% (6958)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
fof(f143,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK4(sK1,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v13_waybel_0(X1,sK1)
      | ~ v2_waybel_0(X1,sK1)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(sK1)
      | v2_waybel_7(X1,sK1)
      | ~ v5_orders_2(sK1)
      | ~ v4_orders_2(sK1)
      | ~ v3_orders_2(sK1) ) ),
    inference(resolution,[],[f85,f61])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ v1_lattice3(X0)
      | ~ r2_hidden(sK4(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | v2_waybel_7(X1,X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f906,plain,
    ( r2_hidden(sK4(sK1,sK2),sK2)
    | r2_hidden(sK3(sK1,sK2),sK2)
    | v2_waybel_7(sK2,sK1) ),
    inference(subsumption_resolution,[],[f905,f65])).

fof(f905,plain,
    ( r2_hidden(sK3(sK1,sK2),sK2)
    | r2_hidden(sK4(sK1,sK2),sK2)
    | v2_waybel_7(sK2,sK1)
    | v1_xboole_0(sK2) ),
    inference(subsumption_resolution,[],[f904,f528])).

fof(f904,plain,
    ( r2_hidden(sK3(sK1,sK2),sK2)
    | r2_hidden(sK4(sK1,sK2),sK2)
    | v2_waybel_7(sK2,sK1)
    | ~ v2_waybel_0(sK2,sK1)
    | v1_xboole_0(sK2) ),
    inference(subsumption_resolution,[],[f903,f435])).

fof(f903,plain,
    ( r2_hidden(sK3(sK1,sK2),sK2)
    | r2_hidden(sK4(sK1,sK2),sK2)
    | v2_waybel_7(sK2,sK1)
    | ~ v13_waybel_0(sK2,sK1)
    | ~ v2_waybel_0(sK2,sK1)
    | v1_xboole_0(sK2) ),
    inference(subsumption_resolution,[],[f902,f69])).

fof(f902,plain,
    ( r2_hidden(sK3(sK1,sK2),sK2)
    | r2_hidden(sK4(sK1,sK2),sK2)
    | v2_waybel_7(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v13_waybel_0(sK2,sK1)
    | ~ v2_waybel_0(sK2,sK1)
    | v1_xboole_0(sK2) ),
    inference(duplicate_literal_removal,[],[f901])).

fof(f901,plain,
    ( r2_hidden(sK3(sK1,sK2),sK2)
    | r2_hidden(sK4(sK1,sK2),sK2)
    | v2_waybel_7(sK2,sK1)
    | v2_waybel_7(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v13_waybel_0(sK2,sK1)
    | ~ v2_waybel_0(sK2,sK1)
    | v1_xboole_0(sK2) ),
    inference(resolution,[],[f899,f217])).

fof(f217,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(sK1,X0),u1_struct_0(sK0))
      | v2_waybel_7(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X0,sK1)
      | ~ v2_waybel_0(X0,sK1)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f216,f58])).

fof(f216,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(sK1,X0),u1_struct_0(sK0))
      | v2_waybel_7(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X0,sK1)
      | ~ v2_waybel_0(X0,sK1)
      | v1_xboole_0(X0)
      | ~ v3_orders_2(sK1) ) ),
    inference(subsumption_resolution,[],[f215,f59])).

fof(f215,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(sK1,X0),u1_struct_0(sK0))
      | v2_waybel_7(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X0,sK1)
      | ~ v2_waybel_0(X0,sK1)
      | v1_xboole_0(X0)
      | ~ v4_orders_2(sK1)
      | ~ v3_orders_2(sK1) ) ),
    inference(subsumption_resolution,[],[f214,f60])).

fof(f214,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(sK1,X0),u1_struct_0(sK0))
      | v2_waybel_7(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X0,sK1)
      | ~ v2_waybel_0(X0,sK1)
      | v1_xboole_0(X0)
      | ~ v5_orders_2(sK1)
      | ~ v4_orders_2(sK1)
      | ~ v3_orders_2(sK1) ) ),
    inference(subsumption_resolution,[],[f213,f61])).

fof(f213,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(sK1,X0),u1_struct_0(sK0))
      | v2_waybel_7(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X0,sK1)
      | ~ v2_waybel_0(X0,sK1)
      | v1_xboole_0(X0)
      | ~ v1_lattice3(sK1)
      | ~ v5_orders_2(sK1)
      | ~ v4_orders_2(sK1)
      | ~ v3_orders_2(sK1) ) ),
    inference(subsumption_resolution,[],[f212,f63])).

fof(f212,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(sK1,X0),u1_struct_0(sK0))
      | v2_waybel_7(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X0,sK1)
      | ~ v2_waybel_0(X0,sK1)
      | v1_xboole_0(X0)
      | ~ l1_orders_2(sK1)
      | ~ v1_lattice3(sK1)
      | ~ v5_orders_2(sK1)
      | ~ v4_orders_2(sK1)
      | ~ v3_orders_2(sK1) ) ),
    inference(superposition,[],[f81,f153])).

fof(f81,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
      | v2_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f899,plain,
    ( ~ m1_subset_1(sK3(sK1,sK2),u1_struct_0(sK0))
    | r2_hidden(sK3(sK1,sK2),sK2)
    | r2_hidden(sK4(sK1,sK2),sK2)
    | v2_waybel_7(sK2,sK1) ),
    inference(subsumption_resolution,[],[f898,f65])).

fof(f898,plain,
    ( ~ m1_subset_1(sK3(sK1,sK2),u1_struct_0(sK0))
    | r2_hidden(sK3(sK1,sK2),sK2)
    | r2_hidden(sK4(sK1,sK2),sK2)
    | v2_waybel_7(sK2,sK1)
    | v1_xboole_0(sK2) ),
    inference(subsumption_resolution,[],[f897,f528])).

fof(f897,plain,
    ( ~ m1_subset_1(sK3(sK1,sK2),u1_struct_0(sK0))
    | r2_hidden(sK3(sK1,sK2),sK2)
    | r2_hidden(sK4(sK1,sK2),sK2)
    | v2_waybel_7(sK2,sK1)
    | ~ v2_waybel_0(sK2,sK1)
    | v1_xboole_0(sK2) ),
    inference(subsumption_resolution,[],[f896,f435])).

% (6964)Refutation not found, incomplete strategy% (6964)------------------------------
% (6964)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (6964)Termination reason: Refutation not found, incomplete strategy

% (6964)Memory used [KB]: 10618
% (6964)Time elapsed: 0.117 s
% (6964)------------------------------
% (6964)------------------------------
fof(f896,plain,
    ( ~ m1_subset_1(sK3(sK1,sK2),u1_struct_0(sK0))
    | r2_hidden(sK3(sK1,sK2),sK2)
    | r2_hidden(sK4(sK1,sK2),sK2)
    | v2_waybel_7(sK2,sK1)
    | ~ v13_waybel_0(sK2,sK1)
    | ~ v2_waybel_0(sK2,sK1)
    | v1_xboole_0(sK2) ),
    inference(subsumption_resolution,[],[f895,f69])).

fof(f895,plain,
    ( ~ m1_subset_1(sK3(sK1,sK2),u1_struct_0(sK0))
    | r2_hidden(sK3(sK1,sK2),sK2)
    | r2_hidden(sK4(sK1,sK2),sK2)
    | v2_waybel_7(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v13_waybel_0(sK2,sK1)
    | ~ v2_waybel_0(sK2,sK1)
    | v1_xboole_0(sK2) ),
    inference(resolution,[],[f887,f224])).

fof(f224,plain,(
    ! [X0] :
      ( m1_subset_1(sK4(sK1,X0),u1_struct_0(sK0))
      | v2_waybel_7(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X0,sK1)
      | ~ v2_waybel_0(X0,sK1)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f223,f58])).

fof(f223,plain,(
    ! [X0] :
      ( m1_subset_1(sK4(sK1,X0),u1_struct_0(sK0))
      | v2_waybel_7(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X0,sK1)
      | ~ v2_waybel_0(X0,sK1)
      | v1_xboole_0(X0)
      | ~ v3_orders_2(sK1) ) ),
    inference(subsumption_resolution,[],[f222,f59])).

fof(f222,plain,(
    ! [X0] :
      ( m1_subset_1(sK4(sK1,X0),u1_struct_0(sK0))
      | v2_waybel_7(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X0,sK1)
      | ~ v2_waybel_0(X0,sK1)
      | v1_xboole_0(X0)
      | ~ v4_orders_2(sK1)
      | ~ v3_orders_2(sK1) ) ),
    inference(subsumption_resolution,[],[f221,f60])).

fof(f221,plain,(
    ! [X0] :
      ( m1_subset_1(sK4(sK1,X0),u1_struct_0(sK0))
      | v2_waybel_7(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X0,sK1)
      | ~ v2_waybel_0(X0,sK1)
      | v1_xboole_0(X0)
      | ~ v5_orders_2(sK1)
      | ~ v4_orders_2(sK1)
      | ~ v3_orders_2(sK1) ) ),
    inference(subsumption_resolution,[],[f220,f61])).

fof(f220,plain,(
    ! [X0] :
      ( m1_subset_1(sK4(sK1,X0),u1_struct_0(sK0))
      | v2_waybel_7(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X0,sK1)
      | ~ v2_waybel_0(X0,sK1)
      | v1_xboole_0(X0)
      | ~ v1_lattice3(sK1)
      | ~ v5_orders_2(sK1)
      | ~ v4_orders_2(sK1)
      | ~ v3_orders_2(sK1) ) ),
    inference(subsumption_resolution,[],[f219,f63])).

fof(f219,plain,(
    ! [X0] :
      ( m1_subset_1(sK4(sK1,X0),u1_struct_0(sK0))
      | v2_waybel_7(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X0,sK1)
      | ~ v2_waybel_0(X0,sK1)
      | v1_xboole_0(X0)
      | ~ l1_orders_2(sK1)
      | ~ v1_lattice3(sK1)
      | ~ v5_orders_2(sK1)
      | ~ v4_orders_2(sK1)
      | ~ v3_orders_2(sK1) ) ),
    inference(superposition,[],[f82,f153])).

fof(f82,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK4(X0,X1),u1_struct_0(X0))
      | v2_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f887,plain,
    ( ~ m1_subset_1(sK4(sK1,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(sK1,sK2),u1_struct_0(sK0))
    | r2_hidden(sK3(sK1,sK2),sK2)
    | r2_hidden(sK4(sK1,sK2),sK2) ),
    inference(resolution,[],[f885,f440])).

fof(f440,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k13_lattice3(sK0,X0,X1),sK2)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X0,sK2)
      | r2_hidden(X1,sK2) ) ),
    inference(subsumption_resolution,[],[f439,f65])).

fof(f439,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k13_lattice3(sK0,X0,X1),sK2)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X0,sK2)
      | v1_xboole_0(sK2)
      | r2_hidden(X1,sK2) ) ),
    inference(subsumption_resolution,[],[f438,f66])).

fof(f438,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k13_lattice3(sK0,X0,X1),sK2)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X0,sK2)
      | ~ v2_waybel_0(sK2,sK0)
      | v1_xboole_0(sK2)
      | r2_hidden(X1,sK2) ) ),
    inference(subsumption_resolution,[],[f437,f67])).

fof(f437,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k13_lattice3(sK0,X0,X1),sK2)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X0,sK2)
      | ~ v13_waybel_0(sK2,sK0)
      | ~ v2_waybel_0(sK2,sK0)
      | v1_xboole_0(sK2)
      | r2_hidden(X1,sK2) ) ),
    inference(subsumption_resolution,[],[f436,f68])).

fof(f68,plain,(
    v2_waybel_7(sK2,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f436,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k13_lattice3(sK0,X0,X1),sK2)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v2_waybel_7(sK2,sK0)
      | r2_hidden(X0,sK2)
      | ~ v13_waybel_0(sK2,sK0)
      | ~ v2_waybel_0(sK2,sK0)
      | v1_xboole_0(sK2)
      | r2_hidden(X1,sK2) ) ),
    inference(resolution,[],[f250,f69])).

fof(f250,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(k13_lattice3(sK0,X0,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v2_waybel_7(X1,sK0)
      | r2_hidden(X0,X1)
      | ~ v13_waybel_0(X1,sK0)
      | ~ v2_waybel_0(X1,sK0)
      | v1_xboole_0(X1)
      | r2_hidden(X2,X1) ) ),
    inference(subsumption_resolution,[],[f249,f52])).

fof(f52,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f249,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_hidden(k13_lattice3(sK0,X0,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v2_waybel_7(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X1,sK0)
      | ~ v2_waybel_0(X1,sK0)
      | v1_xboole_0(X1)
      | r2_hidden(X2,X1)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f248,f53])).

fof(f53,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f248,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_hidden(k13_lattice3(sK0,X0,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v2_waybel_7(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X1,sK0)
      | ~ v2_waybel_0(X1,sK0)
      | v1_xboole_0(X1)
      | r2_hidden(X2,X1)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f247,f54])).

fof(f54,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f247,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_hidden(k13_lattice3(sK0,X0,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v2_waybel_7(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X1,sK0)
      | ~ v2_waybel_0(X1,sK0)
      | v1_xboole_0(X1)
      | r2_hidden(X2,X1)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f245,f57])).

fof(f245,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_hidden(k13_lattice3(sK0,X0,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v2_waybel_7(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X1,sK0)
      | ~ v2_waybel_0(X1,sK0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(sK0)
      | r2_hidden(X2,X1)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(resolution,[],[f80,f55])).

fof(f55,plain,(
    v1_lattice3(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f80,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ v1_lattice3(X0)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(k13_lattice3(X0,X4,X5),X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v2_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | r2_hidden(X5,X1)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f885,plain,(
    r2_hidden(k13_lattice3(sK0,sK3(sK1,sK2),sK4(sK1,sK2)),sK2) ),
    inference(subsumption_resolution,[],[f884,f528])).

fof(f884,plain,
    ( r2_hidden(k13_lattice3(sK0,sK3(sK1,sK2),sK4(sK1,sK2)),sK2)
    | ~ v2_waybel_0(sK2,sK1) ),
    inference(subsumption_resolution,[],[f883,f435])).

fof(f883,plain,
    ( r2_hidden(k13_lattice3(sK0,sK3(sK1,sK2),sK4(sK1,sK2)),sK2)
    | ~ v13_waybel_0(sK2,sK1)
    | ~ v2_waybel_0(sK2,sK1) ),
    inference(superposition,[],[f412,f879])).

% (6958)Refutation not found, incomplete strategy% (6958)------------------------------
% (6958)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (6958)Termination reason: Refutation not found, incomplete strategy

% (6958)Memory used [KB]: 6140
% (6958)Time elapsed: 0.090 s
% (6958)------------------------------
% (6958)------------------------------
fof(f879,plain,(
    k13_lattice3(sK1,sK3(sK1,sK2),sK4(sK1,sK2)) = k13_lattice3(sK0,sK3(sK1,sK2),sK4(sK1,sK2)) ),
    inference(forward_demodulation,[],[f877,f874])).

fof(f874,plain,(
    k1_yellow_0(sK0,k2_tarski(sK3(sK1,sK2),sK4(sK1,sK2))) = k13_lattice3(sK0,sK3(sK1,sK2),sK4(sK1,sK2)) ),
    inference(superposition,[],[f813,f870])).

fof(f870,plain,(
    k2_tarski(sK3(sK1,sK2),sK4(sK1,sK2)) = k7_domain_1(u1_struct_0(sK0),sK3(sK1,sK2),sK4(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f869,f63])).

fof(f869,plain,
    ( k2_tarski(sK3(sK1,sK2),sK4(sK1,sK2)) = k7_domain_1(u1_struct_0(sK0),sK3(sK1,sK2),sK4(sK1,sK2))
    | ~ l1_orders_2(sK1) ),
    inference(subsumption_resolution,[],[f868,f62])).

fof(f62,plain,(
    v2_lattice3(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f868,plain,
    ( k2_tarski(sK3(sK1,sK2),sK4(sK1,sK2)) = k7_domain_1(u1_struct_0(sK0),sK3(sK1,sK2),sK4(sK1,sK2))
    | ~ v2_lattice3(sK1)
    | ~ l1_orders_2(sK1) ),
    inference(resolution,[],[f862,f73])).

fof(f73,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_lattice3)).

fof(f862,plain,
    ( v2_struct_0(sK1)
    | k2_tarski(sK3(sK1,sK2),sK4(sK1,sK2)) = k7_domain_1(u1_struct_0(sK0),sK3(sK1,sK2),sK4(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f861,f63])).

fof(f861,plain,
    ( k2_tarski(sK3(sK1,sK2),sK4(sK1,sK2)) = k7_domain_1(u1_struct_0(sK0),sK3(sK1,sK2),sK4(sK1,sK2))
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK1) ),
    inference(resolution,[],[f854,f71])).

fof(f71,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f854,plain,
    ( ~ l1_struct_0(sK1)
    | k2_tarski(sK3(sK1,sK2),sK4(sK1,sK2)) = k7_domain_1(u1_struct_0(sK0),sK3(sK1,sK2),sK4(sK1,sK2))
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f852,f167])).

fof(f167,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1) ),
    inference(superposition,[],[f78,f153])).

fof(f78,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f852,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | k2_tarski(sK3(sK1,sK2),sK4(sK1,sK2)) = k7_domain_1(u1_struct_0(sK0),sK3(sK1,sK2),sK4(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f851,f528])).

fof(f851,plain,
    ( k2_tarski(sK3(sK1,sK2),sK4(sK1,sK2)) = k7_domain_1(u1_struct_0(sK0),sK3(sK1,sK2),sK4(sK1,sK2))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ v2_waybel_0(sK2,sK1) ),
    inference(subsumption_resolution,[],[f850,f435])).

fof(f850,plain,
    ( k2_tarski(sK3(sK1,sK2),sK4(sK1,sK2)) = k7_domain_1(u1_struct_0(sK0),sK3(sK1,sK2),sK4(sK1,sK2))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ v13_waybel_0(sK2,sK1)
    | ~ v2_waybel_0(sK2,sK1) ),
    inference(resolution,[],[f843,f173])).

fof(f843,plain,
    ( v2_waybel_7(sK2,sK1)
    | k2_tarski(sK3(sK1,sK2),sK4(sK1,sK2)) = k7_domain_1(u1_struct_0(sK0),sK3(sK1,sK2),sK4(sK1,sK2))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f842,f65])).

fof(f842,plain,
    ( k2_tarski(sK3(sK1,sK2),sK4(sK1,sK2)) = k7_domain_1(u1_struct_0(sK0),sK3(sK1,sK2),sK4(sK1,sK2))
    | v2_waybel_7(sK2,sK1)
    | v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(sK2) ),
    inference(subsumption_resolution,[],[f841,f528])).

fof(f841,plain,
    ( k2_tarski(sK3(sK1,sK2),sK4(sK1,sK2)) = k7_domain_1(u1_struct_0(sK0),sK3(sK1,sK2),sK4(sK1,sK2))
    | v2_waybel_7(sK2,sK1)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ v2_waybel_0(sK2,sK1)
    | v1_xboole_0(sK2) ),
    inference(subsumption_resolution,[],[f840,f435])).

fof(f840,plain,
    ( k2_tarski(sK3(sK1,sK2),sK4(sK1,sK2)) = k7_domain_1(u1_struct_0(sK0),sK3(sK1,sK2),sK4(sK1,sK2))
    | v2_waybel_7(sK2,sK1)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ v13_waybel_0(sK2,sK1)
    | ~ v2_waybel_0(sK2,sK1)
    | v1_xboole_0(sK2) ),
    inference(duplicate_literal_removal,[],[f839])).

fof(f839,plain,
    ( k2_tarski(sK3(sK1,sK2),sK4(sK1,sK2)) = k7_domain_1(u1_struct_0(sK0),sK3(sK1,sK2),sK4(sK1,sK2))
    | v2_waybel_7(sK2,sK1)
    | v2_waybel_7(sK2,sK1)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ v13_waybel_0(sK2,sK1)
    | ~ v2_waybel_0(sK2,sK1)
    | v1_xboole_0(sK2) ),
    inference(resolution,[],[f582,f69])).

fof(f582,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_tarski(sK3(sK1,X0),sK4(sK1,sK2)) = k7_domain_1(u1_struct_0(sK0),sK3(sK1,X0),sK4(sK1,sK2))
      | v2_waybel_7(sK2,sK1)
      | v2_waybel_7(X0,sK1)
      | v1_xboole_0(u1_struct_0(sK0))
      | ~ v13_waybel_0(X0,sK1)
      | ~ v2_waybel_0(X0,sK1)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f537,f217])).

% (6973)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
fof(f537,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v1_xboole_0(u1_struct_0(sK0))
      | k2_tarski(X0,sK4(sK1,sK2)) = k7_domain_1(u1_struct_0(sK0),X0,sK4(sK1,sK2))
      | v2_waybel_7(sK2,sK1) ) ),
    inference(resolution,[],[f528,f501])).

fof(f501,plain,(
    ! [X0] :
      ( ~ v2_waybel_0(sK2,sK1)
      | k2_tarski(X0,sK4(sK1,sK2)) = k7_domain_1(u1_struct_0(sK0),X0,sK4(sK1,sK2))
      | v1_xboole_0(u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_waybel_7(sK2,sK1) ) ),
    inference(subsumption_resolution,[],[f500,f65])).

fof(f500,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k2_tarski(X0,sK4(sK1,sK2)) = k7_domain_1(u1_struct_0(sK0),X0,sK4(sK1,sK2))
      | v1_xboole_0(u1_struct_0(sK0))
      | ~ v2_waybel_0(sK2,sK1)
      | v1_xboole_0(sK2)
      | v2_waybel_7(sK2,sK1) ) ),
    inference(subsumption_resolution,[],[f499,f435])).

fof(f499,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k2_tarski(X0,sK4(sK1,sK2)) = k7_domain_1(u1_struct_0(sK0),X0,sK4(sK1,sK2))
      | v1_xboole_0(u1_struct_0(sK0))
      | ~ v13_waybel_0(sK2,sK1)
      | ~ v2_waybel_0(sK2,sK1)
      | v1_xboole_0(sK2)
      | v2_waybel_7(sK2,sK1) ) ),
    inference(resolution,[],[f469,f69])).

fof(f469,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | k2_tarski(X3,sK4(sK1,X2)) = k7_domain_1(u1_struct_0(sK0),X3,sK4(sK1,X2))
      | v1_xboole_0(u1_struct_0(sK0))
      | ~ v13_waybel_0(X2,sK1)
      | ~ v2_waybel_0(X2,sK1)
      | v1_xboole_0(X2)
      | v2_waybel_7(X2,sK1) ) ),
    inference(forward_demodulation,[],[f468,f153])).

fof(f468,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(sK0))
      | k2_tarski(X3,sK4(sK1,X2)) = k7_domain_1(u1_struct_0(sK0),X3,sK4(sK1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X2,sK1)
      | ~ v2_waybel_0(X2,sK1)
      | v1_xboole_0(X2)
      | v2_waybel_7(X2,sK1)
      | v1_xboole_0(u1_struct_0(sK1)) ) ),
    inference(forward_demodulation,[],[f467,f153])).

fof(f467,plain,(
    ! [X2,X3] :
      ( k2_tarski(X3,sK4(sK1,X2)) = k7_domain_1(u1_struct_0(sK0),X3,sK4(sK1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X2,sK1)
      | ~ v2_waybel_0(X2,sK1)
      | v1_xboole_0(X2)
      | v2_waybel_7(X2,sK1)
      | ~ m1_subset_1(X3,u1_struct_0(sK1))
      | v1_xboole_0(u1_struct_0(sK1)) ) ),
    inference(forward_demodulation,[],[f466,f153])).

fof(f466,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X2,sK1)
      | ~ v2_waybel_0(X2,sK1)
      | v1_xboole_0(X2)
      | v2_waybel_7(X2,sK1)
      | k7_domain_1(u1_struct_0(sK1),X3,sK4(sK1,X2)) = k2_tarski(X3,sK4(sK1,X2))
      | ~ m1_subset_1(X3,u1_struct_0(sK1))
      | v1_xboole_0(u1_struct_0(sK1)) ) ),
    inference(forward_demodulation,[],[f465,f153])).

fof(f465,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v13_waybel_0(X2,sK1)
      | ~ v2_waybel_0(X2,sK1)
      | v1_xboole_0(X2)
      | v2_waybel_7(X2,sK1)
      | k7_domain_1(u1_struct_0(sK1),X3,sK4(sK1,X2)) = k2_tarski(X3,sK4(sK1,X2))
      | ~ m1_subset_1(X3,u1_struct_0(sK1))
      | v1_xboole_0(u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f464,f58])).

fof(f464,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v13_waybel_0(X2,sK1)
      | ~ v2_waybel_0(X2,sK1)
      | v1_xboole_0(X2)
      | v2_waybel_7(X2,sK1)
      | ~ v3_orders_2(sK1)
      | k7_domain_1(u1_struct_0(sK1),X3,sK4(sK1,X2)) = k2_tarski(X3,sK4(sK1,X2))
      | ~ m1_subset_1(X3,u1_struct_0(sK1))
      | v1_xboole_0(u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f463,f59])).

fof(f463,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v13_waybel_0(X2,sK1)
      | ~ v2_waybel_0(X2,sK1)
      | v1_xboole_0(X2)
      | v2_waybel_7(X2,sK1)
      | ~ v4_orders_2(sK1)
      | ~ v3_orders_2(sK1)
      | k7_domain_1(u1_struct_0(sK1),X3,sK4(sK1,X2)) = k2_tarski(X3,sK4(sK1,X2))
      | ~ m1_subset_1(X3,u1_struct_0(sK1))
      | v1_xboole_0(u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f462,f60])).

fof(f462,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v13_waybel_0(X2,sK1)
      | ~ v2_waybel_0(X2,sK1)
      | v1_xboole_0(X2)
      | v2_waybel_7(X2,sK1)
      | ~ v5_orders_2(sK1)
      | ~ v4_orders_2(sK1)
      | ~ v3_orders_2(sK1)
      | k7_domain_1(u1_struct_0(sK1),X3,sK4(sK1,X2)) = k2_tarski(X3,sK4(sK1,X2))
      | ~ m1_subset_1(X3,u1_struct_0(sK1))
      | v1_xboole_0(u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f457,f63])).

fof(f457,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v13_waybel_0(X2,sK1)
      | ~ v2_waybel_0(X2,sK1)
      | v1_xboole_0(X2)
      | ~ l1_orders_2(sK1)
      | v2_waybel_7(X2,sK1)
      | ~ v5_orders_2(sK1)
      | ~ v4_orders_2(sK1)
      | ~ v3_orders_2(sK1)
      | k7_domain_1(u1_struct_0(sK1),X3,sK4(sK1,X2)) = k2_tarski(X3,sK4(sK1,X2))
      | ~ m1_subset_1(X3,u1_struct_0(sK1))
      | v1_xboole_0(u1_struct_0(sK1)) ) ),
    inference(resolution,[],[f218,f61])).

fof(f218,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_lattice3(X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v13_waybel_0(X0,X1)
      | ~ v2_waybel_0(X0,X1)
      | v1_xboole_0(X0)
      | ~ l1_orders_2(X1)
      | v2_waybel_7(X0,X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | k7_domain_1(u1_struct_0(X1),X2,sK4(X1,X0)) = k2_tarski(X2,sK4(X1,X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | v1_xboole_0(u1_struct_0(X1)) ) ),
    inference(resolution,[],[f82,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,X0)
      | k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,X0)
        & m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_domain_1)).

fof(f813,plain,(
    k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK0),sK3(sK1,sK2),sK4(sK1,sK2))) = k13_lattice3(sK0,sK3(sK1,sK2),sK4(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f812,f528])).

fof(f812,plain,
    ( k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK0),sK3(sK1,sK2),sK4(sK1,sK2))) = k13_lattice3(sK0,sK3(sK1,sK2),sK4(sK1,sK2))
    | ~ v2_waybel_0(sK2,sK1) ),
    inference(subsumption_resolution,[],[f811,f435])).

fof(f811,plain,
    ( k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK0),sK3(sK1,sK2),sK4(sK1,sK2))) = k13_lattice3(sK0,sK3(sK1,sK2),sK4(sK1,sK2))
    | ~ v13_waybel_0(sK2,sK1)
    | ~ v2_waybel_0(sK2,sK1) ),
    inference(resolution,[],[f791,f173])).

fof(f791,plain,
    ( v2_waybel_7(sK2,sK1)
    | k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK0),sK3(sK1,sK2),sK4(sK1,sK2))) = k13_lattice3(sK0,sK3(sK1,sK2),sK4(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f790,f65])).

fof(f790,plain,
    ( k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK0),sK3(sK1,sK2),sK4(sK1,sK2))) = k13_lattice3(sK0,sK3(sK1,sK2),sK4(sK1,sK2))
    | v2_waybel_7(sK2,sK1)
    | v1_xboole_0(sK2) ),
    inference(subsumption_resolution,[],[f789,f528])).

fof(f789,plain,
    ( k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK0),sK3(sK1,sK2),sK4(sK1,sK2))) = k13_lattice3(sK0,sK3(sK1,sK2),sK4(sK1,sK2))
    | v2_waybel_7(sK2,sK1)
    | ~ v2_waybel_0(sK2,sK1)
    | v1_xboole_0(sK2) ),
    inference(subsumption_resolution,[],[f788,f435])).

fof(f788,plain,
    ( k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK0),sK3(sK1,sK2),sK4(sK1,sK2))) = k13_lattice3(sK0,sK3(sK1,sK2),sK4(sK1,sK2))
    | v2_waybel_7(sK2,sK1)
    | ~ v13_waybel_0(sK2,sK1)
    | ~ v2_waybel_0(sK2,sK1)
    | v1_xboole_0(sK2) ),
    inference(duplicate_literal_removal,[],[f787])).

fof(f787,plain,
    ( k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK0),sK3(sK1,sK2),sK4(sK1,sK2))) = k13_lattice3(sK0,sK3(sK1,sK2),sK4(sK1,sK2))
    | v2_waybel_7(sK2,sK1)
    | v2_waybel_7(sK2,sK1)
    | ~ v13_waybel_0(sK2,sK1)
    | ~ v2_waybel_0(sK2,sK1)
    | v1_xboole_0(sK2) ),
    inference(resolution,[],[f624,f69])).

fof(f624,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK0),sK3(sK1,sK2),sK4(sK1,X1))) = k13_lattice3(sK0,sK3(sK1,sK2),sK4(sK1,X1))
      | v2_waybel_7(X1,sK1)
      | v2_waybel_7(sK2,sK1)
      | ~ v13_waybel_0(X1,sK1)
      | ~ v2_waybel_0(X1,sK1)
      | v1_xboole_0(X1) ) ),
    inference(resolution,[],[f622,f224])).

fof(f622,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_waybel_7(sK2,sK1)
      | k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK0),sK3(sK1,sK2),X0)) = k13_lattice3(sK0,sK3(sK1,sK2),X0) ) ),
    inference(subsumption_resolution,[],[f621,f65])).

fof(f621,plain,(
    ! [X0] :
      ( v2_waybel_7(sK2,sK1)
      | v1_xboole_0(sK2)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK0),sK3(sK1,sK2),X0)) = k13_lattice3(sK0,sK3(sK1,sK2),X0) ) ),
    inference(subsumption_resolution,[],[f620,f528])).

fof(f620,plain,(
    ! [X0] :
      ( v2_waybel_7(sK2,sK1)
      | ~ v2_waybel_0(sK2,sK1)
      | v1_xboole_0(sK2)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK0),sK3(sK1,sK2),X0)) = k13_lattice3(sK0,sK3(sK1,sK2),X0) ) ),
    inference(subsumption_resolution,[],[f619,f435])).

fof(f619,plain,(
    ! [X0] :
      ( v2_waybel_7(sK2,sK1)
      | ~ v13_waybel_0(sK2,sK1)
      | ~ v2_waybel_0(sK2,sK1)
      | v1_xboole_0(sK2)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK0),sK3(sK1,sK2),X0)) = k13_lattice3(sK0,sK3(sK1,sK2),X0) ) ),
    inference(resolution,[],[f472,f69])).

fof(f472,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_waybel_7(X4,sK1)
      | ~ v13_waybel_0(X4,sK1)
      | ~ v2_waybel_0(X4,sK1)
      | v1_xboole_0(X4)
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK0),sK3(sK1,X4),X5)) = k13_lattice3(sK0,sK3(sK1,X4),X5) ) ),
    inference(resolution,[],[f217,f125])).

fof(f125,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK0),X1,X0)) = k13_lattice3(sK0,X1,X0) ) ),
    inference(subsumption_resolution,[],[f124,f52])).

fof(f124,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK0),X1,X0)) = k13_lattice3(sK0,X1,X0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f123,f53])).

fof(f123,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK0),X1,X0)) = k13_lattice3(sK0,X1,X0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f122,f54])).

fof(f122,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK0),X1,X0)) = k13_lattice3(sK0,X1,X0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f120,f57])).

fof(f120,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK0),X1,X0)) = k13_lattice3(sK0,X1,X0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(resolution,[],[f79,f55])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_lattice3(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | k1_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,X2)) = k13_lattice3(X0,X1,X2)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,X2)) = k13_lattice3(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,X2)) = k13_lattice3(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k1_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,X2)) = k13_lattice3(X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_yellow_0)).

fof(f877,plain,(
    k13_lattice3(sK1,sK3(sK1,sK2),sK4(sK1,sK2)) = k1_yellow_0(sK0,k2_tarski(sK3(sK1,sK2),sK4(sK1,sK2))) ),
    inference(superposition,[],[f873,f761])).

fof(f761,plain,(
    k1_yellow_0(sK1,k2_tarski(sK3(sK1,sK2),sK4(sK1,sK2))) = k1_yellow_0(sK0,k2_tarski(sK3(sK1,sK2),sK4(sK1,sK2))) ),
    inference(subsumption_resolution,[],[f760,f528])).

fof(f760,plain,
    ( k1_yellow_0(sK1,k2_tarski(sK3(sK1,sK2),sK4(sK1,sK2))) = k1_yellow_0(sK0,k2_tarski(sK3(sK1,sK2),sK4(sK1,sK2)))
    | ~ v2_waybel_0(sK2,sK1) ),
    inference(subsumption_resolution,[],[f759,f435])).

fof(f759,plain,
    ( k1_yellow_0(sK1,k2_tarski(sK3(sK1,sK2),sK4(sK1,sK2))) = k1_yellow_0(sK0,k2_tarski(sK3(sK1,sK2),sK4(sK1,sK2)))
    | ~ v13_waybel_0(sK2,sK1)
    | ~ v2_waybel_0(sK2,sK1) ),
    inference(resolution,[],[f753,f173])).

fof(f753,plain,
    ( v2_waybel_7(sK2,sK1)
    | k1_yellow_0(sK1,k2_tarski(sK3(sK1,sK2),sK4(sK1,sK2))) = k1_yellow_0(sK0,k2_tarski(sK3(sK1,sK2),sK4(sK1,sK2))) ),
    inference(subsumption_resolution,[],[f752,f65])).

fof(f752,plain,
    ( k1_yellow_0(sK1,k2_tarski(sK3(sK1,sK2),sK4(sK1,sK2))) = k1_yellow_0(sK0,k2_tarski(sK3(sK1,sK2),sK4(sK1,sK2)))
    | v2_waybel_7(sK2,sK1)
    | v1_xboole_0(sK2) ),
    inference(subsumption_resolution,[],[f751,f528])).

fof(f751,plain,
    ( k1_yellow_0(sK1,k2_tarski(sK3(sK1,sK2),sK4(sK1,sK2))) = k1_yellow_0(sK0,k2_tarski(sK3(sK1,sK2),sK4(sK1,sK2)))
    | v2_waybel_7(sK2,sK1)
    | ~ v2_waybel_0(sK2,sK1)
    | v1_xboole_0(sK2) ),
    inference(subsumption_resolution,[],[f750,f435])).

fof(f750,plain,
    ( k1_yellow_0(sK1,k2_tarski(sK3(sK1,sK2),sK4(sK1,sK2))) = k1_yellow_0(sK0,k2_tarski(sK3(sK1,sK2),sK4(sK1,sK2)))
    | v2_waybel_7(sK2,sK1)
    | ~ v13_waybel_0(sK2,sK1)
    | ~ v2_waybel_0(sK2,sK1)
    | v1_xboole_0(sK2) ),
    inference(duplicate_literal_removal,[],[f749])).

fof(f749,plain,
    ( k1_yellow_0(sK1,k2_tarski(sK3(sK1,sK2),sK4(sK1,sK2))) = k1_yellow_0(sK0,k2_tarski(sK3(sK1,sK2),sK4(sK1,sK2)))
    | v2_waybel_7(sK2,sK1)
    | v2_waybel_7(sK2,sK1)
    | ~ v13_waybel_0(sK2,sK1)
    | ~ v2_waybel_0(sK2,sK1)
    | v1_xboole_0(sK2) ),
    inference(resolution,[],[f565,f69])).

fof(f565,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_yellow_0(sK1,k2_tarski(sK3(sK1,X0),sK4(sK1,sK2))) = k1_yellow_0(sK0,k2_tarski(sK3(sK1,X0),sK4(sK1,sK2)))
      | v2_waybel_7(X0,sK1)
      | v2_waybel_7(sK2,sK1)
      | ~ v13_waybel_0(X0,sK1)
      | ~ v2_waybel_0(X0,sK1)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f564,f217])).

fof(f564,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_waybel_7(sK2,sK1)
      | k1_yellow_0(sK1,k2_tarski(X0,sK4(sK1,sK2))) = k1_yellow_0(sK0,k2_tarski(X0,sK4(sK1,sK2))) ) ),
    inference(subsumption_resolution,[],[f563,f65])).

fof(f563,plain,(
    ! [X0] :
      ( v2_waybel_7(sK2,sK1)
      | v1_xboole_0(sK2)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k1_yellow_0(sK1,k2_tarski(X0,sK4(sK1,sK2))) = k1_yellow_0(sK0,k2_tarski(X0,sK4(sK1,sK2))) ) ),
    inference(subsumption_resolution,[],[f562,f528])).

fof(f562,plain,(
    ! [X0] :
      ( v2_waybel_7(sK2,sK1)
      | ~ v2_waybel_0(sK2,sK1)
      | v1_xboole_0(sK2)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k1_yellow_0(sK1,k2_tarski(X0,sK4(sK1,sK2))) = k1_yellow_0(sK0,k2_tarski(X0,sK4(sK1,sK2))) ) ),
    inference(subsumption_resolution,[],[f561,f435])).

fof(f561,plain,(
    ! [X0] :
      ( v2_waybel_7(sK2,sK1)
      | ~ v13_waybel_0(sK2,sK1)
      | ~ v2_waybel_0(sK2,sK1)
      | v1_xboole_0(sK2)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k1_yellow_0(sK1,k2_tarski(X0,sK4(sK1,sK2))) = k1_yellow_0(sK0,k2_tarski(X0,sK4(sK1,sK2))) ) ),
    inference(resolution,[],[f475,f69])).

fof(f475,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_waybel_7(X0,sK1)
      | ~ v13_waybel_0(X0,sK1)
      | ~ v2_waybel_0(X0,sK1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k1_yellow_0(sK1,k2_tarski(X1,sK4(sK1,X0))) = k1_yellow_0(sK0,k2_tarski(X1,sK4(sK1,X0))) ) ),
    inference(resolution,[],[f224,f384])).

fof(f384,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k1_yellow_0(sK1,k2_tarski(X0,X1)) = k1_yellow_0(sK0,k2_tarski(X0,X1)) ) ),
    inference(forward_demodulation,[],[f383,f153])).

fof(f383,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k1_yellow_0(sK1,k2_tarski(X0,X1)) = k1_yellow_0(sK0,k2_tarski(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK1)) ) ),
    inference(forward_demodulation,[],[f382,f153])).

fof(f382,plain,(
    ! [X0,X1] :
      ( k1_yellow_0(sK1,k2_tarski(X0,X1)) = k1_yellow_0(sK0,k2_tarski(X0,X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,u1_struct_0(sK1)) ) ),
    inference(resolution,[],[f381,f113])).

fof(f113,plain,(
    ! [X2,X3] :
      ( r1_yellow_0(sK1,k2_tarski(X3,X2))
      | ~ m1_subset_1(X3,u1_struct_0(sK1))
      | ~ m1_subset_1(X2,u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f112,f60])).

fof(f112,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK1))
      | ~ m1_subset_1(X3,u1_struct_0(sK1))
      | r1_yellow_0(sK1,k2_tarski(X3,X2))
      | ~ v5_orders_2(sK1) ) ),
    inference(subsumption_resolution,[],[f109,f63])).

fof(f109,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK1))
      | ~ m1_subset_1(X3,u1_struct_0(sK1))
      | r1_yellow_0(sK1,k2_tarski(X3,X2))
      | ~ l1_orders_2(sK1)
      | ~ v5_orders_2(sK1) ) ),
    inference(resolution,[],[f86,f61])).

fof(f86,plain,(
    ! [X4,X0,X3] :
      ( ~ v1_lattice3(X0)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r1_yellow_0(X0,k2_tarski(X3,X4))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ( ( v1_lattice3(X0)
          | ( ~ r1_yellow_0(X0,k2_tarski(sK5(X0),sK6(X0)))
            & m1_subset_1(sK6(X0),u1_struct_0(X0))
            & m1_subset_1(sK5(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( r1_yellow_0(X0,k2_tarski(X3,X4))
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v1_lattice3(X0) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f48,f50,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_yellow_0(X0,k2_tarski(X1,X2))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ~ r1_yellow_0(X0,k2_tarski(sK5(X0),X2))
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK5(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0] :
      ( ? [X2] :
          ( ~ r1_yellow_0(X0,k2_tarski(sK5(X0),X2))
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ~ r1_yellow_0(X0,k2_tarski(sK5(X0),sK6(X0)))
        & m1_subset_1(sK6(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0] :
      ( ( ( v1_lattice3(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ~ r1_yellow_0(X0,k2_tarski(X1,X2))
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( r1_yellow_0(X0,k2_tarski(X3,X4))
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v1_lattice3(X0) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(rectify,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ( ( v1_lattice3(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ~ r1_yellow_0(X0,k2_tarski(X1,X2))
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( r1_yellow_0(X0,k2_tarski(X1,X2))
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v1_lattice3(X0) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_lattice3(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( r1_yellow_0(X0,k2_tarski(X1,X2))
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_lattice3(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( r1_yellow_0(X0,k2_tarski(X1,X2))
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ( v1_lattice3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => r1_yellow_0(X0,k2_tarski(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_yellow_0)).

fof(f381,plain,(
    ! [X0] :
      ( ~ r1_yellow_0(sK1,X0)
      | k1_yellow_0(sK1,X0) = k1_yellow_0(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f380,f57])).

fof(f380,plain,(
    ! [X0] :
      ( ~ r1_yellow_0(sK1,X0)
      | k1_yellow_0(sK1,X0) = k1_yellow_0(sK0,X0)
      | ~ l1_orders_2(sK0) ) ),
    inference(equality_resolution,[],[f118])).

fof(f118,plain,(
    ! [X0,X1] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
      | ~ r1_yellow_0(sK1,X1)
      | k1_yellow_0(sK1,X1) = k1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f114,f63])).

fof(f114,plain,(
    ! [X0,X1] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
      | ~ r1_yellow_0(sK1,X1)
      | k1_yellow_0(sK1,X1) = k1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ l1_orders_2(sK1) ) ),
    inference(superposition,[],[f74,f64])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ r1_yellow_0(X0,X2)
      | k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2)
              | ~ r1_yellow_0(X0,X2) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2)
              | ~ r1_yellow_0(X0,X2) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ! [X2] :
                ( r1_yellow_0(X0,X2)
               => k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_yellow_0)).

fof(f873,plain,(
    k13_lattice3(sK1,sK3(sK1,sK2),sK4(sK1,sK2)) = k1_yellow_0(sK1,k2_tarski(sK3(sK1,sK2),sK4(sK1,sK2))) ),
    inference(superposition,[],[f822,f870])).

fof(f822,plain,(
    k13_lattice3(sK1,sK3(sK1,sK2),sK4(sK1,sK2)) = k1_yellow_0(sK1,k7_domain_1(u1_struct_0(sK0),sK3(sK1,sK2),sK4(sK1,sK2))) ),
    inference(subsumption_resolution,[],[f821,f528])).

fof(f821,plain,
    ( k13_lattice3(sK1,sK3(sK1,sK2),sK4(sK1,sK2)) = k1_yellow_0(sK1,k7_domain_1(u1_struct_0(sK0),sK3(sK1,sK2),sK4(sK1,sK2)))
    | ~ v2_waybel_0(sK2,sK1) ),
    inference(subsumption_resolution,[],[f820,f435])).

fof(f820,plain,
    ( k13_lattice3(sK1,sK3(sK1,sK2),sK4(sK1,sK2)) = k1_yellow_0(sK1,k7_domain_1(u1_struct_0(sK0),sK3(sK1,sK2),sK4(sK1,sK2)))
    | ~ v13_waybel_0(sK2,sK1)
    | ~ v2_waybel_0(sK2,sK1) ),
    inference(resolution,[],[f804,f173])).

fof(f804,plain,
    ( v2_waybel_7(sK2,sK1)
    | k13_lattice3(sK1,sK3(sK1,sK2),sK4(sK1,sK2)) = k1_yellow_0(sK1,k7_domain_1(u1_struct_0(sK0),sK3(sK1,sK2),sK4(sK1,sK2))) ),
    inference(subsumption_resolution,[],[f803,f65])).

fof(f803,plain,
    ( k13_lattice3(sK1,sK3(sK1,sK2),sK4(sK1,sK2)) = k1_yellow_0(sK1,k7_domain_1(u1_struct_0(sK0),sK3(sK1,sK2),sK4(sK1,sK2)))
    | v2_waybel_7(sK2,sK1)
    | v1_xboole_0(sK2) ),
    inference(subsumption_resolution,[],[f802,f528])).

fof(f802,plain,
    ( k13_lattice3(sK1,sK3(sK1,sK2),sK4(sK1,sK2)) = k1_yellow_0(sK1,k7_domain_1(u1_struct_0(sK0),sK3(sK1,sK2),sK4(sK1,sK2)))
    | v2_waybel_7(sK2,sK1)
    | ~ v2_waybel_0(sK2,sK1)
    | v1_xboole_0(sK2) ),
    inference(subsumption_resolution,[],[f801,f435])).

fof(f801,plain,
    ( k13_lattice3(sK1,sK3(sK1,sK2),sK4(sK1,sK2)) = k1_yellow_0(sK1,k7_domain_1(u1_struct_0(sK0),sK3(sK1,sK2),sK4(sK1,sK2)))
    | v2_waybel_7(sK2,sK1)
    | ~ v13_waybel_0(sK2,sK1)
    | ~ v2_waybel_0(sK2,sK1)
    | v1_xboole_0(sK2) ),
    inference(duplicate_literal_removal,[],[f800])).

fof(f800,plain,
    ( k13_lattice3(sK1,sK3(sK1,sK2),sK4(sK1,sK2)) = k1_yellow_0(sK1,k7_domain_1(u1_struct_0(sK0),sK3(sK1,sK2),sK4(sK1,sK2)))
    | v2_waybel_7(sK2,sK1)
    | v2_waybel_7(sK2,sK1)
    | ~ v13_waybel_0(sK2,sK1)
    | ~ v2_waybel_0(sK2,sK1)
    | v1_xboole_0(sK2) ),
    inference(resolution,[],[f643,f69])).

fof(f643,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k13_lattice3(sK1,sK3(sK1,X0),sK4(sK1,sK2)) = k1_yellow_0(sK1,k7_domain_1(u1_struct_0(sK0),sK3(sK1,X0),sK4(sK1,sK2)))
      | v2_waybel_7(X0,sK1)
      | v2_waybel_7(sK2,sK1)
      | ~ v13_waybel_0(X0,sK1)
      | ~ v2_waybel_0(X0,sK1)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f642,f217])).

fof(f642,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_waybel_7(sK2,sK1)
      | k13_lattice3(sK1,X0,sK4(sK1,sK2)) = k1_yellow_0(sK1,k7_domain_1(u1_struct_0(sK0),X0,sK4(sK1,sK2))) ) ),
    inference(subsumption_resolution,[],[f641,f65])).

fof(f641,plain,(
    ! [X0] :
      ( v2_waybel_7(sK2,sK1)
      | v1_xboole_0(sK2)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k13_lattice3(sK1,X0,sK4(sK1,sK2)) = k1_yellow_0(sK1,k7_domain_1(u1_struct_0(sK0),X0,sK4(sK1,sK2))) ) ),
    inference(subsumption_resolution,[],[f640,f528])).

fof(f640,plain,(
    ! [X0] :
      ( v2_waybel_7(sK2,sK1)
      | ~ v2_waybel_0(sK2,sK1)
      | v1_xboole_0(sK2)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k13_lattice3(sK1,X0,sK4(sK1,sK2)) = k1_yellow_0(sK1,k7_domain_1(u1_struct_0(sK0),X0,sK4(sK1,sK2))) ) ),
    inference(subsumption_resolution,[],[f639,f435])).

fof(f639,plain,(
    ! [X0] :
      ( v2_waybel_7(sK2,sK1)
      | ~ v13_waybel_0(sK2,sK1)
      | ~ v2_waybel_0(sK2,sK1)
      | v1_xboole_0(sK2)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k13_lattice3(sK1,X0,sK4(sK1,sK2)) = k1_yellow_0(sK1,k7_domain_1(u1_struct_0(sK0),X0,sK4(sK1,sK2))) ) ),
    inference(resolution,[],[f476,f69])).

fof(f476,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_waybel_7(X2,sK1)
      | ~ v13_waybel_0(X2,sK1)
      | ~ v2_waybel_0(X2,sK1)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | k13_lattice3(sK1,X3,sK4(sK1,X2)) = k1_yellow_0(sK1,k7_domain_1(u1_struct_0(sK0),X3,sK4(sK1,X2))) ) ),
    inference(resolution,[],[f224,f320])).

fof(f320,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k13_lattice3(sK1,X0,X1) = k1_yellow_0(sK1,k7_domain_1(u1_struct_0(sK0),X0,X1)) ) ),
    inference(superposition,[],[f129,f153])).

fof(f129,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(sK1))
      | ~ m1_subset_1(X2,u1_struct_0(sK1))
      | k1_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),X3,X2)) = k13_lattice3(sK1,X3,X2) ) ),
    inference(subsumption_resolution,[],[f128,f58])).

fof(f128,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK1))
      | ~ m1_subset_1(X3,u1_struct_0(sK1))
      | k1_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),X3,X2)) = k13_lattice3(sK1,X3,X2)
      | ~ v3_orders_2(sK1) ) ),
    inference(subsumption_resolution,[],[f127,f59])).

fof(f127,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK1))
      | ~ m1_subset_1(X3,u1_struct_0(sK1))
      | k1_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),X3,X2)) = k13_lattice3(sK1,X3,X2)
      | ~ v4_orders_2(sK1)
      | ~ v3_orders_2(sK1) ) ),
    inference(subsumption_resolution,[],[f126,f60])).

fof(f126,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK1))
      | ~ m1_subset_1(X3,u1_struct_0(sK1))
      | k1_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),X3,X2)) = k13_lattice3(sK1,X3,X2)
      | ~ v5_orders_2(sK1)
      | ~ v4_orders_2(sK1)
      | ~ v3_orders_2(sK1) ) ),
    inference(subsumption_resolution,[],[f121,f63])).

fof(f121,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK1))
      | ~ m1_subset_1(X3,u1_struct_0(sK1))
      | ~ l1_orders_2(sK1)
      | k1_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),X3,X2)) = k13_lattice3(sK1,X3,X2)
      | ~ v5_orders_2(sK1)
      | ~ v4_orders_2(sK1)
      | ~ v3_orders_2(sK1) ) ),
    inference(resolution,[],[f79,f61])).

fof(f412,plain,
    ( r2_hidden(k13_lattice3(sK1,sK3(sK1,sK2),sK4(sK1,sK2)),sK2)
    | ~ v13_waybel_0(sK2,sK1)
    | ~ v2_waybel_0(sK2,sK1) ),
    inference(subsumption_resolution,[],[f411,f173])).

fof(f411,plain,
    ( r2_hidden(k13_lattice3(sK1,sK3(sK1,sK2),sK4(sK1,sK2)),sK2)
    | ~ v13_waybel_0(sK2,sK1)
    | ~ v2_waybel_0(sK2,sK1)
    | v2_waybel_7(sK2,sK1) ),
    inference(subsumption_resolution,[],[f410,f65])).

fof(f410,plain,
    ( r2_hidden(k13_lattice3(sK1,sK3(sK1,sK2),sK4(sK1,sK2)),sK2)
    | ~ v13_waybel_0(sK2,sK1)
    | ~ v2_waybel_0(sK2,sK1)
    | v1_xboole_0(sK2)
    | v2_waybel_7(sK2,sK1) ),
    inference(resolution,[],[f236,f69])).

fof(f236,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(k13_lattice3(sK1,sK3(sK1,X1),sK4(sK1,X1)),X1)
      | ~ v13_waybel_0(X1,sK1)
      | ~ v2_waybel_0(X1,sK1)
      | v1_xboole_0(X1)
      | v2_waybel_7(X1,sK1) ) ),
    inference(forward_demodulation,[],[f235,f153])).

fof(f235,plain,(
    ! [X1] :
      ( r2_hidden(k13_lattice3(sK1,sK3(sK1,X1),sK4(sK1,X1)),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v13_waybel_0(X1,sK1)
      | ~ v2_waybel_0(X1,sK1)
      | v1_xboole_0(X1)
      | v2_waybel_7(X1,sK1) ) ),
    inference(subsumption_resolution,[],[f234,f58])).

fof(f234,plain,(
    ! [X1] :
      ( r2_hidden(k13_lattice3(sK1,sK3(sK1,X1),sK4(sK1,X1)),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v13_waybel_0(X1,sK1)
      | ~ v2_waybel_0(X1,sK1)
      | v1_xboole_0(X1)
      | v2_waybel_7(X1,sK1)
      | ~ v3_orders_2(sK1) ) ),
    inference(subsumption_resolution,[],[f233,f59])).

fof(f233,plain,(
    ! [X1] :
      ( r2_hidden(k13_lattice3(sK1,sK3(sK1,X1),sK4(sK1,X1)),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v13_waybel_0(X1,sK1)
      | ~ v2_waybel_0(X1,sK1)
      | v1_xboole_0(X1)
      | v2_waybel_7(X1,sK1)
      | ~ v4_orders_2(sK1)
      | ~ v3_orders_2(sK1) ) ),
    inference(subsumption_resolution,[],[f232,f60])).

fof(f232,plain,(
    ! [X1] :
      ( r2_hidden(k13_lattice3(sK1,sK3(sK1,X1),sK4(sK1,X1)),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v13_waybel_0(X1,sK1)
      | ~ v2_waybel_0(X1,sK1)
      | v1_xboole_0(X1)
      | v2_waybel_7(X1,sK1)
      | ~ v5_orders_2(sK1)
      | ~ v4_orders_2(sK1)
      | ~ v3_orders_2(sK1) ) ),
    inference(subsumption_resolution,[],[f227,f63])).

fof(f227,plain,(
    ! [X1] :
      ( r2_hidden(k13_lattice3(sK1,sK3(sK1,X1),sK4(sK1,X1)),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v13_waybel_0(X1,sK1)
      | ~ v2_waybel_0(X1,sK1)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(sK1)
      | v2_waybel_7(X1,sK1)
      | ~ v5_orders_2(sK1)
      | ~ v4_orders_2(sK1)
      | ~ v3_orders_2(sK1) ) ),
    inference(resolution,[],[f83,f61])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ v1_lattice3(X0)
      | r2_hidden(k13_lattice3(X0,sK3(X0,X1),sK4(X0,X1)),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | v2_waybel_7(X1,X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f46])).

%------------------------------------------------------------------------------
