%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : yellow19__t2_yellow19.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:51 EDT 2019

% Result     : Theorem 1.32s
% Output     : Refutation 1.32s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 112 expanded)
%              Number of leaves         :   14 (  38 expanded)
%              Depth                    :   21
%              Number of atoms          :  355 ( 742 expanded)
%              Number of equality atoms :   10 (  12 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1282,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1281,f78])).

fof(f78,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0)))) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,
    ( v1_xboole_0(sK2)
    & r2_hidden(sK2,sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
    & v13_waybel_0(sK1,k3_yellow_1(sK0))
    & v2_waybel_0(sK1,k3_yellow_1(sK0))
    & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0)))
    & ~ v1_xboole_0(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f37,f63,f62,f61])).

fof(f61,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( v1_xboole_0(X2)
                & r2_hidden(X2,X1) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
            & v13_waybel_0(X1,k3_yellow_1(X0))
            & v2_waybel_0(X1,k3_yellow_1(X0))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( v1_xboole_0(X2)
              & r2_hidden(X2,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
          & v13_waybel_0(X1,k3_yellow_1(sK0))
          & v2_waybel_0(X1,k3_yellow_1(sK0))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(sK0)))
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( v1_xboole_0(X2)
              & r2_hidden(X2,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
          & v13_waybel_0(X1,k3_yellow_1(X0))
          & v2_waybel_0(X1,k3_yellow_1(X0))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
          & ~ v1_xboole_0(X1) )
     => ( ? [X2] :
            ( v1_xboole_0(X2)
            & r2_hidden(X2,sK1) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
        & v13_waybel_0(sK1,k3_yellow_1(X0))
        & v2_waybel_0(sK1,k3_yellow_1(X0))
        & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(X0)))
        & ~ v1_xboole_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X1] :
      ( ? [X2] :
          ( v1_xboole_0(X2)
          & r2_hidden(X2,X1) )
     => ( v1_xboole_0(sK2)
        & r2_hidden(sK2,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( v1_xboole_0(X2)
              & r2_hidden(X2,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
          & v13_waybel_0(X1,k3_yellow_1(X0))
          & v2_waybel_0(X1,k3_yellow_1(X0))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( v1_xboole_0(X2)
              & r2_hidden(X2,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
          & v13_waybel_0(X1,k3_yellow_1(X0))
          & v2_waybel_0(X1,k3_yellow_1(X0))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
              & v13_waybel_0(X1,k3_yellow_1(X0))
              & v2_waybel_0(X1,k3_yellow_1(X0))
              & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
              & ~ v1_xboole_0(X1) )
           => ! [X2] :
                ~ ( v1_xboole_0(X2)
                  & r2_hidden(X2,X1) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
            & v13_waybel_0(X1,k3_yellow_1(X0))
            & v2_waybel_0(X1,k3_yellow_1(X0))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
            & ~ v1_xboole_0(X1) )
         => ! [X2] :
              ~ ( v1_xboole_0(X2)
                & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t2_yellow19.p',t2_yellow19)).

fof(f1281,plain,(
    ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0)))) ),
    inference(subsumption_resolution,[],[f1280,f75])).

fof(f75,plain,(
    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0))) ),
    inference(cnf_transformation,[],[f64])).

fof(f1280,plain,
    ( ~ v1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0)))) ),
    inference(subsumption_resolution,[],[f1279,f76])).

fof(f76,plain,(
    v2_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f64])).

fof(f1279,plain,
    ( ~ v2_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ v1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0)))) ),
    inference(subsumption_resolution,[],[f1278,f128])).

fof(f128,plain,(
    r2_hidden(o_0_0_xboole_0,sK1) ),
    inference(backward_demodulation,[],[f126,f79])).

fof(f79,plain,(
    r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f64])).

fof(f126,plain,(
    o_0_0_xboole_0 = sK2 ),
    inference(resolution,[],[f124,f80])).

fof(f80,plain,(
    v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f64])).

fof(f124,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f104,f82])).

fof(f82,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t2_yellow19.p',d2_xboole_0)).

fof(f104,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t2_yellow19.p',t6_boole)).

fof(f1278,plain,
    ( ~ r2_hidden(o_0_0_xboole_0,sK1)
    | ~ v2_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ v1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0)))) ),
    inference(resolution,[],[f1078,f77])).

fof(f77,plain,(
    v13_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f64])).

fof(f1078,plain,(
    ! [X0,X1] :
      ( ~ v13_waybel_0(X0,k3_yellow_1(X1))
      | ~ r2_hidden(o_0_0_xboole_0,X0)
      | ~ v2_waybel_0(X0,k3_yellow_1(X1))
      | ~ v1_subset_1(X0,u1_struct_0(k3_yellow_1(X1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) ) ),
    inference(forward_demodulation,[],[f1077,f123])).

fof(f123,plain,(
    ! [X0] : o_0_0_xboole_0 = k3_yellow_0(k3_yellow_1(X0)) ),
    inference(definition_unfolding,[],[f83,f82])).

fof(f83,plain,(
    ! [X0] : k1_xboole_0 = k3_yellow_0(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] : k1_xboole_0 = k3_yellow_0(k3_yellow_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t2_yellow19.p',t18_yellow_1)).

fof(f1077,plain,(
    ! [X0,X1] :
      ( ~ v13_waybel_0(X0,k3_yellow_1(X1))
      | ~ v2_waybel_0(X0,k3_yellow_1(X1))
      | ~ r2_hidden(k3_yellow_0(k3_yellow_1(X1)),X0)
      | ~ v1_subset_1(X0,u1_struct_0(k3_yellow_1(X1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) ) ),
    inference(subsumption_resolution,[],[f1076,f84])).

fof(f84,plain,(
    ! [X0] : ~ v2_struct_0(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0] :
      ( v5_orders_2(k3_yellow_1(X0))
      & v4_orders_2(k3_yellow_1(X0))
      & v3_orders_2(k3_yellow_1(X0))
      & v1_orders_2(k3_yellow_1(X0))
      & ~ v2_struct_0(k3_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t2_yellow19.p',fc7_yellow_1)).

fof(f1076,plain,(
    ! [X0,X1] :
      ( ~ v13_waybel_0(X0,k3_yellow_1(X1))
      | ~ v2_waybel_0(X0,k3_yellow_1(X1))
      | ~ r2_hidden(k3_yellow_0(k3_yellow_1(X1)),X0)
      | v2_struct_0(k3_yellow_1(X1))
      | ~ v1_subset_1(X0,u1_struct_0(k3_yellow_1(X1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) ) ),
    inference(subsumption_resolution,[],[f1075,f86])).

fof(f86,plain,(
    ! [X0] : v3_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f34])).

fof(f1075,plain,(
    ! [X0,X1] :
      ( ~ v13_waybel_0(X0,k3_yellow_1(X1))
      | ~ v2_waybel_0(X0,k3_yellow_1(X1))
      | ~ r2_hidden(k3_yellow_0(k3_yellow_1(X1)),X0)
      | ~ v3_orders_2(k3_yellow_1(X1))
      | v2_struct_0(k3_yellow_1(X1))
      | ~ v1_subset_1(X0,u1_struct_0(k3_yellow_1(X1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) ) ),
    inference(subsumption_resolution,[],[f1074,f87])).

fof(f87,plain,(
    ! [X0] : v4_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f34])).

fof(f1074,plain,(
    ! [X0,X1] :
      ( ~ v13_waybel_0(X0,k3_yellow_1(X1))
      | ~ v2_waybel_0(X0,k3_yellow_1(X1))
      | ~ r2_hidden(k3_yellow_0(k3_yellow_1(X1)),X0)
      | ~ v4_orders_2(k3_yellow_1(X1))
      | ~ v3_orders_2(k3_yellow_1(X1))
      | v2_struct_0(k3_yellow_1(X1))
      | ~ v1_subset_1(X0,u1_struct_0(k3_yellow_1(X1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) ) ),
    inference(subsumption_resolution,[],[f1073,f88])).

fof(f88,plain,(
    ! [X0] : v5_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f34])).

fof(f1073,plain,(
    ! [X0,X1] :
      ( ~ v13_waybel_0(X0,k3_yellow_1(X1))
      | ~ v2_waybel_0(X0,k3_yellow_1(X1))
      | ~ r2_hidden(k3_yellow_0(k3_yellow_1(X1)),X0)
      | ~ v5_orders_2(k3_yellow_1(X1))
      | ~ v4_orders_2(k3_yellow_1(X1))
      | ~ v3_orders_2(k3_yellow_1(X1))
      | v2_struct_0(k3_yellow_1(X1))
      | ~ v1_subset_1(X0,u1_struct_0(k3_yellow_1(X1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) ) ),
    inference(subsumption_resolution,[],[f1072,f92])).

fof(f92,plain,(
    ! [X0] : l1_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_orders_2(k3_yellow_1(X0))
      & v1_orders_2(k3_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t2_yellow19.p',dt_k3_yellow_1)).

fof(f1072,plain,(
    ! [X0,X1] :
      ( ~ v13_waybel_0(X0,k3_yellow_1(X1))
      | ~ v2_waybel_0(X0,k3_yellow_1(X1))
      | ~ l1_orders_2(k3_yellow_1(X1))
      | ~ r2_hidden(k3_yellow_0(k3_yellow_1(X1)),X0)
      | ~ v5_orders_2(k3_yellow_1(X1))
      | ~ v4_orders_2(k3_yellow_1(X1))
      | ~ v3_orders_2(k3_yellow_1(X1))
      | v2_struct_0(k3_yellow_1(X1))
      | ~ v1_subset_1(X0,u1_struct_0(k3_yellow_1(X1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) ) ),
    inference(resolution,[],[f612,f90])).

fof(f90,plain,(
    ! [X0] : v3_lattice3(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0] :
      ( v3_lattice3(k3_yellow_1(X0))
      & v1_orders_2(k3_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t2_yellow19.p',fc8_yellow_1)).

fof(f612,plain,(
    ! [X0,X1] :
      ( ~ v3_lattice3(X1)
      | ~ v13_waybel_0(X0,X1)
      | ~ v2_waybel_0(X0,X1)
      | ~ l1_orders_2(X1)
      | ~ r2_hidden(k3_yellow_0(X1),X0)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1)
      | ~ v1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) ) ),
    inference(duplicate_literal_removal,[],[f611])).

fof(f611,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v13_waybel_0(X0,X1)
      | ~ v2_waybel_0(X0,X1)
      | ~ l1_orders_2(X1)
      | ~ r2_hidden(k3_yellow_0(X1),X0)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1)
      | ~ v1_subset_1(X0,u1_struct_0(X1))
      | ~ v3_lattice3(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X1) ) ),
    inference(resolution,[],[f446,f100])).

fof(f100,plain,(
    ! [X0] :
      ( v25_waybel_0(X0)
      | ~ v3_lattice3(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ( v25_waybel_0(X0)
        & v24_waybel_0(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
      | ~ v3_lattice3(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ( v25_waybel_0(X0)
        & v24_waybel_0(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
      | ~ v3_lattice3(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( ( v3_lattice3(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ( v25_waybel_0(X0)
          & v24_waybel_0(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t2_yellow19.p',cc11_waybel_0)).

fof(f446,plain,(
    ! [X0,X1] :
      ( ~ v25_waybel_0(X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v13_waybel_0(X0,X1)
      | ~ v2_waybel_0(X0,X1)
      | ~ l1_orders_2(X1)
      | ~ r2_hidden(k3_yellow_0(X1),X0)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1)
      | ~ v1_subset_1(X0,u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f445])).

fof(f445,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v13_waybel_0(X0,X1)
      | ~ v2_waybel_0(X0,X1)
      | ~ l1_orders_2(X1)
      | ~ r2_hidden(k3_yellow_0(X1),X0)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1)
      | ~ v25_waybel_0(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X1) ) ),
    inference(resolution,[],[f397,f103])).

fof(f103,plain,(
    ! [X0] :
      ( v1_yellow_0(X0)
      | ~ v25_waybel_0(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ( v1_yellow_0(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
      | ~ v25_waybel_0(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ( v1_yellow_0(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
      | ~ v25_waybel_0(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( ( v25_waybel_0(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ( v1_yellow_0(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t2_yellow19.p',cc12_waybel_0)).

fof(f397,plain,(
    ! [X0,X1] :
      ( ~ v1_yellow_0(X0)
      | ~ v1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | ~ l1_orders_2(X0)
      | ~ r2_hidden(k3_yellow_0(X0),X1)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f105,f118])).

fof(f118,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t2_yellow19.p',t7_boole)).

fof(f105,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k3_yellow_0(X0),X1)
      | ~ v1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_subset_1(X1,u1_struct_0(X0))
              | r2_hidden(k3_yellow_0(X0),X1) )
            & ( ~ r2_hidden(k3_yellow_0(X0),X1)
              | ~ v1_subset_1(X1,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
          <=> ~ r2_hidden(k3_yellow_0(X0),X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
          <=> ~ r2_hidden(k3_yellow_0(X0),X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ( v1_subset_1(X1,u1_struct_0(X0))
          <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t2_yellow19.p',t8_waybel_7)).
%------------------------------------------------------------------------------
