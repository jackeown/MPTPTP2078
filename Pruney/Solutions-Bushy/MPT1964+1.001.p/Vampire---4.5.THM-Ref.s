%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1964+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:58 EST 2020

% Result     : Theorem 0.12s
% Output     : Refutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :  202 ( 959 expanded)
%              Number of leaves         :    8 ( 221 expanded)
%              Depth                    :   26
%              Number of atoms          :  867 (4770 expanded)
%              Number of equality atoms :    5 (  25 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1672,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1671,f456])).

fof(f456,plain,(
    v2_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f455,f169])).

fof(f169,plain,
    ( r2_hidden(sK4(k3_yellow_1(sK0),sK1),sK1)
    | v2_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f168,f37])).

fof(f37,plain,(
    ! [X0] : v11_waybel_1(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v11_waybel_1(k3_yellow_1(X0))
      & v1_orders_2(k3_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_waybel_7)).

fof(f168,plain,
    ( r2_hidden(sK4(k3_yellow_1(sK0),sK1),sK1)
    | v2_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ v11_waybel_1(k3_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f167,f38])).

fof(f38,plain,(
    ! [X0] : ~ v2_struct_0(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v5_orders_2(k3_yellow_1(X0))
      & v4_orders_2(k3_yellow_1(X0))
      & v3_orders_2(k3_yellow_1(X0))
      & v1_orders_2(k3_yellow_1(X0))
      & ~ v2_struct_0(k3_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_yellow_1)).

fof(f167,plain,
    ( r2_hidden(sK4(k3_yellow_1(sK0),sK1),sK1)
    | v2_waybel_0(sK1,k3_yellow_1(sK0))
    | v2_struct_0(k3_yellow_1(sK0))
    | ~ v11_waybel_1(k3_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f166,f35])).

fof(f35,plain,(
    ! [X0] : l1_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(k3_yellow_1(X0))
      & v1_orders_2(k3_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_yellow_1)).

fof(f166,plain,
    ( r2_hidden(sK4(k3_yellow_1(sK0),sK1),sK1)
    | v2_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | v2_struct_0(k3_yellow_1(sK0))
    | ~ v11_waybel_1(k3_yellow_1(sK0)) ),
    inference(resolution,[],[f62,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v11_waybel_1(X0)
      | v2_lattice3(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v10_waybel_1(X0)
        & v2_waybel_1(X0)
        & v3_yellow_0(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v10_waybel_1(X0)
        & v2_waybel_1(X0)
        & v3_yellow_0(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( ( v11_waybel_1(X0)
          & ~ v2_struct_0(X0) )
       => ( v10_waybel_1(X0)
          & v2_waybel_1(X0)
          & v3_yellow_0(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc8_waybel_1)).

fof(f62,plain,
    ( ~ v2_lattice3(k3_yellow_1(sK0))
    | r2_hidden(sK4(k3_yellow_1(sK0),sK1),sK1)
    | v2_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f61,f24])).

fof(f24,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0)))) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ( v2_waybel_0(X1,k3_yellow_1(X0))
      <~> ! [X2,X3] :
            ( r2_hidden(k3_xboole_0(X2,X3),X1)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X2,X1) ) )
      & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      & v13_waybel_0(X1,k3_yellow_1(X0)) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ( v2_waybel_0(X1,k3_yellow_1(X0))
      <~> ! [X2,X3] :
            ( r2_hidden(k3_xboole_0(X2,X3),X1)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X2,X1) ) )
      & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      & v13_waybel_0(X1,k3_yellow_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
          & v13_waybel_0(X1,k3_yellow_1(X0)) )
       => ( v2_waybel_0(X1,k3_yellow_1(X0))
        <=> ! [X2,X3] :
              ( ( r2_hidden(X3,X1)
                & r2_hidden(X2,X1) )
             => r2_hidden(k3_xboole_0(X2,X3),X1) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
        & v13_waybel_0(X1,k3_yellow_1(X0)) )
     => ( v2_waybel_0(X1,k3_yellow_1(X0))
      <=> ! [X2,X3] :
            ( ( r2_hidden(X3,X1)
              & r2_hidden(X2,X1) )
           => r2_hidden(k3_xboole_0(X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_waybel_7)).

fof(f61,plain,
    ( ~ v2_lattice3(k3_yellow_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
    | r2_hidden(sK4(k3_yellow_1(sK0),sK1),sK1)
    | v2_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f60,f35])).

fof(f60,plain,
    ( ~ v2_lattice3(k3_yellow_1(sK0))
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
    | r2_hidden(sK4(k3_yellow_1(sK0),sK1),sK1)
    | v2_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f52,f42])).

fof(f42,plain,(
    ! [X0] : v5_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f52,plain,
    ( ~ v5_orders_2(k3_yellow_1(sK0))
    | ~ v2_lattice3(k3_yellow_1(sK0))
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
    | r2_hidden(sK4(k3_yellow_1(sK0),sK1),sK1)
    | v2_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(resolution,[],[f23,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(sK4(X0,X1),X1)
      | v2_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(k12_lattice3(X0,X2,X3),X1)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f15])).

% (20590)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(k12_lattice3(X0,X2,X3),X1)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0) )
         => ( v2_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r2_hidden(X3,X1)
                        & r2_hidden(X2,X1) )
                     => r2_hidden(k12_lattice3(X0,X2,X3),X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_waybel_0)).

fof(f23,plain,(
    v13_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f455,plain,
    ( v2_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ r2_hidden(sK4(k3_yellow_1(sK0),sK1),sK1) ),
    inference(duplicate_literal_removal,[],[f452])).

fof(f452,plain,
    ( v2_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ r2_hidden(sK4(k3_yellow_1(sK0),sK1),sK1)
    | v2_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(resolution,[],[f347,f261])).

fof(f261,plain,(
    ! [X0] :
      ( r2_hidden(k3_xboole_0(X0,sK5(k3_yellow_1(sK0),sK1)),sK1)
      | ~ r2_hidden(X0,sK1)
      | v2_waybel_0(sK1,k3_yellow_1(sK0)) ) ),
    inference(duplicate_literal_removal,[],[f257])).

fof(f257,plain,(
    ! [X0] :
      ( v2_waybel_0(sK1,k3_yellow_1(sK0))
      | ~ r2_hidden(X0,sK1)
      | r2_hidden(k3_xboole_0(X0,sK5(k3_yellow_1(sK0),sK1)),sK1)
      | v2_waybel_0(sK1,k3_yellow_1(sK0)) ) ),
    inference(resolution,[],[f173,f22])).

fof(f22,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,sK1)
      | ~ r2_hidden(X2,sK1)
      | r2_hidden(k3_xboole_0(X2,X3),sK1)
      | v2_waybel_0(sK1,k3_yellow_1(sK0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f173,plain,
    ( r2_hidden(sK5(k3_yellow_1(sK0),sK1),sK1)
    | v2_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f172,f37])).

fof(f172,plain,
    ( r2_hidden(sK5(k3_yellow_1(sK0),sK1),sK1)
    | v2_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ v11_waybel_1(k3_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f171,f38])).

fof(f171,plain,
    ( r2_hidden(sK5(k3_yellow_1(sK0),sK1),sK1)
    | v2_waybel_0(sK1,k3_yellow_1(sK0))
    | v2_struct_0(k3_yellow_1(sK0))
    | ~ v11_waybel_1(k3_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f170,f35])).

fof(f170,plain,
    ( r2_hidden(sK5(k3_yellow_1(sK0),sK1),sK1)
    | v2_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | v2_struct_0(k3_yellow_1(sK0))
    | ~ v11_waybel_1(k3_yellow_1(sK0)) ),
    inference(resolution,[],[f65,f47])).

fof(f65,plain,
    ( ~ v2_lattice3(k3_yellow_1(sK0))
    | r2_hidden(sK5(k3_yellow_1(sK0),sK1),sK1)
    | v2_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f64,f24])).

fof(f64,plain,
    ( ~ v2_lattice3(k3_yellow_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
    | r2_hidden(sK5(k3_yellow_1(sK0),sK1),sK1)
    | v2_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f63,f35])).

fof(f63,plain,
    ( ~ v2_lattice3(k3_yellow_1(sK0))
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
    | r2_hidden(sK5(k3_yellow_1(sK0),sK1),sK1)
    | v2_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f53,f42])).

fof(f53,plain,
    ( ~ v5_orders_2(k3_yellow_1(sK0))
    | ~ v2_lattice3(k3_yellow_1(sK0))
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
    | r2_hidden(sK5(k3_yellow_1(sK0),sK1),sK1)
    | v2_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(resolution,[],[f23,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(sK5(X0,X1),X1)
      | v2_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f347,plain,
    ( ~ r2_hidden(k3_xboole_0(sK4(k3_yellow_1(sK0),sK1),sK5(k3_yellow_1(sK0),sK1)),sK1)
    | v2_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f346,f190])).

fof(f190,plain,
    ( m1_subset_1(sK5(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0)))
    | v2_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f189,f37])).

fof(f189,plain,
    ( m1_subset_1(sK5(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0)))
    | v2_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ v11_waybel_1(k3_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f188,f38])).

fof(f188,plain,
    ( m1_subset_1(sK5(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0)))
    | v2_waybel_0(sK1,k3_yellow_1(sK0))
    | v2_struct_0(k3_yellow_1(sK0))
    | ~ v11_waybel_1(k3_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f187,f35])).

fof(f187,plain,
    ( m1_subset_1(sK5(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0)))
    | v2_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | v2_struct_0(k3_yellow_1(sK0))
    | ~ v11_waybel_1(k3_yellow_1(sK0)) ),
    inference(resolution,[],[f59,f47])).

fof(f59,plain,
    ( ~ v2_lattice3(k3_yellow_1(sK0))
    | m1_subset_1(sK5(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0)))
    | v2_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f58,f24])).

fof(f58,plain,
    ( ~ v2_lattice3(k3_yellow_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
    | m1_subset_1(sK5(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0)))
    | v2_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f57,f35])).

fof(f57,plain,
    ( ~ v2_lattice3(k3_yellow_1(sK0))
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
    | m1_subset_1(sK5(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0)))
    | v2_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f51,f42])).

fof(f51,plain,
    ( ~ v5_orders_2(k3_yellow_1(sK0))
    | ~ v2_lattice3(k3_yellow_1(sK0))
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
    | m1_subset_1(sK5(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0)))
    | v2_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(resolution,[],[f23,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
      | v2_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f346,plain,
    ( ~ r2_hidden(k3_xboole_0(sK4(k3_yellow_1(sK0),sK1),sK5(k3_yellow_1(sK0),sK1)),sK1)
    | v2_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ m1_subset_1(sK5(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0))) ),
    inference(subsumption_resolution,[],[f345,f202])).

fof(f202,plain,
    ( m1_subset_1(sK4(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0)))
    | v2_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f201,f37])).

fof(f201,plain,
    ( m1_subset_1(sK4(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0)))
    | v2_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ v11_waybel_1(k3_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f200,f38])).

fof(f200,plain,
    ( m1_subset_1(sK4(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0)))
    | v2_waybel_0(sK1,k3_yellow_1(sK0))
    | v2_struct_0(k3_yellow_1(sK0))
    | ~ v11_waybel_1(k3_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f199,f35])).

fof(f199,plain,
    ( m1_subset_1(sK4(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0)))
    | v2_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | v2_struct_0(k3_yellow_1(sK0))
    | ~ v11_waybel_1(k3_yellow_1(sK0)) ),
    inference(resolution,[],[f74,f47])).

fof(f74,plain,
    ( ~ v2_lattice3(k3_yellow_1(sK0))
    | m1_subset_1(sK4(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0)))
    | v2_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f73,f24])).

fof(f73,plain,
    ( ~ v2_lattice3(k3_yellow_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
    | m1_subset_1(sK4(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0)))
    | v2_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f72,f35])).

fof(f72,plain,
    ( ~ v2_lattice3(k3_yellow_1(sK0))
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
    | m1_subset_1(sK4(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0)))
    | v2_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f56,f42])).

fof(f56,plain,
    ( ~ v5_orders_2(k3_yellow_1(sK0))
    | ~ v2_lattice3(k3_yellow_1(sK0))
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
    | m1_subset_1(sK4(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0)))
    | v2_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(resolution,[],[f23,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(sK4(X0,X1),u1_struct_0(X0))
      | v2_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f345,plain,
    ( ~ r2_hidden(k3_xboole_0(sK4(k3_yellow_1(sK0),sK1),sK5(k3_yellow_1(sK0),sK1)),sK1)
    | v2_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ m1_subset_1(sK4(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0)))
    | ~ m1_subset_1(sK5(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0))) ),
    inference(superposition,[],[f214,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
      | k12_lattice3(k3_yellow_1(X0),X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k12_lattice3(k3_yellow_1(X0),X1,X2) = k3_xboole_0(X1,X2)
            & k13_lattice3(k3_yellow_1(X0),X1,X2) = k2_xboole_0(X1,X2) )
          | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) )
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
         => ( k12_lattice3(k3_yellow_1(X0),X1,X2) = k3_xboole_0(X1,X2)
            & k13_lattice3(k3_yellow_1(X0),X1,X2) = k2_xboole_0(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_yellow_1)).

fof(f214,plain,
    ( ~ r2_hidden(k12_lattice3(k3_yellow_1(sK0),sK4(k3_yellow_1(sK0),sK1),sK5(k3_yellow_1(sK0),sK1)),sK1)
    | v2_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f213,f37])).

fof(f213,plain,
    ( ~ r2_hidden(k12_lattice3(k3_yellow_1(sK0),sK4(k3_yellow_1(sK0),sK1),sK5(k3_yellow_1(sK0),sK1)),sK1)
    | v2_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ v11_waybel_1(k3_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f212,f38])).

fof(f212,plain,
    ( ~ r2_hidden(k12_lattice3(k3_yellow_1(sK0),sK4(k3_yellow_1(sK0),sK1),sK5(k3_yellow_1(sK0),sK1)),sK1)
    | v2_waybel_0(sK1,k3_yellow_1(sK0))
    | v2_struct_0(k3_yellow_1(sK0))
    | ~ v11_waybel_1(k3_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f211,f35])).

fof(f211,plain,
    ( ~ r2_hidden(k12_lattice3(k3_yellow_1(sK0),sK4(k3_yellow_1(sK0),sK1),sK5(k3_yellow_1(sK0),sK1)),sK1)
    | v2_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | v2_struct_0(k3_yellow_1(sK0))
    | ~ v11_waybel_1(k3_yellow_1(sK0)) ),
    inference(resolution,[],[f68,f47])).

fof(f68,plain,
    ( ~ v2_lattice3(k3_yellow_1(sK0))
    | ~ r2_hidden(k12_lattice3(k3_yellow_1(sK0),sK4(k3_yellow_1(sK0),sK1),sK5(k3_yellow_1(sK0),sK1)),sK1)
    | v2_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f67,f24])).

fof(f67,plain,
    ( ~ v2_lattice3(k3_yellow_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
    | ~ r2_hidden(k12_lattice3(k3_yellow_1(sK0),sK4(k3_yellow_1(sK0),sK1),sK5(k3_yellow_1(sK0),sK1)),sK1)
    | v2_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f66,f35])).

fof(f66,plain,
    ( ~ v2_lattice3(k3_yellow_1(sK0))
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
    | ~ r2_hidden(k12_lattice3(k3_yellow_1(sK0),sK4(k3_yellow_1(sK0),sK1),sK5(k3_yellow_1(sK0),sK1)),sK1)
    | v2_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f54,f42])).

fof(f54,plain,
    ( ~ v5_orders_2(k3_yellow_1(sK0))
    | ~ v2_lattice3(k3_yellow_1(sK0))
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
    | ~ r2_hidden(k12_lattice3(k3_yellow_1(sK0),sK4(k3_yellow_1(sK0),sK1),sK5(k3_yellow_1(sK0),sK1)),sK1)
    | v2_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(resolution,[],[f23,f31])).

% (20584)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(k12_lattice3(X0,sK4(X0,X1),sK5(X0,X1)),X1)
      | v2_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f1671,plain,(
    ~ v2_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f1670,f429])).

fof(f429,plain,(
    r2_hidden(sK2,sK1) ),
    inference(subsumption_resolution,[],[f427,f145])).

fof(f145,plain,
    ( r2_hidden(sK4(k3_yellow_1(sK0),sK1),sK1)
    | r2_hidden(sK2,sK1) ),
    inference(subsumption_resolution,[],[f144,f37])).

fof(f144,plain,
    ( r2_hidden(sK2,sK1)
    | r2_hidden(sK4(k3_yellow_1(sK0),sK1),sK1)
    | ~ v11_waybel_1(k3_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f143,f38])).

fof(f143,plain,
    ( r2_hidden(sK2,sK1)
    | r2_hidden(sK4(k3_yellow_1(sK0),sK1),sK1)
    | v2_struct_0(k3_yellow_1(sK0))
    | ~ v11_waybel_1(k3_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f142,f35])).

fof(f142,plain,
    ( r2_hidden(sK2,sK1)
    | r2_hidden(sK4(k3_yellow_1(sK0),sK1),sK1)
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | v2_struct_0(k3_yellow_1(sK0))
    | ~ v11_waybel_1(k3_yellow_1(sK0)) ),
    inference(resolution,[],[f94,f47])).

fof(f94,plain,
    ( ~ v2_lattice3(k3_yellow_1(sK0))
    | r2_hidden(sK2,sK1)
    | r2_hidden(sK4(k3_yellow_1(sK0),sK1),sK1) ),
    inference(subsumption_resolution,[],[f93,f24])).

fof(f93,plain,
    ( r2_hidden(sK2,sK1)
    | ~ v2_lattice3(k3_yellow_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
    | r2_hidden(sK4(k3_yellow_1(sK0),sK1),sK1) ),
    inference(subsumption_resolution,[],[f92,f23])).

fof(f92,plain,
    ( r2_hidden(sK2,sK1)
    | ~ v2_lattice3(k3_yellow_1(sK0))
    | ~ v13_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
    | r2_hidden(sK4(k3_yellow_1(sK0),sK1),sK1) ),
    inference(subsumption_resolution,[],[f91,f35])).

fof(f91,plain,
    ( r2_hidden(sK2,sK1)
    | ~ v2_lattice3(k3_yellow_1(sK0))
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | ~ v13_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
    | r2_hidden(sK4(k3_yellow_1(sK0),sK1),sK1) ),
    inference(subsumption_resolution,[],[f83,f42])).

fof(f83,plain,
    ( r2_hidden(sK2,sK1)
    | ~ v5_orders_2(k3_yellow_1(sK0))
    | ~ v2_lattice3(k3_yellow_1(sK0))
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | ~ v13_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
    | r2_hidden(sK4(k3_yellow_1(sK0),sK1),sK1) ),
    inference(resolution,[],[f19,f29])).

fof(f19,plain,
    ( ~ v2_waybel_0(sK1,k3_yellow_1(sK0))
    | r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f427,plain,
    ( r2_hidden(sK2,sK1)
    | ~ r2_hidden(sK4(k3_yellow_1(sK0),sK1),sK1) ),
    inference(duplicate_literal_removal,[],[f426])).

fof(f426,plain,
    ( r2_hidden(sK2,sK1)
    | ~ r2_hidden(sK4(k3_yellow_1(sK0),sK1),sK1)
    | r2_hidden(sK2,sK1) ),
    inference(resolution,[],[f339,f196])).

fof(f196,plain,(
    ! [X0] :
      ( r2_hidden(k3_xboole_0(X0,sK5(k3_yellow_1(sK0),sK1)),sK1)
      | ~ r2_hidden(X0,sK1)
      | r2_hidden(sK2,sK1) ) ),
    inference(subsumption_resolution,[],[f192,f19])).

fof(f192,plain,(
    ! [X0] :
      ( r2_hidden(sK2,sK1)
      | ~ r2_hidden(X0,sK1)
      | r2_hidden(k3_xboole_0(X0,sK5(k3_yellow_1(sK0),sK1)),sK1)
      | v2_waybel_0(sK1,k3_yellow_1(sK0)) ) ),
    inference(resolution,[],[f149,f22])).

fof(f149,plain,
    ( r2_hidden(sK5(k3_yellow_1(sK0),sK1),sK1)
    | r2_hidden(sK2,sK1) ),
    inference(subsumption_resolution,[],[f148,f37])).

fof(f148,plain,
    ( r2_hidden(sK2,sK1)
    | r2_hidden(sK5(k3_yellow_1(sK0),sK1),sK1)
    | ~ v11_waybel_1(k3_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f147,f38])).

fof(f147,plain,
    ( r2_hidden(sK2,sK1)
    | r2_hidden(sK5(k3_yellow_1(sK0),sK1),sK1)
    | v2_struct_0(k3_yellow_1(sK0))
    | ~ v11_waybel_1(k3_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f146,f35])).

fof(f146,plain,
    ( r2_hidden(sK2,sK1)
    | r2_hidden(sK5(k3_yellow_1(sK0),sK1),sK1)
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | v2_struct_0(k3_yellow_1(sK0))
    | ~ v11_waybel_1(k3_yellow_1(sK0)) ),
    inference(resolution,[],[f98,f47])).

fof(f98,plain,
    ( ~ v2_lattice3(k3_yellow_1(sK0))
    | r2_hidden(sK2,sK1)
    | r2_hidden(sK5(k3_yellow_1(sK0),sK1),sK1) ),
    inference(subsumption_resolution,[],[f97,f24])).

fof(f97,plain,
    ( r2_hidden(sK2,sK1)
    | ~ v2_lattice3(k3_yellow_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
    | r2_hidden(sK5(k3_yellow_1(sK0),sK1),sK1) ),
    inference(subsumption_resolution,[],[f96,f23])).

fof(f96,plain,
    ( r2_hidden(sK2,sK1)
    | ~ v2_lattice3(k3_yellow_1(sK0))
    | ~ v13_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
    | r2_hidden(sK5(k3_yellow_1(sK0),sK1),sK1) ),
    inference(subsumption_resolution,[],[f95,f35])).

fof(f95,plain,
    ( r2_hidden(sK2,sK1)
    | ~ v2_lattice3(k3_yellow_1(sK0))
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | ~ v13_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
    | r2_hidden(sK5(k3_yellow_1(sK0),sK1),sK1) ),
    inference(subsumption_resolution,[],[f84,f42])).

fof(f84,plain,
    ( r2_hidden(sK2,sK1)
    | ~ v5_orders_2(k3_yellow_1(sK0))
    | ~ v2_lattice3(k3_yellow_1(sK0))
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | ~ v13_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
    | r2_hidden(sK5(k3_yellow_1(sK0),sK1),sK1) ),
    inference(resolution,[],[f19,f30])).

fof(f339,plain,
    ( ~ r2_hidden(k3_xboole_0(sK4(k3_yellow_1(sK0),sK1),sK5(k3_yellow_1(sK0),sK1)),sK1)
    | r2_hidden(sK2,sK1) ),
    inference(subsumption_resolution,[],[f338,f177])).

fof(f177,plain,
    ( m1_subset_1(sK5(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0)))
    | r2_hidden(sK2,sK1) ),
    inference(subsumption_resolution,[],[f176,f37])).

fof(f176,plain,
    ( r2_hidden(sK2,sK1)
    | m1_subset_1(sK5(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0)))
    | ~ v11_waybel_1(k3_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f175,f38])).

fof(f175,plain,
    ( r2_hidden(sK2,sK1)
    | m1_subset_1(sK5(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0)))
    | v2_struct_0(k3_yellow_1(sK0))
    | ~ v11_waybel_1(k3_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f174,f35])).

fof(f174,plain,
    ( r2_hidden(sK2,sK1)
    | m1_subset_1(sK5(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0)))
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | v2_struct_0(k3_yellow_1(sK0))
    | ~ v11_waybel_1(k3_yellow_1(sK0)) ),
    inference(resolution,[],[f90,f47])).

fof(f90,plain,
    ( ~ v2_lattice3(k3_yellow_1(sK0))
    | r2_hidden(sK2,sK1)
    | m1_subset_1(sK5(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0))) ),
    inference(subsumption_resolution,[],[f89,f24])).

fof(f89,plain,
    ( r2_hidden(sK2,sK1)
    | ~ v2_lattice3(k3_yellow_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
    | m1_subset_1(sK5(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0))) ),
    inference(subsumption_resolution,[],[f88,f23])).

fof(f88,plain,
    ( r2_hidden(sK2,sK1)
    | ~ v2_lattice3(k3_yellow_1(sK0))
    | ~ v13_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
    | m1_subset_1(sK5(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0))) ),
    inference(subsumption_resolution,[],[f87,f35])).

fof(f87,plain,
    ( r2_hidden(sK2,sK1)
    | ~ v2_lattice3(k3_yellow_1(sK0))
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | ~ v13_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
    | m1_subset_1(sK5(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0))) ),
    inference(subsumption_resolution,[],[f82,f42])).

fof(f82,plain,
    ( r2_hidden(sK2,sK1)
    | ~ v5_orders_2(k3_yellow_1(sK0))
    | ~ v2_lattice3(k3_yellow_1(sK0))
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | ~ v13_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
    | m1_subset_1(sK5(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0))) ),
    inference(resolution,[],[f19,f28])).

fof(f338,plain,
    ( ~ r2_hidden(k3_xboole_0(sK4(k3_yellow_1(sK0),sK1),sK5(k3_yellow_1(sK0),sK1)),sK1)
    | r2_hidden(sK2,sK1)
    | ~ m1_subset_1(sK5(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0))) ),
    inference(subsumption_resolution,[],[f337,f154])).

fof(f154,plain,
    ( m1_subset_1(sK4(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0)))
    | r2_hidden(sK2,sK1) ),
    inference(resolution,[],[f145,f81])).

fof(f81,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK1)
      | m1_subset_1(X2,u1_struct_0(k3_yellow_1(sK0))) ) ),
    inference(resolution,[],[f24,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f337,plain,
    ( ~ r2_hidden(k3_xboole_0(sK4(k3_yellow_1(sK0),sK1),sK5(k3_yellow_1(sK0),sK1)),sK1)
    | r2_hidden(sK2,sK1)
    | ~ m1_subset_1(sK4(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0)))
    | ~ m1_subset_1(sK5(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0))) ),
    inference(superposition,[],[f206,f26])).

fof(f206,plain,
    ( ~ r2_hidden(k12_lattice3(k3_yellow_1(sK0),sK4(k3_yellow_1(sK0),sK1),sK5(k3_yellow_1(sK0),sK1)),sK1)
    | r2_hidden(sK2,sK1) ),
    inference(subsumption_resolution,[],[f205,f37])).

fof(f205,plain,
    ( r2_hidden(sK2,sK1)
    | ~ r2_hidden(k12_lattice3(k3_yellow_1(sK0),sK4(k3_yellow_1(sK0),sK1),sK5(k3_yellow_1(sK0),sK1)),sK1)
    | ~ v11_waybel_1(k3_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f204,f38])).

fof(f204,plain,
    ( r2_hidden(sK2,sK1)
    | ~ r2_hidden(k12_lattice3(k3_yellow_1(sK0),sK4(k3_yellow_1(sK0),sK1),sK5(k3_yellow_1(sK0),sK1)),sK1)
    | v2_struct_0(k3_yellow_1(sK0))
    | ~ v11_waybel_1(k3_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f203,f35])).

fof(f203,plain,
    ( r2_hidden(sK2,sK1)
    | ~ r2_hidden(k12_lattice3(k3_yellow_1(sK0),sK4(k3_yellow_1(sK0),sK1),sK5(k3_yellow_1(sK0),sK1)),sK1)
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | v2_struct_0(k3_yellow_1(sK0))
    | ~ v11_waybel_1(k3_yellow_1(sK0)) ),
    inference(resolution,[],[f102,f47])).

fof(f102,plain,
    ( ~ v2_lattice3(k3_yellow_1(sK0))
    | r2_hidden(sK2,sK1)
    | ~ r2_hidden(k12_lattice3(k3_yellow_1(sK0),sK4(k3_yellow_1(sK0),sK1),sK5(k3_yellow_1(sK0),sK1)),sK1) ),
    inference(subsumption_resolution,[],[f101,f24])).

fof(f101,plain,
    ( r2_hidden(sK2,sK1)
    | ~ v2_lattice3(k3_yellow_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
    | ~ r2_hidden(k12_lattice3(k3_yellow_1(sK0),sK4(k3_yellow_1(sK0),sK1),sK5(k3_yellow_1(sK0),sK1)),sK1) ),
    inference(subsumption_resolution,[],[f100,f23])).

fof(f100,plain,
    ( r2_hidden(sK2,sK1)
    | ~ v2_lattice3(k3_yellow_1(sK0))
    | ~ v13_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
    | ~ r2_hidden(k12_lattice3(k3_yellow_1(sK0),sK4(k3_yellow_1(sK0),sK1),sK5(k3_yellow_1(sK0),sK1)),sK1) ),
    inference(subsumption_resolution,[],[f99,f35])).

fof(f99,plain,
    ( r2_hidden(sK2,sK1)
    | ~ v2_lattice3(k3_yellow_1(sK0))
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | ~ v13_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
    | ~ r2_hidden(k12_lattice3(k3_yellow_1(sK0),sK4(k3_yellow_1(sK0),sK1),sK5(k3_yellow_1(sK0),sK1)),sK1) ),
    inference(subsumption_resolution,[],[f85,f42])).

fof(f85,plain,
    ( r2_hidden(sK2,sK1)
    | ~ v5_orders_2(k3_yellow_1(sK0))
    | ~ v2_lattice3(k3_yellow_1(sK0))
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | ~ v13_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
    | ~ r2_hidden(k12_lattice3(k3_yellow_1(sK0),sK4(k3_yellow_1(sK0),sK1),sK5(k3_yellow_1(sK0),sK1)),sK1) ),
    inference(resolution,[],[f19,f31])).

fof(f1670,plain,
    ( ~ r2_hidden(sK2,sK1)
    | ~ v2_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f1648,f433])).

fof(f433,plain,(
    r2_hidden(sK3,sK1) ),
    inference(subsumption_resolution,[],[f432,f153])).

fof(f153,plain,
    ( r2_hidden(sK4(k3_yellow_1(sK0),sK1),sK1)
    | r2_hidden(sK3,sK1) ),
    inference(subsumption_resolution,[],[f152,f37])).

fof(f152,plain,
    ( r2_hidden(sK3,sK1)
    | r2_hidden(sK4(k3_yellow_1(sK0),sK1),sK1)
    | ~ v11_waybel_1(k3_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f151,f38])).

fof(f151,plain,
    ( r2_hidden(sK3,sK1)
    | r2_hidden(sK4(k3_yellow_1(sK0),sK1),sK1)
    | v2_struct_0(k3_yellow_1(sK0))
    | ~ v11_waybel_1(k3_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f150,f35])).

fof(f150,plain,
    ( r2_hidden(sK3,sK1)
    | r2_hidden(sK4(k3_yellow_1(sK0),sK1),sK1)
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | v2_struct_0(k3_yellow_1(sK0))
    | ~ v11_waybel_1(k3_yellow_1(sK0)) ),
    inference(resolution,[],[f119,f47])).

fof(f119,plain,
    ( ~ v2_lattice3(k3_yellow_1(sK0))
    | r2_hidden(sK3,sK1)
    | r2_hidden(sK4(k3_yellow_1(sK0),sK1),sK1) ),
    inference(subsumption_resolution,[],[f118,f24])).

fof(f118,plain,
    ( r2_hidden(sK3,sK1)
    | ~ v2_lattice3(k3_yellow_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
    | r2_hidden(sK4(k3_yellow_1(sK0),sK1),sK1) ),
    inference(subsumption_resolution,[],[f117,f23])).

fof(f117,plain,
    ( r2_hidden(sK3,sK1)
    | ~ v2_lattice3(k3_yellow_1(sK0))
    | ~ v13_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
    | r2_hidden(sK4(k3_yellow_1(sK0),sK1),sK1) ),
    inference(subsumption_resolution,[],[f116,f35])).

fof(f116,plain,
    ( r2_hidden(sK3,sK1)
    | ~ v2_lattice3(k3_yellow_1(sK0))
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | ~ v13_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
    | r2_hidden(sK4(k3_yellow_1(sK0),sK1),sK1) ),
    inference(subsumption_resolution,[],[f108,f42])).

fof(f108,plain,
    ( r2_hidden(sK3,sK1)
    | ~ v5_orders_2(k3_yellow_1(sK0))
    | ~ v2_lattice3(k3_yellow_1(sK0))
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | ~ v13_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
    | r2_hidden(sK4(k3_yellow_1(sK0),sK1),sK1) ),
    inference(resolution,[],[f20,f29])).

fof(f20,plain,
    ( ~ v2_waybel_0(sK1,k3_yellow_1(sK0))
    | r2_hidden(sK3,sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f432,plain,
    ( r2_hidden(sK3,sK1)
    | ~ r2_hidden(sK4(k3_yellow_1(sK0),sK1),sK1) ),
    inference(duplicate_literal_removal,[],[f430])).

fof(f430,plain,
    ( r2_hidden(sK3,sK1)
    | ~ r2_hidden(sK4(k3_yellow_1(sK0),sK1),sK1)
    | r2_hidden(sK3,sK1) ),
    inference(resolution,[],[f343,f245])).

fof(f245,plain,(
    ! [X0] :
      ( r2_hidden(k3_xboole_0(X0,sK5(k3_yellow_1(sK0),sK1)),sK1)
      | ~ r2_hidden(X0,sK1)
      | r2_hidden(sK3,sK1) ) ),
    inference(subsumption_resolution,[],[f241,f20])).

fof(f241,plain,(
    ! [X0] :
      ( r2_hidden(sK3,sK1)
      | ~ r2_hidden(X0,sK1)
      | r2_hidden(k3_xboole_0(X0,sK5(k3_yellow_1(sK0),sK1)),sK1)
      | v2_waybel_0(sK1,k3_yellow_1(sK0)) ) ),
    inference(resolution,[],[f165,f22])).

fof(f165,plain,
    ( r2_hidden(sK5(k3_yellow_1(sK0),sK1),sK1)
    | r2_hidden(sK3,sK1) ),
    inference(subsumption_resolution,[],[f164,f37])).

fof(f164,plain,
    ( r2_hidden(sK3,sK1)
    | r2_hidden(sK5(k3_yellow_1(sK0),sK1),sK1)
    | ~ v11_waybel_1(k3_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f163,f38])).

fof(f163,plain,
    ( r2_hidden(sK3,sK1)
    | r2_hidden(sK5(k3_yellow_1(sK0),sK1),sK1)
    | v2_struct_0(k3_yellow_1(sK0))
    | ~ v11_waybel_1(k3_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f162,f35])).

fof(f162,plain,
    ( r2_hidden(sK3,sK1)
    | r2_hidden(sK5(k3_yellow_1(sK0),sK1),sK1)
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | v2_struct_0(k3_yellow_1(sK0))
    | ~ v11_waybel_1(k3_yellow_1(sK0)) ),
    inference(resolution,[],[f123,f47])).

fof(f123,plain,
    ( ~ v2_lattice3(k3_yellow_1(sK0))
    | r2_hidden(sK3,sK1)
    | r2_hidden(sK5(k3_yellow_1(sK0),sK1),sK1) ),
    inference(subsumption_resolution,[],[f122,f24])).

fof(f122,plain,
    ( r2_hidden(sK3,sK1)
    | ~ v2_lattice3(k3_yellow_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
    | r2_hidden(sK5(k3_yellow_1(sK0),sK1),sK1) ),
    inference(subsumption_resolution,[],[f121,f23])).

fof(f121,plain,
    ( r2_hidden(sK3,sK1)
    | ~ v2_lattice3(k3_yellow_1(sK0))
    | ~ v13_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
    | r2_hidden(sK5(k3_yellow_1(sK0),sK1),sK1) ),
    inference(subsumption_resolution,[],[f120,f35])).

fof(f120,plain,
    ( r2_hidden(sK3,sK1)
    | ~ v2_lattice3(k3_yellow_1(sK0))
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | ~ v13_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
    | r2_hidden(sK5(k3_yellow_1(sK0),sK1),sK1) ),
    inference(subsumption_resolution,[],[f109,f42])).

fof(f109,plain,
    ( r2_hidden(sK3,sK1)
    | ~ v5_orders_2(k3_yellow_1(sK0))
    | ~ v2_lattice3(k3_yellow_1(sK0))
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | ~ v13_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
    | r2_hidden(sK5(k3_yellow_1(sK0),sK1),sK1) ),
    inference(resolution,[],[f20,f30])).

fof(f343,plain,
    ( ~ r2_hidden(k3_xboole_0(sK4(k3_yellow_1(sK0),sK1),sK5(k3_yellow_1(sK0),sK1)),sK1)
    | r2_hidden(sK3,sK1) ),
    inference(subsumption_resolution,[],[f342,f182])).

fof(f182,plain,
    ( m1_subset_1(sK5(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0)))
    | r2_hidden(sK3,sK1) ),
    inference(subsumption_resolution,[],[f181,f37])).

fof(f181,plain,
    ( r2_hidden(sK3,sK1)
    | m1_subset_1(sK5(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0)))
    | ~ v11_waybel_1(k3_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f180,f38])).

fof(f180,plain,
    ( r2_hidden(sK3,sK1)
    | m1_subset_1(sK5(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0)))
    | v2_struct_0(k3_yellow_1(sK0))
    | ~ v11_waybel_1(k3_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f179,f35])).

fof(f179,plain,
    ( r2_hidden(sK3,sK1)
    | m1_subset_1(sK5(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0)))
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | v2_struct_0(k3_yellow_1(sK0))
    | ~ v11_waybel_1(k3_yellow_1(sK0)) ),
    inference(resolution,[],[f115,f47])).

fof(f115,plain,
    ( ~ v2_lattice3(k3_yellow_1(sK0))
    | r2_hidden(sK3,sK1)
    | m1_subset_1(sK5(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0))) ),
    inference(subsumption_resolution,[],[f114,f24])).

fof(f114,plain,
    ( r2_hidden(sK3,sK1)
    | ~ v2_lattice3(k3_yellow_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
    | m1_subset_1(sK5(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0))) ),
    inference(subsumption_resolution,[],[f113,f23])).

fof(f113,plain,
    ( r2_hidden(sK3,sK1)
    | ~ v2_lattice3(k3_yellow_1(sK0))
    | ~ v13_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
    | m1_subset_1(sK5(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0))) ),
    inference(subsumption_resolution,[],[f112,f35])).

fof(f112,plain,
    ( r2_hidden(sK3,sK1)
    | ~ v2_lattice3(k3_yellow_1(sK0))
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | ~ v13_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
    | m1_subset_1(sK5(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0))) ),
    inference(subsumption_resolution,[],[f107,f42])).

fof(f107,plain,
    ( r2_hidden(sK3,sK1)
    | ~ v5_orders_2(k3_yellow_1(sK0))
    | ~ v2_lattice3(k3_yellow_1(sK0))
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | ~ v13_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
    | m1_subset_1(sK5(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0))) ),
    inference(resolution,[],[f20,f28])).

fof(f342,plain,
    ( ~ r2_hidden(k3_xboole_0(sK4(k3_yellow_1(sK0),sK1),sK5(k3_yellow_1(sK0),sK1)),sK1)
    | r2_hidden(sK3,sK1)
    | ~ m1_subset_1(sK5(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0))) ),
    inference(subsumption_resolution,[],[f341,f186])).

fof(f186,plain,
    ( m1_subset_1(sK4(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0)))
    | r2_hidden(sK3,sK1) ),
    inference(subsumption_resolution,[],[f185,f37])).

fof(f185,plain,
    ( r2_hidden(sK3,sK1)
    | m1_subset_1(sK4(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0)))
    | ~ v11_waybel_1(k3_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f184,f38])).

fof(f184,plain,
    ( r2_hidden(sK3,sK1)
    | m1_subset_1(sK4(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0)))
    | v2_struct_0(k3_yellow_1(sK0))
    | ~ v11_waybel_1(k3_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f183,f35])).

fof(f183,plain,
    ( r2_hidden(sK3,sK1)
    | m1_subset_1(sK4(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0)))
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | v2_struct_0(k3_yellow_1(sK0))
    | ~ v11_waybel_1(k3_yellow_1(sK0)) ),
    inference(resolution,[],[f131,f47])).

fof(f131,plain,
    ( ~ v2_lattice3(k3_yellow_1(sK0))
    | r2_hidden(sK3,sK1)
    | m1_subset_1(sK4(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0))) ),
    inference(subsumption_resolution,[],[f130,f24])).

fof(f130,plain,
    ( r2_hidden(sK3,sK1)
    | ~ v2_lattice3(k3_yellow_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
    | m1_subset_1(sK4(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0))) ),
    inference(subsumption_resolution,[],[f129,f23])).

fof(f129,plain,
    ( r2_hidden(sK3,sK1)
    | ~ v2_lattice3(k3_yellow_1(sK0))
    | ~ v13_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
    | m1_subset_1(sK4(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0))) ),
    inference(subsumption_resolution,[],[f128,f35])).

fof(f128,plain,
    ( r2_hidden(sK3,sK1)
    | ~ v2_lattice3(k3_yellow_1(sK0))
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | ~ v13_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
    | m1_subset_1(sK4(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0))) ),
    inference(subsumption_resolution,[],[f111,f42])).

fof(f111,plain,
    ( r2_hidden(sK3,sK1)
    | ~ v5_orders_2(k3_yellow_1(sK0))
    | ~ v2_lattice3(k3_yellow_1(sK0))
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | ~ v13_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
    | m1_subset_1(sK4(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0))) ),
    inference(resolution,[],[f20,f33])).

fof(f341,plain,
    ( ~ r2_hidden(k3_xboole_0(sK4(k3_yellow_1(sK0),sK1),sK5(k3_yellow_1(sK0),sK1)),sK1)
    | r2_hidden(sK3,sK1)
    | ~ m1_subset_1(sK4(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0)))
    | ~ m1_subset_1(sK5(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0))) ),
    inference(superposition,[],[f210,f26])).

fof(f210,plain,
    ( ~ r2_hidden(k12_lattice3(k3_yellow_1(sK0),sK4(k3_yellow_1(sK0),sK1),sK5(k3_yellow_1(sK0),sK1)),sK1)
    | r2_hidden(sK3,sK1) ),
    inference(subsumption_resolution,[],[f209,f37])).

fof(f209,plain,
    ( r2_hidden(sK3,sK1)
    | ~ r2_hidden(k12_lattice3(k3_yellow_1(sK0),sK4(k3_yellow_1(sK0),sK1),sK5(k3_yellow_1(sK0),sK1)),sK1)
    | ~ v11_waybel_1(k3_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f208,f38])).

fof(f208,plain,
    ( r2_hidden(sK3,sK1)
    | ~ r2_hidden(k12_lattice3(k3_yellow_1(sK0),sK4(k3_yellow_1(sK0),sK1),sK5(k3_yellow_1(sK0),sK1)),sK1)
    | v2_struct_0(k3_yellow_1(sK0))
    | ~ v11_waybel_1(k3_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f207,f35])).

fof(f207,plain,
    ( r2_hidden(sK3,sK1)
    | ~ r2_hidden(k12_lattice3(k3_yellow_1(sK0),sK4(k3_yellow_1(sK0),sK1),sK5(k3_yellow_1(sK0),sK1)),sK1)
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | v2_struct_0(k3_yellow_1(sK0))
    | ~ v11_waybel_1(k3_yellow_1(sK0)) ),
    inference(resolution,[],[f127,f47])).

fof(f127,plain,
    ( ~ v2_lattice3(k3_yellow_1(sK0))
    | r2_hidden(sK3,sK1)
    | ~ r2_hidden(k12_lattice3(k3_yellow_1(sK0),sK4(k3_yellow_1(sK0),sK1),sK5(k3_yellow_1(sK0),sK1)),sK1) ),
    inference(subsumption_resolution,[],[f126,f24])).

fof(f126,plain,
    ( r2_hidden(sK3,sK1)
    | ~ v2_lattice3(k3_yellow_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
    | ~ r2_hidden(k12_lattice3(k3_yellow_1(sK0),sK4(k3_yellow_1(sK0),sK1),sK5(k3_yellow_1(sK0),sK1)),sK1) ),
    inference(subsumption_resolution,[],[f125,f23])).

fof(f125,plain,
    ( r2_hidden(sK3,sK1)
    | ~ v2_lattice3(k3_yellow_1(sK0))
    | ~ v13_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
    | ~ r2_hidden(k12_lattice3(k3_yellow_1(sK0),sK4(k3_yellow_1(sK0),sK1),sK5(k3_yellow_1(sK0),sK1)),sK1) ),
    inference(subsumption_resolution,[],[f124,f35])).

fof(f124,plain,
    ( r2_hidden(sK3,sK1)
    | ~ v2_lattice3(k3_yellow_1(sK0))
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | ~ v13_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
    | ~ r2_hidden(k12_lattice3(k3_yellow_1(sK0),sK4(k3_yellow_1(sK0),sK1),sK5(k3_yellow_1(sK0),sK1)),sK1) ),
    inference(subsumption_resolution,[],[f110,f42])).

% (20599)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
fof(f110,plain,
    ( r2_hidden(sK3,sK1)
    | ~ v5_orders_2(k3_yellow_1(sK0))
    | ~ v2_lattice3(k3_yellow_1(sK0))
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | ~ v13_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
    | ~ r2_hidden(k12_lattice3(k3_yellow_1(sK0),sK4(k3_yellow_1(sK0),sK1),sK5(k3_yellow_1(sK0),sK1)),sK1) ),
    inference(resolution,[],[f20,f31])).

fof(f1648,plain,
    ( ~ r2_hidden(sK3,sK1)
    | ~ r2_hidden(sK2,sK1)
    | ~ v2_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(resolution,[],[f1283,f21])).

fof(f21,plain,
    ( ~ r2_hidden(k3_xboole_0(sK2,sK3),sK1)
    | ~ v2_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f1283,plain,(
    ! [X0,X1] :
      ( r2_hidden(k3_xboole_0(X0,X1),sK1)
      | ~ r2_hidden(X1,sK1)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f1282,f81])).

fof(f1282,plain,(
    ! [X0,X1] :
      ( r2_hidden(k3_xboole_0(X0,X1),sK1)
      | ~ r2_hidden(X1,sK1)
      | ~ r2_hidden(X0,sK1)
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(sK0))) ) ),
    inference(subsumption_resolution,[],[f1279,f81])).

fof(f1279,plain,(
    ! [X0,X1] :
      ( r2_hidden(k3_xboole_0(X0,X1),sK1)
      | ~ r2_hidden(X1,sK1)
      | ~ r2_hidden(X0,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(sK0))) ) ),
    inference(superposition,[],[f649,f26])).

fof(f649,plain,(
    ! [X0,X1] :
      ( r2_hidden(k12_lattice3(k3_yellow_1(sK0),X1,X0),sK1)
      | ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(X1,sK1) ) ),
    inference(resolution,[],[f456,f220])).

fof(f220,plain,(
    ! [X0,X1] :
      ( ~ v2_waybel_0(sK1,k3_yellow_1(sK0))
      | ~ r2_hidden(X1,sK1)
      | r2_hidden(k12_lattice3(k3_yellow_1(sK0),X0,X1),sK1)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f219,f81])).

fof(f219,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(sK0)))
      | ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(X1,sK1)
      | r2_hidden(k12_lattice3(k3_yellow_1(sK0),X0,X1),sK1)
      | ~ v2_waybel_0(sK1,k3_yellow_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f218,f81])).

fof(f218,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(sK0)))
      | ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(X1,sK1)
      | r2_hidden(k12_lattice3(k3_yellow_1(sK0),X0,X1),sK1)
      | ~ v2_waybel_0(sK1,k3_yellow_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f217,f37])).

fof(f217,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(sK0)))
      | ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(X1,sK1)
      | r2_hidden(k12_lattice3(k3_yellow_1(sK0),X0,X1),sK1)
      | ~ v2_waybel_0(sK1,k3_yellow_1(sK0))
      | ~ v11_waybel_1(k3_yellow_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f216,f38])).

fof(f216,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(sK0)))
      | ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(X1,sK1)
      | r2_hidden(k12_lattice3(k3_yellow_1(sK0),X0,X1),sK1)
      | ~ v2_waybel_0(sK1,k3_yellow_1(sK0))
      | v2_struct_0(k3_yellow_1(sK0))
      | ~ v11_waybel_1(k3_yellow_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f215,f35])).

fof(f215,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(sK0)))
      | ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(X1,sK1)
      | r2_hidden(k12_lattice3(k3_yellow_1(sK0),X0,X1),sK1)
      | ~ v2_waybel_0(sK1,k3_yellow_1(sK0))
      | ~ l1_orders_2(k3_yellow_1(sK0))
      | v2_struct_0(k3_yellow_1(sK0))
      | ~ v11_waybel_1(k3_yellow_1(sK0)) ) ),
    inference(resolution,[],[f71,f47])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ v2_lattice3(k3_yellow_1(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(sK0)))
      | ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(X1,sK1)
      | r2_hidden(k12_lattice3(k3_yellow_1(sK0),X0,X1),sK1)
      | ~ v2_waybel_0(sK1,k3_yellow_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f70,f24])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ v2_lattice3(k3_yellow_1(sK0))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
      | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(sK0)))
      | ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(X1,sK1)
      | r2_hidden(k12_lattice3(k3_yellow_1(sK0),X0,X1),sK1)
      | ~ v2_waybel_0(sK1,k3_yellow_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f69,f35])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ v2_lattice3(k3_yellow_1(sK0))
      | ~ l1_orders_2(k3_yellow_1(sK0))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
      | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(sK0)))
      | ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(X1,sK1)
      | r2_hidden(k12_lattice3(k3_yellow_1(sK0),X0,X1),sK1)
      | ~ v2_waybel_0(sK1,k3_yellow_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f55,f42])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v5_orders_2(k3_yellow_1(sK0))
      | ~ v2_lattice3(k3_yellow_1(sK0))
      | ~ l1_orders_2(k3_yellow_1(sK0))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
      | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(sK0)))
      | ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(X1,sK1)
      | r2_hidden(k12_lattice3(k3_yellow_1(sK0),X0,X1),sK1)
      | ~ v2_waybel_0(sK1,k3_yellow_1(sK0)) ) ),
    inference(resolution,[],[f23,f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v5_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(k12_lattice3(X0,X2,X3),X1)
      | ~ v2_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

%------------------------------------------------------------------------------
