%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : waybel_7__t30_waybel_7.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:05 EDT 2019

% Result     : Theorem 266.88s
% Output     : Refutation 266.88s
% Verified   : 
% Statistics : Number of formulae       :  398 (10790 expanded)
%              Number of leaves         :   28 (3283 expanded)
%              Depth                    :   49
%              Number of atoms          : 2774 (153261 expanded)
%              Number of equality atoms :   49 (1143 expanded)
%              Maximal formula depth    :   25 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f56908,plain,(
    $false ),
    inference(subsumption_resolution,[],[f56724,f54399])).

fof(f54399,plain,(
    r1_xboole_0(k1_tarski(k3_yellow_0(sK0)),sK3(sK0,k1_tarski(k3_yellow_0(sK0)),sK1)) ),
    inference(subsumption_resolution,[],[f54361,f52229])).

fof(f52229,plain,(
    r1_subset_1(k1_tarski(k3_yellow_0(sK0)),sK3(sK0,k1_tarski(k3_yellow_0(sK0)),sK1)) ),
    inference(subsumption_resolution,[],[f52103,f1233])).

fof(f1233,plain,(
    ~ m1_subset_1(k3_yellow_0(sK0),sK1) ),
    inference(subsumption_resolution,[],[f1232,f129])).

fof(f129,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f99])).

fof(f99,plain,
    ( ! [X2] :
        ( ~ v3_waybel_7(X2,sK0)
        | ~ r1_tarski(sK1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v13_waybel_0(X2,sK0)
        | ~ v2_waybel_0(X2,sK0)
        | v1_xboole_0(X2) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & v13_waybel_0(sK1,sK0)
    & v2_waybel_0(sK1,sK0)
    & v1_subset_1(sK1,u1_struct_0(sK0))
    & ~ v1_xboole_0(sK1)
    & l1_orders_2(sK0)
    & v2_lattice3(sK0)
    & v1_lattice3(sK0)
    & v11_waybel_1(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v7_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f47,f98,f97])).

fof(f97,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ! [X2] :
                ( ~ v3_waybel_7(X2,X0)
                | ~ r1_tarski(X1,X2)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                | ~ v13_waybel_0(X2,X0)
                | ~ v2_waybel_0(X2,X0)
                | v1_xboole_0(X2) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & v1_subset_1(X1,u1_struct_0(X0))
            & ~ v1_xboole_0(X1) )
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v11_waybel_1(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v7_struct_0(X0) )
   => ( ? [X1] :
          ( ! [X2] :
              ( ~ v3_waybel_7(X2,sK0)
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
              | ~ v13_waybel_0(X2,sK0)
              | ~ v2_waybel_0(X2,sK0)
              | v1_xboole_0(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
          & v13_waybel_0(X1,sK0)
          & v2_waybel_0(X1,sK0)
          & v1_subset_1(X1,u1_struct_0(sK0))
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(sK0)
      & v2_lattice3(sK0)
      & v1_lattice3(sK0)
      & v11_waybel_1(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v7_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f98,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ~ v3_waybel_7(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v13_waybel_0(X2,X0)
              | ~ v2_waybel_0(X2,X0)
              | v1_xboole_0(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & v2_waybel_0(X1,X0)
          & v1_subset_1(X1,u1_struct_0(X0))
          & ~ v1_xboole_0(X1) )
     => ( ! [X2] :
            ( ~ v3_waybel_7(X2,X0)
            | ~ r1_tarski(sK1,X2)
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v13_waybel_0(X2,X0)
            | ~ v2_waybel_0(X2,X0)
            | v1_xboole_0(X2) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        & v13_waybel_0(sK1,X0)
        & v2_waybel_0(sK1,X0)
        & v1_subset_1(sK1,u1_struct_0(X0))
        & ~ v1_xboole_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ~ v3_waybel_7(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v13_waybel_0(X2,X0)
              | ~ v2_waybel_0(X2,X0)
              | v1_xboole_0(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & v2_waybel_0(X1,X0)
          & v1_subset_1(X1,u1_struct_0(X0))
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v11_waybel_1(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ~ v3_waybel_7(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v13_waybel_0(X2,X0)
              | ~ v2_waybel_0(X2,X0)
              | v1_xboole_0(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & v2_waybel_0(X1,X0)
          & v1_subset_1(X1,u1_struct_0(X0))
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v11_waybel_1(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v11_waybel_1(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v7_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X1,X0)
              & v2_waybel_0(X1,X0)
              & v1_subset_1(X1,u1_struct_0(X0))
              & ~ v1_xboole_0(X1) )
           => ? [X2] :
                ( v3_waybel_7(X2,X0)
                & r1_tarski(X1,X2)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & v13_waybel_0(X2,X0)
                & v2_waybel_0(X2,X0)
                & ~ v1_xboole_0(X2) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v11_waybel_1(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v7_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & v1_subset_1(X1,u1_struct_0(X0))
            & ~ v1_xboole_0(X1) )
         => ? [X2] :
              ( v3_waybel_7(X2,X0)
              & r1_tarski(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X2,X0)
              & v2_waybel_0(X2,X0)
              & ~ v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t30_waybel_7.p',t30_waybel_7)).

fof(f1232,plain,
    ( v1_xboole_0(sK1)
    | ~ m1_subset_1(k3_yellow_0(sK0),sK1) ),
    inference(resolution,[],[f873,f177])).

fof(f177,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t30_waybel_7.p',t2_subset)).

fof(f873,plain,(
    ~ r2_hidden(k3_yellow_0(sK0),sK1) ),
    inference(resolution,[],[f546,f751])).

fof(f751,plain,(
    v1_yellow_0(sK0) ),
    inference(subsumption_resolution,[],[f749,f128])).

fof(f128,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f99])).

fof(f749,plain,
    ( v1_yellow_0(sK0)
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f477,f138])).

fof(f138,plain,(
    ! [X0] :
      ( v1_yellow_0(X0)
      | ~ v3_yellow_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ( v2_yellow_0(X0)
        & v1_yellow_0(X0) )
      | ~ v3_yellow_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ( v2_yellow_0(X0)
        & v1_yellow_0(X0) )
      | ~ v3_yellow_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f40])).

fof(f40,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v3_yellow_0(X0)
       => ( v2_yellow_0(X0)
          & v1_yellow_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t30_waybel_7.p',cc4_yellow_0)).

fof(f477,plain,(
    v3_yellow_0(sK0) ),
    inference(subsumption_resolution,[],[f476,f128])).

fof(f476,plain,
    ( v3_yellow_0(sK0)
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f461,f125])).

fof(f125,plain,(
    v11_waybel_1(sK0) ),
    inference(cnf_transformation,[],[f99])).

fof(f461,plain,
    ( v3_yellow_0(sK0)
    | ~ v11_waybel_1(sK0)
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f388,f147])).

fof(f147,plain,(
    ! [X0] :
      ( v3_yellow_0(X0)
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
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
    inference(flattening,[],[f54])).

fof(f54,plain,(
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
    inference(ennf_transformation,[],[f41])).

fof(f41,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/waybel_7__t30_waybel_7.p',cc8_waybel_1)).

fof(f388,plain,(
    ~ v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f377,f128])).

fof(f377,plain,
    ( ~ v2_struct_0(sK0)
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f127,f140])).

fof(f140,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f39])).

fof(f39,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t30_waybel_7.p',cc2_lattice3)).

fof(f127,plain,(
    v2_lattice3(sK0) ),
    inference(cnf_transformation,[],[f99])).

fof(f546,plain,
    ( ~ v1_yellow_0(sK0)
    | ~ r2_hidden(k3_yellow_0(sK0),sK1) ),
    inference(subsumption_resolution,[],[f545,f388])).

fof(f545,plain,
    ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
    | ~ v1_yellow_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f544,f122])).

fof(f122,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f99])).

fof(f544,plain,
    ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
    | ~ v1_yellow_0(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f543,f123])).

fof(f123,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f99])).

fof(f543,plain,
    ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
    | ~ v1_yellow_0(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f542,f124])).

fof(f124,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f99])).

fof(f542,plain,
    ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
    | ~ v1_yellow_0(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f541,f128])).

fof(f541,plain,
    ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
    | ~ l1_orders_2(sK0)
    | ~ v1_yellow_0(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f540,f129])).

fof(f540,plain,
    ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(sK0)
    | ~ v1_yellow_0(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f539,f132])).

fof(f132,plain,(
    v13_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f99])).

fof(f539,plain,
    ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
    | ~ v13_waybel_0(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(sK0)
    | ~ v1_yellow_0(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f538,f133])).

fof(f133,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f99])).

fof(f538,plain,
    ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(sK0)
    | ~ v1_yellow_0(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f526,f130])).

fof(f130,plain,(
    v1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f99])).

fof(f526,plain,
    ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
    | ~ v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(sK0)
    | ~ v1_yellow_0(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f131,f157])).

fof(f157,plain,(
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
    inference(cnf_transformation,[],[f102])).

fof(f102,plain,(
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
    inference(nnf_transformation,[],[f62])).

fof(f62,plain,(
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
    inference(flattening,[],[f61])).

fof(f61,plain,(
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
    inference(ennf_transformation,[],[f38])).

fof(f38,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/waybel_7__t30_waybel_7.p',t8_waybel_7)).

fof(f131,plain,(
    v2_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f99])).

fof(f52103,plain,
    ( m1_subset_1(k3_yellow_0(sK0),sK1)
    | r1_subset_1(k1_tarski(k3_yellow_0(sK0)),sK3(sK0,k1_tarski(k3_yellow_0(sK0)),sK1)) ),
    inference(resolution,[],[f51942,f3799])).

fof(f3799,plain,
    ( ~ r1_subset_1(k1_tarski(k3_yellow_0(sK0)),sK1)
    | r1_subset_1(k1_tarski(k3_yellow_0(sK0)),sK3(sK0,k1_tarski(k3_yellow_0(sK0)),sK1)) ),
    inference(forward_demodulation,[],[f3678,f3623])).

fof(f3623,plain,(
    k1_tarski(k3_yellow_0(sK0)) = k5_waybel_0(sK0,k3_yellow_0(sK0)) ),
    inference(resolution,[],[f871,f1144])).

fof(f1144,plain,(
    ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f851,f672])).

fof(f672,plain,(
    ! [X14] :
      ( ~ r2_hidden(X14,sK1)
      | ~ v1_xboole_0(u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f133,f198])).

fof(f198,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f96])).

fof(f96,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t30_waybel_7.p',t5_subset)).

fof(f851,plain,(
    r2_hidden(sK4(sK1),sK1) ),
    inference(resolution,[],[f446,f169])).

fof(f169,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f108])).

fof(f108,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f20,f107])).

fof(f107,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f20,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t30_waybel_7.p',existence_m1_subset_1)).

fof(f446,plain,(
    ! [X33] :
      ( ~ m1_subset_1(X33,sK1)
      | r2_hidden(X33,sK1) ) ),
    inference(resolution,[],[f129,f177])).

fof(f871,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | k1_tarski(k3_yellow_0(sK0)) = k5_waybel_0(sK0,k3_yellow_0(sK0)) ),
    inference(backward_demodulation,[],[f870,f818])).

fof(f818,plain,
    ( k1_tarski(k3_yellow_0(sK0)) = k6_domain_1(u1_struct_0(sK0),k3_yellow_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f390,f186])).

fof(f186,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t30_waybel_7.p',redefinition_k6_domain_1)).

fof(f390,plain,(
    m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) ),
    inference(resolution,[],[f128,f137])).

fof(f137,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t30_waybel_7.p',dt_k3_yellow_0)).

fof(f870,plain,(
    k5_waybel_0(sK0,k3_yellow_0(sK0)) = k6_domain_1(u1_struct_0(sK0),k3_yellow_0(sK0)) ),
    inference(subsumption_resolution,[],[f869,f388])).

fof(f869,plain,
    ( k5_waybel_0(sK0,k3_yellow_0(sK0)) = k6_domain_1(u1_struct_0(sK0),k3_yellow_0(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f868,f122])).

fof(f868,plain,
    ( k5_waybel_0(sK0,k3_yellow_0(sK0)) = k6_domain_1(u1_struct_0(sK0),k3_yellow_0(sK0))
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f867,f123])).

fof(f867,plain,
    ( k5_waybel_0(sK0,k3_yellow_0(sK0)) = k6_domain_1(u1_struct_0(sK0),k3_yellow_0(sK0))
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f866,f124])).

fof(f866,plain,
    ( k5_waybel_0(sK0,k3_yellow_0(sK0)) = k6_domain_1(u1_struct_0(sK0),k3_yellow_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f854,f128])).

fof(f854,plain,
    ( k5_waybel_0(sK0,k3_yellow_0(sK0)) = k6_domain_1(u1_struct_0(sK0),k3_yellow_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f751,f156])).

fof(f156,plain,(
    ! [X0] :
      ( k5_waybel_0(X0,k3_yellow_0(X0)) = k6_domain_1(u1_struct_0(X0),k3_yellow_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( k5_waybel_0(X0,k3_yellow_0(X0)) = k6_domain_1(u1_struct_0(X0),k3_yellow_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( k5_waybel_0(X0,k3_yellow_0(X0)) = k6_domain_1(u1_struct_0(X0),k3_yellow_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => k5_waybel_0(X0,k3_yellow_0(X0)) = k6_domain_1(u1_struct_0(X0),k3_yellow_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t30_waybel_7.p',t23_waybel_4)).

fof(f3678,plain,
    ( r1_subset_1(k1_tarski(k3_yellow_0(sK0)),sK3(sK0,k1_tarski(k3_yellow_0(sK0)),sK1))
    | ~ r1_subset_1(k5_waybel_0(sK0,k3_yellow_0(sK0)),sK1) ),
    inference(backward_demodulation,[],[f3623,f1983])).

fof(f1983,plain,
    ( ~ r1_subset_1(k5_waybel_0(sK0,k3_yellow_0(sK0)),sK1)
    | r1_subset_1(k5_waybel_0(sK0,k3_yellow_0(sK0)),sK3(sK0,k5_waybel_0(sK0,k3_yellow_0(sK0)),sK1)) ),
    inference(subsumption_resolution,[],[f1982,f824])).

fof(f824,plain,(
    ~ v1_xboole_0(k5_waybel_0(sK0,k3_yellow_0(sK0))) ),
    inference(subsumption_resolution,[],[f823,f388])).

fof(f823,plain,
    ( ~ v1_xboole_0(k5_waybel_0(sK0,k3_yellow_0(sK0)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f822,f122])).

fof(f822,plain,
    ( ~ v1_xboole_0(k5_waybel_0(sK0,k3_yellow_0(sK0)))
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f814,f128])).

fof(f814,plain,
    ( ~ v1_xboole_0(k5_waybel_0(sK0,k3_yellow_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f390,f179])).

fof(f179,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k5_waybel_0(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ( v1_waybel_0(k5_waybel_0(X0,X1),X0)
        & ~ v1_xboole_0(k5_waybel_0(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ( v1_waybel_0(k5_waybel_0(X0,X1),X0)
        & ~ v1_xboole_0(k5_waybel_0(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f43])).

fof(f43,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_waybel_0(k5_waybel_0(X0,X1),X0)
        & ~ v1_xboole_0(k5_waybel_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t30_waybel_7.p',fc8_waybel_0)).

fof(f1982,plain,
    ( ~ r1_subset_1(k5_waybel_0(sK0,k3_yellow_0(sK0)),sK1)
    | r1_subset_1(k5_waybel_0(sK0,k3_yellow_0(sK0)),sK3(sK0,k5_waybel_0(sK0,k3_yellow_0(sK0)),sK1))
    | v1_xboole_0(k5_waybel_0(sK0,k3_yellow_0(sK0))) ),
    inference(subsumption_resolution,[],[f1981,f827])).

fof(f827,plain,(
    v1_waybel_0(k5_waybel_0(sK0,k3_yellow_0(sK0)),sK0) ),
    inference(subsumption_resolution,[],[f826,f388])).

fof(f826,plain,
    ( v1_waybel_0(k5_waybel_0(sK0,k3_yellow_0(sK0)),sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f825,f122])).

fof(f825,plain,
    ( v1_waybel_0(k5_waybel_0(sK0,k3_yellow_0(sK0)),sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f815,f128])).

fof(f815,plain,
    ( v1_waybel_0(k5_waybel_0(sK0,k3_yellow_0(sK0)),sK0)
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f390,f180])).

fof(f180,plain,(
    ! [X0,X1] :
      ( v1_waybel_0(k5_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f1981,plain,
    ( ~ r1_subset_1(k5_waybel_0(sK0,k3_yellow_0(sK0)),sK1)
    | r1_subset_1(k5_waybel_0(sK0,k3_yellow_0(sK0)),sK3(sK0,k5_waybel_0(sK0,k3_yellow_0(sK0)),sK1))
    | ~ v1_waybel_0(k5_waybel_0(sK0,k3_yellow_0(sK0)),sK0)
    | v1_xboole_0(k5_waybel_0(sK0,k3_yellow_0(sK0))) ),
    inference(subsumption_resolution,[],[f1948,f821])).

fof(f821,plain,(
    m1_subset_1(k5_waybel_0(sK0,k3_yellow_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f820,f388])).

fof(f820,plain,
    ( m1_subset_1(k5_waybel_0(sK0,k3_yellow_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f813,f128])).

fof(f813,plain,
    ( m1_subset_1(k5_waybel_0(sK0,k3_yellow_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f390,f181])).

fof(f181,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t30_waybel_7.p',dt_k5_waybel_0)).

fof(f1948,plain,
    ( ~ r1_subset_1(k5_waybel_0(sK0,k3_yellow_0(sK0)),sK1)
    | ~ m1_subset_1(k5_waybel_0(sK0,k3_yellow_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_subset_1(k5_waybel_0(sK0,k3_yellow_0(sK0)),sK3(sK0,k5_waybel_0(sK0,k3_yellow_0(sK0)),sK1))
    | ~ v1_waybel_0(k5_waybel_0(sK0,k3_yellow_0(sK0)),sK0)
    | v1_xboole_0(k5_waybel_0(sK0,k3_yellow_0(sK0))) ),
    inference(resolution,[],[f830,f616])).

fof(f616,plain,(
    ! [X6] :
      ( ~ v12_waybel_0(X6,sK0)
      | ~ r1_subset_1(X6,sK1)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_subset_1(X6,sK3(sK0,X6,sK1))
      | ~ v1_waybel_0(X6,sK0)
      | v1_xboole_0(X6) ) ),
    inference(subsumption_resolution,[],[f615,f122])).

fof(f615,plain,(
    ! [X6] :
      ( r1_subset_1(X6,sK3(sK0,X6,sK1))
      | ~ r1_subset_1(X6,sK1)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X6,sK0)
      | ~ v1_waybel_0(X6,sK0)
      | v1_xboole_0(X6)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f614,f123])).

fof(f614,plain,(
    ! [X6] :
      ( r1_subset_1(X6,sK3(sK0,X6,sK1))
      | ~ r1_subset_1(X6,sK1)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X6,sK0)
      | ~ v1_waybel_0(X6,sK0)
      | v1_xboole_0(X6)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f613,f124])).

fof(f613,plain,(
    ! [X6] :
      ( r1_subset_1(X6,sK3(sK0,X6,sK1))
      | ~ r1_subset_1(X6,sK1)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X6,sK0)
      | ~ v1_waybel_0(X6,sK0)
      | v1_xboole_0(X6)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f612,f479])).

fof(f479,plain,(
    v2_waybel_1(sK0) ),
    inference(subsumption_resolution,[],[f478,f128])).

fof(f478,plain,
    ( v2_waybel_1(sK0)
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f462,f125])).

fof(f462,plain,
    ( v2_waybel_1(sK0)
    | ~ v11_waybel_1(sK0)
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f388,f148])).

fof(f148,plain,(
    ! [X0] :
      ( v2_waybel_1(X0)
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f612,plain,(
    ! [X6] :
      ( r1_subset_1(X6,sK3(sK0,X6,sK1))
      | ~ r1_subset_1(X6,sK1)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X6,sK0)
      | ~ v1_waybel_0(X6,sK0)
      | v1_xboole_0(X6)
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f611,f126])).

fof(f126,plain,(
    v1_lattice3(sK0) ),
    inference(cnf_transformation,[],[f99])).

fof(f611,plain,(
    ! [X6] :
      ( r1_subset_1(X6,sK3(sK0,X6,sK1))
      | ~ r1_subset_1(X6,sK1)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X6,sK0)
      | ~ v1_waybel_0(X6,sK0)
      | v1_xboole_0(X6)
      | ~ v1_lattice3(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f610,f127])).

fof(f610,plain,(
    ! [X6] :
      ( r1_subset_1(X6,sK3(sK0,X6,sK1))
      | ~ r1_subset_1(X6,sK1)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X6,sK0)
      | ~ v1_waybel_0(X6,sK0)
      | v1_xboole_0(X6)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f609,f128])).

fof(f609,plain,(
    ! [X6] :
      ( r1_subset_1(X6,sK3(sK0,X6,sK1))
      | ~ r1_subset_1(X6,sK1)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X6,sK0)
      | ~ v1_waybel_0(X6,sK0)
      | v1_xboole_0(X6)
      | ~ l1_orders_2(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f608,f129])).

fof(f608,plain,(
    ! [X6] :
      ( r1_subset_1(X6,sK3(sK0,X6,sK1))
      | ~ r1_subset_1(X6,sK1)
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X6,sK0)
      | ~ v1_waybel_0(X6,sK0)
      | v1_xboole_0(X6)
      | ~ l1_orders_2(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f607,f132])).

fof(f607,plain,(
    ! [X6] :
      ( r1_subset_1(X6,sK3(sK0,X6,sK1))
      | ~ r1_subset_1(X6,sK1)
      | ~ v13_waybel_0(sK1,sK0)
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X6,sK0)
      | ~ v1_waybel_0(X6,sK0)
      | v1_xboole_0(X6)
      | ~ l1_orders_2(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f534,f133])).

fof(f534,plain,(
    ! [X6] :
      ( r1_subset_1(X6,sK3(sK0,X6,sK1))
      | ~ r1_subset_1(X6,sK1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(sK1,sK0)
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X6,sK0)
      | ~ v1_waybel_0(X6,sK0)
      | v1_xboole_0(X6)
      | ~ l1_orders_2(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(resolution,[],[f131,f165])).

fof(f165,plain,(
    ! [X2,X0,X1] :
      ( r1_subset_1(X1,sK3(X0,X1,X2))
      | ~ r1_subset_1(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X2,X0)
      | ~ v2_waybel_0(X2,X0)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f104])).

fof(f104,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_subset_1(X1,sK3(X0,X1,X2))
                & r1_tarski(X2,sK3(X0,X1,X2))
                & v2_waybel_7(sK3(X0,X1,X2),X0)
                & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
                & v13_waybel_0(sK3(X0,X1,X2),X0)
                & v2_waybel_0(sK3(X0,X1,X2),X0)
                & ~ v1_xboole_0(sK3(X0,X1,X2)) )
              | ~ r1_subset_1(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v13_waybel_0(X2,X0)
              | ~ v2_waybel_0(X2,X0)
              | v1_xboole_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0)
          | ~ v1_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f64,f103])).

fof(f103,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r1_subset_1(X1,X3)
          & r1_tarski(X2,X3)
          & v2_waybel_7(X3,X0)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X3,X0)
          & v2_waybel_0(X3,X0)
          & ~ v1_xboole_0(X3) )
     => ( r1_subset_1(X1,sK3(X0,X1,X2))
        & r1_tarski(X2,sK3(X0,X1,X2))
        & v2_waybel_7(sK3(X0,X1,X2),X0)
        & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
        & v13_waybel_0(sK3(X0,X1,X2),X0)
        & v2_waybel_0(sK3(X0,X1,X2),X0)
        & ~ v1_xboole_0(sK3(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( r1_subset_1(X1,X3)
                  & r1_tarski(X2,X3)
                  & v2_waybel_7(X3,X0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  & v13_waybel_0(X3,X0)
                  & v2_waybel_0(X3,X0)
                  & ~ v1_xboole_0(X3) )
              | ~ r1_subset_1(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v13_waybel_0(X2,X0)
              | ~ v2_waybel_0(X2,X0)
              | v1_xboole_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0)
          | ~ v1_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( r1_subset_1(X1,X3)
                  & r1_tarski(X2,X3)
                  & v2_waybel_7(X3,X0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  & v13_waybel_0(X3,X0)
                  & v2_waybel_0(X3,X0)
                  & ~ v1_xboole_0(X3) )
              | ~ r1_subset_1(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v13_waybel_0(X2,X0)
              | ~ v2_waybel_0(X2,X0)
              | v1_xboole_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0)
          | ~ v1_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v2_waybel_1(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v12_waybel_0(X1,X0)
            & v1_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & v13_waybel_0(X2,X0)
                & v2_waybel_0(X2,X0)
                & ~ v1_xboole_0(X2) )
             => ~ ( ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                        & v13_waybel_0(X3,X0)
                        & v2_waybel_0(X3,X0)
                        & ~ v1_xboole_0(X3) )
                     => ~ ( r1_subset_1(X1,X3)
                          & r1_tarski(X2,X3)
                          & v2_waybel_7(X3,X0) ) )
                  & r1_subset_1(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t30_waybel_7.p',t29_waybel_7)).

fof(f830,plain,(
    v12_waybel_0(k5_waybel_0(sK0,k3_yellow_0(sK0)),sK0) ),
    inference(subsumption_resolution,[],[f829,f388])).

fof(f829,plain,
    ( v12_waybel_0(k5_waybel_0(sK0,k3_yellow_0(sK0)),sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f828,f123])).

fof(f828,plain,
    ( v12_waybel_0(k5_waybel_0(sK0,k3_yellow_0(sK0)),sK0)
    | ~ v4_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f816,f128])).

fof(f816,plain,
    ( v12_waybel_0(k5_waybel_0(sK0,k3_yellow_0(sK0)),sK0)
    | ~ l1_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f390,f178])).

fof(f178,plain,(
    ! [X0,X1] :
      ( v12_waybel_0(k5_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( v12_waybel_0(k5_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( v12_waybel_0(k5_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f42])).

fof(f42,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v4_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => v12_waybel_0(k5_waybel_0(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t30_waybel_7.p',fc12_waybel_0)).

fof(f51942,plain,(
    ! [X5] :
      ( r1_subset_1(k1_tarski(X5),sK1)
      | m1_subset_1(X5,sK1) ) ),
    inference(duplicate_literal_removal,[],[f51873])).

fof(f51873,plain,(
    ! [X5] :
      ( m1_subset_1(X5,sK1)
      | r1_subset_1(k1_tarski(X5),sK1)
      | r1_subset_1(k1_tarski(X5),sK1) ) ),
    inference(superposition,[],[f28554,f51434])).

fof(f51434,plain,(
    ! [X0] :
      ( sK5(k1_tarski(X0),sK1) = X0
      | r1_subset_1(k1_tarski(X0),sK1) ) ),
    inference(resolution,[],[f5587,f203])).

fof(f203,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f189])).

fof(f189,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f115])).

fof(f115,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK6(X0,X1) != X0
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( sK6(X0,X1) = X0
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f113,f114])).

fof(f114,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK6(X0,X1) != X0
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( sK6(X0,X1) = X0
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f113,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f112])).

fof(f112,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t30_waybel_7.p',d1_tarski)).

fof(f5587,plain,(
    ! [X4] :
      ( r2_hidden(sK5(k1_tarski(X4),sK1),k1_tarski(X4))
      | r1_subset_1(k1_tarski(X4),sK1) ) ),
    inference(resolution,[],[f3082,f170])).

fof(f170,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f110])).

fof(f110,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f67,f109])).

fof(f109,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t30_waybel_7.p',t3_xboole_0)).

fof(f3082,plain,(
    ! [X10] :
      ( ~ r1_xboole_0(k1_tarski(X10),sK1)
      | r1_subset_1(k1_tarski(X10),sK1) ) ),
    inference(resolution,[],[f1162,f202])).

fof(f202,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f201])).

fof(f201,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f190])).

fof(f190,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f115])).

fof(f1162,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X4,X3)
      | r1_subset_1(X3,sK1)
      | ~ r1_xboole_0(X3,sK1) ) ),
    inference(resolution,[],[f451,f196])).

fof(f196,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t30_waybel_7.p',t7_boole)).

fof(f451,plain,(
    ! [X38] :
      ( v1_xboole_0(X38)
      | ~ r1_xboole_0(X38,sK1)
      | r1_subset_1(X38,sK1) ) ),
    inference(resolution,[],[f129,f185])).

fof(f185,plain,(
    ! [X0,X1] :
      ( r1_subset_1(X0,X1)
      | ~ r1_xboole_0(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( ( ( r1_subset_1(X0,X1)
          | ~ r1_xboole_0(X0,X1) )
        & ( r1_xboole_0(X0,X1)
          | ~ r1_subset_1(X0,X1) ) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t30_waybel_7.p',redefinition_r1_subset_1)).

fof(f28554,plain,(
    ! [X15] :
      ( m1_subset_1(sK5(k1_tarski(X15),sK1),sK1)
      | r1_subset_1(k1_tarski(X15),sK1) ) ),
    inference(resolution,[],[f5588,f176])).

fof(f176,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t30_waybel_7.p',t1_subset)).

fof(f5588,plain,(
    ! [X5] :
      ( r2_hidden(sK5(k1_tarski(X5),sK1),sK1)
      | r1_subset_1(k1_tarski(X5),sK1) ) ),
    inference(resolution,[],[f3082,f171])).

fof(f171,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f110])).

fof(f54361,plain,
    ( r1_xboole_0(k1_tarski(k3_yellow_0(sK0)),sK3(sK0,k1_tarski(k3_yellow_0(sK0)),sK1))
    | ~ r1_subset_1(k1_tarski(k3_yellow_0(sK0)),sK3(sK0,k1_tarski(k3_yellow_0(sK0)),sK1)) ),
    inference(resolution,[],[f52223,f3779])).

fof(f3779,plain,(
    ! [X37] :
      ( v1_xboole_0(X37)
      | r1_xboole_0(k1_tarski(k3_yellow_0(sK0)),X37)
      | ~ r1_subset_1(k1_tarski(k3_yellow_0(sK0)),X37) ) ),
    inference(forward_demodulation,[],[f3657,f3623])).

fof(f3657,plain,(
    ! [X37] :
      ( r1_xboole_0(k1_tarski(k3_yellow_0(sK0)),X37)
      | ~ r1_subset_1(k5_waybel_0(sK0,k3_yellow_0(sK0)),X37)
      | v1_xboole_0(X37) ) ),
    inference(backward_demodulation,[],[f3623,f1484])).

fof(f1484,plain,(
    ! [X37] :
      ( r1_xboole_0(k5_waybel_0(sK0,k3_yellow_0(sK0)),X37)
      | ~ r1_subset_1(k5_waybel_0(sK0,k3_yellow_0(sK0)),X37)
      | v1_xboole_0(X37) ) ),
    inference(resolution,[],[f824,f184])).

fof(f184,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f111])).

fof(f52223,plain,(
    ~ v1_xboole_0(sK3(sK0,k1_tarski(k3_yellow_0(sK0)),sK1)) ),
    inference(subsumption_resolution,[],[f52097,f1233])).

fof(f52097,plain,
    ( m1_subset_1(k3_yellow_0(sK0),sK1)
    | ~ v1_xboole_0(sK3(sK0,k1_tarski(k3_yellow_0(sK0)),sK1)) ),
    inference(resolution,[],[f51942,f3793])).

fof(f3793,plain,
    ( ~ r1_subset_1(k1_tarski(k3_yellow_0(sK0)),sK1)
    | ~ v1_xboole_0(sK3(sK0,k1_tarski(k3_yellow_0(sK0)),sK1)) ),
    inference(forward_demodulation,[],[f3672,f3623])).

fof(f3672,plain,
    ( ~ v1_xboole_0(sK3(sK0,k1_tarski(k3_yellow_0(sK0)),sK1))
    | ~ r1_subset_1(k5_waybel_0(sK0,k3_yellow_0(sK0)),sK1) ),
    inference(backward_demodulation,[],[f3623,f1965])).

fof(f1965,plain,
    ( ~ r1_subset_1(k5_waybel_0(sK0,k3_yellow_0(sK0)),sK1)
    | ~ v1_xboole_0(sK3(sK0,k5_waybel_0(sK0,k3_yellow_0(sK0)),sK1)) ),
    inference(subsumption_resolution,[],[f1964,f824])).

fof(f1964,plain,
    ( ~ r1_subset_1(k5_waybel_0(sK0,k3_yellow_0(sK0)),sK1)
    | ~ v1_xboole_0(sK3(sK0,k5_waybel_0(sK0,k3_yellow_0(sK0)),sK1))
    | v1_xboole_0(k5_waybel_0(sK0,k3_yellow_0(sK0))) ),
    inference(subsumption_resolution,[],[f1963,f827])).

fof(f1963,plain,
    ( ~ r1_subset_1(k5_waybel_0(sK0,k3_yellow_0(sK0)),sK1)
    | ~ v1_xboole_0(sK3(sK0,k5_waybel_0(sK0,k3_yellow_0(sK0)),sK1))
    | ~ v1_waybel_0(k5_waybel_0(sK0,k3_yellow_0(sK0)),sK0)
    | v1_xboole_0(k5_waybel_0(sK0,k3_yellow_0(sK0))) ),
    inference(subsumption_resolution,[],[f1942,f821])).

fof(f1942,plain,
    ( ~ r1_subset_1(k5_waybel_0(sK0,k3_yellow_0(sK0)),sK1)
    | ~ m1_subset_1(k5_waybel_0(sK0,k3_yellow_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_xboole_0(sK3(sK0,k5_waybel_0(sK0,k3_yellow_0(sK0)),sK1))
    | ~ v1_waybel_0(k5_waybel_0(sK0,k3_yellow_0(sK0)),sK0)
    | v1_xboole_0(k5_waybel_0(sK0,k3_yellow_0(sK0))) ),
    inference(resolution,[],[f830,f556])).

fof(f556,plain,(
    ! [X0] :
      ( ~ v12_waybel_0(X0,sK0)
      | ~ r1_subset_1(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v1_xboole_0(sK3(sK0,X0,sK1))
      | ~ v1_waybel_0(X0,sK0)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f555,f122])).

fof(f555,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK3(sK0,X0,sK1))
      | ~ r1_subset_1(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X0,sK0)
      | ~ v1_waybel_0(X0,sK0)
      | v1_xboole_0(X0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f554,f123])).

fof(f554,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK3(sK0,X0,sK1))
      | ~ r1_subset_1(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X0,sK0)
      | ~ v1_waybel_0(X0,sK0)
      | v1_xboole_0(X0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f553,f124])).

fof(f553,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK3(sK0,X0,sK1))
      | ~ r1_subset_1(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X0,sK0)
      | ~ v1_waybel_0(X0,sK0)
      | v1_xboole_0(X0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f552,f479])).

fof(f552,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK3(sK0,X0,sK1))
      | ~ r1_subset_1(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X0,sK0)
      | ~ v1_waybel_0(X0,sK0)
      | v1_xboole_0(X0)
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f551,f126])).

fof(f551,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK3(sK0,X0,sK1))
      | ~ r1_subset_1(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X0,sK0)
      | ~ v1_waybel_0(X0,sK0)
      | v1_xboole_0(X0)
      | ~ v1_lattice3(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f550,f127])).

fof(f550,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK3(sK0,X0,sK1))
      | ~ r1_subset_1(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X0,sK0)
      | ~ v1_waybel_0(X0,sK0)
      | v1_xboole_0(X0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f549,f128])).

fof(f549,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK3(sK0,X0,sK1))
      | ~ r1_subset_1(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X0,sK0)
      | ~ v1_waybel_0(X0,sK0)
      | v1_xboole_0(X0)
      | ~ l1_orders_2(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f548,f129])).

fof(f548,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK3(sK0,X0,sK1))
      | ~ r1_subset_1(X0,sK1)
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X0,sK0)
      | ~ v1_waybel_0(X0,sK0)
      | v1_xboole_0(X0)
      | ~ l1_orders_2(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f547,f132])).

fof(f547,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK3(sK0,X0,sK1))
      | ~ r1_subset_1(X0,sK1)
      | ~ v13_waybel_0(sK1,sK0)
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X0,sK0)
      | ~ v1_waybel_0(X0,sK0)
      | v1_xboole_0(X0)
      | ~ l1_orders_2(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f528,f133])).

fof(f528,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK3(sK0,X0,sK1))
      | ~ r1_subset_1(X0,sK1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(sK1,sK0)
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X0,sK0)
      | ~ v1_waybel_0(X0,sK0)
      | v1_xboole_0(X0)
      | ~ l1_orders_2(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(resolution,[],[f131,f159])).

fof(f159,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(sK3(X0,X1,X2))
      | ~ r1_subset_1(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X2,X0)
      | ~ v2_waybel_0(X2,X0)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f104])).

fof(f56724,plain,(
    ~ r1_xboole_0(k1_tarski(k3_yellow_0(sK0)),sK3(sK0,k1_tarski(k3_yellow_0(sK0)),sK1)) ),
    inference(resolution,[],[f55208,f12589])).

fof(f12589,plain,(
    ! [X0] :
      ( ~ r2_hidden(k3_yellow_0(sK0),X0)
      | ~ r1_xboole_0(k1_tarski(k3_yellow_0(sK0)),X0) ) ),
    inference(forward_demodulation,[],[f12536,f12535])).

fof(f12535,plain,(
    k3_yellow_0(sK0) = sK4(k1_tarski(k3_yellow_0(sK0))) ),
    inference(resolution,[],[f12519,f203])).

fof(f12519,plain,(
    r2_hidden(sK4(k1_tarski(k3_yellow_0(sK0))),k1_tarski(k3_yellow_0(sK0))) ),
    inference(resolution,[],[f3775,f169])).

fof(f3775,plain,(
    ! [X33] :
      ( ~ m1_subset_1(X33,k1_tarski(k3_yellow_0(sK0)))
      | r2_hidden(X33,k1_tarski(k3_yellow_0(sK0))) ) ),
    inference(forward_demodulation,[],[f3653,f3623])).

fof(f3653,plain,(
    ! [X33] :
      ( r2_hidden(X33,k1_tarski(k3_yellow_0(sK0)))
      | ~ m1_subset_1(X33,k5_waybel_0(sK0,k3_yellow_0(sK0))) ) ),
    inference(backward_demodulation,[],[f3623,f1480])).

fof(f1480,plain,(
    ! [X33] :
      ( r2_hidden(X33,k5_waybel_0(sK0,k3_yellow_0(sK0)))
      | ~ m1_subset_1(X33,k5_waybel_0(sK0,k3_yellow_0(sK0))) ) ),
    inference(resolution,[],[f824,f177])).

fof(f12536,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(k1_tarski(k3_yellow_0(sK0)),X0)
      | ~ r2_hidden(sK4(k1_tarski(k3_yellow_0(sK0))),X0) ) ),
    inference(resolution,[],[f12519,f172])).

fof(f172,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f110])).

fof(f55208,plain,(
    r2_hidden(k3_yellow_0(sK0),sK3(sK0,k1_tarski(k3_yellow_0(sK0)),sK1)) ),
    inference(subsumption_resolution,[],[f55207,f388])).

fof(f55207,plain,
    ( r2_hidden(k3_yellow_0(sK0),sK3(sK0,k1_tarski(k3_yellow_0(sK0)),sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f55206,f122])).

fof(f55206,plain,
    ( r2_hidden(k3_yellow_0(sK0),sK3(sK0,k1_tarski(k3_yellow_0(sK0)),sK1))
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f55205,f123])).

fof(f55205,plain,
    ( r2_hidden(k3_yellow_0(sK0),sK3(sK0,k1_tarski(k3_yellow_0(sK0)),sK1))
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f55204,f124])).

fof(f55204,plain,
    ( r2_hidden(k3_yellow_0(sK0),sK3(sK0,k1_tarski(k3_yellow_0(sK0)),sK1))
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f55203,f751])).

fof(f55203,plain,
    ( r2_hidden(k3_yellow_0(sK0),sK3(sK0,k1_tarski(k3_yellow_0(sK0)),sK1))
    | ~ v1_yellow_0(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f55202,f128])).

fof(f55202,plain,
    ( r2_hidden(k3_yellow_0(sK0),sK3(sK0,k1_tarski(k3_yellow_0(sK0)),sK1))
    | ~ l1_orders_2(sK0)
    | ~ v1_yellow_0(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f55201,f52223])).

fof(f55201,plain,
    ( r2_hidden(k3_yellow_0(sK0),sK3(sK0,k1_tarski(k3_yellow_0(sK0)),sK1))
    | v1_xboole_0(sK3(sK0,k1_tarski(k3_yellow_0(sK0)),sK1))
    | ~ l1_orders_2(sK0)
    | ~ v1_yellow_0(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f55200,f52225])).

fof(f52225,plain,(
    v13_waybel_0(sK3(sK0,k1_tarski(k3_yellow_0(sK0)),sK1),sK0) ),
    inference(subsumption_resolution,[],[f52099,f1233])).

fof(f52099,plain,
    ( m1_subset_1(k3_yellow_0(sK0),sK1)
    | v13_waybel_0(sK3(sK0,k1_tarski(k3_yellow_0(sK0)),sK1),sK0) ),
    inference(resolution,[],[f51942,f3795])).

fof(f3795,plain,
    ( ~ r1_subset_1(k1_tarski(k3_yellow_0(sK0)),sK1)
    | v13_waybel_0(sK3(sK0,k1_tarski(k3_yellow_0(sK0)),sK1),sK0) ),
    inference(forward_demodulation,[],[f3674,f3623])).

fof(f3674,plain,
    ( v13_waybel_0(sK3(sK0,k1_tarski(k3_yellow_0(sK0)),sK1),sK0)
    | ~ r1_subset_1(k5_waybel_0(sK0,k3_yellow_0(sK0)),sK1) ),
    inference(backward_demodulation,[],[f3623,f1971])).

fof(f1971,plain,
    ( ~ r1_subset_1(k5_waybel_0(sK0,k3_yellow_0(sK0)),sK1)
    | v13_waybel_0(sK3(sK0,k5_waybel_0(sK0,k3_yellow_0(sK0)),sK1),sK0) ),
    inference(subsumption_resolution,[],[f1970,f824])).

fof(f1970,plain,
    ( ~ r1_subset_1(k5_waybel_0(sK0,k3_yellow_0(sK0)),sK1)
    | v13_waybel_0(sK3(sK0,k5_waybel_0(sK0,k3_yellow_0(sK0)),sK1),sK0)
    | v1_xboole_0(k5_waybel_0(sK0,k3_yellow_0(sK0))) ),
    inference(subsumption_resolution,[],[f1969,f827])).

fof(f1969,plain,
    ( ~ r1_subset_1(k5_waybel_0(sK0,k3_yellow_0(sK0)),sK1)
    | v13_waybel_0(sK3(sK0,k5_waybel_0(sK0,k3_yellow_0(sK0)),sK1),sK0)
    | ~ v1_waybel_0(k5_waybel_0(sK0,k3_yellow_0(sK0)),sK0)
    | v1_xboole_0(k5_waybel_0(sK0,k3_yellow_0(sK0))) ),
    inference(subsumption_resolution,[],[f1944,f821])).

fof(f1944,plain,
    ( ~ r1_subset_1(k5_waybel_0(sK0,k3_yellow_0(sK0)),sK1)
    | ~ m1_subset_1(k5_waybel_0(sK0,k3_yellow_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v13_waybel_0(sK3(sK0,k5_waybel_0(sK0,k3_yellow_0(sK0)),sK1),sK0)
    | ~ v1_waybel_0(k5_waybel_0(sK0,k3_yellow_0(sK0)),sK0)
    | v1_xboole_0(k5_waybel_0(sK0,k3_yellow_0(sK0))) ),
    inference(resolution,[],[f830,f576])).

fof(f576,plain,(
    ! [X2] :
      ( ~ v12_waybel_0(X2,sK0)
      | ~ r1_subset_1(X2,sK1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | v13_waybel_0(sK3(sK0,X2,sK1),sK0)
      | ~ v1_waybel_0(X2,sK0)
      | v1_xboole_0(X2) ) ),
    inference(subsumption_resolution,[],[f575,f122])).

fof(f575,plain,(
    ! [X2] :
      ( v13_waybel_0(sK3(sK0,X2,sK1),sK0)
      | ~ r1_subset_1(X2,sK1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X2,sK0)
      | ~ v1_waybel_0(X2,sK0)
      | v1_xboole_0(X2)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f574,f123])).

fof(f574,plain,(
    ! [X2] :
      ( v13_waybel_0(sK3(sK0,X2,sK1),sK0)
      | ~ r1_subset_1(X2,sK1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X2,sK0)
      | ~ v1_waybel_0(X2,sK0)
      | v1_xboole_0(X2)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f573,f124])).

fof(f573,plain,(
    ! [X2] :
      ( v13_waybel_0(sK3(sK0,X2,sK1),sK0)
      | ~ r1_subset_1(X2,sK1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X2,sK0)
      | ~ v1_waybel_0(X2,sK0)
      | v1_xboole_0(X2)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f572,f479])).

fof(f572,plain,(
    ! [X2] :
      ( v13_waybel_0(sK3(sK0,X2,sK1),sK0)
      | ~ r1_subset_1(X2,sK1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X2,sK0)
      | ~ v1_waybel_0(X2,sK0)
      | v1_xboole_0(X2)
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f571,f126])).

fof(f571,plain,(
    ! [X2] :
      ( v13_waybel_0(sK3(sK0,X2,sK1),sK0)
      | ~ r1_subset_1(X2,sK1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X2,sK0)
      | ~ v1_waybel_0(X2,sK0)
      | v1_xboole_0(X2)
      | ~ v1_lattice3(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f570,f127])).

fof(f570,plain,(
    ! [X2] :
      ( v13_waybel_0(sK3(sK0,X2,sK1),sK0)
      | ~ r1_subset_1(X2,sK1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X2,sK0)
      | ~ v1_waybel_0(X2,sK0)
      | v1_xboole_0(X2)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f569,f128])).

fof(f569,plain,(
    ! [X2] :
      ( v13_waybel_0(sK3(sK0,X2,sK1),sK0)
      | ~ r1_subset_1(X2,sK1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X2,sK0)
      | ~ v1_waybel_0(X2,sK0)
      | v1_xboole_0(X2)
      | ~ l1_orders_2(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f568,f129])).

fof(f568,plain,(
    ! [X2] :
      ( v13_waybel_0(sK3(sK0,X2,sK1),sK0)
      | ~ r1_subset_1(X2,sK1)
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X2,sK0)
      | ~ v1_waybel_0(X2,sK0)
      | v1_xboole_0(X2)
      | ~ l1_orders_2(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f567,f132])).

fof(f567,plain,(
    ! [X2] :
      ( v13_waybel_0(sK3(sK0,X2,sK1),sK0)
      | ~ r1_subset_1(X2,sK1)
      | ~ v13_waybel_0(sK1,sK0)
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X2,sK0)
      | ~ v1_waybel_0(X2,sK0)
      | v1_xboole_0(X2)
      | ~ l1_orders_2(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f530,f133])).

fof(f530,plain,(
    ! [X2] :
      ( v13_waybel_0(sK3(sK0,X2,sK1),sK0)
      | ~ r1_subset_1(X2,sK1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(sK1,sK0)
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X2,sK0)
      | ~ v1_waybel_0(X2,sK0)
      | v1_xboole_0(X2)
      | ~ l1_orders_2(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(resolution,[],[f131,f161])).

fof(f161,plain,(
    ! [X2,X0,X1] :
      ( v13_waybel_0(sK3(X0,X1,X2),X0)
      | ~ r1_subset_1(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X2,X0)
      | ~ v2_waybel_0(X2,X0)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f104])).

fof(f55200,plain,
    ( r2_hidden(k3_yellow_0(sK0),sK3(sK0,k1_tarski(k3_yellow_0(sK0)),sK1))
    | ~ v13_waybel_0(sK3(sK0,k1_tarski(k3_yellow_0(sK0)),sK1),sK0)
    | v1_xboole_0(sK3(sK0,k1_tarski(k3_yellow_0(sK0)),sK1))
    | ~ l1_orders_2(sK0)
    | ~ v1_yellow_0(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f55199,f52226])).

fof(f52226,plain,(
    m1_subset_1(sK3(sK0,k1_tarski(k3_yellow_0(sK0)),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f52100,f1233])).

fof(f52100,plain,
    ( m1_subset_1(k3_yellow_0(sK0),sK1)
    | m1_subset_1(sK3(sK0,k1_tarski(k3_yellow_0(sK0)),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f51942,f3796])).

fof(f3796,plain,
    ( ~ r1_subset_1(k1_tarski(k3_yellow_0(sK0)),sK1)
    | m1_subset_1(sK3(sK0,k1_tarski(k3_yellow_0(sK0)),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f3675,f3623])).

fof(f3675,plain,
    ( m1_subset_1(sK3(sK0,k1_tarski(k3_yellow_0(sK0)),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_subset_1(k5_waybel_0(sK0,k3_yellow_0(sK0)),sK1) ),
    inference(backward_demodulation,[],[f3623,f1974])).

fof(f1974,plain,
    ( ~ r1_subset_1(k5_waybel_0(sK0,k3_yellow_0(sK0)),sK1)
    | m1_subset_1(sK3(sK0,k5_waybel_0(sK0,k3_yellow_0(sK0)),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f1973,f824])).

fof(f1973,plain,
    ( ~ r1_subset_1(k5_waybel_0(sK0,k3_yellow_0(sK0)),sK1)
    | m1_subset_1(sK3(sK0,k5_waybel_0(sK0,k3_yellow_0(sK0)),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(k5_waybel_0(sK0,k3_yellow_0(sK0))) ),
    inference(subsumption_resolution,[],[f1972,f827])).

fof(f1972,plain,
    ( ~ r1_subset_1(k5_waybel_0(sK0,k3_yellow_0(sK0)),sK1)
    | m1_subset_1(sK3(sK0,k5_waybel_0(sK0,k3_yellow_0(sK0)),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_waybel_0(k5_waybel_0(sK0,k3_yellow_0(sK0)),sK0)
    | v1_xboole_0(k5_waybel_0(sK0,k3_yellow_0(sK0))) ),
    inference(subsumption_resolution,[],[f1945,f821])).

fof(f1945,plain,
    ( ~ r1_subset_1(k5_waybel_0(sK0,k3_yellow_0(sK0)),sK1)
    | ~ m1_subset_1(k5_waybel_0(sK0,k3_yellow_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK3(sK0,k5_waybel_0(sK0,k3_yellow_0(sK0)),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_waybel_0(k5_waybel_0(sK0,k3_yellow_0(sK0)),sK0)
    | v1_xboole_0(k5_waybel_0(sK0,k3_yellow_0(sK0))) ),
    inference(resolution,[],[f830,f586])).

fof(f586,plain,(
    ! [X3] :
      ( ~ v12_waybel_0(X3,sK0)
      | ~ r1_subset_1(X3,sK1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(sK3(sK0,X3,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v1_waybel_0(X3,sK0)
      | v1_xboole_0(X3) ) ),
    inference(subsumption_resolution,[],[f585,f122])).

fof(f585,plain,(
    ! [X3] :
      ( m1_subset_1(sK3(sK0,X3,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(X3,sK1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X3,sK0)
      | ~ v1_waybel_0(X3,sK0)
      | v1_xboole_0(X3)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f584,f123])).

fof(f584,plain,(
    ! [X3] :
      ( m1_subset_1(sK3(sK0,X3,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(X3,sK1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X3,sK0)
      | ~ v1_waybel_0(X3,sK0)
      | v1_xboole_0(X3)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f583,f124])).

fof(f583,plain,(
    ! [X3] :
      ( m1_subset_1(sK3(sK0,X3,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(X3,sK1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X3,sK0)
      | ~ v1_waybel_0(X3,sK0)
      | v1_xboole_0(X3)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f582,f479])).

fof(f582,plain,(
    ! [X3] :
      ( m1_subset_1(sK3(sK0,X3,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(X3,sK1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X3,sK0)
      | ~ v1_waybel_0(X3,sK0)
      | v1_xboole_0(X3)
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f581,f126])).

fof(f581,plain,(
    ! [X3] :
      ( m1_subset_1(sK3(sK0,X3,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(X3,sK1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X3,sK0)
      | ~ v1_waybel_0(X3,sK0)
      | v1_xboole_0(X3)
      | ~ v1_lattice3(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f580,f127])).

fof(f580,plain,(
    ! [X3] :
      ( m1_subset_1(sK3(sK0,X3,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(X3,sK1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X3,sK0)
      | ~ v1_waybel_0(X3,sK0)
      | v1_xboole_0(X3)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f579,f128])).

fof(f579,plain,(
    ! [X3] :
      ( m1_subset_1(sK3(sK0,X3,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(X3,sK1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X3,sK0)
      | ~ v1_waybel_0(X3,sK0)
      | v1_xboole_0(X3)
      | ~ l1_orders_2(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f578,f129])).

fof(f578,plain,(
    ! [X3] :
      ( m1_subset_1(sK3(sK0,X3,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(X3,sK1)
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X3,sK0)
      | ~ v1_waybel_0(X3,sK0)
      | v1_xboole_0(X3)
      | ~ l1_orders_2(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f577,f132])).

fof(f577,plain,(
    ! [X3] :
      ( m1_subset_1(sK3(sK0,X3,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(X3,sK1)
      | ~ v13_waybel_0(sK1,sK0)
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X3,sK0)
      | ~ v1_waybel_0(X3,sK0)
      | v1_xboole_0(X3)
      | ~ l1_orders_2(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f531,f133])).

fof(f531,plain,(
    ! [X3] :
      ( m1_subset_1(sK3(sK0,X3,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(X3,sK1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(sK1,sK0)
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X3,sK0)
      | ~ v1_waybel_0(X3,sK0)
      | v1_xboole_0(X3)
      | ~ l1_orders_2(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(resolution,[],[f131,f162])).

fof(f162,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_subset_1(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X2,X0)
      | ~ v2_waybel_0(X2,X0)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f104])).

fof(f55199,plain,
    ( r2_hidden(k3_yellow_0(sK0),sK3(sK0,k1_tarski(k3_yellow_0(sK0)),sK1))
    | ~ m1_subset_1(sK3(sK0,k1_tarski(k3_yellow_0(sK0)),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v13_waybel_0(sK3(sK0,k1_tarski(k3_yellow_0(sK0)),sK1),sK0)
    | v1_xboole_0(sK3(sK0,k1_tarski(k3_yellow_0(sK0)),sK1))
    | ~ l1_orders_2(sK0)
    | ~ v1_yellow_0(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f55185,f53138])).

fof(f53138,plain,(
    ~ v1_subset_1(sK3(sK0,k1_tarski(k3_yellow_0(sK0)),sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f53137,f3630])).

fof(f3630,plain,(
    ~ v1_xboole_0(k1_tarski(k3_yellow_0(sK0))) ),
    inference(backward_demodulation,[],[f3623,f824])).

fof(f53137,plain,
    ( ~ v1_subset_1(sK3(sK0,k1_tarski(k3_yellow_0(sK0)),sK1),u1_struct_0(sK0))
    | v1_xboole_0(k1_tarski(k3_yellow_0(sK0))) ),
    inference(subsumption_resolution,[],[f53136,f3631])).

fof(f3631,plain,(
    v1_waybel_0(k1_tarski(k3_yellow_0(sK0)),sK0) ),
    inference(backward_demodulation,[],[f3623,f827])).

fof(f53136,plain,
    ( ~ v1_subset_1(sK3(sK0,k1_tarski(k3_yellow_0(sK0)),sK1),u1_struct_0(sK0))
    | ~ v1_waybel_0(k1_tarski(k3_yellow_0(sK0)),sK0)
    | v1_xboole_0(k1_tarski(k3_yellow_0(sK0))) ),
    inference(subsumption_resolution,[],[f53135,f3632])).

fof(f3632,plain,(
    v12_waybel_0(k1_tarski(k3_yellow_0(sK0)),sK0) ),
    inference(backward_demodulation,[],[f3623,f830])).

fof(f53135,plain,
    ( ~ v1_subset_1(sK3(sK0,k1_tarski(k3_yellow_0(sK0)),sK1),u1_struct_0(sK0))
    | ~ v12_waybel_0(k1_tarski(k3_yellow_0(sK0)),sK0)
    | ~ v1_waybel_0(k1_tarski(k3_yellow_0(sK0)),sK0)
    | v1_xboole_0(k1_tarski(k3_yellow_0(sK0))) ),
    inference(subsumption_resolution,[],[f53134,f3629])).

fof(f3629,plain,(
    m1_subset_1(k1_tarski(k3_yellow_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f3623,f821])).

fof(f53134,plain,
    ( ~ v1_subset_1(sK3(sK0,k1_tarski(k3_yellow_0(sK0)),sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k1_tarski(k3_yellow_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v12_waybel_0(k1_tarski(k3_yellow_0(sK0)),sK0)
    | ~ v1_waybel_0(k1_tarski(k3_yellow_0(sK0)),sK0)
    | v1_xboole_0(k1_tarski(k3_yellow_0(sK0))) ),
    inference(subsumption_resolution,[],[f53133,f129])).

fof(f53133,plain,
    ( ~ v1_subset_1(sK3(sK0,k1_tarski(k3_yellow_0(sK0)),sK1),u1_struct_0(sK0))
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(k1_tarski(k3_yellow_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v12_waybel_0(k1_tarski(k3_yellow_0(sK0)),sK0)
    | ~ v1_waybel_0(k1_tarski(k3_yellow_0(sK0)),sK0)
    | v1_xboole_0(k1_tarski(k3_yellow_0(sK0))) ),
    inference(subsumption_resolution,[],[f53132,f131])).

fof(f53132,plain,
    ( ~ v1_subset_1(sK3(sK0,k1_tarski(k3_yellow_0(sK0)),sK1),u1_struct_0(sK0))
    | ~ v2_waybel_0(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(k1_tarski(k3_yellow_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v12_waybel_0(k1_tarski(k3_yellow_0(sK0)),sK0)
    | ~ v1_waybel_0(k1_tarski(k3_yellow_0(sK0)),sK0)
    | v1_xboole_0(k1_tarski(k3_yellow_0(sK0))) ),
    inference(subsumption_resolution,[],[f53131,f132])).

fof(f53131,plain,
    ( ~ v1_subset_1(sK3(sK0,k1_tarski(k3_yellow_0(sK0)),sK1),u1_struct_0(sK0))
    | ~ v13_waybel_0(sK1,sK0)
    | ~ v2_waybel_0(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(k1_tarski(k3_yellow_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v12_waybel_0(k1_tarski(k3_yellow_0(sK0)),sK0)
    | ~ v1_waybel_0(k1_tarski(k3_yellow_0(sK0)),sK0)
    | v1_xboole_0(k1_tarski(k3_yellow_0(sK0))) ),
    inference(subsumption_resolution,[],[f53130,f133])).

fof(f53130,plain,
    ( ~ v1_subset_1(sK3(sK0,k1_tarski(k3_yellow_0(sK0)),sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,sK0)
    | ~ v2_waybel_0(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(k1_tarski(k3_yellow_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v12_waybel_0(k1_tarski(k3_yellow_0(sK0)),sK0)
    | ~ v1_waybel_0(k1_tarski(k3_yellow_0(sK0)),sK0)
    | v1_xboole_0(k1_tarski(k3_yellow_0(sK0))) ),
    inference(subsumption_resolution,[],[f53039,f52228])).

fof(f52228,plain,(
    r1_tarski(sK1,sK3(sK0,k1_tarski(k3_yellow_0(sK0)),sK1)) ),
    inference(subsumption_resolution,[],[f52102,f1233])).

fof(f52102,plain,
    ( m1_subset_1(k3_yellow_0(sK0),sK1)
    | r1_tarski(sK1,sK3(sK0,k1_tarski(k3_yellow_0(sK0)),sK1)) ),
    inference(resolution,[],[f51942,f3798])).

fof(f3798,plain,
    ( ~ r1_subset_1(k1_tarski(k3_yellow_0(sK0)),sK1)
    | r1_tarski(sK1,sK3(sK0,k1_tarski(k3_yellow_0(sK0)),sK1)) ),
    inference(forward_demodulation,[],[f3677,f3623])).

fof(f3677,plain,
    ( r1_tarski(sK1,sK3(sK0,k1_tarski(k3_yellow_0(sK0)),sK1))
    | ~ r1_subset_1(k5_waybel_0(sK0,k3_yellow_0(sK0)),sK1) ),
    inference(backward_demodulation,[],[f3623,f1980])).

fof(f1980,plain,
    ( ~ r1_subset_1(k5_waybel_0(sK0,k3_yellow_0(sK0)),sK1)
    | r1_tarski(sK1,sK3(sK0,k5_waybel_0(sK0,k3_yellow_0(sK0)),sK1)) ),
    inference(subsumption_resolution,[],[f1979,f824])).

fof(f1979,plain,
    ( ~ r1_subset_1(k5_waybel_0(sK0,k3_yellow_0(sK0)),sK1)
    | r1_tarski(sK1,sK3(sK0,k5_waybel_0(sK0,k3_yellow_0(sK0)),sK1))
    | v1_xboole_0(k5_waybel_0(sK0,k3_yellow_0(sK0))) ),
    inference(subsumption_resolution,[],[f1978,f827])).

fof(f1978,plain,
    ( ~ r1_subset_1(k5_waybel_0(sK0,k3_yellow_0(sK0)),sK1)
    | r1_tarski(sK1,sK3(sK0,k5_waybel_0(sK0,k3_yellow_0(sK0)),sK1))
    | ~ v1_waybel_0(k5_waybel_0(sK0,k3_yellow_0(sK0)),sK0)
    | v1_xboole_0(k5_waybel_0(sK0,k3_yellow_0(sK0))) ),
    inference(subsumption_resolution,[],[f1947,f821])).

fof(f1947,plain,
    ( ~ r1_subset_1(k5_waybel_0(sK0,k3_yellow_0(sK0)),sK1)
    | ~ m1_subset_1(k5_waybel_0(sK0,k3_yellow_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,sK3(sK0,k5_waybel_0(sK0,k3_yellow_0(sK0)),sK1))
    | ~ v1_waybel_0(k5_waybel_0(sK0,k3_yellow_0(sK0)),sK0)
    | v1_xboole_0(k5_waybel_0(sK0,k3_yellow_0(sK0))) ),
    inference(resolution,[],[f830,f606])).

fof(f606,plain,(
    ! [X5] :
      ( ~ v12_waybel_0(X5,sK0)
      | ~ r1_subset_1(X5,sK1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(sK1,sK3(sK0,X5,sK1))
      | ~ v1_waybel_0(X5,sK0)
      | v1_xboole_0(X5) ) ),
    inference(subsumption_resolution,[],[f605,f122])).

fof(f605,plain,(
    ! [X5] :
      ( r1_tarski(sK1,sK3(sK0,X5,sK1))
      | ~ r1_subset_1(X5,sK1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X5,sK0)
      | ~ v1_waybel_0(X5,sK0)
      | v1_xboole_0(X5)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f604,f123])).

fof(f604,plain,(
    ! [X5] :
      ( r1_tarski(sK1,sK3(sK0,X5,sK1))
      | ~ r1_subset_1(X5,sK1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X5,sK0)
      | ~ v1_waybel_0(X5,sK0)
      | v1_xboole_0(X5)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f603,f124])).

fof(f603,plain,(
    ! [X5] :
      ( r1_tarski(sK1,sK3(sK0,X5,sK1))
      | ~ r1_subset_1(X5,sK1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X5,sK0)
      | ~ v1_waybel_0(X5,sK0)
      | v1_xboole_0(X5)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f602,f479])).

fof(f602,plain,(
    ! [X5] :
      ( r1_tarski(sK1,sK3(sK0,X5,sK1))
      | ~ r1_subset_1(X5,sK1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X5,sK0)
      | ~ v1_waybel_0(X5,sK0)
      | v1_xboole_0(X5)
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f601,f126])).

fof(f601,plain,(
    ! [X5] :
      ( r1_tarski(sK1,sK3(sK0,X5,sK1))
      | ~ r1_subset_1(X5,sK1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X5,sK0)
      | ~ v1_waybel_0(X5,sK0)
      | v1_xboole_0(X5)
      | ~ v1_lattice3(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f600,f127])).

fof(f600,plain,(
    ! [X5] :
      ( r1_tarski(sK1,sK3(sK0,X5,sK1))
      | ~ r1_subset_1(X5,sK1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X5,sK0)
      | ~ v1_waybel_0(X5,sK0)
      | v1_xboole_0(X5)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f599,f128])).

fof(f599,plain,(
    ! [X5] :
      ( r1_tarski(sK1,sK3(sK0,X5,sK1))
      | ~ r1_subset_1(X5,sK1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X5,sK0)
      | ~ v1_waybel_0(X5,sK0)
      | v1_xboole_0(X5)
      | ~ l1_orders_2(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f598,f129])).

fof(f598,plain,(
    ! [X5] :
      ( r1_tarski(sK1,sK3(sK0,X5,sK1))
      | ~ r1_subset_1(X5,sK1)
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X5,sK0)
      | ~ v1_waybel_0(X5,sK0)
      | v1_xboole_0(X5)
      | ~ l1_orders_2(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f597,f132])).

fof(f597,plain,(
    ! [X5] :
      ( r1_tarski(sK1,sK3(sK0,X5,sK1))
      | ~ r1_subset_1(X5,sK1)
      | ~ v13_waybel_0(sK1,sK0)
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X5,sK0)
      | ~ v1_waybel_0(X5,sK0)
      | v1_xboole_0(X5)
      | ~ l1_orders_2(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f533,f133])).

fof(f533,plain,(
    ! [X5] :
      ( r1_tarski(sK1,sK3(sK0,X5,sK1))
      | ~ r1_subset_1(X5,sK1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(sK1,sK0)
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X5,sK0)
      | ~ v1_waybel_0(X5,sK0)
      | v1_xboole_0(X5)
      | ~ l1_orders_2(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(resolution,[],[f131,f164])).

fof(f164,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,sK3(X0,X1,X2))
      | ~ r1_subset_1(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X2,X0)
      | ~ v2_waybel_0(X2,X0)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f104])).

fof(f53039,plain,
    ( ~ v1_subset_1(sK3(sK0,k1_tarski(k3_yellow_0(sK0)),sK1),u1_struct_0(sK0))
    | ~ r1_tarski(sK1,sK3(sK0,k1_tarski(k3_yellow_0(sK0)),sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,sK0)
    | ~ v2_waybel_0(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(k1_tarski(k3_yellow_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v12_waybel_0(k1_tarski(k3_yellow_0(sK0)),sK0)
    | ~ v1_waybel_0(k1_tarski(k3_yellow_0(sK0)),sK0)
    | v1_xboole_0(k1_tarski(k3_yellow_0(sK0))) ),
    inference(resolution,[],[f52715,f1519])).

fof(f1519,plain,(
    ! [X0,X1] :
      ( ~ r1_subset_1(X0,X1)
      | ~ v1_subset_1(sK3(sK0,X0,X1),u1_struct_0(sK0))
      | ~ r1_tarski(sK1,sK3(sK0,X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X1,sK0)
      | ~ v2_waybel_0(X1,sK0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X0,sK0)
      | ~ v1_waybel_0(X0,sK0)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f1518,f775])).

fof(f775,plain,(
    ! [X2,X3] :
      ( v2_waybel_0(sK3(sK0,X2,X3),sK0)
      | ~ r1_subset_1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X3,sK0)
      | ~ v2_waybel_0(X3,sK0)
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X2,sK0)
      | ~ v1_waybel_0(X2,sK0)
      | v1_xboole_0(X2) ) ),
    inference(subsumption_resolution,[],[f774,f122])).

fof(f774,plain,(
    ! [X2,X3] :
      ( v2_waybel_0(sK3(sK0,X2,X3),sK0)
      | ~ r1_subset_1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X3,sK0)
      | ~ v2_waybel_0(X3,sK0)
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X2,sK0)
      | ~ v1_waybel_0(X2,sK0)
      | v1_xboole_0(X2)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f773,f123])).

fof(f773,plain,(
    ! [X2,X3] :
      ( v2_waybel_0(sK3(sK0,X2,X3),sK0)
      | ~ r1_subset_1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X3,sK0)
      | ~ v2_waybel_0(X3,sK0)
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X2,sK0)
      | ~ v1_waybel_0(X2,sK0)
      | v1_xboole_0(X2)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f772,f124])).

fof(f772,plain,(
    ! [X2,X3] :
      ( v2_waybel_0(sK3(sK0,X2,X3),sK0)
      | ~ r1_subset_1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X3,sK0)
      | ~ v2_waybel_0(X3,sK0)
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X2,sK0)
      | ~ v1_waybel_0(X2,sK0)
      | v1_xboole_0(X2)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f771,f126])).

fof(f771,plain,(
    ! [X2,X3] :
      ( v2_waybel_0(sK3(sK0,X2,X3),sK0)
      | ~ r1_subset_1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X3,sK0)
      | ~ v2_waybel_0(X3,sK0)
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X2,sK0)
      | ~ v1_waybel_0(X2,sK0)
      | v1_xboole_0(X2)
      | ~ v1_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f770,f127])).

fof(f770,plain,(
    ! [X2,X3] :
      ( v2_waybel_0(sK3(sK0,X2,X3),sK0)
      | ~ r1_subset_1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X3,sK0)
      | ~ v2_waybel_0(X3,sK0)
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X2,sK0)
      | ~ v1_waybel_0(X2,sK0)
      | v1_xboole_0(X2)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f758,f128])).

fof(f758,plain,(
    ! [X2,X3] :
      ( v2_waybel_0(sK3(sK0,X2,X3),sK0)
      | ~ r1_subset_1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X3,sK0)
      | ~ v2_waybel_0(X3,sK0)
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X2,sK0)
      | ~ v1_waybel_0(X2,sK0)
      | v1_xboole_0(X2)
      | ~ l1_orders_2(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(resolution,[],[f479,f160])).

fof(f160,plain,(
    ! [X2,X0,X1] :
      ( v2_waybel_0(sK3(X0,X1,X2),X0)
      | ~ r1_subset_1(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X2,X0)
      | ~ v2_waybel_0(X2,X0)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f104])).

fof(f1518,plain,(
    ! [X0,X1] :
      ( ~ v2_waybel_0(sK3(sK0,X0,X1),sK0)
      | ~ r1_tarski(sK1,sK3(sK0,X0,X1))
      | ~ v1_subset_1(sK3(sK0,X0,X1),u1_struct_0(sK0))
      | ~ r1_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X1,sK0)
      | ~ v2_waybel_0(X1,sK0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X0,sK0)
      | ~ v1_waybel_0(X0,sK0)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f1517,f781])).

fof(f781,plain,(
    ! [X4,X5] :
      ( v13_waybel_0(sK3(sK0,X4,X5),sK0)
      | ~ r1_subset_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X5,sK0)
      | ~ v2_waybel_0(X5,sK0)
      | v1_xboole_0(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X4,sK0)
      | ~ v1_waybel_0(X4,sK0)
      | v1_xboole_0(X4) ) ),
    inference(subsumption_resolution,[],[f780,f122])).

fof(f780,plain,(
    ! [X4,X5] :
      ( v13_waybel_0(sK3(sK0,X4,X5),sK0)
      | ~ r1_subset_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X5,sK0)
      | ~ v2_waybel_0(X5,sK0)
      | v1_xboole_0(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X4,sK0)
      | ~ v1_waybel_0(X4,sK0)
      | v1_xboole_0(X4)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f779,f123])).

fof(f779,plain,(
    ! [X4,X5] :
      ( v13_waybel_0(sK3(sK0,X4,X5),sK0)
      | ~ r1_subset_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X5,sK0)
      | ~ v2_waybel_0(X5,sK0)
      | v1_xboole_0(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X4,sK0)
      | ~ v1_waybel_0(X4,sK0)
      | v1_xboole_0(X4)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f778,f124])).

fof(f778,plain,(
    ! [X4,X5] :
      ( v13_waybel_0(sK3(sK0,X4,X5),sK0)
      | ~ r1_subset_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X5,sK0)
      | ~ v2_waybel_0(X5,sK0)
      | v1_xboole_0(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X4,sK0)
      | ~ v1_waybel_0(X4,sK0)
      | v1_xboole_0(X4)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f777,f126])).

fof(f777,plain,(
    ! [X4,X5] :
      ( v13_waybel_0(sK3(sK0,X4,X5),sK0)
      | ~ r1_subset_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X5,sK0)
      | ~ v2_waybel_0(X5,sK0)
      | v1_xboole_0(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X4,sK0)
      | ~ v1_waybel_0(X4,sK0)
      | v1_xboole_0(X4)
      | ~ v1_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f776,f127])).

fof(f776,plain,(
    ! [X4,X5] :
      ( v13_waybel_0(sK3(sK0,X4,X5),sK0)
      | ~ r1_subset_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X5,sK0)
      | ~ v2_waybel_0(X5,sK0)
      | v1_xboole_0(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X4,sK0)
      | ~ v1_waybel_0(X4,sK0)
      | v1_xboole_0(X4)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f759,f128])).

fof(f759,plain,(
    ! [X4,X5] :
      ( v13_waybel_0(sK3(sK0,X4,X5),sK0)
      | ~ r1_subset_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X5,sK0)
      | ~ v2_waybel_0(X5,sK0)
      | v1_xboole_0(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X4,sK0)
      | ~ v1_waybel_0(X4,sK0)
      | v1_xboole_0(X4)
      | ~ l1_orders_2(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(resolution,[],[f479,f161])).

fof(f1517,plain,(
    ! [X0,X1] :
      ( ~ v13_waybel_0(sK3(sK0,X0,X1),sK0)
      | ~ v2_waybel_0(sK3(sK0,X0,X1),sK0)
      | ~ r1_tarski(sK1,sK3(sK0,X0,X1))
      | ~ v1_subset_1(sK3(sK0,X0,X1),u1_struct_0(sK0))
      | ~ r1_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X1,sK0)
      | ~ v2_waybel_0(X1,sK0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X0,sK0)
      | ~ v1_waybel_0(X0,sK0)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f1516,f787])).

fof(f787,plain,(
    ! [X6,X7] :
      ( m1_subset_1(sK3(sK0,X6,X7),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(X6,X7)
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X7,sK0)
      | ~ v2_waybel_0(X7,sK0)
      | v1_xboole_0(X7)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X6,sK0)
      | ~ v1_waybel_0(X6,sK0)
      | v1_xboole_0(X6) ) ),
    inference(subsumption_resolution,[],[f786,f122])).

fof(f786,plain,(
    ! [X6,X7] :
      ( m1_subset_1(sK3(sK0,X6,X7),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(X6,X7)
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X7,sK0)
      | ~ v2_waybel_0(X7,sK0)
      | v1_xboole_0(X7)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X6,sK0)
      | ~ v1_waybel_0(X6,sK0)
      | v1_xboole_0(X6)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f785,f123])).

fof(f785,plain,(
    ! [X6,X7] :
      ( m1_subset_1(sK3(sK0,X6,X7),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(X6,X7)
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X7,sK0)
      | ~ v2_waybel_0(X7,sK0)
      | v1_xboole_0(X7)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X6,sK0)
      | ~ v1_waybel_0(X6,sK0)
      | v1_xboole_0(X6)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f784,f124])).

fof(f784,plain,(
    ! [X6,X7] :
      ( m1_subset_1(sK3(sK0,X6,X7),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(X6,X7)
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X7,sK0)
      | ~ v2_waybel_0(X7,sK0)
      | v1_xboole_0(X7)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X6,sK0)
      | ~ v1_waybel_0(X6,sK0)
      | v1_xboole_0(X6)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f783,f126])).

fof(f783,plain,(
    ! [X6,X7] :
      ( m1_subset_1(sK3(sK0,X6,X7),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(X6,X7)
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X7,sK0)
      | ~ v2_waybel_0(X7,sK0)
      | v1_xboole_0(X7)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X6,sK0)
      | ~ v1_waybel_0(X6,sK0)
      | v1_xboole_0(X6)
      | ~ v1_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f782,f127])).

fof(f782,plain,(
    ! [X6,X7] :
      ( m1_subset_1(sK3(sK0,X6,X7),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(X6,X7)
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X7,sK0)
      | ~ v2_waybel_0(X7,sK0)
      | v1_xboole_0(X7)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X6,sK0)
      | ~ v1_waybel_0(X6,sK0)
      | v1_xboole_0(X6)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f760,f128])).

fof(f760,plain,(
    ! [X6,X7] :
      ( m1_subset_1(sK3(sK0,X6,X7),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(X6,X7)
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X7,sK0)
      | ~ v2_waybel_0(X7,sK0)
      | v1_xboole_0(X7)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X6,sK0)
      | ~ v1_waybel_0(X6,sK0)
      | v1_xboole_0(X6)
      | ~ l1_orders_2(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(resolution,[],[f479,f162])).

fof(f1516,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK3(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(sK3(sK0,X0,X1),sK0)
      | ~ v2_waybel_0(sK3(sK0,X0,X1),sK0)
      | ~ r1_tarski(sK1,sK3(sK0,X0,X1))
      | ~ v1_subset_1(sK3(sK0,X0,X1),u1_struct_0(sK0))
      | ~ r1_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X1,sK0)
      | ~ v2_waybel_0(X1,sK0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X0,sK0)
      | ~ v1_waybel_0(X0,sK0)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f1515,f769])).

fof(f769,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(sK3(sK0,X0,X1))
      | ~ r1_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X1,sK0)
      | ~ v2_waybel_0(X1,sK0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X0,sK0)
      | ~ v1_waybel_0(X0,sK0)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f768,f122])).

fof(f768,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(sK3(sK0,X0,X1))
      | ~ r1_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X1,sK0)
      | ~ v2_waybel_0(X1,sK0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X0,sK0)
      | ~ v1_waybel_0(X0,sK0)
      | v1_xboole_0(X0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f767,f123])).

fof(f767,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(sK3(sK0,X0,X1))
      | ~ r1_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X1,sK0)
      | ~ v2_waybel_0(X1,sK0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X0,sK0)
      | ~ v1_waybel_0(X0,sK0)
      | v1_xboole_0(X0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f766,f124])).

fof(f766,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(sK3(sK0,X0,X1))
      | ~ r1_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X1,sK0)
      | ~ v2_waybel_0(X1,sK0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X0,sK0)
      | ~ v1_waybel_0(X0,sK0)
      | v1_xboole_0(X0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f765,f126])).

fof(f765,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(sK3(sK0,X0,X1))
      | ~ r1_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X1,sK0)
      | ~ v2_waybel_0(X1,sK0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X0,sK0)
      | ~ v1_waybel_0(X0,sK0)
      | v1_xboole_0(X0)
      | ~ v1_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f764,f127])).

fof(f764,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(sK3(sK0,X0,X1))
      | ~ r1_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X1,sK0)
      | ~ v2_waybel_0(X1,sK0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X0,sK0)
      | ~ v1_waybel_0(X0,sK0)
      | v1_xboole_0(X0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f757,f128])).

fof(f757,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(sK3(sK0,X0,X1))
      | ~ r1_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X1,sK0)
      | ~ v2_waybel_0(X1,sK0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X0,sK0)
      | ~ v1_waybel_0(X0,sK0)
      | v1_xboole_0(X0)
      | ~ l1_orders_2(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(resolution,[],[f479,f159])).

fof(f1515,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK3(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(sK3(sK0,X0,X1),sK0)
      | ~ v2_waybel_0(sK3(sK0,X0,X1),sK0)
      | v1_xboole_0(sK3(sK0,X0,X1))
      | ~ r1_tarski(sK1,sK3(sK0,X0,X1))
      | ~ v1_subset_1(sK3(sK0,X0,X1),u1_struct_0(sK0))
      | ~ r1_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X1,sK0)
      | ~ v2_waybel_0(X1,sK0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X0,sK0)
      | ~ v1_waybel_0(X0,sK0)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f1514,f122])).

fof(f1514,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK3(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(sK3(sK0,X0,X1),sK0)
      | ~ v2_waybel_0(sK3(sK0,X0,X1),sK0)
      | v1_xboole_0(sK3(sK0,X0,X1))
      | ~ r1_tarski(sK1,sK3(sK0,X0,X1))
      | ~ v1_subset_1(sK3(sK0,X0,X1),u1_struct_0(sK0))
      | ~ r1_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X1,sK0)
      | ~ v2_waybel_0(X1,sK0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X0,sK0)
      | ~ v1_waybel_0(X0,sK0)
      | v1_xboole_0(X0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f1513,f123])).

fof(f1513,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK3(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(sK3(sK0,X0,X1),sK0)
      | ~ v2_waybel_0(sK3(sK0,X0,X1),sK0)
      | v1_xboole_0(sK3(sK0,X0,X1))
      | ~ r1_tarski(sK1,sK3(sK0,X0,X1))
      | ~ v1_subset_1(sK3(sK0,X0,X1),u1_struct_0(sK0))
      | ~ r1_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X1,sK0)
      | ~ v2_waybel_0(X1,sK0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X0,sK0)
      | ~ v1_waybel_0(X0,sK0)
      | v1_xboole_0(X0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f1512,f124])).

fof(f1512,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK3(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(sK3(sK0,X0,X1),sK0)
      | ~ v2_waybel_0(sK3(sK0,X0,X1),sK0)
      | v1_xboole_0(sK3(sK0,X0,X1))
      | ~ r1_tarski(sK1,sK3(sK0,X0,X1))
      | ~ v1_subset_1(sK3(sK0,X0,X1),u1_struct_0(sK0))
      | ~ r1_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X1,sK0)
      | ~ v2_waybel_0(X1,sK0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X0,sK0)
      | ~ v1_waybel_0(X0,sK0)
      | v1_xboole_0(X0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f1511,f479])).

fof(f1511,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK3(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(sK3(sK0,X0,X1),sK0)
      | ~ v2_waybel_0(sK3(sK0,X0,X1),sK0)
      | v1_xboole_0(sK3(sK0,X0,X1))
      | ~ r1_tarski(sK1,sK3(sK0,X0,X1))
      | ~ v1_subset_1(sK3(sK0,X0,X1),u1_struct_0(sK0))
      | ~ r1_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X1,sK0)
      | ~ v2_waybel_0(X1,sK0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X0,sK0)
      | ~ v1_waybel_0(X0,sK0)
      | v1_xboole_0(X0)
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f1510,f126])).

fof(f1510,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK3(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(sK3(sK0,X0,X1),sK0)
      | ~ v2_waybel_0(sK3(sK0,X0,X1),sK0)
      | v1_xboole_0(sK3(sK0,X0,X1))
      | ~ r1_tarski(sK1,sK3(sK0,X0,X1))
      | ~ v1_subset_1(sK3(sK0,X0,X1),u1_struct_0(sK0))
      | ~ r1_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X1,sK0)
      | ~ v2_waybel_0(X1,sK0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X0,sK0)
      | ~ v1_waybel_0(X0,sK0)
      | v1_xboole_0(X0)
      | ~ v1_lattice3(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f1509,f127])).

fof(f1509,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK3(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(sK3(sK0,X0,X1),sK0)
      | ~ v2_waybel_0(sK3(sK0,X0,X1),sK0)
      | v1_xboole_0(sK3(sK0,X0,X1))
      | ~ r1_tarski(sK1,sK3(sK0,X0,X1))
      | ~ v1_subset_1(sK3(sK0,X0,X1),u1_struct_0(sK0))
      | ~ r1_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X1,sK0)
      | ~ v2_waybel_0(X1,sK0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X0,sK0)
      | ~ v1_waybel_0(X0,sK0)
      | v1_xboole_0(X0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f1506,f128])).

fof(f1506,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK3(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(sK3(sK0,X0,X1),sK0)
      | ~ v2_waybel_0(sK3(sK0,X0,X1),sK0)
      | v1_xboole_0(sK3(sK0,X0,X1))
      | ~ r1_tarski(sK1,sK3(sK0,X0,X1))
      | ~ v1_subset_1(sK3(sK0,X0,X1),u1_struct_0(sK0))
      | ~ r1_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X1,sK0)
      | ~ v2_waybel_0(X1,sK0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X0,sK0)
      | ~ v1_waybel_0(X0,sK0)
      | v1_xboole_0(X0)
      | ~ l1_orders_2(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(resolution,[],[f743,f163])).

fof(f163,plain,(
    ! [X2,X0,X1] :
      ( v2_waybel_7(sK3(X0,X1,X2),X0)
      | ~ r1_subset_1(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X2,X0)
      | ~ v2_waybel_0(X2,X0)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f104])).

fof(f743,plain,(
    ! [X0] :
      ( ~ v2_waybel_7(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X0,sK0)
      | ~ v2_waybel_0(X0,sK0)
      | v1_xboole_0(X0)
      | ~ r1_tarski(sK1,X0)
      | ~ v1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f742,f122])).

fof(f742,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X0,sK0)
      | ~ v2_waybel_0(X0,sK0)
      | v1_xboole_0(X0)
      | ~ v2_waybel_7(X0,sK0)
      | ~ v1_subset_1(X0,u1_struct_0(sK0))
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f741,f123])).

fof(f741,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X0,sK0)
      | ~ v2_waybel_0(X0,sK0)
      | v1_xboole_0(X0)
      | ~ v2_waybel_7(X0,sK0)
      | ~ v1_subset_1(X0,u1_struct_0(sK0))
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f740,f124])).

fof(f740,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X0,sK0)
      | ~ v2_waybel_0(X0,sK0)
      | v1_xboole_0(X0)
      | ~ v2_waybel_7(X0,sK0)
      | ~ v1_subset_1(X0,u1_struct_0(sK0))
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f739,f125])).

fof(f739,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X0,sK0)
      | ~ v2_waybel_0(X0,sK0)
      | v1_xboole_0(X0)
      | ~ v2_waybel_7(X0,sK0)
      | ~ v1_subset_1(X0,u1_struct_0(sK0))
      | ~ v11_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f738,f126])).

fof(f738,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X0,sK0)
      | ~ v2_waybel_0(X0,sK0)
      | v1_xboole_0(X0)
      | ~ v2_waybel_7(X0,sK0)
      | ~ v1_subset_1(X0,u1_struct_0(sK0))
      | ~ v1_lattice3(sK0)
      | ~ v11_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f737,f127])).

fof(f737,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X0,sK0)
      | ~ v2_waybel_0(X0,sK0)
      | v1_xboole_0(X0)
      | ~ v2_waybel_7(X0,sK0)
      | ~ v1_subset_1(X0,u1_struct_0(sK0))
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v11_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f736,f128])).

fof(f736,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X0,sK0)
      | ~ v2_waybel_0(X0,sK0)
      | v1_xboole_0(X0)
      | ~ v2_waybel_7(X0,sK0)
      | ~ v1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v11_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(duplicate_literal_removal,[],[f735])).

fof(f735,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X0,sK0)
      | ~ v2_waybel_0(X0,sK0)
      | v1_xboole_0(X0)
      | ~ v2_waybel_7(X0,sK0)
      | ~ v1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X0,sK0)
      | ~ v2_waybel_0(X0,sK0)
      | v1_xboole_0(X0)
      | ~ l1_orders_2(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v11_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(resolution,[],[f134,f166])).

fof(f166,plain,(
    ! [X0,X1] :
      ( v3_waybel_7(X1,X0)
      | ~ v2_waybel_7(X1,X0)
      | ~ v1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v11_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f106])).

fof(f106,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( ( v2_waybel_7(X1,X0)
                & v1_subset_1(X1,u1_struct_0(X0)) )
              | ~ v3_waybel_7(X1,X0) )
            & ( v3_waybel_7(X1,X0)
              | ~ v2_waybel_7(X1,X0)
              | ~ v1_subset_1(X1,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v11_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f105])).

fof(f105,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( ( v2_waybel_7(X1,X0)
                & v1_subset_1(X1,u1_struct_0(X0)) )
              | ~ v3_waybel_7(X1,X0) )
            & ( v3_waybel_7(X1,X0)
              | ~ v2_waybel_7(X1,X0)
              | ~ v1_subset_1(X1,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v11_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_waybel_7(X1,X0)
              & v1_subset_1(X1,u1_struct_0(X0)) )
          <=> v3_waybel_7(X1,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v11_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f65])).

fof(f65,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_waybel_7(X1,X0)
              & v1_subset_1(X1,u1_struct_0(X0)) )
          <=> v3_waybel_7(X1,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v11_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v11_waybel_1(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ( ( v2_waybel_7(X1,X0)
              & v1_subset_1(X1,u1_struct_0(X0)) )
          <=> v3_waybel_7(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t30_waybel_7.p',t26_waybel_7)).

fof(f134,plain,(
    ! [X2] :
      ( ~ v3_waybel_7(X2,sK0)
      | ~ r1_tarski(sK1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X2,sK0)
      | ~ v2_waybel_0(X2,sK0)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f99])).

fof(f52715,plain,(
    r1_subset_1(k1_tarski(k3_yellow_0(sK0)),sK1) ),
    inference(subsumption_resolution,[],[f52606,f3630])).

fof(f52606,plain,
    ( r1_subset_1(k1_tarski(k3_yellow_0(sK0)),sK1)
    | v1_xboole_0(k1_tarski(k3_yellow_0(sK0))) ),
    inference(resolution,[],[f52230,f448])).

fof(f448,plain,(
    ! [X35] :
      ( ~ r1_subset_1(sK1,X35)
      | r1_subset_1(X35,sK1)
      | v1_xboole_0(X35) ) ),
    inference(resolution,[],[f129,f183])).

fof(f183,plain,(
    ! [X0,X1] :
      ( r1_subset_1(X1,X0)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r1_subset_1(X1,X0)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r1_subset_1(X1,X0)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
       => r1_subset_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t30_waybel_7.p',symmetry_r1_subset_1)).

fof(f52230,plain,(
    r1_subset_1(sK1,k1_tarski(k3_yellow_0(sK0))) ),
    inference(subsumption_resolution,[],[f52104,f1233])).

fof(f52104,plain,
    ( m1_subset_1(k3_yellow_0(sK0),sK1)
    | r1_subset_1(sK1,k1_tarski(k3_yellow_0(sK0))) ),
    inference(resolution,[],[f51942,f16417])).

fof(f16417,plain,
    ( ~ r1_subset_1(k1_tarski(k3_yellow_0(sK0)),sK1)
    | r1_subset_1(sK1,k1_tarski(k3_yellow_0(sK0))) ),
    inference(resolution,[],[f3777,f129])).

fof(f3777,plain,(
    ! [X35] :
      ( v1_xboole_0(X35)
      | r1_subset_1(X35,k1_tarski(k3_yellow_0(sK0)))
      | ~ r1_subset_1(k1_tarski(k3_yellow_0(sK0)),X35) ) ),
    inference(forward_demodulation,[],[f3655,f3623])).

fof(f3655,plain,(
    ! [X35] :
      ( r1_subset_1(X35,k1_tarski(k3_yellow_0(sK0)))
      | ~ r1_subset_1(k5_waybel_0(sK0,k3_yellow_0(sK0)),X35)
      | v1_xboole_0(X35) ) ),
    inference(backward_demodulation,[],[f3623,f1482])).

fof(f1482,plain,(
    ! [X35] :
      ( r1_subset_1(X35,k5_waybel_0(sK0,k3_yellow_0(sK0)))
      | ~ r1_subset_1(k5_waybel_0(sK0,k3_yellow_0(sK0)),X35)
      | v1_xboole_0(X35) ) ),
    inference(resolution,[],[f824,f183])).

fof(f55185,plain,
    ( v1_subset_1(sK3(sK0,k1_tarski(k3_yellow_0(sK0)),sK1),u1_struct_0(sK0))
    | r2_hidden(k3_yellow_0(sK0),sK3(sK0,k1_tarski(k3_yellow_0(sK0)),sK1))
    | ~ m1_subset_1(sK3(sK0,k1_tarski(k3_yellow_0(sK0)),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v13_waybel_0(sK3(sK0,k1_tarski(k3_yellow_0(sK0)),sK1),sK0)
    | v1_xboole_0(sK3(sK0,k1_tarski(k3_yellow_0(sK0)),sK1))
    | ~ l1_orders_2(sK0)
    | ~ v1_yellow_0(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f52224,f158])).

fof(f158,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,u1_struct_0(X0))
      | r2_hidden(k3_yellow_0(X0),X1)
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
    inference(cnf_transformation,[],[f102])).

fof(f52224,plain,(
    v2_waybel_0(sK3(sK0,k1_tarski(k3_yellow_0(sK0)),sK1),sK0) ),
    inference(subsumption_resolution,[],[f52098,f1233])).

fof(f52098,plain,
    ( m1_subset_1(k3_yellow_0(sK0),sK1)
    | v2_waybel_0(sK3(sK0,k1_tarski(k3_yellow_0(sK0)),sK1),sK0) ),
    inference(resolution,[],[f51942,f3794])).

fof(f3794,plain,
    ( ~ r1_subset_1(k1_tarski(k3_yellow_0(sK0)),sK1)
    | v2_waybel_0(sK3(sK0,k1_tarski(k3_yellow_0(sK0)),sK1),sK0) ),
    inference(forward_demodulation,[],[f3673,f3623])).

fof(f3673,plain,
    ( v2_waybel_0(sK3(sK0,k1_tarski(k3_yellow_0(sK0)),sK1),sK0)
    | ~ r1_subset_1(k5_waybel_0(sK0,k3_yellow_0(sK0)),sK1) ),
    inference(backward_demodulation,[],[f3623,f1968])).

fof(f1968,plain,
    ( ~ r1_subset_1(k5_waybel_0(sK0,k3_yellow_0(sK0)),sK1)
    | v2_waybel_0(sK3(sK0,k5_waybel_0(sK0,k3_yellow_0(sK0)),sK1),sK0) ),
    inference(subsumption_resolution,[],[f1967,f824])).

fof(f1967,plain,
    ( ~ r1_subset_1(k5_waybel_0(sK0,k3_yellow_0(sK0)),sK1)
    | v2_waybel_0(sK3(sK0,k5_waybel_0(sK0,k3_yellow_0(sK0)),sK1),sK0)
    | v1_xboole_0(k5_waybel_0(sK0,k3_yellow_0(sK0))) ),
    inference(subsumption_resolution,[],[f1966,f827])).

fof(f1966,plain,
    ( ~ r1_subset_1(k5_waybel_0(sK0,k3_yellow_0(sK0)),sK1)
    | v2_waybel_0(sK3(sK0,k5_waybel_0(sK0,k3_yellow_0(sK0)),sK1),sK0)
    | ~ v1_waybel_0(k5_waybel_0(sK0,k3_yellow_0(sK0)),sK0)
    | v1_xboole_0(k5_waybel_0(sK0,k3_yellow_0(sK0))) ),
    inference(subsumption_resolution,[],[f1943,f821])).

fof(f1943,plain,
    ( ~ r1_subset_1(k5_waybel_0(sK0,k3_yellow_0(sK0)),sK1)
    | ~ m1_subset_1(k5_waybel_0(sK0,k3_yellow_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_waybel_0(sK3(sK0,k5_waybel_0(sK0,k3_yellow_0(sK0)),sK1),sK0)
    | ~ v1_waybel_0(k5_waybel_0(sK0,k3_yellow_0(sK0)),sK0)
    | v1_xboole_0(k5_waybel_0(sK0,k3_yellow_0(sK0))) ),
    inference(resolution,[],[f830,f566])).

fof(f566,plain,(
    ! [X1] :
      ( ~ v12_waybel_0(X1,sK0)
      | ~ r1_subset_1(X1,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_waybel_0(sK3(sK0,X1,sK1),sK0)
      | ~ v1_waybel_0(X1,sK0)
      | v1_xboole_0(X1) ) ),
    inference(subsumption_resolution,[],[f565,f122])).

fof(f565,plain,(
    ! [X1] :
      ( v2_waybel_0(sK3(sK0,X1,sK1),sK0)
      | ~ r1_subset_1(X1,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X1,sK0)
      | ~ v1_waybel_0(X1,sK0)
      | v1_xboole_0(X1)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f564,f123])).

fof(f564,plain,(
    ! [X1] :
      ( v2_waybel_0(sK3(sK0,X1,sK1),sK0)
      | ~ r1_subset_1(X1,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X1,sK0)
      | ~ v1_waybel_0(X1,sK0)
      | v1_xboole_0(X1)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f563,f124])).

fof(f563,plain,(
    ! [X1] :
      ( v2_waybel_0(sK3(sK0,X1,sK1),sK0)
      | ~ r1_subset_1(X1,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X1,sK0)
      | ~ v1_waybel_0(X1,sK0)
      | v1_xboole_0(X1)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f562,f479])).

fof(f562,plain,(
    ! [X1] :
      ( v2_waybel_0(sK3(sK0,X1,sK1),sK0)
      | ~ r1_subset_1(X1,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X1,sK0)
      | ~ v1_waybel_0(X1,sK0)
      | v1_xboole_0(X1)
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f561,f126])).

fof(f561,plain,(
    ! [X1] :
      ( v2_waybel_0(sK3(sK0,X1,sK1),sK0)
      | ~ r1_subset_1(X1,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X1,sK0)
      | ~ v1_waybel_0(X1,sK0)
      | v1_xboole_0(X1)
      | ~ v1_lattice3(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f560,f127])).

fof(f560,plain,(
    ! [X1] :
      ( v2_waybel_0(sK3(sK0,X1,sK1),sK0)
      | ~ r1_subset_1(X1,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X1,sK0)
      | ~ v1_waybel_0(X1,sK0)
      | v1_xboole_0(X1)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f559,f128])).

fof(f559,plain,(
    ! [X1] :
      ( v2_waybel_0(sK3(sK0,X1,sK1),sK0)
      | ~ r1_subset_1(X1,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X1,sK0)
      | ~ v1_waybel_0(X1,sK0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f558,f129])).

fof(f558,plain,(
    ! [X1] :
      ( v2_waybel_0(sK3(sK0,X1,sK1),sK0)
      | ~ r1_subset_1(X1,sK1)
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X1,sK0)
      | ~ v1_waybel_0(X1,sK0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f557,f132])).

fof(f557,plain,(
    ! [X1] :
      ( v2_waybel_0(sK3(sK0,X1,sK1),sK0)
      | ~ r1_subset_1(X1,sK1)
      | ~ v13_waybel_0(sK1,sK0)
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X1,sK0)
      | ~ v1_waybel_0(X1,sK0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f529,f133])).

fof(f529,plain,(
    ! [X1] :
      ( v2_waybel_0(sK3(sK0,X1,sK1),sK0)
      | ~ r1_subset_1(X1,sK1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(sK1,sK0)
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X1,sK0)
      | ~ v1_waybel_0(X1,sK0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(resolution,[],[f131,f160])).
%------------------------------------------------------------------------------
