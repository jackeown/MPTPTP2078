%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1987+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:01 EST 2020

% Result     : Theorem 0.15s
% Output     : Refutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :  225 (2189 expanded)
%              Number of leaves         :   29 ( 757 expanded)
%              Depth                    :   28
%              Number of atoms          : 1410 (42330 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f565,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f147,f237,f272,f292,f295,f347,f350,f438,f441,f453,f564])).

fof(f564,plain,
    ( ~ spl9_1
    | spl9_2 ),
    inference(avatar_contradiction_clause,[],[f563])).

fof(f563,plain,
    ( $false
    | ~ spl9_1
    | spl9_2 ),
    inference(subsumption_resolution,[],[f562,f463])).

fof(f463,plain,
    ( ~ r2_hidden(sK4,sK6)
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f72,f141])).

fof(f141,plain,
    ( r1_waybel_3(sK3,sK4,sK5)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl9_1
  <=> r1_waybel_3(sK3,sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f72,plain,
    ( ~ r2_hidden(sK4,sK6)
    | ~ r1_waybel_3(sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
    ( ( ( ~ r2_hidden(sK4,sK6)
        & r3_orders_2(sK3,sK5,k1_yellow_0(sK3,sK6))
        & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3)))
        & v1_waybel_7(sK6,sK3)
        & v12_waybel_0(sK6,sK3)
        & v1_waybel_0(sK6,sK3)
        & ~ v1_xboole_0(sK6) )
      | ~ r1_waybel_3(sK3,sK4,sK5) )
    & ( ! [X4] :
          ( r2_hidden(sK4,X4)
          | ~ r3_orders_2(sK3,sK5,k1_yellow_0(sK3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK3)))
          | ~ v1_waybel_7(X4,sK3)
          | ~ v12_waybel_0(X4,sK3)
          | ~ v1_waybel_0(X4,sK3)
          | v1_xboole_0(X4) )
      | r1_waybel_3(sK3,sK4,sK5) )
    & m1_subset_1(sK5,u1_struct_0(sK3))
    & m1_subset_1(sK4,u1_struct_0(sK3))
    & l1_orders_2(sK3)
    & v3_lattice3(sK3)
    & v2_lattice3(sK3)
    & v1_lattice3(sK3)
    & v2_waybel_1(sK3)
    & v5_orders_2(sK3)
    & v4_orders_2(sK3)
    & v3_orders_2(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f39,f43,f42,f41,f40])).

% (27899)lrs+10_4_add=off:afp=100000:afq=2.0:amm=sco:anc=none:nm=64:nwc=1:stl=150:sp=occurrence:updr=off_733 on theBenchmark
fof(f40,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ? [X3] :
                      ( ~ r2_hidden(X1,X3)
                      & r3_orders_2(X0,X2,k1_yellow_0(X0,X3))
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                      & v1_waybel_7(X3,X0)
                      & v12_waybel_0(X3,X0)
                      & v1_waybel_0(X3,X0)
                      & ~ v1_xboole_0(X3) )
                  | ~ r1_waybel_3(X0,X1,X2) )
                & ( ! [X4] :
                      ( r2_hidden(X1,X4)
                      | ~ r3_orders_2(X0,X2,k1_yellow_0(X0,X4))
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                      | ~ v1_waybel_7(X4,X0)
                      | ~ v12_waybel_0(X4,X0)
                      | ~ v1_waybel_0(X4,X0)
                      | v1_xboole_0(X4) )
                  | r1_waybel_3(X0,X1,X2) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v3_lattice3(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v2_waybel_1(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ r2_hidden(X1,X3)
                    & r3_orders_2(sK3,X2,k1_yellow_0(sK3,X3))
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3)))
                    & v1_waybel_7(X3,sK3)
                    & v12_waybel_0(X3,sK3)
                    & v1_waybel_0(X3,sK3)
                    & ~ v1_xboole_0(X3) )
                | ~ r1_waybel_3(sK3,X1,X2) )
              & ( ! [X4] :
                    ( r2_hidden(X1,X4)
                    | ~ r3_orders_2(sK3,X2,k1_yellow_0(sK3,X4))
                    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK3)))
                    | ~ v1_waybel_7(X4,sK3)
                    | ~ v12_waybel_0(X4,sK3)
                    | ~ v1_waybel_0(X4,sK3)
                    | v1_xboole_0(X4) )
                | r1_waybel_3(sK3,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(sK3)) )
          & m1_subset_1(X1,u1_struct_0(sK3)) )
      & l1_orders_2(sK3)
      & v3_lattice3(sK3)
      & v2_lattice3(sK3)
      & v1_lattice3(sK3)
      & v2_waybel_1(sK3)
      & v5_orders_2(sK3)
      & v4_orders_2(sK3)
      & v3_orders_2(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ? [X3] :
                  ( ~ r2_hidden(X1,X3)
                  & r3_orders_2(sK3,X2,k1_yellow_0(sK3,X3))
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3)))
                  & v1_waybel_7(X3,sK3)
                  & v12_waybel_0(X3,sK3)
                  & v1_waybel_0(X3,sK3)
                  & ~ v1_xboole_0(X3) )
              | ~ r1_waybel_3(sK3,X1,X2) )
            & ( ! [X4] :
                  ( r2_hidden(X1,X4)
                  | ~ r3_orders_2(sK3,X2,k1_yellow_0(sK3,X4))
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK3)))
                  | ~ v1_waybel_7(X4,sK3)
                  | ~ v12_waybel_0(X4,sK3)
                  | ~ v1_waybel_0(X4,sK3)
                  | v1_xboole_0(X4) )
              | r1_waybel_3(sK3,X1,X2) )
            & m1_subset_1(X2,u1_struct_0(sK3)) )
        & m1_subset_1(X1,u1_struct_0(sK3)) )
   => ( ? [X2] :
          ( ( ? [X3] :
                ( ~ r2_hidden(sK4,X3)
                & r3_orders_2(sK3,X2,k1_yellow_0(sK3,X3))
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3)))
                & v1_waybel_7(X3,sK3)
                & v12_waybel_0(X3,sK3)
                & v1_waybel_0(X3,sK3)
                & ~ v1_xboole_0(X3) )
            | ~ r1_waybel_3(sK3,sK4,X2) )
          & ( ! [X4] :
                ( r2_hidden(sK4,X4)
                | ~ r3_orders_2(sK3,X2,k1_yellow_0(sK3,X4))
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK3)))
                | ~ v1_waybel_7(X4,sK3)
                | ~ v12_waybel_0(X4,sK3)
                | ~ v1_waybel_0(X4,sK3)
                | v1_xboole_0(X4) )
            | r1_waybel_3(sK3,sK4,X2) )
          & m1_subset_1(X2,u1_struct_0(sK3)) )
      & m1_subset_1(sK4,u1_struct_0(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X2] :
        ( ( ? [X3] :
              ( ~ r2_hidden(sK4,X3)
              & r3_orders_2(sK3,X2,k1_yellow_0(sK3,X3))
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3)))
              & v1_waybel_7(X3,sK3)
              & v12_waybel_0(X3,sK3)
              & v1_waybel_0(X3,sK3)
              & ~ v1_xboole_0(X3) )
          | ~ r1_waybel_3(sK3,sK4,X2) )
        & ( ! [X4] :
              ( r2_hidden(sK4,X4)
              | ~ r3_orders_2(sK3,X2,k1_yellow_0(sK3,X4))
              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK3)))
              | ~ v1_waybel_7(X4,sK3)
              | ~ v12_waybel_0(X4,sK3)
              | ~ v1_waybel_0(X4,sK3)
              | v1_xboole_0(X4) )
          | r1_waybel_3(sK3,sK4,X2) )
        & m1_subset_1(X2,u1_struct_0(sK3)) )
   => ( ( ? [X3] :
            ( ~ r2_hidden(sK4,X3)
            & r3_orders_2(sK3,sK5,k1_yellow_0(sK3,X3))
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3)))
            & v1_waybel_7(X3,sK3)
            & v12_waybel_0(X3,sK3)
            & v1_waybel_0(X3,sK3)
            & ~ v1_xboole_0(X3) )
        | ~ r1_waybel_3(sK3,sK4,sK5) )
      & ( ! [X4] :
            ( r2_hidden(sK4,X4)
            | ~ r3_orders_2(sK3,sK5,k1_yellow_0(sK3,X4))
            | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK3)))
            | ~ v1_waybel_7(X4,sK3)
            | ~ v12_waybel_0(X4,sK3)
            | ~ v1_waybel_0(X4,sK3)
            | v1_xboole_0(X4) )
        | r1_waybel_3(sK3,sK4,sK5) )
      & m1_subset_1(sK5,u1_struct_0(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X3] :
        ( ~ r2_hidden(sK4,X3)
        & r3_orders_2(sK3,sK5,k1_yellow_0(sK3,X3))
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3)))
        & v1_waybel_7(X3,sK3)
        & v12_waybel_0(X3,sK3)
        & v1_waybel_0(X3,sK3)
        & ~ v1_xboole_0(X3) )
   => ( ~ r2_hidden(sK4,sK6)
      & r3_orders_2(sK3,sK5,k1_yellow_0(sK3,sK6))
      & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3)))
      & v1_waybel_7(sK6,sK3)
      & v12_waybel_0(sK6,sK3)
      & v1_waybel_0(sK6,sK3)
      & ~ v1_xboole_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ r2_hidden(X1,X3)
                    & r3_orders_2(X0,X2,k1_yellow_0(X0,X3))
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                    & v1_waybel_7(X3,X0)
                    & v12_waybel_0(X3,X0)
                    & v1_waybel_0(X3,X0)
                    & ~ v1_xboole_0(X3) )
                | ~ r1_waybel_3(X0,X1,X2) )
              & ( ! [X4] :
                    ( r2_hidden(X1,X4)
                    | ~ r3_orders_2(X0,X2,k1_yellow_0(X0,X4))
                    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                    | ~ v1_waybel_7(X4,X0)
                    | ~ v12_waybel_0(X4,X0)
                    | ~ v1_waybel_0(X4,X0)
                    | v1_xboole_0(X4) )
                | r1_waybel_3(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v3_lattice3(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v2_waybel_1(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ r2_hidden(X1,X3)
                    & r3_orders_2(X0,X2,k1_yellow_0(X0,X3))
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                    & v1_waybel_7(X3,X0)
                    & v12_waybel_0(X3,X0)
                    & v1_waybel_0(X3,X0)
                    & ~ v1_xboole_0(X3) )
                | ~ r1_waybel_3(X0,X1,X2) )
              & ( ! [X3] :
                    ( r2_hidden(X1,X3)
                    | ~ r3_orders_2(X0,X2,k1_yellow_0(X0,X3))
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                    | ~ v1_waybel_7(X3,X0)
                    | ~ v12_waybel_0(X3,X0)
                    | ~ v1_waybel_0(X3,X0)
                    | v1_xboole_0(X3) )
                | r1_waybel_3(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v3_lattice3(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v2_waybel_1(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ r2_hidden(X1,X3)
                    & r3_orders_2(X0,X2,k1_yellow_0(X0,X3))
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                    & v1_waybel_7(X3,X0)
                    & v12_waybel_0(X3,X0)
                    & v1_waybel_0(X3,X0)
                    & ~ v1_xboole_0(X3) )
                | ~ r1_waybel_3(X0,X1,X2) )
              & ( ! [X3] :
                    ( r2_hidden(X1,X3)
                    | ~ r3_orders_2(X0,X2,k1_yellow_0(X0,X3))
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                    | ~ v1_waybel_7(X3,X0)
                    | ~ v12_waybel_0(X3,X0)
                    | ~ v1_waybel_0(X3,X0)
                    | v1_xboole_0(X3) )
                | r1_waybel_3(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v3_lattice3(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v2_waybel_1(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r1_waybel_3(X0,X1,X2)
              <~> ! [X3] :
                    ( r2_hidden(X1,X3)
                    | ~ r3_orders_2(X0,X2,k1_yellow_0(X0,X3))
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                    | ~ v1_waybel_7(X3,X0)
                    | ~ v12_waybel_0(X3,X0)
                    | ~ v1_waybel_0(X3,X0)
                    | v1_xboole_0(X3) ) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v3_lattice3(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v2_waybel_1(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r1_waybel_3(X0,X1,X2)
              <~> ! [X3] :
                    ( r2_hidden(X1,X3)
                    | ~ r3_orders_2(X0,X2,k1_yellow_0(X0,X3))
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                    | ~ v1_waybel_7(X3,X0)
                    | ~ v12_waybel_0(X3,X0)
                    | ~ v1_waybel_0(X3,X0)
                    | v1_xboole_0(X3) ) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v3_lattice3(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v2_waybel_1(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v3_lattice3(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v2_waybel_1(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r1_waybel_3(X0,X1,X2)
                <=> ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                        & v1_waybel_7(X3,X0)
                        & v12_waybel_0(X3,X0)
                        & v1_waybel_0(X3,X0)
                        & ~ v1_xboole_0(X3) )
                     => ( r3_orders_2(X0,X2,k1_yellow_0(X0,X3))
                       => r2_hidden(X1,X3) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_lattice3(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v2_waybel_1(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_waybel_3(X0,X1,X2)
              <=> ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                      & v1_waybel_7(X3,X0)
                      & v12_waybel_0(X3,X0)
                      & v1_waybel_0(X3,X0)
                      & ~ v1_xboole_0(X3) )
                   => ( r3_orders_2(X0,X2,k1_yellow_0(X0,X3))
                     => r2_hidden(X1,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_waybel_7)).

fof(f562,plain,
    ( r2_hidden(sK4,sK6)
    | ~ spl9_1
    | spl9_2 ),
    inference(subsumption_resolution,[],[f561,f63])).

fof(f63,plain,(
    m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f44])).

fof(f561,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | r2_hidden(sK4,sK6)
    | ~ spl9_1
    | spl9_2 ),
    inference(resolution,[],[f549,f141])).

fof(f549,plain,
    ( ! [X2] :
        ( ~ r1_waybel_3(sK3,X2,sK5)
        | ~ m1_subset_1(X2,u1_struct_0(sK3))
        | r2_hidden(X2,sK6) )
    | ~ spl9_1
    | spl9_2 ),
    inference(subsumption_resolution,[],[f545,f64])).

fof(f64,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f44])).

fof(f545,plain,
    ( ! [X2] :
        ( ~ r1_waybel_3(sK3,X2,sK5)
        | ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ m1_subset_1(X2,u1_struct_0(sK3))
        | r2_hidden(X2,sK6) )
    | ~ spl9_1
    | spl9_2 ),
    inference(resolution,[],[f543,f465])).

fof(f465,plain,
    ( r3_orders_2(sK3,sK5,k1_yellow_0(sK3,sK6))
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f71,f141])).

fof(f71,plain,
    ( r3_orders_2(sK3,sK5,k1_yellow_0(sK3,sK6))
    | ~ r1_waybel_3(sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f44])).

fof(f543,plain,
    ( ! [X0,X1] :
        ( ~ r3_orders_2(sK3,X0,k1_yellow_0(sK3,sK6))
        | ~ r1_waybel_3(sK3,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | r2_hidden(X1,sK6) )
    | ~ spl9_1
    | spl9_2 ),
    inference(subsumption_resolution,[],[f459,f464])).

fof(f464,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f70,f141])).

fof(f70,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_waybel_3(sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f44])).

fof(f459,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ r3_orders_2(sK3,X0,k1_yellow_0(sK3,sK6))
        | ~ r1_waybel_3(sK3,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | r2_hidden(X1,sK6) )
    | ~ spl9_1
    | spl9_2 ),
    inference(subsumption_resolution,[],[f458,f146])).

fof(f146,plain,
    ( ~ v1_xboole_0(sK6)
    | spl9_2 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl9_2
  <=> v1_xboole_0(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f458,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ r3_orders_2(sK3,X0,k1_yellow_0(sK3,sK6))
        | v1_xboole_0(sK6)
        | ~ r1_waybel_3(sK3,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | r2_hidden(X1,sK6) )
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f456,f454])).

fof(f454,plain,
    ( v1_waybel_0(sK6,sK3)
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f67,f141])).

fof(f67,plain,
    ( v1_waybel_0(sK6,sK3)
    | ~ r1_waybel_3(sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f44])).

fof(f456,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ r3_orders_2(sK3,X0,k1_yellow_0(sK3,sK6))
        | ~ v1_waybel_0(sK6,sK3)
        | v1_xboole_0(sK6)
        | ~ r1_waybel_3(sK3,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | r2_hidden(X1,sK6) )
    | ~ spl9_1 ),
    inference(resolution,[],[f455,f374])).

fof(f374,plain,(
    ! [X4,X5,X3] :
      ( ~ v12_waybel_0(X4,sK3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ r3_orders_2(sK3,X3,k1_yellow_0(sK3,X4))
      | ~ v1_waybel_0(X4,sK3)
      | v1_xboole_0(X4)
      | ~ r1_waybel_3(sK3,X5,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK3))
      | ~ m1_subset_1(X5,u1_struct_0(sK3))
      | r2_hidden(X5,X4) ) ),
    inference(subsumption_resolution,[],[f109,f131])).

fof(f131,plain,(
    ~ v2_struct_0(sK3) ),
    inference(global_subsumption,[],[f62,f130])).

fof(f130,plain,
    ( ~ v2_struct_0(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(resolution,[],[f60,f73])).

fof(f73,plain,(
    ! [X0] :
      ( ~ v2_lattice3(X0)
      | ~ v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_lattice3)).

fof(f60,plain,(
    v2_lattice3(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f62,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f109,plain,(
    ! [X4,X5,X3] :
      ( ~ r3_orders_2(sK3,X3,k1_yellow_0(sK3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ v12_waybel_0(X4,sK3)
      | ~ v1_waybel_0(X4,sK3)
      | v1_xboole_0(X4)
      | ~ r1_waybel_3(sK3,X5,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK3))
      | ~ m1_subset_1(X5,u1_struct_0(sK3))
      | r2_hidden(X5,X4)
      | v2_struct_0(sK3) ) ),
    inference(global_subsumption,[],[f62,f108])).

fof(f108,plain,(
    ! [X4,X5,X3] :
      ( ~ r3_orders_2(sK3,X3,k1_yellow_0(sK3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ v12_waybel_0(X4,sK3)
      | ~ v1_waybel_0(X4,sK3)
      | v1_xboole_0(X4)
      | ~ r1_waybel_3(sK3,X5,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK3))
      | ~ m1_subset_1(X5,u1_struct_0(sK3))
      | ~ l1_orders_2(sK3)
      | r2_hidden(X5,X4)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f106,f55])).

fof(f55,plain,(
    v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f106,plain,(
    ! [X4,X5,X3] :
      ( ~ r3_orders_2(sK3,X3,k1_yellow_0(sK3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ v12_waybel_0(X4,sK3)
      | ~ v1_waybel_0(X4,sK3)
      | v1_xboole_0(X4)
      | ~ r1_waybel_3(sK3,X5,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK3))
      | ~ m1_subset_1(X5,u1_struct_0(sK3))
      | ~ l1_orders_2(sK3)
      | r2_hidden(X5,X4)
      | ~ v3_orders_2(sK3)
      | v2_struct_0(sK3) ) ),
    inference(resolution,[],[f56,f86])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v4_orders_2(X0)
      | ~ r3_orders_2(X0,X2,k1_yellow_0(X0,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X3,X0)
      | ~ v1_waybel_0(X3,X0)
      | v1_xboole_0(X3)
      | ~ r1_waybel_3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_hidden(X1,X3)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_hidden(X1,X3)
                  | ~ r3_orders_2(X0,X2,k1_yellow_0(X0,X3))
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  | ~ v12_waybel_0(X3,X0)
                  | ~ v1_waybel_0(X3,X0)
                  | v1_xboole_0(X3) )
              | ~ r1_waybel_3(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_hidden(X1,X3)
                  | ~ r3_orders_2(X0,X2,k1_yellow_0(X0,X3))
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  | ~ v12_waybel_0(X3,X0)
                  | ~ v1_waybel_0(X3,X0)
                  | v1_xboole_0(X3) )
              | ~ r1_waybel_3(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_waybel_3(X0,X1,X2)
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                      & v12_waybel_0(X3,X0)
                      & v1_waybel_0(X3,X0)
                      & ~ v1_xboole_0(X3) )
                   => ( r3_orders_2(X0,X2,k1_yellow_0(X0,X3))
                     => r2_hidden(X1,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_waybel_3)).

fof(f56,plain,(
    v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f455,plain,
    ( v12_waybel_0(sK6,sK3)
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f68,f141])).

fof(f68,plain,
    ( v12_waybel_0(sK6,sK3)
    | ~ r1_waybel_3(sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f44])).

fof(f453,plain,
    ( ~ spl9_14
    | ~ spl9_20 ),
    inference(avatar_contradiction_clause,[],[f452])).

fof(f452,plain,
    ( $false
    | ~ spl9_14
    | ~ spl9_20 ),
    inference(subsumption_resolution,[],[f451,f291])).

fof(f291,plain,
    ( sP2(sK4,sK7(sK4,sK3,sK5),sK3)
    | ~ spl9_14 ),
    inference(avatar_component_clause,[],[f289])).

fof(f289,plain,
    ( spl9_14
  <=> sP2(sK4,sK7(sK4,sK3,sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f451,plain,
    ( ~ sP2(sK4,sK7(sK4,sK3,sK5),sK3)
    | ~ spl9_20 ),
    inference(resolution,[],[f433,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(sK8(X0,X1,X2))
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r2_hidden(X0,sK8(X0,X1,X2))
        & r1_tarski(X1,sK8(X0,X1,X2))
        & v1_waybel_7(sK8(X0,X1,X2),X2)
        & m1_subset_1(sK8(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2)))
        & v12_waybel_0(sK8(X0,X1,X2),X2)
        & v1_waybel_0(sK8(X0,X1,X2),X2)
        & ~ v1_xboole_0(sK8(X0,X1,X2)) )
      | ~ sP2(X0,X1,X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f51,f52])).

fof(f52,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X0,X3)
          & r1_tarski(X1,X3)
          & v1_waybel_7(X3,X2)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
          & v12_waybel_0(X3,X2)
          & v1_waybel_0(X3,X2)
          & ~ v1_xboole_0(X3) )
     => ( ~ r2_hidden(X0,sK8(X0,X1,X2))
        & r1_tarski(X1,sK8(X0,X1,X2))
        & v1_waybel_7(sK8(X0,X1,X2),X2)
        & m1_subset_1(sK8(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2)))
        & v12_waybel_0(sK8(X0,X1,X2),X2)
        & v1_waybel_0(sK8(X0,X1,X2),X2)
        & ~ v1_xboole_0(sK8(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

% (27891)lrs+1011_2:1_add=large:afr=on:afp=4000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:gs=on:irw=on:nm=64:nwc=1:sas=z3:stl=30:sos=on:sp=reverse_arity:thf=on:urr=on:updr=off_81 on theBenchmark
% (27898)lrs+1010_4:1_aac=none:add=off:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=on:gs=on:gsem=on:irw=on:nm=0:nwc=2.5:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_2 on theBenchmark
% (27885)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% (27895)dis+1011_4_awrs=decay:awrsf=32:afp=40000:afq=1.0:amm=off:anc=all:bs=on:cond=on:fsr=off:gsp=input_only:lma=on:nm=16:nwc=1:nicw=on:sac=on:sp=frequency:thi=all:updr=off:uhcvi=on_670 on theBenchmark
fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_hidden(X0,X3)
          & r1_tarski(X1,X3)
          & v1_waybel_7(X3,X2)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
          & v12_waybel_0(X3,X2)
          & v1_waybel_0(X3,X2)
          & ~ v1_xboole_0(X3) )
      | ~ sP2(X0,X1,X2) ) ),
    inference(rectify,[],[f50])).

fof(f50,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X2,X3)
          & r1_tarski(X1,X3)
          & v1_waybel_7(X3,X0)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
          & v12_waybel_0(X3,X0)
          & v1_waybel_0(X3,X0)
          & ~ v1_xboole_0(X3) )
      | ~ sP2(X2,X1,X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X2,X3)
          & r1_tarski(X1,X3)
          & v1_waybel_7(X3,X0)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
          & v12_waybel_0(X3,X0)
          & v1_waybel_0(X3,X0)
          & ~ v1_xboole_0(X3) )
      | ~ sP2(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f433,plain,
    ( v1_xboole_0(sK8(sK4,sK7(sK4,sK3,sK5),sK3))
    | ~ spl9_20 ),
    inference(avatar_component_clause,[],[f431])).

fof(f431,plain,
    ( spl9_20
  <=> v1_xboole_0(sK8(sK4,sK7(sK4,sK3,sK5),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).

fof(f441,plain,
    ( ~ spl9_14
    | ~ spl9_21 ),
    inference(avatar_contradiction_clause,[],[f440])).

fof(f440,plain,
    ( $false
    | ~ spl9_14
    | ~ spl9_21 ),
    inference(subsumption_resolution,[],[f439,f291])).

fof(f439,plain,
    ( ~ sP2(sK4,sK7(sK4,sK3,sK5),sK3)
    | ~ spl9_21 ),
    inference(resolution,[],[f437,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,sK8(X0,X1,X2))
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f437,plain,
    ( r2_hidden(sK4,sK8(sK4,sK7(sK4,sK3,sK5),sK3))
    | ~ spl9_21 ),
    inference(avatar_component_clause,[],[f435])).

fof(f435,plain,
    ( spl9_21
  <=> r2_hidden(sK4,sK8(sK4,sK7(sK4,sK3,sK5),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).

fof(f438,plain,
    ( spl9_20
    | spl9_21
    | spl9_1
    | ~ spl9_14
    | ~ spl9_18 ),
    inference(avatar_split_clause,[],[f421,f341,f289,f140,f435,f431])).

fof(f341,plain,
    ( spl9_18
  <=> ! [X3] :
        ( r1_orders_2(sK3,sK5,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK3))
        | ~ r3_orders_2(sK3,k1_yellow_0(sK3,sK7(sK4,sK3,sK5)),X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).

fof(f421,plain,
    ( r2_hidden(sK4,sK8(sK4,sK7(sK4,sK3,sK5),sK3))
    | v1_xboole_0(sK8(sK4,sK7(sK4,sK3,sK5),sK3))
    | spl9_1
    | ~ spl9_14
    | ~ spl9_18 ),
    inference(subsumption_resolution,[],[f420,f296])).

fof(f296,plain,
    ( v1_waybel_0(sK8(sK4,sK7(sK4,sK3,sK5),sK3),sK3)
    | ~ spl9_14 ),
    inference(resolution,[],[f291,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | v1_waybel_0(sK8(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f420,plain,
    ( r2_hidden(sK4,sK8(sK4,sK7(sK4,sK3,sK5),sK3))
    | ~ v1_waybel_0(sK8(sK4,sK7(sK4,sK3,sK5),sK3),sK3)
    | v1_xboole_0(sK8(sK4,sK7(sK4,sK3,sK5),sK3))
    | spl9_1
    | ~ spl9_14
    | ~ spl9_18 ),
    inference(subsumption_resolution,[],[f419,f297])).

fof(f297,plain,
    ( v12_waybel_0(sK8(sK4,sK7(sK4,sK3,sK5),sK3),sK3)
    | ~ spl9_14 ),
    inference(resolution,[],[f291,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | v12_waybel_0(sK8(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f419,plain,
    ( r2_hidden(sK4,sK8(sK4,sK7(sK4,sK3,sK5),sK3))
    | ~ v12_waybel_0(sK8(sK4,sK7(sK4,sK3,sK5),sK3),sK3)
    | ~ v1_waybel_0(sK8(sK4,sK7(sK4,sK3,sK5),sK3),sK3)
    | v1_xboole_0(sK8(sK4,sK7(sK4,sK3,sK5),sK3))
    | spl9_1
    | ~ spl9_14
    | ~ spl9_18 ),
    inference(subsumption_resolution,[],[f418,f299])).

fof(f299,plain,
    ( v1_waybel_7(sK8(sK4,sK7(sK4,sK3,sK5),sK3),sK3)
    | ~ spl9_14 ),
    inference(resolution,[],[f291,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | v1_waybel_7(sK8(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f418,plain,
    ( r2_hidden(sK4,sK8(sK4,sK7(sK4,sK3,sK5),sK3))
    | ~ v1_waybel_7(sK8(sK4,sK7(sK4,sK3,sK5),sK3),sK3)
    | ~ v12_waybel_0(sK8(sK4,sK7(sK4,sK3,sK5),sK3),sK3)
    | ~ v1_waybel_0(sK8(sK4,sK7(sK4,sK3,sK5),sK3),sK3)
    | v1_xboole_0(sK8(sK4,sK7(sK4,sK3,sK5),sK3))
    | spl9_1
    | ~ spl9_14
    | ~ spl9_18 ),
    inference(subsumption_resolution,[],[f415,f298])).

fof(f298,plain,
    ( m1_subset_1(sK8(sK4,sK7(sK4,sK3,sK5),sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl9_14 ),
    inference(resolution,[],[f291,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | m1_subset_1(sK8(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f415,plain,
    ( r2_hidden(sK4,sK8(sK4,sK7(sK4,sK3,sK5),sK3))
    | ~ m1_subset_1(sK8(sK4,sK7(sK4,sK3,sK5),sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_waybel_7(sK8(sK4,sK7(sK4,sK3,sK5),sK3),sK3)
    | ~ v12_waybel_0(sK8(sK4,sK7(sK4,sK3,sK5),sK3),sK3)
    | ~ v1_waybel_0(sK8(sK4,sK7(sK4,sK3,sK5),sK3),sK3)
    | v1_xboole_0(sK8(sK4,sK7(sK4,sK3,sK5),sK3))
    | spl9_1
    | ~ spl9_14
    | ~ spl9_18 ),
    inference(resolution,[],[f414,f300])).

fof(f300,plain,
    ( r1_tarski(sK7(sK4,sK3,sK5),sK8(sK4,sK7(sK4,sK3,sK5),sK3))
    | ~ spl9_14 ),
    inference(resolution,[],[f291,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | r1_tarski(X1,sK8(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f414,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK7(sK4,sK3,sK5),X0)
        | r2_hidden(sK4,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ v1_waybel_7(X0,sK3)
        | ~ v12_waybel_0(X0,sK3)
        | ~ v1_waybel_0(X0,sK3)
        | v1_xboole_0(X0) )
    | spl9_1
    | ~ spl9_18 ),
    inference(subsumption_resolution,[],[f413,f62])).

fof(f413,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK7(sK4,sK3,sK5),X0)
        | r2_hidden(sK4,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ v1_waybel_7(X0,sK3)
        | ~ v12_waybel_0(X0,sK3)
        | ~ v1_waybel_0(X0,sK3)
        | v1_xboole_0(X0)
        | ~ l1_orders_2(sK3) )
    | spl9_1
    | ~ spl9_18 ),
    inference(resolution,[],[f366,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_0)).

fof(f366,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_yellow_0(sK3,X0),u1_struct_0(sK3))
        | ~ r1_tarski(sK7(sK4,sK3,sK5),X0)
        | r2_hidden(sK4,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ v1_waybel_7(X0,sK3)
        | ~ v12_waybel_0(X0,sK3)
        | ~ v1_waybel_0(X0,sK3)
        | v1_xboole_0(X0) )
    | spl9_1
    | ~ spl9_18 ),
    inference(resolution,[],[f365,f319])).

fof(f319,plain,
    ( ! [X4] :
        ( ~ r3_orders_2(sK3,sK5,k1_yellow_0(sK3,X4))
        | r2_hidden(sK4,X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ v1_waybel_7(X4,sK3)
        | ~ v12_waybel_0(X4,sK3)
        | ~ v1_waybel_0(X4,sK3)
        | v1_xboole_0(X4) )
    | spl9_1 ),
    inference(subsumption_resolution,[],[f65,f142])).

fof(f142,plain,
    ( ~ r1_waybel_3(sK3,sK4,sK5)
    | spl9_1 ),
    inference(avatar_component_clause,[],[f140])).

fof(f65,plain,(
    ! [X4] :
      ( r2_hidden(sK4,X4)
      | ~ r3_orders_2(sK3,sK5,k1_yellow_0(sK3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ v1_waybel_7(X4,sK3)
      | ~ v12_waybel_0(X4,sK3)
      | ~ v1_waybel_0(X4,sK3)
      | v1_xboole_0(X4)
      | r1_waybel_3(sK3,sK4,sK5) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f365,plain,
    ( ! [X4] :
        ( r3_orders_2(sK3,sK5,k1_yellow_0(sK3,X4))
        | ~ m1_subset_1(k1_yellow_0(sK3,X4),u1_struct_0(sK3))
        | ~ r1_tarski(sK7(sK4,sK3,sK5),X4) )
    | ~ spl9_18 ),
    inference(subsumption_resolution,[],[f362,f64])).

fof(f362,plain,
    ( ! [X4] :
        ( ~ r1_tarski(sK7(sK4,sK3,sK5),X4)
        | ~ m1_subset_1(k1_yellow_0(sK3,X4),u1_struct_0(sK3))
        | ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | r3_orders_2(sK3,sK5,k1_yellow_0(sK3,X4)) )
    | ~ spl9_18 ),
    inference(resolution,[],[f359,f150])).

fof(f150,plain,(
    ! [X2,X3] :
      ( ~ r1_orders_2(sK3,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK3))
      | ~ m1_subset_1(X2,u1_struct_0(sK3))
      | r3_orders_2(sK3,X2,X3) ) ),
    inference(subsumption_resolution,[],[f104,f131])).

fof(f104,plain,(
    ! [X2,X3] :
      ( ~ r1_orders_2(sK3,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK3))
      | ~ m1_subset_1(X2,u1_struct_0(sK3))
      | r3_orders_2(sK3,X2,X3)
      | v2_struct_0(sK3) ) ),
    inference(global_subsumption,[],[f62,f102])).

fof(f102,plain,(
    ! [X2,X3] :
      ( ~ r1_orders_2(sK3,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK3))
      | ~ m1_subset_1(X2,u1_struct_0(sK3))
      | ~ l1_orders_2(sK3)
      | r3_orders_2(sK3,X2,X3)
      | v2_struct_0(sK3) ) ),
    inference(resolution,[],[f55,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_orders_2(X0)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r3_orders_2(X0,X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_orders_2(X0,X1,X2)
          | ~ r1_orders_2(X0,X1,X2) )
        & ( r1_orders_2(X0,X1,X2)
          | ~ r3_orders_2(X0,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(f359,plain,
    ( ! [X0] :
        ( r1_orders_2(sK3,sK5,k1_yellow_0(sK3,X0))
        | ~ r1_tarski(sK7(sK4,sK3,sK5),X0) )
    | ~ spl9_18 ),
    inference(subsumption_resolution,[],[f358,f62])).

fof(f358,plain,
    ( ! [X0] :
        ( r1_orders_2(sK3,sK5,k1_yellow_0(sK3,X0))
        | ~ r1_tarski(sK7(sK4,sK3,sK5),X0)
        | ~ l1_orders_2(sK3) )
    | ~ spl9_18 ),
    inference(resolution,[],[f356,f98])).

fof(f356,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_yellow_0(sK3,X0),u1_struct_0(sK3))
        | r1_orders_2(sK3,sK5,k1_yellow_0(sK3,X0))
        | ~ r1_tarski(sK7(sK4,sK3,sK5),X0) )
    | ~ spl9_18 ),
    inference(resolution,[],[f342,f120])).

fof(f120,plain,(
    ! [X0,X1] :
      ( r3_orders_2(sK3,k1_yellow_0(sK3,X0),k1_yellow_0(sK3,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(global_subsumption,[],[f62,f61,f60,f119])).

fof(f119,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ l1_orders_2(sK3)
      | ~ v3_lattice3(sK3)
      | ~ v2_lattice3(sK3)
      | r3_orders_2(sK3,k1_yellow_0(sK3,X0),k1_yellow_0(sK3,X1)) ) ),
    inference(subsumption_resolution,[],[f118,f55])).

fof(f118,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ l1_orders_2(sK3)
      | ~ v3_lattice3(sK3)
      | ~ v2_lattice3(sK3)
      | r3_orders_2(sK3,k1_yellow_0(sK3,X0),k1_yellow_0(sK3,X1))
      | ~ v3_orders_2(sK3) ) ),
    inference(subsumption_resolution,[],[f117,f56])).

fof(f117,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ l1_orders_2(sK3)
      | ~ v3_lattice3(sK3)
      | ~ v2_lattice3(sK3)
      | r3_orders_2(sK3,k1_yellow_0(sK3,X0),k1_yellow_0(sK3,X1))
      | ~ v4_orders_2(sK3)
      | ~ v3_orders_2(sK3) ) ),
    inference(subsumption_resolution,[],[f114,f57])).

fof(f57,plain,(
    v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f114,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ l1_orders_2(sK3)
      | ~ v3_lattice3(sK3)
      | ~ v2_lattice3(sK3)
      | r3_orders_2(sK3,k1_yellow_0(sK3,X0),k1_yellow_0(sK3,X1))
      | ~ v5_orders_2(sK3)
      | ~ v4_orders_2(sK3)
      | ~ v3_orders_2(sK3) ) ),
    inference(resolution,[],[f59,f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_lattice3(X0)
      | ~ r1_tarski(X1,X2)
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ v2_lattice3(X0)
      | r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
            & r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) )
          | ~ r1_tarski(X1,X2) )
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
            & r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) )
          | ~ r1_tarski(X1,X2) )
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_lattice3(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => ( r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
            & r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_waybel_7)).

fof(f59,plain,(
    v1_lattice3(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f61,plain,(
    v3_lattice3(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f342,plain,
    ( ! [X3] :
        ( ~ r3_orders_2(sK3,k1_yellow_0(sK3,sK7(sK4,sK3,sK5)),X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK3))
        | r1_orders_2(sK3,sK5,X3) )
    | ~ spl9_18 ),
    inference(avatar_component_clause,[],[f341])).

fof(f350,plain,(
    spl9_19 ),
    inference(avatar_contradiction_clause,[],[f349])).

fof(f349,plain,
    ( $false
    | spl9_19 ),
    inference(subsumption_resolution,[],[f348,f62])).

fof(f348,plain,
    ( ~ l1_orders_2(sK3)
    | spl9_19 ),
    inference(resolution,[],[f346,f98])).

fof(f346,plain,
    ( ~ m1_subset_1(k1_yellow_0(sK3,sK7(sK4,sK3,sK5)),u1_struct_0(sK3))
    | spl9_19 ),
    inference(avatar_component_clause,[],[f344])).

fof(f344,plain,
    ( spl9_19
  <=> m1_subset_1(k1_yellow_0(sK3,sK7(sK4,sK3,sK5)),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).

fof(f347,plain,
    ( spl9_18
    | ~ spl9_19
    | spl9_1 ),
    inference(avatar_split_clause,[],[f330,f140,f344,f341])).

fof(f330,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(k1_yellow_0(sK3,sK7(sK4,sK3,sK5)),u1_struct_0(sK3))
        | r1_orders_2(sK3,sK5,X3)
        | ~ r3_orders_2(sK3,k1_yellow_0(sK3,sK7(sK4,sK3,sK5)),X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK3)) )
    | spl9_1 ),
    inference(subsumption_resolution,[],[f329,f64])).

fof(f329,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(k1_yellow_0(sK3,sK7(sK4,sK3,sK5)),u1_struct_0(sK3))
        | ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | r1_orders_2(sK3,sK5,X3)
        | ~ r3_orders_2(sK3,k1_yellow_0(sK3,sK7(sK4,sK3,sK5)),X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK3)) )
    | spl9_1 ),
    inference(resolution,[],[f327,f277])).

fof(f277,plain,
    ( r3_orders_2(sK3,sK5,k1_yellow_0(sK3,sK7(sK4,sK3,sK5)))
    | spl9_1 ),
    inference(resolution,[],[f273,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | r3_orders_2(X1,X2,k1_yellow_0(X1,sK7(X0,X1,X2))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r2_hidden(X0,sK7(X0,X1,X2))
        & r3_orders_2(X1,X2,k1_yellow_0(X1,sK7(X0,X1,X2)))
        & m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
        & v12_waybel_0(sK7(X0,X1,X2),X1)
        & v1_waybel_0(sK7(X0,X1,X2),X1)
        & ~ v1_xboole_0(sK7(X0,X1,X2)) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f47,f48])).

fof(f48,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X0,X3)
          & r3_orders_2(X1,X2,k1_yellow_0(X1,X3))
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
          & v12_waybel_0(X3,X1)
          & v1_waybel_0(X3,X1)
          & ~ v1_xboole_0(X3) )
     => ( ~ r2_hidden(X0,sK7(X0,X1,X2))
        & r3_orders_2(X1,X2,k1_yellow_0(X1,sK7(X0,X1,X2)))
        & m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
        & v12_waybel_0(sK7(X0,X1,X2),X1)
        & v1_waybel_0(sK7(X0,X1,X2),X1)
        & ~ v1_xboole_0(sK7(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_hidden(X0,X3)
          & r3_orders_2(X1,X2,k1_yellow_0(X1,X3))
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
          & v12_waybel_0(X3,X1)
          & v1_waybel_0(X3,X1)
          & ~ v1_xboole_0(X3) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ! [X1,X0,X2] :
      ( ? [X3] :
          ( ~ r2_hidden(X1,X3)
          & r3_orders_2(X0,X2,k1_yellow_0(X0,X3))
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
          & v12_waybel_0(X3,X0)
          & v1_waybel_0(X3,X0)
          & ~ v1_xboole_0(X3) )
      | ~ sP1(X1,X0,X2) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X1,X0,X2] :
      ( ? [X3] :
          ( ~ r2_hidden(X1,X3)
          & r3_orders_2(X0,X2,k1_yellow_0(X0,X3))
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
          & v12_waybel_0(X3,X0)
          & v1_waybel_0(X3,X0)
          & ~ v1_xboole_0(X3) )
      | ~ sP1(X1,X0,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f273,plain,
    ( sP1(sK4,sK3,sK5)
    | spl9_1 ),
    inference(subsumption_resolution,[],[f162,f142])).

fof(f162,plain,
    ( sP1(sK4,sK3,sK5)
    | r1_waybel_3(sK3,sK4,sK5) ),
    inference(resolution,[],[f157,f64])).

fof(f157,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK3))
      | sP1(sK4,sK3,X2)
      | r1_waybel_3(sK3,sK4,X2) ) ),
    inference(resolution,[],[f155,f63])).

fof(f155,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
      | ~ m1_subset_1(X1,u1_struct_0(sK3))
      | sP1(X0,sK3,X1)
      | r1_waybel_3(sK3,X0,X1) ) ),
    inference(subsumption_resolution,[],[f154,f131])).

fof(f154,plain,(
    ! [X0,X1] :
      ( sP1(X0,sK3,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK3))
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | r1_waybel_3(sK3,X0,X1)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f113,f137])).

fof(f137,plain,(
    v24_waybel_0(sK3) ),
    inference(resolution,[],[f134,f76])).

fof(f76,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | v24_waybel_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ( v25_waybel_0(X0)
        & v24_waybel_0(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
      | ~ sP0(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( v25_waybel_0(X0)
        & v24_waybel_0(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
      | ~ sP0(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f134,plain,(
    sP0(sK3) ),
    inference(global_subsumption,[],[f62,f131,f133])).

fof(f133,plain,
    ( sP0(sK3)
    | v2_struct_0(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(subsumption_resolution,[],[f132,f55])).

fof(f132,plain,
    ( sP0(sK3)
    | ~ v3_orders_2(sK3)
    | v2_struct_0(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(resolution,[],[f61,f78])).

fof(f78,plain,(
    ! [X0] :
      ( ~ v3_lattice3(X0)
      | sP0(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( sP0(X0)
      | ~ v3_lattice3(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f17,f31])).

fof(f17,plain,(
    ! [X0] :
      ( ( v25_waybel_0(X0)
        & v24_waybel_0(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
      | ~ v3_lattice3(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v25_waybel_0(X0)
        & v24_waybel_0(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
      | ~ v3_lattice3(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( ( v3_lattice3(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ( v25_waybel_0(X0)
          & v24_waybel_0(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc11_waybel_0)).

fof(f113,plain,(
    ! [X0,X1] :
      ( sP1(X0,sK3,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK3))
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | ~ v24_waybel_0(sK3)
      | r1_waybel_3(sK3,X0,X1)
      | v2_struct_0(sK3) ) ),
    inference(global_subsumption,[],[f62,f112])).

fof(f112,plain,(
    ! [X0,X1] :
      ( sP1(X0,sK3,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK3))
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | ~ l1_orders_2(sK3)
      | ~ v24_waybel_0(sK3)
      | r1_waybel_3(sK3,X0,X1)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f111,f55])).

fof(f111,plain,(
    ! [X0,X1] :
      ( sP1(X0,sK3,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK3))
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | ~ l1_orders_2(sK3)
      | ~ v24_waybel_0(sK3)
      | r1_waybel_3(sK3,X0,X1)
      | ~ v3_orders_2(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f110,f56])).

fof(f110,plain,(
    ! [X0,X1] :
      ( sP1(X0,sK3,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK3))
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | ~ l1_orders_2(sK3)
      | ~ v24_waybel_0(sK3)
      | r1_waybel_3(sK3,X0,X1)
      | ~ v4_orders_2(sK3)
      | ~ v3_orders_2(sK3)
      | v2_struct_0(sK3) ) ),
    inference(resolution,[],[f57,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | sP1(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v24_waybel_0(X0)
      | r1_waybel_3(X0,X1,X2)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_waybel_3(X0,X1,X2)
              | sP1(X1,X0,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v24_waybel_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f19,f33])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_waybel_3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r2_hidden(X1,X3)
                  & r3_orders_2(X0,X2,k1_yellow_0(X0,X3))
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  & v12_waybel_0(X3,X0)
                  & v1_waybel_0(X3,X0)
                  & ~ v1_xboole_0(X3) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v24_waybel_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_waybel_3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r2_hidden(X1,X3)
                  & r3_orders_2(X0,X2,k1_yellow_0(X0,X3))
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  & v12_waybel_0(X3,X0)
                  & v1_waybel_0(X3,X0)
                  & ~ v1_xboole_0(X3) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v24_waybel_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v24_waybel_0(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                      & v12_waybel_0(X3,X0)
                      & v1_waybel_0(X3,X0)
                      & ~ v1_xboole_0(X3) )
                   => ( r3_orders_2(X0,X2,k1_yellow_0(X0,X3))
                     => r2_hidden(X1,X3) ) )
               => r1_waybel_3(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_waybel_3)).

fof(f327,plain,(
    ! [X4,X5,X3] :
      ( ~ r3_orders_2(sK3,X5,X4)
      | ~ m1_subset_1(X4,u1_struct_0(sK3))
      | ~ m1_subset_1(X5,u1_struct_0(sK3))
      | r1_orders_2(sK3,X5,X3)
      | ~ r3_orders_2(sK3,X4,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK3)) ) ),
    inference(duplicate_literal_removal,[],[f326])).

fof(f326,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(sK3))
      | ~ m1_subset_1(X4,u1_struct_0(sK3))
      | ~ m1_subset_1(X5,u1_struct_0(sK3))
      | r1_orders_2(sK3,X5,X3)
      | ~ r3_orders_2(sK3,X4,X3)
      | ~ m1_subset_1(X4,u1_struct_0(sK3))
      | ~ m1_subset_1(X5,u1_struct_0(sK3))
      | ~ r3_orders_2(sK3,X5,X4) ) ),
    inference(resolution,[],[f226,f148])).

fof(f148,plain,(
    ! [X0,X1] :
      ( r1_orders_2(sK3,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK3))
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | ~ r3_orders_2(sK3,X0,X1) ) ),
    inference(subsumption_resolution,[],[f103,f131])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ r3_orders_2(sK3,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK3))
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | r1_orders_2(sK3,X0,X1)
      | v2_struct_0(sK3) ) ),
    inference(global_subsumption,[],[f62,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ r3_orders_2(sK3,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK3))
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | ~ l1_orders_2(sK3)
      | r1_orders_2(sK3,X0,X1)
      | v2_struct_0(sK3) ) ),
    inference(resolution,[],[f55,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_orders_2(X0)
      | ~ r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f226,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_orders_2(sK3,X3,X4)
      | ~ m1_subset_1(X5,u1_struct_0(sK3))
      | ~ m1_subset_1(X4,u1_struct_0(sK3))
      | ~ m1_subset_1(X3,u1_struct_0(sK3))
      | r1_orders_2(sK3,X3,X5)
      | ~ r3_orders_2(sK3,X4,X5) ) ),
    inference(duplicate_literal_removal,[],[f225])).

fof(f225,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_orders_2(sK3,X3,X4)
      | ~ m1_subset_1(X5,u1_struct_0(sK3))
      | ~ m1_subset_1(X4,u1_struct_0(sK3))
      | ~ m1_subset_1(X3,u1_struct_0(sK3))
      | r1_orders_2(sK3,X3,X5)
      | ~ m1_subset_1(X5,u1_struct_0(sK3))
      | ~ m1_subset_1(X4,u1_struct_0(sK3))
      | ~ r3_orders_2(sK3,X4,X5) ) ),
    inference(resolution,[],[f107,f148])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(sK3,X0,X1)
      | ~ r1_orders_2(sK3,X2,X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK3))
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | ~ m1_subset_1(X2,u1_struct_0(sK3))
      | r1_orders_2(sK3,X2,X1) ) ),
    inference(global_subsumption,[],[f62,f105])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(sK3,X0,X1)
      | ~ r1_orders_2(sK3,X2,X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK3))
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | ~ m1_subset_1(X2,u1_struct_0(sK3))
      | ~ l1_orders_2(sK3)
      | r1_orders_2(sK3,X2,X1) ) ),
    inference(resolution,[],[f56,f87])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v4_orders_2(X0)
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,X1,X3) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X1,X3)
                  | ~ r1_orders_2(X0,X2,X3)
                  | ~ r1_orders_2(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X1,X3)
                  | ~ r1_orders_2(X0,X2,X3)
                  | ~ r1_orders_2(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X2) )
                   => r1_orders_2(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_orders_2)).

fof(f295,plain,
    ( spl9_1
    | ~ spl9_13 ),
    inference(avatar_contradiction_clause,[],[f294])).

fof(f294,plain,
    ( $false
    | spl9_1
    | ~ spl9_13 ),
    inference(subsumption_resolution,[],[f293,f273])).

fof(f293,plain,
    ( ~ sP1(sK4,sK3,sK5)
    | ~ spl9_13 ),
    inference(resolution,[],[f287,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,sK7(X0,X1,X2))
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f287,plain,
    ( r2_hidden(sK4,sK7(sK4,sK3,sK5))
    | ~ spl9_13 ),
    inference(avatar_component_clause,[],[f285])).

fof(f285,plain,
    ( spl9_13
  <=> r2_hidden(sK4,sK7(sK4,sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).

fof(f292,plain,
    ( spl9_13
    | spl9_14
    | ~ spl9_10 ),
    inference(avatar_split_clause,[],[f281,f235,f289,f285])).

fof(f235,plain,
    ( spl9_10
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK3))
        | sP2(X0,sK7(sK4,sK3,sK5),sK3)
        | r2_hidden(X0,sK7(sK4,sK3,sK5)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f281,plain,
    ( sP2(sK4,sK7(sK4,sK3,sK5),sK3)
    | r2_hidden(sK4,sK7(sK4,sK3,sK5))
    | ~ spl9_10 ),
    inference(resolution,[],[f236,f63])).

fof(f236,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK3))
        | sP2(X0,sK7(sK4,sK3,sK5),sK3)
        | r2_hidden(X0,sK7(sK4,sK3,sK5)) )
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f235])).

% (27896)ott+11_5:1_afp=100000:afq=1.1:br=off:gs=on:nm=64:nwc=1:sos=all:urr=on:updr=off_287 on theBenchmark
fof(f272,plain,
    ( spl9_1
    | ~ spl9_9 ),
    inference(avatar_contradiction_clause,[],[f271])).

fof(f271,plain,
    ( $false
    | spl9_1
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f270,f142])).

fof(f270,plain,
    ( r1_waybel_3(sK3,sK4,sK5)
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f162,f269])).

fof(f269,plain,
    ( ~ sP1(sK4,sK3,sK5)
    | ~ spl9_9 ),
    inference(resolution,[],[f233,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(sK7(X0,X1,X2))
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f233,plain,
    ( v1_xboole_0(sK7(sK4,sK3,sK5))
    | ~ spl9_9 ),
    inference(avatar_component_clause,[],[f231])).

fof(f231,plain,
    ( spl9_9
  <=> v1_xboole_0(sK7(sK4,sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f237,plain,
    ( spl9_9
    | spl9_10
    | spl9_1 ),
    inference(avatar_split_clause,[],[f229,f140,f235,f231])).

fof(f229,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK3))
        | r2_hidden(X0,sK7(sK4,sK3,sK5))
        | v1_xboole_0(sK7(sK4,sK3,sK5))
        | sP2(X0,sK7(sK4,sK3,sK5),sK3) )
    | spl9_1 ),
    inference(subsumption_resolution,[],[f228,f165])).

fof(f165,plain,
    ( v1_waybel_0(sK7(sK4,sK3,sK5),sK3)
    | spl9_1 ),
    inference(resolution,[],[f164,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | v1_waybel_0(sK7(X0,X1,X2),X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f164,plain,
    ( sP1(sK4,sK3,sK5)
    | spl9_1 ),
    inference(subsumption_resolution,[],[f162,f142])).

fof(f228,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK3))
        | r2_hidden(X0,sK7(sK4,sK3,sK5))
        | ~ v1_waybel_0(sK7(sK4,sK3,sK5),sK3)
        | v1_xboole_0(sK7(sK4,sK3,sK5))
        | sP2(X0,sK7(sK4,sK3,sK5),sK3) )
    | spl9_1 ),
    inference(subsumption_resolution,[],[f227,f167])).

fof(f167,plain,
    ( m1_subset_1(sK7(sK4,sK3,sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | spl9_1 ),
    inference(resolution,[],[f164,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f227,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(sK7(sK4,sK3,sK5),k1_zfmisc_1(u1_struct_0(sK3)))
        | r2_hidden(X0,sK7(sK4,sK3,sK5))
        | ~ v1_waybel_0(sK7(sK4,sK3,sK5),sK3)
        | v1_xboole_0(sK7(sK4,sK3,sK5))
        | sP2(X0,sK7(sK4,sK3,sK5),sK3) )
    | spl9_1 ),
    inference(resolution,[],[f129,f166])).

fof(f166,plain,
    ( v12_waybel_0(sK7(sK4,sK3,sK5),sK3)
    | spl9_1 ),
    inference(resolution,[],[f164,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | v12_waybel_0(sK7(X0,X1,X2),X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f129,plain,(
    ! [X4,X5] :
      ( ~ v12_waybel_0(X5,sK3)
      | ~ m1_subset_1(X4,u1_struct_0(sK3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK3)))
      | r2_hidden(X4,X5)
      | ~ v1_waybel_0(X5,sK3)
      | v1_xboole_0(X5)
      | sP2(X4,X5,sK3) ) ),
    inference(global_subsumption,[],[f62,f60,f128])).

fof(f128,plain,(
    ! [X4,X5] :
      ( r2_hidden(X4,X5)
      | ~ m1_subset_1(X4,u1_struct_0(sK3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ v12_waybel_0(X5,sK3)
      | ~ v1_waybel_0(X5,sK3)
      | v1_xboole_0(X5)
      | ~ l1_orders_2(sK3)
      | ~ v2_lattice3(sK3)
      | sP2(X4,X5,sK3) ) ),
    inference(subsumption_resolution,[],[f127,f55])).

fof(f127,plain,(
    ! [X4,X5] :
      ( r2_hidden(X4,X5)
      | ~ m1_subset_1(X4,u1_struct_0(sK3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ v12_waybel_0(X5,sK3)
      | ~ v1_waybel_0(X5,sK3)
      | v1_xboole_0(X5)
      | ~ l1_orders_2(sK3)
      | ~ v2_lattice3(sK3)
      | sP2(X4,X5,sK3)
      | ~ v3_orders_2(sK3) ) ),
    inference(subsumption_resolution,[],[f126,f56])).

fof(f126,plain,(
    ! [X4,X5] :
      ( r2_hidden(X4,X5)
      | ~ m1_subset_1(X4,u1_struct_0(sK3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ v12_waybel_0(X5,sK3)
      | ~ v1_waybel_0(X5,sK3)
      | v1_xboole_0(X5)
      | ~ l1_orders_2(sK3)
      | ~ v2_lattice3(sK3)
      | sP2(X4,X5,sK3)
      | ~ v4_orders_2(sK3)
      | ~ v3_orders_2(sK3) ) ),
    inference(subsumption_resolution,[],[f125,f57])).

fof(f125,plain,(
    ! [X4,X5] :
      ( r2_hidden(X4,X5)
      | ~ m1_subset_1(X4,u1_struct_0(sK3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ v12_waybel_0(X5,sK3)
      | ~ v1_waybel_0(X5,sK3)
      | v1_xboole_0(X5)
      | ~ l1_orders_2(sK3)
      | ~ v2_lattice3(sK3)
      | sP2(X4,X5,sK3)
      | ~ v5_orders_2(sK3)
      | ~ v4_orders_2(sK3)
      | ~ v3_orders_2(sK3) ) ),
    inference(subsumption_resolution,[],[f116,f58])).

fof(f58,plain,(
    v2_waybel_1(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f116,plain,(
    ! [X4,X5] :
      ( r2_hidden(X4,X5)
      | ~ m1_subset_1(X4,u1_struct_0(sK3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ v12_waybel_0(X5,sK3)
      | ~ v1_waybel_0(X5,sK3)
      | v1_xboole_0(X5)
      | ~ l1_orders_2(sK3)
      | ~ v2_lattice3(sK3)
      | sP2(X4,X5,sK3)
      | ~ v2_waybel_1(sK3)
      | ~ v5_orders_2(sK3)
      | ~ v4_orders_2(sK3)
      | ~ v3_orders_2(sK3) ) ),
    inference(resolution,[],[f59,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_lattice3(X0)
      | r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | sP2(X2,X1,X0)
      | ~ v2_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP2(X2,X1,X0)
              | r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
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
    inference(definition_folding,[],[f25,f35])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(X2,X3)
                  & r1_tarski(X1,X3)
                  & v1_waybel_7(X3,X0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  & v12_waybel_0(X3,X0)
                  & v1_waybel_0(X3,X0)
                  & ~ v1_xboole_0(X3) )
              | r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(X2,X3)
                  & r1_tarski(X1,X3)
                  & v1_waybel_7(X3,X0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  & v12_waybel_0(X3,X0)
                  & v1_waybel_0(X3,X0)
                  & ~ v1_xboole_0(X3) )
              | r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ~ ( ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                        & v12_waybel_0(X3,X0)
                        & v1_waybel_0(X3,X0)
                        & ~ v1_xboole_0(X3) )
                     => ~ ( ~ r2_hidden(X2,X3)
                          & r1_tarski(X1,X3)
                          & v1_waybel_7(X3,X0) ) )
                  & ~ r2_hidden(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_waybel_7)).

fof(f147,plain,
    ( ~ spl9_1
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f66,f144,f140])).

fof(f66,plain,
    ( ~ v1_xboole_0(sK6)
    | ~ r1_waybel_3(sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f44])).

%------------------------------------------------------------------------------
