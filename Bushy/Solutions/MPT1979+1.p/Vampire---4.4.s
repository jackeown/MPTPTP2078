%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : waybel_7__t28_waybel_7.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:05 EDT 2019

% Result     : Theorem 35.85s
% Output     : Refutation 35.85s
% Verified   : 
% Statistics : Number of formulae       :  258 (1756 expanded)
%              Number of leaves         :   17 ( 309 expanded)
%              Depth                    :   31
%              Number of atoms          : 1785 (21576 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   21 (   9 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f35479,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f35314,f35316,f35466])).

fof(f35466,plain,(
    ~ spl13_516 ),
    inference(avatar_contradiction_clause,[],[f35465])).

fof(f35465,plain,
    ( $false
    | ~ spl13_516 ),
    inference(subsumption_resolution,[],[f35464,f464])).

fof(f464,plain,(
    v2_waybel_0(k6_waybel_0(sK0,sK2),sK0) ),
    inference(subsumption_resolution,[],[f463,f100])).

fof(f100,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( r2_hidden(X2,X3)
                  | ~ r1_tarski(X1,X3)
                  | ~ v1_waybel_7(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  | ~ v12_waybel_0(X3,X0)
                  | ~ v1_waybel_0(X3,X0)
                  | v1_xboole_0(X3) )
              & ~ r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v12_waybel_0(X1,X0)
          & v1_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v2_waybel_1(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( r2_hidden(X2,X3)
                  | ~ r1_tarski(X1,X3)
                  | ~ v1_waybel_7(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  | ~ v12_waybel_0(X3,X0)
                  | ~ v1_waybel_0(X3,X0)
                  | v1_xboole_0(X3) )
              & ~ r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v12_waybel_0(X1,X0)
          & v1_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v2_waybel_1(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
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
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/waybel_7__t28_waybel_7.p',t28_waybel_7)).

fof(f463,plain,
    ( ~ l1_orders_2(sK0)
    | v2_waybel_0(k6_waybel_0(sK0,sK2),sK0) ),
    inference(subsumption_resolution,[],[f462,f94])).

fof(f94,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f462,plain,
    ( ~ v3_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | v2_waybel_0(k6_waybel_0(sK0,sK2),sK0) ),
    inference(subsumption_resolution,[],[f435,f285])).

fof(f285,plain,(
    ~ v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f277,f100])).

fof(f277,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v2_struct_0(sK0) ),
    inference(resolution,[],[f99,f102])).

fof(f102,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t28_waybel_7.p',cc2_lattice3)).

fof(f99,plain,(
    v2_lattice3(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f435,plain,
    ( v2_struct_0(sK0)
    | ~ v3_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | v2_waybel_0(k6_waybel_0(sK0,sK2),sK0) ),
    inference(resolution,[],[f88,f129])).

fof(f129,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_waybel_0(k6_waybel_0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( v2_waybel_0(k6_waybel_0(X0,X1),X0)
        & ~ v1_xboole_0(k6_waybel_0(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( v2_waybel_0(k6_waybel_0(X0,X1),X0)
        & ~ v1_xboole_0(k6_waybel_0(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f39])).

fof(f39,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_waybel_0(k6_waybel_0(X0,X1),X0)
        & ~ v1_xboole_0(k6_waybel_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t28_waybel_7.p',fc9_waybel_0)).

fof(f88,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f44])).

fof(f35464,plain,
    ( ~ v2_waybel_0(k6_waybel_0(sK0,sK2),sK0)
    | ~ spl13_516 ),
    inference(subsumption_resolution,[],[f35463,f461])).

fof(f461,plain,(
    ~ v1_xboole_0(k6_waybel_0(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f460,f100])).

fof(f460,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v1_xboole_0(k6_waybel_0(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f459,f94])).

fof(f459,plain,
    ( ~ v3_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ v1_xboole_0(k6_waybel_0(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f434,f285])).

fof(f434,plain,
    ( v2_struct_0(sK0)
    | ~ v3_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ v1_xboole_0(k6_waybel_0(sK0,sK2)) ),
    inference(resolution,[],[f88,f128])).

fof(f128,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v1_xboole_0(k6_waybel_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f35463,plain,
    ( v1_xboole_0(k6_waybel_0(sK0,sK2))
    | ~ v2_waybel_0(k6_waybel_0(sK0,sK2),sK0)
    | ~ spl13_516 ),
    inference(subsumption_resolution,[],[f35462,f20079])).

fof(f20079,plain,(
    r1_subset_1(sK1,k6_waybel_0(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f20069,f461])).

fof(f20069,plain,
    ( v1_xboole_0(k6_waybel_0(sK0,sK2))
    | r1_subset_1(sK1,k6_waybel_0(sK0,sK2)) ),
    inference(resolution,[],[f20006,f179])).

fof(f179,plain,(
    ! [X32] :
      ( ~ r1_xboole_0(sK1,X32)
      | v1_xboole_0(X32)
      | r1_subset_1(sK1,X32) ) ),
    inference(resolution,[],[f90,f133])).

fof(f133,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | ~ r1_xboole_0(X0,X1)
      | r1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t28_waybel_7.p',redefinition_r1_subset_1)).

fof(f90,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f20006,plain,(
    r1_xboole_0(sK1,k6_waybel_0(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f20005,f90])).

fof(f20005,plain,
    ( v1_xboole_0(sK1)
    | r1_xboole_0(sK1,k6_waybel_0(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f20004,f89])).

fof(f89,plain,(
    ~ r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f20004,plain,
    ( r2_hidden(sK2,sK1)
    | v1_xboole_0(sK1)
    | r1_xboole_0(sK1,k6_waybel_0(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f19987,f88])).

fof(f19987,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r2_hidden(sK2,sK1)
    | v1_xboole_0(sK1)
    | r1_xboole_0(sK1,k6_waybel_0(sK0,sK2)) ),
    inference(resolution,[],[f6623,f4069])).

fof(f4069,plain,(
    ! [X5] :
      ( ~ r1_subset_1(k6_waybel_0(sK0,sK2),X5)
      | v1_xboole_0(X5)
      | r1_xboole_0(X5,k6_waybel_0(sK0,sK2)) ) ),
    inference(subsumption_resolution,[],[f4065,f461])).

fof(f4065,plain,(
    ! [X5] :
      ( r1_xboole_0(X5,k6_waybel_0(sK0,sK2))
      | v1_xboole_0(X5)
      | v1_xboole_0(k6_waybel_0(sK0,sK2))
      | ~ r1_subset_1(k6_waybel_0(sK0,sK2),X5) ) ),
    inference(duplicate_literal_removal,[],[f4064])).

fof(f4064,plain,(
    ! [X5] :
      ( r1_xboole_0(X5,k6_waybel_0(sK0,sK2))
      | v1_xboole_0(X5)
      | v1_xboole_0(k6_waybel_0(sK0,sK2))
      | v1_xboole_0(X5)
      | ~ r1_subset_1(k6_waybel_0(sK0,sK2),X5) ) ),
    inference(resolution,[],[f635,f132])).

fof(f132,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | ~ r1_subset_1(X0,X1)
      | r1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_subset_1(X1,X0)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f68])).

fof(f68,plain,(
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
    file('/export/starexec/sandbox/benchmark/waybel_7__t28_waybel_7.p',symmetry_r1_subset_1)).

fof(f635,plain,(
    ! [X33] :
      ( ~ r1_subset_1(X33,k6_waybel_0(sK0,sK2))
      | r1_xboole_0(X33,k6_waybel_0(sK0,sK2))
      | v1_xboole_0(X33) ) ),
    inference(resolution,[],[f461,f134])).

fof(f134,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | r1_xboole_0(X0,X1)
      | ~ r1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f6623,plain,(
    ! [X14] :
      ( r1_subset_1(k6_waybel_0(sK0,X14),sK1)
      | ~ m1_subset_1(X14,u1_struct_0(sK0))
      | r2_hidden(X14,sK1) ) ),
    inference(subsumption_resolution,[],[f6622,f407])).

fof(f407,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ v1_xboole_0(k6_waybel_0(sK0,X5)) ) ),
    inference(subsumption_resolution,[],[f406,f100])).

fof(f406,plain,(
    ! [X5] :
      ( ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ v1_xboole_0(k6_waybel_0(sK0,X5)) ) ),
    inference(subsumption_resolution,[],[f398,f94])).

fof(f398,plain,(
    ! [X5] :
      ( ~ v3_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ v1_xboole_0(k6_waybel_0(sK0,X5)) ) ),
    inference(resolution,[],[f285,f128])).

fof(f6622,plain,(
    ! [X14] :
      ( r2_hidden(X14,sK1)
      | ~ m1_subset_1(X14,u1_struct_0(sK0))
      | r1_subset_1(k6_waybel_0(sK0,X14),sK1)
      | v1_xboole_0(k6_waybel_0(sK0,X14)) ) ),
    inference(subsumption_resolution,[],[f6621,f4409])).

fof(f4409,plain,(
    ! [X8] :
      ( m1_subset_1(sK7(k6_waybel_0(sK0,X8),sK1),u1_struct_0(sK0))
      | ~ m1_subset_1(X8,u1_struct_0(sK0))
      | r1_subset_1(k6_waybel_0(sK0,X8),sK1) ) ),
    inference(subsumption_resolution,[],[f4399,f407])).

fof(f4399,plain,(
    ! [X8] :
      ( ~ m1_subset_1(X8,u1_struct_0(sK0))
      | m1_subset_1(sK7(k6_waybel_0(sK0,X8),sK1),u1_struct_0(sK0))
      | r1_subset_1(k6_waybel_0(sK0,X8),sK1)
      | v1_xboole_0(k6_waybel_0(sK0,X8)) ) ),
    inference(resolution,[],[f1242,f1118])).

fof(f1118,plain,(
    ! [X2] :
      ( r2_hidden(sK7(X2,sK1),X2)
      | r1_subset_1(X2,sK1)
      | v1_xboole_0(X2) ) ),
    inference(resolution,[],[f178,f121])).

fof(f121,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK7(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t28_waybel_7.p',t3_xboole_0)).

fof(f178,plain,(
    ! [X31] :
      ( ~ r1_xboole_0(X31,sK1)
      | v1_xboole_0(X31)
      | r1_subset_1(X31,sK1) ) ),
    inference(resolution,[],[f90,f133])).

fof(f1242,plain,(
    ! [X39,X38] :
      ( ~ r2_hidden(X39,k6_waybel_0(sK0,X38))
      | ~ m1_subset_1(X38,u1_struct_0(sK0))
      | m1_subset_1(X39,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f313,f145])).

fof(f145,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f85])).

fof(f85,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f84])).

fof(f84,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t28_waybel_7.p',t4_subset)).

fof(f313,plain,(
    ! [X29] :
      ( m1_subset_1(k6_waybel_0(sK0,X29),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X29,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f305,f285])).

fof(f305,plain,(
    ! [X29] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X29,u1_struct_0(sK0))
      | m1_subset_1(k6_waybel_0(sK0,X29),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f100,f130])).

fof(f130,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | m1_subset_1(k6_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k6_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t28_waybel_7.p',dt_k6_waybel_0)).

fof(f6621,plain,(
    ! [X14] :
      ( ~ m1_subset_1(sK7(k6_waybel_0(sK0,X14),sK1),u1_struct_0(sK0))
      | r2_hidden(X14,sK1)
      | ~ m1_subset_1(X14,u1_struct_0(sK0))
      | r1_subset_1(k6_waybel_0(sK0,X14),sK1)
      | v1_xboole_0(k6_waybel_0(sK0,X14)) ) ),
    inference(subsumption_resolution,[],[f6604,f1119])).

fof(f1119,plain,(
    ! [X3] :
      ( r2_hidden(sK7(X3,sK1),sK1)
      | r1_subset_1(X3,sK1)
      | v1_xboole_0(X3) ) ),
    inference(resolution,[],[f178,f122])).

fof(f122,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK7(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f6604,plain,(
    ! [X14] :
      ( ~ r2_hidden(sK7(k6_waybel_0(sK0,X14),sK1),sK1)
      | ~ m1_subset_1(sK7(k6_waybel_0(sK0,X14),sK1),u1_struct_0(sK0))
      | r2_hidden(X14,sK1)
      | ~ m1_subset_1(X14,u1_struct_0(sK0))
      | r1_subset_1(k6_waybel_0(sK0,X14),sK1)
      | v1_xboole_0(k6_waybel_0(sK0,X14)) ) ),
    inference(resolution,[],[f2041,f1118])).

fof(f2041,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X5,k6_waybel_0(sK0,X4))
      | ~ r2_hidden(X5,sK1)
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | r2_hidden(X4,sK1)
      | ~ m1_subset_1(X4,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f2040,f100])).

fof(f2040,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ r2_hidden(X5,sK1)
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | r2_hidden(X4,sK1)
      | ~ l1_orders_2(sK0)
      | ~ r2_hidden(X5,k6_waybel_0(sK0,X4)) ) ),
    inference(subsumption_resolution,[],[f2032,f285])).

fof(f2032,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ r2_hidden(X5,sK1)
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | r2_hidden(X4,sK1)
      | v2_struct_0(sK0)
      | ~ l1_orders_2(sK0)
      | ~ r2_hidden(X5,k6_waybel_0(sK0,X4)) ) ),
    inference(duplicate_literal_removal,[],[f2031])).

fof(f2031,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ r2_hidden(X5,sK1)
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | r2_hidden(X4,sK1)
      | v2_struct_0(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ r2_hidden(X5,k6_waybel_0(sK0,X4)) ) ),
    inference(resolution,[],[f426,f111])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_orders_2(X0,X1,X2)
      | ~ r2_hidden(X2,k6_waybel_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k6_waybel_0(X0,X1))
              <=> r1_orders_2(X0,X1,X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k6_waybel_0(X0,X1))
              <=> r1_orders_2(X0,X1,X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k6_waybel_0(X0,X1))
              <=> r1_orders_2(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t28_waybel_7.p',t18_waybel_0)).

fof(f426,plain,(
    ! [X0,X1] :
      ( ~ r1_orders_2(sK0,X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X0,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X1,sK1) ) ),
    inference(subsumption_resolution,[],[f425,f93])).

fof(f93,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f44])).

fof(f425,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X0,sK1)
      | ~ r1_orders_2(sK0,X1,X0)
      | r2_hidden(X1,sK1) ) ),
    inference(subsumption_resolution,[],[f417,f100])).

fof(f417,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X0,sK1)
      | ~ r1_orders_2(sK0,X1,X0)
      | r2_hidden(X1,sK1) ) ),
    inference(resolution,[],[f92,f107])).

fof(f107,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_hidden(X2,X1)
      | ~ r1_orders_2(X0,X3,X2)
      | r2_hidden(X3,X1)
      | ~ v12_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v12_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X3,X2)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v12_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X3,X2)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v12_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r1_orders_2(X0,X3,X2)
                        & r2_hidden(X2,X1) )
                     => r2_hidden(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t28_waybel_7.p',d19_waybel_0)).

fof(f92,plain,(
    v12_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f35462,plain,
    ( ~ r1_subset_1(sK1,k6_waybel_0(sK0,sK2))
    | v1_xboole_0(k6_waybel_0(sK0,sK2))
    | ~ v2_waybel_0(k6_waybel_0(sK0,sK2),sK0)
    | ~ spl13_516 ),
    inference(subsumption_resolution,[],[f35461,f466])).

fof(f466,plain,(
    m1_subset_1(k6_waybel_0(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f465,f100])).

fof(f465,plain,
    ( ~ l1_orders_2(sK0)
    | m1_subset_1(k6_waybel_0(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f436,f285])).

fof(f436,plain,
    ( v2_struct_0(sK0)
    | ~ l1_orders_2(sK0)
    | m1_subset_1(k6_waybel_0(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f88,f130])).

fof(f35461,plain,
    ( ~ m1_subset_1(k6_waybel_0(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_subset_1(sK1,k6_waybel_0(sK0,sK2))
    | v1_xboole_0(k6_waybel_0(sK0,sK2))
    | ~ v2_waybel_0(k6_waybel_0(sK0,sK2),sK0)
    | ~ spl13_516 ),
    inference(subsumption_resolution,[],[f35460,f458])).

fof(f458,plain,(
    v13_waybel_0(k6_waybel_0(sK0,sK2),sK0) ),
    inference(subsumption_resolution,[],[f457,f100])).

fof(f457,plain,
    ( ~ l1_orders_2(sK0)
    | v13_waybel_0(k6_waybel_0(sK0,sK2),sK0) ),
    inference(subsumption_resolution,[],[f456,f95])).

fof(f95,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f456,plain,
    ( ~ v4_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | v13_waybel_0(k6_waybel_0(sK0,sK2),sK0) ),
    inference(subsumption_resolution,[],[f433,f285])).

fof(f433,plain,
    ( v2_struct_0(sK0)
    | ~ v4_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | v13_waybel_0(k6_waybel_0(sK0,sK2),sK0) ),
    inference(resolution,[],[f88,f127])).

fof(f127,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v4_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v13_waybel_0(k6_waybel_0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v13_waybel_0(k6_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v13_waybel_0(k6_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f38])).

fof(f38,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v4_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => v13_waybel_0(k6_waybel_0(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t28_waybel_7.p',fc13_waybel_0)).

fof(f35460,plain,
    ( ~ v13_waybel_0(k6_waybel_0(sK0,sK2),sK0)
    | ~ m1_subset_1(k6_waybel_0(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_subset_1(sK1,k6_waybel_0(sK0,sK2))
    | v1_xboole_0(k6_waybel_0(sK0,sK2))
    | ~ v2_waybel_0(k6_waybel_0(sK0,sK2),sK0)
    | ~ spl13_516 ),
    inference(subsumption_resolution,[],[f35459,f88])).

fof(f35459,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v13_waybel_0(k6_waybel_0(sK0,sK2),sK0)
    | ~ m1_subset_1(k6_waybel_0(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_subset_1(sK1,k6_waybel_0(sK0,sK2))
    | v1_xboole_0(k6_waybel_0(sK0,sK2))
    | ~ v2_waybel_0(k6_waybel_0(sK0,sK2),sK0)
    | ~ spl13_516 ),
    inference(subsumption_resolution,[],[f35438,f652])).

fof(f652,plain,(
    r1_orders_2(sK0,sK2,sK2) ),
    inference(subsumption_resolution,[],[f651,f88])).

fof(f651,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK2,sK2) ),
    inference(subsumption_resolution,[],[f650,f100])).

fof(f650,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK2,sK2) ),
    inference(subsumption_resolution,[],[f649,f94])).

fof(f649,plain,
    ( ~ v3_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK2,sK2) ),
    inference(subsumption_resolution,[],[f648,f285])).

fof(f648,plain,
    ( v2_struct_0(sK0)
    | ~ v3_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK2,sK2) ),
    inference(duplicate_literal_removal,[],[f647])).

fof(f647,plain,
    ( v2_struct_0(sK0)
    | ~ v3_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK2,sK2) ),
    inference(resolution,[],[f482,f144])).

fof(f144,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_orders_2(X0,X1,X2)
      | ~ r3_orders_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f83,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f82])).

fof(f82,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t28_waybel_7.p',redefinition_r3_orders_2)).

fof(f482,plain,(
    r3_orders_2(sK0,sK2,sK2) ),
    inference(subsumption_resolution,[],[f481,f441])).

fof(f441,plain,(
    sP10(sK0) ),
    inference(resolution,[],[f88,f150])).

fof(f150,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | sP10(X0) ) ),
    inference(cnf_transformation,[],[f150_D])).

fof(f150_D,plain,(
    ! [X0] :
      ( ! [X2] : ~ m1_subset_1(X2,u1_struct_0(X0))
    <=> ~ sP10(X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP10])])).

fof(f481,plain,
    ( r3_orders_2(sK0,sK2,sK2)
    | ~ sP10(sK0) ),
    inference(subsumption_resolution,[],[f480,f100])).

fof(f480,plain,
    ( ~ l1_orders_2(sK0)
    | r3_orders_2(sK0,sK2,sK2)
    | ~ sP10(sK0) ),
    inference(subsumption_resolution,[],[f479,f94])).

fof(f479,plain,
    ( ~ v3_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | r3_orders_2(sK0,sK2,sK2)
    | ~ sP10(sK0) ),
    inference(subsumption_resolution,[],[f442,f285])).

fof(f442,plain,
    ( v2_struct_0(sK0)
    | ~ v3_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | r3_orders_2(sK0,sK2,sK2)
    | ~ sP10(sK0) ),
    inference(resolution,[],[f88,f151])).

fof(f151,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r3_orders_2(X0,X1,X1)
      | ~ sP10(X0) ) ),
    inference(general_splitting,[],[f142,f150_D])).

fof(f142,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r3_orders_2(X0,X1,X1) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f80])).

fof(f80,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r3_orders_2(X0,X1,X1) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t28_waybel_7.p',reflexivity_r3_orders_2)).

fof(f35438,plain,
    ( ~ r1_orders_2(sK0,sK2,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v13_waybel_0(k6_waybel_0(sK0,sK2),sK0)
    | ~ m1_subset_1(k6_waybel_0(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_subset_1(sK1,k6_waybel_0(sK0,sK2))
    | v1_xboole_0(k6_waybel_0(sK0,sK2))
    | ~ v2_waybel_0(k6_waybel_0(sK0,sK2),sK0)
    | ~ spl13_516 ),
    inference(resolution,[],[f35313,f2314])).

fof(f2314,plain,(
    ! [X7] :
      ( r2_hidden(sK2,sK5(sK0,sK1,X7))
      | ~ v13_waybel_0(X7,sK0)
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(sK1,X7)
      | v1_xboole_0(X7)
      | ~ v2_waybel_0(X7,sK0) ) ),
    inference(subsumption_resolution,[],[f2313,f384])).

fof(f384,plain,(
    ! [X5] :
      ( r1_tarski(sK1,sK5(sK0,sK1,X5))
      | ~ v2_waybel_0(X5,sK0)
      | ~ v13_waybel_0(X5,sK0)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(sK1,X5)
      | v1_xboole_0(X5) ) ),
    inference(subsumption_resolution,[],[f383,f93])).

fof(f383,plain,(
    ! [X5] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X5)
      | ~ v2_waybel_0(X5,sK0)
      | ~ v13_waybel_0(X5,sK0)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(sK1,X5)
      | r1_tarski(sK1,sK5(sK0,sK1,X5)) ) ),
    inference(subsumption_resolution,[],[f382,f92])).

fof(f382,plain,(
    ! [X5] :
      ( ~ v12_waybel_0(sK1,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X5)
      | ~ v2_waybel_0(X5,sK0)
      | ~ v13_waybel_0(X5,sK0)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(sK1,X5)
      | r1_tarski(sK1,sK5(sK0,sK1,X5)) ) ),
    inference(subsumption_resolution,[],[f381,f90])).

fof(f381,plain,(
    ! [X5] :
      ( v1_xboole_0(sK1)
      | ~ v12_waybel_0(sK1,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X5)
      | ~ v2_waybel_0(X5,sK0)
      | ~ v13_waybel_0(X5,sK0)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(sK1,X5)
      | r1_tarski(sK1,sK5(sK0,sK1,X5)) ) ),
    inference(subsumption_resolution,[],[f380,f100])).

fof(f380,plain,(
    ! [X5] :
      ( ~ l1_orders_2(sK0)
      | v1_xboole_0(sK1)
      | ~ v12_waybel_0(sK1,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X5)
      | ~ v2_waybel_0(X5,sK0)
      | ~ v13_waybel_0(X5,sK0)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(sK1,X5)
      | r1_tarski(sK1,sK5(sK0,sK1,X5)) ) ),
    inference(subsumption_resolution,[],[f379,f99])).

fof(f379,plain,(
    ! [X5] :
      ( ~ v2_lattice3(sK0)
      | ~ l1_orders_2(sK0)
      | v1_xboole_0(sK1)
      | ~ v12_waybel_0(sK1,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X5)
      | ~ v2_waybel_0(X5,sK0)
      | ~ v13_waybel_0(X5,sK0)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(sK1,X5)
      | r1_tarski(sK1,sK5(sK0,sK1,X5)) ) ),
    inference(subsumption_resolution,[],[f378,f98])).

fof(f98,plain,(
    v1_lattice3(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f378,plain,(
    ! [X5] :
      ( ~ v1_lattice3(sK0)
      | ~ v2_lattice3(sK0)
      | ~ l1_orders_2(sK0)
      | v1_xboole_0(sK1)
      | ~ v12_waybel_0(sK1,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X5)
      | ~ v2_waybel_0(X5,sK0)
      | ~ v13_waybel_0(X5,sK0)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(sK1,X5)
      | r1_tarski(sK1,sK5(sK0,sK1,X5)) ) ),
    inference(subsumption_resolution,[],[f377,f97])).

fof(f97,plain,(
    v2_waybel_1(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f377,plain,(
    ! [X5] :
      ( ~ v2_waybel_1(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_lattice3(sK0)
      | ~ l1_orders_2(sK0)
      | v1_xboole_0(sK1)
      | ~ v12_waybel_0(sK1,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X5)
      | ~ v2_waybel_0(X5,sK0)
      | ~ v13_waybel_0(X5,sK0)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(sK1,X5)
      | r1_tarski(sK1,sK5(sK0,sK1,X5)) ) ),
    inference(subsumption_resolution,[],[f376,f96])).

fof(f96,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f376,plain,(
    ! [X5] :
      ( ~ v5_orders_2(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_lattice3(sK0)
      | ~ l1_orders_2(sK0)
      | v1_xboole_0(sK1)
      | ~ v12_waybel_0(sK1,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X5)
      | ~ v2_waybel_0(X5,sK0)
      | ~ v13_waybel_0(X5,sK0)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(sK1,X5)
      | r1_tarski(sK1,sK5(sK0,sK1,X5)) ) ),
    inference(subsumption_resolution,[],[f375,f95])).

fof(f375,plain,(
    ! [X5] :
      ( ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_lattice3(sK0)
      | ~ l1_orders_2(sK0)
      | v1_xboole_0(sK1)
      | ~ v12_waybel_0(sK1,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X5)
      | ~ v2_waybel_0(X5,sK0)
      | ~ v13_waybel_0(X5,sK0)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(sK1,X5)
      | r1_tarski(sK1,sK5(sK0,sK1,X5)) ) ),
    inference(subsumption_resolution,[],[f323,f94])).

fof(f323,plain,(
    ! [X5] :
      ( ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_lattice3(sK0)
      | ~ l1_orders_2(sK0)
      | v1_xboole_0(sK1)
      | ~ v12_waybel_0(sK1,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X5)
      | ~ v2_waybel_0(X5,sK0)
      | ~ v13_waybel_0(X5,sK0)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(sK1,X5)
      | r1_tarski(sK1,sK5(sK0,sK1,X5)) ) ),
    inference(resolution,[],[f91,f117])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v2_waybel_1(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | v1_xboole_0(X1)
      | ~ v1_waybel_0(X1,X0)
      | ~ v12_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X2)
      | ~ v2_waybel_0(X2,X0)
      | ~ v13_waybel_0(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_subset_1(X1,X2)
      | r1_tarski(X1,sK5(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( r1_subset_1(X3,X2)
                  & r1_tarski(X1,X3)
                  & v1_waybel_7(X3,X0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  & v12_waybel_0(X3,X0)
                  & v1_waybel_0(X3,X0)
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
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( r1_subset_1(X3,X2)
                  & r1_tarski(X1,X3)
                  & v1_waybel_7(X3,X0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  & v12_waybel_0(X3,X0)
                  & v1_waybel_0(X3,X0)
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
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
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
                        & v12_waybel_0(X3,X0)
                        & v1_waybel_0(X3,X0)
                        & ~ v1_xboole_0(X3) )
                     => ~ ( r1_subset_1(X3,X2)
                          & r1_tarski(X1,X3)
                          & v1_waybel_7(X3,X0) ) )
                  & r1_subset_1(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t28_waybel_7.p',t27_waybel_7)).

fof(f91,plain,(
    v1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f2313,plain,(
    ! [X7] :
      ( ~ v2_waybel_0(X7,sK0)
      | ~ v13_waybel_0(X7,sK0)
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(sK1,X7)
      | v1_xboole_0(X7)
      | ~ r1_tarski(sK1,sK5(sK0,sK1,X7))
      | r2_hidden(sK2,sK5(sK0,sK1,X7)) ) ),
    inference(subsumption_resolution,[],[f2312,f374])).

fof(f374,plain,(
    ! [X4] :
      ( v1_waybel_7(sK5(sK0,sK1,X4),sK0)
      | ~ v2_waybel_0(X4,sK0)
      | ~ v13_waybel_0(X4,sK0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(sK1,X4)
      | v1_xboole_0(X4) ) ),
    inference(subsumption_resolution,[],[f373,f93])).

fof(f373,plain,(
    ! [X4] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X4)
      | ~ v2_waybel_0(X4,sK0)
      | ~ v13_waybel_0(X4,sK0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(sK1,X4)
      | v1_waybel_7(sK5(sK0,sK1,X4),sK0) ) ),
    inference(subsumption_resolution,[],[f372,f92])).

fof(f372,plain,(
    ! [X4] :
      ( ~ v12_waybel_0(sK1,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X4)
      | ~ v2_waybel_0(X4,sK0)
      | ~ v13_waybel_0(X4,sK0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(sK1,X4)
      | v1_waybel_7(sK5(sK0,sK1,X4),sK0) ) ),
    inference(subsumption_resolution,[],[f371,f90])).

fof(f371,plain,(
    ! [X4] :
      ( v1_xboole_0(sK1)
      | ~ v12_waybel_0(sK1,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X4)
      | ~ v2_waybel_0(X4,sK0)
      | ~ v13_waybel_0(X4,sK0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(sK1,X4)
      | v1_waybel_7(sK5(sK0,sK1,X4),sK0) ) ),
    inference(subsumption_resolution,[],[f370,f100])).

fof(f370,plain,(
    ! [X4] :
      ( ~ l1_orders_2(sK0)
      | v1_xboole_0(sK1)
      | ~ v12_waybel_0(sK1,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X4)
      | ~ v2_waybel_0(X4,sK0)
      | ~ v13_waybel_0(X4,sK0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(sK1,X4)
      | v1_waybel_7(sK5(sK0,sK1,X4),sK0) ) ),
    inference(subsumption_resolution,[],[f369,f99])).

fof(f369,plain,(
    ! [X4] :
      ( ~ v2_lattice3(sK0)
      | ~ l1_orders_2(sK0)
      | v1_xboole_0(sK1)
      | ~ v12_waybel_0(sK1,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X4)
      | ~ v2_waybel_0(X4,sK0)
      | ~ v13_waybel_0(X4,sK0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(sK1,X4)
      | v1_waybel_7(sK5(sK0,sK1,X4),sK0) ) ),
    inference(subsumption_resolution,[],[f368,f98])).

fof(f368,plain,(
    ! [X4] :
      ( ~ v1_lattice3(sK0)
      | ~ v2_lattice3(sK0)
      | ~ l1_orders_2(sK0)
      | v1_xboole_0(sK1)
      | ~ v12_waybel_0(sK1,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X4)
      | ~ v2_waybel_0(X4,sK0)
      | ~ v13_waybel_0(X4,sK0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(sK1,X4)
      | v1_waybel_7(sK5(sK0,sK1,X4),sK0) ) ),
    inference(subsumption_resolution,[],[f367,f97])).

fof(f367,plain,(
    ! [X4] :
      ( ~ v2_waybel_1(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_lattice3(sK0)
      | ~ l1_orders_2(sK0)
      | v1_xboole_0(sK1)
      | ~ v12_waybel_0(sK1,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X4)
      | ~ v2_waybel_0(X4,sK0)
      | ~ v13_waybel_0(X4,sK0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(sK1,X4)
      | v1_waybel_7(sK5(sK0,sK1,X4),sK0) ) ),
    inference(subsumption_resolution,[],[f366,f96])).

fof(f366,plain,(
    ! [X4] :
      ( ~ v5_orders_2(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_lattice3(sK0)
      | ~ l1_orders_2(sK0)
      | v1_xboole_0(sK1)
      | ~ v12_waybel_0(sK1,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X4)
      | ~ v2_waybel_0(X4,sK0)
      | ~ v13_waybel_0(X4,sK0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(sK1,X4)
      | v1_waybel_7(sK5(sK0,sK1,X4),sK0) ) ),
    inference(subsumption_resolution,[],[f365,f95])).

fof(f365,plain,(
    ! [X4] :
      ( ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_lattice3(sK0)
      | ~ l1_orders_2(sK0)
      | v1_xboole_0(sK1)
      | ~ v12_waybel_0(sK1,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X4)
      | ~ v2_waybel_0(X4,sK0)
      | ~ v13_waybel_0(X4,sK0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(sK1,X4)
      | v1_waybel_7(sK5(sK0,sK1,X4),sK0) ) ),
    inference(subsumption_resolution,[],[f322,f94])).

fof(f322,plain,(
    ! [X4] :
      ( ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_lattice3(sK0)
      | ~ l1_orders_2(sK0)
      | v1_xboole_0(sK1)
      | ~ v12_waybel_0(sK1,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X4)
      | ~ v2_waybel_0(X4,sK0)
      | ~ v13_waybel_0(X4,sK0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(sK1,X4)
      | v1_waybel_7(sK5(sK0,sK1,X4),sK0) ) ),
    inference(resolution,[],[f91,f116])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v2_waybel_1(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | v1_xboole_0(X1)
      | ~ v1_waybel_0(X1,X0)
      | ~ v12_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X2)
      | ~ v2_waybel_0(X2,X0)
      | ~ v13_waybel_0(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_subset_1(X1,X2)
      | v1_waybel_7(sK5(X0,X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f2312,plain,(
    ! [X7] :
      ( ~ v2_waybel_0(X7,sK0)
      | ~ v13_waybel_0(X7,sK0)
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(sK1,X7)
      | v1_xboole_0(X7)
      | ~ v1_waybel_7(sK5(sK0,sK1,X7),sK0)
      | ~ r1_tarski(sK1,sK5(sK0,sK1,X7))
      | r2_hidden(sK2,sK5(sK0,sK1,X7)) ) ),
    inference(subsumption_resolution,[],[f2311,f334])).

fof(f334,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_waybel_0(X0,sK0)
      | ~ v13_waybel_0(X0,sK0)
      | v1_xboole_0(X0)
      | ~ r1_subset_1(sK1,X0)
      | ~ v1_xboole_0(sK5(sK0,sK1,X0)) ) ),
    inference(subsumption_resolution,[],[f333,f93])).

fof(f333,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X0)
      | ~ v2_waybel_0(X0,sK0)
      | ~ v13_waybel_0(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(sK1,X0)
      | ~ v1_xboole_0(sK5(sK0,sK1,X0)) ) ),
    inference(subsumption_resolution,[],[f332,f92])).

fof(f332,plain,(
    ! [X0] :
      ( ~ v12_waybel_0(sK1,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X0)
      | ~ v2_waybel_0(X0,sK0)
      | ~ v13_waybel_0(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(sK1,X0)
      | ~ v1_xboole_0(sK5(sK0,sK1,X0)) ) ),
    inference(subsumption_resolution,[],[f331,f90])).

fof(f331,plain,(
    ! [X0] :
      ( v1_xboole_0(sK1)
      | ~ v12_waybel_0(sK1,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X0)
      | ~ v2_waybel_0(X0,sK0)
      | ~ v13_waybel_0(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(sK1,X0)
      | ~ v1_xboole_0(sK5(sK0,sK1,X0)) ) ),
    inference(subsumption_resolution,[],[f330,f100])).

fof(f330,plain,(
    ! [X0] :
      ( ~ l1_orders_2(sK0)
      | v1_xboole_0(sK1)
      | ~ v12_waybel_0(sK1,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X0)
      | ~ v2_waybel_0(X0,sK0)
      | ~ v13_waybel_0(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(sK1,X0)
      | ~ v1_xboole_0(sK5(sK0,sK1,X0)) ) ),
    inference(subsumption_resolution,[],[f329,f99])).

fof(f329,plain,(
    ! [X0] :
      ( ~ v2_lattice3(sK0)
      | ~ l1_orders_2(sK0)
      | v1_xboole_0(sK1)
      | ~ v12_waybel_0(sK1,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X0)
      | ~ v2_waybel_0(X0,sK0)
      | ~ v13_waybel_0(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(sK1,X0)
      | ~ v1_xboole_0(sK5(sK0,sK1,X0)) ) ),
    inference(subsumption_resolution,[],[f328,f98])).

fof(f328,plain,(
    ! [X0] :
      ( ~ v1_lattice3(sK0)
      | ~ v2_lattice3(sK0)
      | ~ l1_orders_2(sK0)
      | v1_xboole_0(sK1)
      | ~ v12_waybel_0(sK1,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X0)
      | ~ v2_waybel_0(X0,sK0)
      | ~ v13_waybel_0(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(sK1,X0)
      | ~ v1_xboole_0(sK5(sK0,sK1,X0)) ) ),
    inference(subsumption_resolution,[],[f327,f97])).

fof(f327,plain,(
    ! [X0] :
      ( ~ v2_waybel_1(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_lattice3(sK0)
      | ~ l1_orders_2(sK0)
      | v1_xboole_0(sK1)
      | ~ v12_waybel_0(sK1,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X0)
      | ~ v2_waybel_0(X0,sK0)
      | ~ v13_waybel_0(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(sK1,X0)
      | ~ v1_xboole_0(sK5(sK0,sK1,X0)) ) ),
    inference(subsumption_resolution,[],[f326,f96])).

fof(f326,plain,(
    ! [X0] :
      ( ~ v5_orders_2(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_lattice3(sK0)
      | ~ l1_orders_2(sK0)
      | v1_xboole_0(sK1)
      | ~ v12_waybel_0(sK1,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X0)
      | ~ v2_waybel_0(X0,sK0)
      | ~ v13_waybel_0(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(sK1,X0)
      | ~ v1_xboole_0(sK5(sK0,sK1,X0)) ) ),
    inference(subsumption_resolution,[],[f325,f95])).

fof(f325,plain,(
    ! [X0] :
      ( ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_lattice3(sK0)
      | ~ l1_orders_2(sK0)
      | v1_xboole_0(sK1)
      | ~ v12_waybel_0(sK1,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X0)
      | ~ v2_waybel_0(X0,sK0)
      | ~ v13_waybel_0(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(sK1,X0)
      | ~ v1_xboole_0(sK5(sK0,sK1,X0)) ) ),
    inference(subsumption_resolution,[],[f318,f94])).

fof(f318,plain,(
    ! [X0] :
      ( ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_lattice3(sK0)
      | ~ l1_orders_2(sK0)
      | v1_xboole_0(sK1)
      | ~ v12_waybel_0(sK1,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X0)
      | ~ v2_waybel_0(X0,sK0)
      | ~ v13_waybel_0(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(sK1,X0)
      | ~ v1_xboole_0(sK5(sK0,sK1,X0)) ) ),
    inference(resolution,[],[f91,f112])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v2_waybel_1(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | v1_xboole_0(X1)
      | ~ v1_waybel_0(X1,X0)
      | ~ v12_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X2)
      | ~ v2_waybel_0(X2,X0)
      | ~ v13_waybel_0(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_subset_1(X1,X2)
      | ~ v1_xboole_0(sK5(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f2311,plain,(
    ! [X7] :
      ( ~ v2_waybel_0(X7,sK0)
      | ~ v13_waybel_0(X7,sK0)
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(sK1,X7)
      | v1_xboole_0(X7)
      | v1_xboole_0(sK5(sK0,sK1,X7))
      | ~ v1_waybel_7(sK5(sK0,sK1,X7),sK0)
      | ~ r1_tarski(sK1,sK5(sK0,sK1,X7))
      | r2_hidden(sK2,sK5(sK0,sK1,X7)) ) ),
    inference(subsumption_resolution,[],[f2310,f354])).

fof(f354,plain,(
    ! [X2] :
      ( v12_waybel_0(sK5(sK0,sK1,X2),sK0)
      | ~ v2_waybel_0(X2,sK0)
      | ~ v13_waybel_0(X2,sK0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(sK1,X2)
      | v1_xboole_0(X2) ) ),
    inference(subsumption_resolution,[],[f353,f93])).

fof(f353,plain,(
    ! [X2] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X2)
      | ~ v2_waybel_0(X2,sK0)
      | ~ v13_waybel_0(X2,sK0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(sK1,X2)
      | v12_waybel_0(sK5(sK0,sK1,X2),sK0) ) ),
    inference(subsumption_resolution,[],[f352,f92])).

fof(f352,plain,(
    ! [X2] :
      ( ~ v12_waybel_0(sK1,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X2)
      | ~ v2_waybel_0(X2,sK0)
      | ~ v13_waybel_0(X2,sK0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(sK1,X2)
      | v12_waybel_0(sK5(sK0,sK1,X2),sK0) ) ),
    inference(subsumption_resolution,[],[f351,f90])).

fof(f351,plain,(
    ! [X2] :
      ( v1_xboole_0(sK1)
      | ~ v12_waybel_0(sK1,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X2)
      | ~ v2_waybel_0(X2,sK0)
      | ~ v13_waybel_0(X2,sK0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(sK1,X2)
      | v12_waybel_0(sK5(sK0,sK1,X2),sK0) ) ),
    inference(subsumption_resolution,[],[f350,f100])).

fof(f350,plain,(
    ! [X2] :
      ( ~ l1_orders_2(sK0)
      | v1_xboole_0(sK1)
      | ~ v12_waybel_0(sK1,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X2)
      | ~ v2_waybel_0(X2,sK0)
      | ~ v13_waybel_0(X2,sK0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(sK1,X2)
      | v12_waybel_0(sK5(sK0,sK1,X2),sK0) ) ),
    inference(subsumption_resolution,[],[f349,f99])).

fof(f349,plain,(
    ! [X2] :
      ( ~ v2_lattice3(sK0)
      | ~ l1_orders_2(sK0)
      | v1_xboole_0(sK1)
      | ~ v12_waybel_0(sK1,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X2)
      | ~ v2_waybel_0(X2,sK0)
      | ~ v13_waybel_0(X2,sK0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(sK1,X2)
      | v12_waybel_0(sK5(sK0,sK1,X2),sK0) ) ),
    inference(subsumption_resolution,[],[f348,f98])).

fof(f348,plain,(
    ! [X2] :
      ( ~ v1_lattice3(sK0)
      | ~ v2_lattice3(sK0)
      | ~ l1_orders_2(sK0)
      | v1_xboole_0(sK1)
      | ~ v12_waybel_0(sK1,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X2)
      | ~ v2_waybel_0(X2,sK0)
      | ~ v13_waybel_0(X2,sK0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(sK1,X2)
      | v12_waybel_0(sK5(sK0,sK1,X2),sK0) ) ),
    inference(subsumption_resolution,[],[f347,f97])).

fof(f347,plain,(
    ! [X2] :
      ( ~ v2_waybel_1(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_lattice3(sK0)
      | ~ l1_orders_2(sK0)
      | v1_xboole_0(sK1)
      | ~ v12_waybel_0(sK1,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X2)
      | ~ v2_waybel_0(X2,sK0)
      | ~ v13_waybel_0(X2,sK0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(sK1,X2)
      | v12_waybel_0(sK5(sK0,sK1,X2),sK0) ) ),
    inference(subsumption_resolution,[],[f346,f96])).

fof(f346,plain,(
    ! [X2] :
      ( ~ v5_orders_2(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_lattice3(sK0)
      | ~ l1_orders_2(sK0)
      | v1_xboole_0(sK1)
      | ~ v12_waybel_0(sK1,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X2)
      | ~ v2_waybel_0(X2,sK0)
      | ~ v13_waybel_0(X2,sK0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(sK1,X2)
      | v12_waybel_0(sK5(sK0,sK1,X2),sK0) ) ),
    inference(subsumption_resolution,[],[f345,f95])).

fof(f345,plain,(
    ! [X2] :
      ( ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_lattice3(sK0)
      | ~ l1_orders_2(sK0)
      | v1_xboole_0(sK1)
      | ~ v12_waybel_0(sK1,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X2)
      | ~ v2_waybel_0(X2,sK0)
      | ~ v13_waybel_0(X2,sK0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(sK1,X2)
      | v12_waybel_0(sK5(sK0,sK1,X2),sK0) ) ),
    inference(subsumption_resolution,[],[f320,f94])).

fof(f320,plain,(
    ! [X2] :
      ( ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_lattice3(sK0)
      | ~ l1_orders_2(sK0)
      | v1_xboole_0(sK1)
      | ~ v12_waybel_0(sK1,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X2)
      | ~ v2_waybel_0(X2,sK0)
      | ~ v13_waybel_0(X2,sK0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(sK1,X2)
      | v12_waybel_0(sK5(sK0,sK1,X2),sK0) ) ),
    inference(resolution,[],[f91,f114])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v2_waybel_1(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | v1_xboole_0(X1)
      | ~ v1_waybel_0(X1,X0)
      | ~ v12_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X2)
      | ~ v2_waybel_0(X2,X0)
      | ~ v13_waybel_0(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_subset_1(X1,X2)
      | v12_waybel_0(sK5(X0,X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f2310,plain,(
    ! [X7] :
      ( ~ v2_waybel_0(X7,sK0)
      | ~ v13_waybel_0(X7,sK0)
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(sK1,X7)
      | v1_xboole_0(X7)
      | ~ v12_waybel_0(sK5(sK0,sK1,X7),sK0)
      | v1_xboole_0(sK5(sK0,sK1,X7))
      | ~ v1_waybel_7(sK5(sK0,sK1,X7),sK0)
      | ~ r1_tarski(sK1,sK5(sK0,sK1,X7))
      | r2_hidden(sK2,sK5(sK0,sK1,X7)) ) ),
    inference(subsumption_resolution,[],[f2280,f344])).

fof(f344,plain,(
    ! [X1] :
      ( v1_waybel_0(sK5(sK0,sK1,X1),sK0)
      | ~ v2_waybel_0(X1,sK0)
      | ~ v13_waybel_0(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(sK1,X1)
      | v1_xboole_0(X1) ) ),
    inference(subsumption_resolution,[],[f343,f93])).

fof(f343,plain,(
    ! [X1] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X1)
      | ~ v2_waybel_0(X1,sK0)
      | ~ v13_waybel_0(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(sK1,X1)
      | v1_waybel_0(sK5(sK0,sK1,X1),sK0) ) ),
    inference(subsumption_resolution,[],[f342,f92])).

fof(f342,plain,(
    ! [X1] :
      ( ~ v12_waybel_0(sK1,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X1)
      | ~ v2_waybel_0(X1,sK0)
      | ~ v13_waybel_0(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(sK1,X1)
      | v1_waybel_0(sK5(sK0,sK1,X1),sK0) ) ),
    inference(subsumption_resolution,[],[f341,f90])).

fof(f341,plain,(
    ! [X1] :
      ( v1_xboole_0(sK1)
      | ~ v12_waybel_0(sK1,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X1)
      | ~ v2_waybel_0(X1,sK0)
      | ~ v13_waybel_0(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(sK1,X1)
      | v1_waybel_0(sK5(sK0,sK1,X1),sK0) ) ),
    inference(subsumption_resolution,[],[f340,f100])).

fof(f340,plain,(
    ! [X1] :
      ( ~ l1_orders_2(sK0)
      | v1_xboole_0(sK1)
      | ~ v12_waybel_0(sK1,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X1)
      | ~ v2_waybel_0(X1,sK0)
      | ~ v13_waybel_0(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(sK1,X1)
      | v1_waybel_0(sK5(sK0,sK1,X1),sK0) ) ),
    inference(subsumption_resolution,[],[f339,f99])).

fof(f339,plain,(
    ! [X1] :
      ( ~ v2_lattice3(sK0)
      | ~ l1_orders_2(sK0)
      | v1_xboole_0(sK1)
      | ~ v12_waybel_0(sK1,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X1)
      | ~ v2_waybel_0(X1,sK0)
      | ~ v13_waybel_0(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(sK1,X1)
      | v1_waybel_0(sK5(sK0,sK1,X1),sK0) ) ),
    inference(subsumption_resolution,[],[f338,f98])).

fof(f338,plain,(
    ! [X1] :
      ( ~ v1_lattice3(sK0)
      | ~ v2_lattice3(sK0)
      | ~ l1_orders_2(sK0)
      | v1_xboole_0(sK1)
      | ~ v12_waybel_0(sK1,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X1)
      | ~ v2_waybel_0(X1,sK0)
      | ~ v13_waybel_0(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(sK1,X1)
      | v1_waybel_0(sK5(sK0,sK1,X1),sK0) ) ),
    inference(subsumption_resolution,[],[f337,f97])).

fof(f337,plain,(
    ! [X1] :
      ( ~ v2_waybel_1(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_lattice3(sK0)
      | ~ l1_orders_2(sK0)
      | v1_xboole_0(sK1)
      | ~ v12_waybel_0(sK1,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X1)
      | ~ v2_waybel_0(X1,sK0)
      | ~ v13_waybel_0(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(sK1,X1)
      | v1_waybel_0(sK5(sK0,sK1,X1),sK0) ) ),
    inference(subsumption_resolution,[],[f336,f96])).

fof(f336,plain,(
    ! [X1] :
      ( ~ v5_orders_2(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_lattice3(sK0)
      | ~ l1_orders_2(sK0)
      | v1_xboole_0(sK1)
      | ~ v12_waybel_0(sK1,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X1)
      | ~ v2_waybel_0(X1,sK0)
      | ~ v13_waybel_0(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(sK1,X1)
      | v1_waybel_0(sK5(sK0,sK1,X1),sK0) ) ),
    inference(subsumption_resolution,[],[f335,f95])).

fof(f335,plain,(
    ! [X1] :
      ( ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_lattice3(sK0)
      | ~ l1_orders_2(sK0)
      | v1_xboole_0(sK1)
      | ~ v12_waybel_0(sK1,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X1)
      | ~ v2_waybel_0(X1,sK0)
      | ~ v13_waybel_0(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(sK1,X1)
      | v1_waybel_0(sK5(sK0,sK1,X1),sK0) ) ),
    inference(subsumption_resolution,[],[f319,f94])).

fof(f319,plain,(
    ! [X1] :
      ( ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_lattice3(sK0)
      | ~ l1_orders_2(sK0)
      | v1_xboole_0(sK1)
      | ~ v12_waybel_0(sK1,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X1)
      | ~ v2_waybel_0(X1,sK0)
      | ~ v13_waybel_0(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(sK1,X1)
      | v1_waybel_0(sK5(sK0,sK1,X1),sK0) ) ),
    inference(resolution,[],[f91,f113])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v2_waybel_1(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | v1_xboole_0(X1)
      | ~ v1_waybel_0(X1,X0)
      | ~ v12_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X2)
      | ~ v2_waybel_0(X2,X0)
      | ~ v13_waybel_0(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_subset_1(X1,X2)
      | v1_waybel_0(sK5(X0,X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f2280,plain,(
    ! [X7] :
      ( ~ v2_waybel_0(X7,sK0)
      | ~ v13_waybel_0(X7,sK0)
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(sK1,X7)
      | v1_xboole_0(X7)
      | ~ v1_waybel_0(sK5(sK0,sK1,X7),sK0)
      | ~ v12_waybel_0(sK5(sK0,sK1,X7),sK0)
      | v1_xboole_0(sK5(sK0,sK1,X7))
      | ~ v1_waybel_7(sK5(sK0,sK1,X7),sK0)
      | ~ r1_tarski(sK1,sK5(sK0,sK1,X7))
      | r2_hidden(sK2,sK5(sK0,sK1,X7)) ) ),
    inference(resolution,[],[f364,f87])).

fof(f87,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v1_waybel_0(X3,sK0)
      | ~ v12_waybel_0(X3,sK0)
      | v1_xboole_0(X3)
      | ~ v1_waybel_7(X3,sK0)
      | ~ r1_tarski(sK1,X3)
      | r2_hidden(sK2,X3) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f364,plain,(
    ! [X3] :
      ( m1_subset_1(sK5(sK0,sK1,X3),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_waybel_0(X3,sK0)
      | ~ v13_waybel_0(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(sK1,X3)
      | v1_xboole_0(X3) ) ),
    inference(subsumption_resolution,[],[f363,f93])).

fof(f363,plain,(
    ! [X3] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X3)
      | ~ v2_waybel_0(X3,sK0)
      | ~ v13_waybel_0(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(sK1,X3)
      | m1_subset_1(sK5(sK0,sK1,X3),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f362,f92])).

fof(f362,plain,(
    ! [X3] :
      ( ~ v12_waybel_0(sK1,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X3)
      | ~ v2_waybel_0(X3,sK0)
      | ~ v13_waybel_0(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(sK1,X3)
      | m1_subset_1(sK5(sK0,sK1,X3),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f361,f90])).

fof(f361,plain,(
    ! [X3] :
      ( v1_xboole_0(sK1)
      | ~ v12_waybel_0(sK1,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X3)
      | ~ v2_waybel_0(X3,sK0)
      | ~ v13_waybel_0(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(sK1,X3)
      | m1_subset_1(sK5(sK0,sK1,X3),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f360,f100])).

fof(f360,plain,(
    ! [X3] :
      ( ~ l1_orders_2(sK0)
      | v1_xboole_0(sK1)
      | ~ v12_waybel_0(sK1,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X3)
      | ~ v2_waybel_0(X3,sK0)
      | ~ v13_waybel_0(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(sK1,X3)
      | m1_subset_1(sK5(sK0,sK1,X3),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f359,f99])).

fof(f359,plain,(
    ! [X3] :
      ( ~ v2_lattice3(sK0)
      | ~ l1_orders_2(sK0)
      | v1_xboole_0(sK1)
      | ~ v12_waybel_0(sK1,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X3)
      | ~ v2_waybel_0(X3,sK0)
      | ~ v13_waybel_0(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(sK1,X3)
      | m1_subset_1(sK5(sK0,sK1,X3),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f358,f98])).

fof(f358,plain,(
    ! [X3] :
      ( ~ v1_lattice3(sK0)
      | ~ v2_lattice3(sK0)
      | ~ l1_orders_2(sK0)
      | v1_xboole_0(sK1)
      | ~ v12_waybel_0(sK1,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X3)
      | ~ v2_waybel_0(X3,sK0)
      | ~ v13_waybel_0(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(sK1,X3)
      | m1_subset_1(sK5(sK0,sK1,X3),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f357,f97])).

fof(f357,plain,(
    ! [X3] :
      ( ~ v2_waybel_1(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_lattice3(sK0)
      | ~ l1_orders_2(sK0)
      | v1_xboole_0(sK1)
      | ~ v12_waybel_0(sK1,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X3)
      | ~ v2_waybel_0(X3,sK0)
      | ~ v13_waybel_0(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(sK1,X3)
      | m1_subset_1(sK5(sK0,sK1,X3),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f356,f96])).

fof(f356,plain,(
    ! [X3] :
      ( ~ v5_orders_2(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_lattice3(sK0)
      | ~ l1_orders_2(sK0)
      | v1_xboole_0(sK1)
      | ~ v12_waybel_0(sK1,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X3)
      | ~ v2_waybel_0(X3,sK0)
      | ~ v13_waybel_0(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(sK1,X3)
      | m1_subset_1(sK5(sK0,sK1,X3),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f355,f95])).

fof(f355,plain,(
    ! [X3] :
      ( ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_lattice3(sK0)
      | ~ l1_orders_2(sK0)
      | v1_xboole_0(sK1)
      | ~ v12_waybel_0(sK1,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X3)
      | ~ v2_waybel_0(X3,sK0)
      | ~ v13_waybel_0(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(sK1,X3)
      | m1_subset_1(sK5(sK0,sK1,X3),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f321,f94])).

fof(f321,plain,(
    ! [X3] :
      ( ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_lattice3(sK0)
      | ~ l1_orders_2(sK0)
      | v1_xboole_0(sK1)
      | ~ v12_waybel_0(sK1,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X3)
      | ~ v2_waybel_0(X3,sK0)
      | ~ v13_waybel_0(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(sK1,X3)
      | m1_subset_1(sK5(sK0,sK1,X3),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f91,f115])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v2_waybel_1(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | v1_xboole_0(X1)
      | ~ v1_waybel_0(X1,X0)
      | ~ v12_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X2)
      | ~ v2_waybel_0(X2,X0)
      | ~ v13_waybel_0(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_subset_1(X1,X2)
      | m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f35313,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,sK5(sK0,sK1,k6_waybel_0(sK0,sK2)))
        | ~ r1_orders_2(sK0,sK2,X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
    | ~ spl13_516 ),
    inference(avatar_component_clause,[],[f35312])).

fof(f35312,plain,
    ( spl13_516
  <=> ! [X4] :
        ( ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2,X4)
        | ~ r2_hidden(X4,sK5(sK0,sK1,k6_waybel_0(sK0,sK2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_516])])).

fof(f35316,plain,(
    spl13_97 ),
    inference(avatar_contradiction_clause,[],[f35315])).

fof(f35315,plain,
    ( $false
    | ~ spl13_97 ),
    inference(subsumption_resolution,[],[f4155,f20079])).

fof(f4155,plain,
    ( ~ r1_subset_1(sK1,k6_waybel_0(sK0,sK2))
    | ~ spl13_97 ),
    inference(avatar_component_clause,[],[f4154])).

fof(f4154,plain,
    ( spl13_97
  <=> ~ r1_subset_1(sK1,k6_waybel_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_97])])).

fof(f35314,plain,
    ( spl13_516
    | ~ spl13_97 ),
    inference(avatar_split_clause,[],[f7394,f4154,f35312])).

fof(f7394,plain,(
    ! [X4] :
      ( ~ r1_subset_1(sK1,k6_waybel_0(sK0,sK2))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ r2_hidden(X4,sK5(sK0,sK1,k6_waybel_0(sK0,sK2)))
      | ~ r1_orders_2(sK0,sK2,X4) ) ),
    inference(subsumption_resolution,[],[f7393,f464])).

fof(f7393,plain,(
    ! [X4] :
      ( ~ r1_subset_1(sK1,k6_waybel_0(sK0,sK2))
      | ~ v2_waybel_0(k6_waybel_0(sK0,sK2),sK0)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ r2_hidden(X4,sK5(sK0,sK1,k6_waybel_0(sK0,sK2)))
      | ~ r1_orders_2(sK0,sK2,X4) ) ),
    inference(subsumption_resolution,[],[f7392,f461])).

fof(f7392,plain,(
    ! [X4] :
      ( ~ r1_subset_1(sK1,k6_waybel_0(sK0,sK2))
      | v1_xboole_0(k6_waybel_0(sK0,sK2))
      | ~ v2_waybel_0(k6_waybel_0(sK0,sK2),sK0)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ r2_hidden(X4,sK5(sK0,sK1,k6_waybel_0(sK0,sK2)))
      | ~ r1_orders_2(sK0,sK2,X4) ) ),
    inference(subsumption_resolution,[],[f7391,f466])).

fof(f7391,plain,(
    ! [X4] :
      ( ~ m1_subset_1(k6_waybel_0(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(sK1,k6_waybel_0(sK0,sK2))
      | v1_xboole_0(k6_waybel_0(sK0,sK2))
      | ~ v2_waybel_0(k6_waybel_0(sK0,sK2),sK0)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ r2_hidden(X4,sK5(sK0,sK1,k6_waybel_0(sK0,sK2)))
      | ~ r1_orders_2(sK0,sK2,X4) ) ),
    inference(subsumption_resolution,[],[f7382,f458])).

fof(f7382,plain,(
    ! [X4] :
      ( ~ v13_waybel_0(k6_waybel_0(sK0,sK2),sK0)
      | ~ m1_subset_1(k6_waybel_0(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(sK1,k6_waybel_0(sK0,sK2))
      | v1_xboole_0(k6_waybel_0(sK0,sK2))
      | ~ v2_waybel_0(k6_waybel_0(sK0,sK2),sK0)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ r2_hidden(X4,sK5(sK0,sK1,k6_waybel_0(sK0,sK2)))
      | ~ r1_orders_2(sK0,sK2,X4) ) ),
    inference(resolution,[],[f2270,f1798])).

fof(f1798,plain,(
    ! [X4,X5] :
      ( ~ r1_xboole_0(X5,k6_waybel_0(sK0,sK2))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ r2_hidden(X4,X5)
      | ~ r1_orders_2(sK0,sK2,X4) ) ),
    inference(resolution,[],[f451,f120])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f451,plain,(
    ! [X5] :
      ( r2_hidden(X5,k6_waybel_0(sK0,sK2))
      | ~ r1_orders_2(sK0,sK2,X5)
      | ~ m1_subset_1(X5,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f450,f100])).

fof(f450,plain,(
    ! [X5] :
      ( ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,sK2,X5)
      | r2_hidden(X5,k6_waybel_0(sK0,sK2)) ) ),
    inference(subsumption_resolution,[],[f430,f285])).

fof(f430,plain,(
    ! [X5] :
      ( v2_struct_0(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,sK2,X5)
      | r2_hidden(X5,k6_waybel_0(sK0,sK2)) ) ),
    inference(resolution,[],[f88,f110])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | r2_hidden(X2,k6_waybel_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f2270,plain,(
    ! [X15] :
      ( r1_xboole_0(sK5(sK0,sK1,X15),X15)
      | ~ v13_waybel_0(X15,sK0)
      | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(sK1,X15)
      | v1_xboole_0(X15)
      | ~ v2_waybel_0(X15,sK0) ) ),
    inference(subsumption_resolution,[],[f2253,f334])).

fof(f2253,plain,(
    ! [X15] :
      ( ~ v2_waybel_0(X15,sK0)
      | ~ v13_waybel_0(X15,sK0)
      | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(sK1,X15)
      | v1_xboole_0(X15)
      | v1_xboole_0(sK5(sK0,sK1,X15))
      | r1_xboole_0(sK5(sK0,sK1,X15),X15) ) ),
    inference(duplicate_literal_removal,[],[f2250])).

fof(f2250,plain,(
    ! [X15] :
      ( ~ v2_waybel_0(X15,sK0)
      | ~ v13_waybel_0(X15,sK0)
      | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(sK1,X15)
      | v1_xboole_0(X15)
      | v1_xboole_0(sK5(sK0,sK1,X15))
      | v1_xboole_0(X15)
      | r1_xboole_0(sK5(sK0,sK1,X15),X15) ) ),
    inference(resolution,[],[f394,f134])).

fof(f394,plain,(
    ! [X6] :
      ( r1_subset_1(sK5(sK0,sK1,X6),X6)
      | ~ v2_waybel_0(X6,sK0)
      | ~ v13_waybel_0(X6,sK0)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(sK1,X6)
      | v1_xboole_0(X6) ) ),
    inference(subsumption_resolution,[],[f393,f93])).

fof(f393,plain,(
    ! [X6] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X6)
      | ~ v2_waybel_0(X6,sK0)
      | ~ v13_waybel_0(X6,sK0)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(sK1,X6)
      | r1_subset_1(sK5(sK0,sK1,X6),X6) ) ),
    inference(subsumption_resolution,[],[f392,f92])).

fof(f392,plain,(
    ! [X6] :
      ( ~ v12_waybel_0(sK1,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X6)
      | ~ v2_waybel_0(X6,sK0)
      | ~ v13_waybel_0(X6,sK0)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(sK1,X6)
      | r1_subset_1(sK5(sK0,sK1,X6),X6) ) ),
    inference(subsumption_resolution,[],[f391,f90])).

fof(f391,plain,(
    ! [X6] :
      ( v1_xboole_0(sK1)
      | ~ v12_waybel_0(sK1,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X6)
      | ~ v2_waybel_0(X6,sK0)
      | ~ v13_waybel_0(X6,sK0)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(sK1,X6)
      | r1_subset_1(sK5(sK0,sK1,X6),X6) ) ),
    inference(subsumption_resolution,[],[f390,f100])).

fof(f390,plain,(
    ! [X6] :
      ( ~ l1_orders_2(sK0)
      | v1_xboole_0(sK1)
      | ~ v12_waybel_0(sK1,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X6)
      | ~ v2_waybel_0(X6,sK0)
      | ~ v13_waybel_0(X6,sK0)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(sK1,X6)
      | r1_subset_1(sK5(sK0,sK1,X6),X6) ) ),
    inference(subsumption_resolution,[],[f389,f99])).

fof(f389,plain,(
    ! [X6] :
      ( ~ v2_lattice3(sK0)
      | ~ l1_orders_2(sK0)
      | v1_xboole_0(sK1)
      | ~ v12_waybel_0(sK1,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X6)
      | ~ v2_waybel_0(X6,sK0)
      | ~ v13_waybel_0(X6,sK0)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(sK1,X6)
      | r1_subset_1(sK5(sK0,sK1,X6),X6) ) ),
    inference(subsumption_resolution,[],[f388,f98])).

fof(f388,plain,(
    ! [X6] :
      ( ~ v1_lattice3(sK0)
      | ~ v2_lattice3(sK0)
      | ~ l1_orders_2(sK0)
      | v1_xboole_0(sK1)
      | ~ v12_waybel_0(sK1,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X6)
      | ~ v2_waybel_0(X6,sK0)
      | ~ v13_waybel_0(X6,sK0)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(sK1,X6)
      | r1_subset_1(sK5(sK0,sK1,X6),X6) ) ),
    inference(subsumption_resolution,[],[f387,f97])).

fof(f387,plain,(
    ! [X6] :
      ( ~ v2_waybel_1(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_lattice3(sK0)
      | ~ l1_orders_2(sK0)
      | v1_xboole_0(sK1)
      | ~ v12_waybel_0(sK1,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X6)
      | ~ v2_waybel_0(X6,sK0)
      | ~ v13_waybel_0(X6,sK0)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(sK1,X6)
      | r1_subset_1(sK5(sK0,sK1,X6),X6) ) ),
    inference(subsumption_resolution,[],[f386,f96])).

fof(f386,plain,(
    ! [X6] :
      ( ~ v5_orders_2(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_lattice3(sK0)
      | ~ l1_orders_2(sK0)
      | v1_xboole_0(sK1)
      | ~ v12_waybel_0(sK1,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X6)
      | ~ v2_waybel_0(X6,sK0)
      | ~ v13_waybel_0(X6,sK0)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(sK1,X6)
      | r1_subset_1(sK5(sK0,sK1,X6),X6) ) ),
    inference(subsumption_resolution,[],[f385,f95])).

fof(f385,plain,(
    ! [X6] :
      ( ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_lattice3(sK0)
      | ~ l1_orders_2(sK0)
      | v1_xboole_0(sK1)
      | ~ v12_waybel_0(sK1,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X6)
      | ~ v2_waybel_0(X6,sK0)
      | ~ v13_waybel_0(X6,sK0)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(sK1,X6)
      | r1_subset_1(sK5(sK0,sK1,X6),X6) ) ),
    inference(subsumption_resolution,[],[f324,f94])).

fof(f324,plain,(
    ! [X6] :
      ( ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_lattice3(sK0)
      | ~ l1_orders_2(sK0)
      | v1_xboole_0(sK1)
      | ~ v12_waybel_0(sK1,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X6)
      | ~ v2_waybel_0(X6,sK0)
      | ~ v13_waybel_0(X6,sK0)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(sK1,X6)
      | r1_subset_1(sK5(sK0,sK1,X6),X6) ) ),
    inference(resolution,[],[f91,f118])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v2_waybel_1(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | v1_xboole_0(X1)
      | ~ v1_waybel_0(X1,X0)
      | ~ v12_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X2)
      | ~ v2_waybel_0(X2,X0)
      | ~ v13_waybel_0(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_subset_1(X1,X2)
      | r1_subset_1(sK5(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f53])).
%------------------------------------------------------------------------------
