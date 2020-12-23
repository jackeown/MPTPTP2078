%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tmap_1__t45_tmap_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:15 EDT 2019

% Result     : Theorem 66.90s
% Output     : Refutation 66.90s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 686 expanded)
%              Number of leaves         :   12 ( 135 expanded)
%              Depth                    :   16
%              Number of atoms          :  574 (8004 expanded)
%              Number of equality atoms :   17 (  25 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6805,plain,(
    $false ),
    inference(subsumption_resolution,[],[f6790,f5129])).

fof(f5129,plain,(
    sP4(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),k1_tsep_1(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f5128,f89])).

fof(f89,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_pre_topc(X1,k1_tsep_1(X0,X2,X1))
                    | ~ v1_borsuk_1(X1,k1_tsep_1(X0,X2,X1))
                    | ~ m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
                    | ~ v1_borsuk_1(X1,k1_tsep_1(X0,X1,X2)) )
                  & r1_tsep_1(X3,X2)
                  & m1_pre_topc(X1,X3)
                  & m1_pre_topc(X3,X0)
                  & v1_borsuk_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_pre_topc(X1,k1_tsep_1(X0,X2,X1))
                    | ~ v1_borsuk_1(X1,k1_tsep_1(X0,X2,X1))
                    | ~ m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
                    | ~ v1_borsuk_1(X1,k1_tsep_1(X0,X1,X2)) )
                  & r1_tsep_1(X3,X2)
                  & m1_pre_topc(X1,X3)
                  & m1_pre_topc(X3,X0)
                  & v1_borsuk_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & v1_borsuk_1(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ( ( r1_tsep_1(X3,X2)
                        & m1_pre_topc(X1,X3) )
                     => ( m1_pre_topc(X1,k1_tsep_1(X0,X2,X1))
                        & v1_borsuk_1(X1,k1_tsep_1(X0,X2,X1))
                        & m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
                        & v1_borsuk_1(X1,k1_tsep_1(X0,X1,X2)) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & v1_borsuk_1(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( ( r1_tsep_1(X3,X2)
                      & m1_pre_topc(X1,X3) )
                   => ( m1_pre_topc(X1,k1_tsep_1(X0,X2,X1))
                      & v1_borsuk_1(X1,k1_tsep_1(X0,X2,X1))
                      & m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
                      & v1_borsuk_1(X1,k1_tsep_1(X0,X1,X2)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t45_tmap_1.p',t45_tmap_1)).

fof(f5128,plain,
    ( sP4(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),k1_tsep_1(sK0,sK1,sK2))
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f5127,f88])).

fof(f88,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f5127,plain,
    ( sP4(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),k1_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f5126,f4362])).

fof(f4362,plain,(
    ~ r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f88,f79,f86,f282,f81,f90,f89,f87,f256,f213,f276,f104])).

fof(f104,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tsep_1(X3,X2)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X1,X2)
      | r1_tsep_1(X1,X3)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ~ r1_tsep_1(X3,X2)
                    & ~ r1_tsep_1(X2,X3) )
                  | ( r1_tsep_1(X3,X1)
                    & r1_tsep_1(X1,X3) )
                  | ~ m1_pre_topc(X1,X2)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ~ r1_tsep_1(X3,X2)
                    & ~ r1_tsep_1(X2,X3) )
                  | ( r1_tsep_1(X3,X1)
                    & r1_tsep_1(X1,X3) )
                  | ~ m1_pre_topc(X1,X2)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( m1_pre_topc(X1,X2)
                   => ( ( ~ r1_tsep_1(X3,X2)
                        & ~ r1_tsep_1(X2,X3) )
                      | ( r1_tsep_1(X3,X1)
                        & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t45_tmap_1.p',t23_tmap_1)).

fof(f276,plain,(
    m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f88,f84,f85,f86,f87,f90,f89,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t45_tmap_1.p',t22_tsep_1)).

fof(f85,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f84,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f213,plain,(
    ~ v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f88,f84,f85,f86,f87,f90,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t45_tmap_1.p',dt_k1_tsep_1)).

fof(f256,plain,(
    m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) ),
    inference(unit_resulting_resolution,[],[f88,f84,f85,f86,f87,f90,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f87,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f90,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f81,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f282,plain,(
    ~ r1_tsep_1(sK1,sK3) ),
    inference(unit_resulting_resolution,[],[f88,f79,f82,f81,f86,f87,f90,f89,f105])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tsep_1(X1,X2)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ~ r1_tsep_1(X2,X1)
                & ~ r1_tsep_1(X1,X2) )
              | ~ m1_pre_topc(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ~ r1_tsep_1(X2,X1)
                & ~ r1_tsep_1(X1,X2) )
              | ~ m1_pre_topc(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( m1_pre_topc(X1,X2)
               => ( ~ r1_tsep_1(X2,X1)
                  & ~ r1_tsep_1(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t45_tmap_1.p',t22_tmap_1)).

fof(f82,plain,(
    m1_pre_topc(sK1,sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f86,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f79,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f5126,plain,
    ( sP4(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),k1_tsep_1(sK0,sK1,sK2))
    | r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f5125,f81])).

fof(f5125,plain,
    ( sP4(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(sK3,sK0)
    | r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f5124,f80])).

fof(f80,plain,(
    v1_borsuk_1(sK3,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f5124,plain,
    ( sP4(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),k1_tsep_1(sK0,sK1,sK2))
    | ~ v1_borsuk_1(sK3,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f5123,f79])).

fof(f5123,plain,
    ( sP4(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),k1_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(sK3)
    | ~ v1_borsuk_1(sK3,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f5122,f256])).

fof(f5122,plain,
    ( sP4(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK3)
    | ~ v1_borsuk_1(sK3,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f5121,f213])).

fof(f5121,plain,
    ( sP4(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),k1_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK3)
    | ~ v1_borsuk_1(sK3,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f5120,f90])).

fof(f5120,plain,
    ( sP4(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),k1_tsep_1(sK0,sK1,sK2))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK3)
    | ~ v1_borsuk_1(sK3,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(superposition,[],[f333,f401])).

fof(f401,plain,(
    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k2_tsep_1(sK0,sK3,k1_tsep_1(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f84,f88,f79,f83,f85,f82,f81,f86,f87,f90,f89,f97])).

fof(f97,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tsep_1(X2,X3)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X1,X2)
      | v2_struct_0(X0)
      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X3,X1))
                    & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) )
                  | ( ~ r1_tsep_1(X3,X2)
                    & ~ r1_tsep_1(X2,X3) )
                  | ~ m1_pre_topc(X1,X2)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X3,X1))
                    & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) )
                  | ( ~ r1_tsep_1(X3,X2)
                    & ~ r1_tsep_1(X2,X3) )
                  | ~ m1_pre_topc(X1,X2)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( m1_pre_topc(X1,X2)
                   => ( ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X3,X1))
                        & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) )
                      | ( ~ r1_tsep_1(X3,X2)
                        & ~ r1_tsep_1(X2,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t45_tmap_1.p',t33_tmap_1)).

fof(f83,plain,(
    r1_tsep_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f333,plain,(
    ! [X2,X0,X1] :
      ( sP4(k2_tsep_1(X0,X2,X1),X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ v1_borsuk_1(X2,X0)
      | ~ m1_pre_topc(X2,X0)
      | r1_tsep_1(X2,X1)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f332,f108])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k2_tsep_1(X0,X2,X1),X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ v1_borsuk_1(X2,X0)
      | ~ m1_pre_topc(X2,X0)
      | r1_tsep_1(X2,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(k2_tsep_1(X0,X2,X1),X1)
                & v1_borsuk_1(k2_tsep_1(X0,X2,X1),X1) )
              | r1_tsep_1(X2,X1)
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_borsuk_1(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(k2_tsep_1(X0,X2,X1),X1)
                & v1_borsuk_1(k2_tsep_1(X0,X2,X1),X1) )
              | r1_tsep_1(X2,X1)
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_borsuk_1(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_borsuk_1(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( ~ r1_tsep_1(X2,X1)
               => ( m1_pre_topc(k2_tsep_1(X0,X2,X1),X1)
                  & v1_borsuk_1(k2_tsep_1(X0,X2,X1),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t45_tmap_1.p',t43_tmap_1)).

fof(f332,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ v1_borsuk_1(X2,X0)
      | ~ m1_pre_topc(X2,X0)
      | r1_tsep_1(X2,X1)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(k2_tsep_1(X0,X2,X1),X1)
      | sP4(k2_tsep_1(X0,X2,X1),X1) ) ),
    inference(resolution,[],[f107,f109])).

fof(f109,plain,(
    ! [X2,X0] :
      ( ~ v1_borsuk_1(X2,X0)
      | ~ m1_pre_topc(X2,X0)
      | sP4(X2,X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_borsuk_1(X1,X0) )
              <=> ( m1_pre_topc(X2,X0)
                  & v1_borsuk_1(X2,X0) ) )
              | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != X2
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_borsuk_1(X1,X0) )
              <=> ( m1_pre_topc(X2,X0)
                  & v1_borsuk_1(X2,X0) ) )
              | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != X2
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2) )
             => ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
               => ( ( m1_pre_topc(X1,X0)
                    & v1_borsuk_1(X1,X0) )
                <=> ( m1_pre_topc(X2,X0)
                    & v1_borsuk_1(X2,X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t45_tmap_1.p',t13_tmap_1)).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( v1_borsuk_1(k2_tsep_1(X0,X2,X1),X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ v1_borsuk_1(X2,X0)
      | ~ m1_pre_topc(X2,X0)
      | r1_tsep_1(X2,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f6790,plain,(
    ~ sP4(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),k1_tsep_1(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f1085,f1082,f317,f161,f146,f4411,f4414,f139])).

fof(f139,plain,(
    ! [X0,X1] :
      ( ~ sP4(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v2_pre_topc(X0)
      | v1_borsuk_1(X1,X0) ) ),
    inference(equality_resolution,[],[f113])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X2)
      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != X2
      | ~ sP4(X2,X0)
      | v1_borsuk_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f4414,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(unit_resulting_resolution,[],[f90,f203,f124])).

fof(f124,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t45_tmap_1.p',dt_m1_pre_topc)).

fof(f203,plain,(
    m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK0) ),
    inference(unit_resulting_resolution,[],[f90,f87,f123])).

fof(f123,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t45_tmap_1.p',t11_tmap_1)).

fof(f4411,plain,(
    v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(unit_resulting_resolution,[],[f89,f90,f203,f120])).

fof(f120,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f40])).

fof(f40,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t45_tmap_1.p',cc1_pre_topc)).

fof(f146,plain,(
    l1_pre_topc(sK1) ),
    inference(unit_resulting_resolution,[],[f90,f87,f124])).

fof(f161,plain,(
    v2_pre_topc(sK1) ),
    inference(unit_resulting_resolution,[],[f89,f87,f90,f120])).

fof(f317,plain,(
    ~ v1_borsuk_1(sK1,k1_tsep_1(sK0,sK1,sK2)) ),
    inference(duplicate_literal_removal,[],[f316])).

fof(f316,plain,
    ( ~ v1_borsuk_1(sK1,k1_tsep_1(sK0,sK1,sK2))
    | ~ v1_borsuk_1(sK1,k1_tsep_1(sK0,sK1,sK2)) ),
    inference(forward_demodulation,[],[f315,f299])).

fof(f299,plain,(
    k1_tsep_1(sK0,sK1,sK2) = k1_tsep_1(sK0,sK2,sK1) ),
    inference(unit_resulting_resolution,[],[f90,f86,f87,f84,f85,f88,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t45_tmap_1.p',commutativity_k1_tsep_1)).

fof(f315,plain,
    ( ~ v1_borsuk_1(sK1,k1_tsep_1(sK0,sK2,sK1))
    | ~ v1_borsuk_1(sK1,k1_tsep_1(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f314,f276])).

fof(f314,plain,
    ( ~ m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK2))
    | ~ v1_borsuk_1(sK1,k1_tsep_1(sK0,sK2,sK1))
    | ~ v1_borsuk_1(sK1,k1_tsep_1(sK0,sK1,sK2)) ),
    inference(duplicate_literal_removal,[],[f313])).

fof(f313,plain,
    ( ~ m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK2))
    | ~ v1_borsuk_1(sK1,k1_tsep_1(sK0,sK2,sK1))
    | ~ m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK2))
    | ~ v1_borsuk_1(sK1,k1_tsep_1(sK0,sK1,sK2)) ),
    inference(backward_demodulation,[],[f299,f78])).

fof(f78,plain,
    ( ~ v1_borsuk_1(sK1,k1_tsep_1(sK0,sK2,sK1))
    | ~ m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK2))
    | ~ v1_borsuk_1(sK1,k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(sK1,k1_tsep_1(sK0,sK2,sK1)) ),
    inference(cnf_transformation,[],[f43])).

fof(f1082,plain,(
    v2_pre_topc(k1_tsep_1(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f89,f90,f256,f120])).

fof(f1085,plain,(
    l1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f90,f256,f124])).
%------------------------------------------------------------------------------
