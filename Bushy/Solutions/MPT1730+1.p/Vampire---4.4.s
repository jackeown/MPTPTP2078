%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tmap_1__t39_tmap_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:14 EDT 2019

% Result     : Theorem 2.46s
% Output     : Refutation 2.46s
% Verified   : 
% Statistics : Number of formulae       :  361 ( 768 expanded)
%              Number of leaves         :   84 ( 339 expanded)
%              Depth                    :   14
%              Number of atoms          : 1360 (4380 expanded)
%              Number of equality atoms :  112 ( 199 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f24888,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f227,f241,f248,f255,f269,f290,f297,f304,f320,f337,f357,f364,f372,f535,f754,f908,f975,f1113,f1269,f1790,f1833,f1879,f1933,f2004,f2015,f2426,f2858,f3672,f7553,f7856,f8240,f10646,f10647,f10666,f10753,f12269,f13142,f13147,f13401,f13409,f18612,f19853,f22335,f22337,f22935,f22961,f22968,f22982,f22991,f22992,f23033,f23490,f24292,f24779,f24887])).

fof(f24887,plain,
    ( spl11_55
    | spl11_59
    | spl11_65
    | spl11_177 ),
    inference(avatar_contradiction_clause,[],[f24886])).

fof(f24886,plain,
    ( $false
    | ~ spl11_55
    | ~ spl11_59
    | ~ spl11_65
    | ~ spl11_177 ),
    inference(subsumption_resolution,[],[f24885,f585])).

fof(f585,plain,
    ( ~ r1_tsep_1(sK2,sK3)
    | ~ spl11_65 ),
    inference(avatar_component_clause,[],[f584])).

fof(f584,plain,
    ( spl11_65
  <=> ~ r1_tsep_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_65])])).

fof(f24885,plain,
    ( r1_tsep_1(sK2,sK3)
    | ~ spl11_55
    | ~ spl11_59
    | ~ spl11_177 ),
    inference(subsumption_resolution,[],[f24868,f1951])).

fof(f1951,plain,
    ( ~ r1_tsep_1(sK3,sK2)
    | ~ spl11_177 ),
    inference(avatar_component_clause,[],[f1950])).

fof(f1950,plain,
    ( spl11_177
  <=> ~ r1_tsep_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_177])])).

fof(f24868,plain,
    ( r1_tsep_1(sK3,sK2)
    | r1_tsep_1(sK2,sK3)
    | ~ spl11_55
    | ~ spl11_59 ),
    inference(subsumption_resolution,[],[f24867,f519])).

fof(f519,plain,
    ( ~ r1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK3)
    | ~ spl11_55 ),
    inference(avatar_component_clause,[],[f518])).

fof(f518,plain,
    ( spl11_55
  <=> ~ r1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_55])])).

fof(f24867,plain,
    ( r1_tsep_1(sK3,sK2)
    | r1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK3)
    | r1_tsep_1(sK2,sK3)
    | ~ spl11_59 ),
    inference(subsumption_resolution,[],[f161,f531])).

fof(f531,plain,
    ( ~ r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2))
    | ~ spl11_59 ),
    inference(avatar_component_clause,[],[f530])).

fof(f530,plain,
    ( spl11_59
  <=> ~ r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_59])])).

fof(f161,plain,
    ( r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2))
    | r1_tsep_1(sK3,sK2)
    | r1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK3)
    | r1_tsep_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f104])).

fof(f104,plain,
    ( ( ( r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2))
        & ( ~ r1_tsep_1(sK3,sK2)
          | ~ r1_tsep_1(sK3,sK1) ) )
      | ( r1_tsep_1(sK3,sK2)
        & r1_tsep_1(sK3,sK1)
        & ~ r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2)) )
      | ( r1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK3)
        & ( ~ r1_tsep_1(sK2,sK3)
          | ~ r1_tsep_1(sK1,sK3) ) )
      | ( r1_tsep_1(sK2,sK3)
        & r1_tsep_1(sK1,sK3)
        & ~ r1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK3) ) )
    & m1_pre_topc(sK3,sK0)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f57,f103,f102,f101,f100])).

fof(f100,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ( r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))
                        & ( ~ r1_tsep_1(X3,X2)
                          | ~ r1_tsep_1(X3,X1) ) )
                      | ( r1_tsep_1(X3,X2)
                        & r1_tsep_1(X3,X1)
                        & ~ r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) )
                      | ( r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)
                        & ( ~ r1_tsep_1(X2,X3)
                          | ~ r1_tsep_1(X1,X3) ) )
                      | ( r1_tsep_1(X2,X3)
                        & r1_tsep_1(X1,X3)
                        & ~ r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) ) )
                    & m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( r1_tsep_1(X3,k1_tsep_1(sK0,X1,X2))
                      & ( ~ r1_tsep_1(X3,X2)
                        | ~ r1_tsep_1(X3,X1) ) )
                    | ( r1_tsep_1(X3,X2)
                      & r1_tsep_1(X3,X1)
                      & ~ r1_tsep_1(X3,k1_tsep_1(sK0,X1,X2)) )
                    | ( r1_tsep_1(k1_tsep_1(sK0,X1,X2),X3)
                      & ( ~ r1_tsep_1(X2,X3)
                        | ~ r1_tsep_1(X1,X3) ) )
                    | ( r1_tsep_1(X2,X3)
                      & r1_tsep_1(X1,X3)
                      & ~ r1_tsep_1(k1_tsep_1(sK0,X1,X2),X3) ) )
                  & m1_pre_topc(X3,sK0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f101,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))
                      & ( ~ r1_tsep_1(X3,X2)
                        | ~ r1_tsep_1(X3,X1) ) )
                    | ( r1_tsep_1(X3,X2)
                      & r1_tsep_1(X3,X1)
                      & ~ r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) )
                    | ( r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)
                      & ( ~ r1_tsep_1(X2,X3)
                        | ~ r1_tsep_1(X1,X3) ) )
                    | ( r1_tsep_1(X2,X3)
                      & r1_tsep_1(X1,X3)
                      & ~ r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) ) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ( ( r1_tsep_1(X3,k1_tsep_1(X0,sK1,X2))
                    & ( ~ r1_tsep_1(X3,X2)
                      | ~ r1_tsep_1(X3,sK1) ) )
                  | ( r1_tsep_1(X3,X2)
                    & r1_tsep_1(X3,sK1)
                    & ~ r1_tsep_1(X3,k1_tsep_1(X0,sK1,X2)) )
                  | ( r1_tsep_1(k1_tsep_1(X0,sK1,X2),X3)
                    & ( ~ r1_tsep_1(X2,X3)
                      | ~ r1_tsep_1(sK1,X3) ) )
                  | ( r1_tsep_1(X2,X3)
                    & r1_tsep_1(sK1,X3)
                    & ~ r1_tsep_1(k1_tsep_1(X0,sK1,X2),X3) ) )
                & m1_pre_topc(X3,X0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(sK1,X0)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ( ( r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))
                  & ( ~ r1_tsep_1(X3,X2)
                    | ~ r1_tsep_1(X3,X1) ) )
                | ( r1_tsep_1(X3,X2)
                  & r1_tsep_1(X3,X1)
                  & ~ r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) )
                | ( r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)
                  & ( ~ r1_tsep_1(X2,X3)
                    | ~ r1_tsep_1(X1,X3) ) )
                | ( r1_tsep_1(X2,X3)
                  & r1_tsep_1(X1,X3)
                  & ~ r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) ) )
              & m1_pre_topc(X3,X0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ( ( r1_tsep_1(X3,k1_tsep_1(X0,X1,sK2))
                & ( ~ r1_tsep_1(X3,sK2)
                  | ~ r1_tsep_1(X3,X1) ) )
              | ( r1_tsep_1(X3,sK2)
                & r1_tsep_1(X3,X1)
                & ~ r1_tsep_1(X3,k1_tsep_1(X0,X1,sK2)) )
              | ( r1_tsep_1(k1_tsep_1(X0,X1,sK2),X3)
                & ( ~ r1_tsep_1(sK2,X3)
                  | ~ r1_tsep_1(X1,X3) ) )
              | ( r1_tsep_1(sK2,X3)
                & r1_tsep_1(X1,X3)
                & ~ r1_tsep_1(k1_tsep_1(X0,X1,sK2),X3) ) )
            & m1_pre_topc(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK2,X0)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ( r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))
              & ( ~ r1_tsep_1(X3,X2)
                | ~ r1_tsep_1(X3,X1) ) )
            | ( r1_tsep_1(X3,X2)
              & r1_tsep_1(X3,X1)
              & ~ r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) )
            | ( r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)
              & ( ~ r1_tsep_1(X2,X3)
                | ~ r1_tsep_1(X1,X3) ) )
            | ( r1_tsep_1(X2,X3)
              & r1_tsep_1(X1,X3)
              & ~ r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) ) )
          & m1_pre_topc(X3,X0)
          & ~ v2_struct_0(X3) )
     => ( ( ( r1_tsep_1(sK3,k1_tsep_1(X0,X1,X2))
            & ( ~ r1_tsep_1(sK3,X2)
              | ~ r1_tsep_1(sK3,X1) ) )
          | ( r1_tsep_1(sK3,X2)
            & r1_tsep_1(sK3,X1)
            & ~ r1_tsep_1(sK3,k1_tsep_1(X0,X1,X2)) )
          | ( r1_tsep_1(k1_tsep_1(X0,X1,X2),sK3)
            & ( ~ r1_tsep_1(X2,sK3)
              | ~ r1_tsep_1(X1,sK3) ) )
          | ( r1_tsep_1(X2,sK3)
            & r1_tsep_1(X1,sK3)
            & ~ r1_tsep_1(k1_tsep_1(X0,X1,X2),sK3) ) )
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))
                      & ( ~ r1_tsep_1(X3,X2)
                        | ~ r1_tsep_1(X3,X1) ) )
                    | ( r1_tsep_1(X3,X2)
                      & r1_tsep_1(X3,X1)
                      & ~ r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) )
                    | ( r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)
                      & ( ~ r1_tsep_1(X2,X3)
                        | ~ r1_tsep_1(X1,X3) ) )
                    | ( r1_tsep_1(X2,X3)
                      & r1_tsep_1(X1,X3)
                      & ~ r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) ) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))
                      & ( ~ r1_tsep_1(X3,X2)
                        | ~ r1_tsep_1(X3,X1) ) )
                    | ( r1_tsep_1(X3,X2)
                      & r1_tsep_1(X3,X1)
                      & ~ r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) )
                    | ( r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)
                      & ( ~ r1_tsep_1(X2,X3)
                        | ~ r1_tsep_1(X1,X3) ) )
                    | ( r1_tsep_1(X2,X3)
                      & r1_tsep_1(X1,X3)
                      & ~ r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) ) )
                  & m1_pre_topc(X3,X0)
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
                      & ~ v2_struct_0(X3) )
                   => ( ~ ( r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))
                          & ~ ( r1_tsep_1(X3,X2)
                              & r1_tsep_1(X3,X1) ) )
                      & ~ ( r1_tsep_1(X3,X2)
                          & r1_tsep_1(X3,X1)
                          & ~ r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) )
                      & ~ ( r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)
                          & ~ ( r1_tsep_1(X2,X3)
                              & r1_tsep_1(X1,X3) ) )
                      & ~ ( r1_tsep_1(X2,X3)
                          & r1_tsep_1(X1,X3)
                          & ~ r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) ) ) ) ) ) ) ),
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
                    & ~ v2_struct_0(X3) )
                 => ( ~ ( r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))
                        & ~ ( r1_tsep_1(X3,X2)
                            & r1_tsep_1(X3,X1) ) )
                    & ~ ( r1_tsep_1(X3,X2)
                        & r1_tsep_1(X3,X1)
                        & ~ r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) )
                    & ~ ( r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)
                        & ~ ( r1_tsep_1(X2,X3)
                            & r1_tsep_1(X1,X3) ) )
                    & ~ ( r1_tsep_1(X2,X3)
                        & r1_tsep_1(X1,X3)
                        & ~ r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t39_tmap_1.p',t39_tmap_1)).

fof(f24779,plain,
    ( ~ spl11_264
    | spl11_635
    | ~ spl11_672
    | ~ spl11_1036 ),
    inference(avatar_contradiction_clause,[],[f24778])).

fof(f24778,plain,
    ( $false
    | ~ spl11_264
    | ~ spl11_635
    | ~ spl11_672
    | ~ spl11_1036 ),
    inference(subsumption_resolution,[],[f24777,f12231])).

fof(f12231,plain,
    ( k3_xboole_0(u1_struct_0(sK3),u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) != k1_xboole_0
    | ~ spl11_635 ),
    inference(avatar_component_clause,[],[f12230])).

fof(f12230,plain,
    ( spl11_635
  <=> k3_xboole_0(u1_struct_0(sK3),u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) != k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_635])])).

fof(f24777,plain,
    ( k3_xboole_0(u1_struct_0(sK3),u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) = k1_xboole_0
    | ~ spl11_264
    | ~ spl11_672
    | ~ spl11_1036 ),
    inference(forward_demodulation,[],[f24776,f13405])).

fof(f13405,plain,
    ( k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)) = k1_xboole_0
    | ~ spl11_672 ),
    inference(avatar_component_clause,[],[f13404])).

fof(f13404,plain,
    ( spl11_672
  <=> k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_672])])).

fof(f24776,plain,
    ( k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)) = k3_xboole_0(u1_struct_0(sK3),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    | ~ spl11_264
    | ~ spl11_1036 ),
    inference(forward_demodulation,[],[f24681,f179])).

fof(f179,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t39_tmap_1.p',commutativity_k3_xboole_0)).

fof(f24681,plain,
    ( k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2)) = k3_xboole_0(u1_struct_0(sK3),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    | ~ spl11_264
    | ~ spl11_1036 ),
    inference(superposition,[],[f24264,f2857])).

fof(f2857,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ spl11_264 ),
    inference(avatar_component_clause,[],[f2856])).

fof(f2856,plain,
    ( spl11_264
  <=> u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_264])])).

fof(f24264,plain,
    ( ! [X1] : k3_xboole_0(u1_struct_0(sK3),X1) = k3_xboole_0(u1_struct_0(sK3),k2_xboole_0(u1_struct_0(sK1),X1))
    | ~ spl11_1036 ),
    inference(avatar_component_clause,[],[f24263])).

fof(f24263,plain,
    ( spl11_1036
  <=> ! [X1] : k3_xboole_0(u1_struct_0(sK3),X1) = k3_xboole_0(u1_struct_0(sK3),k2_xboole_0(u1_struct_0(sK1),X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1036])])).

fof(f24292,plain,
    ( spl11_1036
    | ~ spl11_590 ),
    inference(avatar_split_clause,[],[f23144,f10751,f24263])).

fof(f10751,plain,
    ( spl11_590
  <=> k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK1)) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_590])])).

fof(f23144,plain,
    ( ! [X7] : k3_xboole_0(u1_struct_0(sK3),X7) = k3_xboole_0(u1_struct_0(sK3),k2_xboole_0(u1_struct_0(sK1),X7))
    | ~ spl11_590 ),
    inference(forward_demodulation,[],[f23067,f163])).

fof(f163,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f41])).

fof(f41,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t39_tmap_1.p',t1_boole)).

fof(f23067,plain,
    ( ! [X7] : k2_xboole_0(k3_xboole_0(u1_struct_0(sK3),X7),k1_xboole_0) = k3_xboole_0(u1_struct_0(sK3),k2_xboole_0(u1_struct_0(sK1),X7))
    | ~ spl11_590 ),
    inference(superposition,[],[f453,f10752])).

fof(f10752,plain,
    ( k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK1)) = k1_xboole_0
    | ~ spl11_590 ),
    inference(avatar_component_clause,[],[f10751])).

fof(f453,plain,(
    ! [X6,X7,X5] : k2_xboole_0(k3_xboole_0(X5,X7),k3_xboole_0(X5,X6)) = k3_xboole_0(X5,k2_xboole_0(X6,X7)) ),
    inference(superposition,[],[f197,f180])).

fof(f180,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t39_tmap_1.p',commutativity_k2_xboole_0)).

fof(f197,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t39_tmap_1.p',t23_xboole_1)).

fof(f23490,plain,
    ( spl11_670
    | ~ spl11_1034 ),
    inference(avatar_split_clause,[],[f22985,f22980,f13396])).

fof(f13396,plain,
    ( spl11_670
  <=> k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2)) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_670])])).

fof(f22980,plain,
    ( spl11_1034
  <=> r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1034])])).

fof(f22985,plain,
    ( k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2)) = k1_xboole_0
    | ~ spl11_1034 ),
    inference(resolution,[],[f22981,f191])).

fof(f191,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t39_tmap_1.p',d7_xboole_0)).

fof(f22981,plain,
    ( r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ spl11_1034 ),
    inference(avatar_component_clause,[],[f22980])).

fof(f23033,plain,
    ( spl11_55
    | ~ spl11_100
    | ~ spl11_634
    | ~ spl11_782 ),
    inference(avatar_contradiction_clause,[],[f23032])).

fof(f23032,plain,
    ( $false
    | ~ spl11_55
    | ~ spl11_100
    | ~ spl11_634
    | ~ spl11_782 ),
    inference(subsumption_resolution,[],[f23031,f898])).

fof(f898,plain,
    ( l1_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ spl11_100 ),
    inference(avatar_component_clause,[],[f897])).

fof(f897,plain,
    ( spl11_100
  <=> l1_struct_0(k1_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_100])])).

fof(f23031,plain,
    ( ~ l1_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ spl11_55
    | ~ spl11_634
    | ~ spl11_782 ),
    inference(subsumption_resolution,[],[f23026,f12234])).

fof(f12234,plain,
    ( k3_xboole_0(u1_struct_0(sK3),u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) = k1_xboole_0
    | ~ spl11_634 ),
    inference(avatar_component_clause,[],[f12233])).

fof(f12233,plain,
    ( spl11_634
  <=> k3_xboole_0(u1_struct_0(sK3),u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_634])])).

fof(f23026,plain,
    ( k3_xboole_0(u1_struct_0(sK3),u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) != k1_xboole_0
    | ~ l1_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ spl11_55
    | ~ spl11_782 ),
    inference(resolution,[],[f519,f19852])).

fof(f19852,plain,
    ( ! [X1] :
        ( r1_tsep_1(X1,sK3)
        | k3_xboole_0(u1_struct_0(sK3),u1_struct_0(X1)) != k1_xboole_0
        | ~ l1_struct_0(X1) )
    | ~ spl11_782 ),
    inference(avatar_component_clause,[],[f19851])).

fof(f19851,plain,
    ( spl11_782
  <=> ! [X1] :
        ( ~ l1_struct_0(X1)
        | k3_xboole_0(u1_struct_0(sK3),u1_struct_0(X1)) != k1_xboole_0
        | r1_tsep_1(X1,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_782])])).

fof(f22992,plain,
    ( spl11_592
    | ~ spl11_26
    | ~ spl11_634
    | ~ spl11_890 ),
    inference(avatar_split_clause,[],[f22945,f21380,f12233,f318,f11077])).

fof(f11077,plain,
    ( spl11_592
  <=> v1_xboole_0(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_592])])).

fof(f318,plain,
    ( spl11_26
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_26])])).

fof(f21380,plain,
    ( spl11_890
  <=> ! [X1] :
        ( ~ v1_xboole_0(k3_xboole_0(X1,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))))
        | v1_xboole_0(k3_xboole_0(X1,u1_struct_0(sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_890])])).

fof(f22945,plain,
    ( v1_xboole_0(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)))
    | ~ spl11_26
    | ~ spl11_634
    | ~ spl11_890 ),
    inference(forward_demodulation,[],[f22944,f179])).

fof(f22944,plain,
    ( v1_xboole_0(k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK1)))
    | ~ spl11_26
    | ~ spl11_634
    | ~ spl11_890 ),
    inference(subsumption_resolution,[],[f22941,f319])).

fof(f319,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl11_26 ),
    inference(avatar_component_clause,[],[f318])).

fof(f22941,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK1)))
    | ~ spl11_634
    | ~ spl11_890 ),
    inference(superposition,[],[f21381,f12234])).

fof(f21381,plain,
    ( ! [X1] :
        ( ~ v1_xboole_0(k3_xboole_0(X1,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))))
        | v1_xboole_0(k3_xboole_0(X1,u1_struct_0(sK1))) )
    | ~ spl11_890 ),
    inference(avatar_component_clause,[],[f21380])).

fof(f22991,plain,
    ( spl11_672
    | ~ spl11_666 ),
    inference(avatar_split_clause,[],[f22974,f13128,f13404])).

fof(f13128,plain,
    ( spl11_666
  <=> r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_666])])).

fof(f22974,plain,
    ( k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)) = k1_xboole_0
    | ~ spl11_666 ),
    inference(resolution,[],[f13129,f191])).

fof(f13129,plain,
    ( r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ spl11_666 ),
    inference(avatar_component_clause,[],[f13128])).

fof(f22982,plain,
    ( spl11_1034
    | ~ spl11_102
    | ~ spl11_176
    | ~ spl11_668 ),
    inference(avatar_split_clause,[],[f22972,f13137,f1947,f903,f22980])).

fof(f903,plain,
    ( spl11_102
  <=> l1_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_102])])).

fof(f1947,plain,
    ( spl11_176
  <=> r1_tsep_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_176])])).

fof(f13137,plain,
    ( spl11_668
  <=> l1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_668])])).

fof(f22972,plain,
    ( r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ spl11_102
    | ~ spl11_176
    | ~ spl11_668 ),
    inference(subsumption_resolution,[],[f22971,f904])).

fof(f904,plain,
    ( l1_struct_0(sK3)
    | ~ spl11_102 ),
    inference(avatar_component_clause,[],[f903])).

fof(f22971,plain,
    ( r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ l1_struct_0(sK3)
    | ~ spl11_176
    | ~ spl11_668 ),
    inference(subsumption_resolution,[],[f22969,f13138])).

fof(f13138,plain,
    ( l1_struct_0(sK2)
    | ~ spl11_668 ),
    inference(avatar_component_clause,[],[f13137])).

fof(f22969,plain,
    ( r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK3)
    | ~ spl11_176 ),
    inference(resolution,[],[f1948,f165])).

fof(f165,plain,(
    ! [X0,X1] :
      ( ~ r1_tsep_1(X0,X1)
      | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f105])).

fof(f105,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_tsep_1(X0,X1)
              | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
            & ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
              | ~ r1_tsep_1(X0,X1) ) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t39_tmap_1.p',d3_tsep_1)).

fof(f1948,plain,
    ( r1_tsep_1(sK3,sK2)
    | ~ spl11_176 ),
    inference(avatar_component_clause,[],[f1947])).

fof(f22968,plain,
    ( spl11_176
    | ~ spl11_64
    | ~ spl11_102
    | ~ spl11_668 ),
    inference(avatar_split_clause,[],[f22967,f13137,f903,f581,f1947])).

fof(f581,plain,
    ( spl11_64
  <=> r1_tsep_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_64])])).

fof(f22967,plain,
    ( r1_tsep_1(sK3,sK2)
    | ~ spl11_64
    | ~ spl11_102
    | ~ spl11_668 ),
    inference(subsumption_resolution,[],[f22966,f13138])).

fof(f22966,plain,
    ( r1_tsep_1(sK3,sK2)
    | ~ l1_struct_0(sK2)
    | ~ spl11_64
    | ~ spl11_102 ),
    inference(subsumption_resolution,[],[f22963,f904])).

fof(f22963,plain,
    ( r1_tsep_1(sK3,sK2)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | ~ spl11_64 ),
    inference(resolution,[],[f582,f190])).

fof(f190,plain,(
    ! [X0,X1] :
      ( ~ r1_tsep_1(X0,X1)
      | r1_tsep_1(X1,X0)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f39])).

fof(f39,axiom,(
    ! [X0,X1] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( r1_tsep_1(X0,X1)
       => r1_tsep_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t39_tmap_1.p',symmetry_r1_tsep_1)).

fof(f582,plain,
    ( r1_tsep_1(sK2,sK3)
    | ~ spl11_64 ),
    inference(avatar_component_clause,[],[f581])).

fof(f22961,plain,
    ( spl11_673
    | ~ spl11_1032 ),
    inference(avatar_contradiction_clause,[],[f22960])).

fof(f22960,plain,
    ( $false
    | ~ spl11_673
    | ~ spl11_1032 ),
    inference(subsumption_resolution,[],[f22955,f13408])).

fof(f13408,plain,
    ( k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)) != k1_xboole_0
    | ~ spl11_673 ),
    inference(avatar_component_clause,[],[f13407])).

fof(f13407,plain,
    ( spl11_673
  <=> k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)) != k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_673])])).

fof(f22955,plain,
    ( k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)) = k1_xboole_0
    | ~ spl11_1032 ),
    inference(resolution,[],[f22934,f167])).

fof(f167,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f50])).

fof(f50,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t39_tmap_1.p',t6_boole)).

fof(f22934,plain,
    ( v1_xboole_0(k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)))
    | ~ spl11_1032 ),
    inference(avatar_component_clause,[],[f22933])).

fof(f22933,plain,
    ( spl11_1032
  <=> v1_xboole_0(k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1032])])).

fof(f22935,plain,
    ( spl11_1032
    | ~ spl11_26
    | ~ spl11_634
    | ~ spl11_886 ),
    inference(avatar_split_clause,[],[f22925,f21369,f12233,f318,f22933])).

fof(f21369,plain,
    ( spl11_886
  <=> ! [X0] :
        ( ~ v1_xboole_0(k3_xboole_0(X0,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))))
        | v1_xboole_0(k3_xboole_0(X0,u1_struct_0(sK2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_886])])).

fof(f22925,plain,
    ( v1_xboole_0(k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)))
    | ~ spl11_26
    | ~ spl11_634
    | ~ spl11_886 ),
    inference(forward_demodulation,[],[f22924,f179])).

fof(f22924,plain,
    ( v1_xboole_0(k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2)))
    | ~ spl11_26
    | ~ spl11_634
    | ~ spl11_886 ),
    inference(subsumption_resolution,[],[f22921,f319])).

fof(f22921,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2)))
    | ~ spl11_634
    | ~ spl11_886 ),
    inference(superposition,[],[f21370,f12234])).

fof(f21370,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(k3_xboole_0(X0,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))))
        | v1_xboole_0(k3_xboole_0(X0,u1_struct_0(sK2))) )
    | ~ spl11_886 ),
    inference(avatar_component_clause,[],[f21369])).

fof(f22337,plain,
    ( spl11_890
    | ~ spl11_264 ),
    inference(avatar_split_clause,[],[f17994,f2856,f21380])).

fof(f17994,plain,
    ( ! [X1] :
        ( ~ v1_xboole_0(k3_xboole_0(X1,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))))
        | v1_xboole_0(k3_xboole_0(X1,u1_struct_0(sK1))) )
    | ~ spl11_264 ),
    inference(superposition,[],[f555,f2857])).

fof(f555,plain,(
    ! [X8,X7,X9] :
      ( ~ v1_xboole_0(k3_xboole_0(X7,k2_xboole_0(X8,X9)))
      | v1_xboole_0(k3_xboole_0(X7,X8)) ) ),
    inference(superposition,[],[f341,f197])).

fof(f341,plain,(
    ! [X2,X3] :
      ( ~ v1_xboole_0(k2_xboole_0(X3,X2))
      | v1_xboole_0(X3) ) ),
    inference(superposition,[],[f181,f180])).

fof(f181,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_xboole_0(X1,X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_xboole_0(X1,X0))
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f53])).

fof(f53,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
     => ~ v1_xboole_0(k2_xboole_0(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t39_tmap_1.p',fc5_xboole_0)).

fof(f22335,plain,
    ( spl11_886
    | ~ spl11_264 ),
    inference(avatar_split_clause,[],[f17992,f2856,f21369])).

fof(f17992,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(k3_xboole_0(X0,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))))
        | v1_xboole_0(k3_xboole_0(X0,u1_struct_0(sK2))) )
    | ~ spl11_264 ),
    inference(superposition,[],[f458,f2857])).

fof(f458,plain,(
    ! [X10,X8,X9] :
      ( ~ v1_xboole_0(k3_xboole_0(X8,k2_xboole_0(X9,X10)))
      | v1_xboole_0(k3_xboole_0(X8,X10)) ) ),
    inference(superposition,[],[f181,f197])).

fof(f19853,plain,
    ( spl11_782
    | ~ spl11_102
    | ~ spl11_346 ),
    inference(avatar_split_clause,[],[f3685,f3670,f903,f19851])).

fof(f3670,plain,
    ( spl11_346
  <=> ! [X0] :
        ( ~ l1_struct_0(X0)
        | r1_tsep_1(sK3,X0)
        | k3_xboole_0(u1_struct_0(sK3),u1_struct_0(X0)) != k1_xboole_0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_346])])).

fof(f3685,plain,
    ( ! [X1] :
        ( ~ l1_struct_0(X1)
        | k3_xboole_0(u1_struct_0(sK3),u1_struct_0(X1)) != k1_xboole_0
        | r1_tsep_1(X1,sK3) )
    | ~ spl11_102
    | ~ spl11_346 ),
    inference(subsumption_resolution,[],[f3682,f904])).

fof(f3682,plain,
    ( ! [X1] :
        ( ~ l1_struct_0(X1)
        | k3_xboole_0(u1_struct_0(sK3),u1_struct_0(X1)) != k1_xboole_0
        | r1_tsep_1(X1,sK3)
        | ~ l1_struct_0(sK3) )
    | ~ spl11_346 ),
    inference(duplicate_literal_removal,[],[f3681])).

fof(f3681,plain,
    ( ! [X1] :
        ( ~ l1_struct_0(X1)
        | k3_xboole_0(u1_struct_0(sK3),u1_struct_0(X1)) != k1_xboole_0
        | r1_tsep_1(X1,sK3)
        | ~ l1_struct_0(X1)
        | ~ l1_struct_0(sK3) )
    | ~ spl11_346 ),
    inference(resolution,[],[f3671,f190])).

fof(f3671,plain,
    ( ! [X0] :
        ( r1_tsep_1(sK3,X0)
        | ~ l1_struct_0(X0)
        | k3_xboole_0(u1_struct_0(sK3),u1_struct_0(X0)) != k1_xboole_0 )
    | ~ spl11_346 ),
    inference(avatar_component_clause,[],[f3670])).

fof(f18612,plain,
    ( spl11_475
    | ~ spl11_592 ),
    inference(avatar_contradiction_clause,[],[f18609])).

fof(f18609,plain,
    ( $false
    | ~ spl11_475
    | ~ spl11_592 ),
    inference(unit_resulting_resolution,[],[f11078,f8239,f167])).

fof(f8239,plain,
    ( k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) != k1_xboole_0
    | ~ spl11_475 ),
    inference(avatar_component_clause,[],[f8238])).

fof(f8238,plain,
    ( spl11_475
  <=> k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) != k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_475])])).

fof(f11078,plain,
    ( v1_xboole_0(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)))
    | ~ spl11_592 ),
    inference(avatar_component_clause,[],[f11077])).

fof(f13409,plain,
    ( ~ spl11_673
    | spl11_667 ),
    inference(avatar_split_clause,[],[f13168,f13125,f13407])).

fof(f13125,plain,
    ( spl11_667
  <=> ~ r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_667])])).

fof(f13168,plain,
    ( k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)) != k1_xboole_0
    | ~ spl11_667 ),
    inference(resolution,[],[f13126,f192])).

fof(f192,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f111])).

fof(f13126,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ spl11_667 ),
    inference(avatar_component_clause,[],[f13125])).

fof(f13401,plain,
    ( ~ spl11_671
    | spl11_667 ),
    inference(avatar_split_clause,[],[f13167,f13125,f13399])).

fof(f13399,plain,
    ( spl11_671
  <=> k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2)) != k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_671])])).

fof(f13167,plain,
    ( k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2)) != k1_xboole_0
    | ~ spl11_667 ),
    inference(resolution,[],[f13126,f378])).

fof(f378,plain,(
    ! [X2,X3] :
      ( r1_xboole_0(X3,X2)
      | k3_xboole_0(X2,X3) != k1_xboole_0 ) ),
    inference(resolution,[],[f192,f182])).

fof(f182,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f40])).

fof(f40,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t39_tmap_1.p',symmetry_r1_xboole_0)).

fof(f13147,plain,
    ( ~ spl11_32
    | spl11_669 ),
    inference(avatar_contradiction_clause,[],[f13146])).

fof(f13146,plain,
    ( $false
    | ~ spl11_32
    | ~ spl11_669 ),
    inference(subsumption_resolution,[],[f13144,f363])).

fof(f363,plain,
    ( l1_pre_topc(sK2)
    | ~ spl11_32 ),
    inference(avatar_component_clause,[],[f362])).

fof(f362,plain,
    ( spl11_32
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_32])])).

fof(f13144,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ spl11_669 ),
    inference(resolution,[],[f13141,f168])).

fof(f168,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t39_tmap_1.p',dt_l1_pre_topc)).

fof(f13141,plain,
    ( ~ l1_struct_0(sK2)
    | ~ spl11_669 ),
    inference(avatar_component_clause,[],[f13140])).

fof(f13140,plain,
    ( spl11_669
  <=> ~ l1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_669])])).

fof(f13142,plain,
    ( ~ spl11_669
    | spl11_65
    | ~ spl11_102
    | ~ spl11_666 ),
    inference(avatar_split_clause,[],[f13135,f13128,f903,f584,f13140])).

fof(f13135,plain,
    ( ~ l1_struct_0(sK2)
    | ~ spl11_65
    | ~ spl11_102
    | ~ spl11_666 ),
    inference(subsumption_resolution,[],[f13134,f904])).

fof(f13134,plain,
    ( ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | ~ spl11_65
    | ~ spl11_666 ),
    inference(subsumption_resolution,[],[f13131,f585])).

fof(f13131,plain,
    ( r1_tsep_1(sK2,sK3)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | ~ spl11_666 ),
    inference(resolution,[],[f13129,f166])).

fof(f166,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f105])).

fof(f12269,plain,
    ( spl11_634
    | ~ spl11_236 ),
    inference(avatar_split_clause,[],[f7743,f2424,f12233])).

fof(f2424,plain,
    ( spl11_236
  <=> k3_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK3)) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_236])])).

fof(f7743,plain,
    ( k3_xboole_0(u1_struct_0(sK3),u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) = k1_xboole_0
    | ~ spl11_236 ),
    inference(forward_demodulation,[],[f7682,f163])).

fof(f7682,plain,
    ( k2_xboole_0(k1_xboole_0,k1_xboole_0) = k3_xboole_0(u1_struct_0(sK3),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    | ~ spl11_236 ),
    inference(superposition,[],[f1003,f2425])).

fof(f2425,plain,
    ( k3_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK3)) = k1_xboole_0
    | ~ spl11_236 ),
    inference(avatar_component_clause,[],[f2424])).

fof(f1003,plain,(
    ! [X14,X15] : k2_xboole_0(k1_xboole_0,k3_xboole_0(X15,X14)) = k3_xboole_0(X14,X15) ),
    inference(forward_demodulation,[],[f981,f338])).

fof(f338,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f180,f163])).

fof(f981,plain,(
    ! [X14,X15] : k2_xboole_0(k1_xboole_0,k3_xboole_0(X15,X14)) = k3_xboole_0(X14,k2_xboole_0(k1_xboole_0,X15)) ),
    inference(superposition,[],[f449,f164])).

fof(f164,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f45])).

fof(f45,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t39_tmap_1.p',t2_boole)).

fof(f449,plain,(
    ! [X6,X4,X5] : k2_xboole_0(k3_xboole_0(X4,X6),k3_xboole_0(X5,X4)) = k3_xboole_0(X4,k2_xboole_0(X6,X5)) ),
    inference(superposition,[],[f197,f179])).

fof(f10753,plain,
    ( spl11_590
    | ~ spl11_588 ),
    inference(avatar_split_clause,[],[f10675,f10664,f10751])).

fof(f10664,plain,
    ( spl11_588
  <=> r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_588])])).

fof(f10675,plain,
    ( k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK1)) = k1_xboole_0
    | ~ spl11_588 ),
    inference(resolution,[],[f10665,f191])).

fof(f10665,plain,
    ( r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ spl11_588 ),
    inference(avatar_component_clause,[],[f10664])).

fof(f10666,plain,
    ( spl11_588
    | ~ spl11_56
    | ~ spl11_102
    | ~ spl11_466 ),
    inference(avatar_split_clause,[],[f10651,f7541,f903,f527,f10664])).

fof(f527,plain,
    ( spl11_56
  <=> r1_tsep_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_56])])).

fof(f7541,plain,
    ( spl11_466
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_466])])).

fof(f10651,plain,
    ( r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ spl11_56
    | ~ spl11_102
    | ~ spl11_466 ),
    inference(subsumption_resolution,[],[f10650,f904])).

fof(f10650,plain,
    ( r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ l1_struct_0(sK3)
    | ~ spl11_56
    | ~ spl11_466 ),
    inference(subsumption_resolution,[],[f10648,f7542])).

fof(f7542,plain,
    ( l1_struct_0(sK1)
    | ~ spl11_466 ),
    inference(avatar_component_clause,[],[f7541])).

fof(f10648,plain,
    ( r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK3)
    | ~ spl11_56 ),
    inference(resolution,[],[f528,f165])).

fof(f528,plain,
    ( r1_tsep_1(sK3,sK1)
    | ~ spl11_56 ),
    inference(avatar_component_clause,[],[f527])).

fof(f10647,plain,
    ( spl11_56
    | ~ spl11_52
    | ~ spl11_102
    | ~ spl11_466 ),
    inference(avatar_split_clause,[],[f10642,f7541,f903,f515,f527])).

fof(f515,plain,
    ( spl11_52
  <=> r1_tsep_1(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_52])])).

fof(f10642,plain,
    ( r1_tsep_1(sK3,sK1)
    | ~ spl11_52
    | ~ spl11_102
    | ~ spl11_466 ),
    inference(subsumption_resolution,[],[f10641,f7542])).

fof(f10641,plain,
    ( r1_tsep_1(sK3,sK1)
    | ~ l1_struct_0(sK1)
    | ~ spl11_52
    | ~ spl11_102 ),
    inference(subsumption_resolution,[],[f10633,f904])).

fof(f10633,plain,
    ( r1_tsep_1(sK3,sK1)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK1)
    | ~ spl11_52 ),
    inference(resolution,[],[f516,f190])).

fof(f516,plain,
    ( r1_tsep_1(sK1,sK3)
    | ~ spl11_52 ),
    inference(avatar_component_clause,[],[f515])).

fof(f10646,plain,
    ( ~ spl11_65
    | ~ spl11_57
    | ~ spl11_177
    | ~ spl11_52
    | ~ spl11_54
    | ~ spl11_58 ),
    inference(avatar_split_clause,[],[f10645,f533,f521,f515,f1950,f524,f584])).

fof(f524,plain,
    ( spl11_57
  <=> ~ r1_tsep_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_57])])).

fof(f521,plain,
    ( spl11_54
  <=> r1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_54])])).

fof(f533,plain,
    ( spl11_58
  <=> r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_58])])).

fof(f10645,plain,
    ( ~ r1_tsep_1(sK3,sK2)
    | ~ r1_tsep_1(sK3,sK1)
    | ~ r1_tsep_1(sK2,sK3)
    | ~ spl11_52
    | ~ spl11_54
    | ~ spl11_58 ),
    inference(subsumption_resolution,[],[f10644,f522])).

fof(f522,plain,
    ( r1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK3)
    | ~ spl11_54 ),
    inference(avatar_component_clause,[],[f521])).

fof(f10644,plain,
    ( ~ r1_tsep_1(sK3,sK2)
    | ~ r1_tsep_1(sK3,sK1)
    | ~ r1_tsep_1(sK2,sK3)
    | ~ r1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK3)
    | ~ spl11_52
    | ~ spl11_58 ),
    inference(subsumption_resolution,[],[f10643,f516])).

fof(f10643,plain,
    ( ~ r1_tsep_1(sK3,sK2)
    | ~ r1_tsep_1(sK3,sK1)
    | ~ r1_tsep_1(sK2,sK3)
    | ~ r1_tsep_1(sK1,sK3)
    | ~ r1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK3)
    | ~ spl11_58 ),
    inference(subsumption_resolution,[],[f126,f534])).

fof(f534,plain,
    ( r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2))
    | ~ spl11_58 ),
    inference(avatar_component_clause,[],[f533])).

fof(f126,plain,
    ( ~ r1_tsep_1(sK3,sK2)
    | ~ r1_tsep_1(sK3,sK1)
    | ~ r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2))
    | ~ r1_tsep_1(sK2,sK3)
    | ~ r1_tsep_1(sK1,sK3)
    | ~ r1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f104])).

fof(f8240,plain,
    ( ~ spl11_475
    | spl11_53
    | ~ spl11_102
    | ~ spl11_472 ),
    inference(avatar_split_clause,[],[f7863,f7854,f903,f512,f8238])).

fof(f512,plain,
    ( spl11_53
  <=> ~ r1_tsep_1(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_53])])).

fof(f7854,plain,
    ( spl11_472
  <=> ! [X2] :
        ( ~ l1_struct_0(X2)
        | r1_tsep_1(sK1,X2)
        | k3_xboole_0(u1_struct_0(sK1),u1_struct_0(X2)) != k1_xboole_0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_472])])).

fof(f7863,plain,
    ( k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) != k1_xboole_0
    | ~ spl11_53
    | ~ spl11_102
    | ~ spl11_472 ),
    inference(subsumption_resolution,[],[f7858,f904])).

fof(f7858,plain,
    ( ~ l1_struct_0(sK3)
    | k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) != k1_xboole_0
    | ~ spl11_53
    | ~ spl11_472 ),
    inference(resolution,[],[f7855,f513])).

fof(f513,plain,
    ( ~ r1_tsep_1(sK1,sK3)
    | ~ spl11_53 ),
    inference(avatar_component_clause,[],[f512])).

fof(f7855,plain,
    ( ! [X2] :
        ( r1_tsep_1(sK1,X2)
        | ~ l1_struct_0(X2)
        | k3_xboole_0(u1_struct_0(sK1),u1_struct_0(X2)) != k1_xboole_0 )
    | ~ spl11_472 ),
    inference(avatar_component_clause,[],[f7854])).

fof(f7856,plain,
    ( spl11_472
    | ~ spl11_466 ),
    inference(avatar_split_clause,[],[f7558,f7541,f7854])).

fof(f7558,plain,
    ( ! [X2] :
        ( ~ l1_struct_0(X2)
        | r1_tsep_1(sK1,X2)
        | k3_xboole_0(u1_struct_0(sK1),u1_struct_0(X2)) != k1_xboole_0 )
    | ~ spl11_466 ),
    inference(resolution,[],[f7542,f418])).

fof(f418,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ l1_struct_0(X1)
      | r1_tsep_1(X0,X1)
      | k3_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) != k1_xboole_0 ) ),
    inference(resolution,[],[f166,f192])).

fof(f7553,plain,
    ( ~ spl11_30
    | spl11_467 ),
    inference(avatar_contradiction_clause,[],[f7552])).

fof(f7552,plain,
    ( $false
    | ~ spl11_30
    | ~ spl11_467 ),
    inference(subsumption_resolution,[],[f7550,f356])).

fof(f356,plain,
    ( l1_pre_topc(sK1)
    | ~ spl11_30 ),
    inference(avatar_component_clause,[],[f355])).

fof(f355,plain,
    ( spl11_30
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_30])])).

fof(f7550,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ spl11_467 ),
    inference(resolution,[],[f7545,f168])).

fof(f7545,plain,
    ( ~ l1_struct_0(sK1)
    | ~ spl11_467 ),
    inference(avatar_component_clause,[],[f7544])).

fof(f7544,plain,
    ( spl11_467
  <=> ~ l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_467])])).

fof(f3672,plain,
    ( spl11_346
    | ~ spl11_102 ),
    inference(avatar_split_clause,[],[f2019,f903,f3670])).

fof(f2019,plain,
    ( ! [X0] :
        ( ~ l1_struct_0(X0)
        | r1_tsep_1(sK3,X0)
        | k3_xboole_0(u1_struct_0(sK3),u1_struct_0(X0)) != k1_xboole_0 )
    | ~ spl11_102 ),
    inference(resolution,[],[f904,f418])).

fof(f2858,plain,
    ( spl11_264
    | spl11_9
    | ~ spl11_20
    | ~ spl11_130 ),
    inference(avatar_split_clause,[],[f1310,f1267,f295,f253,f2856])).

fof(f253,plain,
    ( spl11_9
  <=> ~ v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_9])])).

fof(f295,plain,
    ( spl11_20
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_20])])).

fof(f1267,plain,
    ( spl11_130
  <=> ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | u1_struct_0(k1_tsep_1(sK0,sK1,X0)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_130])])).

fof(f1310,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ spl11_9
    | ~ spl11_20
    | ~ spl11_130 ),
    inference(subsumption_resolution,[],[f1305,f254])).

fof(f254,plain,
    ( ~ v2_struct_0(sK2)
    | ~ spl11_9 ),
    inference(avatar_component_clause,[],[f253])).

fof(f1305,plain,
    ( v2_struct_0(sK2)
    | u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ spl11_20
    | ~ spl11_130 ),
    inference(resolution,[],[f1268,f296])).

fof(f296,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl11_20 ),
    inference(avatar_component_clause,[],[f295])).

fof(f1268,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | u1_struct_0(k1_tsep_1(sK0,sK1,X0)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0)) )
    | ~ spl11_130 ),
    inference(avatar_component_clause,[],[f1267])).

fof(f2426,plain,
    ( spl11_236
    | ~ spl11_172 ),
    inference(avatar_split_clause,[],[f2043,f1931,f2424])).

fof(f1931,plain,
    ( spl11_172
  <=> r1_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_172])])).

fof(f2043,plain,
    ( k3_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK3)) = k1_xboole_0
    | ~ spl11_172 ),
    inference(resolution,[],[f1932,f191])).

fof(f1932,plain,
    ( r1_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK3))
    | ~ spl11_172 ),
    inference(avatar_component_clause,[],[f1931])).

fof(f2015,plain,
    ( ~ spl11_34
    | spl11_103 ),
    inference(avatar_contradiction_clause,[],[f2014])).

fof(f2014,plain,
    ( $false
    | ~ spl11_34
    | ~ spl11_103 ),
    inference(subsumption_resolution,[],[f2012,f371])).

fof(f371,plain,
    ( l1_pre_topc(sK3)
    | ~ spl11_34 ),
    inference(avatar_component_clause,[],[f370])).

fof(f370,plain,
    ( spl11_34
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_34])])).

fof(f2012,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ spl11_103 ),
    inference(resolution,[],[f907,f168])).

fof(f907,plain,
    ( ~ l1_struct_0(sK3)
    | ~ spl11_103 ),
    inference(avatar_component_clause,[],[f906])).

fof(f906,plain,
    ( spl11_103
  <=> ~ l1_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_103])])).

fof(f2004,plain,
    ( ~ spl11_103
    | spl11_55
    | ~ spl11_58
    | ~ spl11_100 ),
    inference(avatar_split_clause,[],[f2003,f897,f533,f518,f906])).

fof(f2003,plain,
    ( ~ l1_struct_0(sK3)
    | ~ spl11_55
    | ~ spl11_58
    | ~ spl11_100 ),
    inference(subsumption_resolution,[],[f1934,f519])).

fof(f1934,plain,
    ( r1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK3)
    | ~ l1_struct_0(sK3)
    | ~ spl11_58
    | ~ spl11_100 ),
    inference(subsumption_resolution,[],[f1913,f898])).

fof(f1913,plain,
    ( r1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK3)
    | ~ l1_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ l1_struct_0(sK3)
    | ~ spl11_58 ),
    inference(resolution,[],[f534,f190])).

fof(f1933,plain,
    ( ~ spl11_103
    | spl11_172
    | ~ spl11_54
    | ~ spl11_100 ),
    inference(avatar_split_clause,[],[f1915,f897,f521,f1931,f906])).

fof(f1915,plain,
    ( r1_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK3))
    | ~ l1_struct_0(sK3)
    | ~ spl11_54
    | ~ spl11_100 ),
    inference(subsumption_resolution,[],[f537,f898])).

fof(f537,plain,
    ( r1_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK3))
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ spl11_54 ),
    inference(resolution,[],[f522,f165])).

fof(f1879,plain,
    ( ~ spl11_4
    | spl11_107
    | ~ spl11_170 ),
    inference(avatar_contradiction_clause,[],[f1857])).

fof(f1857,plain,
    ( $false
    | ~ spl11_4
    | ~ spl11_107
    | ~ spl11_170 ),
    inference(unit_resulting_resolution,[],[f240,f974,f1832,f171])).

fof(f171,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t39_tmap_1.p',dt_m1_pre_topc)).

fof(f1832,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | ~ spl11_170 ),
    inference(avatar_component_clause,[],[f1831])).

fof(f1831,plain,
    ( spl11_170
  <=> m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_170])])).

fof(f974,plain,
    ( ~ l1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ spl11_107 ),
    inference(avatar_component_clause,[],[f973])).

fof(f973,plain,
    ( spl11_107
  <=> ~ l1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_107])])).

fof(f240,plain,
    ( l1_pre_topc(sK0)
    | ~ spl11_4 ),
    inference(avatar_component_clause,[],[f239])).

fof(f239,plain,
    ( spl11_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f1833,plain,
    ( spl11_170
    | spl11_7
    | ~ spl11_18
    | ~ spl11_86
    | ~ spl11_162 ),
    inference(avatar_split_clause,[],[f1818,f1778,f752,f288,f246,f1831])).

fof(f246,plain,
    ( spl11_7
  <=> ~ v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).

fof(f288,plain,
    ( spl11_18
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_18])])).

fof(f752,plain,
    ( spl11_86
  <=> ! [X1] :
        ( ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | m1_pre_topc(k1_tsep_1(sK0,sK2,X1),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_86])])).

fof(f1778,plain,
    ( spl11_162
  <=> k1_tsep_1(sK0,sK1,sK2) = k1_tsep_1(sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_162])])).

fof(f1818,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | ~ spl11_7
    | ~ spl11_18
    | ~ spl11_86
    | ~ spl11_162 ),
    inference(subsumption_resolution,[],[f1817,f289])).

fof(f289,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl11_18 ),
    inference(avatar_component_clause,[],[f288])).

fof(f1817,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ spl11_7
    | ~ spl11_86
    | ~ spl11_162 ),
    inference(subsumption_resolution,[],[f1812,f247])).

fof(f247,plain,
    ( ~ v2_struct_0(sK1)
    | ~ spl11_7 ),
    inference(avatar_component_clause,[],[f246])).

fof(f1812,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ spl11_86
    | ~ spl11_162 ),
    inference(superposition,[],[f753,f1779])).

fof(f1779,plain,
    ( k1_tsep_1(sK0,sK1,sK2) = k1_tsep_1(sK0,sK2,sK1)
    | ~ spl11_162 ),
    inference(avatar_component_clause,[],[f1778])).

fof(f753,plain,
    ( ! [X1] :
        ( m1_pre_topc(k1_tsep_1(sK0,sK2,X1),sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0) )
    | ~ spl11_86 ),
    inference(avatar_component_clause,[],[f752])).

fof(f1790,plain,
    ( spl11_162
    | spl11_7
    | ~ spl11_18
    | ~ spl11_120 ),
    inference(avatar_split_clause,[],[f1146,f1111,f288,f246,f1778])).

fof(f1111,plain,
    ( spl11_120
  <=> ! [X1] :
        ( ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | k1_tsep_1(sK0,X1,sK2) = k1_tsep_1(sK0,sK2,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_120])])).

fof(f1146,plain,
    ( k1_tsep_1(sK0,sK1,sK2) = k1_tsep_1(sK0,sK2,sK1)
    | ~ spl11_7
    | ~ spl11_18
    | ~ spl11_120 ),
    inference(subsumption_resolution,[],[f1142,f247])).

fof(f1142,plain,
    ( v2_struct_0(sK1)
    | k1_tsep_1(sK0,sK1,sK2) = k1_tsep_1(sK0,sK2,sK1)
    | ~ spl11_18
    | ~ spl11_120 ),
    inference(resolution,[],[f1112,f289])).

fof(f1112,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | k1_tsep_1(sK0,X1,sK2) = k1_tsep_1(sK0,sK2,X1) )
    | ~ spl11_120 ),
    inference(avatar_component_clause,[],[f1111])).

fof(f1269,plain,
    ( spl11_130
    | spl11_1
    | ~ spl11_4
    | spl11_7
    | ~ spl11_18 ),
    inference(avatar_split_clause,[],[f633,f288,f246,f239,f225,f1267])).

fof(f225,plain,
    ( spl11_1
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f633,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | u1_struct_0(k1_tsep_1(sK0,sK1,X0)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0)) )
    | ~ spl11_1
    | ~ spl11_4
    | ~ spl11_7
    | ~ spl11_18 ),
    inference(subsumption_resolution,[],[f632,f226])).

fof(f226,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl11_1 ),
    inference(avatar_component_clause,[],[f225])).

fof(f632,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | u1_struct_0(k1_tsep_1(sK0,sK1,X0)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0))
        | v2_struct_0(sK0) )
    | ~ spl11_4
    | ~ spl11_7
    | ~ spl11_18 ),
    inference(subsumption_resolution,[],[f631,f240])).

fof(f631,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | u1_struct_0(k1_tsep_1(sK0,sK1,X0)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0))
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl11_7
    | ~ spl11_18 ),
    inference(subsumption_resolution,[],[f626,f247])).

fof(f626,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | u1_struct_0(k1_tsep_1(sK0,sK1,X0)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0))
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl11_18 ),
    inference(resolution,[],[f618,f289])).

fof(f618,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | u1_struct_0(k1_tsep_1(X0,X1,X2)) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f617,f203])).

fof(f203,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f88])).

fof(f88,plain,(
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
    inference(flattening,[],[f87])).

fof(f87,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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
    file('/export/starexec/sandbox/benchmark/tmap_1__t39_tmap_1.p',dt_k1_tsep_1)).

fof(f617,plain,(
    ! [X2,X0,X1] :
      ( u1_struct_0(k1_tsep_1(X0,X1,X2)) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
      | v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f616,f204])).

fof(f204,plain,(
    ! [X2,X0,X1] :
      ( v1_pre_topc(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f88])).

fof(f616,plain,(
    ! [X2,X0,X1] :
      ( u1_struct_0(k1_tsep_1(X0,X1,X2)) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
      | ~ v1_pre_topc(k1_tsep_1(X0,X1,X2))
      | v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f214,f205])).

fof(f205,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f88])).

fof(f214,plain,(
    ! [X2,X0,X1] :
      ( u1_struct_0(k1_tsep_1(X0,X1,X2)) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ v1_pre_topc(k1_tsep_1(X0,X1,X2))
      | v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f174])).

fof(f174,plain,(
    ! [X2,X0,X3,X1] :
      ( u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
      | k1_tsep_1(X0,X1,X2) != X3
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_pre_topc(X3)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f108])).

fof(f108,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k1_tsep_1(X0,X1,X2) = X3
                      | u1_struct_0(X3) != k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                    & ( u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
                      | k1_tsep_1(X0,X1,X2) != X3 ) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k1_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f67])).

fof(f67,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k1_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & v1_pre_topc(X3)
                    & ~ v2_struct_0(X3) )
                 => ( k1_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t39_tmap_1.p',d2_tsep_1)).

fof(f1113,plain,
    ( spl11_120
    | spl11_1
    | ~ spl11_4
    | spl11_9
    | ~ spl11_20 ),
    inference(avatar_split_clause,[],[f604,f295,f253,f239,f225,f1111])).

fof(f604,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | k1_tsep_1(sK0,X1,sK2) = k1_tsep_1(sK0,sK2,X1) )
    | ~ spl11_1
    | ~ spl11_4
    | ~ spl11_9
    | ~ spl11_20 ),
    inference(subsumption_resolution,[],[f603,f226])).

fof(f603,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | k1_tsep_1(sK0,X1,sK2) = k1_tsep_1(sK0,sK2,X1)
        | v2_struct_0(sK0) )
    | ~ spl11_4
    | ~ spl11_9
    | ~ spl11_20 ),
    inference(subsumption_resolution,[],[f602,f240])).

fof(f602,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | k1_tsep_1(sK0,X1,sK2) = k1_tsep_1(sK0,sK2,X1)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl11_9
    | ~ spl11_20 ),
    inference(subsumption_resolution,[],[f595,f254])).

fof(f595,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | k1_tsep_1(sK0,X1,sK2) = k1_tsep_1(sK0,sK2,X1)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl11_20 ),
    inference(resolution,[],[f202,f296])).

fof(f202,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f86,plain,(
    ! [X0,X1,X2] :
      ( k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f85])).

fof(f85,plain,(
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
    file('/export/starexec/sandbox/benchmark/tmap_1__t39_tmap_1.p',commutativity_k1_tsep_1)).

fof(f975,plain,
    ( ~ spl11_107
    | spl11_101 ),
    inference(avatar_split_clause,[],[f910,f900,f973])).

fof(f900,plain,
    ( spl11_101
  <=> ~ l1_struct_0(k1_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_101])])).

fof(f910,plain,
    ( ~ l1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ spl11_101 ),
    inference(resolution,[],[f901,f168])).

fof(f901,plain,
    ( ~ l1_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ spl11_101 ),
    inference(avatar_component_clause,[],[f900])).

fof(f908,plain,
    ( ~ spl11_101
    | ~ spl11_103
    | spl11_58
    | ~ spl11_54 ),
    inference(avatar_split_clause,[],[f538,f521,f533,f906,f900])).

fof(f538,plain,
    ( r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2))
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ spl11_54 ),
    inference(resolution,[],[f522,f190])).

fof(f754,plain,
    ( spl11_86
    | spl11_1
    | ~ spl11_4
    | spl11_9
    | ~ spl11_20 ),
    inference(avatar_split_clause,[],[f566,f295,f253,f239,f225,f752])).

fof(f566,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | m1_pre_topc(k1_tsep_1(sK0,sK2,X1),sK0) )
    | ~ spl11_1
    | ~ spl11_4
    | ~ spl11_9
    | ~ spl11_20 ),
    inference(subsumption_resolution,[],[f565,f226])).

fof(f565,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | m1_pre_topc(k1_tsep_1(sK0,sK2,X1),sK0)
        | v2_struct_0(sK0) )
    | ~ spl11_4
    | ~ spl11_9
    | ~ spl11_20 ),
    inference(subsumption_resolution,[],[f564,f240])).

fof(f564,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | m1_pre_topc(k1_tsep_1(sK0,sK2,X1),sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl11_9
    | ~ spl11_20 ),
    inference(subsumption_resolution,[],[f557,f254])).

fof(f557,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | m1_pre_topc(k1_tsep_1(sK0,sK2,X1),sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl11_20 ),
    inference(resolution,[],[f205,f296])).

fof(f535,plain,
    ( spl11_52
    | spl11_54
    | spl11_56
    | spl11_58 ),
    inference(avatar_split_clause,[],[f154,f533,f527,f521,f515])).

fof(f154,plain,
    ( r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2))
    | r1_tsep_1(sK3,sK1)
    | r1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK3)
    | r1_tsep_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f104])).

fof(f372,plain,
    ( spl11_34
    | ~ spl11_22
    | ~ spl11_28 ),
    inference(avatar_split_clause,[],[f346,f335,f302,f370])).

fof(f302,plain,
    ( spl11_22
  <=> m1_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_22])])).

fof(f335,plain,
    ( spl11_28
  <=> ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_28])])).

fof(f346,plain,
    ( l1_pre_topc(sK3)
    | ~ spl11_22
    | ~ spl11_28 ),
    inference(resolution,[],[f336,f303])).

fof(f303,plain,
    ( m1_pre_topc(sK3,sK0)
    | ~ spl11_22 ),
    inference(avatar_component_clause,[],[f302])).

fof(f336,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | l1_pre_topc(X0) )
    | ~ spl11_28 ),
    inference(avatar_component_clause,[],[f335])).

fof(f364,plain,
    ( spl11_32
    | ~ spl11_20
    | ~ spl11_28 ),
    inference(avatar_split_clause,[],[f345,f335,f295,f362])).

fof(f345,plain,
    ( l1_pre_topc(sK2)
    | ~ spl11_20
    | ~ spl11_28 ),
    inference(resolution,[],[f336,f296])).

fof(f357,plain,
    ( spl11_30
    | ~ spl11_18
    | ~ spl11_28 ),
    inference(avatar_split_clause,[],[f344,f335,f288,f355])).

fof(f344,plain,
    ( l1_pre_topc(sK1)
    | ~ spl11_18
    | ~ spl11_28 ),
    inference(resolution,[],[f336,f289])).

fof(f337,plain,
    ( spl11_28
    | ~ spl11_4 ),
    inference(avatar_split_clause,[],[f328,f239,f335])).

fof(f328,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | l1_pre_topc(X0) )
    | ~ spl11_4 ),
    inference(resolution,[],[f171,f240])).

fof(f320,plain,
    ( spl11_26
    | ~ spl11_12 ),
    inference(avatar_split_clause,[],[f306,f267,f318])).

fof(f267,plain,
    ( spl11_12
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).

fof(f306,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl11_12 ),
    inference(backward_demodulation,[],[f305,f268])).

fof(f268,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl11_12 ),
    inference(avatar_component_clause,[],[f267])).

fof(f305,plain,
    ( k1_xboole_0 = o_0_0_xboole_0
    | ~ spl11_12 ),
    inference(resolution,[],[f167,f268])).

fof(f304,plain,(
    spl11_22 ),
    inference(avatar_split_clause,[],[f125,f302])).

fof(f125,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f104])).

fof(f297,plain,(
    spl11_20 ),
    inference(avatar_split_clause,[],[f123,f295])).

fof(f123,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f104])).

fof(f290,plain,(
    spl11_18 ),
    inference(avatar_split_clause,[],[f121,f288])).

fof(f121,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f104])).

fof(f269,plain,(
    spl11_12 ),
    inference(avatar_split_clause,[],[f162,f267])).

fof(f162,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t39_tmap_1.p',dt_o_0_0_xboole_0)).

fof(f255,plain,(
    ~ spl11_9 ),
    inference(avatar_split_clause,[],[f122,f253])).

fof(f122,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f104])).

fof(f248,plain,(
    ~ spl11_7 ),
    inference(avatar_split_clause,[],[f120,f246])).

fof(f120,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f104])).

fof(f241,plain,(
    spl11_4 ),
    inference(avatar_split_clause,[],[f119,f239])).

fof(f119,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f104])).

fof(f227,plain,(
    ~ spl11_1 ),
    inference(avatar_split_clause,[],[f117,f225])).

fof(f117,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f104])).
%------------------------------------------------------------------------------
