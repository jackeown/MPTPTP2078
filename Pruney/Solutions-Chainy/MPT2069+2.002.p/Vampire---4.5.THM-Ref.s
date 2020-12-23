%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:36 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  231 (1624 expanded)
%              Number of leaves         :   29 ( 575 expanded)
%              Depth                    :   25
%              Number of atoms          : 1273 (24683 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f376,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f115,f142,f179,f182,f205,f245,f248,f277,f282,f285,f301,f375])).

fof(f375,plain,
    ( ~ spl14_1
    | ~ spl14_6
    | spl14_7 ),
    inference(avatar_contradiction_clause,[],[f374])).

fof(f374,plain,
    ( $false
    | ~ spl14_1
    | ~ spl14_6
    | spl14_7 ),
    inference(subsumption_resolution,[],[f373,f302])).

fof(f302,plain,
    ( ~ r2_hidden(sK9,sK7)
    | ~ spl14_1 ),
    inference(subsumption_resolution,[],[f62,f109])).

fof(f109,plain,
    ( v4_pre_topc(sK7,sK6)
    | ~ spl14_1 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl14_1
  <=> v4_pre_topc(sK7,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_1])])).

fof(f62,plain,
    ( ~ r2_hidden(sK9,sK7)
    | ~ v4_pre_topc(sK7,sK6) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ( ( ~ r2_hidden(sK9,sK7)
        & r1_waybel_7(sK6,sK8,sK9)
        & m1_subset_1(sK9,u1_struct_0(sK6))
        & r2_hidden(sK7,sK8)
        & m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
        & v13_waybel_0(sK8,k3_yellow_1(k2_struct_0(sK6)))
        & v2_waybel_0(sK8,k3_yellow_1(k2_struct_0(sK6)))
        & v1_subset_1(sK8,u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))
        & ~ v1_xboole_0(sK8) )
      | ~ v4_pre_topc(sK7,sK6) )
    & ( ! [X4] :
          ( ! [X5] :
              ( r2_hidden(X5,sK7)
              | ~ r1_waybel_7(sK6,X4,X5)
              | ~ m1_subset_1(X5,u1_struct_0(sK6)) )
          | ~ r2_hidden(sK7,X4)
          | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
          | ~ v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK6)))
          | ~ v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK6)))
          | ~ v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))
          | v1_xboole_0(X4) )
      | v4_pre_topc(sK7,sK6) )
    & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    & l1_pre_topc(sK6)
    & v2_pre_topc(sK6)
    & ~ v2_struct_0(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f25,f29,f28,f27,f26])).

fof(f26,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & r1_waybel_7(X0,X2,X3)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & r2_hidden(X1,X2)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                  & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                  & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                  & v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                  & ~ v1_xboole_0(X2) )
              | ~ v4_pre_topc(X1,X0) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | ~ r1_waybel_7(X0,X4,X5)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ r2_hidden(X1,X4)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                  | ~ v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
                  | ~ v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
                  | ~ v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                  | v1_xboole_0(X4) )
              | v4_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(X3,X1)
                    & r1_waybel_7(sK6,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(sK6)) )
                & r2_hidden(X1,X2)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
                & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(sK6)))
                & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(sK6)))
                & v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))
                & ~ v1_xboole_0(X2) )
            | ~ v4_pre_topc(X1,sK6) )
          & ( ! [X4] :
                ( ! [X5] :
                    ( r2_hidden(X5,X1)
                    | ~ r1_waybel_7(sK6,X4,X5)
                    | ~ m1_subset_1(X5,u1_struct_0(sK6)) )
                | ~ r2_hidden(X1,X4)
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
                | ~ v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK6)))
                | ~ v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK6)))
                | ~ v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))
                | v1_xboole_0(X4) )
            | v4_pre_topc(X1,sK6) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) )
      & l1_pre_topc(sK6)
      & v2_pre_topc(sK6)
      & ~ v2_struct_0(sK6) ) ),
    introduced(choice_axiom,[])).

% (25049)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
fof(f27,plain,
    ( ? [X1] :
        ( ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(X3,X1)
                  & r1_waybel_7(sK6,X2,X3)
                  & m1_subset_1(X3,u1_struct_0(sK6)) )
              & r2_hidden(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
              & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(sK6)))
              & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(sK6)))
              & v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))
              & ~ v1_xboole_0(X2) )
          | ~ v4_pre_topc(X1,sK6) )
        & ( ! [X4] :
              ( ! [X5] :
                  ( r2_hidden(X5,X1)
                  | ~ r1_waybel_7(sK6,X4,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(sK6)) )
              | ~ r2_hidden(X1,X4)
              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
              | ~ v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK6)))
              | ~ v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK6)))
              | ~ v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))
              | v1_xboole_0(X4) )
          | v4_pre_topc(X1,sK6) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) )
   => ( ( ? [X2] :
            ( ? [X3] :
                ( ~ r2_hidden(X3,sK7)
                & r1_waybel_7(sK6,X2,X3)
                & m1_subset_1(X3,u1_struct_0(sK6)) )
            & r2_hidden(sK7,X2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
            & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(sK6)))
            & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(sK6)))
            & v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))
            & ~ v1_xboole_0(X2) )
        | ~ v4_pre_topc(sK7,sK6) )
      & ( ! [X4] :
            ( ! [X5] :
                ( r2_hidden(X5,sK7)
                | ~ r1_waybel_7(sK6,X4,X5)
                | ~ m1_subset_1(X5,u1_struct_0(sK6)) )
            | ~ r2_hidden(sK7,X4)
            | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
            | ~ v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK6)))
            | ~ v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK6)))
            | ~ v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))
            | v1_xboole_0(X4) )
        | v4_pre_topc(sK7,sK6) )
      & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ r2_hidden(X3,sK7)
            & r1_waybel_7(sK6,X2,X3)
            & m1_subset_1(X3,u1_struct_0(sK6)) )
        & r2_hidden(sK7,X2)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
        & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(sK6)))
        & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(sK6)))
        & v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))
        & ~ v1_xboole_0(X2) )
   => ( ? [X3] :
          ( ~ r2_hidden(X3,sK7)
          & r1_waybel_7(sK6,sK8,X3)
          & m1_subset_1(X3,u1_struct_0(sK6)) )
      & r2_hidden(sK7,sK8)
      & m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
      & v13_waybel_0(sK8,k3_yellow_1(k2_struct_0(sK6)))
      & v2_waybel_0(sK8,k3_yellow_1(k2_struct_0(sK6)))
      & v1_subset_1(sK8,u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))
      & ~ v1_xboole_0(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X3] :
        ( ~ r2_hidden(X3,sK7)
        & r1_waybel_7(sK6,sK8,X3)
        & m1_subset_1(X3,u1_struct_0(sK6)) )
   => ( ~ r2_hidden(sK9,sK7)
      & r1_waybel_7(sK6,sK8,sK9)
      & m1_subset_1(sK9,u1_struct_0(sK6)) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(X3,X1)
                    & r1_waybel_7(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_hidden(X1,X2)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                & v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                & ~ v1_xboole_0(X2) )
            | ~ v4_pre_topc(X1,X0) )
          & ( ! [X4] :
                ( ! [X5] :
                    ( r2_hidden(X5,X1)
                    | ~ r1_waybel_7(X0,X4,X5)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                | ~ r2_hidden(X1,X4)
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                | ~ v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
                | ~ v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
                | ~ v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                | v1_xboole_0(X4) )
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(X3,X1)
                    & r1_waybel_7(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_hidden(X1,X2)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                & v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                & ~ v1_xboole_0(X2) )
            | ~ v4_pre_topc(X1,X0) )
          & ( ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_waybel_7(X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_hidden(X1,X2)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                | ~ v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                | v1_xboole_0(X2) )
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(X3,X1)
                    & r1_waybel_7(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_hidden(X1,X2)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                & v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                & ~ v1_xboole_0(X2) )
            | ~ v4_pre_topc(X1,X0) )
          & ( ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_waybel_7(X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_hidden(X1,X2)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                | ~ v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                | v1_xboole_0(X2) )
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_waybel_7(X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_hidden(X1,X2)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                | ~ v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                | v1_xboole_0(X2) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_waybel_7(X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_hidden(X1,X2)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                | ~ v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                | v1_xboole_0(X2) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> ! [X2] :
                  ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                    & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                    & v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                    & ~ v1_xboole_0(X2) )
                 => ( r2_hidden(X1,X2)
                   => ! [X3] :
                        ( m1_subset_1(X3,u1_struct_0(X0))
                       => ( r1_waybel_7(X0,X2,X3)
                         => r2_hidden(X3,X1) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                  & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                  & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                  & v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                  & ~ v1_xboole_0(X2) )
               => ( r2_hidden(X1,X2)
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r1_waybel_7(X0,X2,X3)
                       => r2_hidden(X3,X1) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_yellow19)).

fof(f373,plain,
    ( r2_hidden(sK9,sK7)
    | ~ spl14_1
    | ~ spl14_6
    | spl14_7 ),
    inference(subsumption_resolution,[],[f372,f304])).

fof(f304,plain,
    ( m1_subset_1(sK9,u1_struct_0(sK6))
    | ~ spl14_1 ),
    inference(subsumption_resolution,[],[f60,f109])).

fof(f60,plain,
    ( m1_subset_1(sK9,u1_struct_0(sK6))
    | ~ v4_pre_topc(sK7,sK6) ),
    inference(cnf_transformation,[],[f30])).

fof(f372,plain,
    ( ~ m1_subset_1(sK9,u1_struct_0(sK6))
    | r2_hidden(sK9,sK7)
    | ~ spl14_1
    | ~ spl14_6
    | spl14_7 ),
    inference(resolution,[],[f371,f294])).

fof(f294,plain,
    ( r2_hidden(sK9,k10_yellow_6(sK6,sK13(sK6,sK9,sK7)))
    | ~ spl14_6 ),
    inference(resolution,[],[f178,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ sP4(X0,X1,X2)
      | r2_hidden(X1,k10_yellow_6(X0,sK13(X0,X1,X2))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( sP4(X0,X1,X2)
        | ! [X3] :
            ( ~ r2_hidden(X1,k10_yellow_6(X0,X3))
            | ~ r1_waybel_0(X0,X3,X2)
            | ~ l1_waybel_0(X3,X0)
            | ~ v3_yellow_6(X3,X0)
            | ~ v7_waybel_0(X3)
            | ~ v4_orders_2(X3)
            | v2_struct_0(X3) ) )
      & ( ( r2_hidden(X1,k10_yellow_6(X0,sK13(X0,X1,X2)))
          & r1_waybel_0(X0,sK13(X0,X1,X2),X2)
          & l1_waybel_0(sK13(X0,X1,X2),X0)
          & v3_yellow_6(sK13(X0,X1,X2),X0)
          & v7_waybel_0(sK13(X0,X1,X2))
          & v4_orders_2(sK13(X0,X1,X2))
          & ~ v2_struct_0(sK13(X0,X1,X2)) )
        | ~ sP4(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13])],[f46,f47])).

fof(f47,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X1,k10_yellow_6(X0,X4))
          & r1_waybel_0(X0,X4,X2)
          & l1_waybel_0(X4,X0)
          & v3_yellow_6(X4,X0)
          & v7_waybel_0(X4)
          & v4_orders_2(X4)
          & ~ v2_struct_0(X4) )
     => ( r2_hidden(X1,k10_yellow_6(X0,sK13(X0,X1,X2)))
        & r1_waybel_0(X0,sK13(X0,X1,X2),X2)
        & l1_waybel_0(sK13(X0,X1,X2),X0)
        & v3_yellow_6(sK13(X0,X1,X2),X0)
        & v7_waybel_0(sK13(X0,X1,X2))
        & v4_orders_2(sK13(X0,X1,X2))
        & ~ v2_struct_0(sK13(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( sP4(X0,X1,X2)
        | ! [X3] :
            ( ~ r2_hidden(X1,k10_yellow_6(X0,X3))
            | ~ r1_waybel_0(X0,X3,X2)
            | ~ l1_waybel_0(X3,X0)
            | ~ v3_yellow_6(X3,X0)
            | ~ v7_waybel_0(X3)
            | ~ v4_orders_2(X3)
            | v2_struct_0(X3) ) )
      & ( ? [X4] :
            ( r2_hidden(X1,k10_yellow_6(X0,X4))
            & r1_waybel_0(X0,X4,X2)
            & l1_waybel_0(X4,X0)
            & v3_yellow_6(X4,X0)
            & v7_waybel_0(X4)
            & v4_orders_2(X4)
            & ~ v2_struct_0(X4) )
        | ~ sP4(X0,X1,X2) ) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X0,X2,X1] :
      ( ( sP4(X0,X2,X1)
        | ! [X3] :
            ( ~ r2_hidden(X2,k10_yellow_6(X0,X3))
            | ~ r1_waybel_0(X0,X3,X1)
            | ~ l1_waybel_0(X3,X0)
            | ~ v3_yellow_6(X3,X0)
            | ~ v7_waybel_0(X3)
            | ~ v4_orders_2(X3)
            | v2_struct_0(X3) ) )
      & ( ? [X3] :
            ( r2_hidden(X2,k10_yellow_6(X0,X3))
            & r1_waybel_0(X0,X3,X1)
            & l1_waybel_0(X3,X0)
            & v3_yellow_6(X3,X0)
            & v7_waybel_0(X3)
            & v4_orders_2(X3)
            & ~ v2_struct_0(X3) )
        | ~ sP4(X0,X2,X1) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X2,X1] :
      ( sP4(X0,X2,X1)
    <=> ? [X3] :
          ( r2_hidden(X2,k10_yellow_6(X0,X3))
          & r1_waybel_0(X0,X3,X1)
          & l1_waybel_0(X3,X0)
          & v3_yellow_6(X3,X0)
          & v7_waybel_0(X3)
          & v4_orders_2(X3)
          & ~ v2_struct_0(X3) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f178,plain,
    ( sP4(sK6,sK9,sK7)
    | ~ spl14_6 ),
    inference(avatar_component_clause,[],[f176])).

fof(f176,plain,
    ( spl14_6
  <=> sP4(sK6,sK9,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_6])])).

fof(f371,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k10_yellow_6(sK6,sK13(sK6,sK9,sK7)))
        | ~ m1_subset_1(X0,u1_struct_0(sK6))
        | r2_hidden(X0,sK7) )
    | ~ spl14_1
    | ~ spl14_6
    | spl14_7 ),
    inference(subsumption_resolution,[],[f370,f303])).

fof(f303,plain,
    ( sP0(sK7,sK6)
    | ~ spl14_1 ),
    inference(subsumption_resolution,[],[f117,f109])).

% (25054)dis+1_14_awrs=converge:awrsf=256:av=off:bs=on:bsr=on:bce=on:cond=fast:gsp=input_only:gs=on:lcm=predicate:lma=on:nm=4:nwc=1.7:sp=weighted_frequency:urr=on_33 on theBenchmark
fof(f117,plain,
    ( ~ v4_pre_topc(sK7,sK6)
    | sP0(sK7,sK6) ),
    inference(resolution,[],[f116,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | ~ v4_pre_topc(X1,X0)
      | sP0(X1,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ( v4_pre_topc(X1,X0)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ v4_pre_topc(X1,X0) ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( v4_pre_topc(X1,X0)
      <=> sP0(X1,X0) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f116,plain,(
    sP1(sK6,sK7) ),
    inference(resolution,[],[f106,f52])).

fof(f52,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f30])).

fof(f106,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK6)))
      | sP1(sK6,X4) ) ),
    inference(subsumption_resolution,[],[f105,f49])).

fof(f49,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f30])).

fof(f105,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK6)))
      | sP1(sK6,X4)
      | v2_struct_0(sK6) ) ),
    inference(subsumption_resolution,[],[f100,f50])).

fof(f50,plain,(
    v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f30])).

fof(f100,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK6)))
      | sP1(sK6,X4)
      | ~ v2_pre_topc(sK6)
      | v2_struct_0(sK6) ) ),
    inference(resolution,[],[f51,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | sP1(X0,X1)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f9,f15,f14])).

fof(f14,plain,(
    ! [X1,X0] :
      ( sP0(X1,X0)
    <=> ! [X2] :
          ( ! [X3] :
              ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,k10_yellow_6(X0,X2))
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r1_waybel_0(X0,X2,X1)
          | ~ l1_waybel_0(X2,X0)
          | ~ v3_yellow_6(X2,X0)
          | ~ v7_waybel_0(X2)
          | ~ v4_orders_2(X2)
          | v2_struct_0(X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r2_hidden(X3,k10_yellow_6(X0,X2))
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_waybel_0(X0,X2,X1)
                | ~ l1_waybel_0(X2,X0)
                | ~ v3_yellow_6(X2,X0)
                | ~ v7_waybel_0(X2)
                | ~ v4_orders_2(X2)
                | v2_struct_0(X2) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r2_hidden(X3,k10_yellow_6(X0,X2))
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_waybel_0(X0,X2,X1)
                | ~ l1_waybel_0(X2,X0)
                | ~ v3_yellow_6(X2,X0)
                | ~ v7_waybel_0(X2)
                | ~ v4_orders_2(X2)
                | v2_struct_0(X2) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> ! [X2] :
                ( ( l1_waybel_0(X2,X0)
                  & v3_yellow_6(X2,X0)
                  & v7_waybel_0(X2)
                  & v4_orders_2(X2)
                  & ~ v2_struct_0(X2) )
               => ( r1_waybel_0(X0,X2,X1)
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_hidden(X3,k10_yellow_6(X0,X2))
                       => r2_hidden(X3,X1) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_yellow19)).

fof(f51,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f30])).

fof(f370,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK6))
        | ~ r2_hidden(X0,k10_yellow_6(sK6,sK13(sK6,sK9,sK7)))
        | r2_hidden(X0,sK7)
        | ~ sP0(sK7,sK6) )
    | ~ spl14_6
    | spl14_7 ),
    inference(resolution,[],[f369,f293])).

fof(f293,plain,
    ( r1_waybel_0(sK6,sK13(sK6,sK9,sK7),sK7)
    | ~ spl14_6 ),
    inference(resolution,[],[f178,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ sP4(X0,X1,X2)
      | r1_waybel_0(X0,sK13(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f369,plain,
    ( ! [X0,X1] :
        ( ~ r1_waybel_0(sK6,sK13(sK6,sK9,sK7),X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK6))
        | ~ r2_hidden(X0,k10_yellow_6(sK6,sK13(sK6,sK9,sK7)))
        | r2_hidden(X0,X1)
        | ~ sP0(X1,sK6) )
    | ~ spl14_6
    | spl14_7 ),
    inference(subsumption_resolution,[],[f368,f291])).

fof(f291,plain,
    ( v3_yellow_6(sK13(sK6,sK9,sK7),sK6)
    | ~ spl14_6 ),
    inference(resolution,[],[f178,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ sP4(X0,X1,X2)
      | v3_yellow_6(sK13(X0,X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f368,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK6))
        | ~ r1_waybel_0(sK6,sK13(sK6,sK9,sK7),X1)
        | ~ r2_hidden(X0,k10_yellow_6(sK6,sK13(sK6,sK9,sK7)))
        | ~ v3_yellow_6(sK13(sK6,sK9,sK7),sK6)
        | r2_hidden(X0,X1)
        | ~ sP0(X1,sK6) )
    | ~ spl14_6
    | spl14_7 ),
    inference(resolution,[],[f367,f292])).

fof(f292,plain,
    ( l1_waybel_0(sK13(sK6,sK9,sK7),sK6)
    | ~ spl14_6 ),
    inference(resolution,[],[f178,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ sP4(X0,X1,X2)
      | l1_waybel_0(sK13(X0,X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f367,plain,
    ( ! [X4,X5,X3] :
        ( ~ l1_waybel_0(sK13(sK6,sK9,sK7),X4)
        | ~ m1_subset_1(X3,u1_struct_0(X4))
        | ~ r1_waybel_0(X4,sK13(sK6,sK9,sK7),X5)
        | ~ r2_hidden(X3,k10_yellow_6(X4,sK13(sK6,sK9,sK7)))
        | ~ v3_yellow_6(sK13(sK6,sK9,sK7),X4)
        | r2_hidden(X3,X5)
        | ~ sP0(X5,X4) )
    | ~ spl14_6
    | spl14_7 ),
    inference(subsumption_resolution,[],[f298,f196])).

fof(f196,plain,
    ( ~ v2_struct_0(sK13(sK6,sK9,sK7))
    | spl14_7 ),
    inference(avatar_component_clause,[],[f195])).

fof(f195,plain,
    ( spl14_7
  <=> v2_struct_0(sK13(sK6,sK9,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_7])])).

fof(f298,plain,
    ( ! [X4,X5,X3] :
        ( ~ r2_hidden(X3,k10_yellow_6(X4,sK13(sK6,sK9,sK7)))
        | ~ m1_subset_1(X3,u1_struct_0(X4))
        | ~ r1_waybel_0(X4,sK13(sK6,sK9,sK7),X5)
        | ~ l1_waybel_0(sK13(sK6,sK9,sK7),X4)
        | ~ v3_yellow_6(sK13(sK6,sK9,sK7),X4)
        | r2_hidden(X3,X5)
        | v2_struct_0(sK13(sK6,sK9,sK7))
        | ~ sP0(X5,X4) )
    | ~ spl14_6 ),
    inference(subsumption_resolution,[],[f296,f289])).

fof(f289,plain,
    ( v4_orders_2(sK13(sK6,sK9,sK7))
    | ~ spl14_6 ),
    inference(resolution,[],[f178,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ sP4(X0,X1,X2)
      | v4_orders_2(sK13(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f296,plain,
    ( ! [X4,X5,X3] :
        ( ~ r2_hidden(X3,k10_yellow_6(X4,sK13(sK6,sK9,sK7)))
        | ~ m1_subset_1(X3,u1_struct_0(X4))
        | ~ r1_waybel_0(X4,sK13(sK6,sK9,sK7),X5)
        | ~ l1_waybel_0(sK13(sK6,sK9,sK7),X4)
        | ~ v3_yellow_6(sK13(sK6,sK9,sK7),X4)
        | r2_hidden(X3,X5)
        | ~ v4_orders_2(sK13(sK6,sK9,sK7))
        | v2_struct_0(sK13(sK6,sK9,sK7))
        | ~ sP0(X5,X4) )
    | ~ spl14_6 ),
    inference(resolution,[],[f290,f65])).

fof(f65,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ v7_waybel_0(X4)
      | ~ r2_hidden(X5,k10_yellow_6(X1,X4))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ r1_waybel_0(X1,X4,X0)
      | ~ l1_waybel_0(X4,X1)
      | ~ v3_yellow_6(X4,X1)
      | r2_hidden(X5,X0)
      | ~ v4_orders_2(X4)
      | v2_struct_0(X4)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ~ r2_hidden(sK11(X0,X1),X0)
          & r2_hidden(sK11(X0,X1),k10_yellow_6(X1,sK10(X0,X1)))
          & m1_subset_1(sK11(X0,X1),u1_struct_0(X1))
          & r1_waybel_0(X1,sK10(X0,X1),X0)
          & l1_waybel_0(sK10(X0,X1),X1)
          & v3_yellow_6(sK10(X0,X1),X1)
          & v7_waybel_0(sK10(X0,X1))
          & v4_orders_2(sK10(X0,X1))
          & ~ v2_struct_0(sK10(X0,X1)) ) )
      & ( ! [X4] :
            ( ! [X5] :
                ( r2_hidden(X5,X0)
                | ~ r2_hidden(X5,k10_yellow_6(X1,X4))
                | ~ m1_subset_1(X5,u1_struct_0(X1)) )
            | ~ r1_waybel_0(X1,X4,X0)
            | ~ l1_waybel_0(X4,X1)
            | ~ v3_yellow_6(X4,X1)
            | ~ v7_waybel_0(X4)
            | ~ v4_orders_2(X4)
            | v2_struct_0(X4) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11])],[f33,f35,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(X3,X0)
              & r2_hidden(X3,k10_yellow_6(X1,X2))
              & m1_subset_1(X3,u1_struct_0(X1)) )
          & r1_waybel_0(X1,X2,X0)
          & l1_waybel_0(X2,X1)
          & v3_yellow_6(X2,X1)
          & v7_waybel_0(X2)
          & v4_orders_2(X2)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ~ r2_hidden(X3,X0)
            & r2_hidden(X3,k10_yellow_6(X1,sK10(X0,X1)))
            & m1_subset_1(X3,u1_struct_0(X1)) )
        & r1_waybel_0(X1,sK10(X0,X1),X0)
        & l1_waybel_0(sK10(X0,X1),X1)
        & v3_yellow_6(sK10(X0,X1),X1)
        & v7_waybel_0(sK10(X0,X1))
        & v4_orders_2(sK10(X0,X1))
        & ~ v2_struct_0(sK10(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X0)
          & r2_hidden(X3,k10_yellow_6(X1,sK10(X0,X1)))
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r2_hidden(sK11(X0,X1),X0)
        & r2_hidden(sK11(X0,X1),k10_yellow_6(X1,sK10(X0,X1)))
        & m1_subset_1(sK11(X0,X1),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ? [X3] :
                ( ~ r2_hidden(X3,X0)
                & r2_hidden(X3,k10_yellow_6(X1,X2))
                & m1_subset_1(X3,u1_struct_0(X1)) )
            & r1_waybel_0(X1,X2,X0)
            & l1_waybel_0(X2,X1)
            & v3_yellow_6(X2,X1)
            & v7_waybel_0(X2)
            & v4_orders_2(X2)
            & ~ v2_struct_0(X2) ) )
      & ( ! [X4] :
            ( ! [X5] :
                ( r2_hidden(X5,X0)
                | ~ r2_hidden(X5,k10_yellow_6(X1,X4))
                | ~ m1_subset_1(X5,u1_struct_0(X1)) )
            | ~ r1_waybel_0(X1,X4,X0)
            | ~ l1_waybel_0(X4,X1)
            | ~ v3_yellow_6(X4,X1)
            | ~ v7_waybel_0(X4)
            | ~ v4_orders_2(X4)
            | v2_struct_0(X4) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ? [X2] :
            ( ? [X3] :
                ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,k10_yellow_6(X0,X2))
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & r1_waybel_0(X0,X2,X1)
            & l1_waybel_0(X2,X0)
            & v3_yellow_6(X2,X0)
            & v7_waybel_0(X2)
            & v4_orders_2(X2)
            & ~ v2_struct_0(X2) ) )
      & ( ! [X2] :
            ( ! [X3] :
                ( r2_hidden(X3,X1)
                | ~ r2_hidden(X3,k10_yellow_6(X0,X2))
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            | ~ r1_waybel_0(X0,X2,X1)
            | ~ l1_waybel_0(X2,X0)
            | ~ v3_yellow_6(X2,X0)
            | ~ v7_waybel_0(X2)
            | ~ v4_orders_2(X2)
            | v2_struct_0(X2) )
        | ~ sP0(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f290,plain,
    ( v7_waybel_0(sK13(sK6,sK9,sK7))
    | ~ spl14_6 ),
    inference(resolution,[],[f178,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ sP4(X0,X1,X2)
      | v7_waybel_0(sK13(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f301,plain,
    ( ~ spl14_6
    | ~ spl14_7 ),
    inference(avatar_contradiction_clause,[],[f300])).

fof(f300,plain,
    ( $false
    | ~ spl14_6
    | ~ spl14_7 ),
    inference(subsumption_resolution,[],[f299,f178])).

fof(f299,plain,
    ( ~ sP4(sK6,sK9,sK7)
    | ~ spl14_7 ),
    inference(resolution,[],[f197,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(sK13(X0,X1,X2))
      | ~ sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f197,plain,
    ( v2_struct_0(sK13(sK6,sK9,sK7))
    | ~ spl14_7 ),
    inference(avatar_component_clause,[],[f195])).

fof(f285,plain,
    ( ~ spl14_10
    | ~ spl14_12 ),
    inference(avatar_contradiction_clause,[],[f284])).

fof(f284,plain,
    ( $false
    | ~ spl14_10
    | ~ spl14_12 ),
    inference(subsumption_resolution,[],[f283,f244])).

fof(f244,plain,
    ( sP2(sK11(sK7,sK6),sK6,sK7)
    | ~ spl14_10 ),
    inference(avatar_component_clause,[],[f242])).

fof(f242,plain,
    ( spl14_10
  <=> sP2(sK11(sK7,sK6),sK6,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_10])])).

fof(f283,plain,
    ( ~ sP2(sK11(sK7,sK6),sK6,sK7)
    | ~ spl14_12 ),
    inference(resolution,[],[f273,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(sK12(X0,X1,X2))
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ! [X3] :
            ( ~ r1_waybel_7(X1,X3,X0)
            | ~ r2_hidden(X2,X3)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))
            | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X1)))
            | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X1)))
            | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X1))))
            | v1_xboole_0(X3) ) )
      & ( ( r1_waybel_7(X1,sK12(X0,X1,X2),X0)
          & r2_hidden(X2,sK12(X0,X1,X2))
          & m1_subset_1(sK12(X0,X1,X2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))
          & v13_waybel_0(sK12(X0,X1,X2),k3_yellow_1(k2_struct_0(X1)))
          & v2_waybel_0(sK12(X0,X1,X2),k3_yellow_1(k2_struct_0(X1)))
          & v1_subset_1(sK12(X0,X1,X2),u1_struct_0(k3_yellow_1(k2_struct_0(X1))))
          & ~ v1_xboole_0(sK12(X0,X1,X2)) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f40,f41])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r1_waybel_7(X1,X4,X0)
          & r2_hidden(X2,X4)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))
          & v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X1)))
          & v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X1)))
          & v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(X1))))
          & ~ v1_xboole_0(X4) )
     => ( r1_waybel_7(X1,sK12(X0,X1,X2),X0)
        & r2_hidden(X2,sK12(X0,X1,X2))
        & m1_subset_1(sK12(X0,X1,X2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))
        & v13_waybel_0(sK12(X0,X1,X2),k3_yellow_1(k2_struct_0(X1)))
        & v2_waybel_0(sK12(X0,X1,X2),k3_yellow_1(k2_struct_0(X1)))
        & v1_subset_1(sK12(X0,X1,X2),u1_struct_0(k3_yellow_1(k2_struct_0(X1))))
        & ~ v1_xboole_0(sK12(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ! [X3] :
            ( ~ r1_waybel_7(X1,X3,X0)
            | ~ r2_hidden(X2,X3)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))
            | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X1)))
            | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X1)))
            | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X1))))
            | v1_xboole_0(X3) ) )
      & ( ? [X4] :
            ( r1_waybel_7(X1,X4,X0)
            & r2_hidden(X2,X4)
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))
            & v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X1)))
            & v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X1)))
            & v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(X1))))
            & ~ v1_xboole_0(X4) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ( sP2(X2,X0,X1)
        | ! [X3] :
            ( ~ r1_waybel_7(X0,X3,X2)
            | ~ r2_hidden(X1,X3)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
            | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
            | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            | v1_xboole_0(X3) ) )
      & ( ? [X3] :
            ( r1_waybel_7(X0,X3,X2)
            & r2_hidden(X1,X3)
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
            & v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            & ~ v1_xboole_0(X3) )
        | ~ sP2(X2,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( sP2(X2,X0,X1)
    <=> ? [X3] :
          ( r1_waybel_7(X0,X3,X2)
          & r2_hidden(X1,X3)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X3) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f273,plain,
    ( v1_xboole_0(sK12(sK11(sK7,sK6),sK6,sK7))
    | ~ spl14_12 ),
    inference(avatar_component_clause,[],[f271])).

fof(f271,plain,
    ( spl14_12
  <=> v1_xboole_0(sK12(sK11(sK7,sK6),sK6,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_12])])).

fof(f282,plain,
    ( spl14_1
    | ~ spl14_10
    | ~ spl14_13 ),
    inference(avatar_contradiction_clause,[],[f281])).

fof(f281,plain,
    ( $false
    | spl14_1
    | ~ spl14_10
    | ~ spl14_13 ),
    inference(subsumption_resolution,[],[f280,f206])).

fof(f206,plain,
    ( ~ sP0(sK7,sK6)
    | spl14_1 ),
    inference(subsumption_resolution,[],[f118,f110])).

% (25051)ott+11_5:1_afp=100000:afq=1.1:br=off:gs=on:nm=64:nwc=1:sos=all:urr=on:updr=off_287 on theBenchmark
fof(f110,plain,
    ( ~ v4_pre_topc(sK7,sK6)
    | spl14_1 ),
    inference(avatar_component_clause,[],[f108])).

fof(f118,plain,
    ( ~ sP0(sK7,sK6)
    | v4_pre_topc(sK7,sK6) ),
    inference(resolution,[],[f116,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | ~ sP0(X1,X0)
      | v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f280,plain,
    ( sP0(sK7,sK6)
    | spl14_1
    | ~ spl14_10
    | ~ spl14_13 ),
    inference(resolution,[],[f279,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK11(X0,X1),X0)
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f279,plain,
    ( r2_hidden(sK11(sK7,sK6),sK7)
    | spl14_1
    | ~ spl14_10
    | ~ spl14_13 ),
    inference(subsumption_resolution,[],[f278,f211])).

fof(f211,plain,
    ( m1_subset_1(sK11(sK7,sK6),u1_struct_0(sK6))
    | spl14_1 ),
    inference(resolution,[],[f206,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | m1_subset_1(sK11(X0,X1),u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f278,plain,
    ( r2_hidden(sK11(sK7,sK6),sK7)
    | ~ m1_subset_1(sK11(sK7,sK6),u1_struct_0(sK6))
    | ~ spl14_10
    | ~ spl14_13 ),
    inference(resolution,[],[f276,f255])).

fof(f255,plain,
    ( r1_waybel_7(sK6,sK12(sK11(sK7,sK6),sK6,sK7),sK11(sK7,sK6))
    | ~ spl14_10 ),
    inference(resolution,[],[f244,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | r1_waybel_7(X1,sK12(X0,X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f276,plain,
    ( ! [X0] :
        ( ~ r1_waybel_7(sK6,sK12(sK11(sK7,sK6),sK6,sK7),X0)
        | r2_hidden(X0,sK7)
        | ~ m1_subset_1(X0,u1_struct_0(sK6)) )
    | ~ spl14_13 ),
    inference(avatar_component_clause,[],[f275])).

fof(f275,plain,
    ( spl14_13
  <=> ! [X0] :
        ( ~ r1_waybel_7(sK6,sK12(sK11(sK7,sK6),sK6,sK7),X0)
        | r2_hidden(X0,sK7)
        | ~ m1_subset_1(X0,u1_struct_0(sK6)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_13])])).

fof(f277,plain,
    ( spl14_12
    | spl14_13
    | spl14_1
    | ~ spl14_10 ),
    inference(avatar_split_clause,[],[f269,f242,f108,f275,f271])).

fof(f269,plain,
    ( ! [X0] :
        ( ~ r1_waybel_7(sK6,sK12(sK11(sK7,sK6),sK6,sK7),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK6))
        | r2_hidden(X0,sK7)
        | v1_xboole_0(sK12(sK11(sK7,sK6),sK6,sK7)) )
    | spl14_1
    | ~ spl14_10 ),
    inference(subsumption_resolution,[],[f268,f250])).

fof(f250,plain,
    ( v1_subset_1(sK12(sK11(sK7,sK6),sK6,sK7),u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))
    | ~ spl14_10 ),
    inference(resolution,[],[f244,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | v1_subset_1(sK12(X0,X1,X2),u1_struct_0(k3_yellow_1(k2_struct_0(X1)))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f268,plain,
    ( ! [X0] :
        ( ~ r1_waybel_7(sK6,sK12(sK11(sK7,sK6),sK6,sK7),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK6))
        | r2_hidden(X0,sK7)
        | ~ v1_subset_1(sK12(sK11(sK7,sK6),sK6,sK7),u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))
        | v1_xboole_0(sK12(sK11(sK7,sK6),sK6,sK7)) )
    | spl14_1
    | ~ spl14_10 ),
    inference(subsumption_resolution,[],[f267,f251])).

fof(f251,plain,
    ( v2_waybel_0(sK12(sK11(sK7,sK6),sK6,sK7),k3_yellow_1(k2_struct_0(sK6)))
    | ~ spl14_10 ),
    inference(resolution,[],[f244,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | v2_waybel_0(sK12(X0,X1,X2),k3_yellow_1(k2_struct_0(X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f267,plain,
    ( ! [X0] :
        ( ~ r1_waybel_7(sK6,sK12(sK11(sK7,sK6),sK6,sK7),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK6))
        | r2_hidden(X0,sK7)
        | ~ v2_waybel_0(sK12(sK11(sK7,sK6),sK6,sK7),k3_yellow_1(k2_struct_0(sK6)))
        | ~ v1_subset_1(sK12(sK11(sK7,sK6),sK6,sK7),u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))
        | v1_xboole_0(sK12(sK11(sK7,sK6),sK6,sK7)) )
    | spl14_1
    | ~ spl14_10 ),
    inference(subsumption_resolution,[],[f266,f253])).

fof(f253,plain,
    ( m1_subset_1(sK12(sK11(sK7,sK6),sK6,sK7),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
    | ~ spl14_10 ),
    inference(resolution,[],[f244,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | m1_subset_1(sK12(X0,X1,X2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f266,plain,
    ( ! [X0] :
        ( ~ r1_waybel_7(sK6,sK12(sK11(sK7,sK6),sK6,sK7),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK6))
        | ~ m1_subset_1(sK12(sK11(sK7,sK6),sK6,sK7),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
        | r2_hidden(X0,sK7)
        | ~ v2_waybel_0(sK12(sK11(sK7,sK6),sK6,sK7),k3_yellow_1(k2_struct_0(sK6)))
        | ~ v1_subset_1(sK12(sK11(sK7,sK6),sK6,sK7),u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))
        | v1_xboole_0(sK12(sK11(sK7,sK6),sK6,sK7)) )
    | spl14_1
    | ~ spl14_10 ),
    inference(subsumption_resolution,[],[f265,f254])).

fof(f254,plain,
    ( r2_hidden(sK7,sK12(sK11(sK7,sK6),sK6,sK7))
    | ~ spl14_10 ),
    inference(resolution,[],[f244,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | r2_hidden(X2,sK12(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f265,plain,
    ( ! [X0] :
        ( ~ r1_waybel_7(sK6,sK12(sK11(sK7,sK6),sK6,sK7),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK6))
        | ~ r2_hidden(sK7,sK12(sK11(sK7,sK6),sK6,sK7))
        | ~ m1_subset_1(sK12(sK11(sK7,sK6),sK6,sK7),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
        | r2_hidden(X0,sK7)
        | ~ v2_waybel_0(sK12(sK11(sK7,sK6),sK6,sK7),k3_yellow_1(k2_struct_0(sK6)))
        | ~ v1_subset_1(sK12(sK11(sK7,sK6),sK6,sK7),u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))
        | v1_xboole_0(sK12(sK11(sK7,sK6),sK6,sK7)) )
    | spl14_1
    | ~ spl14_10 ),
    inference(resolution,[],[f236,f252])).

fof(f252,plain,
    ( v13_waybel_0(sK12(sK11(sK7,sK6),sK6,sK7),k3_yellow_1(k2_struct_0(sK6)))
    | ~ spl14_10 ),
    inference(resolution,[],[f244,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | v13_waybel_0(sK12(X0,X1,X2),k3_yellow_1(k2_struct_0(X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f236,plain,
    ( ! [X4,X5] :
        ( ~ v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK6)))
        | ~ r1_waybel_7(sK6,X4,X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK6))
        | ~ r2_hidden(sK7,X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
        | r2_hidden(X5,sK7)
        | ~ v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK6)))
        | ~ v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))
        | v1_xboole_0(X4) )
    | spl14_1 ),
    inference(subsumption_resolution,[],[f53,f110])).

fof(f53,plain,(
    ! [X4,X5] :
      ( r2_hidden(X5,sK7)
      | ~ r1_waybel_7(sK6,X4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(sK6))
      | ~ r2_hidden(sK7,X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
      | ~ v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK6)))
      | ~ v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK6)))
      | ~ v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))
      | v1_xboole_0(X4)
      | v4_pre_topc(sK7,sK6) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f248,plain,
    ( spl14_1
    | spl14_9 ),
    inference(avatar_contradiction_clause,[],[f247])).

fof(f247,plain,
    ( $false
    | spl14_1
    | spl14_9 ),
    inference(subsumption_resolution,[],[f246,f211])).

fof(f246,plain,
    ( ~ m1_subset_1(sK11(sK7,sK6),u1_struct_0(sK6))
    | spl14_9 ),
    inference(resolution,[],[f240,f132])).

fof(f132,plain,(
    ! [X0] :
      ( sP3(sK7,sK6,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK6)) ) ),
    inference(resolution,[],[f104,f52])).

fof(f104,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK6)))
      | ~ m1_subset_1(X2,u1_struct_0(sK6))
      | sP3(X3,sK6,X2) ) ),
    inference(subsumption_resolution,[],[f103,f49])).

fof(f103,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK6))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK6)))
      | sP3(X3,sK6,X2)
      | v2_struct_0(sK6) ) ),
    inference(subsumption_resolution,[],[f99,f50])).

fof(f99,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK6))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK6)))
      | sP3(X3,sK6,X2)
      | ~ v2_pre_topc(sK6)
      | v2_struct_0(sK6) ) ),
    inference(resolution,[],[f51,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | sP3(X1,X0,X2)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP3(X1,X0,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f11,f18,f17])).

fof(f18,plain,(
    ! [X1,X0,X2] :
      ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
      <=> sP2(X2,X0,X1) )
      | ~ sP3(X1,X0,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ? [X3] :
                    ( r1_waybel_7(X0,X3,X2)
                    & r2_hidden(X1,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                    & ~ v1_xboole_0(X3) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ? [X3] :
                    ( r1_waybel_7(X0,X3,X2)
                    & r2_hidden(X1,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                    & ~ v1_xboole_0(X3) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ? [X3] :
                    ( r1_waybel_7(X0,X3,X2)
                    & r2_hidden(X1,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                    & ~ v1_xboole_0(X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_yellow19)).

fof(f240,plain,
    ( ~ sP3(sK7,sK6,sK11(sK7,sK6))
    | spl14_9 ),
    inference(avatar_component_clause,[],[f238])).

fof(f238,plain,
    ( spl14_9
  <=> sP3(sK7,sK6,sK11(sK7,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_9])])).

fof(f245,plain,
    ( ~ spl14_9
    | spl14_10
    | spl14_1
    | ~ spl14_4 ),
    inference(avatar_split_clause,[],[f235,f140,f108,f242,f238])).

fof(f140,plain,
    ( spl14_4
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X0,k10_yellow_6(X1,sK10(sK7,sK6)))
        | sP4(X1,X0,X2)
        | ~ v3_yellow_6(sK10(sK7,sK6),X1)
        | ~ l1_waybel_0(sK10(sK7,sK6),X1)
        | ~ r1_waybel_0(X1,sK10(sK7,sK6),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_4])])).

fof(f235,plain,
    ( sP2(sK11(sK7,sK6),sK6,sK7)
    | ~ sP3(sK7,sK6,sK11(sK7,sK6))
    | spl14_1
    | ~ spl14_4 ),
    inference(resolution,[],[f229,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k2_pre_topc(X1,X0))
      | sP2(X2,X1,X0)
      | ~ sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X2,k2_pre_topc(X1,X0))
          | ~ sP2(X2,X1,X0) )
        & ( sP2(X2,X1,X0)
          | ~ r2_hidden(X2,k2_pre_topc(X1,X0)) ) )
      | ~ sP3(X0,X1,X2) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X1,X0,X2] :
      ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
          | ~ sP2(X2,X0,X1) )
        & ( sP2(X2,X0,X1)
          | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
      | ~ sP3(X1,X0,X2) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f229,plain,
    ( r2_hidden(sK11(sK7,sK6),k2_pre_topc(sK6,sK7))
    | spl14_1
    | ~ spl14_4 ),
    inference(subsumption_resolution,[],[f222,f211])).

fof(f222,plain,
    ( ~ m1_subset_1(sK11(sK7,sK6),u1_struct_0(sK6))
    | r2_hidden(sK11(sK7,sK6),k2_pre_topc(sK6,sK7))
    | spl14_1
    | ~ spl14_4 ),
    inference(resolution,[],[f221,f131])).

fof(f131,plain,(
    ! [X0] :
      ( ~ sP4(sK6,X0,sK7)
      | ~ m1_subset_1(X0,u1_struct_0(sK6))
      | r2_hidden(X0,k2_pre_topc(sK6,sK7)) ) ),
    inference(resolution,[],[f130,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ sP5(X0,X1,X2)
      | ~ sP4(X2,X1,X0)
      | r2_hidden(X1,k2_pre_topc(X2,X0)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X1,k2_pre_topc(X2,X0))
          | ~ sP4(X2,X1,X0) )
        & ( sP4(X2,X1,X0)
          | ~ r2_hidden(X1,k2_pre_topc(X2,X0)) ) )
      | ~ sP5(X0,X1,X2) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X1,X2,X0] :
      ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
          | ~ sP4(X0,X2,X1) )
        & ( sP4(X0,X2,X1)
          | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
      | ~ sP5(X1,X2,X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X1,X2,X0] :
      ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
      <=> sP4(X0,X2,X1) )
      | ~ sP5(X1,X2,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).

fof(f130,plain,(
    ! [X0] :
      ( sP5(sK7,X0,sK6)
      | ~ m1_subset_1(X0,u1_struct_0(sK6)) ) ),
    inference(resolution,[],[f102,f52])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
      | ~ m1_subset_1(X0,u1_struct_0(sK6))
      | sP5(X1,X0,sK6) ) ),
    inference(subsumption_resolution,[],[f101,f49])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
      | sP5(X1,X0,sK6)
      | v2_struct_0(sK6) ) ),
    inference(subsumption_resolution,[],[f98,f50])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
      | sP5(X1,X0,sK6)
      | ~ v2_pre_topc(sK6)
      | v2_struct_0(sK6) ) ),
    inference(resolution,[],[f51,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | sP5(X1,X2,X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP5(X1,X2,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f13,f21,f20])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ? [X3] :
                    ( r2_hidden(X2,k10_yellow_6(X0,X3))
                    & r1_waybel_0(X0,X3,X1)
                    & l1_waybel_0(X3,X0)
                    & v3_yellow_6(X3,X0)
                    & v7_waybel_0(X3)
                    & v4_orders_2(X3)
                    & ~ v2_struct_0(X3) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ? [X3] :
                    ( r2_hidden(X2,k10_yellow_6(X0,X3))
                    & r1_waybel_0(X0,X3,X1)
                    & l1_waybel_0(X3,X0)
                    & v3_yellow_6(X3,X0)
                    & v7_waybel_0(X3)
                    & v4_orders_2(X3)
                    & ~ v2_struct_0(X3) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ? [X3] :
                    ( r2_hidden(X2,k10_yellow_6(X0,X3))
                    & r1_waybel_0(X0,X3,X1)
                    & l1_waybel_0(X3,X0)
                    & v3_yellow_6(X3,X0)
                    & v7_waybel_0(X3)
                    & v4_orders_2(X3)
                    & ~ v2_struct_0(X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_yellow19)).

fof(f221,plain,
    ( sP4(sK6,sK11(sK7,sK6),sK7)
    | spl14_1
    | ~ spl14_4 ),
    inference(resolution,[],[f220,f212])).

fof(f212,plain,
    ( r2_hidden(sK11(sK7,sK6),k10_yellow_6(sK6,sK10(sK7,sK6)))
    | spl14_1 ),
    inference(resolution,[],[f206,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | r2_hidden(sK11(X0,X1),k10_yellow_6(X1,sK10(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f220,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k10_yellow_6(sK6,sK10(sK7,sK6)))
        | sP4(sK6,X0,sK7) )
    | spl14_1
    | ~ spl14_4 ),
    inference(subsumption_resolution,[],[f219,f206])).

fof(f219,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k10_yellow_6(sK6,sK10(sK7,sK6)))
        | sP4(sK6,X0,sK7)
        | sP0(sK7,sK6) )
    | spl14_1
    | ~ spl14_4 ),
    inference(resolution,[],[f218,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_waybel_0(X1,sK10(X0,X1),X0)
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f218,plain,
    ( ! [X0,X1] :
        ( ~ r1_waybel_0(sK6,sK10(sK7,sK6),X1)
        | ~ r2_hidden(X0,k10_yellow_6(sK6,sK10(sK7,sK6)))
        | sP4(sK6,X0,X1) )
    | spl14_1
    | ~ spl14_4 ),
    inference(subsumption_resolution,[],[f217,f209])).

fof(f209,plain,
    ( v3_yellow_6(sK10(sK7,sK6),sK6)
    | spl14_1 ),
    inference(resolution,[],[f206,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | v3_yellow_6(sK10(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f217,plain,
    ( ! [X0,X1] :
        ( sP4(sK6,X0,X1)
        | ~ v3_yellow_6(sK10(sK7,sK6),sK6)
        | ~ r2_hidden(X0,k10_yellow_6(sK6,sK10(sK7,sK6)))
        | ~ r1_waybel_0(sK6,sK10(sK7,sK6),X1) )
    | spl14_1
    | ~ spl14_4 ),
    inference(resolution,[],[f141,f210])).

fof(f210,plain,
    ( l1_waybel_0(sK10(sK7,sK6),sK6)
    | spl14_1 ),
    inference(resolution,[],[f206,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | l1_waybel_0(sK10(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f141,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_waybel_0(sK10(sK7,sK6),X1)
        | sP4(X1,X0,X2)
        | ~ v3_yellow_6(sK10(sK7,sK6),X1)
        | ~ r2_hidden(X0,k10_yellow_6(X1,sK10(sK7,sK6)))
        | ~ r1_waybel_0(X1,sK10(sK7,sK6),X2) )
    | ~ spl14_4 ),
    inference(avatar_component_clause,[],[f140])).

fof(f205,plain,
    ( spl14_1
    | ~ spl14_3 ),
    inference(avatar_contradiction_clause,[],[f204])).

fof(f204,plain,
    ( $false
    | spl14_1
    | ~ spl14_3 ),
    inference(subsumption_resolution,[],[f203,f110])).

fof(f203,plain,
    ( v4_pre_topc(sK7,sK6)
    | ~ spl14_3 ),
    inference(subsumption_resolution,[],[f118,f202])).

fof(f202,plain,
    ( sP0(sK7,sK6)
    | ~ spl14_3 ),
    inference(resolution,[],[f138,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(sK10(X0,X1))
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f138,plain,
    ( v2_struct_0(sK10(sK7,sK6))
    | ~ spl14_3 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl14_3
  <=> v2_struct_0(sK10(sK7,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_3])])).

fof(f182,plain,
    ( ~ spl14_1
    | spl14_5 ),
    inference(avatar_contradiction_clause,[],[f181])).

fof(f181,plain,
    ( $false
    | ~ spl14_1
    | spl14_5 ),
    inference(subsumption_resolution,[],[f180,f146])).

fof(f146,plain,
    ( m1_subset_1(sK9,u1_struct_0(sK6))
    | ~ spl14_1 ),
    inference(subsumption_resolution,[],[f60,f109])).

fof(f180,plain,
    ( ~ m1_subset_1(sK9,u1_struct_0(sK6))
    | spl14_5 ),
    inference(resolution,[],[f174,f130])).

fof(f174,plain,
    ( ~ sP5(sK7,sK9,sK6)
    | spl14_5 ),
    inference(avatar_component_clause,[],[f172])).

fof(f172,plain,
    ( spl14_5
  <=> sP5(sK7,sK9,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_5])])).

fof(f179,plain,
    ( ~ spl14_5
    | spl14_6
    | ~ spl14_1
    | spl14_2 ),
    inference(avatar_split_clause,[],[f167,f112,f108,f176,f172])).

fof(f112,plain,
    ( spl14_2
  <=> v1_xboole_0(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_2])])).

fof(f167,plain,
    ( sP4(sK6,sK9,sK7)
    | ~ sP5(sK7,sK9,sK6)
    | ~ spl14_1
    | spl14_2 ),
    inference(resolution,[],[f166,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k2_pre_topc(X2,X0))
      | sP4(X2,X1,X0)
      | ~ sP5(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f166,plain,
    ( r2_hidden(sK9,k2_pre_topc(sK6,sK7))
    | ~ spl14_1
    | spl14_2 ),
    inference(subsumption_resolution,[],[f159,f146])).

fof(f159,plain,
    ( ~ m1_subset_1(sK9,u1_struct_0(sK6))
    | r2_hidden(sK9,k2_pre_topc(sK6,sK7))
    | ~ spl14_1
    | spl14_2 ),
    inference(resolution,[],[f158,f134])).

fof(f134,plain,(
    ! [X0] :
      ( ~ sP2(X0,sK6,sK7)
      | ~ m1_subset_1(X0,u1_struct_0(sK6))
      | r2_hidden(X0,k2_pre_topc(sK6,sK7)) ) ),
    inference(resolution,[],[f132,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ sP3(X0,X1,X2)
      | ~ sP2(X2,X1,X0)
      | r2_hidden(X2,k2_pre_topc(X1,X0)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f158,plain,
    ( sP2(sK9,sK6,sK7)
    | ~ spl14_1
    | spl14_2 ),
    inference(resolution,[],[f157,f143])).

fof(f143,plain,
    ( r2_hidden(sK7,sK8)
    | ~ spl14_1 ),
    inference(subsumption_resolution,[],[f59,f109])).

fof(f59,plain,
    ( r2_hidden(sK7,sK8)
    | ~ v4_pre_topc(sK7,sK6) ),
    inference(cnf_transformation,[],[f30])).

fof(f157,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK8)
        | sP2(sK9,sK6,X0) )
    | ~ spl14_1
    | spl14_2 ),
    inference(resolution,[],[f156,f147])).

% (25050)dis+1011_4_awrs=decay:awrsf=32:afp=40000:afq=1.0:amm=off:anc=all:bs=on:cond=on:fsr=off:gsp=input_only:lma=on:nm=16:nwc=1:nicw=on:sac=on:sp=frequency:thi=all:updr=off:uhcvi=on_670 on theBenchmark
fof(f147,plain,
    ( r1_waybel_7(sK6,sK8,sK9)
    | ~ spl14_1 ),
    inference(subsumption_resolution,[],[f61,f109])).

fof(f61,plain,
    ( r1_waybel_7(sK6,sK8,sK9)
    | ~ v4_pre_topc(sK7,sK6) ),
    inference(cnf_transformation,[],[f30])).

fof(f156,plain,
    ( ! [X0,X1] :
        ( ~ r1_waybel_7(sK6,sK8,X0)
        | ~ r2_hidden(X1,sK8)
        | sP2(X0,sK6,X1) )
    | ~ spl14_1
    | spl14_2 ),
    inference(subsumption_resolution,[],[f155,f153])).

fof(f153,plain,
    ( v1_subset_1(sK8,u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))
    | ~ spl14_1 ),
    inference(subsumption_resolution,[],[f55,f109])).

fof(f55,plain,
    ( v1_subset_1(sK8,u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))
    | ~ v4_pre_topc(sK7,sK6) ),
    inference(cnf_transformation,[],[f30])).

fof(f155,plain,
    ( ! [X0,X1] :
        ( ~ r1_waybel_7(sK6,sK8,X0)
        | ~ r2_hidden(X1,sK8)
        | sP2(X0,sK6,X1)
        | ~ v1_subset_1(sK8,u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))) )
    | ~ spl14_1
    | spl14_2 ),
    inference(subsumption_resolution,[],[f152,f154])).

fof(f154,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
    | ~ spl14_1 ),
    inference(subsumption_resolution,[],[f58,f109])).

fof(f58,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
    | ~ v4_pre_topc(sK7,sK6) ),
    inference(cnf_transformation,[],[f30])).

fof(f152,plain,
    ( ! [X0,X1] :
        ( ~ r1_waybel_7(sK6,sK8,X0)
        | ~ r2_hidden(X1,sK8)
        | ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
        | sP2(X0,sK6,X1)
        | ~ v1_subset_1(sK8,u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))) )
    | ~ spl14_1
    | spl14_2 ),
    inference(subsumption_resolution,[],[f151,f114])).

fof(f114,plain,
    ( ~ v1_xboole_0(sK8)
    | spl14_2 ),
    inference(avatar_component_clause,[],[f112])).

fof(f151,plain,
    ( ! [X0,X1] :
        ( ~ r1_waybel_7(sK6,sK8,X0)
        | ~ r2_hidden(X1,sK8)
        | ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
        | sP2(X0,sK6,X1)
        | ~ v1_subset_1(sK8,u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))
        | v1_xboole_0(sK8) )
    | ~ spl14_1 ),
    inference(subsumption_resolution,[],[f150,f148])).

fof(f148,plain,
    ( v2_waybel_0(sK8,k3_yellow_1(k2_struct_0(sK6)))
    | ~ spl14_1 ),
    inference(subsumption_resolution,[],[f56,f109])).

fof(f56,plain,
    ( v2_waybel_0(sK8,k3_yellow_1(k2_struct_0(sK6)))
    | ~ v4_pre_topc(sK7,sK6) ),
    inference(cnf_transformation,[],[f30])).

fof(f150,plain,
    ( ! [X0,X1] :
        ( ~ r1_waybel_7(sK6,sK8,X0)
        | ~ r2_hidden(X1,sK8)
        | ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
        | sP2(X0,sK6,X1)
        | ~ v2_waybel_0(sK8,k3_yellow_1(k2_struct_0(sK6)))
        | ~ v1_subset_1(sK8,u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))
        | v1_xboole_0(sK8) )
    | ~ spl14_1 ),
    inference(resolution,[],[f149,f85])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X1)))
      | ~ r1_waybel_7(X1,X3,X0)
      | ~ r2_hidden(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))
      | sP2(X0,X1,X2)
      | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X1)))
      | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X1))))
      | v1_xboole_0(X3) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f149,plain,
    ( v13_waybel_0(sK8,k3_yellow_1(k2_struct_0(sK6)))
    | ~ spl14_1 ),
    inference(subsumption_resolution,[],[f57,f109])).

fof(f57,plain,
    ( v13_waybel_0(sK8,k3_yellow_1(k2_struct_0(sK6)))
    | ~ v4_pre_topc(sK7,sK6) ),
    inference(cnf_transformation,[],[f30])).

fof(f142,plain,
    ( spl14_3
    | spl14_4
    | spl14_1 ),
    inference(avatar_split_clause,[],[f128,f108,f140,f136])).

fof(f128,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,k10_yellow_6(X1,sK10(sK7,sK6)))
        | ~ r1_waybel_0(X1,sK10(sK7,sK6),X2)
        | ~ l1_waybel_0(sK10(sK7,sK6),X1)
        | ~ v3_yellow_6(sK10(sK7,sK6),X1)
        | sP4(X1,X0,X2)
        | v2_struct_0(sK10(sK7,sK6)) )
    | spl14_1 ),
    inference(subsumption_resolution,[],[f126,f120])).

fof(f120,plain,
    ( v4_orders_2(sK10(sK7,sK6))
    | spl14_1 ),
    inference(resolution,[],[f119,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | v4_orders_2(sK10(X0,X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f119,plain,
    ( ~ sP0(sK7,sK6)
    | spl14_1 ),
    inference(subsumption_resolution,[],[f118,f110])).

fof(f126,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,k10_yellow_6(X1,sK10(sK7,sK6)))
        | ~ r1_waybel_0(X1,sK10(sK7,sK6),X2)
        | ~ l1_waybel_0(sK10(sK7,sK6),X1)
        | ~ v3_yellow_6(sK10(sK7,sK6),X1)
        | sP4(X1,X0,X2)
        | ~ v4_orders_2(sK10(sK7,sK6))
        | v2_struct_0(sK10(sK7,sK6)) )
    | spl14_1 ),
    inference(resolution,[],[f121,f96])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v7_waybel_0(X3)
      | ~ r2_hidden(X1,k10_yellow_6(X0,X3))
      | ~ r1_waybel_0(X0,X3,X2)
      | ~ l1_waybel_0(X3,X0)
      | ~ v3_yellow_6(X3,X0)
      | sP4(X0,X1,X2)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f121,plain,
    ( v7_waybel_0(sK10(sK7,sK6))
    | spl14_1 ),
    inference(resolution,[],[f119,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | v7_waybel_0(sK10(X0,X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f115,plain,
    ( ~ spl14_1
    | ~ spl14_2 ),
    inference(avatar_split_clause,[],[f54,f112,f108])).

fof(f54,plain,
    ( ~ v1_xboole_0(sK8)
    | ~ v4_pre_topc(sK7,sK6) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n020.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:49:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.43  % (25038)dis+1_3_add=large:afp=4000:afq=1.0:anc=none:gs=on:gsem=off:inw=on:lcm=reverse:lwlo=on:nm=64:nwc=1:sas=z3:sos=all:sac=on:thi=all:uwa=all:updr=off:uhcvi=on_12 on theBenchmark
% 0.22/0.43  % (25046)lrs+1011_2:1_add=large:afr=on:afp=4000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:gs=on:irw=on:nm=64:nwc=1:sas=z3:stl=30:sos=on:sp=reverse_arity:thf=on:urr=on:updr=off_81 on theBenchmark
% 0.22/0.44  % (25044)WARNING: option uwaf not known.
% 0.22/0.44  % (25047)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.22/0.44  % (25044)lrs+10_4:1_av=off:bd=off:bsr=on:cond=on:fde=unused:inw=on:lcm=reverse:lma=on:lwlo=on:nm=64:nwc=5:stl=90:sp=reverse_arity:thi=strong:uwa=ground:updr=off:uwaf=on_73 on theBenchmark
% 0.22/0.44  % (25035)dis+1002_8:1_awrs=converge:awrsf=256:anc=all_dependent:br=off:fsr=off:fde=none:gs=on:gsaa=from_current:gsem=on:irw=on:nm=64:nwc=1:sas=z3:s2a=on:sp=frequency:thf=on:uwa=interpreted_only:urr=on_7 on theBenchmark
% 0.22/0.45  % (25036)lrs+1_3_awrs=decay:awrsf=4:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fsr=off:fde=unused:gs=on:lwlo=on:nm=16:nwc=1:sas=z3:stl=30:ss=axioms:s2a=on:st=1.2:sos=theory:sp=frequency_3 on theBenchmark
% 0.22/0.45  % (25042)lrs+1003_2:3_afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=on:fde=unused:gs=on:inw=on:nm=0:newcnf=on:nwc=1:sas=z3:stl=30:sac=on:sp=occurrence:tha=off:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.45  % (25048)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.22/0.45  % (25048)Refutation not found, incomplete strategy% (25048)------------------------------
% 0.22/0.45  % (25048)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.45  % (25039)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.22/0.46  % (25043)dis+11_24_afp=40000:afq=1.1:amm=sco:anc=none:bs=on:gs=on:gsem=off:lcm=predicate:lma=on:nm=2:nwc=1:sos=on:sac=on:updr=off_91 on theBenchmark
% 0.22/0.46  % (25034)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
% 0.22/0.46  % (25045)dis+11_3_awrs=decay:awrsf=256:av=off:gs=on:gsem=on:lcm=reverse:nm=0:nwc=1:sos=all:sp=frequency:updr=off_4 on theBenchmark
% 0.22/0.47  % (25043)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % (25041)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.22/0.47  % (25048)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.47  
% 0.22/0.47  % (25048)Memory used [KB]: 5373
% 0.22/0.47  % (25048)Time elapsed: 0.066 s
% 0.22/0.47  % (25048)------------------------------
% 0.22/0.47  % (25048)------------------------------
% 0.22/0.48  % (25040)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.22/0.48  % (25052)lrs+1010_4:1_aac=none:add=off:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=on:gs=on:gsem=on:irw=on:nm=0:nwc=2.5:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.48  % (25037)lrs-11_4:1_afp=4000:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_3 on theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f376,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(avatar_sat_refutation,[],[f115,f142,f179,f182,f205,f245,f248,f277,f282,f285,f301,f375])).
% 0.22/0.48  fof(f375,plain,(
% 0.22/0.48    ~spl14_1 | ~spl14_6 | spl14_7),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f374])).
% 0.22/0.48  fof(f374,plain,(
% 0.22/0.48    $false | (~spl14_1 | ~spl14_6 | spl14_7)),
% 0.22/0.48    inference(subsumption_resolution,[],[f373,f302])).
% 0.22/0.48  fof(f302,plain,(
% 0.22/0.48    ~r2_hidden(sK9,sK7) | ~spl14_1),
% 0.22/0.48    inference(subsumption_resolution,[],[f62,f109])).
% 0.22/0.48  fof(f109,plain,(
% 0.22/0.48    v4_pre_topc(sK7,sK6) | ~spl14_1),
% 0.22/0.48    inference(avatar_component_clause,[],[f108])).
% 0.22/0.48  fof(f108,plain,(
% 0.22/0.48    spl14_1 <=> v4_pre_topc(sK7,sK6)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl14_1])])).
% 0.22/0.48  fof(f62,plain,(
% 0.22/0.48    ~r2_hidden(sK9,sK7) | ~v4_pre_topc(sK7,sK6)),
% 0.22/0.48    inference(cnf_transformation,[],[f30])).
% 0.22/0.48  fof(f30,plain,(
% 0.22/0.48    ((((~r2_hidden(sK9,sK7) & r1_waybel_7(sK6,sK8,sK9) & m1_subset_1(sK9,u1_struct_0(sK6))) & r2_hidden(sK7,sK8) & m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))) & v13_waybel_0(sK8,k3_yellow_1(k2_struct_0(sK6))) & v2_waybel_0(sK8,k3_yellow_1(k2_struct_0(sK6))) & v1_subset_1(sK8,u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))) & ~v1_xboole_0(sK8)) | ~v4_pre_topc(sK7,sK6)) & (! [X4] : (! [X5] : (r2_hidden(X5,sK7) | ~r1_waybel_7(sK6,X4,X5) | ~m1_subset_1(X5,u1_struct_0(sK6))) | ~r2_hidden(sK7,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))) | ~v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK6))) | ~v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK6))) | ~v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))) | v1_xboole_0(X4)) | v4_pre_topc(sK7,sK6)) & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))) & l1_pre_topc(sK6) & v2_pre_topc(sK6) & ~v2_struct_0(sK6)),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f25,f29,f28,f27,f26])).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : ((? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_waybel_7(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) & r2_hidden(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X2)) | ~v4_pre_topc(X1,X0)) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_waybel_7(X0,X4,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~r2_hidden(X1,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X4)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_waybel_7(sK6,X2,X3) & m1_subset_1(X3,u1_struct_0(sK6))) & r2_hidden(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(sK6))) & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(sK6))) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))) & ~v1_xboole_0(X2)) | ~v4_pre_topc(X1,sK6)) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_waybel_7(sK6,X4,X5) | ~m1_subset_1(X5,u1_struct_0(sK6))) | ~r2_hidden(X1,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))) | ~v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK6))) | ~v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK6))) | ~v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))) | v1_xboole_0(X4)) | v4_pre_topc(X1,sK6)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))) & l1_pre_topc(sK6) & v2_pre_topc(sK6) & ~v2_struct_0(sK6))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  % (25049)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    ? [X1] : ((? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_waybel_7(sK6,X2,X3) & m1_subset_1(X3,u1_struct_0(sK6))) & r2_hidden(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(sK6))) & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(sK6))) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))) & ~v1_xboole_0(X2)) | ~v4_pre_topc(X1,sK6)) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_waybel_7(sK6,X4,X5) | ~m1_subset_1(X5,u1_struct_0(sK6))) | ~r2_hidden(X1,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))) | ~v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK6))) | ~v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK6))) | ~v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))) | v1_xboole_0(X4)) | v4_pre_topc(X1,sK6)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))) => ((? [X2] : (? [X3] : (~r2_hidden(X3,sK7) & r1_waybel_7(sK6,X2,X3) & m1_subset_1(X3,u1_struct_0(sK6))) & r2_hidden(sK7,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(sK6))) & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(sK6))) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))) & ~v1_xboole_0(X2)) | ~v4_pre_topc(sK7,sK6)) & (! [X4] : (! [X5] : (r2_hidden(X5,sK7) | ~r1_waybel_7(sK6,X4,X5) | ~m1_subset_1(X5,u1_struct_0(sK6))) | ~r2_hidden(sK7,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))) | ~v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK6))) | ~v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK6))) | ~v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))) | v1_xboole_0(X4)) | v4_pre_topc(sK7,sK6)) & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    ? [X2] : (? [X3] : (~r2_hidden(X3,sK7) & r1_waybel_7(sK6,X2,X3) & m1_subset_1(X3,u1_struct_0(sK6))) & r2_hidden(sK7,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(sK6))) & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(sK6))) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))) & ~v1_xboole_0(X2)) => (? [X3] : (~r2_hidden(X3,sK7) & r1_waybel_7(sK6,sK8,X3) & m1_subset_1(X3,u1_struct_0(sK6))) & r2_hidden(sK7,sK8) & m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))) & v13_waybel_0(sK8,k3_yellow_1(k2_struct_0(sK6))) & v2_waybel_0(sK8,k3_yellow_1(k2_struct_0(sK6))) & v1_subset_1(sK8,u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))) & ~v1_xboole_0(sK8))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    ? [X3] : (~r2_hidden(X3,sK7) & r1_waybel_7(sK6,sK8,X3) & m1_subset_1(X3,u1_struct_0(sK6))) => (~r2_hidden(sK9,sK7) & r1_waybel_7(sK6,sK8,sK9) & m1_subset_1(sK9,u1_struct_0(sK6)))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : ((? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_waybel_7(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) & r2_hidden(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X2)) | ~v4_pre_topc(X1,X0)) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_waybel_7(X0,X4,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~r2_hidden(X1,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X4)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.48    inference(rectify,[],[f24])).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : ((? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_waybel_7(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) & r2_hidden(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X2)) | ~v4_pre_topc(X1,X0)) & (! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_waybel_7(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X2)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.48    inference(flattening,[],[f23])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : (((? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_waybel_7(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) & r2_hidden(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X2)) | ~v4_pre_topc(X1,X0)) & (! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_waybel_7(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X2)) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.48    inference(nnf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_waybel_7(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X2))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.48    inference(flattening,[],[f6])).
% 0.22/0.48  fof(f6,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> ! [X2] : ((! [X3] : ((r2_hidden(X3,X1) | ~r1_waybel_7(X0,X2,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_hidden(X1,X2)) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X2)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,negated_conjecture,(
% 0.22/0.48    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X2)) => (r2_hidden(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_waybel_7(X0,X2,X3) => r2_hidden(X3,X1))))))))),
% 0.22/0.48    inference(negated_conjecture,[],[f4])).
% 0.22/0.48  fof(f4,conjecture,(
% 0.22/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X2)) => (r2_hidden(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_waybel_7(X0,X2,X3) => r2_hidden(X3,X1))))))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_yellow19)).
% 0.22/0.48  fof(f373,plain,(
% 0.22/0.48    r2_hidden(sK9,sK7) | (~spl14_1 | ~spl14_6 | spl14_7)),
% 0.22/0.48    inference(subsumption_resolution,[],[f372,f304])).
% 0.22/0.48  fof(f304,plain,(
% 0.22/0.48    m1_subset_1(sK9,u1_struct_0(sK6)) | ~spl14_1),
% 0.22/0.48    inference(subsumption_resolution,[],[f60,f109])).
% 0.22/0.48  fof(f60,plain,(
% 0.22/0.48    m1_subset_1(sK9,u1_struct_0(sK6)) | ~v4_pre_topc(sK7,sK6)),
% 0.22/0.48    inference(cnf_transformation,[],[f30])).
% 0.22/0.48  fof(f372,plain,(
% 0.22/0.48    ~m1_subset_1(sK9,u1_struct_0(sK6)) | r2_hidden(sK9,sK7) | (~spl14_1 | ~spl14_6 | spl14_7)),
% 0.22/0.48    inference(resolution,[],[f371,f294])).
% 0.22/0.48  fof(f294,plain,(
% 0.22/0.48    r2_hidden(sK9,k10_yellow_6(sK6,sK13(sK6,sK9,sK7))) | ~spl14_6),
% 0.22/0.48    inference(resolution,[],[f178,f95])).
% 0.22/0.48  fof(f95,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~sP4(X0,X1,X2) | r2_hidden(X1,k10_yellow_6(X0,sK13(X0,X1,X2)))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f48])).
% 0.22/0.48  fof(f48,plain,(
% 0.22/0.48    ! [X0,X1,X2] : ((sP4(X0,X1,X2) | ! [X3] : (~r2_hidden(X1,k10_yellow_6(X0,X3)) | ~r1_waybel_0(X0,X3,X2) | ~l1_waybel_0(X3,X0) | ~v3_yellow_6(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3))) & ((r2_hidden(X1,k10_yellow_6(X0,sK13(X0,X1,X2))) & r1_waybel_0(X0,sK13(X0,X1,X2),X2) & l1_waybel_0(sK13(X0,X1,X2),X0) & v3_yellow_6(sK13(X0,X1,X2),X0) & v7_waybel_0(sK13(X0,X1,X2)) & v4_orders_2(sK13(X0,X1,X2)) & ~v2_struct_0(sK13(X0,X1,X2))) | ~sP4(X0,X1,X2)))),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13])],[f46,f47])).
% 0.22/0.48  fof(f47,plain,(
% 0.22/0.48    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X1,k10_yellow_6(X0,X4)) & r1_waybel_0(X0,X4,X2) & l1_waybel_0(X4,X0) & v3_yellow_6(X4,X0) & v7_waybel_0(X4) & v4_orders_2(X4) & ~v2_struct_0(X4)) => (r2_hidden(X1,k10_yellow_6(X0,sK13(X0,X1,X2))) & r1_waybel_0(X0,sK13(X0,X1,X2),X2) & l1_waybel_0(sK13(X0,X1,X2),X0) & v3_yellow_6(sK13(X0,X1,X2),X0) & v7_waybel_0(sK13(X0,X1,X2)) & v4_orders_2(sK13(X0,X1,X2)) & ~v2_struct_0(sK13(X0,X1,X2))))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f46,plain,(
% 0.22/0.48    ! [X0,X1,X2] : ((sP4(X0,X1,X2) | ! [X3] : (~r2_hidden(X1,k10_yellow_6(X0,X3)) | ~r1_waybel_0(X0,X3,X2) | ~l1_waybel_0(X3,X0) | ~v3_yellow_6(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3))) & (? [X4] : (r2_hidden(X1,k10_yellow_6(X0,X4)) & r1_waybel_0(X0,X4,X2) & l1_waybel_0(X4,X0) & v3_yellow_6(X4,X0) & v7_waybel_0(X4) & v4_orders_2(X4) & ~v2_struct_0(X4)) | ~sP4(X0,X1,X2)))),
% 0.22/0.48    inference(rectify,[],[f45])).
% 0.22/0.48  fof(f45,plain,(
% 0.22/0.48    ! [X0,X2,X1] : ((sP4(X0,X2,X1) | ! [X3] : (~r2_hidden(X2,k10_yellow_6(X0,X3)) | ~r1_waybel_0(X0,X3,X1) | ~l1_waybel_0(X3,X0) | ~v3_yellow_6(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3))) & (? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & r1_waybel_0(X0,X3,X1) & l1_waybel_0(X3,X0) & v3_yellow_6(X3,X0) & v7_waybel_0(X3) & v4_orders_2(X3) & ~v2_struct_0(X3)) | ~sP4(X0,X2,X1)))),
% 0.22/0.48    inference(nnf_transformation,[],[f20])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ! [X0,X2,X1] : (sP4(X0,X2,X1) <=> ? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & r1_waybel_0(X0,X3,X1) & l1_waybel_0(X3,X0) & v3_yellow_6(X3,X0) & v7_waybel_0(X3) & v4_orders_2(X3) & ~v2_struct_0(X3)))),
% 0.22/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 0.22/0.48  fof(f178,plain,(
% 0.22/0.48    sP4(sK6,sK9,sK7) | ~spl14_6),
% 0.22/0.48    inference(avatar_component_clause,[],[f176])).
% 0.22/0.48  fof(f176,plain,(
% 0.22/0.48    spl14_6 <=> sP4(sK6,sK9,sK7)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl14_6])])).
% 0.22/0.48  fof(f371,plain,(
% 0.22/0.48    ( ! [X0] : (~r2_hidden(X0,k10_yellow_6(sK6,sK13(sK6,sK9,sK7))) | ~m1_subset_1(X0,u1_struct_0(sK6)) | r2_hidden(X0,sK7)) ) | (~spl14_1 | ~spl14_6 | spl14_7)),
% 0.22/0.48    inference(subsumption_resolution,[],[f370,f303])).
% 0.22/0.48  fof(f303,plain,(
% 0.22/0.48    sP0(sK7,sK6) | ~spl14_1),
% 0.22/0.48    inference(subsumption_resolution,[],[f117,f109])).
% 0.22/0.48  % (25054)dis+1_14_awrs=converge:awrsf=256:av=off:bs=on:bsr=on:bce=on:cond=fast:gsp=input_only:gs=on:lcm=predicate:lma=on:nm=4:nwc=1.7:sp=weighted_frequency:urr=on_33 on theBenchmark
% 0.22/0.48  fof(f117,plain,(
% 0.22/0.48    ~v4_pre_topc(sK7,sK6) | sP0(sK7,sK6)),
% 0.22/0.48    inference(resolution,[],[f116,f63])).
% 0.22/0.48  fof(f63,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~sP1(X0,X1) | ~v4_pre_topc(X1,X0) | sP0(X1,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f31])).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    ! [X0,X1] : (((v4_pre_topc(X1,X0) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~v4_pre_topc(X1,X0))) | ~sP1(X0,X1))),
% 0.22/0.48    inference(nnf_transformation,[],[f15])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ! [X0,X1] : ((v4_pre_topc(X1,X0) <=> sP0(X1,X0)) | ~sP1(X0,X1))),
% 0.22/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.22/0.48  fof(f116,plain,(
% 0.22/0.48    sP1(sK6,sK7)),
% 0.22/0.48    inference(resolution,[],[f106,f52])).
% 0.22/0.48  fof(f52,plain,(
% 0.22/0.48    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))),
% 0.22/0.48    inference(cnf_transformation,[],[f30])).
% 0.22/0.48  fof(f106,plain,(
% 0.22/0.48    ( ! [X4] : (~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK6))) | sP1(sK6,X4)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f105,f49])).
% 0.22/0.48  fof(f49,plain,(
% 0.22/0.48    ~v2_struct_0(sK6)),
% 0.22/0.48    inference(cnf_transformation,[],[f30])).
% 0.22/0.48  fof(f105,plain,(
% 0.22/0.48    ( ! [X4] : (~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK6))) | sP1(sK6,X4) | v2_struct_0(sK6)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f100,f50])).
% 0.22/0.48  fof(f50,plain,(
% 0.22/0.48    v2_pre_topc(sK6)),
% 0.22/0.48    inference(cnf_transformation,[],[f30])).
% 0.22/0.48  fof(f100,plain,(
% 0.22/0.48    ( ! [X4] : (~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK6))) | sP1(sK6,X4) | ~v2_pre_topc(sK6) | v2_struct_0(sK6)) )),
% 0.22/0.48    inference(resolution,[],[f51,f75])).
% 0.22/0.48  fof(f75,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | sP1(X0,X1) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f16])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (sP1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.48    inference(definition_folding,[],[f9,f15,f14])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    ! [X1,X0] : (sP0(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,k10_yellow_6(X0,X2)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r1_waybel_0(X0,X2,X1) | ~l1_waybel_0(X2,X0) | ~v3_yellow_6(X2,X0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2)))),
% 0.22/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.48  fof(f9,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,k10_yellow_6(X0,X2)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r1_waybel_0(X0,X2,X1) | ~l1_waybel_0(X2,X0) | ~v3_yellow_6(X2,X0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.48    inference(flattening,[],[f8])).
% 0.22/0.48  fof(f8,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> ! [X2] : ((! [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,k10_yellow_6(X0,X2))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r1_waybel_0(X0,X2,X1)) | (~l1_waybel_0(X2,X0) | ~v3_yellow_6(X2,X0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> ! [X2] : ((l1_waybel_0(X2,X0) & v3_yellow_6(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) => (r1_waybel_0(X0,X2,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,k10_yellow_6(X0,X2)) => r2_hidden(X3,X1))))))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_yellow19)).
% 0.22/0.48  fof(f51,plain,(
% 0.22/0.48    l1_pre_topc(sK6)),
% 0.22/0.48    inference(cnf_transformation,[],[f30])).
% 0.22/0.48  fof(f370,plain,(
% 0.22/0.48    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK6)) | ~r2_hidden(X0,k10_yellow_6(sK6,sK13(sK6,sK9,sK7))) | r2_hidden(X0,sK7) | ~sP0(sK7,sK6)) ) | (~spl14_6 | spl14_7)),
% 0.22/0.48    inference(resolution,[],[f369,f293])).
% 0.22/0.48  fof(f293,plain,(
% 0.22/0.48    r1_waybel_0(sK6,sK13(sK6,sK9,sK7),sK7) | ~spl14_6),
% 0.22/0.48    inference(resolution,[],[f178,f94])).
% 0.22/0.48  fof(f94,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~sP4(X0,X1,X2) | r1_waybel_0(X0,sK13(X0,X1,X2),X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f48])).
% 0.22/0.48  fof(f369,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r1_waybel_0(sK6,sK13(sK6,sK9,sK7),X1) | ~m1_subset_1(X0,u1_struct_0(sK6)) | ~r2_hidden(X0,k10_yellow_6(sK6,sK13(sK6,sK9,sK7))) | r2_hidden(X0,X1) | ~sP0(X1,sK6)) ) | (~spl14_6 | spl14_7)),
% 0.22/0.48    inference(subsumption_resolution,[],[f368,f291])).
% 0.22/0.48  fof(f291,plain,(
% 0.22/0.48    v3_yellow_6(sK13(sK6,sK9,sK7),sK6) | ~spl14_6),
% 0.22/0.48    inference(resolution,[],[f178,f92])).
% 0.22/0.48  fof(f92,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~sP4(X0,X1,X2) | v3_yellow_6(sK13(X0,X1,X2),X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f48])).
% 0.22/0.48  fof(f368,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK6)) | ~r1_waybel_0(sK6,sK13(sK6,sK9,sK7),X1) | ~r2_hidden(X0,k10_yellow_6(sK6,sK13(sK6,sK9,sK7))) | ~v3_yellow_6(sK13(sK6,sK9,sK7),sK6) | r2_hidden(X0,X1) | ~sP0(X1,sK6)) ) | (~spl14_6 | spl14_7)),
% 0.22/0.48    inference(resolution,[],[f367,f292])).
% 0.22/0.48  fof(f292,plain,(
% 0.22/0.48    l1_waybel_0(sK13(sK6,sK9,sK7),sK6) | ~spl14_6),
% 0.22/0.48    inference(resolution,[],[f178,f93])).
% 0.22/0.48  fof(f93,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~sP4(X0,X1,X2) | l1_waybel_0(sK13(X0,X1,X2),X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f48])).
% 0.22/0.48  fof(f367,plain,(
% 0.22/0.48    ( ! [X4,X5,X3] : (~l1_waybel_0(sK13(sK6,sK9,sK7),X4) | ~m1_subset_1(X3,u1_struct_0(X4)) | ~r1_waybel_0(X4,sK13(sK6,sK9,sK7),X5) | ~r2_hidden(X3,k10_yellow_6(X4,sK13(sK6,sK9,sK7))) | ~v3_yellow_6(sK13(sK6,sK9,sK7),X4) | r2_hidden(X3,X5) | ~sP0(X5,X4)) ) | (~spl14_6 | spl14_7)),
% 0.22/0.48    inference(subsumption_resolution,[],[f298,f196])).
% 0.22/0.48  fof(f196,plain,(
% 0.22/0.48    ~v2_struct_0(sK13(sK6,sK9,sK7)) | spl14_7),
% 0.22/0.48    inference(avatar_component_clause,[],[f195])).
% 0.22/0.48  fof(f195,plain,(
% 0.22/0.48    spl14_7 <=> v2_struct_0(sK13(sK6,sK9,sK7))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl14_7])])).
% 0.22/0.48  fof(f298,plain,(
% 0.22/0.48    ( ! [X4,X5,X3] : (~r2_hidden(X3,k10_yellow_6(X4,sK13(sK6,sK9,sK7))) | ~m1_subset_1(X3,u1_struct_0(X4)) | ~r1_waybel_0(X4,sK13(sK6,sK9,sK7),X5) | ~l1_waybel_0(sK13(sK6,sK9,sK7),X4) | ~v3_yellow_6(sK13(sK6,sK9,sK7),X4) | r2_hidden(X3,X5) | v2_struct_0(sK13(sK6,sK9,sK7)) | ~sP0(X5,X4)) ) | ~spl14_6),
% 0.22/0.48    inference(subsumption_resolution,[],[f296,f289])).
% 0.22/0.48  fof(f289,plain,(
% 0.22/0.48    v4_orders_2(sK13(sK6,sK9,sK7)) | ~spl14_6),
% 0.22/0.48    inference(resolution,[],[f178,f90])).
% 0.22/0.48  fof(f90,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~sP4(X0,X1,X2) | v4_orders_2(sK13(X0,X1,X2))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f48])).
% 0.22/0.48  fof(f296,plain,(
% 0.22/0.48    ( ! [X4,X5,X3] : (~r2_hidden(X3,k10_yellow_6(X4,sK13(sK6,sK9,sK7))) | ~m1_subset_1(X3,u1_struct_0(X4)) | ~r1_waybel_0(X4,sK13(sK6,sK9,sK7),X5) | ~l1_waybel_0(sK13(sK6,sK9,sK7),X4) | ~v3_yellow_6(sK13(sK6,sK9,sK7),X4) | r2_hidden(X3,X5) | ~v4_orders_2(sK13(sK6,sK9,sK7)) | v2_struct_0(sK13(sK6,sK9,sK7)) | ~sP0(X5,X4)) ) | ~spl14_6),
% 0.22/0.48    inference(resolution,[],[f290,f65])).
% 0.22/0.48  fof(f65,plain,(
% 0.22/0.48    ( ! [X4,X0,X5,X1] : (~v7_waybel_0(X4) | ~r2_hidden(X5,k10_yellow_6(X1,X4)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~r1_waybel_0(X1,X4,X0) | ~l1_waybel_0(X4,X1) | ~v3_yellow_6(X4,X1) | r2_hidden(X5,X0) | ~v4_orders_2(X4) | v2_struct_0(X4) | ~sP0(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f36])).
% 0.22/0.48  fof(f36,plain,(
% 0.22/0.48    ! [X0,X1] : ((sP0(X0,X1) | ((~r2_hidden(sK11(X0,X1),X0) & r2_hidden(sK11(X0,X1),k10_yellow_6(X1,sK10(X0,X1))) & m1_subset_1(sK11(X0,X1),u1_struct_0(X1))) & r1_waybel_0(X1,sK10(X0,X1),X0) & l1_waybel_0(sK10(X0,X1),X1) & v3_yellow_6(sK10(X0,X1),X1) & v7_waybel_0(sK10(X0,X1)) & v4_orders_2(sK10(X0,X1)) & ~v2_struct_0(sK10(X0,X1)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X0) | ~r2_hidden(X5,k10_yellow_6(X1,X4)) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r1_waybel_0(X1,X4,X0) | ~l1_waybel_0(X4,X1) | ~v3_yellow_6(X4,X1) | ~v7_waybel_0(X4) | ~v4_orders_2(X4) | v2_struct_0(X4)) | ~sP0(X0,X1)))),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11])],[f33,f35,f34])).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    ! [X1,X0] : (? [X2] : (? [X3] : (~r2_hidden(X3,X0) & r2_hidden(X3,k10_yellow_6(X1,X2)) & m1_subset_1(X3,u1_struct_0(X1))) & r1_waybel_0(X1,X2,X0) & l1_waybel_0(X2,X1) & v3_yellow_6(X2,X1) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) => (? [X3] : (~r2_hidden(X3,X0) & r2_hidden(X3,k10_yellow_6(X1,sK10(X0,X1))) & m1_subset_1(X3,u1_struct_0(X1))) & r1_waybel_0(X1,sK10(X0,X1),X0) & l1_waybel_0(sK10(X0,X1),X1) & v3_yellow_6(sK10(X0,X1),X1) & v7_waybel_0(sK10(X0,X1)) & v4_orders_2(sK10(X0,X1)) & ~v2_struct_0(sK10(X0,X1))))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f35,plain,(
% 0.22/0.48    ! [X1,X0] : (? [X3] : (~r2_hidden(X3,X0) & r2_hidden(X3,k10_yellow_6(X1,sK10(X0,X1))) & m1_subset_1(X3,u1_struct_0(X1))) => (~r2_hidden(sK11(X0,X1),X0) & r2_hidden(sK11(X0,X1),k10_yellow_6(X1,sK10(X0,X1))) & m1_subset_1(sK11(X0,X1),u1_struct_0(X1))))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : (? [X3] : (~r2_hidden(X3,X0) & r2_hidden(X3,k10_yellow_6(X1,X2)) & m1_subset_1(X3,u1_struct_0(X1))) & r1_waybel_0(X1,X2,X0) & l1_waybel_0(X2,X1) & v3_yellow_6(X2,X1) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2))) & (! [X4] : (! [X5] : (r2_hidden(X5,X0) | ~r2_hidden(X5,k10_yellow_6(X1,X4)) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r1_waybel_0(X1,X4,X0) | ~l1_waybel_0(X4,X1) | ~v3_yellow_6(X4,X1) | ~v7_waybel_0(X4) | ~v4_orders_2(X4) | v2_struct_0(X4)) | ~sP0(X0,X1)))),
% 0.22/0.48    inference(rectify,[],[f32])).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    ! [X1,X0] : ((sP0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r2_hidden(X3,k10_yellow_6(X0,X2)) & m1_subset_1(X3,u1_struct_0(X0))) & r1_waybel_0(X0,X2,X1) & l1_waybel_0(X2,X0) & v3_yellow_6(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2))) & (! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,k10_yellow_6(X0,X2)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r1_waybel_0(X0,X2,X1) | ~l1_waybel_0(X2,X0) | ~v3_yellow_6(X2,X0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2)) | ~sP0(X1,X0)))),
% 0.22/0.48    inference(nnf_transformation,[],[f14])).
% 0.22/0.48  fof(f290,plain,(
% 0.22/0.48    v7_waybel_0(sK13(sK6,sK9,sK7)) | ~spl14_6),
% 0.22/0.48    inference(resolution,[],[f178,f91])).
% 0.22/0.48  fof(f91,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~sP4(X0,X1,X2) | v7_waybel_0(sK13(X0,X1,X2))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f48])).
% 0.22/0.48  fof(f301,plain,(
% 0.22/0.48    ~spl14_6 | ~spl14_7),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f300])).
% 0.22/0.48  fof(f300,plain,(
% 0.22/0.48    $false | (~spl14_6 | ~spl14_7)),
% 0.22/0.48    inference(subsumption_resolution,[],[f299,f178])).
% 0.22/0.48  fof(f299,plain,(
% 0.22/0.48    ~sP4(sK6,sK9,sK7) | ~spl14_7),
% 0.22/0.48    inference(resolution,[],[f197,f89])).
% 0.22/0.48  fof(f89,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~v2_struct_0(sK13(X0,X1,X2)) | ~sP4(X0,X1,X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f48])).
% 0.22/0.48  fof(f197,plain,(
% 0.22/0.48    v2_struct_0(sK13(sK6,sK9,sK7)) | ~spl14_7),
% 0.22/0.48    inference(avatar_component_clause,[],[f195])).
% 0.22/0.48  fof(f285,plain,(
% 0.22/0.48    ~spl14_10 | ~spl14_12),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f284])).
% 0.22/0.48  fof(f284,plain,(
% 0.22/0.48    $false | (~spl14_10 | ~spl14_12)),
% 0.22/0.48    inference(subsumption_resolution,[],[f283,f244])).
% 0.22/0.48  fof(f244,plain,(
% 0.22/0.48    sP2(sK11(sK7,sK6),sK6,sK7) | ~spl14_10),
% 0.22/0.48    inference(avatar_component_clause,[],[f242])).
% 0.22/0.48  fof(f242,plain,(
% 0.22/0.48    spl14_10 <=> sP2(sK11(sK7,sK6),sK6,sK7)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl14_10])])).
% 0.22/0.48  fof(f283,plain,(
% 0.22/0.48    ~sP2(sK11(sK7,sK6),sK6,sK7) | ~spl14_12),
% 0.22/0.48    inference(resolution,[],[f273,f78])).
% 0.22/0.48  fof(f78,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~v1_xboole_0(sK12(X0,X1,X2)) | ~sP2(X0,X1,X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f42])).
% 0.22/0.48  fof(f42,plain,(
% 0.22/0.48    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ! [X3] : (~r1_waybel_7(X1,X3,X0) | ~r2_hidden(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))) | ~v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X1))) | ~v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X1))) | ~v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X1)))) | v1_xboole_0(X3))) & ((r1_waybel_7(X1,sK12(X0,X1,X2),X0) & r2_hidden(X2,sK12(X0,X1,X2)) & m1_subset_1(sK12(X0,X1,X2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))) & v13_waybel_0(sK12(X0,X1,X2),k3_yellow_1(k2_struct_0(X1))) & v2_waybel_0(sK12(X0,X1,X2),k3_yellow_1(k2_struct_0(X1))) & v1_subset_1(sK12(X0,X1,X2),u1_struct_0(k3_yellow_1(k2_struct_0(X1)))) & ~v1_xboole_0(sK12(X0,X1,X2))) | ~sP2(X0,X1,X2)))),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f40,f41])).
% 0.22/0.48  fof(f41,plain,(
% 0.22/0.48    ! [X2,X1,X0] : (? [X4] : (r1_waybel_7(X1,X4,X0) & r2_hidden(X2,X4) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))) & v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X1))) & v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X1))) & v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(X1)))) & ~v1_xboole_0(X4)) => (r1_waybel_7(X1,sK12(X0,X1,X2),X0) & r2_hidden(X2,sK12(X0,X1,X2)) & m1_subset_1(sK12(X0,X1,X2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))) & v13_waybel_0(sK12(X0,X1,X2),k3_yellow_1(k2_struct_0(X1))) & v2_waybel_0(sK12(X0,X1,X2),k3_yellow_1(k2_struct_0(X1))) & v1_subset_1(sK12(X0,X1,X2),u1_struct_0(k3_yellow_1(k2_struct_0(X1)))) & ~v1_xboole_0(sK12(X0,X1,X2))))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f40,plain,(
% 0.22/0.48    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ! [X3] : (~r1_waybel_7(X1,X3,X0) | ~r2_hidden(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))) | ~v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X1))) | ~v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X1))) | ~v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X1)))) | v1_xboole_0(X3))) & (? [X4] : (r1_waybel_7(X1,X4,X0) & r2_hidden(X2,X4) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))) & v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X1))) & v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X1))) & v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(X1)))) & ~v1_xboole_0(X4)) | ~sP2(X0,X1,X2)))),
% 0.22/0.48    inference(rectify,[],[f39])).
% 0.22/0.48  fof(f39,plain,(
% 0.22/0.48    ! [X2,X0,X1] : ((sP2(X2,X0,X1) | ! [X3] : (~r1_waybel_7(X0,X3,X2) | ~r2_hidden(X1,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X3))) & (? [X3] : (r1_waybel_7(X0,X3,X2) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X3)) | ~sP2(X2,X0,X1)))),
% 0.22/0.48    inference(nnf_transformation,[],[f17])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ! [X2,X0,X1] : (sP2(X2,X0,X1) <=> ? [X3] : (r1_waybel_7(X0,X3,X2) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X3)))),
% 0.22/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.22/0.48  fof(f273,plain,(
% 0.22/0.48    v1_xboole_0(sK12(sK11(sK7,sK6),sK6,sK7)) | ~spl14_12),
% 0.22/0.48    inference(avatar_component_clause,[],[f271])).
% 0.22/0.48  fof(f271,plain,(
% 0.22/0.48    spl14_12 <=> v1_xboole_0(sK12(sK11(sK7,sK6),sK6,sK7))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl14_12])])).
% 0.22/0.48  fof(f282,plain,(
% 0.22/0.48    spl14_1 | ~spl14_10 | ~spl14_13),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f281])).
% 0.22/0.48  fof(f281,plain,(
% 0.22/0.48    $false | (spl14_1 | ~spl14_10 | ~spl14_13)),
% 0.22/0.48    inference(subsumption_resolution,[],[f280,f206])).
% 0.22/0.48  fof(f206,plain,(
% 0.22/0.48    ~sP0(sK7,sK6) | spl14_1),
% 0.22/0.48    inference(subsumption_resolution,[],[f118,f110])).
% 0.22/0.48  % (25051)ott+11_5:1_afp=100000:afq=1.1:br=off:gs=on:nm=64:nwc=1:sos=all:urr=on:updr=off_287 on theBenchmark
% 0.22/0.48  fof(f110,plain,(
% 0.22/0.48    ~v4_pre_topc(sK7,sK6) | spl14_1),
% 0.22/0.48    inference(avatar_component_clause,[],[f108])).
% 0.22/0.48  fof(f118,plain,(
% 0.22/0.48    ~sP0(sK7,sK6) | v4_pre_topc(sK7,sK6)),
% 0.22/0.48    inference(resolution,[],[f116,f64])).
% 0.22/0.48  fof(f64,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~sP1(X0,X1) | ~sP0(X1,X0) | v4_pre_topc(X1,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f31])).
% 0.22/0.48  fof(f280,plain,(
% 0.22/0.48    sP0(sK7,sK6) | (spl14_1 | ~spl14_10 | ~spl14_13)),
% 0.22/0.48    inference(resolution,[],[f279,f74])).
% 0.22/0.48  fof(f74,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r2_hidden(sK11(X0,X1),X0) | sP0(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f36])).
% 0.22/0.48  fof(f279,plain,(
% 0.22/0.48    r2_hidden(sK11(sK7,sK6),sK7) | (spl14_1 | ~spl14_10 | ~spl14_13)),
% 0.22/0.48    inference(subsumption_resolution,[],[f278,f211])).
% 0.22/0.48  fof(f211,plain,(
% 0.22/0.48    m1_subset_1(sK11(sK7,sK6),u1_struct_0(sK6)) | spl14_1),
% 0.22/0.48    inference(resolution,[],[f206,f72])).
% 0.22/0.48  fof(f72,plain,(
% 0.22/0.48    ( ! [X0,X1] : (sP0(X0,X1) | m1_subset_1(sK11(X0,X1),u1_struct_0(X1))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f36])).
% 0.22/0.48  fof(f278,plain,(
% 0.22/0.48    r2_hidden(sK11(sK7,sK6),sK7) | ~m1_subset_1(sK11(sK7,sK6),u1_struct_0(sK6)) | (~spl14_10 | ~spl14_13)),
% 0.22/0.48    inference(resolution,[],[f276,f255])).
% 0.22/0.48  fof(f255,plain,(
% 0.22/0.48    r1_waybel_7(sK6,sK12(sK11(sK7,sK6),sK6,sK7),sK11(sK7,sK6)) | ~spl14_10),
% 0.22/0.48    inference(resolution,[],[f244,f84])).
% 0.22/0.48  fof(f84,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~sP2(X0,X1,X2) | r1_waybel_7(X1,sK12(X0,X1,X2),X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f42])).
% 0.22/0.48  fof(f276,plain,(
% 0.22/0.48    ( ! [X0] : (~r1_waybel_7(sK6,sK12(sK11(sK7,sK6),sK6,sK7),X0) | r2_hidden(X0,sK7) | ~m1_subset_1(X0,u1_struct_0(sK6))) ) | ~spl14_13),
% 0.22/0.48    inference(avatar_component_clause,[],[f275])).
% 0.22/0.48  fof(f275,plain,(
% 0.22/0.48    spl14_13 <=> ! [X0] : (~r1_waybel_7(sK6,sK12(sK11(sK7,sK6),sK6,sK7),X0) | r2_hidden(X0,sK7) | ~m1_subset_1(X0,u1_struct_0(sK6)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl14_13])])).
% 0.22/0.48  fof(f277,plain,(
% 0.22/0.48    spl14_12 | spl14_13 | spl14_1 | ~spl14_10),
% 0.22/0.48    inference(avatar_split_clause,[],[f269,f242,f108,f275,f271])).
% 0.22/0.48  fof(f269,plain,(
% 0.22/0.48    ( ! [X0] : (~r1_waybel_7(sK6,sK12(sK11(sK7,sK6),sK6,sK7),X0) | ~m1_subset_1(X0,u1_struct_0(sK6)) | r2_hidden(X0,sK7) | v1_xboole_0(sK12(sK11(sK7,sK6),sK6,sK7))) ) | (spl14_1 | ~spl14_10)),
% 0.22/0.48    inference(subsumption_resolution,[],[f268,f250])).
% 0.22/0.48  fof(f250,plain,(
% 0.22/0.48    v1_subset_1(sK12(sK11(sK7,sK6),sK6,sK7),u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))) | ~spl14_10),
% 0.22/0.48    inference(resolution,[],[f244,f79])).
% 0.22/0.48  fof(f79,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~sP2(X0,X1,X2) | v1_subset_1(sK12(X0,X1,X2),u1_struct_0(k3_yellow_1(k2_struct_0(X1))))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f42])).
% 0.22/0.48  fof(f268,plain,(
% 0.22/0.48    ( ! [X0] : (~r1_waybel_7(sK6,sK12(sK11(sK7,sK6),sK6,sK7),X0) | ~m1_subset_1(X0,u1_struct_0(sK6)) | r2_hidden(X0,sK7) | ~v1_subset_1(sK12(sK11(sK7,sK6),sK6,sK7),u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))) | v1_xboole_0(sK12(sK11(sK7,sK6),sK6,sK7))) ) | (spl14_1 | ~spl14_10)),
% 0.22/0.48    inference(subsumption_resolution,[],[f267,f251])).
% 0.22/0.48  fof(f251,plain,(
% 0.22/0.48    v2_waybel_0(sK12(sK11(sK7,sK6),sK6,sK7),k3_yellow_1(k2_struct_0(sK6))) | ~spl14_10),
% 0.22/0.48    inference(resolution,[],[f244,f80])).
% 0.22/0.48  fof(f80,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~sP2(X0,X1,X2) | v2_waybel_0(sK12(X0,X1,X2),k3_yellow_1(k2_struct_0(X1)))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f42])).
% 0.22/0.48  fof(f267,plain,(
% 0.22/0.48    ( ! [X0] : (~r1_waybel_7(sK6,sK12(sK11(sK7,sK6),sK6,sK7),X0) | ~m1_subset_1(X0,u1_struct_0(sK6)) | r2_hidden(X0,sK7) | ~v2_waybel_0(sK12(sK11(sK7,sK6),sK6,sK7),k3_yellow_1(k2_struct_0(sK6))) | ~v1_subset_1(sK12(sK11(sK7,sK6),sK6,sK7),u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))) | v1_xboole_0(sK12(sK11(sK7,sK6),sK6,sK7))) ) | (spl14_1 | ~spl14_10)),
% 0.22/0.48    inference(subsumption_resolution,[],[f266,f253])).
% 0.22/0.48  fof(f253,plain,(
% 0.22/0.48    m1_subset_1(sK12(sK11(sK7,sK6),sK6,sK7),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))) | ~spl14_10),
% 0.22/0.48    inference(resolution,[],[f244,f82])).
% 0.22/0.48  fof(f82,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~sP2(X0,X1,X2) | m1_subset_1(sK12(X0,X1,X2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f42])).
% 0.22/0.48  fof(f266,plain,(
% 0.22/0.48    ( ! [X0] : (~r1_waybel_7(sK6,sK12(sK11(sK7,sK6),sK6,sK7),X0) | ~m1_subset_1(X0,u1_struct_0(sK6)) | ~m1_subset_1(sK12(sK11(sK7,sK6),sK6,sK7),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))) | r2_hidden(X0,sK7) | ~v2_waybel_0(sK12(sK11(sK7,sK6),sK6,sK7),k3_yellow_1(k2_struct_0(sK6))) | ~v1_subset_1(sK12(sK11(sK7,sK6),sK6,sK7),u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))) | v1_xboole_0(sK12(sK11(sK7,sK6),sK6,sK7))) ) | (spl14_1 | ~spl14_10)),
% 0.22/0.48    inference(subsumption_resolution,[],[f265,f254])).
% 0.22/0.48  fof(f254,plain,(
% 0.22/0.48    r2_hidden(sK7,sK12(sK11(sK7,sK6),sK6,sK7)) | ~spl14_10),
% 0.22/0.48    inference(resolution,[],[f244,f83])).
% 0.22/0.48  fof(f83,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~sP2(X0,X1,X2) | r2_hidden(X2,sK12(X0,X1,X2))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f42])).
% 0.22/0.48  fof(f265,plain,(
% 0.22/0.48    ( ! [X0] : (~r1_waybel_7(sK6,sK12(sK11(sK7,sK6),sK6,sK7),X0) | ~m1_subset_1(X0,u1_struct_0(sK6)) | ~r2_hidden(sK7,sK12(sK11(sK7,sK6),sK6,sK7)) | ~m1_subset_1(sK12(sK11(sK7,sK6),sK6,sK7),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))) | r2_hidden(X0,sK7) | ~v2_waybel_0(sK12(sK11(sK7,sK6),sK6,sK7),k3_yellow_1(k2_struct_0(sK6))) | ~v1_subset_1(sK12(sK11(sK7,sK6),sK6,sK7),u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))) | v1_xboole_0(sK12(sK11(sK7,sK6),sK6,sK7))) ) | (spl14_1 | ~spl14_10)),
% 0.22/0.48    inference(resolution,[],[f236,f252])).
% 0.22/0.48  fof(f252,plain,(
% 0.22/0.48    v13_waybel_0(sK12(sK11(sK7,sK6),sK6,sK7),k3_yellow_1(k2_struct_0(sK6))) | ~spl14_10),
% 0.22/0.48    inference(resolution,[],[f244,f81])).
% 0.22/0.48  fof(f81,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~sP2(X0,X1,X2) | v13_waybel_0(sK12(X0,X1,X2),k3_yellow_1(k2_struct_0(X1)))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f42])).
% 0.22/0.48  fof(f236,plain,(
% 0.22/0.48    ( ! [X4,X5] : (~v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK6))) | ~r1_waybel_7(sK6,X4,X5) | ~m1_subset_1(X5,u1_struct_0(sK6)) | ~r2_hidden(sK7,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))) | r2_hidden(X5,sK7) | ~v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK6))) | ~v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))) | v1_xboole_0(X4)) ) | spl14_1),
% 0.22/0.48    inference(subsumption_resolution,[],[f53,f110])).
% 0.22/0.48  fof(f53,plain,(
% 0.22/0.48    ( ! [X4,X5] : (r2_hidden(X5,sK7) | ~r1_waybel_7(sK6,X4,X5) | ~m1_subset_1(X5,u1_struct_0(sK6)) | ~r2_hidden(sK7,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))) | ~v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK6))) | ~v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK6))) | ~v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))) | v1_xboole_0(X4) | v4_pre_topc(sK7,sK6)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f30])).
% 0.22/0.48  fof(f248,plain,(
% 0.22/0.48    spl14_1 | spl14_9),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f247])).
% 0.22/0.48  fof(f247,plain,(
% 0.22/0.48    $false | (spl14_1 | spl14_9)),
% 0.22/0.48    inference(subsumption_resolution,[],[f246,f211])).
% 0.22/0.48  fof(f246,plain,(
% 0.22/0.48    ~m1_subset_1(sK11(sK7,sK6),u1_struct_0(sK6)) | spl14_9),
% 0.22/0.48    inference(resolution,[],[f240,f132])).
% 0.22/0.48  fof(f132,plain,(
% 0.22/0.48    ( ! [X0] : (sP3(sK7,sK6,X0) | ~m1_subset_1(X0,u1_struct_0(sK6))) )),
% 0.22/0.48    inference(resolution,[],[f104,f52])).
% 0.22/0.48  fof(f104,plain,(
% 0.22/0.48    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK6))) | ~m1_subset_1(X2,u1_struct_0(sK6)) | sP3(X3,sK6,X2)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f103,f49])).
% 0.22/0.48  fof(f103,plain,(
% 0.22/0.48    ( ! [X2,X3] : (~m1_subset_1(X2,u1_struct_0(sK6)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK6))) | sP3(X3,sK6,X2) | v2_struct_0(sK6)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f99,f50])).
% 0.22/0.48  fof(f99,plain,(
% 0.22/0.48    ( ! [X2,X3] : (~m1_subset_1(X2,u1_struct_0(sK6)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK6))) | sP3(X3,sK6,X2) | ~v2_pre_topc(sK6) | v2_struct_0(sK6)) )),
% 0.22/0.48    inference(resolution,[],[f51,f86])).
% 0.22/0.48  fof(f86,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | sP3(X1,X0,X2) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f19])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : (sP3(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.48    inference(definition_folding,[],[f11,f18,f17])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ! [X1,X0,X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <=> sP2(X2,X0,X1)) | ~sP3(X1,X0,X2))),
% 0.22/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.22/0.48  fof(f11,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <=> ? [X3] : (r1_waybel_7(X0,X3,X2) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X3))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.48    inference(flattening,[],[f10])).
% 0.22/0.48  fof(f10,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <=> ? [X3] : (r1_waybel_7(X0,X3,X2) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X3))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k2_pre_topc(X0,X1)) <=> ? [X3] : (r1_waybel_7(X0,X3,X2) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X3))))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_yellow19)).
% 0.22/0.48  fof(f240,plain,(
% 0.22/0.48    ~sP3(sK7,sK6,sK11(sK7,sK6)) | spl14_9),
% 0.22/0.48    inference(avatar_component_clause,[],[f238])).
% 0.22/0.48  fof(f238,plain,(
% 0.22/0.48    spl14_9 <=> sP3(sK7,sK6,sK11(sK7,sK6))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl14_9])])).
% 0.22/0.48  fof(f245,plain,(
% 0.22/0.48    ~spl14_9 | spl14_10 | spl14_1 | ~spl14_4),
% 0.22/0.48    inference(avatar_split_clause,[],[f235,f140,f108,f242,f238])).
% 0.22/0.48  fof(f140,plain,(
% 0.22/0.48    spl14_4 <=> ! [X1,X0,X2] : (~r2_hidden(X0,k10_yellow_6(X1,sK10(sK7,sK6))) | sP4(X1,X0,X2) | ~v3_yellow_6(sK10(sK7,sK6),X1) | ~l1_waybel_0(sK10(sK7,sK6),X1) | ~r1_waybel_0(X1,sK10(sK7,sK6),X2))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl14_4])])).
% 0.22/0.48  fof(f235,plain,(
% 0.22/0.48    sP2(sK11(sK7,sK6),sK6,sK7) | ~sP3(sK7,sK6,sK11(sK7,sK6)) | (spl14_1 | ~spl14_4)),
% 0.22/0.48    inference(resolution,[],[f229,f76])).
% 0.22/0.48  fof(f76,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~r2_hidden(X2,k2_pre_topc(X1,X0)) | sP2(X2,X1,X0) | ~sP3(X0,X1,X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f38])).
% 0.22/0.48  fof(f38,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (((r2_hidden(X2,k2_pre_topc(X1,X0)) | ~sP2(X2,X1,X0)) & (sP2(X2,X1,X0) | ~r2_hidden(X2,k2_pre_topc(X1,X0)))) | ~sP3(X0,X1,X2))),
% 0.22/0.48    inference(rectify,[],[f37])).
% 0.22/0.48  fof(f37,plain,(
% 0.22/0.48    ! [X1,X0,X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | ~sP2(X2,X0,X1)) & (sP2(X2,X0,X1) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~sP3(X1,X0,X2))),
% 0.22/0.48    inference(nnf_transformation,[],[f18])).
% 0.22/0.48  fof(f229,plain,(
% 0.22/0.48    r2_hidden(sK11(sK7,sK6),k2_pre_topc(sK6,sK7)) | (spl14_1 | ~spl14_4)),
% 0.22/0.48    inference(subsumption_resolution,[],[f222,f211])).
% 0.22/0.48  fof(f222,plain,(
% 0.22/0.48    ~m1_subset_1(sK11(sK7,sK6),u1_struct_0(sK6)) | r2_hidden(sK11(sK7,sK6),k2_pre_topc(sK6,sK7)) | (spl14_1 | ~spl14_4)),
% 0.22/0.48    inference(resolution,[],[f221,f131])).
% 0.22/0.48  fof(f131,plain,(
% 0.22/0.48    ( ! [X0] : (~sP4(sK6,X0,sK7) | ~m1_subset_1(X0,u1_struct_0(sK6)) | r2_hidden(X0,k2_pre_topc(sK6,sK7))) )),
% 0.22/0.48    inference(resolution,[],[f130,f88])).
% 0.22/0.48  fof(f88,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~sP5(X0,X1,X2) | ~sP4(X2,X1,X0) | r2_hidden(X1,k2_pre_topc(X2,X0))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f44])).
% 0.22/0.48  fof(f44,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (((r2_hidden(X1,k2_pre_topc(X2,X0)) | ~sP4(X2,X1,X0)) & (sP4(X2,X1,X0) | ~r2_hidden(X1,k2_pre_topc(X2,X0)))) | ~sP5(X0,X1,X2))),
% 0.22/0.48    inference(rectify,[],[f43])).
% 0.22/0.48  fof(f43,plain,(
% 0.22/0.48    ! [X1,X2,X0] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | ~sP4(X0,X2,X1)) & (sP4(X0,X2,X1) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~sP5(X1,X2,X0))),
% 0.22/0.48    inference(nnf_transformation,[],[f21])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ! [X1,X2,X0] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <=> sP4(X0,X2,X1)) | ~sP5(X1,X2,X0))),
% 0.22/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).
% 0.22/0.48  fof(f130,plain,(
% 0.22/0.48    ( ! [X0] : (sP5(sK7,X0,sK6) | ~m1_subset_1(X0,u1_struct_0(sK6))) )),
% 0.22/0.48    inference(resolution,[],[f102,f52])).
% 0.22/0.48  fof(f102,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) | ~m1_subset_1(X0,u1_struct_0(sK6)) | sP5(X1,X0,sK6)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f101,f49])).
% 0.22/0.48  fof(f101,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK6)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) | sP5(X1,X0,sK6) | v2_struct_0(sK6)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f98,f50])).
% 0.22/0.48  fof(f98,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK6)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) | sP5(X1,X0,sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6)) )),
% 0.22/0.48    inference(resolution,[],[f51,f97])).
% 0.22/0.48  fof(f97,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | sP5(X1,X2,X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f22])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : (sP5(X1,X2,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.48    inference(definition_folding,[],[f13,f21,f20])).
% 0.22/0.48  fof(f13,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <=> ? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & r1_waybel_0(X0,X3,X1) & l1_waybel_0(X3,X0) & v3_yellow_6(X3,X0) & v7_waybel_0(X3) & v4_orders_2(X3) & ~v2_struct_0(X3))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.48    inference(flattening,[],[f12])).
% 0.22/0.48  fof(f12,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <=> ? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & r1_waybel_0(X0,X3,X1) & l1_waybel_0(X3,X0) & v3_yellow_6(X3,X0) & v7_waybel_0(X3) & v4_orders_2(X3) & ~v2_struct_0(X3))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k2_pre_topc(X0,X1)) <=> ? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & r1_waybel_0(X0,X3,X1) & l1_waybel_0(X3,X0) & v3_yellow_6(X3,X0) & v7_waybel_0(X3) & v4_orders_2(X3) & ~v2_struct_0(X3))))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_yellow19)).
% 0.22/0.48  fof(f221,plain,(
% 0.22/0.48    sP4(sK6,sK11(sK7,sK6),sK7) | (spl14_1 | ~spl14_4)),
% 0.22/0.48    inference(resolution,[],[f220,f212])).
% 0.22/0.48  fof(f212,plain,(
% 0.22/0.48    r2_hidden(sK11(sK7,sK6),k10_yellow_6(sK6,sK10(sK7,sK6))) | spl14_1),
% 0.22/0.48    inference(resolution,[],[f206,f73])).
% 0.22/0.48  fof(f73,plain,(
% 0.22/0.48    ( ! [X0,X1] : (sP0(X0,X1) | r2_hidden(sK11(X0,X1),k10_yellow_6(X1,sK10(X0,X1)))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f36])).
% 0.22/0.48  fof(f220,plain,(
% 0.22/0.48    ( ! [X0] : (~r2_hidden(X0,k10_yellow_6(sK6,sK10(sK7,sK6))) | sP4(sK6,X0,sK7)) ) | (spl14_1 | ~spl14_4)),
% 0.22/0.48    inference(subsumption_resolution,[],[f219,f206])).
% 0.22/0.48  fof(f219,plain,(
% 0.22/0.48    ( ! [X0] : (~r2_hidden(X0,k10_yellow_6(sK6,sK10(sK7,sK6))) | sP4(sK6,X0,sK7) | sP0(sK7,sK6)) ) | (spl14_1 | ~spl14_4)),
% 0.22/0.48    inference(resolution,[],[f218,f71])).
% 0.22/0.48  fof(f71,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r1_waybel_0(X1,sK10(X0,X1),X0) | sP0(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f36])).
% 0.22/0.48  fof(f218,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r1_waybel_0(sK6,sK10(sK7,sK6),X1) | ~r2_hidden(X0,k10_yellow_6(sK6,sK10(sK7,sK6))) | sP4(sK6,X0,X1)) ) | (spl14_1 | ~spl14_4)),
% 0.22/0.48    inference(subsumption_resolution,[],[f217,f209])).
% 0.22/0.48  fof(f209,plain,(
% 0.22/0.48    v3_yellow_6(sK10(sK7,sK6),sK6) | spl14_1),
% 0.22/0.48    inference(resolution,[],[f206,f69])).
% 0.22/0.48  fof(f69,plain,(
% 0.22/0.48    ( ! [X0,X1] : (sP0(X0,X1) | v3_yellow_6(sK10(X0,X1),X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f36])).
% 0.22/0.48  fof(f217,plain,(
% 0.22/0.48    ( ! [X0,X1] : (sP4(sK6,X0,X1) | ~v3_yellow_6(sK10(sK7,sK6),sK6) | ~r2_hidden(X0,k10_yellow_6(sK6,sK10(sK7,sK6))) | ~r1_waybel_0(sK6,sK10(sK7,sK6),X1)) ) | (spl14_1 | ~spl14_4)),
% 0.22/0.48    inference(resolution,[],[f141,f210])).
% 0.22/0.48  fof(f210,plain,(
% 0.22/0.48    l1_waybel_0(sK10(sK7,sK6),sK6) | spl14_1),
% 0.22/0.48    inference(resolution,[],[f206,f70])).
% 0.22/0.48  fof(f70,plain,(
% 0.22/0.48    ( ! [X0,X1] : (sP0(X0,X1) | l1_waybel_0(sK10(X0,X1),X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f36])).
% 0.22/0.48  fof(f141,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~l1_waybel_0(sK10(sK7,sK6),X1) | sP4(X1,X0,X2) | ~v3_yellow_6(sK10(sK7,sK6),X1) | ~r2_hidden(X0,k10_yellow_6(X1,sK10(sK7,sK6))) | ~r1_waybel_0(X1,sK10(sK7,sK6),X2)) ) | ~spl14_4),
% 0.22/0.48    inference(avatar_component_clause,[],[f140])).
% 0.22/0.48  fof(f205,plain,(
% 0.22/0.48    spl14_1 | ~spl14_3),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f204])).
% 0.22/0.48  fof(f204,plain,(
% 0.22/0.48    $false | (spl14_1 | ~spl14_3)),
% 0.22/0.48    inference(subsumption_resolution,[],[f203,f110])).
% 0.22/0.48  fof(f203,plain,(
% 0.22/0.48    v4_pre_topc(sK7,sK6) | ~spl14_3),
% 0.22/0.48    inference(subsumption_resolution,[],[f118,f202])).
% 0.22/0.48  fof(f202,plain,(
% 0.22/0.48    sP0(sK7,sK6) | ~spl14_3),
% 0.22/0.48    inference(resolution,[],[f138,f66])).
% 0.22/0.48  fof(f66,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~v2_struct_0(sK10(X0,X1)) | sP0(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f36])).
% 0.22/0.48  fof(f138,plain,(
% 0.22/0.48    v2_struct_0(sK10(sK7,sK6)) | ~spl14_3),
% 0.22/0.48    inference(avatar_component_clause,[],[f136])).
% 0.22/0.48  fof(f136,plain,(
% 0.22/0.48    spl14_3 <=> v2_struct_0(sK10(sK7,sK6))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl14_3])])).
% 0.22/0.48  fof(f182,plain,(
% 0.22/0.48    ~spl14_1 | spl14_5),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f181])).
% 0.22/0.48  fof(f181,plain,(
% 0.22/0.48    $false | (~spl14_1 | spl14_5)),
% 0.22/0.48    inference(subsumption_resolution,[],[f180,f146])).
% 0.22/0.48  fof(f146,plain,(
% 0.22/0.48    m1_subset_1(sK9,u1_struct_0(sK6)) | ~spl14_1),
% 0.22/0.48    inference(subsumption_resolution,[],[f60,f109])).
% 0.22/0.48  fof(f180,plain,(
% 0.22/0.48    ~m1_subset_1(sK9,u1_struct_0(sK6)) | spl14_5),
% 0.22/0.48    inference(resolution,[],[f174,f130])).
% 0.22/0.48  fof(f174,plain,(
% 0.22/0.48    ~sP5(sK7,sK9,sK6) | spl14_5),
% 0.22/0.48    inference(avatar_component_clause,[],[f172])).
% 0.22/0.48  fof(f172,plain,(
% 0.22/0.48    spl14_5 <=> sP5(sK7,sK9,sK6)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl14_5])])).
% 0.22/0.48  fof(f179,plain,(
% 0.22/0.48    ~spl14_5 | spl14_6 | ~spl14_1 | spl14_2),
% 0.22/0.48    inference(avatar_split_clause,[],[f167,f112,f108,f176,f172])).
% 0.22/0.48  fof(f112,plain,(
% 0.22/0.48    spl14_2 <=> v1_xboole_0(sK8)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl14_2])])).
% 0.22/0.48  fof(f167,plain,(
% 0.22/0.48    sP4(sK6,sK9,sK7) | ~sP5(sK7,sK9,sK6) | (~spl14_1 | spl14_2)),
% 0.22/0.48    inference(resolution,[],[f166,f87])).
% 0.22/0.48  fof(f87,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~r2_hidden(X1,k2_pre_topc(X2,X0)) | sP4(X2,X1,X0) | ~sP5(X0,X1,X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f44])).
% 0.22/0.48  fof(f166,plain,(
% 0.22/0.48    r2_hidden(sK9,k2_pre_topc(sK6,sK7)) | (~spl14_1 | spl14_2)),
% 0.22/0.48    inference(subsumption_resolution,[],[f159,f146])).
% 0.22/0.48  fof(f159,plain,(
% 0.22/0.48    ~m1_subset_1(sK9,u1_struct_0(sK6)) | r2_hidden(sK9,k2_pre_topc(sK6,sK7)) | (~spl14_1 | spl14_2)),
% 0.22/0.48    inference(resolution,[],[f158,f134])).
% 0.22/0.48  fof(f134,plain,(
% 0.22/0.48    ( ! [X0] : (~sP2(X0,sK6,sK7) | ~m1_subset_1(X0,u1_struct_0(sK6)) | r2_hidden(X0,k2_pre_topc(sK6,sK7))) )),
% 0.22/0.48    inference(resolution,[],[f132,f77])).
% 0.22/0.48  fof(f77,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~sP3(X0,X1,X2) | ~sP2(X2,X1,X0) | r2_hidden(X2,k2_pre_topc(X1,X0))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f38])).
% 0.22/0.48  fof(f158,plain,(
% 0.22/0.48    sP2(sK9,sK6,sK7) | (~spl14_1 | spl14_2)),
% 0.22/0.48    inference(resolution,[],[f157,f143])).
% 0.22/0.48  fof(f143,plain,(
% 0.22/0.48    r2_hidden(sK7,sK8) | ~spl14_1),
% 0.22/0.48    inference(subsumption_resolution,[],[f59,f109])).
% 0.22/0.48  fof(f59,plain,(
% 0.22/0.48    r2_hidden(sK7,sK8) | ~v4_pre_topc(sK7,sK6)),
% 0.22/0.48    inference(cnf_transformation,[],[f30])).
% 0.22/0.48  fof(f157,plain,(
% 0.22/0.48    ( ! [X0] : (~r2_hidden(X0,sK8) | sP2(sK9,sK6,X0)) ) | (~spl14_1 | spl14_2)),
% 0.22/0.48    inference(resolution,[],[f156,f147])).
% 0.22/0.48  % (25050)dis+1011_4_awrs=decay:awrsf=32:afp=40000:afq=1.0:amm=off:anc=all:bs=on:cond=on:fsr=off:gsp=input_only:lma=on:nm=16:nwc=1:nicw=on:sac=on:sp=frequency:thi=all:updr=off:uhcvi=on_670 on theBenchmark
% 0.22/0.49  fof(f147,plain,(
% 0.22/0.49    r1_waybel_7(sK6,sK8,sK9) | ~spl14_1),
% 0.22/0.49    inference(subsumption_resolution,[],[f61,f109])).
% 0.22/0.49  fof(f61,plain,(
% 0.22/0.49    r1_waybel_7(sK6,sK8,sK9) | ~v4_pre_topc(sK7,sK6)),
% 0.22/0.49    inference(cnf_transformation,[],[f30])).
% 0.22/0.49  fof(f156,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r1_waybel_7(sK6,sK8,X0) | ~r2_hidden(X1,sK8) | sP2(X0,sK6,X1)) ) | (~spl14_1 | spl14_2)),
% 0.22/0.49    inference(subsumption_resolution,[],[f155,f153])).
% 0.22/0.49  fof(f153,plain,(
% 0.22/0.49    v1_subset_1(sK8,u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))) | ~spl14_1),
% 0.22/0.49    inference(subsumption_resolution,[],[f55,f109])).
% 0.22/0.49  fof(f55,plain,(
% 0.22/0.49    v1_subset_1(sK8,u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))) | ~v4_pre_topc(sK7,sK6)),
% 0.22/0.49    inference(cnf_transformation,[],[f30])).
% 0.22/0.49  fof(f155,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r1_waybel_7(sK6,sK8,X0) | ~r2_hidden(X1,sK8) | sP2(X0,sK6,X1) | ~v1_subset_1(sK8,u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))) ) | (~spl14_1 | spl14_2)),
% 0.22/0.49    inference(subsumption_resolution,[],[f152,f154])).
% 0.22/0.49  fof(f154,plain,(
% 0.22/0.49    m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))) | ~spl14_1),
% 0.22/0.49    inference(subsumption_resolution,[],[f58,f109])).
% 0.22/0.49  fof(f58,plain,(
% 0.22/0.49    m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))) | ~v4_pre_topc(sK7,sK6)),
% 0.22/0.49    inference(cnf_transformation,[],[f30])).
% 0.22/0.49  fof(f152,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r1_waybel_7(sK6,sK8,X0) | ~r2_hidden(X1,sK8) | ~m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))) | sP2(X0,sK6,X1) | ~v1_subset_1(sK8,u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))) ) | (~spl14_1 | spl14_2)),
% 0.22/0.49    inference(subsumption_resolution,[],[f151,f114])).
% 0.22/0.49  fof(f114,plain,(
% 0.22/0.49    ~v1_xboole_0(sK8) | spl14_2),
% 0.22/0.49    inference(avatar_component_clause,[],[f112])).
% 0.22/0.49  fof(f151,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r1_waybel_7(sK6,sK8,X0) | ~r2_hidden(X1,sK8) | ~m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))) | sP2(X0,sK6,X1) | ~v1_subset_1(sK8,u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))) | v1_xboole_0(sK8)) ) | ~spl14_1),
% 0.22/0.49    inference(subsumption_resolution,[],[f150,f148])).
% 0.22/0.49  fof(f148,plain,(
% 0.22/0.49    v2_waybel_0(sK8,k3_yellow_1(k2_struct_0(sK6))) | ~spl14_1),
% 0.22/0.49    inference(subsumption_resolution,[],[f56,f109])).
% 0.22/0.49  fof(f56,plain,(
% 0.22/0.49    v2_waybel_0(sK8,k3_yellow_1(k2_struct_0(sK6))) | ~v4_pre_topc(sK7,sK6)),
% 0.22/0.49    inference(cnf_transformation,[],[f30])).
% 0.22/0.49  fof(f150,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r1_waybel_7(sK6,sK8,X0) | ~r2_hidden(X1,sK8) | ~m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))) | sP2(X0,sK6,X1) | ~v2_waybel_0(sK8,k3_yellow_1(k2_struct_0(sK6))) | ~v1_subset_1(sK8,u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))) | v1_xboole_0(sK8)) ) | ~spl14_1),
% 0.22/0.49    inference(resolution,[],[f149,f85])).
% 0.22/0.49  fof(f85,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (~v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X1))) | ~r1_waybel_7(X1,X3,X0) | ~r2_hidden(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))) | sP2(X0,X1,X2) | ~v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X1))) | ~v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X1)))) | v1_xboole_0(X3)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f42])).
% 0.22/0.49  fof(f149,plain,(
% 0.22/0.49    v13_waybel_0(sK8,k3_yellow_1(k2_struct_0(sK6))) | ~spl14_1),
% 0.22/0.49    inference(subsumption_resolution,[],[f57,f109])).
% 0.22/0.49  fof(f57,plain,(
% 0.22/0.49    v13_waybel_0(sK8,k3_yellow_1(k2_struct_0(sK6))) | ~v4_pre_topc(sK7,sK6)),
% 0.22/0.49    inference(cnf_transformation,[],[f30])).
% 0.22/0.49  fof(f142,plain,(
% 0.22/0.49    spl14_3 | spl14_4 | spl14_1),
% 0.22/0.49    inference(avatar_split_clause,[],[f128,f108,f140,f136])).
% 0.22/0.49  fof(f128,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X0,k10_yellow_6(X1,sK10(sK7,sK6))) | ~r1_waybel_0(X1,sK10(sK7,sK6),X2) | ~l1_waybel_0(sK10(sK7,sK6),X1) | ~v3_yellow_6(sK10(sK7,sK6),X1) | sP4(X1,X0,X2) | v2_struct_0(sK10(sK7,sK6))) ) | spl14_1),
% 0.22/0.49    inference(subsumption_resolution,[],[f126,f120])).
% 0.22/0.49  fof(f120,plain,(
% 0.22/0.49    v4_orders_2(sK10(sK7,sK6)) | spl14_1),
% 0.22/0.49    inference(resolution,[],[f119,f67])).
% 0.22/0.49  fof(f67,plain,(
% 0.22/0.49    ( ! [X0,X1] : (sP0(X0,X1) | v4_orders_2(sK10(X0,X1))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f36])).
% 0.22/0.49  fof(f119,plain,(
% 0.22/0.49    ~sP0(sK7,sK6) | spl14_1),
% 0.22/0.49    inference(subsumption_resolution,[],[f118,f110])).
% 0.22/0.49  fof(f126,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X0,k10_yellow_6(X1,sK10(sK7,sK6))) | ~r1_waybel_0(X1,sK10(sK7,sK6),X2) | ~l1_waybel_0(sK10(sK7,sK6),X1) | ~v3_yellow_6(sK10(sK7,sK6),X1) | sP4(X1,X0,X2) | ~v4_orders_2(sK10(sK7,sK6)) | v2_struct_0(sK10(sK7,sK6))) ) | spl14_1),
% 0.22/0.49    inference(resolution,[],[f121,f96])).
% 0.22/0.49  fof(f96,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (~v7_waybel_0(X3) | ~r2_hidden(X1,k10_yellow_6(X0,X3)) | ~r1_waybel_0(X0,X3,X2) | ~l1_waybel_0(X3,X0) | ~v3_yellow_6(X3,X0) | sP4(X0,X1,X2) | ~v4_orders_2(X3) | v2_struct_0(X3)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f48])).
% 0.22/0.49  fof(f121,plain,(
% 0.22/0.49    v7_waybel_0(sK10(sK7,sK6)) | spl14_1),
% 0.22/0.49    inference(resolution,[],[f119,f68])).
% 0.22/0.49  fof(f68,plain,(
% 0.22/0.49    ( ! [X0,X1] : (sP0(X0,X1) | v7_waybel_0(sK10(X0,X1))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f36])).
% 0.22/0.49  fof(f115,plain,(
% 0.22/0.49    ~spl14_1 | ~spl14_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f54,f112,f108])).
% 0.22/0.49  fof(f54,plain,(
% 0.22/0.49    ~v1_xboole_0(sK8) | ~v4_pre_topc(sK7,sK6)),
% 0.22/0.49    inference(cnf_transformation,[],[f30])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (25043)------------------------------
% 0.22/0.49  % (25043)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (25043)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (25043)Memory used [KB]: 10106
% 0.22/0.49  % (25043)Time elapsed: 0.083 s
% 0.22/0.49  % (25043)------------------------------
% 0.22/0.49  % (25043)------------------------------
% 0.22/0.49  % (25033)Success in time 0.125 s
%------------------------------------------------------------------------------
