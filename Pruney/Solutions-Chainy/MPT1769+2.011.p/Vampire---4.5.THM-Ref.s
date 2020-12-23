%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:45 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.31s
% Verified   : 
% Statistics : Number of formulae       :  151 (2339 expanded)
%              Number of leaves         :   20 (1123 expanded)
%              Depth                    :   27
%              Number of atoms          :  994 (55313 expanded)
%              Number of equality atoms :   77 (3005 expanded)
%              Maximal formula depth    :   24 (   7 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f303,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f72,f73,f91,f96,f101,f229,f234,f293,f302])).

fof(f302,plain,
    ( spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(avatar_contradiction_clause,[],[f301])).

fof(f301,plain,
    ( $false
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f300,f295])).

fof(f295,plain,
    ( r2_funct_2(u1_struct_0(sK2),sK4,k2_tmap_1(sK0,sK1,sK4,sK2),sK4)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(forward_demodulation,[],[f294,f268])).

fof(f268,plain,
    ( u1_struct_0(sK1) = sK4
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(resolution,[],[f264,f85])).

fof(f85,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl7_3
  <=> v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f264,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | sK4 = X0 )
    | ~ spl7_4 ),
    inference(resolution,[],[f90,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

fof(f90,plain,
    ( v1_xboole_0(sK4)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl7_4
  <=> v1_xboole_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f294,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK4)
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(forward_demodulation,[],[f70,f270])).

fof(f270,plain,
    ( sK4 = sK5
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(resolution,[],[f264,f95])).

fof(f95,plain,
    ( v1_xboole_0(sK5)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl7_5
  <=> v1_xboole_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f70,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl7_2
  <=> r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f300,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),sK4,k2_tmap_1(sK0,sK1,sK4,sK2),sK4)
    | spl7_1
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(forward_demodulation,[],[f299,f268])).

fof(f299,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK4)
    | spl7_1
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(forward_demodulation,[],[f298,f226])).

fof(f226,plain,(
    k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(sK0,sK1,sK0,sK2,sK4) ),
    inference(subsumption_resolution,[],[f225,f77])).

fof(f77,plain,(
    ~ v2_struct_0(sK0) ),
    inference(forward_demodulation,[],[f40,f51])).

fof(f51,plain,(
    sK0 = sK3 ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
      | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5) )
    & ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5) )
    & r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6)
    & sK0 = sK3
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    & v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK1))
    & v1_funct_1(sK6)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    & v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
    & v1_funct_1(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK4)
    & m1_pre_topc(sK3,sK0)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f22,f29,f28,f27,f26,f25,f24,f23])).

fof(f23,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ? [X6] :
                                ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                                  | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
                                & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                                  | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
                                & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                                & X0 = X3
                                & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                                & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                                & v1_funct_1(X6) )
                            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                            & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                            & v1_funct_1(X5) )
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                    & m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(sK0,X1,X4,X2),X5)
                                | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK0,X1,X3,X2,X6),X5) )
                              & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(sK0,X1,X4,X2),X5)
                                | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK0,X1,X3,X2,X6),X5) )
                              & r1_funct_2(u1_struct_0(sK0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                              & sK0 = X3
                              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(X6) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,sK0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ? [X6] :
                            ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(sK0,X1,X4,X2),X5)
                              | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK0,X1,X3,X2,X6),X5) )
                            & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(sK0,X1,X4,X2),X5)
                              | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK0,X1,X3,X2,X6),X5) )
                            & r1_funct_2(u1_struct_0(sK0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                            & sK0 = X3
                            & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(X6) )
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X5) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
                    & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X1))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,sK0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK0)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,X4,X2),X5)
                            | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X3,X2,X6),X5) )
                          & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,X4,X2),X5)
                            | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X3,X2,X6),X5) )
                          & r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(X3),u1_struct_0(sK1),X4,X6)
                          & sK0 = X3
                          & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                          & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(sK1))
                          & v1_funct_1(X6) )
                      & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1))))
                      & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(sK1))
                      & v1_funct_1(X5) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
                  & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1))
                  & v1_funct_1(X4) )
              & m1_pre_topc(X3,sK0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK0)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,X4,X2),X5)
                          | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X3,X2,X6),X5) )
                        & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,X4,X2),X5)
                          | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X3,X2,X6),X5) )
                        & r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(X3),u1_struct_0(sK1),X4,X6)
                        & sK0 = X3
                        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                        & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(sK1))
                        & v1_funct_1(X6) )
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1))))
                    & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(sK1))
                    & v1_funct_1(X5) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
                & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,sK0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,X4,sK2),X5)
                        | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X3,sK2,X6),X5) )
                      & ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,X4,sK2),X5)
                        | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X3,sK2,X6),X5) )
                      & r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(X3),u1_struct_0(sK1),X4,X6)
                      & sK0 = X3
                      & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                      & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(sK1))
                      & v1_funct_1(X6) )
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
                  & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(sK1))
                  & v1_funct_1(X5) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
              & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,sK0)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,X4,sK2),X5)
                      | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X3,sK2,X6),X5) )
                    & ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,X4,sK2),X5)
                      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X3,sK2,X6),X5) )
                    & r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(X3),u1_struct_0(sK1),X4,X6)
                    & sK0 = X3
                    & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                    & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(sK1))
                    & v1_funct_1(X6) )
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
                & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(sK1))
                & v1_funct_1(X5) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
            & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1))
            & v1_funct_1(X4) )
        & m1_pre_topc(X3,sK0)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,X4,sK2),X5)
                    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,X6),X5) )
                  & ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,X4,sK2),X5)
                    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,X6),X5) )
                  & r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK3),u1_struct_0(sK1),X4,X6)
                  & sK0 = sK3
                  & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
                  & v1_funct_2(X6,u1_struct_0(sK3),u1_struct_0(sK1))
                  & v1_funct_1(X6) )
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
              & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(sK1))
              & v1_funct_1(X5) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X4) )
      & m1_pre_topc(sK3,sK0)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ? [X6] :
                ( ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,X4,sK2),X5)
                  | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,X6),X5) )
                & ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,X4,sK2),X5)
                  | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,X6),X5) )
                & r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK3),u1_struct_0(sK1),X4,X6)
                & sK0 = sK3
                & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
                & v1_funct_2(X6,u1_struct_0(sK3),u1_struct_0(sK1))
                & v1_funct_1(X6) )
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
            & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(sK1))
            & v1_funct_1(X5) )
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( ? [X6] :
              ( ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),X5)
                | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,X6),X5) )
              & ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),X5)
                | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,X6),X5) )
              & r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK3),u1_struct_0(sK1),sK4,X6)
              & sK0 = sK3
              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
              & v1_funct_2(X6,u1_struct_0(sK3),u1_struct_0(sK1))
              & v1_funct_1(X6) )
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
          & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(sK1))
          & v1_funct_1(X5) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X5] :
        ( ? [X6] :
            ( ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),X5)
              | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,X6),X5) )
            & ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),X5)
              | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,X6),X5) )
            & r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK3),u1_struct_0(sK1),sK4,X6)
            & sK0 = sK3
            & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
            & v1_funct_2(X6,u1_struct_0(sK3),u1_struct_0(sK1))
            & v1_funct_1(X6) )
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(sK1))
        & v1_funct_1(X5) )
   => ( ? [X6] :
          ( ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
            | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,X6),sK5) )
          & ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
            | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,X6),sK5) )
          & r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK3),u1_struct_0(sK1),sK4,X6)
          & sK0 = sK3
          & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
          & v1_funct_2(X6,u1_struct_0(sK3),u1_struct_0(sK1))
          & v1_funct_1(X6) )
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
      & v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X6] :
        ( ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
          | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,X6),sK5) )
        & ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
          | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,X6),sK5) )
        & r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK3),u1_struct_0(sK1),sK4,X6)
        & sK0 = sK3
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        & v1_funct_2(X6,u1_struct_0(sK3),u1_struct_0(sK1))
        & v1_funct_1(X6) )
   => ( ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
        | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5) )
      & ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
        | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5) )
      & r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6)
      & sK0 = sK3
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      & v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK1))
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                                | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
                              & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                                | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
                              & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                              & X0 = X3
                              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(X6) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                                | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
                              & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                                | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
                              & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                              & X0 = X3
                              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(X6) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)
                              <~> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) )
                              & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                              & X0 = X3
                              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(X6) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)
                              <~> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) )
                              & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                              & X0 = X3
                              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(X6) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ! [X5] :
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                              & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                              & v1_funct_1(X5) )
                           => ! [X6] :
                                ( ( m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                                  & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                                  & v1_funct_1(X6) )
                               => ( ( r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                                    & X0 = X3 )
                                 => ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)
                                  <=> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                            & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                            & v1_funct_1(X5) )
                         => ! [X6] :
                              ( ( m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                                & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                                & v1_funct_1(X6) )
                             => ( ( r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                                  & X0 = X3 )
                               => ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)
                                <=> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_tmap_1)).

fof(f40,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f30])).

fof(f225,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(sK0,sK1,sK0,sK2,sK4)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f224,f33])).

fof(f33,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f224,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(sK0,sK1,sK0,sK2,sK4)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f223,f34])).

fof(f34,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f223,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(sK0,sK1,sK0,sK2,sK4)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f211,f76])).

fof(f76,plain,(
    m1_pre_topc(sK0,sK0) ),
    inference(forward_demodulation,[],[f41,f51])).

fof(f41,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f211,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK0,X0)
      | k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(X0,sK1,sK0,sK2,sK4)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(forward_demodulation,[],[f210,f167])).

fof(f167,plain,(
    k2_tmap_1(sK0,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f166,f35])).

fof(f35,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f166,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2))
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f165,f36])).

fof(f36,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f165,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2))
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f164,f37])).

fof(f37,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f164,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f163,f42])).

fof(f42,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f30])).

fof(f163,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2))
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f161,f43])).

fof(f43,plain,(
    v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f30])).

fof(f161,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f131,f44])).

fof(f44,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f30])).

fof(f131,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | k2_tmap_1(sK0,X0,X1,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X0),X1,u1_struct_0(sK2))
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f130,f77])).

% (3310)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% (3313)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% (3297)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% (3314)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% (3303)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% (3296)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% (3311)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% (3312)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% (3289)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% (3309)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
fof(f130,plain,(
    ! [X0,X1] :
      ( k2_tmap_1(sK0,X0,X1,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X0),X1,u1_struct_0(sK2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f129,f33])).

fof(f129,plain,(
    ! [X0,X1] :
      ( k2_tmap_1(sK0,X0,X1,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X0),X1,u1_struct_0(sK2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f127,f34])).

fof(f127,plain,(
    ! [X0,X1] :
      ( k2_tmap_1(sK0,X0,X1,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X0),X1,u1_struct_0(sK2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f56,f39])).

fof(f39,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_pre_topc(X3,X0)
      | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).

% (3302)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
fof(f210,plain,(
    ! [X0] :
      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(X0,sK1,sK0,sK2,sK4)
      | ~ m1_pre_topc(sK0,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f209,f35])).

fof(f209,plain,(
    ! [X0] :
      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(X0,sK1,sK0,sK2,sK4)
      | ~ m1_pre_topc(sK0,X0)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f208,f36])).

fof(f208,plain,(
    ! [X0] :
      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(X0,sK1,sK0,sK2,sK4)
      | ~ m1_pre_topc(sK0,X0)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f207,f37])).

fof(f207,plain,(
    ! [X0] :
      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(X0,sK1,sK0,sK2,sK4)
      | ~ m1_pre_topc(sK0,X0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f206,f42])).

fof(f206,plain,(
    ! [X0] :
      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(X0,sK1,sK0,sK2,sK4)
      | ~ v1_funct_1(sK4)
      | ~ m1_pre_topc(sK0,X0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f204,f43])).

fof(f204,plain,(
    ! [X0] :
      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(X0,sK1,sK0,sK2,sK4)
      | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(sK4)
      | ~ m1_pre_topc(sK0,X0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f138,f44])).

fof(f138,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | k3_tmap_1(X0,X1,sK0,sK2,X2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X1),X2,u1_struct_0(sK2))
      | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(sK0,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f135,f102])).

fof(f102,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK0,X0)
      | m1_pre_topc(sK2,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(resolution,[],[f57,f39])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X2,X1)
      | m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).

fof(f135,plain,(
    ! [X2,X0,X1] :
      ( k3_tmap_1(X0,X1,sK0,sK2,X2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X1),X2,u1_struct_0(sK2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(sK2,X0)
      | ~ m1_pre_topc(sK0,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f55,f39])).

fof(f55,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_pre_topc(X3,X2)
      | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X3,X2)
                       => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).

fof(f298,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK4)
    | spl7_1
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(forward_demodulation,[],[f297,f51])).

fof(f297,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK4)
    | spl7_1
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(forward_demodulation,[],[f296,f271])).

fof(f271,plain,
    ( sK4 = sK6
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(resolution,[],[f264,f100])).

% (3296)Refutation not found, incomplete strategy% (3296)------------------------------
% (3296)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (3296)Termination reason: Refutation not found, incomplete strategy

% (3296)Memory used [KB]: 1663
% (3296)Time elapsed: 0.119 s
% (3296)------------------------------
% (3296)------------------------------
fof(f100,plain,
    ( v1_xboole_0(sK6)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl7_6
  <=> v1_xboole_0(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f296,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK4)
    | spl7_1
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(forward_demodulation,[],[f67,f270])).

fof(f67,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl7_1
  <=> r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f293,plain,
    ( ~ spl7_1
    | spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(avatar_contradiction_clause,[],[f292])).

fof(f292,plain,
    ( $false
    | ~ spl7_1
    | spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f291,f288])).

fof(f288,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),sK4,k2_tmap_1(sK0,sK1,sK4,sK2),sK4)
    | spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(forward_demodulation,[],[f283,f268])).

fof(f283,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK4)
    | spl7_2
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(superposition,[],[f71,f270])).

fof(f71,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f69])).

fof(f291,plain,
    ( r2_funct_2(u1_struct_0(sK2),sK4,k2_tmap_1(sK0,sK1,sK4,sK2),sK4)
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(forward_demodulation,[],[f290,f268])).

fof(f290,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK4)
    | ~ spl7_1
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(forward_demodulation,[],[f289,f226])).

fof(f289,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK4)
    | ~ spl7_1
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(forward_demodulation,[],[f285,f271])).

fof(f285,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK6),sK4)
    | ~ spl7_1
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(superposition,[],[f235,f270])).

fof(f235,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK6),sK5)
    | ~ spl7_1 ),
    inference(forward_demodulation,[],[f66,f51])).

fof(f66,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f65])).

fof(f234,plain,
    ( ~ spl7_1
    | spl7_2
    | spl7_3 ),
    inference(avatar_contradiction_clause,[],[f233])).

fof(f233,plain,
    ( $false
    | ~ spl7_1
    | spl7_2
    | spl7_3 ),
    inference(subsumption_resolution,[],[f232,f71])).

fof(f232,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | ~ spl7_1
    | spl7_3 ),
    inference(forward_demodulation,[],[f231,f226])).

fof(f231,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5)
    | ~ spl7_1
    | spl7_3 ),
    inference(forward_demodulation,[],[f230,f51])).

fof(f230,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)
    | ~ spl7_1
    | spl7_3 ),
    inference(forward_demodulation,[],[f66,f126])).

fof(f126,plain,
    ( sK4 = sK6
    | spl7_3 ),
    inference(subsumption_resolution,[],[f125,f75])).

fof(f75,plain,(
    v1_funct_2(sK6,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f49,f51])).

fof(f49,plain,(
    v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f30])).

fof(f125,plain,
    ( ~ v1_funct_2(sK6,u1_struct_0(sK0),u1_struct_0(sK1))
    | sK4 = sK6
    | spl7_3 ),
    inference(forward_demodulation,[],[f124,f51])).

fof(f124,plain,
    ( sK4 = sK6
    | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK1))
    | spl7_3 ),
    inference(subsumption_resolution,[],[f123,f74])).

fof(f74,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(forward_demodulation,[],[f50,f51])).

fof(f50,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f30])).

fof(f123,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | sK4 = sK6
    | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK1))
    | spl7_3 ),
    inference(forward_demodulation,[],[f122,f51])).

fof(f122,plain,
    ( sK4 = sK6
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK1))
    | spl7_3 ),
    inference(subsumption_resolution,[],[f121,f86])).

fof(f86,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | spl7_3 ),
    inference(avatar_component_clause,[],[f84])).

fof(f121,plain,
    ( sK4 = sK6
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f120,f42])).

fof(f120,plain,
    ( sK4 = sK6
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f119,f43])).

fof(f119,plain,
    ( sK4 = sK6
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f118,f44])).

fof(f118,plain,
    ( sK4 = sK6
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f117,f48])).

fof(f48,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f30])).

fof(f117,plain,
    ( sK4 = sK6
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK6)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(duplicate_literal_removal,[],[f116])).

fof(f116,plain,
    ( sK4 = sK6
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK6)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(resolution,[],[f60,f52])).

fof(f52,plain,(
    r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6) ),
    inference(cnf_transformation,[],[f30])).

fof(f60,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
      | X4 = X5
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
          | X4 != X5 )
        & ( X4 = X5
          | ~ r1_funct_2(X0,X1,X2,X3,X4,X5) ) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_2(X5,X2,X3)
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X4,X0,X1)
        & v1_funct_1(X4)
        & ~ v1_xboole_0(X3)
        & ~ v1_xboole_0(X1) )
     => ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_funct_2)).

fof(f229,plain,
    ( spl7_1
    | ~ spl7_2
    | spl7_3 ),
    inference(avatar_contradiction_clause,[],[f228])).

fof(f228,plain,
    ( $false
    | spl7_1
    | ~ spl7_2
    | spl7_3 ),
    inference(subsumption_resolution,[],[f227,f70])).

fof(f227,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | spl7_1
    | spl7_3 ),
    inference(superposition,[],[f143,f226])).

fof(f143,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5)
    | spl7_1
    | spl7_3 ),
    inference(superposition,[],[f78,f126])).

fof(f78,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK6),sK5)
    | spl7_1 ),
    inference(forward_demodulation,[],[f67,f51])).

fof(f101,plain,
    ( ~ spl7_3
    | spl7_6 ),
    inference(avatar_split_clause,[],[f82,f98,f84])).

fof(f82,plain,
    ( v1_xboole_0(sK6)
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(resolution,[],[f58,f74])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | v1_xboole_0(X2)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f96,plain,
    ( ~ spl7_3
    | spl7_5 ),
    inference(avatar_split_clause,[],[f81,f93,f84])).

fof(f81,plain,
    ( v1_xboole_0(sK5)
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(resolution,[],[f58,f47])).

fof(f47,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f30])).

fof(f91,plain,
    ( ~ spl7_3
    | spl7_4 ),
    inference(avatar_split_clause,[],[f80,f88,f84])).

fof(f80,plain,
    ( v1_xboole_0(sK4)
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(resolution,[],[f58,f44])).

fof(f73,plain,
    ( spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f53,f69,f65])).

fof(f53,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5) ),
    inference(cnf_transformation,[],[f30])).

fof(f72,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f54,f69,f65])).

fof(f54,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:13:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.46  % (3298)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.46  % (3306)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.50  % (3301)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.51  % (3307)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.51  % (3292)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.51  % (3291)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.51  % (3305)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.51  % (3300)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.51  % (3293)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.51  % (3290)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (3293)Refutation not found, incomplete strategy% (3293)------------------------------
% 0.20/0.52  % (3293)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (3293)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (3293)Memory used [KB]: 6268
% 0.20/0.52  % (3293)Time elapsed: 0.100 s
% 0.20/0.52  % (3293)------------------------------
% 0.20/0.52  % (3293)------------------------------
% 0.20/0.52  % (3299)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.52  % (3294)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.52  % (3308)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.52  % (3299)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f303,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(avatar_sat_refutation,[],[f72,f73,f91,f96,f101,f229,f234,f293,f302])).
% 0.20/0.52  fof(f302,plain,(
% 0.20/0.52    spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f301])).
% 0.20/0.52  fof(f301,plain,(
% 0.20/0.52    $false | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6)),
% 0.20/0.52    inference(subsumption_resolution,[],[f300,f295])).
% 0.20/0.52  fof(f295,plain,(
% 0.20/0.52    r2_funct_2(u1_struct_0(sK2),sK4,k2_tmap_1(sK0,sK1,sK4,sK2),sK4) | (~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5)),
% 0.20/0.52    inference(forward_demodulation,[],[f294,f268])).
% 0.20/0.52  fof(f268,plain,(
% 0.20/0.52    u1_struct_0(sK1) = sK4 | (~spl7_3 | ~spl7_4)),
% 0.20/0.52    inference(resolution,[],[f264,f85])).
% 0.20/0.52  fof(f85,plain,(
% 0.20/0.52    v1_xboole_0(u1_struct_0(sK1)) | ~spl7_3),
% 0.20/0.52    inference(avatar_component_clause,[],[f84])).
% 0.20/0.52  fof(f84,plain,(
% 0.20/0.52    spl7_3 <=> v1_xboole_0(u1_struct_0(sK1))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.20/0.52  fof(f264,plain,(
% 0.20/0.52    ( ! [X0] : (~v1_xboole_0(X0) | sK4 = X0) ) | ~spl7_4),
% 0.20/0.52    inference(resolution,[],[f90,f59])).
% 0.20/0.52  fof(f59,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f18])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).
% 0.20/0.52  fof(f90,plain,(
% 0.20/0.52    v1_xboole_0(sK4) | ~spl7_4),
% 0.20/0.52    inference(avatar_component_clause,[],[f88])).
% 0.20/0.52  fof(f88,plain,(
% 0.20/0.52    spl7_4 <=> v1_xboole_0(sK4)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.20/0.52  fof(f294,plain,(
% 0.20/0.52    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK4) | (~spl7_2 | ~spl7_4 | ~spl7_5)),
% 0.20/0.52    inference(forward_demodulation,[],[f70,f270])).
% 0.20/0.52  fof(f270,plain,(
% 0.20/0.52    sK4 = sK5 | (~spl7_4 | ~spl7_5)),
% 0.20/0.52    inference(resolution,[],[f264,f95])).
% 0.20/0.52  fof(f95,plain,(
% 0.20/0.52    v1_xboole_0(sK5) | ~spl7_5),
% 0.20/0.52    inference(avatar_component_clause,[],[f93])).
% 0.20/0.52  fof(f93,plain,(
% 0.20/0.52    spl7_5 <=> v1_xboole_0(sK5)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.20/0.52  fof(f70,plain,(
% 0.20/0.52    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | ~spl7_2),
% 0.20/0.52    inference(avatar_component_clause,[],[f69])).
% 0.20/0.52  fof(f69,plain,(
% 0.20/0.52    spl7_2 <=> r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.20/0.52  fof(f300,plain,(
% 0.20/0.52    ~r2_funct_2(u1_struct_0(sK2),sK4,k2_tmap_1(sK0,sK1,sK4,sK2),sK4) | (spl7_1 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6)),
% 0.20/0.52    inference(forward_demodulation,[],[f299,f268])).
% 0.20/0.52  fof(f299,plain,(
% 0.20/0.52    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK4) | (spl7_1 | ~spl7_4 | ~spl7_5 | ~spl7_6)),
% 0.20/0.52    inference(forward_demodulation,[],[f298,f226])).
% 0.20/0.52  fof(f226,plain,(
% 0.20/0.52    k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(sK0,sK1,sK0,sK2,sK4)),
% 0.20/0.52    inference(subsumption_resolution,[],[f225,f77])).
% 0.20/0.52  fof(f77,plain,(
% 0.20/0.52    ~v2_struct_0(sK0)),
% 0.20/0.52    inference(forward_demodulation,[],[f40,f51])).
% 0.20/0.52  fof(f51,plain,(
% 0.20/0.52    sK0 = sK3),
% 0.20/0.52    inference(cnf_transformation,[],[f30])).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    (((((((~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)) & (r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)) & r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6) & sK0 = sK3 & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK6)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f22,f29,f28,f27,f26,f25,f24,f23])).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(sK0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(sK0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(sK0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & sK0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f24,plain,(
% 0.20/0.53    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(sK0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(sK0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(sK0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & sK0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(X3),u1_struct_0(sK1),X4,X6) & sK0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f25,plain,(
% 0.20/0.53    ? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(X3),u1_struct_0(sK1),X4,X6) & sK0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,X4,sK2),X5) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X3,sK2,X6),X5)) & (r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,X4,sK2),X5) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X3,sK2,X6),X5)) & r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(X3),u1_struct_0(sK1),X4,X6) & sK0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f26,plain,(
% 0.20/0.53    ? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,X4,sK2),X5) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X3,sK2,X6),X5)) & (r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,X4,sK2),X5) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X3,sK2,X6),X5)) & r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(X3),u1_struct_0(sK1),X4,X6) & sK0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,X4,sK2),X5) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,X6),X5)) & (r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,X4,sK2),X5) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,X6),X5)) & r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK3),u1_struct_0(sK1),X4,X6) & sK0 = sK3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(X6,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f27,plain,(
% 0.20/0.53    ? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,X4,sK2),X5) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,X6),X5)) & (r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,X4,sK2),X5) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,X6),X5)) & r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK3),u1_struct_0(sK1),X4,X6) & sK0 = sK3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(X6,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),X5) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,X6),X5)) & (r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),X5) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,X6),X5)) & r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK3),u1_struct_0(sK1),sK4,X6) & sK0 = sK3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(X6,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK4))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f28,plain,(
% 0.20/0.53    ? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),X5) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,X6),X5)) & (r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),X5) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,X6),X5)) & r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK3),u1_struct_0(sK1),sK4,X6) & sK0 = sK3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(X6,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(X5)) => (? [X6] : ((~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,X6),sK5)) & (r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,X6),sK5)) & r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK3),u1_struct_0(sK1),sK4,X6) & sK0 = sK3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(X6,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(X6)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(sK5))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f29,plain,(
% 0.20/0.53    ? [X6] : ((~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,X6),sK5)) & (r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,X6),sK5)) & r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK3),u1_struct_0(sK1),sK4,X6) & sK0 = sK3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(X6,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(X6)) => ((~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)) & (r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)) & r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6) & sK0 = sK3 & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK6))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f22,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.53    inference(flattening,[],[f21])).
% 0.20/0.53  fof(f21,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5))) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.53    inference(nnf_transformation,[],[f10])).
% 0.20/0.53  fof(f10,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) <~> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.53    inference(flattening,[],[f9])).
% 0.20/0.53  fof(f9,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) <~> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)) & (r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3)) & (m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f8])).
% 0.20/0.53  fof(f8,negated_conjecture,(
% 0.20/0.53    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) => ((r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3) => (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) <=> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5))))))))))),
% 0.20/0.53    inference(negated_conjecture,[],[f7])).
% 0.20/0.53  fof(f7,conjecture,(
% 0.20/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) => ((r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3) => (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) <=> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5))))))))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_tmap_1)).
% 0.20/0.53  fof(f40,plain,(
% 0.20/0.53    ~v2_struct_0(sK3)),
% 0.20/0.53    inference(cnf_transformation,[],[f30])).
% 0.20/0.53  fof(f225,plain,(
% 0.20/0.53    k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(sK0,sK1,sK0,sK2,sK4) | v2_struct_0(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f224,f33])).
% 0.20/0.53  fof(f33,plain,(
% 0.20/0.53    v2_pre_topc(sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f30])).
% 0.20/0.53  fof(f224,plain,(
% 0.20/0.53    k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(sK0,sK1,sK0,sK2,sK4) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f223,f34])).
% 0.20/0.53  fof(f34,plain,(
% 0.20/0.53    l1_pre_topc(sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f30])).
% 0.20/0.53  fof(f223,plain,(
% 0.20/0.53    k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(sK0,sK1,sK0,sK2,sK4) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.53    inference(resolution,[],[f211,f76])).
% 0.20/0.53  fof(f76,plain,(
% 0.20/0.53    m1_pre_topc(sK0,sK0)),
% 0.20/0.53    inference(forward_demodulation,[],[f41,f51])).
% 0.20/0.53  fof(f41,plain,(
% 0.20/0.53    m1_pre_topc(sK3,sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f30])).
% 0.20/0.53  fof(f211,plain,(
% 0.20/0.53    ( ! [X0] : (~m1_pre_topc(sK0,X0) | k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(X0,sK1,sK0,sK2,sK4) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.53    inference(forward_demodulation,[],[f210,f167])).
% 0.20/0.53  fof(f167,plain,(
% 0.20/0.53    k2_tmap_1(sK0,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2))),
% 0.20/0.53    inference(subsumption_resolution,[],[f166,f35])).
% 0.20/0.53  fof(f35,plain,(
% 0.20/0.53    ~v2_struct_0(sK1)),
% 0.20/0.53    inference(cnf_transformation,[],[f30])).
% 0.20/0.53  fof(f166,plain,(
% 0.20/0.53    k2_tmap_1(sK0,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) | v2_struct_0(sK1)),
% 0.20/0.53    inference(subsumption_resolution,[],[f165,f36])).
% 0.20/0.53  fof(f36,plain,(
% 0.20/0.53    v2_pre_topc(sK1)),
% 0.20/0.53    inference(cnf_transformation,[],[f30])).
% 0.20/0.53  fof(f165,plain,(
% 0.20/0.53    k2_tmap_1(sK0,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)),
% 0.20/0.53    inference(subsumption_resolution,[],[f164,f37])).
% 0.20/0.53  fof(f37,plain,(
% 0.20/0.53    l1_pre_topc(sK1)),
% 0.20/0.53    inference(cnf_transformation,[],[f30])).
% 0.20/0.53  fof(f164,plain,(
% 0.20/0.53    k2_tmap_1(sK0,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)),
% 0.20/0.53    inference(subsumption_resolution,[],[f163,f42])).
% 0.20/0.53  fof(f42,plain,(
% 0.20/0.53    v1_funct_1(sK4)),
% 0.20/0.53    inference(cnf_transformation,[],[f30])).
% 0.20/0.53  fof(f163,plain,(
% 0.20/0.53    k2_tmap_1(sK0,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)),
% 0.20/0.53    inference(subsumption_resolution,[],[f161,f43])).
% 0.20/0.53  fof(f43,plain,(
% 0.20/0.53    v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.20/0.53    inference(cnf_transformation,[],[f30])).
% 0.20/0.53  fof(f161,plain,(
% 0.20/0.53    k2_tmap_1(sK0,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)),
% 0.20/0.53    inference(resolution,[],[f131,f44])).
% 0.20/0.53  fof(f44,plain,(
% 0.20/0.53    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.20/0.53    inference(cnf_transformation,[],[f30])).
% 0.20/0.53  fof(f131,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | k2_tmap_1(sK0,X0,X1,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X0),X1,u1_struct_0(sK2)) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f130,f77])).
% 0.20/0.53  % (3310)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.53  % (3313)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.31/0.53  % (3297)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.31/0.53  % (3314)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.31/0.53  % (3303)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.31/0.54  % (3296)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.31/0.54  % (3311)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.31/0.54  % (3312)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.31/0.54  % (3289)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.31/0.54  % (3309)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.31/0.54  fof(f130,plain,(
% 1.31/0.54    ( ! [X0,X1] : (k2_tmap_1(sK0,X0,X1,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X0),X1,u1_struct_0(sK2)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v2_struct_0(sK0)) )),
% 1.31/0.54    inference(subsumption_resolution,[],[f129,f33])).
% 1.31/0.54  fof(f129,plain,(
% 1.31/0.54    ( ! [X0,X1] : (k2_tmap_1(sK0,X0,X1,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X0),X1,u1_struct_0(sK2)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.31/0.54    inference(subsumption_resolution,[],[f127,f34])).
% 1.31/0.54  fof(f127,plain,(
% 1.31/0.54    ( ! [X0,X1] : (k2_tmap_1(sK0,X0,X1,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X0),X1,u1_struct_0(sK2)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.31/0.54    inference(resolution,[],[f56,f39])).
% 1.31/0.54  fof(f39,plain,(
% 1.31/0.54    m1_pre_topc(sK2,sK0)),
% 1.31/0.54    inference(cnf_transformation,[],[f30])).
% 1.31/0.54  fof(f56,plain,(
% 1.31/0.54    ( ! [X2,X0,X3,X1] : (~m1_pre_topc(X3,X0) | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.31/0.54    inference(cnf_transformation,[],[f14])).
% 1.31/0.54  fof(f14,plain,(
% 1.31/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.31/0.54    inference(flattening,[],[f13])).
% 1.31/0.54  fof(f13,plain,(
% 1.31/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.31/0.54    inference(ennf_transformation,[],[f4])).
% 1.31/0.54  fof(f4,axiom,(
% 1.31/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 1.31/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).
% 1.31/0.54  % (3302)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.31/0.54  fof(f210,plain,(
% 1.31/0.54    ( ! [X0] : (k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(X0,sK1,sK0,sK2,sK4) | ~m1_pre_topc(sK0,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.31/0.54    inference(subsumption_resolution,[],[f209,f35])).
% 1.31/0.54  fof(f209,plain,(
% 1.31/0.54    ( ! [X0] : (k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(X0,sK1,sK0,sK2,sK4) | ~m1_pre_topc(sK0,X0) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.31/0.54    inference(subsumption_resolution,[],[f208,f36])).
% 1.31/0.54  fof(f208,plain,(
% 1.31/0.54    ( ! [X0] : (k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(X0,sK1,sK0,sK2,sK4) | ~m1_pre_topc(sK0,X0) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.31/0.54    inference(subsumption_resolution,[],[f207,f37])).
% 1.31/0.54  fof(f207,plain,(
% 1.31/0.54    ( ! [X0] : (k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(X0,sK1,sK0,sK2,sK4) | ~m1_pre_topc(sK0,X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.31/0.54    inference(subsumption_resolution,[],[f206,f42])).
% 1.31/0.54  fof(f206,plain,(
% 1.31/0.54    ( ! [X0] : (k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(X0,sK1,sK0,sK2,sK4) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK0,X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.31/0.54    inference(subsumption_resolution,[],[f204,f43])).
% 1.31/0.54  fof(f204,plain,(
% 1.31/0.54    ( ! [X0] : (k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(X0,sK1,sK0,sK2,sK4) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK0,X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.31/0.54    inference(resolution,[],[f138,f44])).
% 1.31/0.54  fof(f138,plain,(
% 1.31/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | k3_tmap_1(X0,X1,sK0,sK2,X2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X1),X2,u1_struct_0(sK2)) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~m1_pre_topc(sK0,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.31/0.54    inference(subsumption_resolution,[],[f135,f102])).
% 1.31/0.54  fof(f102,plain,(
% 1.31/0.54    ( ! [X0] : (~m1_pre_topc(sK0,X0) | m1_pre_topc(sK2,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.31/0.54    inference(resolution,[],[f57,f39])).
% 1.31/0.54  fof(f57,plain,(
% 1.31/0.54    ( ! [X2,X0,X1] : (~m1_pre_topc(X2,X1) | m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.31/0.54    inference(cnf_transformation,[],[f16])).
% 1.31/0.54  fof(f16,plain,(
% 1.31/0.54    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.31/0.54    inference(flattening,[],[f15])).
% 1.31/0.54  fof(f15,plain,(
% 1.31/0.54    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.31/0.54    inference(ennf_transformation,[],[f6])).
% 1.31/0.54  fof(f6,axiom,(
% 1.31/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 1.31/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).
% 1.31/0.54  fof(f135,plain,(
% 1.31/0.54    ( ! [X2,X0,X1] : (k3_tmap_1(X0,X1,sK0,sK2,X2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X1),X2,u1_struct_0(sK2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~m1_pre_topc(sK2,X0) | ~m1_pre_topc(sK0,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.31/0.54    inference(resolution,[],[f55,f39])).
% 1.31/0.54  fof(f55,plain,(
% 1.31/0.54    ( ! [X4,X2,X0,X3,X1] : (~m1_pre_topc(X3,X2) | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.31/0.54    inference(cnf_transformation,[],[f12])).
% 1.31/0.54  fof(f12,plain,(
% 1.31/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.31/0.54    inference(flattening,[],[f11])).
% 1.31/0.54  fof(f11,plain,(
% 1.31/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.31/0.54    inference(ennf_transformation,[],[f5])).
% 1.31/0.54  fof(f5,axiom,(
% 1.31/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))))))))),
% 1.31/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).
% 1.31/0.54  fof(f298,plain,(
% 1.31/0.54    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK4) | (spl7_1 | ~spl7_4 | ~spl7_5 | ~spl7_6)),
% 1.31/0.54    inference(forward_demodulation,[],[f297,f51])).
% 1.31/0.54  fof(f297,plain,(
% 1.31/0.54    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK4) | (spl7_1 | ~spl7_4 | ~spl7_5 | ~spl7_6)),
% 1.31/0.54    inference(forward_demodulation,[],[f296,f271])).
% 1.31/0.54  fof(f271,plain,(
% 1.31/0.54    sK4 = sK6 | (~spl7_4 | ~spl7_6)),
% 1.31/0.54    inference(resolution,[],[f264,f100])).
% 1.31/0.54  % (3296)Refutation not found, incomplete strategy% (3296)------------------------------
% 1.31/0.54  % (3296)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.54  % (3296)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.54  
% 1.31/0.54  % (3296)Memory used [KB]: 1663
% 1.31/0.54  % (3296)Time elapsed: 0.119 s
% 1.31/0.54  % (3296)------------------------------
% 1.31/0.54  % (3296)------------------------------
% 1.31/0.54  fof(f100,plain,(
% 1.31/0.54    v1_xboole_0(sK6) | ~spl7_6),
% 1.31/0.54    inference(avatar_component_clause,[],[f98])).
% 1.31/0.54  fof(f98,plain,(
% 1.31/0.54    spl7_6 <=> v1_xboole_0(sK6)),
% 1.31/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 1.31/0.54  fof(f296,plain,(
% 1.31/0.54    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK4) | (spl7_1 | ~spl7_4 | ~spl7_5)),
% 1.31/0.54    inference(forward_demodulation,[],[f67,f270])).
% 1.31/0.54  fof(f67,plain,(
% 1.31/0.54    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5) | spl7_1),
% 1.31/0.54    inference(avatar_component_clause,[],[f65])).
% 1.31/0.54  fof(f65,plain,(
% 1.31/0.54    spl7_1 <=> r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)),
% 1.31/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.31/0.54  fof(f293,plain,(
% 1.31/0.54    ~spl7_1 | spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6),
% 1.31/0.54    inference(avatar_contradiction_clause,[],[f292])).
% 1.31/0.54  fof(f292,plain,(
% 1.31/0.54    $false | (~spl7_1 | spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6)),
% 1.31/0.54    inference(subsumption_resolution,[],[f291,f288])).
% 1.31/0.54  fof(f288,plain,(
% 1.31/0.54    ~r2_funct_2(u1_struct_0(sK2),sK4,k2_tmap_1(sK0,sK1,sK4,sK2),sK4) | (spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5)),
% 1.31/0.54    inference(forward_demodulation,[],[f283,f268])).
% 1.31/0.54  fof(f283,plain,(
% 1.31/0.54    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK4) | (spl7_2 | ~spl7_4 | ~spl7_5)),
% 1.31/0.54    inference(superposition,[],[f71,f270])).
% 1.31/0.54  fof(f71,plain,(
% 1.31/0.54    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | spl7_2),
% 1.31/0.54    inference(avatar_component_clause,[],[f69])).
% 1.31/0.54  fof(f291,plain,(
% 1.31/0.54    r2_funct_2(u1_struct_0(sK2),sK4,k2_tmap_1(sK0,sK1,sK4,sK2),sK4) | (~spl7_1 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6)),
% 1.31/0.54    inference(forward_demodulation,[],[f290,f268])).
% 1.31/0.54  fof(f290,plain,(
% 1.31/0.54    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK4) | (~spl7_1 | ~spl7_4 | ~spl7_5 | ~spl7_6)),
% 1.31/0.54    inference(forward_demodulation,[],[f289,f226])).
% 1.31/0.54  fof(f289,plain,(
% 1.31/0.54    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK4) | (~spl7_1 | ~spl7_4 | ~spl7_5 | ~spl7_6)),
% 1.31/0.54    inference(forward_demodulation,[],[f285,f271])).
% 1.31/0.54  fof(f285,plain,(
% 1.31/0.54    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK6),sK4) | (~spl7_1 | ~spl7_4 | ~spl7_5)),
% 1.31/0.54    inference(superposition,[],[f235,f270])).
% 1.31/0.54  fof(f235,plain,(
% 1.31/0.54    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK6),sK5) | ~spl7_1),
% 1.31/0.54    inference(forward_demodulation,[],[f66,f51])).
% 1.31/0.54  fof(f66,plain,(
% 1.31/0.54    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5) | ~spl7_1),
% 1.31/0.54    inference(avatar_component_clause,[],[f65])).
% 1.31/0.54  fof(f234,plain,(
% 1.31/0.54    ~spl7_1 | spl7_2 | spl7_3),
% 1.31/0.54    inference(avatar_contradiction_clause,[],[f233])).
% 1.31/0.54  fof(f233,plain,(
% 1.31/0.54    $false | (~spl7_1 | spl7_2 | spl7_3)),
% 1.31/0.54    inference(subsumption_resolution,[],[f232,f71])).
% 1.31/0.54  fof(f232,plain,(
% 1.31/0.54    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | (~spl7_1 | spl7_3)),
% 1.31/0.54    inference(forward_demodulation,[],[f231,f226])).
% 1.31/0.54  fof(f231,plain,(
% 1.31/0.54    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5) | (~spl7_1 | spl7_3)),
% 1.31/0.54    inference(forward_demodulation,[],[f230,f51])).
% 1.31/0.54  fof(f230,plain,(
% 1.31/0.54    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) | (~spl7_1 | spl7_3)),
% 1.31/0.54    inference(forward_demodulation,[],[f66,f126])).
% 1.31/0.54  fof(f126,plain,(
% 1.31/0.54    sK4 = sK6 | spl7_3),
% 1.31/0.54    inference(subsumption_resolution,[],[f125,f75])).
% 1.31/0.54  fof(f75,plain,(
% 1.31/0.54    v1_funct_2(sK6,u1_struct_0(sK0),u1_struct_0(sK1))),
% 1.31/0.54    inference(forward_demodulation,[],[f49,f51])).
% 1.31/0.54  fof(f49,plain,(
% 1.31/0.54    v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK1))),
% 1.31/0.54    inference(cnf_transformation,[],[f30])).
% 1.31/0.54  fof(f125,plain,(
% 1.31/0.54    ~v1_funct_2(sK6,u1_struct_0(sK0),u1_struct_0(sK1)) | sK4 = sK6 | spl7_3),
% 1.31/0.54    inference(forward_demodulation,[],[f124,f51])).
% 1.31/0.54  fof(f124,plain,(
% 1.31/0.54    sK4 = sK6 | ~v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK1)) | spl7_3),
% 1.31/0.54    inference(subsumption_resolution,[],[f123,f74])).
% 1.31/0.54  fof(f74,plain,(
% 1.31/0.54    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 1.31/0.54    inference(forward_demodulation,[],[f50,f51])).
% 1.31/0.54  fof(f50,plain,(
% 1.31/0.54    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 1.31/0.54    inference(cnf_transformation,[],[f30])).
% 1.31/0.54  fof(f123,plain,(
% 1.31/0.54    ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | sK4 = sK6 | ~v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK1)) | spl7_3),
% 1.31/0.54    inference(forward_demodulation,[],[f122,f51])).
% 1.31/0.54  fof(f122,plain,(
% 1.31/0.54    sK4 = sK6 | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK1)) | spl7_3),
% 1.31/0.54    inference(subsumption_resolution,[],[f121,f86])).
% 1.31/0.54  fof(f86,plain,(
% 1.31/0.54    ~v1_xboole_0(u1_struct_0(sK1)) | spl7_3),
% 1.31/0.54    inference(avatar_component_clause,[],[f84])).
% 1.31/0.54  fof(f121,plain,(
% 1.31/0.54    sK4 = sK6 | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK1))),
% 1.31/0.54    inference(subsumption_resolution,[],[f120,f42])).
% 1.31/0.54  fof(f120,plain,(
% 1.31/0.54    sK4 = sK6 | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | v1_xboole_0(u1_struct_0(sK1))),
% 1.31/0.54    inference(subsumption_resolution,[],[f119,f43])).
% 1.31/0.54  fof(f119,plain,(
% 1.31/0.54    sK4 = sK6 | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | v1_xboole_0(u1_struct_0(sK1))),
% 1.31/0.54    inference(subsumption_resolution,[],[f118,f44])).
% 1.31/0.54  fof(f118,plain,(
% 1.31/0.54    sK4 = sK6 | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | v1_xboole_0(u1_struct_0(sK1))),
% 1.31/0.54    inference(subsumption_resolution,[],[f117,f48])).
% 1.31/0.54  fof(f48,plain,(
% 1.31/0.54    v1_funct_1(sK6)),
% 1.31/0.54    inference(cnf_transformation,[],[f30])).
% 1.31/0.54  fof(f117,plain,(
% 1.31/0.54    sK4 = sK6 | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK6) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | v1_xboole_0(u1_struct_0(sK1))),
% 1.31/0.54    inference(duplicate_literal_removal,[],[f116])).
% 1.31/0.54  fof(f116,plain,(
% 1.31/0.54    sK4 = sK6 | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK6) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | v1_xboole_0(u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK1))),
% 1.31/0.54    inference(resolution,[],[f60,f52])).
% 1.31/0.54  fof(f52,plain,(
% 1.31/0.54    r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6)),
% 1.31/0.54    inference(cnf_transformation,[],[f30])).
% 1.31/0.54  fof(f60,plain,(
% 1.31/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (~r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 = X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 1.31/0.54    inference(cnf_transformation,[],[f31])).
% 1.31/0.54  fof(f31,plain,(
% 1.31/0.54    ! [X0,X1,X2,X3,X4,X5] : (((r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 != X5) & (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 1.31/0.54    inference(nnf_transformation,[],[f20])).
% 1.31/0.54  fof(f20,plain,(
% 1.31/0.54    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 1.31/0.54    inference(flattening,[],[f19])).
% 1.31/0.54  fof(f19,plain,(
% 1.31/0.54    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 1.31/0.54    inference(ennf_transformation,[],[f3])).
% 1.31/0.54  fof(f3,axiom,(
% 1.31/0.54    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => (r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5))),
% 1.31/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_funct_2)).
% 1.31/0.54  fof(f229,plain,(
% 1.31/0.54    spl7_1 | ~spl7_2 | spl7_3),
% 1.31/0.54    inference(avatar_contradiction_clause,[],[f228])).
% 1.31/0.54  fof(f228,plain,(
% 1.31/0.54    $false | (spl7_1 | ~spl7_2 | spl7_3)),
% 1.31/0.54    inference(subsumption_resolution,[],[f227,f70])).
% 1.31/0.54  fof(f227,plain,(
% 1.31/0.54    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | (spl7_1 | spl7_3)),
% 1.31/0.54    inference(superposition,[],[f143,f226])).
% 1.31/0.54  fof(f143,plain,(
% 1.31/0.54    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5) | (spl7_1 | spl7_3)),
% 1.31/0.54    inference(superposition,[],[f78,f126])).
% 1.31/0.54  fof(f78,plain,(
% 1.31/0.54    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK6),sK5) | spl7_1),
% 1.31/0.54    inference(forward_demodulation,[],[f67,f51])).
% 1.31/0.54  fof(f101,plain,(
% 1.31/0.54    ~spl7_3 | spl7_6),
% 1.31/0.54    inference(avatar_split_clause,[],[f82,f98,f84])).
% 1.31/0.54  fof(f82,plain,(
% 1.31/0.54    v1_xboole_0(sK6) | ~v1_xboole_0(u1_struct_0(sK1))),
% 1.31/0.54    inference(resolution,[],[f58,f74])).
% 1.31/0.54  fof(f58,plain,(
% 1.31/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_xboole_0(X2) | ~v1_xboole_0(X0)) )),
% 1.31/0.54    inference(cnf_transformation,[],[f17])).
% 1.31/0.54  fof(f17,plain,(
% 1.31/0.54    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 1.31/0.54    inference(ennf_transformation,[],[f2])).
% 1.31/0.54  fof(f2,axiom,(
% 1.31/0.54    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 1.31/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).
% 1.31/0.54  fof(f96,plain,(
% 1.31/0.54    ~spl7_3 | spl7_5),
% 1.31/0.54    inference(avatar_split_clause,[],[f81,f93,f84])).
% 1.31/0.54  fof(f81,plain,(
% 1.31/0.54    v1_xboole_0(sK5) | ~v1_xboole_0(u1_struct_0(sK1))),
% 1.31/0.54    inference(resolution,[],[f58,f47])).
% 1.31/0.54  fof(f47,plain,(
% 1.31/0.54    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 1.31/0.54    inference(cnf_transformation,[],[f30])).
% 1.31/0.54  fof(f91,plain,(
% 1.31/0.54    ~spl7_3 | spl7_4),
% 1.31/0.54    inference(avatar_split_clause,[],[f80,f88,f84])).
% 1.31/0.54  fof(f80,plain,(
% 1.31/0.54    v1_xboole_0(sK4) | ~v1_xboole_0(u1_struct_0(sK1))),
% 1.31/0.54    inference(resolution,[],[f58,f44])).
% 1.31/0.54  fof(f73,plain,(
% 1.31/0.54    spl7_1 | spl7_2),
% 1.31/0.54    inference(avatar_split_clause,[],[f53,f69,f65])).
% 1.31/0.54  fof(f53,plain,(
% 1.31/0.54    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)),
% 1.31/0.54    inference(cnf_transformation,[],[f30])).
% 1.31/0.54  fof(f72,plain,(
% 1.31/0.54    ~spl7_1 | ~spl7_2),
% 1.31/0.54    inference(avatar_split_clause,[],[f54,f69,f65])).
% 1.31/0.54  fof(f54,plain,(
% 1.31/0.54    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)),
% 1.31/0.54    inference(cnf_transformation,[],[f30])).
% 1.31/0.54  % SZS output end Proof for theBenchmark
% 1.31/0.54  % (3299)------------------------------
% 1.31/0.54  % (3299)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.54  % (3299)Termination reason: Refutation
% 1.31/0.54  
% 1.31/0.54  % (3299)Memory used [KB]: 10874
% 1.31/0.54  % (3299)Time elapsed: 0.110 s
% 1.31/0.54  % (3299)------------------------------
% 1.31/0.54  % (3299)------------------------------
% 1.31/0.54  % (3288)Success in time 0.179 s
%------------------------------------------------------------------------------
