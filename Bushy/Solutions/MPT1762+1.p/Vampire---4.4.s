%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tmap_1__t73_tmap_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:20 EDT 2019

% Result     : Theorem 0.76s
% Output     : Refutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :  202 ( 980 expanded)
%              Number of leaves         :   35 ( 490 expanded)
%              Depth                    :   23
%              Number of atoms          : 1147 (17746 expanded)
%              Number of equality atoms :  121 (1172 expanded)
%              Maximal formula depth    :   20 (   7 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4773,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f235,f305,f311,f357,f364,f397,f446,f450,f1113,f1134,f1211,f1423,f4772])).

fof(f4772,plain,
    ( spl13_1
    | spl13_3
    | ~ spl13_10
    | spl13_29
    | ~ spl13_98
    | ~ spl13_110
    | spl13_113
    | ~ spl13_126 ),
    inference(avatar_contradiction_clause,[],[f4771])).

fof(f4771,plain,
    ( $false
    | ~ spl13_1
    | ~ spl13_3
    | ~ spl13_10
    | ~ spl13_29
    | ~ spl13_98
    | ~ spl13_110
    | ~ spl13_113
    | ~ spl13_126 ),
    inference(subsumption_resolution,[],[f4698,f4704])).

fof(f4704,plain,
    ( k1_funct_1(sK4,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) = k1_funct_1(sK5,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5))
    | ~ spl13_10
    | ~ spl13_110
    | ~ spl13_126 ),
    inference(forward_demodulation,[],[f1515,f1230])).

fof(f1230,plain,
    ( k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) = k1_funct_1(sK4,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5))
    | ~ spl13_10
    | ~ spl13_110 ),
    inference(resolution,[],[f1106,f234])).

fof(f234,plain,
    ( ! [X11] :
        ( ~ m1_subset_1(X11,u1_struct_0(sK3))
        | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X11) = k1_funct_1(sK4,X11) )
    | ~ spl13_10 ),
    inference(avatar_component_clause,[],[f233])).

fof(f233,plain,
    ( spl13_10
  <=> ! [X11] :
        ( ~ m1_subset_1(X11,u1_struct_0(sK3))
        | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X11) = k1_funct_1(sK4,X11) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_10])])).

fof(f1106,plain,
    ( m1_subset_1(sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5),u1_struct_0(sK3))
    | ~ spl13_110 ),
    inference(avatar_component_clause,[],[f1105])).

fof(f1105,plain,
    ( spl13_110
  <=> m1_subset_1(sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_110])])).

fof(f1515,plain,
    ( k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) = k1_funct_1(sK5,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5))
    | ~ spl13_110
    | ~ spl13_126 ),
    inference(subsumption_resolution,[],[f1510,f1106])).

fof(f1510,plain,
    ( k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) = k1_funct_1(sK5,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5))
    | ~ m1_subset_1(sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5),u1_struct_0(sK3))
    | ~ spl13_126 ),
    inference(resolution,[],[f1210,f115])).

fof(f115,plain,(
    ! [X6] :
      ( ~ r2_hidden(X6,u1_struct_0(sK2))
      | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X6) = k1_funct_1(sK5,X6)
      | ~ m1_subset_1(X6,u1_struct_0(sK3)) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f86,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)
    & ! [X6] :
        ( k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X6) = k1_funct_1(sK5,X6)
        | ~ r2_hidden(X6,u1_struct_0(sK2))
        | ~ m1_subset_1(X6,u1_struct_0(sK3)) )
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    & v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
    & v1_funct_1(sK5)
    & m1_pre_topc(sK2,sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f41,f85,f84,f83,f82,f81,f80])).

fof(f80,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)
                            & ! [X6] :
                                ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6)
                                | ~ r2_hidden(X6,u1_struct_0(X2))
                                | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                            & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                            & v1_funct_1(X5) )
                        & m1_pre_topc(X2,X3)
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
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
                          ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK0,X1,X3,X2,X4),X5)
                          & ! [X6] :
                              ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6)
                              | ~ r2_hidden(X6,u1_struct_0(X2))
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
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

fof(f81,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)
                          & ! [X6] :
                              ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6)
                              | ~ r2_hidden(X6,u1_struct_0(X2))
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k3_tmap_1(X0,sK1,X3,X2,X4),X5)
                        & ! [X6] :
                            ( k3_funct_2(u1_struct_0(X3),u1_struct_0(sK1),X4,X6) = k1_funct_1(X5,X6)
                            | ~ r2_hidden(X6,u1_struct_0(X2))
                            | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1))))
                        & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(sK1))
                        & v1_funct_1(X5) )
                    & m1_pre_topc(X2,X3)
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                    & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,X0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK1)
        & v2_pre_topc(sK1)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)
                      & ! [X6] :
                          ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6)
                          | ~ r2_hidden(X6,u1_struct_0(X2))
                          | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                      & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X5) )
                  & m1_pre_topc(X2,X3)
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                  & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                  & v1_funct_1(X4) )
              & m1_pre_topc(X3,X0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,sK2,X4),X5)
                    & ! [X6] :
                        ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6)
                        | ~ r2_hidden(X6,u1_struct_0(sK2))
                        | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
                    & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(X1))
                    & v1_funct_1(X5) )
                & m1_pre_topc(sK2,X3)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK2,X0)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)
                  & ! [X6] :
                      ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6)
                      | ~ r2_hidden(X6,u1_struct_0(X2))
                      | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                  & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                  & v1_funct_1(X5) )
              & m1_pre_topc(X2,X3)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
              & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,X0)
          & ~ v2_struct_0(X3) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,sK3,X2,X4),X5)
                & ! [X6] :
                    ( k3_funct_2(u1_struct_0(sK3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6)
                    | ~ r2_hidden(X6,u1_struct_0(X2))
                    | ~ m1_subset_1(X6,u1_struct_0(sK3)) )
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                & v1_funct_1(X5) )
            & m1_pre_topc(X2,sK3)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
            & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X1))
            & v1_funct_1(X4) )
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)
              & ! [X6] :
                  ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6)
                  | ~ r2_hidden(X6,u1_struct_0(X2))
                  | ~ m1_subset_1(X6,u1_struct_0(X3)) )
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
              & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
              & v1_funct_1(X5) )
          & m1_pre_topc(X2,X3)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
          & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
          & v1_funct_1(X4) )
     => ( ? [X5] :
            ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,sK4),X5)
            & ! [X6] :
                ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),sK4,X6) = k1_funct_1(X5,X6)
                | ~ r2_hidden(X6,u1_struct_0(X2))
                | ~ m1_subset_1(X6,u1_struct_0(X3)) )
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
            & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
            & v1_funct_1(X5) )
        & m1_pre_topc(X2,X3)
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f85,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)
          & ! [X6] :
              ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6)
              | ~ r2_hidden(X6,u1_struct_0(X2))
              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
          & v1_funct_1(X5) )
     => ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),sK5)
        & ! [X6] :
            ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(sK5,X6)
            | ~ r2_hidden(X6,u1_struct_0(X2))
            | ~ m1_subset_1(X6,u1_struct_0(X3)) )
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v1_funct_2(sK5,u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)
                          & ! [X6] :
                              ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6)
                              | ~ r2_hidden(X6,u1_struct_0(X2))
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
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
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)
                          & ! [X6] :
                              ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6)
                              | ~ r2_hidden(X6,u1_struct_0(X2))
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
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
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
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
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ( m1_pre_topc(X2,X3)
                         => ! [X5] :
                              ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                                & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                                & v1_funct_1(X5) )
                             => ( ! [X6] :
                                    ( m1_subset_1(X6,u1_struct_0(X3))
                                   => ( r2_hidden(X6,u1_struct_0(X2))
                                     => k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6) ) )
                               => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
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
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X2,X3)
                       => ! [X5] :
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                              & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                              & v1_funct_1(X5) )
                           => ( ! [X6] :
                                  ( m1_subset_1(X6,u1_struct_0(X3))
                                 => ( r2_hidden(X6,u1_struct_0(X2))
                                   => k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6) ) )
                             => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t73_tmap_1.p',t73_tmap_1)).

fof(f1210,plain,
    ( r2_hidden(sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5),u1_struct_0(sK2))
    | ~ spl13_126 ),
    inference(avatar_component_clause,[],[f1209])).

fof(f1209,plain,
    ( spl13_126
  <=> r2_hidden(sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_126])])).

fof(f4698,plain,
    ( k1_funct_1(sK4,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) != k1_funct_1(sK5,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5))
    | ~ spl13_1
    | ~ spl13_3
    | ~ spl13_10
    | ~ spl13_29
    | ~ spl13_98
    | ~ spl13_110
    | ~ spl13_113 ),
    inference(subsumption_resolution,[],[f4697,f1109])).

fof(f1109,plain,
    ( k7_relat_1(sK4,u1_struct_0(sK2)) != sK5
    | ~ spl13_113 ),
    inference(avatar_component_clause,[],[f1108])).

fof(f1108,plain,
    ( spl13_113
  <=> k7_relat_1(sK4,u1_struct_0(sK2)) != sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_113])])).

fof(f4697,plain,
    ( k7_relat_1(sK4,u1_struct_0(sK2)) = sK5
    | k1_funct_1(sK4,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) != k1_funct_1(sK5,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5))
    | ~ spl13_1
    | ~ spl13_3
    | ~ spl13_10
    | ~ spl13_29
    | ~ spl13_98
    | ~ spl13_110 ),
    inference(forward_demodulation,[],[f4696,f240])).

fof(f240,plain,(
    ! [X14] : k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X14) = k7_relat_1(sK4,X14) ),
    inference(subsumption_resolution,[],[f176,f108])).

fof(f108,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f86])).

fof(f176,plain,(
    ! [X14] :
      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X14) = k7_relat_1(sK4,X14)
      | ~ v1_funct_1(sK4) ) ),
    inference(resolution,[],[f110,f144])).

fof(f144,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f74])).

fof(f74,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t73_tmap_1.p',redefinition_k2_partfun1)).

fof(f110,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f86])).

fof(f4696,plain,
    ( k1_funct_1(sK4,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) != k1_funct_1(sK5,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5))
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = sK5
    | ~ spl13_1
    | ~ spl13_3
    | ~ spl13_10
    | ~ spl13_29
    | ~ spl13_98
    | ~ spl13_110 ),
    inference(subsumption_resolution,[],[f4695,f210])).

fof(f210,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK3))
    | ~ spl13_3 ),
    inference(avatar_component_clause,[],[f209])).

fof(f209,plain,
    ( spl13_3
  <=> ~ v1_xboole_0(u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_3])])).

fof(f4695,plain,
    ( k1_funct_1(sK4,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) != k1_funct_1(sK5,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5))
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = sK5
    | v1_xboole_0(u1_struct_0(sK3))
    | ~ spl13_1
    | ~ spl13_10
    | ~ spl13_29
    | ~ spl13_98
    | ~ spl13_110 ),
    inference(subsumption_resolution,[],[f4694,f204])).

fof(f204,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ spl13_1 ),
    inference(avatar_component_clause,[],[f203])).

fof(f203,plain,
    ( spl13_1
  <=> ~ v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).

fof(f4694,plain,
    ( k1_funct_1(sK4,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) != k1_funct_1(sK5,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5))
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = sK5
    | v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK3))
    | ~ spl13_10
    | ~ spl13_29
    | ~ spl13_98
    | ~ spl13_110 ),
    inference(subsumption_resolution,[],[f4693,f108])).

fof(f4693,plain,
    ( k1_funct_1(sK4,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) != k1_funct_1(sK5,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5))
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = sK5
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK3))
    | ~ spl13_10
    | ~ spl13_29
    | ~ spl13_98
    | ~ spl13_110 ),
    inference(subsumption_resolution,[],[f4692,f109])).

fof(f109,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f86])).

fof(f4692,plain,
    ( k1_funct_1(sK4,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) != k1_funct_1(sK5,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5))
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = sK5
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK3))
    | ~ spl13_10
    | ~ spl13_29
    | ~ spl13_98
    | ~ spl13_110 ),
    inference(subsumption_resolution,[],[f4691,f110])).

fof(f4691,plain,
    ( k1_funct_1(sK4,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) != k1_funct_1(sK5,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5))
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = sK5
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK3))
    | ~ spl13_10
    | ~ spl13_29
    | ~ spl13_98
    | ~ spl13_110 ),
    inference(subsumption_resolution,[],[f4690,f350])).

fof(f350,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK2))
    | ~ spl13_29 ),
    inference(avatar_component_clause,[],[f349])).

fof(f349,plain,
    ( spl13_29
  <=> ~ v1_xboole_0(u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_29])])).

fof(f4690,plain,
    ( k1_funct_1(sK4,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) != k1_funct_1(sK5,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5))
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = sK5
    | v1_xboole_0(u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK3))
    | ~ spl13_10
    | ~ spl13_98
    | ~ spl13_110 ),
    inference(subsumption_resolution,[],[f4689,f1064])).

fof(f1064,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl13_98 ),
    inference(avatar_component_clause,[],[f1063])).

fof(f1063,plain,
    ( spl13_98
  <=> m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_98])])).

fof(f4689,plain,
    ( k1_funct_1(sK4,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) != k1_funct_1(sK5,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5))
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = sK5
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_xboole_0(u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK3))
    | ~ spl13_10
    | ~ spl13_110 ),
    inference(subsumption_resolution,[],[f4688,f112])).

fof(f112,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f86])).

fof(f4688,plain,
    ( k1_funct_1(sK4,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) != k1_funct_1(sK5,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5))
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = sK5
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_xboole_0(u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK3))
    | ~ spl13_10
    | ~ spl13_110 ),
    inference(subsumption_resolution,[],[f4687,f113])).

fof(f113,plain,(
    v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f86])).

fof(f4687,plain,
    ( k1_funct_1(sK4,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) != k1_funct_1(sK5,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5))
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = sK5
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_xboole_0(u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK3))
    | ~ spl13_10
    | ~ spl13_110 ),
    inference(subsumption_resolution,[],[f4683,f114])).

fof(f114,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f86])).

fof(f4683,plain,
    ( k1_funct_1(sK4,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) != k1_funct_1(sK5,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5))
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = sK5
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_xboole_0(u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK3))
    | ~ spl13_10
    | ~ spl13_110 ),
    inference(superposition,[],[f120,f1230])).

fof(f120,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,sK6(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK6(X0,X1,X2,X3,X4))
      | k2_partfun1(X0,X1,X2,X3) = X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X4,X3,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f88])).

fof(f88,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k2_partfun1(X0,X1,X2,X3) = X4
                      | ( k3_funct_2(X0,X1,X2,sK6(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK6(X0,X1,X2,X3,X4))
                        & r2_hidden(sK6(X0,X1,X2,X3,X4),X3)
                        & m1_subset_1(sK6(X0,X1,X2,X3,X4),X0) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                      | ~ v1_funct_2(X4,X3,X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
                  | v1_xboole_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X2,X0,X1)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f43,f87])).

fof(f87,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( k3_funct_2(X0,X1,X2,X5) != k1_funct_1(X4,X5)
          & r2_hidden(X5,X3)
          & m1_subset_1(X5,X0) )
     => ( k3_funct_2(X0,X1,X2,sK6(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK6(X0,X1,X2,X3,X4))
        & r2_hidden(sK6(X0,X1,X2,X3,X4),X3)
        & m1_subset_1(sK6(X0,X1,X2,X3,X4),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k2_partfun1(X0,X1,X2,X3) = X4
                      | ? [X5] :
                          ( k3_funct_2(X0,X1,X2,X5) != k1_funct_1(X4,X5)
                          & r2_hidden(X5,X3)
                          & m1_subset_1(X5,X0) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                      | ~ v1_funct_2(X4,X3,X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
                  | v1_xboole_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X2,X0,X1)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k2_partfun1(X0,X1,X2,X3) = X4
                      | ? [X5] :
                          ( k3_funct_2(X0,X1,X2,X5) != k1_funct_1(X4,X5)
                          & r2_hidden(X5,X3)
                          & m1_subset_1(X5,X0) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                      | ~ v1_funct_2(X4,X3,X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
                  | v1_xboole_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X2,X0,X1)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X2,X0,X1)
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(X0))
                    & ~ v1_xboole_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                        & v1_funct_2(X4,X3,X1)
                        & v1_funct_1(X4) )
                     => ( ! [X5] :
                            ( m1_subset_1(X5,X0)
                           => ( r2_hidden(X5,X3)
                             => k3_funct_2(X0,X1,X2,X5) = k1_funct_1(X4,X5) ) )
                       => k2_partfun1(X0,X1,X2,X3) = X4 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t73_tmap_1.p',t173_funct_2)).

fof(f1423,plain,
    ( ~ spl13_40
    | ~ spl13_112 ),
    inference(avatar_contradiction_clause,[],[f1422])).

fof(f1422,plain,
    ( $false
    | ~ spl13_40
    | ~ spl13_112 ),
    inference(subsumption_resolution,[],[f1419,f396])).

fof(f396,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,sK5)
    | ~ spl13_40 ),
    inference(avatar_component_clause,[],[f395])).

fof(f395,plain,
    ( spl13_40
  <=> r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_40])])).

fof(f1419,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,sK5)
    | ~ spl13_112 ),
    inference(backward_demodulation,[],[f1250,f116])).

fof(f116,plain,(
    ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
    inference(cnf_transformation,[],[f86])).

fof(f1250,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = sK5
    | ~ spl13_112 ),
    inference(forward_demodulation,[],[f1249,f1112])).

fof(f1112,plain,
    ( k7_relat_1(sK4,u1_struct_0(sK2)) = sK5
    | ~ spl13_112 ),
    inference(avatar_component_clause,[],[f1111])).

fof(f1111,plain,
    ( spl13_112
  <=> k7_relat_1(sK4,u1_struct_0(sK2)) = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_112])])).

fof(f1249,plain,(
    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k7_relat_1(sK4,u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f1234,f105])).

fof(f105,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f86])).

fof(f1234,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k7_relat_1(sK4,u1_struct_0(sK2)) ),
    inference(resolution,[],[f808,f111])).

fof(f111,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f86])).

fof(f808,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK3)
      | ~ m1_pre_topc(X0,sK0)
      | k3_tmap_1(sK0,sK1,sK3,X0,sK4) = k7_relat_1(sK4,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f807,f98])).

fof(f98,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f86])).

fof(f807,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK3)
      | ~ m1_pre_topc(X0,sK0)
      | k3_tmap_1(sK0,sK1,sK3,X0,sK4) = k7_relat_1(sK4,u1_struct_0(X0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f806,f99])).

fof(f99,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f86])).

fof(f806,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK3)
      | ~ m1_pre_topc(X0,sK0)
      | k3_tmap_1(sK0,sK1,sK3,X0,sK4) = k7_relat_1(sK4,u1_struct_0(X0))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f805,f100])).

fof(f100,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f86])).

fof(f805,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK3)
      | ~ m1_pre_topc(X0,sK0)
      | k3_tmap_1(sK0,sK1,sK3,X0,sK4) = k7_relat_1(sK4,u1_struct_0(X0))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f793,f107])).

fof(f107,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f86])).

fof(f793,plain,(
    ! [X4,X5] :
      ( ~ m1_pre_topc(sK3,X5)
      | ~ m1_pre_topc(X4,sK3)
      | ~ m1_pre_topc(X4,X5)
      | k3_tmap_1(X5,sK1,sK3,X4,sK4) = k7_relat_1(sK4,u1_struct_0(X4))
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5) ) ),
    inference(forward_demodulation,[],[f199,f240])).

fof(f199,plain,(
    ! [X4,X5] :
      ( ~ m1_pre_topc(X4,sK3)
      | k3_tmap_1(X5,sK1,sK3,X4,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X4))
      | ~ m1_pre_topc(X4,X5)
      | ~ m1_pre_topc(sK3,X5)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5) ) ),
    inference(subsumption_resolution,[],[f198,f101])).

fof(f101,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f86])).

fof(f198,plain,(
    ! [X4,X5] :
      ( ~ m1_pre_topc(X4,sK3)
      | k3_tmap_1(X5,sK1,sK3,X4,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X4))
      | ~ m1_pre_topc(X4,X5)
      | ~ m1_pre_topc(sK3,X5)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5) ) ),
    inference(subsumption_resolution,[],[f197,f102])).

fof(f102,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f86])).

fof(f197,plain,(
    ! [X4,X5] :
      ( ~ m1_pre_topc(X4,sK3)
      | k3_tmap_1(X5,sK1,sK3,X4,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X4))
      | ~ m1_pre_topc(X4,X5)
      | ~ m1_pre_topc(sK3,X5)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5) ) ),
    inference(subsumption_resolution,[],[f196,f103])).

fof(f103,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f86])).

fof(f196,plain,(
    ! [X4,X5] :
      ( ~ m1_pre_topc(X4,sK3)
      | k3_tmap_1(X5,sK1,sK3,X4,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X4))
      | ~ m1_pre_topc(X4,X5)
      | ~ m1_pre_topc(sK3,X5)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5) ) ),
    inference(subsumption_resolution,[],[f195,f108])).

fof(f195,plain,(
    ! [X4,X5] :
      ( ~ m1_pre_topc(X4,sK3)
      | k3_tmap_1(X5,sK1,sK3,X4,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X4))
      | ~ v1_funct_1(sK4)
      | ~ m1_pre_topc(X4,X5)
      | ~ m1_pre_topc(sK3,X5)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5) ) ),
    inference(subsumption_resolution,[],[f169,f109])).

fof(f169,plain,(
    ! [X4,X5] :
      ( ~ m1_pre_topc(X4,sK3)
      | k3_tmap_1(X5,sK1,sK3,X4,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X4))
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ v1_funct_1(sK4)
      | ~ m1_pre_topc(X4,X5)
      | ~ m1_pre_topc(sK3,X5)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5) ) ),
    inference(resolution,[],[f110,f128])).

fof(f128,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ m1_pre_topc(X3,X2)
      | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
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
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
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
    inference(flattening,[],[f52])).

fof(f52,plain,(
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
              ( m1_pre_topc(X2,X0)
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X3,X2)
                       => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t73_tmap_1.p',d5_tmap_1)).

fof(f1211,plain,
    ( spl13_126
    | spl13_112
    | spl13_3
    | ~ spl13_32
    | ~ spl13_98 ),
    inference(avatar_split_clause,[],[f1204,f1063,f362,f209,f1111,f1209])).

fof(f362,plain,
    ( spl13_32
  <=> ! [X9,X8] :
        ( r2_hidden(sK6(X8,u1_struct_0(sK1),X9,u1_struct_0(sK2),sK5),u1_struct_0(sK2))
        | v1_xboole_0(X8)
        | ~ v1_funct_1(X9)
        | ~ v1_funct_2(X9,X8,u1_struct_0(sK1))
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X8,u1_struct_0(sK1))))
        | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X8))
        | k2_partfun1(X8,u1_struct_0(sK1),X9,u1_struct_0(sK2)) = sK5 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_32])])).

fof(f1204,plain,
    ( k7_relat_1(sK4,u1_struct_0(sK2)) = sK5
    | r2_hidden(sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5),u1_struct_0(sK2))
    | ~ spl13_3
    | ~ spl13_32
    | ~ spl13_98 ),
    inference(forward_demodulation,[],[f1203,f240])).

fof(f1203,plain,
    ( r2_hidden(sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5),u1_struct_0(sK2))
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = sK5
    | ~ spl13_3
    | ~ spl13_32
    | ~ spl13_98 ),
    inference(subsumption_resolution,[],[f1202,f1064])).

fof(f1202,plain,
    ( r2_hidden(sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5),u1_struct_0(sK2))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = sK5
    | ~ spl13_3
    | ~ spl13_32 ),
    inference(subsumption_resolution,[],[f1201,f109])).

fof(f1201,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | r2_hidden(sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5),u1_struct_0(sK2))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = sK5
    | ~ spl13_3
    | ~ spl13_32 ),
    inference(subsumption_resolution,[],[f1200,f108])).

fof(f1200,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | r2_hidden(sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5),u1_struct_0(sK2))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = sK5
    | ~ spl13_3
    | ~ spl13_32 ),
    inference(subsumption_resolution,[],[f1187,f210])).

fof(f1187,plain,
    ( v1_xboole_0(u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | r2_hidden(sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5),u1_struct_0(sK2))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = sK5
    | ~ spl13_32 ),
    inference(resolution,[],[f363,f110])).

fof(f363,plain,
    ( ! [X8,X9] :
        ( ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X8,u1_struct_0(sK1))))
        | v1_xboole_0(X8)
        | ~ v1_funct_1(X9)
        | ~ v1_funct_2(X9,X8,u1_struct_0(sK1))
        | r2_hidden(sK6(X8,u1_struct_0(sK1),X9,u1_struct_0(sK2),sK5),u1_struct_0(sK2))
        | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X8))
        | k2_partfun1(X8,u1_struct_0(sK1),X9,u1_struct_0(sK2)) = sK5 )
    | ~ spl13_32 ),
    inference(avatar_component_clause,[],[f362])).

fof(f1134,plain,(
    spl13_99 ),
    inference(avatar_contradiction_clause,[],[f1133])).

fof(f1133,plain,
    ( $false
    | ~ spl13_99 ),
    inference(subsumption_resolution,[],[f1132,f163])).

fof(f163,plain,(
    l1_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f162,f100])).

fof(f162,plain,
    ( l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f107,f123])).

fof(f123,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t73_tmap_1.p',dt_m1_pre_topc)).

fof(f1132,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ spl13_99 ),
    inference(subsumption_resolution,[],[f1131,f111])).

fof(f1131,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | ~ l1_pre_topc(sK3)
    | ~ spl13_99 ),
    inference(resolution,[],[f1067,f124])).

fof(f124,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t73_tmap_1.p',t1_tsep_1)).

fof(f1067,plain,
    ( ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl13_99 ),
    inference(avatar_component_clause,[],[f1066])).

fof(f1066,plain,
    ( spl13_99
  <=> ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_99])])).

fof(f1113,plain,
    ( ~ spl13_99
    | spl13_110
    | spl13_112
    | spl13_3
    | ~ spl13_30 ),
    inference(avatar_split_clause,[],[f1100,f355,f209,f1111,f1105,f1066])).

fof(f355,plain,
    ( spl13_30
  <=> ! [X7,X6] :
        ( m1_subset_1(sK6(X6,u1_struct_0(sK1),X7,u1_struct_0(sK2),sK5),X6)
        | v1_xboole_0(X6)
        | ~ v1_funct_1(X7)
        | ~ v1_funct_2(X7,X6,u1_struct_0(sK1))
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X6,u1_struct_0(sK1))))
        | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X6))
        | k2_partfun1(X6,u1_struct_0(sK1),X7,u1_struct_0(sK2)) = sK5 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_30])])).

fof(f1100,plain,
    ( k7_relat_1(sK4,u1_struct_0(sK2)) = sK5
    | m1_subset_1(sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl13_3
    | ~ spl13_30 ),
    inference(forward_demodulation,[],[f1099,f240])).

fof(f1099,plain,
    ( m1_subset_1(sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = sK5
    | ~ spl13_3
    | ~ spl13_30 ),
    inference(subsumption_resolution,[],[f1098,f109])).

fof(f1098,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | m1_subset_1(sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = sK5
    | ~ spl13_3
    | ~ spl13_30 ),
    inference(subsumption_resolution,[],[f1097,f108])).

fof(f1097,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | m1_subset_1(sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = sK5
    | ~ spl13_3
    | ~ spl13_30 ),
    inference(subsumption_resolution,[],[f1053,f210])).

fof(f1053,plain,
    ( v1_xboole_0(u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | m1_subset_1(sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = sK5
    | ~ spl13_30 ),
    inference(resolution,[],[f356,f110])).

fof(f356,plain,
    ( ! [X6,X7] :
        ( ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X6,u1_struct_0(sK1))))
        | v1_xboole_0(X6)
        | ~ v1_funct_1(X7)
        | ~ v1_funct_2(X7,X6,u1_struct_0(sK1))
        | m1_subset_1(sK6(X6,u1_struct_0(sK1),X7,u1_struct_0(sK2),sK5),X6)
        | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X6))
        | k2_partfun1(X6,u1_struct_0(sK1),X7,u1_struct_0(sK2)) = sK5 )
    | ~ spl13_30 ),
    inference(avatar_component_clause,[],[f355])).

fof(f450,plain,(
    ~ spl13_38 ),
    inference(avatar_contradiction_clause,[],[f449])).

fof(f449,plain,
    ( $false
    | ~ spl13_38 ),
    inference(subsumption_resolution,[],[f399,f390])).

fof(f390,plain,
    ( sP12(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ spl13_38 ),
    inference(avatar_component_clause,[],[f389])).

fof(f389,plain,
    ( spl13_38
  <=> sP12(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_38])])).

fof(f399,plain,(
    ~ sP12(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f398,f112])).

fof(f398,plain,
    ( ~ v1_funct_1(sK5)
    | ~ sP12(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f324,f113])).

fof(f324,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | ~ sP12(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(resolution,[],[f114,f156])).

fof(f156,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ sP12(X1,X0) ) ),
    inference(general_splitting,[],[f140,f155_D])).

fof(f155,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_funct_2(X0,X1,X2,X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | sP12(X1,X0) ) ),
    inference(cnf_transformation,[],[f155_D])).

fof(f155_D,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | r2_funct_2(X0,X1,X2,X2)
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2) )
    <=> ~ sP12(X1,X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP12])])).

fof(f140,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f68])).

fof(f68,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => r2_funct_2(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t73_tmap_1.p',reflexivity_r2_funct_2)).

fof(f446,plain,(
    ~ spl13_28 ),
    inference(avatar_contradiction_clause,[],[f445])).

fof(f445,plain,
    ( $false
    | ~ spl13_28 ),
    inference(subsumption_resolution,[],[f444,f104])).

fof(f104,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f86])).

fof(f444,plain,
    ( v2_struct_0(sK2)
    | ~ spl13_28 ),
    inference(subsumption_resolution,[],[f441,f164])).

fof(f164,plain,(
    l1_struct_0(sK2) ),
    inference(resolution,[],[f161,f122])).

fof(f122,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t73_tmap_1.p',dt_l1_pre_topc)).

fof(f161,plain,(
    l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f160,f100])).

fof(f160,plain,
    ( l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f105,f123])).

fof(f441,plain,
    ( ~ l1_struct_0(sK2)
    | v2_struct_0(sK2)
    | ~ spl13_28 ),
    inference(resolution,[],[f353,f127])).

fof(f127,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f39])).

fof(f39,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t73_tmap_1.p',fc2_struct_0)).

fof(f353,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | ~ spl13_28 ),
    inference(avatar_component_clause,[],[f352])).

fof(f352,plain,
    ( spl13_28
  <=> v1_xboole_0(u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_28])])).

fof(f397,plain,
    ( spl13_38
    | spl13_40 ),
    inference(avatar_split_clause,[],[f384,f395,f389])).

fof(f384,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,sK5)
    | sP12(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f383,f112])).

fof(f383,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,sK5)
    | ~ v1_funct_1(sK5)
    | sP12(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f323,f113])).

fof(f323,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | sP12(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(resolution,[],[f114,f155])).

fof(f364,plain,
    ( spl13_28
    | spl13_32
    | spl13_1 ),
    inference(avatar_split_clause,[],[f360,f203,f362,f352])).

fof(f360,plain,
    ( ! [X8,X9] :
        ( r2_hidden(sK6(X8,u1_struct_0(sK1),X9,u1_struct_0(sK2),sK5),u1_struct_0(sK2))
        | k2_partfun1(X8,u1_struct_0(sK1),X9,u1_struct_0(sK2)) = sK5
        | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X8))
        | v1_xboole_0(u1_struct_0(sK2))
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X8,u1_struct_0(sK1))))
        | ~ v1_funct_2(X9,X8,u1_struct_0(sK1))
        | ~ v1_funct_1(X9)
        | v1_xboole_0(X8) )
    | ~ spl13_1 ),
    inference(subsumption_resolution,[],[f359,f204])).

fof(f359,plain,(
    ! [X8,X9] :
      ( r2_hidden(sK6(X8,u1_struct_0(sK1),X9,u1_struct_0(sK2),sK5),u1_struct_0(sK2))
      | k2_partfun1(X8,u1_struct_0(sK1),X9,u1_struct_0(sK2)) = sK5
      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X8))
      | v1_xboole_0(u1_struct_0(sK2))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X8,u1_struct_0(sK1))))
      | ~ v1_funct_2(X9,X8,u1_struct_0(sK1))
      | ~ v1_funct_1(X9)
      | v1_xboole_0(u1_struct_0(sK1))
      | v1_xboole_0(X8) ) ),
    inference(subsumption_resolution,[],[f358,f112])).

fof(f358,plain,(
    ! [X8,X9] :
      ( r2_hidden(sK6(X8,u1_struct_0(sK1),X9,u1_struct_0(sK2),sK5),u1_struct_0(sK2))
      | k2_partfun1(X8,u1_struct_0(sK1),X9,u1_struct_0(sK2)) = sK5
      | ~ v1_funct_1(sK5)
      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X8))
      | v1_xboole_0(u1_struct_0(sK2))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X8,u1_struct_0(sK1))))
      | ~ v1_funct_2(X9,X8,u1_struct_0(sK1))
      | ~ v1_funct_1(X9)
      | v1_xboole_0(u1_struct_0(sK1))
      | v1_xboole_0(X8) ) ),
    inference(subsumption_resolution,[],[f316,f113])).

fof(f316,plain,(
    ! [X8,X9] :
      ( r2_hidden(sK6(X8,u1_struct_0(sK1),X9,u1_struct_0(sK2),sK5),u1_struct_0(sK2))
      | k2_partfun1(X8,u1_struct_0(sK1),X9,u1_struct_0(sK2)) = sK5
      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ v1_funct_1(sK5)
      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X8))
      | v1_xboole_0(u1_struct_0(sK2))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X8,u1_struct_0(sK1))))
      | ~ v1_funct_2(X9,X8,u1_struct_0(sK1))
      | ~ v1_funct_1(X9)
      | v1_xboole_0(u1_struct_0(sK1))
      | v1_xboole_0(X8) ) ),
    inference(resolution,[],[f114,f119])).

fof(f119,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | r2_hidden(sK6(X0,X1,X2,X3,X4),X3)
      | k2_partfun1(X0,X1,X2,X3) = X4
      | ~ v1_funct_2(X4,X3,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f88])).

fof(f357,plain,
    ( spl13_28
    | spl13_30
    | spl13_1 ),
    inference(avatar_split_clause,[],[f347,f203,f355,f352])).

fof(f347,plain,
    ( ! [X6,X7] :
        ( m1_subset_1(sK6(X6,u1_struct_0(sK1),X7,u1_struct_0(sK2),sK5),X6)
        | k2_partfun1(X6,u1_struct_0(sK1),X7,u1_struct_0(sK2)) = sK5
        | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X6))
        | v1_xboole_0(u1_struct_0(sK2))
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X6,u1_struct_0(sK1))))
        | ~ v1_funct_2(X7,X6,u1_struct_0(sK1))
        | ~ v1_funct_1(X7)
        | v1_xboole_0(X6) )
    | ~ spl13_1 ),
    inference(subsumption_resolution,[],[f346,f204])).

fof(f346,plain,(
    ! [X6,X7] :
      ( m1_subset_1(sK6(X6,u1_struct_0(sK1),X7,u1_struct_0(sK2),sK5),X6)
      | k2_partfun1(X6,u1_struct_0(sK1),X7,u1_struct_0(sK2)) = sK5
      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X6))
      | v1_xboole_0(u1_struct_0(sK2))
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X6,u1_struct_0(sK1))))
      | ~ v1_funct_2(X7,X6,u1_struct_0(sK1))
      | ~ v1_funct_1(X7)
      | v1_xboole_0(u1_struct_0(sK1))
      | v1_xboole_0(X6) ) ),
    inference(subsumption_resolution,[],[f345,f112])).

fof(f345,plain,(
    ! [X6,X7] :
      ( m1_subset_1(sK6(X6,u1_struct_0(sK1),X7,u1_struct_0(sK2),sK5),X6)
      | k2_partfun1(X6,u1_struct_0(sK1),X7,u1_struct_0(sK2)) = sK5
      | ~ v1_funct_1(sK5)
      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X6))
      | v1_xboole_0(u1_struct_0(sK2))
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X6,u1_struct_0(sK1))))
      | ~ v1_funct_2(X7,X6,u1_struct_0(sK1))
      | ~ v1_funct_1(X7)
      | v1_xboole_0(u1_struct_0(sK1))
      | v1_xboole_0(X6) ) ),
    inference(subsumption_resolution,[],[f315,f113])).

fof(f315,plain,(
    ! [X6,X7] :
      ( m1_subset_1(sK6(X6,u1_struct_0(sK1),X7,u1_struct_0(sK2),sK5),X6)
      | k2_partfun1(X6,u1_struct_0(sK1),X7,u1_struct_0(sK2)) = sK5
      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ v1_funct_1(sK5)
      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X6))
      | v1_xboole_0(u1_struct_0(sK2))
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X6,u1_struct_0(sK1))))
      | ~ v1_funct_2(X7,X6,u1_struct_0(sK1))
      | ~ v1_funct_1(X7)
      | v1_xboole_0(u1_struct_0(sK1))
      | v1_xboole_0(X6) ) ),
    inference(resolution,[],[f114,f118])).

fof(f118,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | m1_subset_1(sK6(X0,X1,X2,X3,X4),X0)
      | k2_partfun1(X0,X1,X2,X3) = X4
      | ~ v1_funct_2(X4,X3,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f88])).

fof(f311,plain,(
    ~ spl13_0 ),
    inference(avatar_contradiction_clause,[],[f310])).

fof(f310,plain,
    ( $false
    | ~ spl13_0 ),
    inference(subsumption_resolution,[],[f309,f101])).

fof(f309,plain,
    ( v2_struct_0(sK1)
    | ~ spl13_0 ),
    inference(subsumption_resolution,[],[f306,f159])).

fof(f159,plain,(
    l1_struct_0(sK1) ),
    inference(resolution,[],[f103,f122])).

fof(f306,plain,
    ( ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl13_0 ),
    inference(resolution,[],[f207,f127])).

fof(f207,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ spl13_0 ),
    inference(avatar_component_clause,[],[f206])).

fof(f206,plain,
    ( spl13_0
  <=> v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_0])])).

fof(f305,plain,(
    ~ spl13_2 ),
    inference(avatar_contradiction_clause,[],[f304])).

fof(f304,plain,
    ( $false
    | ~ spl13_2 ),
    inference(subsumption_resolution,[],[f303,f106])).

fof(f106,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f86])).

fof(f303,plain,
    ( v2_struct_0(sK3)
    | ~ spl13_2 ),
    inference(subsumption_resolution,[],[f300,f165])).

fof(f165,plain,(
    l1_struct_0(sK3) ),
    inference(resolution,[],[f163,f122])).

fof(f300,plain,
    ( ~ l1_struct_0(sK3)
    | v2_struct_0(sK3)
    | ~ spl13_2 ),
    inference(resolution,[],[f213,f127])).

fof(f213,plain,
    ( v1_xboole_0(u1_struct_0(sK3))
    | ~ spl13_2 ),
    inference(avatar_component_clause,[],[f212])).

fof(f212,plain,
    ( spl13_2
  <=> v1_xboole_0(u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).

fof(f235,plain,
    ( spl13_2
    | spl13_10 ),
    inference(avatar_split_clause,[],[f231,f233,f212])).

fof(f231,plain,(
    ! [X11] :
      ( ~ m1_subset_1(X11,u1_struct_0(sK3))
      | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X11) = k1_funct_1(sK4,X11)
      | v1_xboole_0(u1_struct_0(sK3)) ) ),
    inference(subsumption_resolution,[],[f230,f108])).

fof(f230,plain,(
    ! [X11] :
      ( ~ m1_subset_1(X11,u1_struct_0(sK3))
      | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X11) = k1_funct_1(sK4,X11)
      | ~ v1_funct_1(sK4)
      | v1_xboole_0(u1_struct_0(sK3)) ) ),
    inference(subsumption_resolution,[],[f173,f109])).

fof(f173,plain,(
    ! [X11] :
      ( ~ m1_subset_1(X11,u1_struct_0(sK3))
      | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X11) = k1_funct_1(sK4,X11)
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ v1_funct_1(sK4)
      | v1_xboole_0(u1_struct_0(sK3)) ) ),
    inference(resolution,[],[f110,f139])).

fof(f139,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,X0)
      | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f66])).

fof(f66,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t73_tmap_1.p',redefinition_k3_funct_2)).
%------------------------------------------------------------------------------
