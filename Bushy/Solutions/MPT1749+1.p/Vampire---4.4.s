%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tmap_1__t59_tmap_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:17 EDT 2019

% Result     : Theorem 0.76s
% Output     : Refutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :  192 ( 858 expanded)
%              Number of leaves         :   34 ( 402 expanded)
%              Depth                    :   21
%              Number of atoms          : 1025 (13139 expanded)
%              Number of equality atoms :  114 ( 987 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8838,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f228,f347,f353,f386,f435,f441,f445,f578,f1105,f1126,f1197,f1217,f8837])).

fof(f8837,plain,
    ( spl12_1
    | spl12_3
    | ~ spl12_10
    | spl12_33
    | ~ spl12_128
    | ~ spl12_140
    | spl12_143
    | ~ spl12_156 ),
    inference(avatar_contradiction_clause,[],[f8836])).

fof(f8836,plain,
    ( $false
    | ~ spl12_1
    | ~ spl12_3
    | ~ spl12_10
    | ~ spl12_33
    | ~ spl12_128
    | ~ spl12_140
    | ~ spl12_143
    | ~ spl12_156 ),
    inference(subsumption_resolution,[],[f5454,f5661])).

fof(f5661,plain,
    ( k1_funct_1(sK3,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) = k1_funct_1(sK4,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4))
    | ~ spl12_10
    | ~ spl12_140
    | ~ spl12_156 ),
    inference(forward_demodulation,[],[f1268,f1259])).

fof(f1259,plain,
    ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) = k1_funct_1(sK3,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4))
    | ~ spl12_10
    | ~ spl12_140 ),
    inference(resolution,[],[f1098,f227])).

fof(f227,plain,
    ( ! [X8] :
        ( ~ m1_subset_1(X8,u1_struct_0(sK1))
        | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X8) = k1_funct_1(sK3,X8) )
    | ~ spl12_10 ),
    inference(avatar_component_clause,[],[f226])).

fof(f226,plain,
    ( spl12_10
  <=> ! [X8] :
        ( ~ m1_subset_1(X8,u1_struct_0(sK1))
        | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X8) = k1_funct_1(sK3,X8) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_10])])).

fof(f1098,plain,
    ( m1_subset_1(sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4),u1_struct_0(sK1))
    | ~ spl12_140 ),
    inference(avatar_component_clause,[],[f1097])).

fof(f1097,plain,
    ( spl12_140
  <=> m1_subset_1(sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_140])])).

fof(f1268,plain,
    ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) = k1_funct_1(sK4,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4))
    | ~ spl12_140
    | ~ spl12_156 ),
    inference(subsumption_resolution,[],[f1263,f1098])).

fof(f1263,plain,
    ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) = k1_funct_1(sK4,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4))
    | ~ m1_subset_1(sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4),u1_struct_0(sK1))
    | ~ spl12_156 ),
    inference(resolution,[],[f1196,f111])).

fof(f111,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,u1_struct_0(sK2))
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X5) = k1_funct_1(sK4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(sK1)) ) ),
    inference(cnf_transformation,[],[f85])).

fof(f85,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK4)
    & ! [X5] :
        ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X5) = k1_funct_1(sK4,X5)
        | ~ r2_hidden(X5,u1_struct_0(sK2))
        | ~ m1_subset_1(X5,u1_struct_0(sK1)) )
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK0))
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    & v1_funct_1(sK3)
    & m1_pre_topc(sK2,sK1)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f41,f84,f83,f82,f81,f80])).

fof(f80,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                        & ! [X5] :
                            ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) = k1_funct_1(X4,X5)
                            | ~ r2_hidden(X5,u1_struct_0(X2))
                            | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                        & v1_funct_1(X4) )
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                    & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                    & v1_funct_1(X3) )
                & m1_pre_topc(X2,X1)
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
                      ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(X1,sK0,X3,X2),X4)
                      & ! [X5] :
                          ( k3_funct_2(u1_struct_0(X1),u1_struct_0(sK0),X3,X5) = k1_funct_1(X4,X5)
                          | ~ r2_hidden(X5,u1_struct_0(X2))
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0))))
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK0))
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(sK0))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X1)
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
                      ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                      & ! [X5] :
                          ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) = k1_funct_1(X4,X5)
                          | ~ r2_hidden(X5,u1_struct_0(X2))
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(sK1,X0,X3,X2),X4)
                    & ! [X5] :
                        ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(X0),X3,X5) = k1_funct_1(X4,X5)
                        | ~ r2_hidden(X5,u1_struct_0(X2))
                        | ~ m1_subset_1(X5,u1_struct_0(sK1)) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                    & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                    & v1_funct_1(X4) )
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
                & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(X0))
                & v1_funct_1(X3) )
            & m1_pre_topc(X2,sK1)
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
                  ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                  & ! [X5] :
                      ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) = k1_funct_1(X4,X5)
                      | ~ r2_hidden(X5,u1_struct_0(X2))
                      | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                  & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X3) )
          & m1_pre_topc(X2,X1)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,sK2),X4)
                & ! [X5] :
                    ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) = k1_funct_1(X4,X5)
                    | ~ r2_hidden(X5,u1_struct_0(sK2))
                    | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
                & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(X0))
                & v1_funct_1(X4) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
            & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
            & v1_funct_1(X3) )
        & m1_pre_topc(sK2,X1)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
              & ! [X5] :
                  ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) = k1_funct_1(X4,X5)
                  | ~ r2_hidden(X5,u1_struct_0(X2))
                  | ~ m1_subset_1(X5,u1_struct_0(X1)) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
              & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
          & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
          & v1_funct_1(X3) )
     => ( ? [X4] :
            ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,sK3,X2),X4)
            & ! [X5] :
                ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),sK3,X5) = k1_funct_1(X4,X5)
                | ~ r2_hidden(X5,u1_struct_0(X2))
                | ~ m1_subset_1(X5,u1_struct_0(X1)) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
            & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
            & v1_funct_1(X4) )
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(sK3,u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
          & ! [X5] :
              ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) = k1_funct_1(X4,X5)
              | ~ r2_hidden(X5,u1_struct_0(X2))
              | ~ m1_subset_1(X5,u1_struct_0(X1)) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
          & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
          & v1_funct_1(X4) )
     => ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),sK4)
        & ! [X5] :
            ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) = k1_funct_1(sK4,X5)
            | ~ r2_hidden(X5,u1_struct_0(X2))
            | ~ m1_subset_1(X5,u1_struct_0(X1)) )
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
        & v1_funct_2(sK4,u1_struct_0(X2),u1_struct_0(X0))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                      & ! [X5] :
                          ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) = k1_funct_1(X4,X5)
                          | ~ r2_hidden(X5,u1_struct_0(X2))
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X1)
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
                      ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                      & ! [X5] :
                          ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) = k1_funct_1(X4,X5)
                          | ~ r2_hidden(X5,u1_struct_0(X2))
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X1)
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
                ( ( m1_pre_topc(X2,X1)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                      & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                      & v1_funct_1(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                          & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                          & v1_funct_1(X4) )
                       => ( ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X1))
                             => ( r2_hidden(X5,u1_struct_0(X2))
                               => k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) = k1_funct_1(X4,X5) ) )
                         => r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) ) ) ) ) ) ) ),
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
              ( ( m1_pre_topc(X2,X1)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                    & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                    & v1_funct_1(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                        & v1_funct_1(X4) )
                     => ( ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X1))
                           => ( r2_hidden(X5,u1_struct_0(X2))
                             => k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) = k1_funct_1(X4,X5) ) )
                       => r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t59_tmap_1.p',t59_tmap_1)).

fof(f1196,plain,
    ( r2_hidden(sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4),u1_struct_0(sK2))
    | ~ spl12_156 ),
    inference(avatar_component_clause,[],[f1195])).

fof(f1195,plain,
    ( spl12_156
  <=> r2_hidden(sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_156])])).

fof(f5454,plain,
    ( k1_funct_1(sK3,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) != k1_funct_1(sK4,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4))
    | ~ spl12_1
    | ~ spl12_3
    | ~ spl12_10
    | ~ spl12_33
    | ~ spl12_128
    | ~ spl12_140
    | ~ spl12_143 ),
    inference(subsumption_resolution,[],[f5453,f1101])).

fof(f1101,plain,
    ( k7_relat_1(sK3,u1_struct_0(sK2)) != sK4
    | ~ spl12_143 ),
    inference(avatar_component_clause,[],[f1100])).

fof(f1100,plain,
    ( spl12_143
  <=> k7_relat_1(sK3,u1_struct_0(sK2)) != sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_143])])).

fof(f5453,plain,
    ( k7_relat_1(sK3,u1_struct_0(sK2)) = sK4
    | k1_funct_1(sK3,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) != k1_funct_1(sK4,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4))
    | ~ spl12_1
    | ~ spl12_3
    | ~ spl12_10
    | ~ spl12_33
    | ~ spl12_128
    | ~ spl12_140 ),
    inference(forward_demodulation,[],[f5452,f233])).

fof(f233,plain,(
    ! [X11] : k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X11) = k7_relat_1(sK3,X11) ),
    inference(subsumption_resolution,[],[f168,f105])).

fof(f105,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f85])).

fof(f168,plain,(
    ! [X11] :
      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X11) = k7_relat_1(sK3,X11)
      | ~ v1_funct_1(sK3) ) ),
    inference(resolution,[],[f107,f143])).

fof(f143,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f76])).

fof(f76,plain,(
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
    file('/export/starexec/sandbox2/benchmark/tmap_1__t59_tmap_1.p',redefinition_k2_partfun1)).

fof(f107,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f85])).

fof(f5452,plain,
    ( k1_funct_1(sK3,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) != k1_funct_1(sK4,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4))
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) = sK4
    | ~ spl12_1
    | ~ spl12_3
    | ~ spl12_10
    | ~ spl12_33
    | ~ spl12_128
    | ~ spl12_140 ),
    inference(subsumption_resolution,[],[f5451,f203])).

fof(f203,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ spl12_3 ),
    inference(avatar_component_clause,[],[f202])).

fof(f202,plain,
    ( spl12_3
  <=> ~ v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).

fof(f5451,plain,
    ( k1_funct_1(sK3,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) != k1_funct_1(sK4,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4))
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) = sK4
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ spl12_1
    | ~ spl12_10
    | ~ spl12_33
    | ~ spl12_128
    | ~ spl12_140 ),
    inference(subsumption_resolution,[],[f5450,f197])).

fof(f197,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl12_1 ),
    inference(avatar_component_clause,[],[f196])).

fof(f196,plain,
    ( spl12_1
  <=> ~ v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).

fof(f5450,plain,
    ( k1_funct_1(sK3,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) != k1_funct_1(sK4,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4))
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) = sK4
    | v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ spl12_10
    | ~ spl12_33
    | ~ spl12_128
    | ~ spl12_140 ),
    inference(subsumption_resolution,[],[f5449,f105])).

fof(f5449,plain,
    ( k1_funct_1(sK3,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) != k1_funct_1(sK4,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4))
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) = sK4
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ spl12_10
    | ~ spl12_33
    | ~ spl12_128
    | ~ spl12_140 ),
    inference(subsumption_resolution,[],[f5448,f106])).

fof(f106,plain,(
    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f85])).

fof(f5448,plain,
    ( k1_funct_1(sK3,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) != k1_funct_1(sK4,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4))
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) = sK4
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ spl12_10
    | ~ spl12_33
    | ~ spl12_128
    | ~ spl12_140 ),
    inference(subsumption_resolution,[],[f5447,f107])).

fof(f5447,plain,
    ( k1_funct_1(sK3,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) != k1_funct_1(sK4,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4))
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) = sK4
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ spl12_10
    | ~ spl12_33
    | ~ spl12_128
    | ~ spl12_140 ),
    inference(subsumption_resolution,[],[f5446,f340])).

fof(f340,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK2))
    | ~ spl12_33 ),
    inference(avatar_component_clause,[],[f339])).

fof(f339,plain,
    ( spl12_33
  <=> ~ v1_xboole_0(u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_33])])).

fof(f5446,plain,
    ( k1_funct_1(sK3,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) != k1_funct_1(sK4,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4))
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) = sK4
    | v1_xboole_0(u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ spl12_10
    | ~ spl12_128
    | ~ spl12_140 ),
    inference(subsumption_resolution,[],[f5445,f1053])).

fof(f1053,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl12_128 ),
    inference(avatar_component_clause,[],[f1052])).

fof(f1052,plain,
    ( spl12_128
  <=> m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_128])])).

fof(f5445,plain,
    ( k1_funct_1(sK3,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) != k1_funct_1(sK4,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4))
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) = sK4
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_xboole_0(u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ spl12_10
    | ~ spl12_140 ),
    inference(subsumption_resolution,[],[f5444,f108])).

fof(f108,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f85])).

fof(f5444,plain,
    ( k1_funct_1(sK3,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) != k1_funct_1(sK4,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4))
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) = sK4
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_xboole_0(u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ spl12_10
    | ~ spl12_140 ),
    inference(subsumption_resolution,[],[f5443,f109])).

fof(f109,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f85])).

fof(f5443,plain,
    ( k1_funct_1(sK3,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) != k1_funct_1(sK4,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4))
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) = sK4
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_xboole_0(u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ spl12_10
    | ~ spl12_140 ),
    inference(subsumption_resolution,[],[f5439,f110])).

fof(f110,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f85])).

fof(f5439,plain,
    ( k1_funct_1(sK3,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) != k1_funct_1(sK4,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4))
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) = sK4
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_xboole_0(u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ spl12_10
    | ~ spl12_140 ),
    inference(superposition,[],[f116,f1259])).

fof(f116,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,sK5(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK5(X0,X1,X2,X3,X4))
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
    inference(cnf_transformation,[],[f87])).

fof(f87,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k2_partfun1(X0,X1,X2,X3) = X4
                      | ( k3_funct_2(X0,X1,X2,sK5(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK5(X0,X1,X2,X3,X4))
                        & r2_hidden(sK5(X0,X1,X2,X3,X4),X3)
                        & m1_subset_1(sK5(X0,X1,X2,X3,X4),X0) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f43,f86])).

fof(f86,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( k3_funct_2(X0,X1,X2,X5) != k1_funct_1(X4,X5)
          & r2_hidden(X5,X3)
          & m1_subset_1(X5,X0) )
     => ( k3_funct_2(X0,X1,X2,sK5(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK5(X0,X1,X2,X3,X4))
        & r2_hidden(sK5(X0,X1,X2,X3,X4),X3)
        & m1_subset_1(sK5(X0,X1,X2,X3,X4),X0) ) ) ),
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
    file('/export/starexec/sandbox2/benchmark/tmap_1__t59_tmap_1.p',t173_funct_2)).

fof(f1217,plain,
    ( ~ spl12_44
    | ~ spl12_142 ),
    inference(avatar_contradiction_clause,[],[f1216])).

fof(f1216,plain,
    ( $false
    | ~ spl12_44
    | ~ spl12_142 ),
    inference(subsumption_resolution,[],[f1200,f385])).

fof(f385,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK4,sK4)
    | ~ spl12_44 ),
    inference(avatar_component_clause,[],[f384])).

fof(f384,plain,
    ( spl12_44
  <=> r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK4,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_44])])).

fof(f1200,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK4,sK4)
    | ~ spl12_142 ),
    inference(backward_demodulation,[],[f1104,f699])).

fof(f699,plain,(
    ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),k7_relat_1(sK3,u1_struct_0(sK2)),sK4) ),
    inference(backward_demodulation,[],[f695,f112])).

fof(f112,plain,(
    ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK4) ),
    inference(cnf_transformation,[],[f85])).

fof(f695,plain,(
    k2_tmap_1(sK1,sK0,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK2)) ),
    inference(resolution,[],[f693,f104])).

fof(f104,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f85])).

fof(f693,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(X2,sK1)
      | k2_tmap_1(sK1,sK0,sK3,X2) = k7_relat_1(sK3,u1_struct_0(X2)) ) ),
    inference(forward_demodulation,[],[f192,f233])).

fof(f192,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(X2,sK1)
      | k2_tmap_1(sK1,sK0,sK3,X2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X2)) ) ),
    inference(subsumption_resolution,[],[f191,f100])).

fof(f100,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f85])).

fof(f191,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(X2,sK1)
      | k2_tmap_1(sK1,sK0,sK3,X2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X2))
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f190,f101])).

fof(f101,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f85])).

fof(f190,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(X2,sK1)
      | k2_tmap_1(sK1,sK0,sK3,X2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X2))
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f189,f102])).

fof(f102,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f85])).

fof(f189,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(X2,sK1)
      | k2_tmap_1(sK1,sK0,sK3,X2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X2))
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f188,f97])).

fof(f97,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f85])).

fof(f188,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(X2,sK1)
      | k2_tmap_1(sK1,sK0,sK3,X2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X2))
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f187,f98])).

fof(f98,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f85])).

fof(f187,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(X2,sK1)
      | k2_tmap_1(sK1,sK0,sK3,X2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X2))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f186,f99])).

fof(f99,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f85])).

fof(f186,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(X2,sK1)
      | k2_tmap_1(sK1,sK0,sK3,X2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X2))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f185,f105])).

fof(f185,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(X2,sK1)
      | k2_tmap_1(sK1,sK0,sK3,X2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X2))
      | ~ v1_funct_1(sK3)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f161,f106])).

fof(f161,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(X2,sK1)
      | k2_tmap_1(sK1,sK0,sK3,X2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X2))
      | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(sK3)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f107,f123])).

fof(f123,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ m1_pre_topc(X3,X0)
      | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
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
    inference(flattening,[],[f50])).

fof(f50,plain,(
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
    file('/export/starexec/sandbox2/benchmark/tmap_1__t59_tmap_1.p',d4_tmap_1)).

fof(f1104,plain,
    ( k7_relat_1(sK3,u1_struct_0(sK2)) = sK4
    | ~ spl12_142 ),
    inference(avatar_component_clause,[],[f1103])).

fof(f1103,plain,
    ( spl12_142
  <=> k7_relat_1(sK3,u1_struct_0(sK2)) = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_142])])).

fof(f1197,plain,
    ( spl12_156
    | spl12_142
    | spl12_3
    | ~ spl12_36
    | ~ spl12_128 ),
    inference(avatar_split_clause,[],[f1190,f1052,f351,f202,f1103,f1195])).

fof(f351,plain,
    ( spl12_36
  <=> ! [X5,X6] :
        ( r2_hidden(sK5(X5,u1_struct_0(sK0),X6,u1_struct_0(sK2),sK4),u1_struct_0(sK2))
        | v1_xboole_0(X5)
        | ~ v1_funct_1(X6)
        | ~ v1_funct_2(X6,X5,u1_struct_0(sK0))
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X5,u1_struct_0(sK0))))
        | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X5))
        | k2_partfun1(X5,u1_struct_0(sK0),X6,u1_struct_0(sK2)) = sK4 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_36])])).

fof(f1190,plain,
    ( k7_relat_1(sK3,u1_struct_0(sK2)) = sK4
    | r2_hidden(sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4),u1_struct_0(sK2))
    | ~ spl12_3
    | ~ spl12_36
    | ~ spl12_128 ),
    inference(forward_demodulation,[],[f1189,f233])).

fof(f1189,plain,
    ( r2_hidden(sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4),u1_struct_0(sK2))
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) = sK4
    | ~ spl12_3
    | ~ spl12_36
    | ~ spl12_128 ),
    inference(subsumption_resolution,[],[f1188,f1053])).

fof(f1188,plain,
    ( r2_hidden(sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) = sK4
    | ~ spl12_3
    | ~ spl12_36 ),
    inference(subsumption_resolution,[],[f1187,f106])).

fof(f1187,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | r2_hidden(sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) = sK4
    | ~ spl12_3
    | ~ spl12_36 ),
    inference(subsumption_resolution,[],[f1186,f105])).

fof(f1186,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | r2_hidden(sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) = sK4
    | ~ spl12_3
    | ~ spl12_36 ),
    inference(subsumption_resolution,[],[f1177,f203])).

fof(f1177,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | r2_hidden(sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) = sK4
    | ~ spl12_36 ),
    inference(resolution,[],[f352,f107])).

fof(f352,plain,
    ( ! [X6,X5] :
        ( ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X5,u1_struct_0(sK0))))
        | v1_xboole_0(X5)
        | ~ v1_funct_1(X6)
        | ~ v1_funct_2(X6,X5,u1_struct_0(sK0))
        | r2_hidden(sK5(X5,u1_struct_0(sK0),X6,u1_struct_0(sK2),sK4),u1_struct_0(sK2))
        | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X5))
        | k2_partfun1(X5,u1_struct_0(sK0),X6,u1_struct_0(sK2)) = sK4 )
    | ~ spl12_36 ),
    inference(avatar_component_clause,[],[f351])).

fof(f1126,plain,(
    spl12_129 ),
    inference(avatar_contradiction_clause,[],[f1125])).

fof(f1125,plain,
    ( $false
    | ~ spl12_129 ),
    inference(subsumption_resolution,[],[f1124,f102])).

fof(f1124,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ spl12_129 ),
    inference(subsumption_resolution,[],[f1123,f104])).

fof(f1123,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ spl12_129 ),
    inference(resolution,[],[f1056,f120])).

fof(f120,plain,(
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
    file('/export/starexec/sandbox2/benchmark/tmap_1__t59_tmap_1.p',t1_tsep_1)).

fof(f1056,plain,
    ( ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl12_129 ),
    inference(avatar_component_clause,[],[f1055])).

fof(f1055,plain,
    ( spl12_129
  <=> ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_129])])).

fof(f1105,plain,
    ( ~ spl12_129
    | spl12_140
    | spl12_142
    | spl12_3
    | ~ spl12_34 ),
    inference(avatar_split_clause,[],[f1092,f345,f202,f1103,f1097,f1055])).

fof(f345,plain,
    ( spl12_34
  <=> ! [X3,X4] :
        ( m1_subset_1(sK5(X3,u1_struct_0(sK0),X4,u1_struct_0(sK2),sK4),X3)
        | v1_xboole_0(X3)
        | ~ v1_funct_1(X4)
        | ~ v1_funct_2(X4,X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,u1_struct_0(sK0))))
        | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X3))
        | k2_partfun1(X3,u1_struct_0(sK0),X4,u1_struct_0(sK2)) = sK4 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_34])])).

fof(f1092,plain,
    ( k7_relat_1(sK3,u1_struct_0(sK2)) = sK4
    | m1_subset_1(sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4),u1_struct_0(sK1))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl12_3
    | ~ spl12_34 ),
    inference(forward_demodulation,[],[f1091,f233])).

fof(f1091,plain,
    ( m1_subset_1(sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4),u1_struct_0(sK1))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) = sK4
    | ~ spl12_3
    | ~ spl12_34 ),
    inference(subsumption_resolution,[],[f1090,f106])).

fof(f1090,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | m1_subset_1(sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4),u1_struct_0(sK1))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) = sK4
    | ~ spl12_3
    | ~ spl12_34 ),
    inference(subsumption_resolution,[],[f1089,f105])).

fof(f1089,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | m1_subset_1(sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4),u1_struct_0(sK1))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) = sK4
    | ~ spl12_3
    | ~ spl12_34 ),
    inference(subsumption_resolution,[],[f1043,f203])).

fof(f1043,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | m1_subset_1(sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4),u1_struct_0(sK1))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) = sK4
    | ~ spl12_34 ),
    inference(resolution,[],[f346,f107])).

fof(f346,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,u1_struct_0(sK0))))
        | v1_xboole_0(X3)
        | ~ v1_funct_1(X4)
        | ~ v1_funct_2(X4,X3,u1_struct_0(sK0))
        | m1_subset_1(sK5(X3,u1_struct_0(sK0),X4,u1_struct_0(sK2),sK4),X3)
        | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X3))
        | k2_partfun1(X3,u1_struct_0(sK0),X4,u1_struct_0(sK2)) = sK4 )
    | ~ spl12_34 ),
    inference(avatar_component_clause,[],[f345])).

fof(f578,plain,(
    ~ spl12_0 ),
    inference(avatar_contradiction_clause,[],[f577])).

fof(f577,plain,
    ( $false
    | ~ spl12_0 ),
    inference(subsumption_resolution,[],[f576,f97])).

fof(f576,plain,
    ( v2_struct_0(sK0)
    | ~ spl12_0 ),
    inference(subsumption_resolution,[],[f573,f154])).

fof(f154,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f99,f118])).

fof(f118,plain,(
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
    file('/export/starexec/sandbox2/benchmark/tmap_1__t59_tmap_1.p',dt_l1_pre_topc)).

fof(f573,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_0 ),
    inference(resolution,[],[f200,f124])).

fof(f124,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
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
    file('/export/starexec/sandbox2/benchmark/tmap_1__t59_tmap_1.p',fc2_struct_0)).

fof(f200,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl12_0 ),
    inference(avatar_component_clause,[],[f199])).

fof(f199,plain,
    ( spl12_0
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_0])])).

fof(f445,plain,(
    ~ spl12_42 ),
    inference(avatar_contradiction_clause,[],[f444])).

fof(f444,plain,
    ( $false
    | ~ spl12_42 ),
    inference(subsumption_resolution,[],[f388,f379])).

fof(f379,plain,
    ( sP11(u1_struct_0(sK0),u1_struct_0(sK2))
    | ~ spl12_42 ),
    inference(avatar_component_clause,[],[f378])).

fof(f378,plain,
    ( spl12_42
  <=> sP11(u1_struct_0(sK0),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_42])])).

fof(f388,plain,(
    ~ sP11(u1_struct_0(sK0),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f387,f108])).

fof(f387,plain,
    ( ~ v1_funct_1(sK4)
    | ~ sP11(u1_struct_0(sK0),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f305,f109])).

fof(f305,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ v1_funct_1(sK4)
    | ~ sP11(u1_struct_0(sK0),u1_struct_0(sK2)) ),
    inference(resolution,[],[f110,f152])).

fof(f152,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ sP11(X1,X0) ) ),
    inference(general_splitting,[],[f139,f151_D])).

fof(f151,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_funct_2(X0,X1,X2,X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | sP11(X1,X0) ) ),
    inference(cnf_transformation,[],[f151_D])).

fof(f151_D,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | r2_funct_2(X0,X1,X2,X2)
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2) )
    <=> ~ sP11(X1,X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP11])])).

fof(f139,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f70])).

fof(f70,plain,(
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
    file('/export/starexec/sandbox2/benchmark/tmap_1__t59_tmap_1.p',reflexivity_r2_funct_2)).

fof(f441,plain,(
    ~ spl12_32 ),
    inference(avatar_contradiction_clause,[],[f440])).

fof(f440,plain,
    ( $false
    | ~ spl12_32 ),
    inference(subsumption_resolution,[],[f439,f103])).

fof(f103,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f85])).

fof(f439,plain,
    ( v2_struct_0(sK2)
    | ~ spl12_32 ),
    inference(subsumption_resolution,[],[f436,f158])).

fof(f158,plain,(
    l1_struct_0(sK2) ),
    inference(resolution,[],[f157,f118])).

fof(f157,plain,(
    l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f156,f102])).

fof(f156,plain,
    ( l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f104,f119])).

fof(f119,plain,(
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
    file('/export/starexec/sandbox2/benchmark/tmap_1__t59_tmap_1.p',dt_m1_pre_topc)).

fof(f436,plain,
    ( ~ l1_struct_0(sK2)
    | v2_struct_0(sK2)
    | ~ spl12_32 ),
    inference(resolution,[],[f343,f124])).

fof(f343,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | ~ spl12_32 ),
    inference(avatar_component_clause,[],[f342])).

fof(f342,plain,
    ( spl12_32
  <=> v1_xboole_0(u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_32])])).

fof(f435,plain,(
    ~ spl12_2 ),
    inference(avatar_contradiction_clause,[],[f434])).

fof(f434,plain,
    ( $false
    | ~ spl12_2 ),
    inference(subsumption_resolution,[],[f433,f100])).

fof(f433,plain,
    ( v2_struct_0(sK1)
    | ~ spl12_2 ),
    inference(subsumption_resolution,[],[f430,f155])).

fof(f155,plain,(
    l1_struct_0(sK1) ),
    inference(resolution,[],[f102,f118])).

fof(f430,plain,
    ( ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl12_2 ),
    inference(resolution,[],[f206,f124])).

fof(f206,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ spl12_2 ),
    inference(avatar_component_clause,[],[f205])).

fof(f205,plain,
    ( spl12_2
  <=> v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).

fof(f386,plain,
    ( spl12_42
    | spl12_44 ),
    inference(avatar_split_clause,[],[f373,f384,f378])).

fof(f373,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK4,sK4)
    | sP11(u1_struct_0(sK0),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f372,f108])).

fof(f372,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK4,sK4)
    | ~ v1_funct_1(sK4)
    | sP11(u1_struct_0(sK0),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f304,f109])).

fof(f304,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK4,sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ v1_funct_1(sK4)
    | sP11(u1_struct_0(sK0),u1_struct_0(sK2)) ),
    inference(resolution,[],[f110,f151])).

fof(f353,plain,
    ( spl12_0
    | spl12_32
    | spl12_36 ),
    inference(avatar_split_clause,[],[f349,f351,f342,f199])).

fof(f349,plain,(
    ! [X6,X5] :
      ( r2_hidden(sK5(X5,u1_struct_0(sK0),X6,u1_struct_0(sK2),sK4),u1_struct_0(sK2))
      | k2_partfun1(X5,u1_struct_0(sK0),X6,u1_struct_0(sK2)) = sK4
      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X5))
      | v1_xboole_0(u1_struct_0(sK2))
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X5,u1_struct_0(sK0))))
      | ~ v1_funct_2(X6,X5,u1_struct_0(sK0))
      | ~ v1_funct_1(X6)
      | v1_xboole_0(u1_struct_0(sK0))
      | v1_xboole_0(X5) ) ),
    inference(subsumption_resolution,[],[f348,f108])).

fof(f348,plain,(
    ! [X6,X5] :
      ( r2_hidden(sK5(X5,u1_struct_0(sK0),X6,u1_struct_0(sK2),sK4),u1_struct_0(sK2))
      | k2_partfun1(X5,u1_struct_0(sK0),X6,u1_struct_0(sK2)) = sK4
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X5))
      | v1_xboole_0(u1_struct_0(sK2))
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X5,u1_struct_0(sK0))))
      | ~ v1_funct_2(X6,X5,u1_struct_0(sK0))
      | ~ v1_funct_1(X6)
      | v1_xboole_0(u1_struct_0(sK0))
      | v1_xboole_0(X5) ) ),
    inference(subsumption_resolution,[],[f297,f109])).

fof(f297,plain,(
    ! [X6,X5] :
      ( r2_hidden(sK5(X5,u1_struct_0(sK0),X6,u1_struct_0(sK2),sK4),u1_struct_0(sK2))
      | k2_partfun1(X5,u1_struct_0(sK0),X6,u1_struct_0(sK2)) = sK4
      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK0))
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X5))
      | v1_xboole_0(u1_struct_0(sK2))
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X5,u1_struct_0(sK0))))
      | ~ v1_funct_2(X6,X5,u1_struct_0(sK0))
      | ~ v1_funct_1(X6)
      | v1_xboole_0(u1_struct_0(sK0))
      | v1_xboole_0(X5) ) ),
    inference(resolution,[],[f110,f115])).

fof(f115,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | r2_hidden(sK5(X0,X1,X2,X3,X4),X3)
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
    inference(cnf_transformation,[],[f87])).

fof(f347,plain,
    ( spl12_0
    | spl12_32
    | spl12_34 ),
    inference(avatar_split_clause,[],[f337,f345,f342,f199])).

fof(f337,plain,(
    ! [X4,X3] :
      ( m1_subset_1(sK5(X3,u1_struct_0(sK0),X4,u1_struct_0(sK2),sK4),X3)
      | k2_partfun1(X3,u1_struct_0(sK0),X4,u1_struct_0(sK2)) = sK4
      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X3))
      | v1_xboole_0(u1_struct_0(sK2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,u1_struct_0(sK0))))
      | ~ v1_funct_2(X4,X3,u1_struct_0(sK0))
      | ~ v1_funct_1(X4)
      | v1_xboole_0(u1_struct_0(sK0))
      | v1_xboole_0(X3) ) ),
    inference(subsumption_resolution,[],[f336,f108])).

fof(f336,plain,(
    ! [X4,X3] :
      ( m1_subset_1(sK5(X3,u1_struct_0(sK0),X4,u1_struct_0(sK2),sK4),X3)
      | k2_partfun1(X3,u1_struct_0(sK0),X4,u1_struct_0(sK2)) = sK4
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X3))
      | v1_xboole_0(u1_struct_0(sK2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,u1_struct_0(sK0))))
      | ~ v1_funct_2(X4,X3,u1_struct_0(sK0))
      | ~ v1_funct_1(X4)
      | v1_xboole_0(u1_struct_0(sK0))
      | v1_xboole_0(X3) ) ),
    inference(subsumption_resolution,[],[f296,f109])).

fof(f296,plain,(
    ! [X4,X3] :
      ( m1_subset_1(sK5(X3,u1_struct_0(sK0),X4,u1_struct_0(sK2),sK4),X3)
      | k2_partfun1(X3,u1_struct_0(sK0),X4,u1_struct_0(sK2)) = sK4
      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK0))
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X3))
      | v1_xboole_0(u1_struct_0(sK2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,u1_struct_0(sK0))))
      | ~ v1_funct_2(X4,X3,u1_struct_0(sK0))
      | ~ v1_funct_1(X4)
      | v1_xboole_0(u1_struct_0(sK0))
      | v1_xboole_0(X3) ) ),
    inference(resolution,[],[f110,f114])).

fof(f114,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | m1_subset_1(sK5(X0,X1,X2,X3,X4),X0)
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
    inference(cnf_transformation,[],[f87])).

fof(f228,plain,
    ( spl12_2
    | spl12_10 ),
    inference(avatar_split_clause,[],[f224,f226,f205])).

fof(f224,plain,(
    ! [X8] :
      ( ~ m1_subset_1(X8,u1_struct_0(sK1))
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X8) = k1_funct_1(sK3,X8)
      | v1_xboole_0(u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f223,f105])).

fof(f223,plain,(
    ! [X8] :
      ( ~ m1_subset_1(X8,u1_struct_0(sK1))
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X8) = k1_funct_1(sK3,X8)
      | ~ v1_funct_1(sK3)
      | v1_xboole_0(u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f165,f106])).

fof(f165,plain,(
    ! [X8] :
      ( ~ m1_subset_1(X8,u1_struct_0(sK1))
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X8) = k1_funct_1(sK3,X8)
      | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(sK3)
      | v1_xboole_0(u1_struct_0(sK1)) ) ),
    inference(resolution,[],[f107,f135])).

fof(f135,plain,(
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
    file('/export/starexec/sandbox2/benchmark/tmap_1__t59_tmap_1.p',redefinition_k3_funct_2)).
%------------------------------------------------------------------------------
