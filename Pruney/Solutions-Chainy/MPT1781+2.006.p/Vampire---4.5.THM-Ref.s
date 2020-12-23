%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:17 EST 2020

% Result     : Theorem 2.11s
% Output     : Refutation 2.76s
% Verified   : 
% Statistics : Number of formulae       :  364 (2469 expanded)
%              Number of leaves         :   46 ( 876 expanded)
%              Depth                    :   30
%              Number of atoms          : 2131 (23543 expanded)
%              Number of equality atoms :  134 (2028 expanded)
%              Maximal formula depth    :   22 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1711,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f305,f308,f311,f778,f792,f797,f802,f856,f861,f1131,f1147,f1152,f1164,f1221,f1326,f1422,f1554,f1601,f1710])).

fof(f1710,plain,
    ( ~ spl10_6
    | ~ spl10_52 ),
    inference(avatar_contradiction_clause,[],[f1709])).

fof(f1709,plain,
    ( $false
    | ~ spl10_6
    | ~ spl10_52 ),
    inference(subsumption_resolution,[],[f1708,f126])).

fof(f126,plain,(
    l1_pre_topc(sK6) ),
    inference(subsumption_resolution,[],[f123,f81])).

fof(f81,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,
    ( ~ r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),k4_tmap_1(sK5,sK6),sK7)
    & ! [X3] :
        ( k1_funct_1(sK7,X3) = X3
        | ~ r2_hidden(X3,u1_struct_0(sK6))
        | ~ m1_subset_1(X3,u1_struct_0(sK5)) )
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5))))
    & v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK5))
    & v1_funct_1(sK7)
    & m1_pre_topc(sK6,sK5)
    & ~ v2_struct_0(sK6)
    & l1_pre_topc(sK5)
    & v2_pre_topc(sK5)
    & ~ v2_struct_0(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f21,f63,f62,f61])).

fof(f61,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)
                & ! [X3] :
                    ( k1_funct_1(X2,X3) = X3
                    | ~ r2_hidden(X3,u1_struct_0(X1))
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X1),u1_struct_0(sK5),k4_tmap_1(sK5,X1),X2)
              & ! [X3] :
                  ( k1_funct_1(X2,X3) = X3
                  | ~ r2_hidden(X3,u1_struct_0(X1))
                  | ~ m1_subset_1(X3,u1_struct_0(sK5)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK5))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK5))
              & v1_funct_1(X2) )
          & m1_pre_topc(X1,sK5)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK5)
      & v2_pre_topc(sK5)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r2_funct_2(u1_struct_0(X1),u1_struct_0(sK5),k4_tmap_1(sK5,X1),X2)
            & ! [X3] :
                ( k1_funct_1(X2,X3) = X3
                | ~ r2_hidden(X3,u1_struct_0(X1))
                | ~ m1_subset_1(X3,u1_struct_0(sK5)) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK5))))
            & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK5))
            & v1_funct_1(X2) )
        & m1_pre_topc(X1,sK5)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ~ r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),k4_tmap_1(sK5,sK6),X2)
          & ! [X3] :
              ( k1_funct_1(X2,X3) = X3
              | ~ r2_hidden(X3,u1_struct_0(sK6))
              | ~ m1_subset_1(X3,u1_struct_0(sK5)) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5))))
          & v1_funct_2(X2,u1_struct_0(sK6),u1_struct_0(sK5))
          & v1_funct_1(X2) )
      & m1_pre_topc(sK6,sK5)
      & ~ v2_struct_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,
    ( ? [X2] :
        ( ~ r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),k4_tmap_1(sK5,sK6),X2)
        & ! [X3] :
            ( k1_funct_1(X2,X3) = X3
            | ~ r2_hidden(X3,u1_struct_0(sK6))
            | ~ m1_subset_1(X3,u1_struct_0(sK5)) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5))))
        & v1_funct_2(X2,u1_struct_0(sK6),u1_struct_0(sK5))
        & v1_funct_1(X2) )
   => ( ~ r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),k4_tmap_1(sK5,sK6),sK7)
      & ! [X3] :
          ( k1_funct_1(sK7,X3) = X3
          | ~ r2_hidden(X3,u1_struct_0(sK6))
          | ~ m1_subset_1(X3,u1_struct_0(sK5)) )
      & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5))))
      & v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK5))
      & v1_funct_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)
              & ! [X3] :
                  ( k1_funct_1(X2,X3) = X3
                  | ~ r2_hidden(X3,u1_struct_0(X1))
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)
              & ! [X3] :
                  ( k1_funct_1(X2,X3) = X3
                  | ~ r2_hidden(X3,u1_struct_0(X1))
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X2) )
               => ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_hidden(X3,u1_struct_0(X1))
                       => k1_funct_1(X2,X3) = X3 ) )
                 => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_hidden(X3,u1_struct_0(X1))
                     => k1_funct_1(X2,X3) = X3 ) )
               => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_tmap_1)).

fof(f123,plain,
    ( l1_pre_topc(sK6)
    | ~ l1_pre_topc(sK5) ),
    inference(resolution,[],[f90,f83])).

fof(f83,plain,(
    m1_pre_topc(sK6,sK5) ),
    inference(cnf_transformation,[],[f64])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f1708,plain,
    ( ~ l1_pre_topc(sK6)
    | ~ spl10_6
    | ~ spl10_52 ),
    inference(subsumption_resolution,[],[f1704,f183])).

fof(f183,plain,
    ( v1_xboole_0(u1_struct_0(sK6))
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f181])).

fof(f181,plain,
    ( spl10_6
  <=> v1_xboole_0(u1_struct_0(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f1704,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK6))
    | ~ l1_pre_topc(sK6)
    | ~ spl10_52 ),
    inference(duplicate_literal_removal,[],[f1703])).

fof(f1703,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK6))
    | ~ l1_pre_topc(sK6)
    | ~ l1_pre_topc(sK6)
    | ~ spl10_52 ),
    inference(resolution,[],[f1697,f89])).

fof(f89,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f1697,plain,
    ( ! [X6] :
        ( ~ m1_pre_topc(sK6,X6)
        | ~ v1_xboole_0(u1_struct_0(X6))
        | ~ l1_pre_topc(X6) )
    | ~ spl10_52 ),
    inference(resolution,[],[f1553,f172])).

fof(f172,plain,(
    ! [X6,X4,X8,X7,X5,X9] :
      ( ~ sP0(X4,X5,X6,X7,X8)
      | ~ l1_pre_topc(X9)
      | ~ v1_xboole_0(u1_struct_0(X9))
      | ~ m1_pre_topc(X8,X9) ) ),
    inference(resolution,[],[f95,f144])).

fof(f144,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,u1_struct_0(X0))
      | ~ l1_pre_topc(X1)
      | ~ v1_xboole_0(u1_struct_0(X1))
      | ~ m1_pre_topc(X0,X1) ) ),
    inference(resolution,[],[f91,f114])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f91,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f95,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(sK8(X0,X1,X2,X3,X4),u1_struct_0(X4))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X2),X1,sK8(X0,X1,X2,X3,X4)) != k1_funct_1(X0,sK8(X0,X1,X2,X3,X4))
        & r2_hidden(sK8(X0,X1,X2,X3,X4),u1_struct_0(X4))
        & m1_subset_1(sK8(X0,X1,X2,X3,X4),u1_struct_0(X3)) )
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f66,f67])).

fof(f67,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X2),X1,X5) != k1_funct_1(X0,X5)
          & r2_hidden(X5,u1_struct_0(X4))
          & m1_subset_1(X5,u1_struct_0(X3)) )
     => ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X2),X1,sK8(X0,X1,X2,X3,X4)) != k1_funct_1(X0,sK8(X0,X1,X2,X3,X4))
        & r2_hidden(sK8(X0,X1,X2,X3,X4),u1_struct_0(X4))
        & m1_subset_1(sK8(X0,X1,X2,X3,X4),u1_struct_0(X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ? [X5] :
          ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X2),X1,X5) != k1_funct_1(X0,X5)
          & r2_hidden(X5,u1_struct_0(X4))
          & m1_subset_1(X5,u1_struct_0(X3)) )
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(rectify,[],[f65])).

fof(f65,plain,(
    ! [X4,X3,X0,X1,X2] :
      ( ? [X5] :
          ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5)
          & r2_hidden(X5,u1_struct_0(X2))
          & m1_subset_1(X5,u1_struct_0(X1)) )
      | ~ sP0(X4,X3,X0,X1,X2) ) ),
    inference(nnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X4,X3,X0,X1,X2] :
      ( ? [X5] :
          ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5)
          & r2_hidden(X5,u1_struct_0(X2))
          & m1_subset_1(X5,u1_struct_0(X1)) )
      | ~ sP0(X4,X3,X0,X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f1553,plain,
    ( sP0(k4_tmap_1(sK5,sK6),k4_tmap_1(sK5,sK5),sK5,sK5,sK6)
    | ~ spl10_52 ),
    inference(avatar_component_clause,[],[f1551])).

fof(f1551,plain,
    ( spl10_52
  <=> sP0(k4_tmap_1(sK5,sK6),k4_tmap_1(sK5,sK5),sK5,sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_52])])).

fof(f1601,plain,(
    ~ spl10_51 ),
    inference(avatar_contradiction_clause,[],[f1600])).

fof(f1600,plain,
    ( $false
    | ~ spl10_51 ),
    inference(subsumption_resolution,[],[f1568,f199])).

fof(f199,plain,(
    r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,sK7) ),
    inference(subsumption_resolution,[],[f198,f84])).

fof(f84,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f64])).

fof(f198,plain,
    ( r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,sK7)
    | ~ v1_funct_1(sK7) ),
    inference(subsumption_resolution,[],[f194,f85])).

fof(f85,plain,(
    v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f64])).

fof(f194,plain,
    ( r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,sK7)
    | ~ v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK5))
    | ~ v1_funct_1(sK7) ),
    inference(resolution,[],[f122,f86])).

fof(f86,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5)))) ),
    inference(cnf_transformation,[],[f64])).

fof(f122,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_funct_2(X0,X1,X3,X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(duplicate_literal_removal,[],[f121])).

fof(f121,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f116])).

fof(f116,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_funct_2(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_funct_2(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

fof(f1568,plain,
    ( ~ r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,sK7)
    | ~ spl10_51 ),
    inference(backward_demodulation,[],[f88,f1567])).

fof(f1567,plain,
    ( k4_tmap_1(sK5,sK6) = sK7
    | ~ spl10_51 ),
    inference(subsumption_resolution,[],[f1566,f151])).

fof(f151,plain,(
    sP1(sK5,sK6) ),
    inference(subsumption_resolution,[],[f150,f79])).

fof(f79,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f64])).

fof(f150,plain,
    ( sP1(sK5,sK6)
    | v2_struct_0(sK5) ),
    inference(subsumption_resolution,[],[f149,f80])).

fof(f80,plain,(
    v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f64])).

fof(f149,plain,
    ( sP1(sK5,sK6)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5) ),
    inference(subsumption_resolution,[],[f146,f81])).

fof(f146,plain,
    ( sP1(sK5,sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5) ),
    inference(resolution,[],[f107,f83])).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | sP1(X0,X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f44,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_tmap_1)).

fof(f1566,plain,
    ( k4_tmap_1(sK5,sK6) = sK7
    | ~ sP1(sK5,sK6)
    | ~ spl10_51 ),
    inference(subsumption_resolution,[],[f1565,f84])).

fof(f1565,plain,
    ( k4_tmap_1(sK5,sK6) = sK7
    | ~ v1_funct_1(sK7)
    | ~ sP1(sK5,sK6)
    | ~ spl10_51 ),
    inference(subsumption_resolution,[],[f1564,f85])).

fof(f1564,plain,
    ( k4_tmap_1(sK5,sK6) = sK7
    | ~ v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK5))
    | ~ v1_funct_1(sK7)
    | ~ sP1(sK5,sK6)
    | ~ spl10_51 ),
    inference(subsumption_resolution,[],[f1556,f86])).

fof(f1556,plain,
    ( k4_tmap_1(sK5,sK6) = sK7
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK5))
    | ~ v1_funct_1(sK7)
    | ~ sP1(sK5,sK6)
    | ~ spl10_51 ),
    inference(resolution,[],[f1549,f352])).

fof(f352,plain,(
    ! [X6,X8,X7] :
      ( ~ r2_funct_2(u1_struct_0(X6),u1_struct_0(X7),X8,k4_tmap_1(X7,X6))
      | k4_tmap_1(X7,X6) = X8
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(X7))))
      | ~ v1_funct_2(X8,u1_struct_0(X6),u1_struct_0(X7))
      | ~ v1_funct_1(X8)
      | ~ sP1(X7,X6) ) ),
    inference(subsumption_resolution,[],[f351,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k4_tmap_1(X0,X1))
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f54])).

fof(f351,plain,(
    ! [X6,X8,X7] :
      ( ~ r2_funct_2(u1_struct_0(X6),u1_struct_0(X7),X8,k4_tmap_1(X7,X6))
      | k4_tmap_1(X7,X6) = X8
      | ~ v1_funct_1(k4_tmap_1(X7,X6))
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(X7))))
      | ~ v1_funct_2(X8,u1_struct_0(X6),u1_struct_0(X7))
      | ~ v1_funct_1(X8)
      | ~ sP1(X7,X6) ) ),
    inference(subsumption_resolution,[],[f346,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f346,plain,(
    ! [X6,X8,X7] :
      ( ~ r2_funct_2(u1_struct_0(X6),u1_struct_0(X7),X8,k4_tmap_1(X7,X6))
      | k4_tmap_1(X7,X6) = X8
      | ~ v1_funct_2(k4_tmap_1(X7,X6),u1_struct_0(X6),u1_struct_0(X7))
      | ~ v1_funct_1(k4_tmap_1(X7,X6))
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(X7))))
      | ~ v1_funct_2(X8,u1_struct_0(X6),u1_struct_0(X7))
      | ~ v1_funct_1(X8)
      | ~ sP1(X7,X6) ) ),
    inference(resolution,[],[f115,f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f115,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_funct_2(X0,X1,X2,X3)
      | X2 = X3
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f1549,plain,
    ( r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,k4_tmap_1(sK5,sK6))
    | ~ spl10_51 ),
    inference(avatar_component_clause,[],[f1547])).

fof(f1547,plain,
    ( spl10_51
  <=> r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,k4_tmap_1(sK5,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_51])])).

fof(f88,plain,(
    ~ r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),k4_tmap_1(sK5,sK6),sK7) ),
    inference(cnf_transformation,[],[f64])).

fof(f1554,plain,
    ( spl10_51
    | spl10_52
    | ~ spl10_11
    | ~ spl10_12
    | ~ spl10_29
    | ~ spl10_32
    | ~ spl10_33
    | ~ spl10_48 ),
    inference(avatar_split_clause,[],[f1545,f1218,f858,f853,f775,f298,f294,f1551,f1547])).

fof(f294,plain,
    ( spl10_11
  <=> v1_funct_1(k4_tmap_1(sK5,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).

fof(f298,plain,
    ( spl10_12
  <=> v1_funct_2(k4_tmap_1(sK5,sK6),u1_struct_0(sK6),u1_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f775,plain,
    ( spl10_29
  <=> v1_funct_1(k4_tmap_1(sK5,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_29])])).

fof(f853,plain,
    ( spl10_32
  <=> v1_funct_2(k4_tmap_1(sK5,sK5),u1_struct_0(sK5),u1_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_32])])).

fof(f858,plain,
    ( spl10_33
  <=> m1_subset_1(k4_tmap_1(sK5,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_33])])).

fof(f1218,plain,
    ( spl10_48
  <=> sK7 = k2_tmap_1(sK5,sK5,k4_tmap_1(sK5,sK5),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_48])])).

fof(f1545,plain,
    ( sP0(k4_tmap_1(sK5,sK6),k4_tmap_1(sK5,sK5),sK5,sK5,sK6)
    | r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,k4_tmap_1(sK5,sK6))
    | ~ spl10_11
    | ~ spl10_12
    | ~ spl10_29
    | ~ spl10_32
    | ~ spl10_33
    | ~ spl10_48 ),
    inference(subsumption_resolution,[],[f1544,f151])).

fof(f1544,plain,
    ( sP0(k4_tmap_1(sK5,sK6),k4_tmap_1(sK5,sK5),sK5,sK5,sK6)
    | r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,k4_tmap_1(sK5,sK6))
    | ~ sP1(sK5,sK6)
    | ~ spl10_11
    | ~ spl10_12
    | ~ spl10_29
    | ~ spl10_32
    | ~ spl10_33
    | ~ spl10_48 ),
    inference(subsumption_resolution,[],[f1543,f295])).

fof(f295,plain,
    ( v1_funct_1(k4_tmap_1(sK5,sK6))
    | ~ spl10_11 ),
    inference(avatar_component_clause,[],[f294])).

fof(f1543,plain,
    ( sP0(k4_tmap_1(sK5,sK6),k4_tmap_1(sK5,sK5),sK5,sK5,sK6)
    | r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,k4_tmap_1(sK5,sK6))
    | ~ v1_funct_1(k4_tmap_1(sK5,sK6))
    | ~ sP1(sK5,sK6)
    | ~ spl10_12
    | ~ spl10_29
    | ~ spl10_32
    | ~ spl10_33
    | ~ spl10_48 ),
    inference(subsumption_resolution,[],[f1537,f299])).

fof(f299,plain,
    ( v1_funct_2(k4_tmap_1(sK5,sK6),u1_struct_0(sK6),u1_struct_0(sK5))
    | ~ spl10_12 ),
    inference(avatar_component_clause,[],[f298])).

fof(f1537,plain,
    ( sP0(k4_tmap_1(sK5,sK6),k4_tmap_1(sK5,sK5),sK5,sK5,sK6)
    | r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,k4_tmap_1(sK5,sK6))
    | ~ v1_funct_2(k4_tmap_1(sK5,sK6),u1_struct_0(sK6),u1_struct_0(sK5))
    | ~ v1_funct_1(k4_tmap_1(sK5,sK6))
    | ~ sP1(sK5,sK6)
    | ~ spl10_29
    | ~ spl10_32
    | ~ spl10_33
    | ~ spl10_48 ),
    inference(resolution,[],[f1383,f106])).

fof(f1383,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5))))
        | sP0(X0,k4_tmap_1(sK5,sK5),sK5,sK5,sK6)
        | r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK6),u1_struct_0(sK5))
        | ~ v1_funct_1(X0) )
    | ~ spl10_29
    | ~ spl10_32
    | ~ spl10_33
    | ~ spl10_48 ),
    inference(subsumption_resolution,[],[f1382,f79])).

fof(f1382,plain,
    ( ! [X0] :
        ( r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,X0)
        | sP0(X0,k4_tmap_1(sK5,sK5),sK5,sK5,sK6)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5))))
        | ~ v1_funct_2(X0,u1_struct_0(sK6),u1_struct_0(sK5))
        | ~ v1_funct_1(X0)
        | v2_struct_0(sK5) )
    | ~ spl10_29
    | ~ spl10_32
    | ~ spl10_33
    | ~ spl10_48 ),
    inference(subsumption_resolution,[],[f1381,f80])).

fof(f1381,plain,
    ( ! [X0] :
        ( r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,X0)
        | sP0(X0,k4_tmap_1(sK5,sK5),sK5,sK5,sK6)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5))))
        | ~ v1_funct_2(X0,u1_struct_0(sK6),u1_struct_0(sK5))
        | ~ v1_funct_1(X0)
        | ~ v2_pre_topc(sK5)
        | v2_struct_0(sK5) )
    | ~ spl10_29
    | ~ spl10_32
    | ~ spl10_33
    | ~ spl10_48 ),
    inference(subsumption_resolution,[],[f1380,f81])).

fof(f1380,plain,
    ( ! [X0] :
        ( r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,X0)
        | sP0(X0,k4_tmap_1(sK5,sK5),sK5,sK5,sK6)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5))))
        | ~ v1_funct_2(X0,u1_struct_0(sK6),u1_struct_0(sK5))
        | ~ v1_funct_1(X0)
        | ~ l1_pre_topc(sK5)
        | ~ v2_pre_topc(sK5)
        | v2_struct_0(sK5) )
    | ~ spl10_29
    | ~ spl10_32
    | ~ spl10_33
    | ~ spl10_48 ),
    inference(subsumption_resolution,[],[f1379,f82])).

fof(f82,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f64])).

fof(f1379,plain,
    ( ! [X0] :
        ( r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,X0)
        | sP0(X0,k4_tmap_1(sK5,sK5),sK5,sK5,sK6)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5))))
        | ~ v1_funct_2(X0,u1_struct_0(sK6),u1_struct_0(sK5))
        | ~ v1_funct_1(X0)
        | v2_struct_0(sK6)
        | ~ l1_pre_topc(sK5)
        | ~ v2_pre_topc(sK5)
        | v2_struct_0(sK5) )
    | ~ spl10_29
    | ~ spl10_32
    | ~ spl10_33
    | ~ spl10_48 ),
    inference(subsumption_resolution,[],[f1378,f83])).

fof(f1378,plain,
    ( ! [X0] :
        ( r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,X0)
        | sP0(X0,k4_tmap_1(sK5,sK5),sK5,sK5,sK6)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5))))
        | ~ v1_funct_2(X0,u1_struct_0(sK6),u1_struct_0(sK5))
        | ~ v1_funct_1(X0)
        | ~ m1_pre_topc(sK6,sK5)
        | v2_struct_0(sK6)
        | ~ l1_pre_topc(sK5)
        | ~ v2_pre_topc(sK5)
        | v2_struct_0(sK5) )
    | ~ spl10_29
    | ~ spl10_32
    | ~ spl10_33
    | ~ spl10_48 ),
    inference(subsumption_resolution,[],[f1377,f777])).

fof(f777,plain,
    ( v1_funct_1(k4_tmap_1(sK5,sK5))
    | ~ spl10_29 ),
    inference(avatar_component_clause,[],[f775])).

fof(f1377,plain,
    ( ! [X0] :
        ( r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,X0)
        | sP0(X0,k4_tmap_1(sK5,sK5),sK5,sK5,sK6)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5))))
        | ~ v1_funct_2(X0,u1_struct_0(sK6),u1_struct_0(sK5))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_1(k4_tmap_1(sK5,sK5))
        | ~ m1_pre_topc(sK6,sK5)
        | v2_struct_0(sK6)
        | ~ l1_pre_topc(sK5)
        | ~ v2_pre_topc(sK5)
        | v2_struct_0(sK5) )
    | ~ spl10_32
    | ~ spl10_33
    | ~ spl10_48 ),
    inference(subsumption_resolution,[],[f1376,f855])).

fof(f855,plain,
    ( v1_funct_2(k4_tmap_1(sK5,sK5),u1_struct_0(sK5),u1_struct_0(sK5))
    | ~ spl10_32 ),
    inference(avatar_component_clause,[],[f853])).

fof(f1376,plain,
    ( ! [X0] :
        ( r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,X0)
        | sP0(X0,k4_tmap_1(sK5,sK5),sK5,sK5,sK6)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5))))
        | ~ v1_funct_2(X0,u1_struct_0(sK6),u1_struct_0(sK5))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(k4_tmap_1(sK5,sK5),u1_struct_0(sK5),u1_struct_0(sK5))
        | ~ v1_funct_1(k4_tmap_1(sK5,sK5))
        | ~ m1_pre_topc(sK6,sK5)
        | v2_struct_0(sK6)
        | ~ l1_pre_topc(sK5)
        | ~ v2_pre_topc(sK5)
        | v2_struct_0(sK5) )
    | ~ spl10_33
    | ~ spl10_48 ),
    inference(subsumption_resolution,[],[f1375,f860])).

fof(f860,plain,
    ( m1_subset_1(k4_tmap_1(sK5,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5))))
    | ~ spl10_33 ),
    inference(avatar_component_clause,[],[f858])).

fof(f1375,plain,
    ( ! [X0] :
        ( r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,X0)
        | sP0(X0,k4_tmap_1(sK5,sK5),sK5,sK5,sK6)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5))))
        | ~ v1_funct_2(X0,u1_struct_0(sK6),u1_struct_0(sK5))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(k4_tmap_1(sK5,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5))))
        | ~ v1_funct_2(k4_tmap_1(sK5,sK5),u1_struct_0(sK5),u1_struct_0(sK5))
        | ~ v1_funct_1(k4_tmap_1(sK5,sK5))
        | ~ m1_pre_topc(sK6,sK5)
        | v2_struct_0(sK6)
        | ~ l1_pre_topc(sK5)
        | ~ v2_pre_topc(sK5)
        | v2_struct_0(sK5) )
    | ~ spl10_48 ),
    inference(duplicate_literal_removal,[],[f1374])).

fof(f1374,plain,
    ( ! [X0] :
        ( r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,X0)
        | sP0(X0,k4_tmap_1(sK5,sK5),sK5,sK5,sK6)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5))))
        | ~ v1_funct_2(X0,u1_struct_0(sK6),u1_struct_0(sK5))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(k4_tmap_1(sK5,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5))))
        | ~ v1_funct_2(k4_tmap_1(sK5,sK5),u1_struct_0(sK5),u1_struct_0(sK5))
        | ~ v1_funct_1(k4_tmap_1(sK5,sK5))
        | ~ m1_pre_topc(sK6,sK5)
        | v2_struct_0(sK6)
        | ~ l1_pre_topc(sK5)
        | ~ v2_pre_topc(sK5)
        | v2_struct_0(sK5)
        | ~ l1_pre_topc(sK5)
        | ~ v2_pre_topc(sK5)
        | v2_struct_0(sK5) )
    | ~ spl10_48 ),
    inference(superposition,[],[f97,f1220])).

fof(f1220,plain,
    ( sK7 = k2_tmap_1(sK5,sK5,k4_tmap_1(sK5,sK5),sK6)
    | ~ spl10_48 ),
    inference(avatar_component_clause,[],[f1218])).

fof(f97,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
      | sP0(X4,X3,X0,X1,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X3)
      | ~ m1_pre_topc(X2,X1)
      | v2_struct_0(X2)
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
                      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                      | sP0(X4,X3,X0,X1,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  | ~ v1_funct_1(X3) )
              | ~ m1_pre_topc(X2,X1)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f30,f52])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                      | ? [X5] :
                          ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5)
                          & r2_hidden(X5,u1_struct_0(X2))
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  | ~ v1_funct_1(X3) )
              | ~ m1_pre_topc(X2,X1)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                      | ? [X5] :
                          ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5)
                          & r2_hidden(X5,u1_struct_0(X2))
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  | ~ v1_funct_1(X3) )
              | ~ m1_pre_topc(X2,X1)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_tmap_1)).

fof(f1422,plain,
    ( spl10_6
    | ~ spl10_13 ),
    inference(avatar_contradiction_clause,[],[f1421])).

fof(f1421,plain,
    ( $false
    | spl10_6
    | ~ spl10_13 ),
    inference(subsumption_resolution,[],[f1420,f126])).

fof(f1420,plain,
    ( ~ l1_pre_topc(sK6)
    | spl10_6
    | ~ spl10_13 ),
    inference(resolution,[],[f1419,f89])).

fof(f1419,plain,
    ( ~ m1_pre_topc(sK6,sK6)
    | spl10_6
    | ~ spl10_13 ),
    inference(subsumption_resolution,[],[f1418,f1410])).

fof(f1410,plain,
    ( sK9(sK7,k4_tmap_1(sK5,sK6),u1_struct_0(sK6)) != k1_funct_1(sK7,sK9(sK7,k4_tmap_1(sK5,sK6),u1_struct_0(sK6)))
    | spl10_6
    | ~ spl10_13 ),
    inference(subsumption_resolution,[],[f1409,f314])).

fof(f314,plain,
    ( ~ sP2(sK7,k4_tmap_1(sK5,sK6),u1_struct_0(sK6))
    | ~ spl10_13 ),
    inference(subsumption_resolution,[],[f312,f88])).

fof(f312,plain,
    ( ~ sP2(sK7,k4_tmap_1(sK5,sK6),u1_struct_0(sK6))
    | r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),k4_tmap_1(sK5,sK6),sK7)
    | ~ spl10_13 ),
    inference(resolution,[],[f304,f109])).

fof(f109,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP3(X0,X1,X2,X3)
      | ~ sP2(X2,X1,X0)
      | r2_funct_2(X0,X3,X1,X2) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_funct_2(X0,X3,X1,X2)
          | ~ sP2(X2,X1,X0) )
        & ( sP2(X2,X1,X0)
          | ~ r2_funct_2(X0,X3,X1,X2) ) )
      | ~ sP3(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f70])).

fof(f70,plain,(
    ! [X0,X2,X3,X1] :
      ( ( ( r2_funct_2(X0,X1,X2,X3)
          | ~ sP2(X3,X2,X0) )
        & ( sP2(X3,X2,X0)
          | ~ r2_funct_2(X0,X1,X2,X3) ) )
      | ~ sP3(X0,X2,X3,X1) ) ),
    inference(nnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X2,X3,X1] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> sP2(X3,X2,X0) )
      | ~ sP3(X0,X2,X3,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f304,plain,
    ( sP3(u1_struct_0(sK6),k4_tmap_1(sK5,sK6),sK7,u1_struct_0(sK5))
    | ~ spl10_13 ),
    inference(avatar_component_clause,[],[f302])).

fof(f302,plain,
    ( spl10_13
  <=> sP3(u1_struct_0(sK6),k4_tmap_1(sK5,sK6),sK7,u1_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).

fof(f1409,plain,
    ( sK9(sK7,k4_tmap_1(sK5,sK6),u1_struct_0(sK6)) != k1_funct_1(sK7,sK9(sK7,k4_tmap_1(sK5,sK6),u1_struct_0(sK6)))
    | sP2(sK7,k4_tmap_1(sK5,sK6),u1_struct_0(sK6))
    | spl10_6
    | ~ spl10_13 ),
    inference(superposition,[],[f112,f1405])).

fof(f1405,plain,
    ( sK9(sK7,k4_tmap_1(sK5,sK6),u1_struct_0(sK6)) = k1_funct_1(k4_tmap_1(sK5,sK6),sK9(sK7,k4_tmap_1(sK5,sK6),u1_struct_0(sK6)))
    | spl10_6
    | ~ spl10_13 ),
    inference(resolution,[],[f1334,f314])).

fof(f1334,plain,
    ( ! [X0,X1] :
        ( sP2(X0,X1,u1_struct_0(sK6))
        | sK9(X0,X1,u1_struct_0(sK6)) = k1_funct_1(k4_tmap_1(sK5,sK6),sK9(X0,X1,u1_struct_0(sK6))) )
    | spl10_6 ),
    inference(subsumption_resolution,[],[f1268,f182])).

fof(f182,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK6))
    | spl10_6 ),
    inference(avatar_component_clause,[],[f181])).

fof(f1268,plain,(
    ! [X0,X1] :
      ( sK9(X0,X1,u1_struct_0(sK6)) = k1_funct_1(k4_tmap_1(sK5,sK6),sK9(X0,X1,u1_struct_0(sK6)))
      | v1_xboole_0(u1_struct_0(sK6))
      | sP2(X0,X1,u1_struct_0(sK6)) ) ),
    inference(subsumption_resolution,[],[f1267,f79])).

fof(f1267,plain,(
    ! [X0,X1] :
      ( sK9(X0,X1,u1_struct_0(sK6)) = k1_funct_1(k4_tmap_1(sK5,sK6),sK9(X0,X1,u1_struct_0(sK6)))
      | v2_struct_0(sK5)
      | v1_xboole_0(u1_struct_0(sK6))
      | sP2(X0,X1,u1_struct_0(sK6)) ) ),
    inference(subsumption_resolution,[],[f1266,f80])).

fof(f1266,plain,(
    ! [X0,X1] :
      ( sK9(X0,X1,u1_struct_0(sK6)) = k1_funct_1(k4_tmap_1(sK5,sK6),sK9(X0,X1,u1_struct_0(sK6)))
      | ~ v2_pre_topc(sK5)
      | v2_struct_0(sK5)
      | v1_xboole_0(u1_struct_0(sK6))
      | sP2(X0,X1,u1_struct_0(sK6)) ) ),
    inference(subsumption_resolution,[],[f1265,f81])).

fof(f1265,plain,(
    ! [X0,X1] :
      ( sK9(X0,X1,u1_struct_0(sK6)) = k1_funct_1(k4_tmap_1(sK5,sK6),sK9(X0,X1,u1_struct_0(sK6)))
      | ~ l1_pre_topc(sK5)
      | ~ v2_pre_topc(sK5)
      | v2_struct_0(sK5)
      | v1_xboole_0(u1_struct_0(sK6))
      | sP2(X0,X1,u1_struct_0(sK6)) ) ),
    inference(subsumption_resolution,[],[f368,f82])).

fof(f368,plain,(
    ! [X0,X1] :
      ( sK9(X0,X1,u1_struct_0(sK6)) = k1_funct_1(k4_tmap_1(sK5,sK6),sK9(X0,X1,u1_struct_0(sK6)))
      | v2_struct_0(sK6)
      | ~ l1_pre_topc(sK5)
      | ~ v2_pre_topc(sK5)
      | v2_struct_0(sK5)
      | v1_xboole_0(u1_struct_0(sK6))
      | sP2(X0,X1,u1_struct_0(sK6)) ) ),
    inference(resolution,[],[f233,f83])).

fof(f233,plain,(
    ! [X19,X17,X20,X18] :
      ( ~ m1_pre_topc(X18,X17)
      | sK9(X19,X20,u1_struct_0(X18)) = k1_funct_1(k4_tmap_1(X17,X18),sK9(X19,X20,u1_struct_0(X18)))
      | v2_struct_0(X18)
      | ~ l1_pre_topc(X17)
      | ~ v2_pre_topc(X17)
      | v2_struct_0(X17)
      | v1_xboole_0(u1_struct_0(X18))
      | sP2(X19,X20,u1_struct_0(X18)) ) ),
    inference(subsumption_resolution,[],[f228,f190])).

fof(f190,plain,(
    ! [X6,X8,X7,X9] :
      ( m1_subset_1(sK9(X6,X7,u1_struct_0(X8)),u1_struct_0(X9))
      | ~ m1_pre_topc(X8,X9)
      | v2_struct_0(X8)
      | ~ l1_pre_topc(X9)
      | v2_struct_0(X9)
      | sP2(X6,X7,u1_struct_0(X8)) ) ),
    inference(resolution,[],[f100,f111])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK9(X0,X1,X2),X2)
      | sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ( k1_funct_1(X1,sK9(X0,X1,X2)) != k1_funct_1(X0,sK9(X0,X1,X2))
          & m1_subset_1(sK9(X0,X1,X2),X2) ) )
      & ( ! [X4] :
            ( k1_funct_1(X1,X4) = k1_funct_1(X0,X4)
            | ~ m1_subset_1(X4,X2) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f73,f74])).

fof(f74,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k1_funct_1(X1,X3) != k1_funct_1(X0,X3)
          & m1_subset_1(X3,X2) )
     => ( k1_funct_1(X1,sK9(X0,X1,X2)) != k1_funct_1(X0,sK9(X0,X1,X2))
        & m1_subset_1(sK9(X0,X1,X2),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f73,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ? [X3] :
            ( k1_funct_1(X1,X3) != k1_funct_1(X0,X3)
            & m1_subset_1(X3,X2) ) )
      & ( ! [X4] :
            ( k1_funct_1(X1,X4) = k1_funct_1(X0,X4)
            | ~ m1_subset_1(X4,X2) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(rectify,[],[f72])).

fof(f72,plain,(
    ! [X3,X2,X0] :
      ( ( sP2(X3,X2,X0)
        | ? [X4] :
            ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
            & m1_subset_1(X4,X0) ) )
      & ( ! [X4] :
            ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
            | ~ m1_subset_1(X4,X0) )
        | ~ sP2(X3,X2,X0) ) ) ),
    inference(nnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X3,X2,X0] :
      ( sP2(X3,X2,X0)
    <=> ! [X4] :
          ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
          | ~ m1_subset_1(X4,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X1))
      | m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_pre_topc)).

fof(f228,plain,(
    ! [X19,X17,X20,X18] :
      ( sK9(X19,X20,u1_struct_0(X18)) = k1_funct_1(k4_tmap_1(X17,X18),sK9(X19,X20,u1_struct_0(X18)))
      | ~ m1_subset_1(sK9(X19,X20,u1_struct_0(X18)),u1_struct_0(X17))
      | ~ m1_pre_topc(X18,X17)
      | v2_struct_0(X18)
      | ~ l1_pre_topc(X17)
      | ~ v2_pre_topc(X17)
      | v2_struct_0(X17)
      | v1_xboole_0(u1_struct_0(X18))
      | sP2(X19,X20,u1_struct_0(X18)) ) ),
    inference(resolution,[],[f99,f142])).

fof(f142,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK9(X0,X1,X2),X2)
      | v1_xboole_0(X2)
      | sP2(X0,X1,X2) ) ),
    inference(resolution,[],[f111,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,u1_struct_0(X1))
      | k1_funct_1(k4_tmap_1(X0,X1),X2) = X2
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_funct_1(k4_tmap_1(X0,X1),X2) = X2
              | ~ r2_hidden(X2,u1_struct_0(X1))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_funct_1(k4_tmap_1(X0,X1),X2) = X2
              | ~ r2_hidden(X2,u1_struct_0(X1))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,u1_struct_0(X1))
               => k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_tmap_1)).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X1,sK9(X0,X1,X2)) != k1_funct_1(X0,sK9(X0,X1,X2))
      | sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f1418,plain,
    ( ~ m1_pre_topc(sK6,sK6)
    | sK9(sK7,k4_tmap_1(sK5,sK6),u1_struct_0(sK6)) = k1_funct_1(sK7,sK9(sK7,k4_tmap_1(sK5,sK6),u1_struct_0(sK6)))
    | spl10_6
    | ~ spl10_13 ),
    inference(subsumption_resolution,[],[f1414,f82])).

fof(f1414,plain,
    ( v2_struct_0(sK6)
    | ~ m1_pre_topc(sK6,sK6)
    | sK9(sK7,k4_tmap_1(sK5,sK6),u1_struct_0(sK6)) = k1_funct_1(sK7,sK9(sK7,k4_tmap_1(sK5,sK6),u1_struct_0(sK6)))
    | spl10_6
    | ~ spl10_13 ),
    inference(resolution,[],[f1332,f314])).

fof(f1332,plain,
    ( ! [X2,X0,X1] :
        ( sP2(X1,X2,u1_struct_0(X0))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK6)
        | sK9(X1,X2,u1_struct_0(X0)) = k1_funct_1(sK7,sK9(X1,X2,u1_struct_0(X0))) )
    | spl10_6 ),
    inference(subsumption_resolution,[],[f1331,f243])).

fof(f243,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK9(X1,X2,u1_struct_0(X0)),u1_struct_0(sK5))
      | sP2(X1,X2,u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK6) ) ),
    inference(subsumption_resolution,[],[f242,f79])).

fof(f242,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | sP2(X1,X2,u1_struct_0(X0))
      | m1_subset_1(sK9(X1,X2,u1_struct_0(X0)),u1_struct_0(sK5))
      | ~ m1_pre_topc(X0,sK6)
      | v2_struct_0(sK5) ) ),
    inference(subsumption_resolution,[],[f241,f81])).

fof(f241,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | sP2(X1,X2,u1_struct_0(X0))
      | m1_subset_1(sK9(X1,X2,u1_struct_0(X0)),u1_struct_0(sK5))
      | ~ m1_pre_topc(X0,sK6)
      | ~ l1_pre_topc(sK5)
      | v2_struct_0(sK5) ) ),
    inference(subsumption_resolution,[],[f238,f82])).

fof(f238,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | v2_struct_0(sK6)
      | sP2(X1,X2,u1_struct_0(X0))
      | m1_subset_1(sK9(X1,X2,u1_struct_0(X0)),u1_struct_0(sK5))
      | ~ m1_pre_topc(X0,sK6)
      | ~ l1_pre_topc(sK5)
      | v2_struct_0(sK5) ) ),
    inference(resolution,[],[f212,f83])).

fof(f212,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_pre_topc(X1,X4)
      | v2_struct_0(X0)
      | v2_struct_0(X1)
      | sP2(X2,X3,u1_struct_0(X0))
      | m1_subset_1(sK9(X2,X3,u1_struct_0(X0)),u1_struct_0(X4))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X4)
      | v2_struct_0(X4) ) ),
    inference(subsumption_resolution,[],[f211,f90])).

fof(f211,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_pre_topc(X0,X1)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X1)
      | sP2(X2,X3,u1_struct_0(X0))
      | m1_subset_1(sK9(X2,X3,u1_struct_0(X0)),u1_struct_0(X4))
      | ~ m1_pre_topc(X1,X4)
      | ~ l1_pre_topc(X4)
      | v2_struct_0(X4) ) ),
    inference(duplicate_literal_removal,[],[f209])).

fof(f209,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_pre_topc(X0,X1)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X1)
      | sP2(X2,X3,u1_struct_0(X0))
      | m1_subset_1(sK9(X2,X3,u1_struct_0(X0)),u1_struct_0(X4))
      | ~ m1_pre_topc(X1,X4)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X4)
      | v2_struct_0(X4) ) ),
    inference(resolution,[],[f190,f100])).

fof(f1331,plain,
    ( ! [X2,X0,X1] :
        ( v2_struct_0(X0)
        | sP2(X1,X2,u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK6)
        | sK9(X1,X2,u1_struct_0(X0)) = k1_funct_1(sK7,sK9(X1,X2,u1_struct_0(X0)))
        | ~ m1_subset_1(sK9(X1,X2,u1_struct_0(X0)),u1_struct_0(sK5)) )
    | spl10_6 ),
    inference(subsumption_resolution,[],[f220,f182])).

fof(f220,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | sP2(X1,X2,u1_struct_0(X0))
      | v1_xboole_0(u1_struct_0(sK6))
      | ~ m1_pre_topc(X0,sK6)
      | sK9(X1,X2,u1_struct_0(X0)) = k1_funct_1(sK7,sK9(X1,X2,u1_struct_0(X0)))
      | ~ m1_subset_1(sK9(X1,X2,u1_struct_0(X0)),u1_struct_0(sK5)) ) ),
    inference(subsumption_resolution,[],[f219,f82])).

fof(f219,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | v2_struct_0(sK6)
      | sP2(X1,X2,u1_struct_0(X0))
      | v1_xboole_0(u1_struct_0(sK6))
      | ~ m1_pre_topc(X0,sK6)
      | sK9(X1,X2,u1_struct_0(X0)) = k1_funct_1(sK7,sK9(X1,X2,u1_struct_0(X0)))
      | ~ m1_subset_1(sK9(X1,X2,u1_struct_0(X0)),u1_struct_0(sK5)) ) ),
    inference(subsumption_resolution,[],[f217,f126])).

fof(f217,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(sK6)
      | v2_struct_0(sK6)
      | sP2(X1,X2,u1_struct_0(X0))
      | v1_xboole_0(u1_struct_0(sK6))
      | ~ m1_pre_topc(X0,sK6)
      | sK9(X1,X2,u1_struct_0(X0)) = k1_funct_1(sK7,sK9(X1,X2,u1_struct_0(X0)))
      | ~ m1_subset_1(sK9(X1,X2,u1_struct_0(X0)),u1_struct_0(sK5)) ) ),
    inference(resolution,[],[f210,f87])).

fof(f87,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,u1_struct_0(sK6))
      | k1_funct_1(sK7,X3) = X3
      | ~ m1_subset_1(X3,u1_struct_0(sK5)) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f210,plain,(
    ! [X6,X8,X7,X5] :
      ( r2_hidden(sK9(X7,X8,u1_struct_0(X5)),u1_struct_0(X6))
      | v2_struct_0(X5)
      | ~ l1_pre_topc(X6)
      | v2_struct_0(X6)
      | sP2(X7,X8,u1_struct_0(X5))
      | v1_xboole_0(u1_struct_0(X6))
      | ~ m1_pre_topc(X5,X6) ) ),
    inference(resolution,[],[f190,f103])).

fof(f1326,plain,
    ( ~ spl10_13
    | ~ spl10_29
    | ~ spl10_32
    | ~ spl10_33
    | spl10_47 ),
    inference(avatar_contradiction_clause,[],[f1325])).

fof(f1325,plain,
    ( $false
    | ~ spl10_13
    | ~ spl10_29
    | ~ spl10_32
    | ~ spl10_33
    | spl10_47 ),
    inference(subsumption_resolution,[],[f1324,f126])).

fof(f1324,plain,
    ( ~ l1_pre_topc(sK6)
    | ~ spl10_13
    | ~ spl10_29
    | ~ spl10_32
    | ~ spl10_33
    | spl10_47 ),
    inference(resolution,[],[f1323,f89])).

fof(f1323,plain,
    ( ~ m1_pre_topc(sK6,sK6)
    | ~ spl10_13
    | ~ spl10_29
    | ~ spl10_32
    | ~ spl10_33
    | spl10_47 ),
    inference(subsumption_resolution,[],[f1322,f1308])).

fof(f1308,plain,
    ( sK9(sK7,k4_tmap_1(sK5,sK6),u1_struct_0(sK6)) != k1_funct_1(sK7,sK9(sK7,k4_tmap_1(sK5,sK6),u1_struct_0(sK6)))
    | ~ spl10_13
    | ~ spl10_29
    | ~ spl10_32
    | ~ spl10_33
    | spl10_47 ),
    inference(subsumption_resolution,[],[f1307,f314])).

fof(f1307,plain,
    ( sK9(sK7,k4_tmap_1(sK5,sK6),u1_struct_0(sK6)) != k1_funct_1(sK7,sK9(sK7,k4_tmap_1(sK5,sK6),u1_struct_0(sK6)))
    | sP2(sK7,k4_tmap_1(sK5,sK6),u1_struct_0(sK6))
    | ~ spl10_13
    | ~ spl10_29
    | ~ spl10_32
    | ~ spl10_33
    | spl10_47 ),
    inference(superposition,[],[f112,f1303])).

fof(f1303,plain,
    ( sK9(sK7,k4_tmap_1(sK5,sK6),u1_struct_0(sK6)) = k1_funct_1(k4_tmap_1(sK5,sK6),sK9(sK7,k4_tmap_1(sK5,sK6),u1_struct_0(sK6)))
    | ~ spl10_13
    | ~ spl10_29
    | ~ spl10_32
    | ~ spl10_33
    | spl10_47 ),
    inference(resolution,[],[f1269,f314])).

fof(f1269,plain,
    ( ! [X0,X1] :
        ( sP2(X0,X1,u1_struct_0(sK6))
        | sK9(X0,X1,u1_struct_0(sK6)) = k1_funct_1(k4_tmap_1(sK5,sK6),sK9(X0,X1,u1_struct_0(sK6))) )
    | ~ spl10_29
    | ~ spl10_32
    | ~ spl10_33
    | spl10_47 ),
    inference(subsumption_resolution,[],[f1268,f1252])).

fof(f1252,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK6))
    | ~ spl10_29
    | ~ spl10_32
    | ~ spl10_33
    | spl10_47 ),
    inference(subsumption_resolution,[],[f1245,f126])).

fof(f1245,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK6))
    | ~ l1_pre_topc(sK6)
    | ~ spl10_29
    | ~ spl10_32
    | ~ spl10_33
    | spl10_47 ),
    inference(duplicate_literal_removal,[],[f1244])).

fof(f1244,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK6))
    | ~ l1_pre_topc(sK6)
    | ~ l1_pre_topc(sK6)
    | ~ spl10_29
    | ~ spl10_32
    | ~ spl10_33
    | spl10_47 ),
    inference(resolution,[],[f1241,f89])).

fof(f1241,plain,
    ( ! [X6] :
        ( ~ m1_pre_topc(sK6,X6)
        | ~ v1_xboole_0(u1_struct_0(X6))
        | ~ l1_pre_topc(X6) )
    | ~ spl10_29
    | ~ spl10_32
    | ~ spl10_33
    | spl10_47 ),
    inference(resolution,[],[f1234,f172])).

fof(f1234,plain,
    ( sP0(sK7,k4_tmap_1(sK5,sK5),sK5,sK5,sK6)
    | ~ spl10_29
    | ~ spl10_32
    | ~ spl10_33
    | spl10_47 ),
    inference(subsumption_resolution,[],[f1233,f79])).

fof(f1233,plain,
    ( sP0(sK7,k4_tmap_1(sK5,sK5),sK5,sK5,sK6)
    | v2_struct_0(sK5)
    | ~ spl10_29
    | ~ spl10_32
    | ~ spl10_33
    | spl10_47 ),
    inference(subsumption_resolution,[],[f1232,f80])).

fof(f1232,plain,
    ( sP0(sK7,k4_tmap_1(sK5,sK5),sK5,sK5,sK6)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ spl10_29
    | ~ spl10_32
    | ~ spl10_33
    | spl10_47 ),
    inference(subsumption_resolution,[],[f1231,f81])).

fof(f1231,plain,
    ( sP0(sK7,k4_tmap_1(sK5,sK5),sK5,sK5,sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ spl10_29
    | ~ spl10_32
    | ~ spl10_33
    | spl10_47 ),
    inference(subsumption_resolution,[],[f1230,f82])).

fof(f1230,plain,
    ( sP0(sK7,k4_tmap_1(sK5,sK5),sK5,sK5,sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ spl10_29
    | ~ spl10_32
    | ~ spl10_33
    | spl10_47 ),
    inference(subsumption_resolution,[],[f1229,f83])).

fof(f1229,plain,
    ( sP0(sK7,k4_tmap_1(sK5,sK5),sK5,sK5,sK6)
    | ~ m1_pre_topc(sK6,sK5)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ spl10_29
    | ~ spl10_32
    | ~ spl10_33
    | spl10_47 ),
    inference(subsumption_resolution,[],[f1228,f777])).

fof(f1228,plain,
    ( sP0(sK7,k4_tmap_1(sK5,sK5),sK5,sK5,sK6)
    | ~ v1_funct_1(k4_tmap_1(sK5,sK5))
    | ~ m1_pre_topc(sK6,sK5)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ spl10_32
    | ~ spl10_33
    | spl10_47 ),
    inference(subsumption_resolution,[],[f1227,f855])).

fof(f1227,plain,
    ( sP0(sK7,k4_tmap_1(sK5,sK5),sK5,sK5,sK6)
    | ~ v1_funct_2(k4_tmap_1(sK5,sK5),u1_struct_0(sK5),u1_struct_0(sK5))
    | ~ v1_funct_1(k4_tmap_1(sK5,sK5))
    | ~ m1_pre_topc(sK6,sK5)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ spl10_33
    | spl10_47 ),
    inference(subsumption_resolution,[],[f1226,f860])).

fof(f1226,plain,
    ( sP0(sK7,k4_tmap_1(sK5,sK5),sK5,sK5,sK6)
    | ~ m1_subset_1(k4_tmap_1(sK5,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5))))
    | ~ v1_funct_2(k4_tmap_1(sK5,sK5),u1_struct_0(sK5),u1_struct_0(sK5))
    | ~ v1_funct_1(k4_tmap_1(sK5,sK5))
    | ~ m1_pre_topc(sK6,sK5)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl10_47 ),
    inference(subsumption_resolution,[],[f1225,f84])).

fof(f1225,plain,
    ( sP0(sK7,k4_tmap_1(sK5,sK5),sK5,sK5,sK6)
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(k4_tmap_1(sK5,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5))))
    | ~ v1_funct_2(k4_tmap_1(sK5,sK5),u1_struct_0(sK5),u1_struct_0(sK5))
    | ~ v1_funct_1(k4_tmap_1(sK5,sK5))
    | ~ m1_pre_topc(sK6,sK5)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl10_47 ),
    inference(subsumption_resolution,[],[f1224,f85])).

fof(f1224,plain,
    ( sP0(sK7,k4_tmap_1(sK5,sK5),sK5,sK5,sK6)
    | ~ v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK5))
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(k4_tmap_1(sK5,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5))))
    | ~ v1_funct_2(k4_tmap_1(sK5,sK5),u1_struct_0(sK5),u1_struct_0(sK5))
    | ~ v1_funct_1(k4_tmap_1(sK5,sK5))
    | ~ m1_pre_topc(sK6,sK5)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl10_47 ),
    inference(subsumption_resolution,[],[f1223,f86])).

fof(f1223,plain,
    ( sP0(sK7,k4_tmap_1(sK5,sK5),sK5,sK5,sK6)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK5))
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(k4_tmap_1(sK5,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5))))
    | ~ v1_funct_2(k4_tmap_1(sK5,sK5),u1_struct_0(sK5),u1_struct_0(sK5))
    | ~ v1_funct_1(k4_tmap_1(sK5,sK5))
    | ~ m1_pre_topc(sK6,sK5)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl10_47 ),
    inference(duplicate_literal_removal,[],[f1222])).

fof(f1222,plain,
    ( sP0(sK7,k4_tmap_1(sK5,sK5),sK5,sK5,sK6)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK5))
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(k4_tmap_1(sK5,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5))))
    | ~ v1_funct_2(k4_tmap_1(sK5,sK5),u1_struct_0(sK5),u1_struct_0(sK5))
    | ~ v1_funct_1(k4_tmap_1(sK5,sK5))
    | ~ m1_pre_topc(sK6,sK5)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl10_47 ),
    inference(resolution,[],[f1216,f97])).

fof(f1216,plain,
    ( ~ r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),k2_tmap_1(sK5,sK5,k4_tmap_1(sK5,sK5),sK6),sK7)
    | spl10_47 ),
    inference(avatar_component_clause,[],[f1214])).

fof(f1214,plain,
    ( spl10_47
  <=> r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),k2_tmap_1(sK5,sK5,k4_tmap_1(sK5,sK5),sK6),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_47])])).

fof(f1322,plain,
    ( ~ m1_pre_topc(sK6,sK6)
    | sK9(sK7,k4_tmap_1(sK5,sK6),u1_struct_0(sK6)) = k1_funct_1(sK7,sK9(sK7,k4_tmap_1(sK5,sK6),u1_struct_0(sK6)))
    | ~ spl10_13
    | ~ spl10_29
    | ~ spl10_32
    | ~ spl10_33
    | spl10_47 ),
    inference(subsumption_resolution,[],[f1318,f82])).

fof(f1318,plain,
    ( v2_struct_0(sK6)
    | ~ m1_pre_topc(sK6,sK6)
    | sK9(sK7,k4_tmap_1(sK5,sK6),u1_struct_0(sK6)) = k1_funct_1(sK7,sK9(sK7,k4_tmap_1(sK5,sK6),u1_struct_0(sK6)))
    | ~ spl10_13
    | ~ spl10_29
    | ~ spl10_32
    | ~ spl10_33
    | spl10_47 ),
    inference(resolution,[],[f1281,f314])).

fof(f1281,plain,
    ( ! [X2,X0,X1] :
        ( sP2(X1,X2,u1_struct_0(X0))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK6)
        | sK9(X1,X2,u1_struct_0(X0)) = k1_funct_1(sK7,sK9(X1,X2,u1_struct_0(X0))) )
    | ~ spl10_29
    | ~ spl10_32
    | ~ spl10_33
    | spl10_47 ),
    inference(subsumption_resolution,[],[f1280,f243])).

fof(f1280,plain,
    ( ! [X2,X0,X1] :
        ( v2_struct_0(X0)
        | sP2(X1,X2,u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK6)
        | sK9(X1,X2,u1_struct_0(X0)) = k1_funct_1(sK7,sK9(X1,X2,u1_struct_0(X0)))
        | ~ m1_subset_1(sK9(X1,X2,u1_struct_0(X0)),u1_struct_0(sK5)) )
    | ~ spl10_29
    | ~ spl10_32
    | ~ spl10_33
    | spl10_47 ),
    inference(subsumption_resolution,[],[f220,f1252])).

fof(f1221,plain,
    ( ~ spl10_47
    | spl10_48
    | ~ spl10_43
    | ~ spl10_44
    | ~ spl10_46 ),
    inference(avatar_split_clause,[],[f1178,f1161,f1149,f1128,f1218,f1214])).

fof(f1128,plain,
    ( spl10_43
  <=> v1_funct_1(k2_tmap_1(sK5,sK5,k4_tmap_1(sK5,sK5),sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_43])])).

fof(f1149,plain,
    ( spl10_44
  <=> v1_funct_2(k2_tmap_1(sK5,sK5,k4_tmap_1(sK5,sK5),sK6),u1_struct_0(sK6),u1_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_44])])).

fof(f1161,plain,
    ( spl10_46
  <=> m1_subset_1(k2_tmap_1(sK5,sK5,k4_tmap_1(sK5,sK5),sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_46])])).

fof(f1178,plain,
    ( sK7 = k2_tmap_1(sK5,sK5,k4_tmap_1(sK5,sK5),sK6)
    | ~ r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),k2_tmap_1(sK5,sK5,k4_tmap_1(sK5,sK5),sK6),sK7)
    | ~ spl10_43
    | ~ spl10_44
    | ~ spl10_46 ),
    inference(subsumption_resolution,[],[f1177,f1130])).

fof(f1130,plain,
    ( v1_funct_1(k2_tmap_1(sK5,sK5,k4_tmap_1(sK5,sK5),sK6))
    | ~ spl10_43 ),
    inference(avatar_component_clause,[],[f1128])).

fof(f1177,plain,
    ( sK7 = k2_tmap_1(sK5,sK5,k4_tmap_1(sK5,sK5),sK6)
    | ~ r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),k2_tmap_1(sK5,sK5,k4_tmap_1(sK5,sK5),sK6),sK7)
    | ~ v1_funct_1(k2_tmap_1(sK5,sK5,k4_tmap_1(sK5,sK5),sK6))
    | ~ spl10_44
    | ~ spl10_46 ),
    inference(subsumption_resolution,[],[f1165,f1151])).

fof(f1151,plain,
    ( v1_funct_2(k2_tmap_1(sK5,sK5,k4_tmap_1(sK5,sK5),sK6),u1_struct_0(sK6),u1_struct_0(sK5))
    | ~ spl10_44 ),
    inference(avatar_component_clause,[],[f1149])).

fof(f1165,plain,
    ( sK7 = k2_tmap_1(sK5,sK5,k4_tmap_1(sK5,sK5),sK6)
    | ~ r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),k2_tmap_1(sK5,sK5,k4_tmap_1(sK5,sK5),sK6),sK7)
    | ~ v1_funct_2(k2_tmap_1(sK5,sK5,k4_tmap_1(sK5,sK5),sK6),u1_struct_0(sK6),u1_struct_0(sK5))
    | ~ v1_funct_1(k2_tmap_1(sK5,sK5,k4_tmap_1(sK5,sK5),sK6))
    | ~ spl10_46 ),
    inference(resolution,[],[f1163,f354])).

fof(f354,plain,(
    ! [X9] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5))))
      | sK7 = X9
      | ~ r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),X9,sK7)
      | ~ v1_funct_2(X9,u1_struct_0(sK6),u1_struct_0(sK5))
      | ~ v1_funct_1(X9) ) ),
    inference(subsumption_resolution,[],[f353,f84])).

fof(f353,plain,(
    ! [X9] :
      ( ~ r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),X9,sK7)
      | sK7 = X9
      | ~ v1_funct_1(sK7)
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5))))
      | ~ v1_funct_2(X9,u1_struct_0(sK6),u1_struct_0(sK5))
      | ~ v1_funct_1(X9) ) ),
    inference(subsumption_resolution,[],[f347,f85])).

fof(f347,plain,(
    ! [X9] :
      ( ~ r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),X9,sK7)
      | sK7 = X9
      | ~ v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK5))
      | ~ v1_funct_1(sK7)
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5))))
      | ~ v1_funct_2(X9,u1_struct_0(sK6),u1_struct_0(sK5))
      | ~ v1_funct_1(X9) ) ),
    inference(resolution,[],[f115,f86])).

fof(f1163,plain,
    ( m1_subset_1(k2_tmap_1(sK5,sK5,k4_tmap_1(sK5,sK5),sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5))))
    | ~ spl10_46 ),
    inference(avatar_component_clause,[],[f1161])).

fof(f1164,plain,
    ( ~ spl10_42
    | spl10_46
    | ~ spl10_29
    | ~ spl10_31
    | ~ spl10_32
    | ~ spl10_33 ),
    inference(avatar_split_clause,[],[f1104,f858,f853,f789,f775,f1161,f1124])).

fof(f1124,plain,
    ( spl10_42
  <=> sP4(sK5,sK6,k4_tmap_1(sK5,sK5),sK5,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_42])])).

fof(f789,plain,
    ( spl10_31
  <=> m1_pre_topc(sK5,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_31])])).

fof(f1104,plain,
    ( m1_subset_1(k2_tmap_1(sK5,sK5,k4_tmap_1(sK5,sK5),sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5))))
    | ~ sP4(sK5,sK6,k4_tmap_1(sK5,sK5),sK5,sK5)
    | ~ spl10_29
    | ~ spl10_31
    | ~ spl10_32
    | ~ spl10_33 ),
    inference(superposition,[],[f119,f1082])).

fof(f1082,plain,
    ( k2_tmap_1(sK5,sK5,k4_tmap_1(sK5,sK5),sK6) = k3_tmap_1(sK5,sK5,sK5,sK6,k4_tmap_1(sK5,sK5))
    | ~ spl10_29
    | ~ spl10_31
    | ~ spl10_32
    | ~ spl10_33 ),
    inference(forward_demodulation,[],[f1079,f919])).

fof(f919,plain,
    ( k2_tmap_1(sK5,sK5,k4_tmap_1(sK5,sK5),sK6) = k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK5),k4_tmap_1(sK5,sK5),u1_struct_0(sK6))
    | ~ spl10_29
    | ~ spl10_32
    | ~ spl10_33 ),
    inference(resolution,[],[f884,f83])).

fof(f884,plain,
    ( ! [X2] :
        ( ~ m1_pre_topc(X2,sK5)
        | k2_tmap_1(sK5,sK5,k4_tmap_1(sK5,sK5),X2) = k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK5),k4_tmap_1(sK5,sK5),u1_struct_0(X2)) )
    | ~ spl10_29
    | ~ spl10_32
    | ~ spl10_33 ),
    inference(subsumption_resolution,[],[f883,f79])).

fof(f883,plain,
    ( ! [X2] :
        ( ~ m1_pre_topc(X2,sK5)
        | k2_tmap_1(sK5,sK5,k4_tmap_1(sK5,sK5),X2) = k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK5),k4_tmap_1(sK5,sK5),u1_struct_0(X2))
        | v2_struct_0(sK5) )
    | ~ spl10_29
    | ~ spl10_32
    | ~ spl10_33 ),
    inference(subsumption_resolution,[],[f882,f80])).

fof(f882,plain,
    ( ! [X2] :
        ( ~ m1_pre_topc(X2,sK5)
        | k2_tmap_1(sK5,sK5,k4_tmap_1(sK5,sK5),X2) = k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK5),k4_tmap_1(sK5,sK5),u1_struct_0(X2))
        | ~ v2_pre_topc(sK5)
        | v2_struct_0(sK5) )
    | ~ spl10_29
    | ~ spl10_32
    | ~ spl10_33 ),
    inference(subsumption_resolution,[],[f881,f81])).

fof(f881,plain,
    ( ! [X2] :
        ( ~ m1_pre_topc(X2,sK5)
        | k2_tmap_1(sK5,sK5,k4_tmap_1(sK5,sK5),X2) = k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK5),k4_tmap_1(sK5,sK5),u1_struct_0(X2))
        | ~ l1_pre_topc(sK5)
        | ~ v2_pre_topc(sK5)
        | v2_struct_0(sK5) )
    | ~ spl10_29
    | ~ spl10_32
    | ~ spl10_33 ),
    inference(subsumption_resolution,[],[f880,f777])).

fof(f880,plain,
    ( ! [X2] :
        ( ~ m1_pre_topc(X2,sK5)
        | k2_tmap_1(sK5,sK5,k4_tmap_1(sK5,sK5),X2) = k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK5),k4_tmap_1(sK5,sK5),u1_struct_0(X2))
        | ~ v1_funct_1(k4_tmap_1(sK5,sK5))
        | ~ l1_pre_topc(sK5)
        | ~ v2_pre_topc(sK5)
        | v2_struct_0(sK5) )
    | ~ spl10_32
    | ~ spl10_33 ),
    inference(subsumption_resolution,[],[f873,f855])).

fof(f873,plain,
    ( ! [X2] :
        ( ~ m1_pre_topc(X2,sK5)
        | k2_tmap_1(sK5,sK5,k4_tmap_1(sK5,sK5),X2) = k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK5),k4_tmap_1(sK5,sK5),u1_struct_0(X2))
        | ~ v1_funct_2(k4_tmap_1(sK5,sK5),u1_struct_0(sK5),u1_struct_0(sK5))
        | ~ v1_funct_1(k4_tmap_1(sK5,sK5))
        | ~ l1_pre_topc(sK5)
        | ~ v2_pre_topc(sK5)
        | v2_struct_0(sK5) )
    | ~ spl10_33 ),
    inference(duplicate_literal_removal,[],[f863])).

fof(f863,plain,
    ( ! [X2] :
        ( ~ m1_pre_topc(X2,sK5)
        | k2_tmap_1(sK5,sK5,k4_tmap_1(sK5,sK5),X2) = k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK5),k4_tmap_1(sK5,sK5),u1_struct_0(X2))
        | ~ v1_funct_2(k4_tmap_1(sK5,sK5),u1_struct_0(sK5),u1_struct_0(sK5))
        | ~ v1_funct_1(k4_tmap_1(sK5,sK5))
        | ~ l1_pre_topc(sK5)
        | ~ v2_pre_topc(sK5)
        | v2_struct_0(sK5)
        | ~ l1_pre_topc(sK5)
        | ~ v2_pre_topc(sK5)
        | v2_struct_0(sK5) )
    | ~ spl10_33 ),
    inference(resolution,[],[f860,f98])).

fof(f98,plain,(
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
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f1079,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK5),k4_tmap_1(sK5,sK5),u1_struct_0(sK6)) = k3_tmap_1(sK5,sK5,sK5,sK6,k4_tmap_1(sK5,sK5))
    | ~ spl10_29
    | ~ spl10_31
    | ~ spl10_32
    | ~ spl10_33 ),
    inference(resolution,[],[f1078,f83])).

fof(f1078,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK5)
        | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK5),k4_tmap_1(sK5,sK5),u1_struct_0(X0)) = k3_tmap_1(sK5,sK5,sK5,X0,k4_tmap_1(sK5,sK5)) )
    | ~ spl10_29
    | ~ spl10_31
    | ~ spl10_32
    | ~ spl10_33 ),
    inference(subsumption_resolution,[],[f1077,f79])).

fof(f1077,plain,
    ( ! [X0] :
        ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK5),k4_tmap_1(sK5,sK5),u1_struct_0(X0)) = k3_tmap_1(sK5,sK5,sK5,X0,k4_tmap_1(sK5,sK5))
        | ~ m1_pre_topc(X0,sK5)
        | v2_struct_0(sK5) )
    | ~ spl10_29
    | ~ spl10_31
    | ~ spl10_32
    | ~ spl10_33 ),
    inference(subsumption_resolution,[],[f1076,f80])).

fof(f1076,plain,
    ( ! [X0] :
        ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK5),k4_tmap_1(sK5,sK5),u1_struct_0(X0)) = k3_tmap_1(sK5,sK5,sK5,X0,k4_tmap_1(sK5,sK5))
        | ~ m1_pre_topc(X0,sK5)
        | ~ v2_pre_topc(sK5)
        | v2_struct_0(sK5) )
    | ~ spl10_29
    | ~ spl10_31
    | ~ spl10_32
    | ~ spl10_33 ),
    inference(subsumption_resolution,[],[f1073,f81])).

fof(f1073,plain,
    ( ! [X0] :
        ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK5),k4_tmap_1(sK5,sK5),u1_struct_0(X0)) = k3_tmap_1(sK5,sK5,sK5,X0,k4_tmap_1(sK5,sK5))
        | ~ m1_pre_topc(X0,sK5)
        | ~ l1_pre_topc(sK5)
        | ~ v2_pre_topc(sK5)
        | v2_struct_0(sK5) )
    | ~ spl10_29
    | ~ spl10_31
    | ~ spl10_32
    | ~ spl10_33 ),
    inference(resolution,[],[f879,f790])).

fof(f790,plain,
    ( m1_pre_topc(sK5,sK5)
    | ~ spl10_31 ),
    inference(avatar_component_clause,[],[f789])).

fof(f879,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(sK5,X1)
        | k3_tmap_1(X1,sK5,sK5,X0,k4_tmap_1(sK5,sK5)) = k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK5),k4_tmap_1(sK5,sK5),u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK5)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl10_29
    | ~ spl10_32
    | ~ spl10_33 ),
    inference(subsumption_resolution,[],[f878,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X2,X1)
      | m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).

fof(f878,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,sK5)
        | k3_tmap_1(X1,sK5,sK5,X0,k4_tmap_1(sK5,sK5)) = k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK5),k4_tmap_1(sK5,sK5),u1_struct_0(X0))
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(sK5,X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl10_29
    | ~ spl10_32
    | ~ spl10_33 ),
    inference(subsumption_resolution,[],[f877,f79])).

fof(f877,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,sK5)
        | k3_tmap_1(X1,sK5,sK5,X0,k4_tmap_1(sK5,sK5)) = k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK5),k4_tmap_1(sK5,sK5),u1_struct_0(X0))
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(sK5,X1)
        | v2_struct_0(sK5)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl10_29
    | ~ spl10_32
    | ~ spl10_33 ),
    inference(subsumption_resolution,[],[f876,f80])).

fof(f876,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,sK5)
        | k3_tmap_1(X1,sK5,sK5,X0,k4_tmap_1(sK5,sK5)) = k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK5),k4_tmap_1(sK5,sK5),u1_struct_0(X0))
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(sK5,X1)
        | ~ v2_pre_topc(sK5)
        | v2_struct_0(sK5)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl10_29
    | ~ spl10_32
    | ~ spl10_33 ),
    inference(subsumption_resolution,[],[f875,f81])).

fof(f875,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,sK5)
        | k3_tmap_1(X1,sK5,sK5,X0,k4_tmap_1(sK5,sK5)) = k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK5),k4_tmap_1(sK5,sK5),u1_struct_0(X0))
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(sK5,X1)
        | ~ l1_pre_topc(sK5)
        | ~ v2_pre_topc(sK5)
        | v2_struct_0(sK5)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl10_29
    | ~ spl10_32
    | ~ spl10_33 ),
    inference(subsumption_resolution,[],[f874,f777])).

fof(f874,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,sK5)
        | k3_tmap_1(X1,sK5,sK5,X0,k4_tmap_1(sK5,sK5)) = k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK5),k4_tmap_1(sK5,sK5),u1_struct_0(X0))
        | ~ v1_funct_1(k4_tmap_1(sK5,sK5))
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(sK5,X1)
        | ~ l1_pre_topc(sK5)
        | ~ v2_pre_topc(sK5)
        | v2_struct_0(sK5)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl10_32
    | ~ spl10_33 ),
    inference(subsumption_resolution,[],[f862,f855])).

fof(f862,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,sK5)
        | k3_tmap_1(X1,sK5,sK5,X0,k4_tmap_1(sK5,sK5)) = k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK5),k4_tmap_1(sK5,sK5),u1_struct_0(X0))
        | ~ v1_funct_2(k4_tmap_1(sK5,sK5),u1_struct_0(sK5),u1_struct_0(sK5))
        | ~ v1_funct_1(k4_tmap_1(sK5,sK5))
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(sK5,X1)
        | ~ l1_pre_topc(sK5)
        | ~ v2_pre_topc(sK5)
        | v2_struct_0(sK5)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl10_33 ),
    inference(resolution,[],[f860,f92])).

fof(f92,plain,(
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
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f119,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k3_tmap_1(X4,X0,X3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ sP4(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k3_tmap_1(X4,X0,X3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k3_tmap_1(X4,X0,X3,X1,X2),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k3_tmap_1(X4,X0,X3,X1,X2)) )
      | ~ sP4(X0,X1,X2,X3,X4) ) ),
    inference(rectify,[],[f77])).

fof(f77,plain,(
    ! [X1,X3,X4,X2,X0] :
      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
      | ~ sP4(X1,X3,X4,X2,X0) ) ),
    inference(nnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X1,X3,X4,X2,X0] :
      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
      | ~ sP4(X1,X3,X4,X2,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f1152,plain,
    ( ~ spl10_42
    | spl10_44
    | ~ spl10_29
    | ~ spl10_31
    | ~ spl10_32
    | ~ spl10_33 ),
    inference(avatar_split_clause,[],[f1103,f858,f853,f789,f775,f1149,f1124])).

fof(f1103,plain,
    ( v1_funct_2(k2_tmap_1(sK5,sK5,k4_tmap_1(sK5,sK5),sK6),u1_struct_0(sK6),u1_struct_0(sK5))
    | ~ sP4(sK5,sK6,k4_tmap_1(sK5,sK5),sK5,sK5)
    | ~ spl10_29
    | ~ spl10_31
    | ~ spl10_32
    | ~ spl10_33 ),
    inference(superposition,[],[f118,f1082])).

fof(f118,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k3_tmap_1(X4,X0,X3,X1,X2),u1_struct_0(X1),u1_struct_0(X0))
      | ~ sP4(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f1147,plain,
    ( ~ spl10_30
    | ~ spl10_31
    | spl10_42 ),
    inference(avatar_contradiction_clause,[],[f1146])).

fof(f1146,plain,
    ( $false
    | ~ spl10_30
    | ~ spl10_31
    | spl10_42 ),
    inference(subsumption_resolution,[],[f1145,f786])).

fof(f786,plain,
    ( sP1(sK5,sK5)
    | ~ spl10_30 ),
    inference(avatar_component_clause,[],[f785])).

fof(f785,plain,
    ( spl10_30
  <=> sP1(sK5,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_30])])).

fof(f1145,plain,
    ( ~ sP1(sK5,sK5)
    | ~ spl10_31
    | spl10_42 ),
    inference(subsumption_resolution,[],[f1144,f79])).

fof(f1144,plain,
    ( v2_struct_0(sK5)
    | ~ sP1(sK5,sK5)
    | ~ spl10_31
    | spl10_42 ),
    inference(subsumption_resolution,[],[f1143,f80])).

fof(f1143,plain,
    ( ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP1(sK5,sK5)
    | ~ spl10_31
    | spl10_42 ),
    inference(subsumption_resolution,[],[f1142,f81])).

fof(f1142,plain,
    ( ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP1(sK5,sK5)
    | ~ spl10_31
    | spl10_42 ),
    inference(subsumption_resolution,[],[f1141,f790])).

fof(f1141,plain,
    ( ~ m1_pre_topc(sK5,sK5)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP1(sK5,sK5)
    | spl10_42 ),
    inference(subsumption_resolution,[],[f1134,f83])).

fof(f1134,plain,
    ( ~ m1_pre_topc(sK6,sK5)
    | ~ m1_pre_topc(sK5,sK5)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP1(sK5,sK5)
    | spl10_42 ),
    inference(duplicate_literal_removal,[],[f1133])).

fof(f1133,plain,
    ( ~ m1_pre_topc(sK6,sK5)
    | ~ m1_pre_topc(sK5,sK5)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP1(sK5,sK5)
    | spl10_42 ),
    inference(resolution,[],[f1126,f422])).

fof(f422,plain,(
    ! [X10,X8,X7,X9] :
      ( sP4(X7,X8,k4_tmap_1(X7,X9),X9,X10)
      | ~ m1_pre_topc(X8,X10)
      | ~ m1_pre_topc(X9,X10)
      | ~ l1_pre_topc(X7)
      | ~ v2_pre_topc(X7)
      | v2_struct_0(X7)
      | ~ l1_pre_topc(X10)
      | ~ v2_pre_topc(X10)
      | v2_struct_0(X10)
      | ~ sP1(X7,X9) ) ),
    inference(subsumption_resolution,[],[f421,f104])).

fof(f421,plain,(
    ! [X10,X8,X7,X9] :
      ( sP4(X7,X8,k4_tmap_1(X7,X9),X9,X10)
      | ~ v1_funct_1(k4_tmap_1(X7,X9))
      | ~ m1_pre_topc(X8,X10)
      | ~ m1_pre_topc(X9,X10)
      | ~ l1_pre_topc(X7)
      | ~ v2_pre_topc(X7)
      | v2_struct_0(X7)
      | ~ l1_pre_topc(X10)
      | ~ v2_pre_topc(X10)
      | v2_struct_0(X10)
      | ~ sP1(X7,X9) ) ),
    inference(subsumption_resolution,[],[f416,f105])).

fof(f416,plain,(
    ! [X10,X8,X7,X9] :
      ( sP4(X7,X8,k4_tmap_1(X7,X9),X9,X10)
      | ~ v1_funct_2(k4_tmap_1(X7,X9),u1_struct_0(X9),u1_struct_0(X7))
      | ~ v1_funct_1(k4_tmap_1(X7,X9))
      | ~ m1_pre_topc(X8,X10)
      | ~ m1_pre_topc(X9,X10)
      | ~ l1_pre_topc(X7)
      | ~ v2_pre_topc(X7)
      | v2_struct_0(X7)
      | ~ l1_pre_topc(X10)
      | ~ v2_pre_topc(X10)
      | v2_struct_0(X10)
      | ~ sP1(X7,X9) ) ),
    inference(resolution,[],[f120,f106])).

fof(f120,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | sP4(X1,X3,X4,X2,X0)
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
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( sP4(X1,X3,X4,X2,X0)
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
    inference(definition_folding,[],[f51,f59])).

fof(f51,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
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
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(X4)
        & m1_pre_topc(X3,X0)
        & m1_pre_topc(X2,X0)
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_tmap_1)).

fof(f1126,plain,
    ( ~ sP4(sK5,sK6,k4_tmap_1(sK5,sK5),sK5,sK5)
    | spl10_42 ),
    inference(avatar_component_clause,[],[f1124])).

fof(f1131,plain,
    ( ~ spl10_42
    | spl10_43
    | ~ spl10_29
    | ~ spl10_31
    | ~ spl10_32
    | ~ spl10_33 ),
    inference(avatar_split_clause,[],[f1102,f858,f853,f789,f775,f1128,f1124])).

fof(f1102,plain,
    ( v1_funct_1(k2_tmap_1(sK5,sK5,k4_tmap_1(sK5,sK5),sK6))
    | ~ sP4(sK5,sK6,k4_tmap_1(sK5,sK5),sK5,sK5)
    | ~ spl10_29
    | ~ spl10_31
    | ~ spl10_32
    | ~ spl10_33 ),
    inference(superposition,[],[f117,f1082])).

fof(f117,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_1(k3_tmap_1(X4,X0,X3,X1,X2))
      | ~ sP4(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f861,plain,
    ( ~ spl10_28
    | spl10_33 ),
    inference(avatar_split_clause,[],[f741,f858,f771])).

fof(f771,plain,
    ( spl10_28
  <=> sP4(sK5,sK5,k4_tmap_1(sK5,sK5),sK5,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_28])])).

fof(f741,plain,
    ( m1_subset_1(k4_tmap_1(sK5,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5))))
    | ~ sP4(sK5,sK5,k4_tmap_1(sK5,sK5),sK5,sK5) ),
    inference(superposition,[],[f119,f736])).

fof(f736,plain,(
    k4_tmap_1(sK5,sK5) = k3_tmap_1(sK5,sK5,sK5,sK5,k4_tmap_1(sK5,sK5)) ),
    inference(subsumption_resolution,[],[f735,f80])).

fof(f735,plain,
    ( ~ v2_pre_topc(sK5)
    | k4_tmap_1(sK5,sK5) = k3_tmap_1(sK5,sK5,sK5,sK5,k4_tmap_1(sK5,sK5)) ),
    inference(subsumption_resolution,[],[f733,f79])).

fof(f733,plain,
    ( v2_struct_0(sK5)
    | ~ v2_pre_topc(sK5)
    | k4_tmap_1(sK5,sK5) = k3_tmap_1(sK5,sK5,sK5,sK5,k4_tmap_1(sK5,sK5)) ),
    inference(resolution,[],[f605,f81])).

fof(f605,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | k4_tmap_1(X0,X0) = k3_tmap_1(X0,X0,X0,X0,k4_tmap_1(X0,X0)) ) ),
    inference(duplicate_literal_removal,[],[f604])).

fof(f604,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | k4_tmap_1(X0,X0) = k3_tmap_1(X0,X0,X0,X0,k4_tmap_1(X0,X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f502,f89])).

fof(f502,plain,(
    ! [X2,X1] :
      ( ~ m1_pre_topc(X1,X2)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | k4_tmap_1(X1,X1) = k3_tmap_1(X2,X1,X1,X1,k4_tmap_1(X1,X1)) ) ),
    inference(subsumption_resolution,[],[f501,f90])).

fof(f501,plain,(
    ! [X2,X1] :
      ( ~ m1_pre_topc(X1,X2)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | k4_tmap_1(X1,X1) = k3_tmap_1(X2,X1,X1,X1,k4_tmap_1(X1,X1)) ) ),
    inference(subsumption_resolution,[],[f496,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f496,plain,(
    ! [X2,X1] :
      ( ~ m1_pre_topc(X1,X2)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | k4_tmap_1(X1,X1) = k3_tmap_1(X2,X1,X1,X1,k4_tmap_1(X1,X1)) ) ),
    inference(duplicate_literal_removal,[],[f495])).

fof(f495,plain,(
    ! [X2,X1] :
      ( ~ m1_pre_topc(X1,X2)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | k4_tmap_1(X1,X1) = k3_tmap_1(X2,X1,X1,X1,k4_tmap_1(X1,X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f440,f148])).

fof(f148,plain,(
    ! [X0] :
      ( sP1(X0,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f147])).

fof(f147,plain,(
    ! [X0] :
      ( sP1(X0,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f107,f89])).

fof(f440,plain,(
    ! [X6,X8,X7] :
      ( ~ sP1(X7,X8)
      | ~ m1_pre_topc(X8,X6)
      | v2_struct_0(X8)
      | ~ l1_pre_topc(X7)
      | ~ v2_pre_topc(X7)
      | v2_struct_0(X7)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6)
      | k4_tmap_1(X7,X8) = k3_tmap_1(X6,X7,X8,X8,k4_tmap_1(X7,X8)) ) ),
    inference(subsumption_resolution,[],[f439,f104])).

fof(f439,plain,(
    ! [X6,X8,X7] :
      ( k4_tmap_1(X7,X8) = k3_tmap_1(X6,X7,X8,X8,k4_tmap_1(X7,X8))
      | ~ v1_funct_1(k4_tmap_1(X7,X8))
      | ~ m1_pre_topc(X8,X6)
      | v2_struct_0(X8)
      | ~ l1_pre_topc(X7)
      | ~ v2_pre_topc(X7)
      | v2_struct_0(X7)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6)
      | ~ sP1(X7,X8) ) ),
    inference(subsumption_resolution,[],[f434,f105])).

fof(f434,plain,(
    ! [X6,X8,X7] :
      ( k4_tmap_1(X7,X8) = k3_tmap_1(X6,X7,X8,X8,k4_tmap_1(X7,X8))
      | ~ v1_funct_2(k4_tmap_1(X7,X8),u1_struct_0(X8),u1_struct_0(X7))
      | ~ v1_funct_1(k4_tmap_1(X7,X8))
      | ~ m1_pre_topc(X8,X6)
      | v2_struct_0(X8)
      | ~ l1_pre_topc(X7)
      | ~ v2_pre_topc(X7)
      | v2_struct_0(X7)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6)
      | ~ sP1(X7,X8) ) ),
    inference(resolution,[],[f432,f106])).

fof(f432,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | k3_tmap_1(X0,X1,X2,X2,X3) = X3
      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f431,f120])).

fof(f431,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_tmap_1(X0,X1,X2,X2,X3) = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ sP4(X1,X2,X3,X2,X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f428])).

fof(f428,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_tmap_1(X0,X1,X2,X2,X3) = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ sP4(X1,X2,X3,X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f350,f93])).

fof(f93,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                    & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                    & v1_funct_1(X3) )
                 => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tmap_1)).

fof(f350,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k3_tmap_1(X3,X1,X4,X0,X5))
      | k3_tmap_1(X3,X1,X4,X0,X5) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ sP4(X1,X0,X5,X4,X3) ) ),
    inference(subsumption_resolution,[],[f349,f117])).

fof(f349,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k3_tmap_1(X3,X1,X4,X0,X5))
      | k3_tmap_1(X3,X1,X4,X0,X5) = X2
      | ~ v1_funct_1(k3_tmap_1(X3,X1,X4,X0,X5))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ sP4(X1,X0,X5,X4,X3) ) ),
    inference(subsumption_resolution,[],[f345,f118])).

fof(f345,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k3_tmap_1(X3,X1,X4,X0,X5))
      | k3_tmap_1(X3,X1,X4,X0,X5) = X2
      | ~ v1_funct_2(k3_tmap_1(X3,X1,X4,X0,X5),u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(k3_tmap_1(X3,X1,X4,X0,X5))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ sP4(X1,X0,X5,X4,X3) ) ),
    inference(resolution,[],[f115,f119])).

fof(f856,plain,
    ( ~ spl10_28
    | spl10_32 ),
    inference(avatar_split_clause,[],[f740,f853,f771])).

fof(f740,plain,
    ( v1_funct_2(k4_tmap_1(sK5,sK5),u1_struct_0(sK5),u1_struct_0(sK5))
    | ~ sP4(sK5,sK5,k4_tmap_1(sK5,sK5),sK5,sK5) ),
    inference(superposition,[],[f118,f736])).

fof(f802,plain,(
    spl10_31 ),
    inference(avatar_contradiction_clause,[],[f801])).

fof(f801,plain,
    ( $false
    | spl10_31 ),
    inference(subsumption_resolution,[],[f800,f81])).

fof(f800,plain,
    ( ~ l1_pre_topc(sK5)
    | spl10_31 ),
    inference(resolution,[],[f791,f89])).

fof(f791,plain,
    ( ~ m1_pre_topc(sK5,sK5)
    | spl10_31 ),
    inference(avatar_component_clause,[],[f789])).

fof(f797,plain,(
    spl10_30 ),
    inference(avatar_contradiction_clause,[],[f796])).

fof(f796,plain,
    ( $false
    | spl10_30 ),
    inference(subsumption_resolution,[],[f795,f79])).

fof(f795,plain,
    ( v2_struct_0(sK5)
    | spl10_30 ),
    inference(subsumption_resolution,[],[f794,f80])).

fof(f794,plain,
    ( ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl10_30 ),
    inference(subsumption_resolution,[],[f793,f81])).

fof(f793,plain,
    ( ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl10_30 ),
    inference(resolution,[],[f787,f148])).

fof(f787,plain,
    ( ~ sP1(sK5,sK5)
    | spl10_30 ),
    inference(avatar_component_clause,[],[f785])).

fof(f792,plain,
    ( ~ spl10_30
    | ~ spl10_31
    | spl10_28 ),
    inference(avatar_split_clause,[],[f783,f771,f789,f785])).

fof(f783,plain,
    ( ~ m1_pre_topc(sK5,sK5)
    | ~ sP1(sK5,sK5)
    | spl10_28 ),
    inference(subsumption_resolution,[],[f782,f79])).

fof(f782,plain,
    ( ~ m1_pre_topc(sK5,sK5)
    | v2_struct_0(sK5)
    | ~ sP1(sK5,sK5)
    | spl10_28 ),
    inference(subsumption_resolution,[],[f781,f80])).

fof(f781,plain,
    ( ~ m1_pre_topc(sK5,sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP1(sK5,sK5)
    | spl10_28 ),
    inference(subsumption_resolution,[],[f780,f81])).

fof(f780,plain,
    ( ~ m1_pre_topc(sK5,sK5)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP1(sK5,sK5)
    | spl10_28 ),
    inference(duplicate_literal_removal,[],[f779])).

fof(f779,plain,
    ( ~ m1_pre_topc(sK5,sK5)
    | ~ m1_pre_topc(sK5,sK5)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP1(sK5,sK5)
    | spl10_28 ),
    inference(resolution,[],[f773,f422])).

fof(f773,plain,
    ( ~ sP4(sK5,sK5,k4_tmap_1(sK5,sK5),sK5,sK5)
    | spl10_28 ),
    inference(avatar_component_clause,[],[f771])).

fof(f778,plain,
    ( ~ spl10_28
    | spl10_29 ),
    inference(avatar_split_clause,[],[f739,f775,f771])).

fof(f739,plain,
    ( v1_funct_1(k4_tmap_1(sK5,sK5))
    | ~ sP4(sK5,sK5,k4_tmap_1(sK5,sK5),sK5,sK5) ),
    inference(superposition,[],[f117,f736])).

fof(f311,plain,(
    spl10_12 ),
    inference(avatar_contradiction_clause,[],[f310])).

fof(f310,plain,
    ( $false
    | spl10_12 ),
    inference(subsumption_resolution,[],[f309,f151])).

fof(f309,plain,
    ( ~ sP1(sK5,sK6)
    | spl10_12 ),
    inference(resolution,[],[f300,f105])).

fof(f300,plain,
    ( ~ v1_funct_2(k4_tmap_1(sK5,sK6),u1_struct_0(sK6),u1_struct_0(sK5))
    | spl10_12 ),
    inference(avatar_component_clause,[],[f298])).

fof(f308,plain,(
    spl10_11 ),
    inference(avatar_contradiction_clause,[],[f307])).

fof(f307,plain,
    ( $false
    | spl10_11 ),
    inference(subsumption_resolution,[],[f306,f151])).

fof(f306,plain,
    ( ~ sP1(sK5,sK6)
    | spl10_11 ),
    inference(resolution,[],[f296,f104])).

fof(f296,plain,
    ( ~ v1_funct_1(k4_tmap_1(sK5,sK6))
    | spl10_11 ),
    inference(avatar_component_clause,[],[f294])).

fof(f305,plain,
    ( ~ spl10_11
    | ~ spl10_12
    | spl10_13 ),
    inference(avatar_split_clause,[],[f286,f302,f298,f294])).

fof(f286,plain,
    ( sP3(u1_struct_0(sK6),k4_tmap_1(sK5,sK6),sK7,u1_struct_0(sK5))
    | ~ v1_funct_2(k4_tmap_1(sK5,sK6),u1_struct_0(sK6),u1_struct_0(sK5))
    | ~ v1_funct_1(k4_tmap_1(sK5,sK6)) ),
    inference(subsumption_resolution,[],[f281,f151])).

fof(f281,plain,
    ( sP3(u1_struct_0(sK6),k4_tmap_1(sK5,sK6),sK7,u1_struct_0(sK5))
    | ~ v1_funct_2(k4_tmap_1(sK5,sK6),u1_struct_0(sK6),u1_struct_0(sK5))
    | ~ v1_funct_1(k4_tmap_1(sK5,sK6))
    | ~ sP1(sK5,sK6) ),
    inference(resolution,[],[f279,f106])).

fof(f279,plain,(
    ! [X9] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5))))
      | sP3(u1_struct_0(sK6),X9,sK7,u1_struct_0(sK5))
      | ~ v1_funct_2(X9,u1_struct_0(sK6),u1_struct_0(sK5))
      | ~ v1_funct_1(X9) ) ),
    inference(subsumption_resolution,[],[f278,f84])).

fof(f278,plain,(
    ! [X9] :
      ( sP3(u1_struct_0(sK6),X9,sK7,u1_struct_0(sK5))
      | ~ v1_funct_1(sK7)
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5))))
      | ~ v1_funct_2(X9,u1_struct_0(sK6),u1_struct_0(sK5))
      | ~ v1_funct_1(X9) ) ),
    inference(subsumption_resolution,[],[f272,f85])).

fof(f272,plain,(
    ! [X9] :
      ( sP3(u1_struct_0(sK6),X9,sK7,u1_struct_0(sK5))
      | ~ v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK5))
      | ~ v1_funct_1(sK7)
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5))))
      | ~ v1_funct_2(X9,u1_struct_0(sK6),u1_struct_0(sK5))
      | ~ v1_funct_1(X9) ) ),
    inference(resolution,[],[f113,f86])).

fof(f113,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP3(X0,X2,X3,X1)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( sP3(X0,X2,X3,X1)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(definition_folding,[],[f46,f57,f56])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( r2_funct_2(X0,X1,X2,X3)
          <=> ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ m1_subset_1(X4,X0) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( r2_funct_2(X0,X1,X2,X3)
          <=> ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ m1_subset_1(X4,X0) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( r2_funct_2(X0,X1,X2,X3)
          <=> ! [X4] :
                ( m1_subset_1(X4,X0)
               => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:25:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (24523)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.47  % (24539)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.49  % (24521)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.50  % (24518)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.50  % (24516)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.51  % (24529)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.51  % (24537)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.51  % (24517)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (24526)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.51  % (24530)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.51  % (24528)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.51  % (24527)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.52  % (24522)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.52  % (24536)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.52  % (24534)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.52  % (24540)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.52  % (24516)Refutation not found, incomplete strategy% (24516)------------------------------
% 0.20/0.52  % (24516)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (24516)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (24516)Memory used [KB]: 10746
% 0.20/0.52  % (24516)Time elapsed: 0.116 s
% 0.20/0.52  % (24516)------------------------------
% 0.20/0.52  % (24516)------------------------------
% 0.20/0.53  % (24533)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.53  % (24520)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.53  % (24538)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.53  % (24541)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.53  % (24532)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.53  % (24524)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.54  % (24525)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.54  % (24531)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.54  % (24535)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.55  % (24519)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 2.11/0.71  % (24541)Refutation found. Thanks to Tanya!
% 2.11/0.71  % SZS status Theorem for theBenchmark
% 2.11/0.71  % SZS output start Proof for theBenchmark
% 2.11/0.71  fof(f1711,plain,(
% 2.11/0.71    $false),
% 2.11/0.71    inference(avatar_sat_refutation,[],[f305,f308,f311,f778,f792,f797,f802,f856,f861,f1131,f1147,f1152,f1164,f1221,f1326,f1422,f1554,f1601,f1710])).
% 2.11/0.71  fof(f1710,plain,(
% 2.11/0.71    ~spl10_6 | ~spl10_52),
% 2.11/0.71    inference(avatar_contradiction_clause,[],[f1709])).
% 2.11/0.71  fof(f1709,plain,(
% 2.11/0.71    $false | (~spl10_6 | ~spl10_52)),
% 2.11/0.71    inference(subsumption_resolution,[],[f1708,f126])).
% 2.11/0.71  fof(f126,plain,(
% 2.11/0.71    l1_pre_topc(sK6)),
% 2.11/0.71    inference(subsumption_resolution,[],[f123,f81])).
% 2.11/0.71  fof(f81,plain,(
% 2.11/0.71    l1_pre_topc(sK5)),
% 2.11/0.71    inference(cnf_transformation,[],[f64])).
% 2.11/0.71  fof(f64,plain,(
% 2.11/0.71    ((~r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),k4_tmap_1(sK5,sK6),sK7) & ! [X3] : (k1_funct_1(sK7,X3) = X3 | ~r2_hidden(X3,u1_struct_0(sK6)) | ~m1_subset_1(X3,u1_struct_0(sK5))) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5)))) & v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK5)) & v1_funct_1(sK7)) & m1_pre_topc(sK6,sK5) & ~v2_struct_0(sK6)) & l1_pre_topc(sK5) & v2_pre_topc(sK5) & ~v2_struct_0(sK5)),
% 2.11/0.71    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f21,f63,f62,f61])).
% 2.11/0.71  fof(f61,plain,(
% 2.11/0.71    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(sK5),k4_tmap_1(sK5,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(sK5))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK5)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK5)) & v1_funct_1(X2)) & m1_pre_topc(X1,sK5) & ~v2_struct_0(X1)) & l1_pre_topc(sK5) & v2_pre_topc(sK5) & ~v2_struct_0(sK5))),
% 2.11/0.71    introduced(choice_axiom,[])).
% 2.11/0.71  fof(f62,plain,(
% 2.11/0.71    ? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(sK5),k4_tmap_1(sK5,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(sK5))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK5)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK5)) & v1_funct_1(X2)) & m1_pre_topc(X1,sK5) & ~v2_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),k4_tmap_1(sK5,sK6),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(sK6)) | ~m1_subset_1(X3,u1_struct_0(sK5))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5)))) & v1_funct_2(X2,u1_struct_0(sK6),u1_struct_0(sK5)) & v1_funct_1(X2)) & m1_pre_topc(sK6,sK5) & ~v2_struct_0(sK6))),
% 2.11/0.71    introduced(choice_axiom,[])).
% 2.11/0.71  fof(f63,plain,(
% 2.11/0.71    ? [X2] : (~r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),k4_tmap_1(sK5,sK6),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(sK6)) | ~m1_subset_1(X3,u1_struct_0(sK5))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5)))) & v1_funct_2(X2,u1_struct_0(sK6),u1_struct_0(sK5)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),k4_tmap_1(sK5,sK6),sK7) & ! [X3] : (k1_funct_1(sK7,X3) = X3 | ~r2_hidden(X3,u1_struct_0(sK6)) | ~m1_subset_1(X3,u1_struct_0(sK5))) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5)))) & v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK5)) & v1_funct_1(sK7))),
% 2.11/0.71    introduced(choice_axiom,[])).
% 2.11/0.71  fof(f21,plain,(
% 2.11/0.71    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.11/0.71    inference(flattening,[],[f20])).
% 2.11/0.71  fof(f20,plain,(
% 2.11/0.71    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : ((k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X0)))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.11/0.71    inference(ennf_transformation,[],[f19])).
% 2.11/0.71  fof(f19,negated_conjecture,(
% 2.11/0.71    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,u1_struct_0(X1)) => k1_funct_1(X2,X3) = X3)) => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)))))),
% 2.11/0.71    inference(negated_conjecture,[],[f18])).
% 2.11/0.71  fof(f18,conjecture,(
% 2.11/0.71    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,u1_struct_0(X1)) => k1_funct_1(X2,X3) = X3)) => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)))))),
% 2.11/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_tmap_1)).
% 2.11/0.71  fof(f123,plain,(
% 2.11/0.71    l1_pre_topc(sK6) | ~l1_pre_topc(sK5)),
% 2.11/0.71    inference(resolution,[],[f90,f83])).
% 2.11/0.71  fof(f83,plain,(
% 2.11/0.71    m1_pre_topc(sK6,sK5)),
% 2.11/0.71    inference(cnf_transformation,[],[f64])).
% 2.11/0.71  fof(f90,plain,(
% 2.11/0.71    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 2.11/0.71    inference(cnf_transformation,[],[f23])).
% 2.11/0.71  fof(f23,plain,(
% 2.11/0.71    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.11/0.71    inference(ennf_transformation,[],[f6])).
% 2.11/0.71  fof(f6,axiom,(
% 2.11/0.71    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.11/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 2.11/0.71  fof(f1708,plain,(
% 2.11/0.71    ~l1_pre_topc(sK6) | (~spl10_6 | ~spl10_52)),
% 2.11/0.71    inference(subsumption_resolution,[],[f1704,f183])).
% 2.11/0.71  fof(f183,plain,(
% 2.11/0.71    v1_xboole_0(u1_struct_0(sK6)) | ~spl10_6),
% 2.11/0.71    inference(avatar_component_clause,[],[f181])).
% 2.11/0.71  fof(f181,plain,(
% 2.11/0.71    spl10_6 <=> v1_xboole_0(u1_struct_0(sK6))),
% 2.11/0.71    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).
% 2.11/0.71  fof(f1704,plain,(
% 2.11/0.71    ~v1_xboole_0(u1_struct_0(sK6)) | ~l1_pre_topc(sK6) | ~spl10_52),
% 2.11/0.71    inference(duplicate_literal_removal,[],[f1703])).
% 2.11/0.71  fof(f1703,plain,(
% 2.11/0.71    ~v1_xboole_0(u1_struct_0(sK6)) | ~l1_pre_topc(sK6) | ~l1_pre_topc(sK6) | ~spl10_52),
% 2.11/0.71    inference(resolution,[],[f1697,f89])).
% 2.11/0.71  fof(f89,plain,(
% 2.11/0.71    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 2.11/0.71    inference(cnf_transformation,[],[f22])).
% 2.11/0.71  fof(f22,plain,(
% 2.11/0.71    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 2.11/0.71    inference(ennf_transformation,[],[f13])).
% 2.11/0.71  fof(f13,axiom,(
% 2.11/0.71    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 2.11/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).
% 2.11/0.71  fof(f1697,plain,(
% 2.11/0.71    ( ! [X6] : (~m1_pre_topc(sK6,X6) | ~v1_xboole_0(u1_struct_0(X6)) | ~l1_pre_topc(X6)) ) | ~spl10_52),
% 2.11/0.71    inference(resolution,[],[f1553,f172])).
% 2.11/0.71  fof(f172,plain,(
% 2.11/0.71    ( ! [X6,X4,X8,X7,X5,X9] : (~sP0(X4,X5,X6,X7,X8) | ~l1_pre_topc(X9) | ~v1_xboole_0(u1_struct_0(X9)) | ~m1_pre_topc(X8,X9)) )),
% 2.11/0.71    inference(resolution,[],[f95,f144])).
% 2.11/0.71  fof(f144,plain,(
% 2.11/0.71    ( ! [X2,X0,X1] : (~r2_hidden(X2,u1_struct_0(X0)) | ~l1_pre_topc(X1) | ~v1_xboole_0(u1_struct_0(X1)) | ~m1_pre_topc(X0,X1)) )),
% 2.11/0.71    inference(resolution,[],[f91,f114])).
% 2.11/0.71  fof(f114,plain,(
% 2.11/0.71    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | ~r2_hidden(X0,X1)) )),
% 2.11/0.71    inference(cnf_transformation,[],[f47])).
% 2.11/0.71  fof(f47,plain,(
% 2.11/0.71    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.11/0.71    inference(ennf_transformation,[],[f2])).
% 2.11/0.71  fof(f2,axiom,(
% 2.11/0.71    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 2.11/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 2.11/0.71  fof(f91,plain,(
% 2.11/0.71    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.11/0.71    inference(cnf_transformation,[],[f24])).
% 2.11/0.71  fof(f24,plain,(
% 2.11/0.71    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.11/0.71    inference(ennf_transformation,[],[f12])).
% 2.11/0.71  fof(f12,axiom,(
% 2.11/0.71    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.11/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 2.11/0.71  fof(f95,plain,(
% 2.11/0.71    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(sK8(X0,X1,X2,X3,X4),u1_struct_0(X4)) | ~sP0(X0,X1,X2,X3,X4)) )),
% 2.11/0.71    inference(cnf_transformation,[],[f68])).
% 2.11/0.71  fof(f68,plain,(
% 2.11/0.71    ! [X0,X1,X2,X3,X4] : ((k3_funct_2(u1_struct_0(X3),u1_struct_0(X2),X1,sK8(X0,X1,X2,X3,X4)) != k1_funct_1(X0,sK8(X0,X1,X2,X3,X4)) & r2_hidden(sK8(X0,X1,X2,X3,X4),u1_struct_0(X4)) & m1_subset_1(sK8(X0,X1,X2,X3,X4),u1_struct_0(X3))) | ~sP0(X0,X1,X2,X3,X4))),
% 2.11/0.71    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f66,f67])).
% 2.11/0.71  fof(f67,plain,(
% 2.11/0.71    ! [X4,X3,X2,X1,X0] : (? [X5] : (k3_funct_2(u1_struct_0(X3),u1_struct_0(X2),X1,X5) != k1_funct_1(X0,X5) & r2_hidden(X5,u1_struct_0(X4)) & m1_subset_1(X5,u1_struct_0(X3))) => (k3_funct_2(u1_struct_0(X3),u1_struct_0(X2),X1,sK8(X0,X1,X2,X3,X4)) != k1_funct_1(X0,sK8(X0,X1,X2,X3,X4)) & r2_hidden(sK8(X0,X1,X2,X3,X4),u1_struct_0(X4)) & m1_subset_1(sK8(X0,X1,X2,X3,X4),u1_struct_0(X3))))),
% 2.11/0.71    introduced(choice_axiom,[])).
% 2.11/0.71  fof(f66,plain,(
% 2.11/0.71    ! [X0,X1,X2,X3,X4] : (? [X5] : (k3_funct_2(u1_struct_0(X3),u1_struct_0(X2),X1,X5) != k1_funct_1(X0,X5) & r2_hidden(X5,u1_struct_0(X4)) & m1_subset_1(X5,u1_struct_0(X3))) | ~sP0(X0,X1,X2,X3,X4))),
% 2.11/0.71    inference(rectify,[],[f65])).
% 2.11/0.71  fof(f65,plain,(
% 2.11/0.71    ! [X4,X3,X0,X1,X2] : (? [X5] : (k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(X1))) | ~sP0(X4,X3,X0,X1,X2))),
% 2.11/0.71    inference(nnf_transformation,[],[f52])).
% 2.11/0.71  fof(f52,plain,(
% 2.11/0.71    ! [X4,X3,X0,X1,X2] : (? [X5] : (k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(X1))) | ~sP0(X4,X3,X0,X1,X2))),
% 2.11/0.71    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.11/0.71  fof(f1553,plain,(
% 2.11/0.71    sP0(k4_tmap_1(sK5,sK6),k4_tmap_1(sK5,sK5),sK5,sK5,sK6) | ~spl10_52),
% 2.11/0.71    inference(avatar_component_clause,[],[f1551])).
% 2.11/0.71  fof(f1551,plain,(
% 2.11/0.71    spl10_52 <=> sP0(k4_tmap_1(sK5,sK6),k4_tmap_1(sK5,sK5),sK5,sK5,sK6)),
% 2.11/0.71    introduced(avatar_definition,[new_symbols(naming,[spl10_52])])).
% 2.11/0.71  fof(f1601,plain,(
% 2.11/0.71    ~spl10_51),
% 2.11/0.71    inference(avatar_contradiction_clause,[],[f1600])).
% 2.11/0.71  fof(f1600,plain,(
% 2.11/0.71    $false | ~spl10_51),
% 2.11/0.71    inference(subsumption_resolution,[],[f1568,f199])).
% 2.11/0.71  fof(f199,plain,(
% 2.11/0.71    r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,sK7)),
% 2.11/0.71    inference(subsumption_resolution,[],[f198,f84])).
% 2.11/0.71  fof(f84,plain,(
% 2.11/0.71    v1_funct_1(sK7)),
% 2.11/0.71    inference(cnf_transformation,[],[f64])).
% 2.11/0.71  fof(f198,plain,(
% 2.11/0.71    r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,sK7) | ~v1_funct_1(sK7)),
% 2.11/0.71    inference(subsumption_resolution,[],[f194,f85])).
% 2.11/0.71  fof(f85,plain,(
% 2.11/0.71    v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK5))),
% 2.11/0.71    inference(cnf_transformation,[],[f64])).
% 2.11/0.71  fof(f194,plain,(
% 2.11/0.71    r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,sK7) | ~v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK5)) | ~v1_funct_1(sK7)),
% 2.11/0.71    inference(resolution,[],[f122,f86])).
% 2.11/0.71  fof(f86,plain,(
% 2.11/0.71    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5))))),
% 2.11/0.71    inference(cnf_transformation,[],[f64])).
% 2.11/0.71  fof(f122,plain,(
% 2.11/0.71    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_funct_2(X0,X1,X3,X3) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.11/0.71    inference(duplicate_literal_removal,[],[f121])).
% 2.11/0.71  fof(f121,plain,(
% 2.11/0.71    ( ! [X0,X3,X1] : (r2_funct_2(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.11/0.71    inference(equality_resolution,[],[f116])).
% 2.11/0.71  fof(f116,plain,(
% 2.11/0.71    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.11/0.71    inference(cnf_transformation,[],[f76])).
% 2.11/0.71  fof(f76,plain,(
% 2.11/0.71    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.11/0.71    inference(nnf_transformation,[],[f49])).
% 2.11/0.71  fof(f49,plain,(
% 2.11/0.71    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.11/0.71    inference(flattening,[],[f48])).
% 2.11/0.71  fof(f48,plain,(
% 2.11/0.71    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.11/0.71    inference(ennf_transformation,[],[f4])).
% 2.11/0.71  fof(f4,axiom,(
% 2.11/0.71    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 2.11/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).
% 2.11/0.71  fof(f1568,plain,(
% 2.11/0.71    ~r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,sK7) | ~spl10_51),
% 2.11/0.71    inference(backward_demodulation,[],[f88,f1567])).
% 2.11/0.71  fof(f1567,plain,(
% 2.11/0.71    k4_tmap_1(sK5,sK6) = sK7 | ~spl10_51),
% 2.11/0.71    inference(subsumption_resolution,[],[f1566,f151])).
% 2.11/0.71  fof(f151,plain,(
% 2.11/0.71    sP1(sK5,sK6)),
% 2.11/0.71    inference(subsumption_resolution,[],[f150,f79])).
% 2.11/0.71  fof(f79,plain,(
% 2.11/0.71    ~v2_struct_0(sK5)),
% 2.11/0.71    inference(cnf_transformation,[],[f64])).
% 2.11/0.71  fof(f150,plain,(
% 2.11/0.71    sP1(sK5,sK6) | v2_struct_0(sK5)),
% 2.11/0.71    inference(subsumption_resolution,[],[f149,f80])).
% 2.11/0.71  fof(f80,plain,(
% 2.11/0.71    v2_pre_topc(sK5)),
% 2.11/0.71    inference(cnf_transformation,[],[f64])).
% 2.11/0.71  fof(f149,plain,(
% 2.11/0.71    sP1(sK5,sK6) | ~v2_pre_topc(sK5) | v2_struct_0(sK5)),
% 2.11/0.71    inference(subsumption_resolution,[],[f146,f81])).
% 2.11/0.71  fof(f146,plain,(
% 2.11/0.71    sP1(sK5,sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5)),
% 2.11/0.71    inference(resolution,[],[f107,f83])).
% 2.11/0.71  fof(f107,plain,(
% 2.11/0.71    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | sP1(X0,X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.11/0.71    inference(cnf_transformation,[],[f55])).
% 2.11/0.71  fof(f55,plain,(
% 2.11/0.71    ! [X0,X1] : (sP1(X0,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.11/0.71    inference(definition_folding,[],[f44,f54])).
% 2.11/0.71  fof(f54,plain,(
% 2.11/0.71    ! [X0,X1] : ((m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))) | ~sP1(X0,X1))),
% 2.11/0.71    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 2.11/0.71  fof(f44,plain,(
% 2.11/0.71    ! [X0,X1] : ((m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.11/0.71    inference(flattening,[],[f43])).
% 2.11/0.71  fof(f43,plain,(
% 2.11/0.71    ! [X0,X1] : ((m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.11/0.71    inference(ennf_transformation,[],[f11])).
% 2.11/0.71  fof(f11,axiom,(
% 2.11/0.71    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))))),
% 2.11/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_tmap_1)).
% 2.11/0.71  fof(f1566,plain,(
% 2.11/0.71    k4_tmap_1(sK5,sK6) = sK7 | ~sP1(sK5,sK6) | ~spl10_51),
% 2.11/0.71    inference(subsumption_resolution,[],[f1565,f84])).
% 2.11/0.71  fof(f1565,plain,(
% 2.11/0.71    k4_tmap_1(sK5,sK6) = sK7 | ~v1_funct_1(sK7) | ~sP1(sK5,sK6) | ~spl10_51),
% 2.11/0.71    inference(subsumption_resolution,[],[f1564,f85])).
% 2.11/0.71  fof(f1564,plain,(
% 2.11/0.71    k4_tmap_1(sK5,sK6) = sK7 | ~v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK5)) | ~v1_funct_1(sK7) | ~sP1(sK5,sK6) | ~spl10_51),
% 2.11/0.71    inference(subsumption_resolution,[],[f1556,f86])).
% 2.11/0.71  fof(f1556,plain,(
% 2.11/0.71    k4_tmap_1(sK5,sK6) = sK7 | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5)))) | ~v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK5)) | ~v1_funct_1(sK7) | ~sP1(sK5,sK6) | ~spl10_51),
% 2.11/0.71    inference(resolution,[],[f1549,f352])).
% 2.11/0.71  fof(f352,plain,(
% 2.11/0.71    ( ! [X6,X8,X7] : (~r2_funct_2(u1_struct_0(X6),u1_struct_0(X7),X8,k4_tmap_1(X7,X6)) | k4_tmap_1(X7,X6) = X8 | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(X7)))) | ~v1_funct_2(X8,u1_struct_0(X6),u1_struct_0(X7)) | ~v1_funct_1(X8) | ~sP1(X7,X6)) )),
% 2.11/0.71    inference(subsumption_resolution,[],[f351,f104])).
% 2.11/0.71  fof(f104,plain,(
% 2.11/0.71    ( ! [X0,X1] : (v1_funct_1(k4_tmap_1(X0,X1)) | ~sP1(X0,X1)) )),
% 2.11/0.71    inference(cnf_transformation,[],[f69])).
% 2.11/0.71  fof(f69,plain,(
% 2.11/0.71    ! [X0,X1] : ((m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))) | ~sP1(X0,X1))),
% 2.11/0.71    inference(nnf_transformation,[],[f54])).
% 2.11/0.71  fof(f351,plain,(
% 2.11/0.71    ( ! [X6,X8,X7] : (~r2_funct_2(u1_struct_0(X6),u1_struct_0(X7),X8,k4_tmap_1(X7,X6)) | k4_tmap_1(X7,X6) = X8 | ~v1_funct_1(k4_tmap_1(X7,X6)) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(X7)))) | ~v1_funct_2(X8,u1_struct_0(X6),u1_struct_0(X7)) | ~v1_funct_1(X8) | ~sP1(X7,X6)) )),
% 2.11/0.71    inference(subsumption_resolution,[],[f346,f105])).
% 2.11/0.71  fof(f105,plain,(
% 2.11/0.71    ( ! [X0,X1] : (v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) | ~sP1(X0,X1)) )),
% 2.11/0.71    inference(cnf_transformation,[],[f69])).
% 2.11/0.71  fof(f346,plain,(
% 2.11/0.71    ( ! [X6,X8,X7] : (~r2_funct_2(u1_struct_0(X6),u1_struct_0(X7),X8,k4_tmap_1(X7,X6)) | k4_tmap_1(X7,X6) = X8 | ~v1_funct_2(k4_tmap_1(X7,X6),u1_struct_0(X6),u1_struct_0(X7)) | ~v1_funct_1(k4_tmap_1(X7,X6)) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(X7)))) | ~v1_funct_2(X8,u1_struct_0(X6),u1_struct_0(X7)) | ~v1_funct_1(X8) | ~sP1(X7,X6)) )),
% 2.11/0.71    inference(resolution,[],[f115,f106])).
% 2.11/0.71  fof(f106,plain,(
% 2.11/0.71    ( ! [X0,X1] : (m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~sP1(X0,X1)) )),
% 2.11/0.71    inference(cnf_transformation,[],[f69])).
% 2.11/0.71  fof(f115,plain,(
% 2.11/0.71    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_funct_2(X0,X1,X2,X3) | X2 = X3 | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.11/0.71    inference(cnf_transformation,[],[f76])).
% 2.11/0.71  fof(f1549,plain,(
% 2.11/0.71    r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,k4_tmap_1(sK5,sK6)) | ~spl10_51),
% 2.11/0.71    inference(avatar_component_clause,[],[f1547])).
% 2.11/0.71  fof(f1547,plain,(
% 2.11/0.71    spl10_51 <=> r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,k4_tmap_1(sK5,sK6))),
% 2.11/0.71    introduced(avatar_definition,[new_symbols(naming,[spl10_51])])).
% 2.11/0.71  fof(f88,plain,(
% 2.11/0.71    ~r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),k4_tmap_1(sK5,sK6),sK7)),
% 2.11/0.71    inference(cnf_transformation,[],[f64])).
% 2.11/0.71  fof(f1554,plain,(
% 2.11/0.71    spl10_51 | spl10_52 | ~spl10_11 | ~spl10_12 | ~spl10_29 | ~spl10_32 | ~spl10_33 | ~spl10_48),
% 2.11/0.71    inference(avatar_split_clause,[],[f1545,f1218,f858,f853,f775,f298,f294,f1551,f1547])).
% 2.11/0.71  fof(f294,plain,(
% 2.11/0.71    spl10_11 <=> v1_funct_1(k4_tmap_1(sK5,sK6))),
% 2.11/0.71    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).
% 2.11/0.71  fof(f298,plain,(
% 2.11/0.71    spl10_12 <=> v1_funct_2(k4_tmap_1(sK5,sK6),u1_struct_0(sK6),u1_struct_0(sK5))),
% 2.11/0.71    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).
% 2.11/0.71  fof(f775,plain,(
% 2.11/0.71    spl10_29 <=> v1_funct_1(k4_tmap_1(sK5,sK5))),
% 2.11/0.71    introduced(avatar_definition,[new_symbols(naming,[spl10_29])])).
% 2.11/0.71  fof(f853,plain,(
% 2.11/0.71    spl10_32 <=> v1_funct_2(k4_tmap_1(sK5,sK5),u1_struct_0(sK5),u1_struct_0(sK5))),
% 2.11/0.71    introduced(avatar_definition,[new_symbols(naming,[spl10_32])])).
% 2.11/0.71  fof(f858,plain,(
% 2.11/0.71    spl10_33 <=> m1_subset_1(k4_tmap_1(sK5,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5))))),
% 2.11/0.71    introduced(avatar_definition,[new_symbols(naming,[spl10_33])])).
% 2.11/0.71  fof(f1218,plain,(
% 2.11/0.71    spl10_48 <=> sK7 = k2_tmap_1(sK5,sK5,k4_tmap_1(sK5,sK5),sK6)),
% 2.11/0.71    introduced(avatar_definition,[new_symbols(naming,[spl10_48])])).
% 2.11/0.71  fof(f1545,plain,(
% 2.11/0.71    sP0(k4_tmap_1(sK5,sK6),k4_tmap_1(sK5,sK5),sK5,sK5,sK6) | r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,k4_tmap_1(sK5,sK6)) | (~spl10_11 | ~spl10_12 | ~spl10_29 | ~spl10_32 | ~spl10_33 | ~spl10_48)),
% 2.11/0.71    inference(subsumption_resolution,[],[f1544,f151])).
% 2.11/0.71  fof(f1544,plain,(
% 2.11/0.71    sP0(k4_tmap_1(sK5,sK6),k4_tmap_1(sK5,sK5),sK5,sK5,sK6) | r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,k4_tmap_1(sK5,sK6)) | ~sP1(sK5,sK6) | (~spl10_11 | ~spl10_12 | ~spl10_29 | ~spl10_32 | ~spl10_33 | ~spl10_48)),
% 2.11/0.71    inference(subsumption_resolution,[],[f1543,f295])).
% 2.11/0.71  fof(f295,plain,(
% 2.11/0.71    v1_funct_1(k4_tmap_1(sK5,sK6)) | ~spl10_11),
% 2.11/0.71    inference(avatar_component_clause,[],[f294])).
% 2.11/0.71  fof(f1543,plain,(
% 2.11/0.71    sP0(k4_tmap_1(sK5,sK6),k4_tmap_1(sK5,sK5),sK5,sK5,sK6) | r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,k4_tmap_1(sK5,sK6)) | ~v1_funct_1(k4_tmap_1(sK5,sK6)) | ~sP1(sK5,sK6) | (~spl10_12 | ~spl10_29 | ~spl10_32 | ~spl10_33 | ~spl10_48)),
% 2.11/0.71    inference(subsumption_resolution,[],[f1537,f299])).
% 2.11/0.71  fof(f299,plain,(
% 2.11/0.71    v1_funct_2(k4_tmap_1(sK5,sK6),u1_struct_0(sK6),u1_struct_0(sK5)) | ~spl10_12),
% 2.11/0.71    inference(avatar_component_clause,[],[f298])).
% 2.11/0.71  fof(f1537,plain,(
% 2.11/0.71    sP0(k4_tmap_1(sK5,sK6),k4_tmap_1(sK5,sK5),sK5,sK5,sK6) | r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,k4_tmap_1(sK5,sK6)) | ~v1_funct_2(k4_tmap_1(sK5,sK6),u1_struct_0(sK6),u1_struct_0(sK5)) | ~v1_funct_1(k4_tmap_1(sK5,sK6)) | ~sP1(sK5,sK6) | (~spl10_29 | ~spl10_32 | ~spl10_33 | ~spl10_48)),
% 2.11/0.71    inference(resolution,[],[f1383,f106])).
% 2.11/0.71  fof(f1383,plain,(
% 2.11/0.71    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5)))) | sP0(X0,k4_tmap_1(sK5,sK5),sK5,sK5,sK6) | r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,X0) | ~v1_funct_2(X0,u1_struct_0(sK6),u1_struct_0(sK5)) | ~v1_funct_1(X0)) ) | (~spl10_29 | ~spl10_32 | ~spl10_33 | ~spl10_48)),
% 2.11/0.71    inference(subsumption_resolution,[],[f1382,f79])).
% 2.11/0.71  fof(f1382,plain,(
% 2.11/0.71    ( ! [X0] : (r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,X0) | sP0(X0,k4_tmap_1(sK5,sK5),sK5,sK5,sK6) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5)))) | ~v1_funct_2(X0,u1_struct_0(sK6),u1_struct_0(sK5)) | ~v1_funct_1(X0) | v2_struct_0(sK5)) ) | (~spl10_29 | ~spl10_32 | ~spl10_33 | ~spl10_48)),
% 2.11/0.71    inference(subsumption_resolution,[],[f1381,f80])).
% 2.11/0.71  fof(f1381,plain,(
% 2.11/0.71    ( ! [X0] : (r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,X0) | sP0(X0,k4_tmap_1(sK5,sK5),sK5,sK5,sK6) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5)))) | ~v1_funct_2(X0,u1_struct_0(sK6),u1_struct_0(sK5)) | ~v1_funct_1(X0) | ~v2_pre_topc(sK5) | v2_struct_0(sK5)) ) | (~spl10_29 | ~spl10_32 | ~spl10_33 | ~spl10_48)),
% 2.11/0.71    inference(subsumption_resolution,[],[f1380,f81])).
% 2.11/0.71  fof(f1380,plain,(
% 2.11/0.71    ( ! [X0] : (r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,X0) | sP0(X0,k4_tmap_1(sK5,sK5),sK5,sK5,sK6) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5)))) | ~v1_funct_2(X0,u1_struct_0(sK6),u1_struct_0(sK5)) | ~v1_funct_1(X0) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5)) ) | (~spl10_29 | ~spl10_32 | ~spl10_33 | ~spl10_48)),
% 2.11/0.71    inference(subsumption_resolution,[],[f1379,f82])).
% 2.11/0.71  fof(f82,plain,(
% 2.11/0.71    ~v2_struct_0(sK6)),
% 2.11/0.71    inference(cnf_transformation,[],[f64])).
% 2.11/0.71  fof(f1379,plain,(
% 2.11/0.71    ( ! [X0] : (r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,X0) | sP0(X0,k4_tmap_1(sK5,sK5),sK5,sK5,sK6) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5)))) | ~v1_funct_2(X0,u1_struct_0(sK6),u1_struct_0(sK5)) | ~v1_funct_1(X0) | v2_struct_0(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5)) ) | (~spl10_29 | ~spl10_32 | ~spl10_33 | ~spl10_48)),
% 2.11/0.71    inference(subsumption_resolution,[],[f1378,f83])).
% 2.11/0.71  fof(f1378,plain,(
% 2.11/0.71    ( ! [X0] : (r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,X0) | sP0(X0,k4_tmap_1(sK5,sK5),sK5,sK5,sK6) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5)))) | ~v1_funct_2(X0,u1_struct_0(sK6),u1_struct_0(sK5)) | ~v1_funct_1(X0) | ~m1_pre_topc(sK6,sK5) | v2_struct_0(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5)) ) | (~spl10_29 | ~spl10_32 | ~spl10_33 | ~spl10_48)),
% 2.76/0.71    inference(subsumption_resolution,[],[f1377,f777])).
% 2.76/0.71  fof(f777,plain,(
% 2.76/0.71    v1_funct_1(k4_tmap_1(sK5,sK5)) | ~spl10_29),
% 2.76/0.71    inference(avatar_component_clause,[],[f775])).
% 2.76/0.71  fof(f1377,plain,(
% 2.76/0.71    ( ! [X0] : (r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,X0) | sP0(X0,k4_tmap_1(sK5,sK5),sK5,sK5,sK6) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5)))) | ~v1_funct_2(X0,u1_struct_0(sK6),u1_struct_0(sK5)) | ~v1_funct_1(X0) | ~v1_funct_1(k4_tmap_1(sK5,sK5)) | ~m1_pre_topc(sK6,sK5) | v2_struct_0(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5)) ) | (~spl10_32 | ~spl10_33 | ~spl10_48)),
% 2.76/0.71    inference(subsumption_resolution,[],[f1376,f855])).
% 2.76/0.71  fof(f855,plain,(
% 2.76/0.71    v1_funct_2(k4_tmap_1(sK5,sK5),u1_struct_0(sK5),u1_struct_0(sK5)) | ~spl10_32),
% 2.76/0.71    inference(avatar_component_clause,[],[f853])).
% 2.76/0.71  fof(f1376,plain,(
% 2.76/0.71    ( ! [X0] : (r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,X0) | sP0(X0,k4_tmap_1(sK5,sK5),sK5,sK5,sK6) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5)))) | ~v1_funct_2(X0,u1_struct_0(sK6),u1_struct_0(sK5)) | ~v1_funct_1(X0) | ~v1_funct_2(k4_tmap_1(sK5,sK5),u1_struct_0(sK5),u1_struct_0(sK5)) | ~v1_funct_1(k4_tmap_1(sK5,sK5)) | ~m1_pre_topc(sK6,sK5) | v2_struct_0(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5)) ) | (~spl10_33 | ~spl10_48)),
% 2.76/0.71    inference(subsumption_resolution,[],[f1375,f860])).
% 2.76/0.71  fof(f860,plain,(
% 2.76/0.71    m1_subset_1(k4_tmap_1(sK5,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5)))) | ~spl10_33),
% 2.76/0.71    inference(avatar_component_clause,[],[f858])).
% 2.76/0.71  fof(f1375,plain,(
% 2.76/0.71    ( ! [X0] : (r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,X0) | sP0(X0,k4_tmap_1(sK5,sK5),sK5,sK5,sK6) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5)))) | ~v1_funct_2(X0,u1_struct_0(sK6),u1_struct_0(sK5)) | ~v1_funct_1(X0) | ~m1_subset_1(k4_tmap_1(sK5,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5)))) | ~v1_funct_2(k4_tmap_1(sK5,sK5),u1_struct_0(sK5),u1_struct_0(sK5)) | ~v1_funct_1(k4_tmap_1(sK5,sK5)) | ~m1_pre_topc(sK6,sK5) | v2_struct_0(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5)) ) | ~spl10_48),
% 2.76/0.71    inference(duplicate_literal_removal,[],[f1374])).
% 2.76/0.71  fof(f1374,plain,(
% 2.76/0.71    ( ! [X0] : (r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,X0) | sP0(X0,k4_tmap_1(sK5,sK5),sK5,sK5,sK6) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5)))) | ~v1_funct_2(X0,u1_struct_0(sK6),u1_struct_0(sK5)) | ~v1_funct_1(X0) | ~m1_subset_1(k4_tmap_1(sK5,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5)))) | ~v1_funct_2(k4_tmap_1(sK5,sK5),u1_struct_0(sK5),u1_struct_0(sK5)) | ~v1_funct_1(k4_tmap_1(sK5,sK5)) | ~m1_pre_topc(sK6,sK5) | v2_struct_0(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5)) ) | ~spl10_48),
% 2.76/0.71    inference(superposition,[],[f97,f1220])).
% 2.76/0.71  fof(f1220,plain,(
% 2.76/0.71    sK7 = k2_tmap_1(sK5,sK5,k4_tmap_1(sK5,sK5),sK6) | ~spl10_48),
% 2.76/0.71    inference(avatar_component_clause,[],[f1218])).
% 2.76/0.71  fof(f97,plain,(
% 2.76/0.71    ( ! [X4,X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | sP0(X4,X3,X0,X1,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.76/0.71    inference(cnf_transformation,[],[f53])).
% 2.76/0.71  fof(f53,plain,(
% 2.76/0.71    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | sP0(X4,X3,X0,X1,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3)) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.76/0.71    inference(definition_folding,[],[f30,f52])).
% 2.76/0.71  fof(f30,plain,(
% 2.76/0.71    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | ? [X5] : (k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3)) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.76/0.71    inference(flattening,[],[f29])).
% 2.76/0.71  fof(f29,plain,(
% 2.76/0.71    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | ? [X5] : ((k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5) & r2_hidden(X5,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X1)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3))) | (~m1_pre_topc(X2,X1) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.76/0.71    inference(ennf_transformation,[],[f14])).
% 2.76/0.71  fof(f14,axiom,(
% 2.76/0.71    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4)) => (! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => (r2_hidden(X5,u1_struct_0(X2)) => k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) = k1_funct_1(X4,X5))) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)))))))),
% 2.76/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_tmap_1)).
% 2.76/0.71  fof(f1422,plain,(
% 2.76/0.71    spl10_6 | ~spl10_13),
% 2.76/0.71    inference(avatar_contradiction_clause,[],[f1421])).
% 2.76/0.71  fof(f1421,plain,(
% 2.76/0.71    $false | (spl10_6 | ~spl10_13)),
% 2.76/0.71    inference(subsumption_resolution,[],[f1420,f126])).
% 2.76/0.71  fof(f1420,plain,(
% 2.76/0.71    ~l1_pre_topc(sK6) | (spl10_6 | ~spl10_13)),
% 2.76/0.71    inference(resolution,[],[f1419,f89])).
% 2.76/0.71  fof(f1419,plain,(
% 2.76/0.71    ~m1_pre_topc(sK6,sK6) | (spl10_6 | ~spl10_13)),
% 2.76/0.71    inference(subsumption_resolution,[],[f1418,f1410])).
% 2.76/0.71  fof(f1410,plain,(
% 2.76/0.71    sK9(sK7,k4_tmap_1(sK5,sK6),u1_struct_0(sK6)) != k1_funct_1(sK7,sK9(sK7,k4_tmap_1(sK5,sK6),u1_struct_0(sK6))) | (spl10_6 | ~spl10_13)),
% 2.76/0.71    inference(subsumption_resolution,[],[f1409,f314])).
% 2.76/0.71  fof(f314,plain,(
% 2.76/0.71    ~sP2(sK7,k4_tmap_1(sK5,sK6),u1_struct_0(sK6)) | ~spl10_13),
% 2.76/0.71    inference(subsumption_resolution,[],[f312,f88])).
% 2.76/0.71  fof(f312,plain,(
% 2.76/0.71    ~sP2(sK7,k4_tmap_1(sK5,sK6),u1_struct_0(sK6)) | r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),k4_tmap_1(sK5,sK6),sK7) | ~spl10_13),
% 2.76/0.71    inference(resolution,[],[f304,f109])).
% 2.76/0.71  fof(f109,plain,(
% 2.76/0.71    ( ! [X2,X0,X3,X1] : (~sP3(X0,X1,X2,X3) | ~sP2(X2,X1,X0) | r2_funct_2(X0,X3,X1,X2)) )),
% 2.76/0.71    inference(cnf_transformation,[],[f71])).
% 2.76/0.71  fof(f71,plain,(
% 2.76/0.71    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X3,X1,X2) | ~sP2(X2,X1,X0)) & (sP2(X2,X1,X0) | ~r2_funct_2(X0,X3,X1,X2))) | ~sP3(X0,X1,X2,X3))),
% 2.76/0.71    inference(rectify,[],[f70])).
% 2.76/0.71  fof(f70,plain,(
% 2.76/0.71    ! [X0,X2,X3,X1] : (((r2_funct_2(X0,X1,X2,X3) | ~sP2(X3,X2,X0)) & (sP2(X3,X2,X0) | ~r2_funct_2(X0,X1,X2,X3))) | ~sP3(X0,X2,X3,X1))),
% 2.76/0.71    inference(nnf_transformation,[],[f57])).
% 2.76/0.71  fof(f57,plain,(
% 2.76/0.71    ! [X0,X2,X3,X1] : ((r2_funct_2(X0,X1,X2,X3) <=> sP2(X3,X2,X0)) | ~sP3(X0,X2,X3,X1))),
% 2.76/0.71    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 2.76/0.71  fof(f304,plain,(
% 2.76/0.71    sP3(u1_struct_0(sK6),k4_tmap_1(sK5,sK6),sK7,u1_struct_0(sK5)) | ~spl10_13),
% 2.76/0.71    inference(avatar_component_clause,[],[f302])).
% 2.76/0.71  fof(f302,plain,(
% 2.76/0.71    spl10_13 <=> sP3(u1_struct_0(sK6),k4_tmap_1(sK5,sK6),sK7,u1_struct_0(sK5))),
% 2.76/0.71    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).
% 2.76/0.71  fof(f1409,plain,(
% 2.76/0.71    sK9(sK7,k4_tmap_1(sK5,sK6),u1_struct_0(sK6)) != k1_funct_1(sK7,sK9(sK7,k4_tmap_1(sK5,sK6),u1_struct_0(sK6))) | sP2(sK7,k4_tmap_1(sK5,sK6),u1_struct_0(sK6)) | (spl10_6 | ~spl10_13)),
% 2.76/0.71    inference(superposition,[],[f112,f1405])).
% 2.76/0.71  fof(f1405,plain,(
% 2.76/0.71    sK9(sK7,k4_tmap_1(sK5,sK6),u1_struct_0(sK6)) = k1_funct_1(k4_tmap_1(sK5,sK6),sK9(sK7,k4_tmap_1(sK5,sK6),u1_struct_0(sK6))) | (spl10_6 | ~spl10_13)),
% 2.76/0.71    inference(resolution,[],[f1334,f314])).
% 2.76/0.71  fof(f1334,plain,(
% 2.76/0.71    ( ! [X0,X1] : (sP2(X0,X1,u1_struct_0(sK6)) | sK9(X0,X1,u1_struct_0(sK6)) = k1_funct_1(k4_tmap_1(sK5,sK6),sK9(X0,X1,u1_struct_0(sK6)))) ) | spl10_6),
% 2.76/0.71    inference(subsumption_resolution,[],[f1268,f182])).
% 2.76/0.71  fof(f182,plain,(
% 2.76/0.71    ~v1_xboole_0(u1_struct_0(sK6)) | spl10_6),
% 2.76/0.71    inference(avatar_component_clause,[],[f181])).
% 2.76/0.71  fof(f1268,plain,(
% 2.76/0.71    ( ! [X0,X1] : (sK9(X0,X1,u1_struct_0(sK6)) = k1_funct_1(k4_tmap_1(sK5,sK6),sK9(X0,X1,u1_struct_0(sK6))) | v1_xboole_0(u1_struct_0(sK6)) | sP2(X0,X1,u1_struct_0(sK6))) )),
% 2.76/0.71    inference(subsumption_resolution,[],[f1267,f79])).
% 2.76/0.71  fof(f1267,plain,(
% 2.76/0.71    ( ! [X0,X1] : (sK9(X0,X1,u1_struct_0(sK6)) = k1_funct_1(k4_tmap_1(sK5,sK6),sK9(X0,X1,u1_struct_0(sK6))) | v2_struct_0(sK5) | v1_xboole_0(u1_struct_0(sK6)) | sP2(X0,X1,u1_struct_0(sK6))) )),
% 2.76/0.71    inference(subsumption_resolution,[],[f1266,f80])).
% 2.76/0.71  fof(f1266,plain,(
% 2.76/0.71    ( ! [X0,X1] : (sK9(X0,X1,u1_struct_0(sK6)) = k1_funct_1(k4_tmap_1(sK5,sK6),sK9(X0,X1,u1_struct_0(sK6))) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | v1_xboole_0(u1_struct_0(sK6)) | sP2(X0,X1,u1_struct_0(sK6))) )),
% 2.76/0.71    inference(subsumption_resolution,[],[f1265,f81])).
% 2.76/0.71  fof(f1265,plain,(
% 2.76/0.71    ( ! [X0,X1] : (sK9(X0,X1,u1_struct_0(sK6)) = k1_funct_1(k4_tmap_1(sK5,sK6),sK9(X0,X1,u1_struct_0(sK6))) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | v1_xboole_0(u1_struct_0(sK6)) | sP2(X0,X1,u1_struct_0(sK6))) )),
% 2.76/0.71    inference(subsumption_resolution,[],[f368,f82])).
% 2.76/0.71  fof(f368,plain,(
% 2.76/0.71    ( ! [X0,X1] : (sK9(X0,X1,u1_struct_0(sK6)) = k1_funct_1(k4_tmap_1(sK5,sK6),sK9(X0,X1,u1_struct_0(sK6))) | v2_struct_0(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | v1_xboole_0(u1_struct_0(sK6)) | sP2(X0,X1,u1_struct_0(sK6))) )),
% 2.76/0.71    inference(resolution,[],[f233,f83])).
% 2.76/0.71  fof(f233,plain,(
% 2.76/0.71    ( ! [X19,X17,X20,X18] : (~m1_pre_topc(X18,X17) | sK9(X19,X20,u1_struct_0(X18)) = k1_funct_1(k4_tmap_1(X17,X18),sK9(X19,X20,u1_struct_0(X18))) | v2_struct_0(X18) | ~l1_pre_topc(X17) | ~v2_pre_topc(X17) | v2_struct_0(X17) | v1_xboole_0(u1_struct_0(X18)) | sP2(X19,X20,u1_struct_0(X18))) )),
% 2.76/0.71    inference(subsumption_resolution,[],[f228,f190])).
% 2.76/0.71  fof(f190,plain,(
% 2.76/0.71    ( ! [X6,X8,X7,X9] : (m1_subset_1(sK9(X6,X7,u1_struct_0(X8)),u1_struct_0(X9)) | ~m1_pre_topc(X8,X9) | v2_struct_0(X8) | ~l1_pre_topc(X9) | v2_struct_0(X9) | sP2(X6,X7,u1_struct_0(X8))) )),
% 2.76/0.71    inference(resolution,[],[f100,f111])).
% 2.76/0.71  fof(f111,plain,(
% 2.76/0.71    ( ! [X2,X0,X1] : (m1_subset_1(sK9(X0,X1,X2),X2) | sP2(X0,X1,X2)) )),
% 2.76/0.71    inference(cnf_transformation,[],[f75])).
% 2.76/0.71  fof(f75,plain,(
% 2.76/0.71    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | (k1_funct_1(X1,sK9(X0,X1,X2)) != k1_funct_1(X0,sK9(X0,X1,X2)) & m1_subset_1(sK9(X0,X1,X2),X2))) & (! [X4] : (k1_funct_1(X1,X4) = k1_funct_1(X0,X4) | ~m1_subset_1(X4,X2)) | ~sP2(X0,X1,X2)))),
% 2.76/0.71    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f73,f74])).
% 2.76/0.71  fof(f74,plain,(
% 2.76/0.71    ! [X2,X1,X0] : (? [X3] : (k1_funct_1(X1,X3) != k1_funct_1(X0,X3) & m1_subset_1(X3,X2)) => (k1_funct_1(X1,sK9(X0,X1,X2)) != k1_funct_1(X0,sK9(X0,X1,X2)) & m1_subset_1(sK9(X0,X1,X2),X2)))),
% 2.76/0.71    introduced(choice_axiom,[])).
% 2.76/0.71  fof(f73,plain,(
% 2.76/0.71    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ? [X3] : (k1_funct_1(X1,X3) != k1_funct_1(X0,X3) & m1_subset_1(X3,X2))) & (! [X4] : (k1_funct_1(X1,X4) = k1_funct_1(X0,X4) | ~m1_subset_1(X4,X2)) | ~sP2(X0,X1,X2)))),
% 2.76/0.71    inference(rectify,[],[f72])).
% 2.76/0.71  fof(f72,plain,(
% 2.76/0.71    ! [X3,X2,X0] : ((sP2(X3,X2,X0) | ? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & m1_subset_1(X4,X0))) & (! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0)) | ~sP2(X3,X2,X0)))),
% 2.76/0.71    inference(nnf_transformation,[],[f56])).
% 2.76/0.71  fof(f56,plain,(
% 2.76/0.71    ! [X3,X2,X0] : (sP2(X3,X2,X0) <=> ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0)))),
% 2.76/0.71    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 2.76/0.71  fof(f100,plain,(
% 2.76/0.71    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X1)) | m1_subset_1(X2,u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.76/0.71    inference(cnf_transformation,[],[f36])).
% 2.76/0.71  fof(f36,plain,(
% 2.76/0.71    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.76/0.71    inference(flattening,[],[f35])).
% 2.76/0.71  fof(f35,plain,(
% 2.76/0.71    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.76/0.71    inference(ennf_transformation,[],[f7])).
% 2.76/0.71  fof(f7,axiom,(
% 2.76/0.71    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 2.76/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_pre_topc)).
% 2.76/0.71  fof(f228,plain,(
% 2.76/0.71    ( ! [X19,X17,X20,X18] : (sK9(X19,X20,u1_struct_0(X18)) = k1_funct_1(k4_tmap_1(X17,X18),sK9(X19,X20,u1_struct_0(X18))) | ~m1_subset_1(sK9(X19,X20,u1_struct_0(X18)),u1_struct_0(X17)) | ~m1_pre_topc(X18,X17) | v2_struct_0(X18) | ~l1_pre_topc(X17) | ~v2_pre_topc(X17) | v2_struct_0(X17) | v1_xboole_0(u1_struct_0(X18)) | sP2(X19,X20,u1_struct_0(X18))) )),
% 2.76/0.71    inference(resolution,[],[f99,f142])).
% 2.76/0.71  fof(f142,plain,(
% 2.76/0.71    ( ! [X2,X0,X1] : (r2_hidden(sK9(X0,X1,X2),X2) | v1_xboole_0(X2) | sP2(X0,X1,X2)) )),
% 2.76/0.71    inference(resolution,[],[f111,f103])).
% 2.76/0.71  fof(f103,plain,(
% 2.76/0.71    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 2.76/0.71    inference(cnf_transformation,[],[f42])).
% 2.76/0.71  fof(f42,plain,(
% 2.76/0.71    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.76/0.71    inference(flattening,[],[f41])).
% 2.76/0.71  fof(f41,plain,(
% 2.76/0.71    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.76/0.71    inference(ennf_transformation,[],[f1])).
% 2.76/0.71  fof(f1,axiom,(
% 2.76/0.71    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.76/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 2.76/0.71  fof(f99,plain,(
% 2.76/0.71    ( ! [X2,X0,X1] : (~r2_hidden(X2,u1_struct_0(X1)) | k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.76/0.71    inference(cnf_transformation,[],[f34])).
% 2.76/0.71  fof(f34,plain,(
% 2.76/0.71    ! [X0] : (! [X1] : (! [X2] : (k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~r2_hidden(X2,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.76/0.71    inference(flattening,[],[f33])).
% 2.76/0.71  fof(f33,plain,(
% 2.76/0.71    ! [X0] : (! [X1] : (! [X2] : ((k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~r2_hidden(X2,u1_struct_0(X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.76/0.71    inference(ennf_transformation,[],[f17])).
% 2.76/0.71  fof(f17,axiom,(
% 2.76/0.71    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,u1_struct_0(X1)) => k1_funct_1(k4_tmap_1(X0,X1),X2) = X2))))),
% 2.76/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_tmap_1)).
% 2.76/0.71  fof(f112,plain,(
% 2.76/0.71    ( ! [X2,X0,X1] : (k1_funct_1(X1,sK9(X0,X1,X2)) != k1_funct_1(X0,sK9(X0,X1,X2)) | sP2(X0,X1,X2)) )),
% 2.76/0.71    inference(cnf_transformation,[],[f75])).
% 2.76/0.71  fof(f1418,plain,(
% 2.76/0.71    ~m1_pre_topc(sK6,sK6) | sK9(sK7,k4_tmap_1(sK5,sK6),u1_struct_0(sK6)) = k1_funct_1(sK7,sK9(sK7,k4_tmap_1(sK5,sK6),u1_struct_0(sK6))) | (spl10_6 | ~spl10_13)),
% 2.76/0.71    inference(subsumption_resolution,[],[f1414,f82])).
% 2.76/0.71  fof(f1414,plain,(
% 2.76/0.71    v2_struct_0(sK6) | ~m1_pre_topc(sK6,sK6) | sK9(sK7,k4_tmap_1(sK5,sK6),u1_struct_0(sK6)) = k1_funct_1(sK7,sK9(sK7,k4_tmap_1(sK5,sK6),u1_struct_0(sK6))) | (spl10_6 | ~spl10_13)),
% 2.76/0.71    inference(resolution,[],[f1332,f314])).
% 2.76/0.71  fof(f1332,plain,(
% 2.76/0.71    ( ! [X2,X0,X1] : (sP2(X1,X2,u1_struct_0(X0)) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK6) | sK9(X1,X2,u1_struct_0(X0)) = k1_funct_1(sK7,sK9(X1,X2,u1_struct_0(X0)))) ) | spl10_6),
% 2.76/0.71    inference(subsumption_resolution,[],[f1331,f243])).
% 2.76/0.71  fof(f243,plain,(
% 2.76/0.71    ( ! [X2,X0,X1] : (m1_subset_1(sK9(X1,X2,u1_struct_0(X0)),u1_struct_0(sK5)) | sP2(X1,X2,u1_struct_0(X0)) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK6)) )),
% 2.76/0.71    inference(subsumption_resolution,[],[f242,f79])).
% 2.76/0.71  fof(f242,plain,(
% 2.76/0.71    ( ! [X2,X0,X1] : (v2_struct_0(X0) | sP2(X1,X2,u1_struct_0(X0)) | m1_subset_1(sK9(X1,X2,u1_struct_0(X0)),u1_struct_0(sK5)) | ~m1_pre_topc(X0,sK6) | v2_struct_0(sK5)) )),
% 2.76/0.71    inference(subsumption_resolution,[],[f241,f81])).
% 2.76/0.71  fof(f241,plain,(
% 2.76/0.71    ( ! [X2,X0,X1] : (v2_struct_0(X0) | sP2(X1,X2,u1_struct_0(X0)) | m1_subset_1(sK9(X1,X2,u1_struct_0(X0)),u1_struct_0(sK5)) | ~m1_pre_topc(X0,sK6) | ~l1_pre_topc(sK5) | v2_struct_0(sK5)) )),
% 2.76/0.71    inference(subsumption_resolution,[],[f238,f82])).
% 2.76/0.71  fof(f238,plain,(
% 2.76/0.71    ( ! [X2,X0,X1] : (v2_struct_0(X0) | v2_struct_0(sK6) | sP2(X1,X2,u1_struct_0(X0)) | m1_subset_1(sK9(X1,X2,u1_struct_0(X0)),u1_struct_0(sK5)) | ~m1_pre_topc(X0,sK6) | ~l1_pre_topc(sK5) | v2_struct_0(sK5)) )),
% 2.76/0.71    inference(resolution,[],[f212,f83])).
% 2.76/0.71  fof(f212,plain,(
% 2.76/0.71    ( ! [X4,X2,X0,X3,X1] : (~m1_pre_topc(X1,X4) | v2_struct_0(X0) | v2_struct_0(X1) | sP2(X2,X3,u1_struct_0(X0)) | m1_subset_1(sK9(X2,X3,u1_struct_0(X0)),u1_struct_0(X4)) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X4) | v2_struct_0(X4)) )),
% 2.76/0.71    inference(subsumption_resolution,[],[f211,f90])).
% 2.76/0.71  fof(f211,plain,(
% 2.76/0.71    ( ! [X4,X2,X0,X3,X1] : (~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~l1_pre_topc(X1) | v2_struct_0(X1) | sP2(X2,X3,u1_struct_0(X0)) | m1_subset_1(sK9(X2,X3,u1_struct_0(X0)),u1_struct_0(X4)) | ~m1_pre_topc(X1,X4) | ~l1_pre_topc(X4) | v2_struct_0(X4)) )),
% 2.76/0.71    inference(duplicate_literal_removal,[],[f209])).
% 2.76/0.71  fof(f209,plain,(
% 2.76/0.71    ( ! [X4,X2,X0,X3,X1] : (~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~l1_pre_topc(X1) | v2_struct_0(X1) | sP2(X2,X3,u1_struct_0(X0)) | m1_subset_1(sK9(X2,X3,u1_struct_0(X0)),u1_struct_0(X4)) | ~m1_pre_topc(X1,X4) | v2_struct_0(X1) | ~l1_pre_topc(X4) | v2_struct_0(X4)) )),
% 2.76/0.71    inference(resolution,[],[f190,f100])).
% 2.76/0.71  fof(f1331,plain,(
% 2.76/0.71    ( ! [X2,X0,X1] : (v2_struct_0(X0) | sP2(X1,X2,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK6) | sK9(X1,X2,u1_struct_0(X0)) = k1_funct_1(sK7,sK9(X1,X2,u1_struct_0(X0))) | ~m1_subset_1(sK9(X1,X2,u1_struct_0(X0)),u1_struct_0(sK5))) ) | spl10_6),
% 2.76/0.71    inference(subsumption_resolution,[],[f220,f182])).
% 2.76/0.71  fof(f220,plain,(
% 2.76/0.71    ( ! [X2,X0,X1] : (v2_struct_0(X0) | sP2(X1,X2,u1_struct_0(X0)) | v1_xboole_0(u1_struct_0(sK6)) | ~m1_pre_topc(X0,sK6) | sK9(X1,X2,u1_struct_0(X0)) = k1_funct_1(sK7,sK9(X1,X2,u1_struct_0(X0))) | ~m1_subset_1(sK9(X1,X2,u1_struct_0(X0)),u1_struct_0(sK5))) )),
% 2.76/0.71    inference(subsumption_resolution,[],[f219,f82])).
% 2.76/0.71  fof(f219,plain,(
% 2.76/0.71    ( ! [X2,X0,X1] : (v2_struct_0(X0) | v2_struct_0(sK6) | sP2(X1,X2,u1_struct_0(X0)) | v1_xboole_0(u1_struct_0(sK6)) | ~m1_pre_topc(X0,sK6) | sK9(X1,X2,u1_struct_0(X0)) = k1_funct_1(sK7,sK9(X1,X2,u1_struct_0(X0))) | ~m1_subset_1(sK9(X1,X2,u1_struct_0(X0)),u1_struct_0(sK5))) )),
% 2.76/0.71    inference(subsumption_resolution,[],[f217,f126])).
% 2.76/0.71  fof(f217,plain,(
% 2.76/0.71    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(sK6) | v2_struct_0(sK6) | sP2(X1,X2,u1_struct_0(X0)) | v1_xboole_0(u1_struct_0(sK6)) | ~m1_pre_topc(X0,sK6) | sK9(X1,X2,u1_struct_0(X0)) = k1_funct_1(sK7,sK9(X1,X2,u1_struct_0(X0))) | ~m1_subset_1(sK9(X1,X2,u1_struct_0(X0)),u1_struct_0(sK5))) )),
% 2.76/0.71    inference(resolution,[],[f210,f87])).
% 2.76/0.71  fof(f87,plain,(
% 2.76/0.71    ( ! [X3] : (~r2_hidden(X3,u1_struct_0(sK6)) | k1_funct_1(sK7,X3) = X3 | ~m1_subset_1(X3,u1_struct_0(sK5))) )),
% 2.76/0.71    inference(cnf_transformation,[],[f64])).
% 2.76/0.71  fof(f210,plain,(
% 2.76/0.71    ( ! [X6,X8,X7,X5] : (r2_hidden(sK9(X7,X8,u1_struct_0(X5)),u1_struct_0(X6)) | v2_struct_0(X5) | ~l1_pre_topc(X6) | v2_struct_0(X6) | sP2(X7,X8,u1_struct_0(X5)) | v1_xboole_0(u1_struct_0(X6)) | ~m1_pre_topc(X5,X6)) )),
% 2.76/0.71    inference(resolution,[],[f190,f103])).
% 2.76/0.71  fof(f1326,plain,(
% 2.76/0.71    ~spl10_13 | ~spl10_29 | ~spl10_32 | ~spl10_33 | spl10_47),
% 2.76/0.71    inference(avatar_contradiction_clause,[],[f1325])).
% 2.76/0.71  fof(f1325,plain,(
% 2.76/0.71    $false | (~spl10_13 | ~spl10_29 | ~spl10_32 | ~spl10_33 | spl10_47)),
% 2.76/0.71    inference(subsumption_resolution,[],[f1324,f126])).
% 2.76/0.71  fof(f1324,plain,(
% 2.76/0.71    ~l1_pre_topc(sK6) | (~spl10_13 | ~spl10_29 | ~spl10_32 | ~spl10_33 | spl10_47)),
% 2.76/0.71    inference(resolution,[],[f1323,f89])).
% 2.76/0.71  fof(f1323,plain,(
% 2.76/0.71    ~m1_pre_topc(sK6,sK6) | (~spl10_13 | ~spl10_29 | ~spl10_32 | ~spl10_33 | spl10_47)),
% 2.76/0.71    inference(subsumption_resolution,[],[f1322,f1308])).
% 2.76/0.71  fof(f1308,plain,(
% 2.76/0.71    sK9(sK7,k4_tmap_1(sK5,sK6),u1_struct_0(sK6)) != k1_funct_1(sK7,sK9(sK7,k4_tmap_1(sK5,sK6),u1_struct_0(sK6))) | (~spl10_13 | ~spl10_29 | ~spl10_32 | ~spl10_33 | spl10_47)),
% 2.76/0.71    inference(subsumption_resolution,[],[f1307,f314])).
% 2.76/0.71  fof(f1307,plain,(
% 2.76/0.71    sK9(sK7,k4_tmap_1(sK5,sK6),u1_struct_0(sK6)) != k1_funct_1(sK7,sK9(sK7,k4_tmap_1(sK5,sK6),u1_struct_0(sK6))) | sP2(sK7,k4_tmap_1(sK5,sK6),u1_struct_0(sK6)) | (~spl10_13 | ~spl10_29 | ~spl10_32 | ~spl10_33 | spl10_47)),
% 2.76/0.71    inference(superposition,[],[f112,f1303])).
% 2.76/0.71  fof(f1303,plain,(
% 2.76/0.71    sK9(sK7,k4_tmap_1(sK5,sK6),u1_struct_0(sK6)) = k1_funct_1(k4_tmap_1(sK5,sK6),sK9(sK7,k4_tmap_1(sK5,sK6),u1_struct_0(sK6))) | (~spl10_13 | ~spl10_29 | ~spl10_32 | ~spl10_33 | spl10_47)),
% 2.76/0.71    inference(resolution,[],[f1269,f314])).
% 2.76/0.71  fof(f1269,plain,(
% 2.76/0.71    ( ! [X0,X1] : (sP2(X0,X1,u1_struct_0(sK6)) | sK9(X0,X1,u1_struct_0(sK6)) = k1_funct_1(k4_tmap_1(sK5,sK6),sK9(X0,X1,u1_struct_0(sK6)))) ) | (~spl10_29 | ~spl10_32 | ~spl10_33 | spl10_47)),
% 2.76/0.71    inference(subsumption_resolution,[],[f1268,f1252])).
% 2.76/0.71  fof(f1252,plain,(
% 2.76/0.71    ~v1_xboole_0(u1_struct_0(sK6)) | (~spl10_29 | ~spl10_32 | ~spl10_33 | spl10_47)),
% 2.76/0.71    inference(subsumption_resolution,[],[f1245,f126])).
% 2.76/0.71  fof(f1245,plain,(
% 2.76/0.71    ~v1_xboole_0(u1_struct_0(sK6)) | ~l1_pre_topc(sK6) | (~spl10_29 | ~spl10_32 | ~spl10_33 | spl10_47)),
% 2.76/0.71    inference(duplicate_literal_removal,[],[f1244])).
% 2.76/0.71  fof(f1244,plain,(
% 2.76/0.71    ~v1_xboole_0(u1_struct_0(sK6)) | ~l1_pre_topc(sK6) | ~l1_pre_topc(sK6) | (~spl10_29 | ~spl10_32 | ~spl10_33 | spl10_47)),
% 2.76/0.71    inference(resolution,[],[f1241,f89])).
% 2.76/0.71  fof(f1241,plain,(
% 2.76/0.71    ( ! [X6] : (~m1_pre_topc(sK6,X6) | ~v1_xboole_0(u1_struct_0(X6)) | ~l1_pre_topc(X6)) ) | (~spl10_29 | ~spl10_32 | ~spl10_33 | spl10_47)),
% 2.76/0.71    inference(resolution,[],[f1234,f172])).
% 2.76/0.71  fof(f1234,plain,(
% 2.76/0.71    sP0(sK7,k4_tmap_1(sK5,sK5),sK5,sK5,sK6) | (~spl10_29 | ~spl10_32 | ~spl10_33 | spl10_47)),
% 2.76/0.71    inference(subsumption_resolution,[],[f1233,f79])).
% 2.76/0.71  fof(f1233,plain,(
% 2.76/0.71    sP0(sK7,k4_tmap_1(sK5,sK5),sK5,sK5,sK6) | v2_struct_0(sK5) | (~spl10_29 | ~spl10_32 | ~spl10_33 | spl10_47)),
% 2.76/0.71    inference(subsumption_resolution,[],[f1232,f80])).
% 2.76/0.71  fof(f1232,plain,(
% 2.76/0.71    sP0(sK7,k4_tmap_1(sK5,sK5),sK5,sK5,sK6) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | (~spl10_29 | ~spl10_32 | ~spl10_33 | spl10_47)),
% 2.76/0.71    inference(subsumption_resolution,[],[f1231,f81])).
% 2.76/0.71  fof(f1231,plain,(
% 2.76/0.71    sP0(sK7,k4_tmap_1(sK5,sK5),sK5,sK5,sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | (~spl10_29 | ~spl10_32 | ~spl10_33 | spl10_47)),
% 2.76/0.71    inference(subsumption_resolution,[],[f1230,f82])).
% 2.76/0.71  fof(f1230,plain,(
% 2.76/0.71    sP0(sK7,k4_tmap_1(sK5,sK5),sK5,sK5,sK6) | v2_struct_0(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | (~spl10_29 | ~spl10_32 | ~spl10_33 | spl10_47)),
% 2.76/0.71    inference(subsumption_resolution,[],[f1229,f83])).
% 2.76/0.71  fof(f1229,plain,(
% 2.76/0.71    sP0(sK7,k4_tmap_1(sK5,sK5),sK5,sK5,sK6) | ~m1_pre_topc(sK6,sK5) | v2_struct_0(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | (~spl10_29 | ~spl10_32 | ~spl10_33 | spl10_47)),
% 2.76/0.71    inference(subsumption_resolution,[],[f1228,f777])).
% 2.76/0.71  fof(f1228,plain,(
% 2.76/0.71    sP0(sK7,k4_tmap_1(sK5,sK5),sK5,sK5,sK6) | ~v1_funct_1(k4_tmap_1(sK5,sK5)) | ~m1_pre_topc(sK6,sK5) | v2_struct_0(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | (~spl10_32 | ~spl10_33 | spl10_47)),
% 2.76/0.71    inference(subsumption_resolution,[],[f1227,f855])).
% 2.76/0.71  fof(f1227,plain,(
% 2.76/0.71    sP0(sK7,k4_tmap_1(sK5,sK5),sK5,sK5,sK6) | ~v1_funct_2(k4_tmap_1(sK5,sK5),u1_struct_0(sK5),u1_struct_0(sK5)) | ~v1_funct_1(k4_tmap_1(sK5,sK5)) | ~m1_pre_topc(sK6,sK5) | v2_struct_0(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | (~spl10_33 | spl10_47)),
% 2.76/0.71    inference(subsumption_resolution,[],[f1226,f860])).
% 2.76/0.71  fof(f1226,plain,(
% 2.76/0.71    sP0(sK7,k4_tmap_1(sK5,sK5),sK5,sK5,sK6) | ~m1_subset_1(k4_tmap_1(sK5,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5)))) | ~v1_funct_2(k4_tmap_1(sK5,sK5),u1_struct_0(sK5),u1_struct_0(sK5)) | ~v1_funct_1(k4_tmap_1(sK5,sK5)) | ~m1_pre_topc(sK6,sK5) | v2_struct_0(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | spl10_47),
% 2.76/0.71    inference(subsumption_resolution,[],[f1225,f84])).
% 2.76/0.71  fof(f1225,plain,(
% 2.76/0.71    sP0(sK7,k4_tmap_1(sK5,sK5),sK5,sK5,sK6) | ~v1_funct_1(sK7) | ~m1_subset_1(k4_tmap_1(sK5,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5)))) | ~v1_funct_2(k4_tmap_1(sK5,sK5),u1_struct_0(sK5),u1_struct_0(sK5)) | ~v1_funct_1(k4_tmap_1(sK5,sK5)) | ~m1_pre_topc(sK6,sK5) | v2_struct_0(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | spl10_47),
% 2.76/0.71    inference(subsumption_resolution,[],[f1224,f85])).
% 2.76/0.71  fof(f1224,plain,(
% 2.76/0.71    sP0(sK7,k4_tmap_1(sK5,sK5),sK5,sK5,sK6) | ~v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK5)) | ~v1_funct_1(sK7) | ~m1_subset_1(k4_tmap_1(sK5,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5)))) | ~v1_funct_2(k4_tmap_1(sK5,sK5),u1_struct_0(sK5),u1_struct_0(sK5)) | ~v1_funct_1(k4_tmap_1(sK5,sK5)) | ~m1_pre_topc(sK6,sK5) | v2_struct_0(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | spl10_47),
% 2.76/0.71    inference(subsumption_resolution,[],[f1223,f86])).
% 2.76/0.71  fof(f1223,plain,(
% 2.76/0.71    sP0(sK7,k4_tmap_1(sK5,sK5),sK5,sK5,sK6) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5)))) | ~v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK5)) | ~v1_funct_1(sK7) | ~m1_subset_1(k4_tmap_1(sK5,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5)))) | ~v1_funct_2(k4_tmap_1(sK5,sK5),u1_struct_0(sK5),u1_struct_0(sK5)) | ~v1_funct_1(k4_tmap_1(sK5,sK5)) | ~m1_pre_topc(sK6,sK5) | v2_struct_0(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | spl10_47),
% 2.76/0.71    inference(duplicate_literal_removal,[],[f1222])).
% 2.76/0.71  fof(f1222,plain,(
% 2.76/0.71    sP0(sK7,k4_tmap_1(sK5,sK5),sK5,sK5,sK6) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5)))) | ~v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK5)) | ~v1_funct_1(sK7) | ~m1_subset_1(k4_tmap_1(sK5,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5)))) | ~v1_funct_2(k4_tmap_1(sK5,sK5),u1_struct_0(sK5),u1_struct_0(sK5)) | ~v1_funct_1(k4_tmap_1(sK5,sK5)) | ~m1_pre_topc(sK6,sK5) | v2_struct_0(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | spl10_47),
% 2.76/0.71    inference(resolution,[],[f1216,f97])).
% 2.76/0.71  fof(f1216,plain,(
% 2.76/0.71    ~r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),k2_tmap_1(sK5,sK5,k4_tmap_1(sK5,sK5),sK6),sK7) | spl10_47),
% 2.76/0.71    inference(avatar_component_clause,[],[f1214])).
% 2.76/0.71  fof(f1214,plain,(
% 2.76/0.71    spl10_47 <=> r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),k2_tmap_1(sK5,sK5,k4_tmap_1(sK5,sK5),sK6),sK7)),
% 2.76/0.71    introduced(avatar_definition,[new_symbols(naming,[spl10_47])])).
% 2.76/0.71  fof(f1322,plain,(
% 2.76/0.71    ~m1_pre_topc(sK6,sK6) | sK9(sK7,k4_tmap_1(sK5,sK6),u1_struct_0(sK6)) = k1_funct_1(sK7,sK9(sK7,k4_tmap_1(sK5,sK6),u1_struct_0(sK6))) | (~spl10_13 | ~spl10_29 | ~spl10_32 | ~spl10_33 | spl10_47)),
% 2.76/0.71    inference(subsumption_resolution,[],[f1318,f82])).
% 2.76/0.71  fof(f1318,plain,(
% 2.76/0.71    v2_struct_0(sK6) | ~m1_pre_topc(sK6,sK6) | sK9(sK7,k4_tmap_1(sK5,sK6),u1_struct_0(sK6)) = k1_funct_1(sK7,sK9(sK7,k4_tmap_1(sK5,sK6),u1_struct_0(sK6))) | (~spl10_13 | ~spl10_29 | ~spl10_32 | ~spl10_33 | spl10_47)),
% 2.76/0.71    inference(resolution,[],[f1281,f314])).
% 2.76/0.71  fof(f1281,plain,(
% 2.76/0.71    ( ! [X2,X0,X1] : (sP2(X1,X2,u1_struct_0(X0)) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK6) | sK9(X1,X2,u1_struct_0(X0)) = k1_funct_1(sK7,sK9(X1,X2,u1_struct_0(X0)))) ) | (~spl10_29 | ~spl10_32 | ~spl10_33 | spl10_47)),
% 2.76/0.71    inference(subsumption_resolution,[],[f1280,f243])).
% 2.76/0.71  fof(f1280,plain,(
% 2.76/0.71    ( ! [X2,X0,X1] : (v2_struct_0(X0) | sP2(X1,X2,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK6) | sK9(X1,X2,u1_struct_0(X0)) = k1_funct_1(sK7,sK9(X1,X2,u1_struct_0(X0))) | ~m1_subset_1(sK9(X1,X2,u1_struct_0(X0)),u1_struct_0(sK5))) ) | (~spl10_29 | ~spl10_32 | ~spl10_33 | spl10_47)),
% 2.76/0.71    inference(subsumption_resolution,[],[f220,f1252])).
% 2.76/0.71  fof(f1221,plain,(
% 2.76/0.71    ~spl10_47 | spl10_48 | ~spl10_43 | ~spl10_44 | ~spl10_46),
% 2.76/0.71    inference(avatar_split_clause,[],[f1178,f1161,f1149,f1128,f1218,f1214])).
% 2.76/0.71  fof(f1128,plain,(
% 2.76/0.71    spl10_43 <=> v1_funct_1(k2_tmap_1(sK5,sK5,k4_tmap_1(sK5,sK5),sK6))),
% 2.76/0.71    introduced(avatar_definition,[new_symbols(naming,[spl10_43])])).
% 2.76/0.71  fof(f1149,plain,(
% 2.76/0.71    spl10_44 <=> v1_funct_2(k2_tmap_1(sK5,sK5,k4_tmap_1(sK5,sK5),sK6),u1_struct_0(sK6),u1_struct_0(sK5))),
% 2.76/0.71    introduced(avatar_definition,[new_symbols(naming,[spl10_44])])).
% 2.76/0.71  fof(f1161,plain,(
% 2.76/0.71    spl10_46 <=> m1_subset_1(k2_tmap_1(sK5,sK5,k4_tmap_1(sK5,sK5),sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5))))),
% 2.76/0.71    introduced(avatar_definition,[new_symbols(naming,[spl10_46])])).
% 2.76/0.71  fof(f1178,plain,(
% 2.76/0.71    sK7 = k2_tmap_1(sK5,sK5,k4_tmap_1(sK5,sK5),sK6) | ~r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),k2_tmap_1(sK5,sK5,k4_tmap_1(sK5,sK5),sK6),sK7) | (~spl10_43 | ~spl10_44 | ~spl10_46)),
% 2.76/0.71    inference(subsumption_resolution,[],[f1177,f1130])).
% 2.76/0.71  fof(f1130,plain,(
% 2.76/0.71    v1_funct_1(k2_tmap_1(sK5,sK5,k4_tmap_1(sK5,sK5),sK6)) | ~spl10_43),
% 2.76/0.71    inference(avatar_component_clause,[],[f1128])).
% 2.76/0.71  fof(f1177,plain,(
% 2.76/0.71    sK7 = k2_tmap_1(sK5,sK5,k4_tmap_1(sK5,sK5),sK6) | ~r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),k2_tmap_1(sK5,sK5,k4_tmap_1(sK5,sK5),sK6),sK7) | ~v1_funct_1(k2_tmap_1(sK5,sK5,k4_tmap_1(sK5,sK5),sK6)) | (~spl10_44 | ~spl10_46)),
% 2.76/0.71    inference(subsumption_resolution,[],[f1165,f1151])).
% 2.76/0.71  fof(f1151,plain,(
% 2.76/0.71    v1_funct_2(k2_tmap_1(sK5,sK5,k4_tmap_1(sK5,sK5),sK6),u1_struct_0(sK6),u1_struct_0(sK5)) | ~spl10_44),
% 2.76/0.71    inference(avatar_component_clause,[],[f1149])).
% 2.76/0.71  fof(f1165,plain,(
% 2.76/0.71    sK7 = k2_tmap_1(sK5,sK5,k4_tmap_1(sK5,sK5),sK6) | ~r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),k2_tmap_1(sK5,sK5,k4_tmap_1(sK5,sK5),sK6),sK7) | ~v1_funct_2(k2_tmap_1(sK5,sK5,k4_tmap_1(sK5,sK5),sK6),u1_struct_0(sK6),u1_struct_0(sK5)) | ~v1_funct_1(k2_tmap_1(sK5,sK5,k4_tmap_1(sK5,sK5),sK6)) | ~spl10_46),
% 2.76/0.71    inference(resolution,[],[f1163,f354])).
% 2.76/0.71  fof(f354,plain,(
% 2.76/0.71    ( ! [X9] : (~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5)))) | sK7 = X9 | ~r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),X9,sK7) | ~v1_funct_2(X9,u1_struct_0(sK6),u1_struct_0(sK5)) | ~v1_funct_1(X9)) )),
% 2.76/0.71    inference(subsumption_resolution,[],[f353,f84])).
% 2.76/0.71  fof(f353,plain,(
% 2.76/0.71    ( ! [X9] : (~r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),X9,sK7) | sK7 = X9 | ~v1_funct_1(sK7) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5)))) | ~v1_funct_2(X9,u1_struct_0(sK6),u1_struct_0(sK5)) | ~v1_funct_1(X9)) )),
% 2.76/0.71    inference(subsumption_resolution,[],[f347,f85])).
% 2.76/0.71  fof(f347,plain,(
% 2.76/0.71    ( ! [X9] : (~r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),X9,sK7) | sK7 = X9 | ~v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK5)) | ~v1_funct_1(sK7) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5)))) | ~v1_funct_2(X9,u1_struct_0(sK6),u1_struct_0(sK5)) | ~v1_funct_1(X9)) )),
% 2.76/0.71    inference(resolution,[],[f115,f86])).
% 2.76/0.71  fof(f1163,plain,(
% 2.76/0.71    m1_subset_1(k2_tmap_1(sK5,sK5,k4_tmap_1(sK5,sK5),sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5)))) | ~spl10_46),
% 2.76/0.71    inference(avatar_component_clause,[],[f1161])).
% 2.76/0.71  fof(f1164,plain,(
% 2.76/0.71    ~spl10_42 | spl10_46 | ~spl10_29 | ~spl10_31 | ~spl10_32 | ~spl10_33),
% 2.76/0.71    inference(avatar_split_clause,[],[f1104,f858,f853,f789,f775,f1161,f1124])).
% 2.76/0.71  fof(f1124,plain,(
% 2.76/0.71    spl10_42 <=> sP4(sK5,sK6,k4_tmap_1(sK5,sK5),sK5,sK5)),
% 2.76/0.71    introduced(avatar_definition,[new_symbols(naming,[spl10_42])])).
% 2.76/0.71  fof(f789,plain,(
% 2.76/0.71    spl10_31 <=> m1_pre_topc(sK5,sK5)),
% 2.76/0.71    introduced(avatar_definition,[new_symbols(naming,[spl10_31])])).
% 2.76/0.71  fof(f1104,plain,(
% 2.76/0.71    m1_subset_1(k2_tmap_1(sK5,sK5,k4_tmap_1(sK5,sK5),sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5)))) | ~sP4(sK5,sK6,k4_tmap_1(sK5,sK5),sK5,sK5) | (~spl10_29 | ~spl10_31 | ~spl10_32 | ~spl10_33)),
% 2.76/0.71    inference(superposition,[],[f119,f1082])).
% 2.76/0.71  fof(f1082,plain,(
% 2.76/0.71    k2_tmap_1(sK5,sK5,k4_tmap_1(sK5,sK5),sK6) = k3_tmap_1(sK5,sK5,sK5,sK6,k4_tmap_1(sK5,sK5)) | (~spl10_29 | ~spl10_31 | ~spl10_32 | ~spl10_33)),
% 2.76/0.71    inference(forward_demodulation,[],[f1079,f919])).
% 2.76/0.71  fof(f919,plain,(
% 2.76/0.71    k2_tmap_1(sK5,sK5,k4_tmap_1(sK5,sK5),sK6) = k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK5),k4_tmap_1(sK5,sK5),u1_struct_0(sK6)) | (~spl10_29 | ~spl10_32 | ~spl10_33)),
% 2.76/0.71    inference(resolution,[],[f884,f83])).
% 2.76/0.71  fof(f884,plain,(
% 2.76/0.71    ( ! [X2] : (~m1_pre_topc(X2,sK5) | k2_tmap_1(sK5,sK5,k4_tmap_1(sK5,sK5),X2) = k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK5),k4_tmap_1(sK5,sK5),u1_struct_0(X2))) ) | (~spl10_29 | ~spl10_32 | ~spl10_33)),
% 2.76/0.71    inference(subsumption_resolution,[],[f883,f79])).
% 2.76/0.71  fof(f883,plain,(
% 2.76/0.71    ( ! [X2] : (~m1_pre_topc(X2,sK5) | k2_tmap_1(sK5,sK5,k4_tmap_1(sK5,sK5),X2) = k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK5),k4_tmap_1(sK5,sK5),u1_struct_0(X2)) | v2_struct_0(sK5)) ) | (~spl10_29 | ~spl10_32 | ~spl10_33)),
% 2.76/0.71    inference(subsumption_resolution,[],[f882,f80])).
% 2.76/0.71  fof(f882,plain,(
% 2.76/0.71    ( ! [X2] : (~m1_pre_topc(X2,sK5) | k2_tmap_1(sK5,sK5,k4_tmap_1(sK5,sK5),X2) = k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK5),k4_tmap_1(sK5,sK5),u1_struct_0(X2)) | ~v2_pre_topc(sK5) | v2_struct_0(sK5)) ) | (~spl10_29 | ~spl10_32 | ~spl10_33)),
% 2.76/0.71    inference(subsumption_resolution,[],[f881,f81])).
% 2.76/0.71  fof(f881,plain,(
% 2.76/0.71    ( ! [X2] : (~m1_pre_topc(X2,sK5) | k2_tmap_1(sK5,sK5,k4_tmap_1(sK5,sK5),X2) = k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK5),k4_tmap_1(sK5,sK5),u1_struct_0(X2)) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5)) ) | (~spl10_29 | ~spl10_32 | ~spl10_33)),
% 2.76/0.71    inference(subsumption_resolution,[],[f880,f777])).
% 2.76/0.71  fof(f880,plain,(
% 2.76/0.71    ( ! [X2] : (~m1_pre_topc(X2,sK5) | k2_tmap_1(sK5,sK5,k4_tmap_1(sK5,sK5),X2) = k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK5),k4_tmap_1(sK5,sK5),u1_struct_0(X2)) | ~v1_funct_1(k4_tmap_1(sK5,sK5)) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5)) ) | (~spl10_32 | ~spl10_33)),
% 2.76/0.71    inference(subsumption_resolution,[],[f873,f855])).
% 2.76/0.71  fof(f873,plain,(
% 2.76/0.71    ( ! [X2] : (~m1_pre_topc(X2,sK5) | k2_tmap_1(sK5,sK5,k4_tmap_1(sK5,sK5),X2) = k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK5),k4_tmap_1(sK5,sK5),u1_struct_0(X2)) | ~v1_funct_2(k4_tmap_1(sK5,sK5),u1_struct_0(sK5),u1_struct_0(sK5)) | ~v1_funct_1(k4_tmap_1(sK5,sK5)) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5)) ) | ~spl10_33),
% 2.76/0.71    inference(duplicate_literal_removal,[],[f863])).
% 2.76/0.71  fof(f863,plain,(
% 2.76/0.71    ( ! [X2] : (~m1_pre_topc(X2,sK5) | k2_tmap_1(sK5,sK5,k4_tmap_1(sK5,sK5),X2) = k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK5),k4_tmap_1(sK5,sK5),u1_struct_0(X2)) | ~v1_funct_2(k4_tmap_1(sK5,sK5),u1_struct_0(sK5),u1_struct_0(sK5)) | ~v1_funct_1(k4_tmap_1(sK5,sK5)) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5)) ) | ~spl10_33),
% 2.76/0.71    inference(resolution,[],[f860,f98])).
% 2.76/0.71  fof(f98,plain,(
% 2.76/0.71    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X0) | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.76/0.71    inference(cnf_transformation,[],[f32])).
% 2.76/0.71  fof(f32,plain,(
% 2.76/0.71    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.76/0.71    inference(flattening,[],[f31])).
% 2.76/0.71  fof(f31,plain,(
% 2.76/0.71    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.76/0.71    inference(ennf_transformation,[],[f8])).
% 2.76/0.71  fof(f8,axiom,(
% 2.76/0.71    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 2.76/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).
% 2.76/0.71  fof(f1079,plain,(
% 2.76/0.71    k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK5),k4_tmap_1(sK5,sK5),u1_struct_0(sK6)) = k3_tmap_1(sK5,sK5,sK5,sK6,k4_tmap_1(sK5,sK5)) | (~spl10_29 | ~spl10_31 | ~spl10_32 | ~spl10_33)),
% 2.76/0.71    inference(resolution,[],[f1078,f83])).
% 2.76/0.71  fof(f1078,plain,(
% 2.76/0.71    ( ! [X0] : (~m1_pre_topc(X0,sK5) | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK5),k4_tmap_1(sK5,sK5),u1_struct_0(X0)) = k3_tmap_1(sK5,sK5,sK5,X0,k4_tmap_1(sK5,sK5))) ) | (~spl10_29 | ~spl10_31 | ~spl10_32 | ~spl10_33)),
% 2.76/0.71    inference(subsumption_resolution,[],[f1077,f79])).
% 2.76/0.71  fof(f1077,plain,(
% 2.76/0.71    ( ! [X0] : (k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK5),k4_tmap_1(sK5,sK5),u1_struct_0(X0)) = k3_tmap_1(sK5,sK5,sK5,X0,k4_tmap_1(sK5,sK5)) | ~m1_pre_topc(X0,sK5) | v2_struct_0(sK5)) ) | (~spl10_29 | ~spl10_31 | ~spl10_32 | ~spl10_33)),
% 2.76/0.71    inference(subsumption_resolution,[],[f1076,f80])).
% 2.76/0.71  fof(f1076,plain,(
% 2.76/0.71    ( ! [X0] : (k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK5),k4_tmap_1(sK5,sK5),u1_struct_0(X0)) = k3_tmap_1(sK5,sK5,sK5,X0,k4_tmap_1(sK5,sK5)) | ~m1_pre_topc(X0,sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5)) ) | (~spl10_29 | ~spl10_31 | ~spl10_32 | ~spl10_33)),
% 2.76/0.71    inference(subsumption_resolution,[],[f1073,f81])).
% 2.76/0.71  fof(f1073,plain,(
% 2.76/0.71    ( ! [X0] : (k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK5),k4_tmap_1(sK5,sK5),u1_struct_0(X0)) = k3_tmap_1(sK5,sK5,sK5,X0,k4_tmap_1(sK5,sK5)) | ~m1_pre_topc(X0,sK5) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5)) ) | (~spl10_29 | ~spl10_31 | ~spl10_32 | ~spl10_33)),
% 2.76/0.71    inference(resolution,[],[f879,f790])).
% 2.76/0.71  fof(f790,plain,(
% 2.76/0.71    m1_pre_topc(sK5,sK5) | ~spl10_31),
% 2.76/0.71    inference(avatar_component_clause,[],[f789])).
% 2.76/0.71  fof(f879,plain,(
% 2.76/0.71    ( ! [X0,X1] : (~m1_pre_topc(sK5,X1) | k3_tmap_1(X1,sK5,sK5,X0,k4_tmap_1(sK5,sK5)) = k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK5),k4_tmap_1(sK5,sK5),u1_struct_0(X0)) | ~m1_pre_topc(X0,sK5) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) ) | (~spl10_29 | ~spl10_32 | ~spl10_33)),
% 2.76/0.71    inference(subsumption_resolution,[],[f878,f102])).
% 2.76/0.71  fof(f102,plain,(
% 2.76/0.71    ( ! [X2,X0,X1] : (~m1_pre_topc(X2,X1) | m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.76/0.71    inference(cnf_transformation,[],[f40])).
% 2.76/0.71  fof(f40,plain,(
% 2.76/0.71    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.76/0.71    inference(flattening,[],[f39])).
% 2.76/0.71  fof(f39,plain,(
% 2.76/0.71    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.76/0.71    inference(ennf_transformation,[],[f16])).
% 2.76/0.71  fof(f16,axiom,(
% 2.76/0.71    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 2.76/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).
% 2.76/0.71  fof(f878,plain,(
% 2.76/0.71    ( ! [X0,X1] : (~m1_pre_topc(X0,sK5) | k3_tmap_1(X1,sK5,sK5,X0,k4_tmap_1(sK5,sK5)) = k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK5),k4_tmap_1(sK5,sK5),u1_struct_0(X0)) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK5,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) ) | (~spl10_29 | ~spl10_32 | ~spl10_33)),
% 2.76/0.71    inference(subsumption_resolution,[],[f877,f79])).
% 2.76/0.71  fof(f877,plain,(
% 2.76/0.71    ( ! [X0,X1] : (~m1_pre_topc(X0,sK5) | k3_tmap_1(X1,sK5,sK5,X0,k4_tmap_1(sK5,sK5)) = k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK5),k4_tmap_1(sK5,sK5),u1_struct_0(X0)) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK5,X1) | v2_struct_0(sK5) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) ) | (~spl10_29 | ~spl10_32 | ~spl10_33)),
% 2.76/0.71    inference(subsumption_resolution,[],[f876,f80])).
% 2.76/0.71  fof(f876,plain,(
% 2.76/0.71    ( ! [X0,X1] : (~m1_pre_topc(X0,sK5) | k3_tmap_1(X1,sK5,sK5,X0,k4_tmap_1(sK5,sK5)) = k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK5),k4_tmap_1(sK5,sK5),u1_struct_0(X0)) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK5,X1) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) ) | (~spl10_29 | ~spl10_32 | ~spl10_33)),
% 2.76/0.71    inference(subsumption_resolution,[],[f875,f81])).
% 2.76/0.71  fof(f875,plain,(
% 2.76/0.71    ( ! [X0,X1] : (~m1_pre_topc(X0,sK5) | k3_tmap_1(X1,sK5,sK5,X0,k4_tmap_1(sK5,sK5)) = k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK5),k4_tmap_1(sK5,sK5),u1_struct_0(X0)) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK5,X1) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) ) | (~spl10_29 | ~spl10_32 | ~spl10_33)),
% 2.76/0.71    inference(subsumption_resolution,[],[f874,f777])).
% 2.76/0.71  fof(f874,plain,(
% 2.76/0.71    ( ! [X0,X1] : (~m1_pre_topc(X0,sK5) | k3_tmap_1(X1,sK5,sK5,X0,k4_tmap_1(sK5,sK5)) = k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK5),k4_tmap_1(sK5,sK5),u1_struct_0(X0)) | ~v1_funct_1(k4_tmap_1(sK5,sK5)) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK5,X1) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) ) | (~spl10_32 | ~spl10_33)),
% 2.76/0.71    inference(subsumption_resolution,[],[f862,f855])).
% 2.76/0.71  fof(f862,plain,(
% 2.76/0.71    ( ! [X0,X1] : (~m1_pre_topc(X0,sK5) | k3_tmap_1(X1,sK5,sK5,X0,k4_tmap_1(sK5,sK5)) = k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK5),k4_tmap_1(sK5,sK5),u1_struct_0(X0)) | ~v1_funct_2(k4_tmap_1(sK5,sK5),u1_struct_0(sK5),u1_struct_0(sK5)) | ~v1_funct_1(k4_tmap_1(sK5,sK5)) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK5,X1) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) ) | ~spl10_33),
% 2.76/0.71    inference(resolution,[],[f860,f92])).
% 2.76/0.71  fof(f92,plain,(
% 2.76/0.71    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X2) | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.76/0.71    inference(cnf_transformation,[],[f26])).
% 2.76/0.71  fof(f26,plain,(
% 2.76/0.71    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.76/0.71    inference(flattening,[],[f25])).
% 2.76/0.71  fof(f25,plain,(
% 2.76/0.71    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.76/0.71    inference(ennf_transformation,[],[f9])).
% 2.76/0.71  fof(f9,axiom,(
% 2.76/0.71    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))))))))),
% 2.76/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).
% 2.76/0.71  fof(f119,plain,(
% 2.76/0.71    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k3_tmap_1(X4,X0,X3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~sP4(X0,X1,X2,X3,X4)) )),
% 2.76/0.71    inference(cnf_transformation,[],[f78])).
% 2.76/0.71  fof(f78,plain,(
% 2.76/0.71    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X4,X0,X3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k3_tmap_1(X4,X0,X3,X1,X2),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k3_tmap_1(X4,X0,X3,X1,X2))) | ~sP4(X0,X1,X2,X3,X4))),
% 2.76/0.71    inference(rectify,[],[f77])).
% 2.76/0.71  fof(f77,plain,(
% 2.76/0.71    ! [X1,X3,X4,X2,X0] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~sP4(X1,X3,X4,X2,X0))),
% 2.76/0.71    inference(nnf_transformation,[],[f59])).
% 2.76/0.71  fof(f59,plain,(
% 2.76/0.71    ! [X1,X3,X4,X2,X0] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~sP4(X1,X3,X4,X2,X0))),
% 2.76/0.71    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 2.76/0.71  fof(f1152,plain,(
% 2.76/0.71    ~spl10_42 | spl10_44 | ~spl10_29 | ~spl10_31 | ~spl10_32 | ~spl10_33),
% 2.76/0.71    inference(avatar_split_clause,[],[f1103,f858,f853,f789,f775,f1149,f1124])).
% 2.76/0.71  fof(f1103,plain,(
% 2.76/0.71    v1_funct_2(k2_tmap_1(sK5,sK5,k4_tmap_1(sK5,sK5),sK6),u1_struct_0(sK6),u1_struct_0(sK5)) | ~sP4(sK5,sK6,k4_tmap_1(sK5,sK5),sK5,sK5) | (~spl10_29 | ~spl10_31 | ~spl10_32 | ~spl10_33)),
% 2.76/0.71    inference(superposition,[],[f118,f1082])).
% 2.76/0.71  fof(f118,plain,(
% 2.76/0.71    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k3_tmap_1(X4,X0,X3,X1,X2),u1_struct_0(X1),u1_struct_0(X0)) | ~sP4(X0,X1,X2,X3,X4)) )),
% 2.76/0.71    inference(cnf_transformation,[],[f78])).
% 2.76/0.71  fof(f1147,plain,(
% 2.76/0.71    ~spl10_30 | ~spl10_31 | spl10_42),
% 2.76/0.71    inference(avatar_contradiction_clause,[],[f1146])).
% 2.76/0.71  fof(f1146,plain,(
% 2.76/0.71    $false | (~spl10_30 | ~spl10_31 | spl10_42)),
% 2.76/0.71    inference(subsumption_resolution,[],[f1145,f786])).
% 2.76/0.71  fof(f786,plain,(
% 2.76/0.71    sP1(sK5,sK5) | ~spl10_30),
% 2.76/0.71    inference(avatar_component_clause,[],[f785])).
% 2.76/0.71  fof(f785,plain,(
% 2.76/0.71    spl10_30 <=> sP1(sK5,sK5)),
% 2.76/0.71    introduced(avatar_definition,[new_symbols(naming,[spl10_30])])).
% 2.76/0.71  fof(f1145,plain,(
% 2.76/0.71    ~sP1(sK5,sK5) | (~spl10_31 | spl10_42)),
% 2.76/0.71    inference(subsumption_resolution,[],[f1144,f79])).
% 2.76/0.71  fof(f1144,plain,(
% 2.76/0.71    v2_struct_0(sK5) | ~sP1(sK5,sK5) | (~spl10_31 | spl10_42)),
% 2.76/0.71    inference(subsumption_resolution,[],[f1143,f80])).
% 2.76/0.71  fof(f1143,plain,(
% 2.76/0.71    ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~sP1(sK5,sK5) | (~spl10_31 | spl10_42)),
% 2.76/0.71    inference(subsumption_resolution,[],[f1142,f81])).
% 2.76/0.71  fof(f1142,plain,(
% 2.76/0.71    ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~sP1(sK5,sK5) | (~spl10_31 | spl10_42)),
% 2.76/0.71    inference(subsumption_resolution,[],[f1141,f790])).
% 2.76/0.71  fof(f1141,plain,(
% 2.76/0.71    ~m1_pre_topc(sK5,sK5) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~sP1(sK5,sK5) | spl10_42),
% 2.76/0.71    inference(subsumption_resolution,[],[f1134,f83])).
% 2.76/0.71  fof(f1134,plain,(
% 2.76/0.71    ~m1_pre_topc(sK6,sK5) | ~m1_pre_topc(sK5,sK5) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~sP1(sK5,sK5) | spl10_42),
% 2.76/0.71    inference(duplicate_literal_removal,[],[f1133])).
% 2.76/0.71  fof(f1133,plain,(
% 2.76/0.71    ~m1_pre_topc(sK6,sK5) | ~m1_pre_topc(sK5,sK5) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~sP1(sK5,sK5) | spl10_42),
% 2.76/0.71    inference(resolution,[],[f1126,f422])).
% 2.76/0.71  fof(f422,plain,(
% 2.76/0.71    ( ! [X10,X8,X7,X9] : (sP4(X7,X8,k4_tmap_1(X7,X9),X9,X10) | ~m1_pre_topc(X8,X10) | ~m1_pre_topc(X9,X10) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7) | v2_struct_0(X7) | ~l1_pre_topc(X10) | ~v2_pre_topc(X10) | v2_struct_0(X10) | ~sP1(X7,X9)) )),
% 2.76/0.71    inference(subsumption_resolution,[],[f421,f104])).
% 2.76/0.71  fof(f421,plain,(
% 2.76/0.71    ( ! [X10,X8,X7,X9] : (sP4(X7,X8,k4_tmap_1(X7,X9),X9,X10) | ~v1_funct_1(k4_tmap_1(X7,X9)) | ~m1_pre_topc(X8,X10) | ~m1_pre_topc(X9,X10) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7) | v2_struct_0(X7) | ~l1_pre_topc(X10) | ~v2_pre_topc(X10) | v2_struct_0(X10) | ~sP1(X7,X9)) )),
% 2.76/0.71    inference(subsumption_resolution,[],[f416,f105])).
% 2.76/0.71  fof(f416,plain,(
% 2.76/0.71    ( ! [X10,X8,X7,X9] : (sP4(X7,X8,k4_tmap_1(X7,X9),X9,X10) | ~v1_funct_2(k4_tmap_1(X7,X9),u1_struct_0(X9),u1_struct_0(X7)) | ~v1_funct_1(k4_tmap_1(X7,X9)) | ~m1_pre_topc(X8,X10) | ~m1_pre_topc(X9,X10) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7) | v2_struct_0(X7) | ~l1_pre_topc(X10) | ~v2_pre_topc(X10) | v2_struct_0(X10) | ~sP1(X7,X9)) )),
% 2.76/0.72    inference(resolution,[],[f120,f106])).
% 2.76/0.72  fof(f120,plain,(
% 2.76/0.72    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | sP4(X1,X3,X4,X2,X0) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.76/0.72    inference(cnf_transformation,[],[f60])).
% 2.76/0.72  fof(f60,plain,(
% 2.76/0.72    ! [X0,X1,X2,X3,X4] : (sP4(X1,X3,X4,X2,X0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.76/0.72    inference(definition_folding,[],[f51,f59])).
% 2.76/0.72  fof(f51,plain,(
% 2.76/0.72    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.76/0.72    inference(flattening,[],[f50])).
% 2.76/0.72  fof(f50,plain,(
% 2.76/0.72    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.76/0.72    inference(ennf_transformation,[],[f10])).
% 2.76/0.72  fof(f10,axiom,(
% 2.76/0.72    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & m1_pre_topc(X2,X0) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))))),
% 2.76/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_tmap_1)).
% 2.76/0.72  fof(f1126,plain,(
% 2.76/0.72    ~sP4(sK5,sK6,k4_tmap_1(sK5,sK5),sK5,sK5) | spl10_42),
% 2.76/0.72    inference(avatar_component_clause,[],[f1124])).
% 2.76/0.72  fof(f1131,plain,(
% 2.76/0.72    ~spl10_42 | spl10_43 | ~spl10_29 | ~spl10_31 | ~spl10_32 | ~spl10_33),
% 2.76/0.72    inference(avatar_split_clause,[],[f1102,f858,f853,f789,f775,f1128,f1124])).
% 2.76/0.72  fof(f1102,plain,(
% 2.76/0.72    v1_funct_1(k2_tmap_1(sK5,sK5,k4_tmap_1(sK5,sK5),sK6)) | ~sP4(sK5,sK6,k4_tmap_1(sK5,sK5),sK5,sK5) | (~spl10_29 | ~spl10_31 | ~spl10_32 | ~spl10_33)),
% 2.76/0.72    inference(superposition,[],[f117,f1082])).
% 2.76/0.72  fof(f117,plain,(
% 2.76/0.72    ( ! [X4,X2,X0,X3,X1] : (v1_funct_1(k3_tmap_1(X4,X0,X3,X1,X2)) | ~sP4(X0,X1,X2,X3,X4)) )),
% 2.76/0.72    inference(cnf_transformation,[],[f78])).
% 2.76/0.72  fof(f861,plain,(
% 2.76/0.72    ~spl10_28 | spl10_33),
% 2.76/0.72    inference(avatar_split_clause,[],[f741,f858,f771])).
% 2.76/0.72  fof(f771,plain,(
% 2.76/0.72    spl10_28 <=> sP4(sK5,sK5,k4_tmap_1(sK5,sK5),sK5,sK5)),
% 2.76/0.72    introduced(avatar_definition,[new_symbols(naming,[spl10_28])])).
% 2.76/0.72  fof(f741,plain,(
% 2.76/0.72    m1_subset_1(k4_tmap_1(sK5,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5)))) | ~sP4(sK5,sK5,k4_tmap_1(sK5,sK5),sK5,sK5)),
% 2.76/0.72    inference(superposition,[],[f119,f736])).
% 2.76/0.72  fof(f736,plain,(
% 2.76/0.72    k4_tmap_1(sK5,sK5) = k3_tmap_1(sK5,sK5,sK5,sK5,k4_tmap_1(sK5,sK5))),
% 2.76/0.72    inference(subsumption_resolution,[],[f735,f80])).
% 2.76/0.72  fof(f735,plain,(
% 2.76/0.72    ~v2_pre_topc(sK5) | k4_tmap_1(sK5,sK5) = k3_tmap_1(sK5,sK5,sK5,sK5,k4_tmap_1(sK5,sK5))),
% 2.76/0.72    inference(subsumption_resolution,[],[f733,f79])).
% 2.76/0.72  fof(f733,plain,(
% 2.76/0.72    v2_struct_0(sK5) | ~v2_pre_topc(sK5) | k4_tmap_1(sK5,sK5) = k3_tmap_1(sK5,sK5,sK5,sK5,k4_tmap_1(sK5,sK5))),
% 2.76/0.72    inference(resolution,[],[f605,f81])).
% 2.76/0.72  fof(f605,plain,(
% 2.76/0.72    ( ! [X0] : (~l1_pre_topc(X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | k4_tmap_1(X0,X0) = k3_tmap_1(X0,X0,X0,X0,k4_tmap_1(X0,X0))) )),
% 2.76/0.72    inference(duplicate_literal_removal,[],[f604])).
% 2.76/0.72  fof(f604,plain,(
% 2.76/0.72    ( ! [X0] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | k4_tmap_1(X0,X0) = k3_tmap_1(X0,X0,X0,X0,k4_tmap_1(X0,X0)) | ~l1_pre_topc(X0)) )),
% 2.76/0.72    inference(resolution,[],[f502,f89])).
% 2.76/0.72  fof(f502,plain,(
% 2.76/0.72    ( ! [X2,X1] : (~m1_pre_topc(X1,X2) | v2_struct_0(X1) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | k4_tmap_1(X1,X1) = k3_tmap_1(X2,X1,X1,X1,k4_tmap_1(X1,X1))) )),
% 2.76/0.72    inference(subsumption_resolution,[],[f501,f90])).
% 2.76/0.72  fof(f501,plain,(
% 2.76/0.72    ( ! [X2,X1] : (~m1_pre_topc(X1,X2) | v2_struct_0(X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | k4_tmap_1(X1,X1) = k3_tmap_1(X2,X1,X1,X1,k4_tmap_1(X1,X1))) )),
% 2.76/0.72    inference(subsumption_resolution,[],[f496,f101])).
% 2.76/0.72  fof(f101,plain,(
% 2.76/0.72    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.76/0.72    inference(cnf_transformation,[],[f38])).
% 2.76/0.72  fof(f38,plain,(
% 2.76/0.72    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.76/0.72    inference(flattening,[],[f37])).
% 2.76/0.72  fof(f37,plain,(
% 2.76/0.72    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.76/0.72    inference(ennf_transformation,[],[f5])).
% 2.76/0.72  fof(f5,axiom,(
% 2.76/0.72    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 2.76/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).
% 2.76/0.72  fof(f496,plain,(
% 2.76/0.72    ( ! [X2,X1] : (~m1_pre_topc(X1,X2) | v2_struct_0(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | k4_tmap_1(X1,X1) = k3_tmap_1(X2,X1,X1,X1,k4_tmap_1(X1,X1))) )),
% 2.76/0.72    inference(duplicate_literal_removal,[],[f495])).
% 2.76/0.72  fof(f495,plain,(
% 2.76/0.72    ( ! [X2,X1] : (~m1_pre_topc(X1,X2) | v2_struct_0(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | k4_tmap_1(X1,X1) = k3_tmap_1(X2,X1,X1,X1,k4_tmap_1(X1,X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 2.76/0.72    inference(resolution,[],[f440,f148])).
% 2.76/0.72  fof(f148,plain,(
% 2.76/0.72    ( ! [X0] : (sP1(X0,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.76/0.72    inference(duplicate_literal_removal,[],[f147])).
% 2.76/0.72  fof(f147,plain,(
% 2.76/0.72    ( ! [X0] : (sP1(X0,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.76/0.72    inference(resolution,[],[f107,f89])).
% 2.76/0.72  fof(f440,plain,(
% 2.76/0.72    ( ! [X6,X8,X7] : (~sP1(X7,X8) | ~m1_pre_topc(X8,X6) | v2_struct_0(X8) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7) | v2_struct_0(X7) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6) | k4_tmap_1(X7,X8) = k3_tmap_1(X6,X7,X8,X8,k4_tmap_1(X7,X8))) )),
% 2.76/0.72    inference(subsumption_resolution,[],[f439,f104])).
% 2.76/0.72  fof(f439,plain,(
% 2.76/0.72    ( ! [X6,X8,X7] : (k4_tmap_1(X7,X8) = k3_tmap_1(X6,X7,X8,X8,k4_tmap_1(X7,X8)) | ~v1_funct_1(k4_tmap_1(X7,X8)) | ~m1_pre_topc(X8,X6) | v2_struct_0(X8) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7) | v2_struct_0(X7) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6) | ~sP1(X7,X8)) )),
% 2.76/0.72    inference(subsumption_resolution,[],[f434,f105])).
% 2.76/0.72  fof(f434,plain,(
% 2.76/0.72    ( ! [X6,X8,X7] : (k4_tmap_1(X7,X8) = k3_tmap_1(X6,X7,X8,X8,k4_tmap_1(X7,X8)) | ~v1_funct_2(k4_tmap_1(X7,X8),u1_struct_0(X8),u1_struct_0(X7)) | ~v1_funct_1(k4_tmap_1(X7,X8)) | ~m1_pre_topc(X8,X6) | v2_struct_0(X8) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7) | v2_struct_0(X7) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6) | ~sP1(X7,X8)) )),
% 2.76/0.72    inference(resolution,[],[f432,f106])).
% 2.76/0.72  fof(f432,plain,(
% 2.76/0.72    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | k3_tmap_1(X0,X1,X2,X2,X3) = X3 | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.76/0.72    inference(subsumption_resolution,[],[f431,f120])).
% 2.76/0.72  fof(f431,plain,(
% 2.76/0.72    ( ! [X2,X0,X3,X1] : (k3_tmap_1(X0,X1,X2,X2,X3) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~sP4(X1,X2,X3,X2,X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.76/0.72    inference(duplicate_literal_removal,[],[f428])).
% 2.76/0.72  fof(f428,plain,(
% 2.76/0.72    ( ! [X2,X0,X3,X1] : (k3_tmap_1(X0,X1,X2,X2,X3) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~sP4(X1,X2,X3,X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.76/0.72    inference(resolution,[],[f350,f93])).
% 2.76/0.72  fof(f93,plain,(
% 2.76/0.72    ( ! [X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.76/0.72    inference(cnf_transformation,[],[f28])).
% 2.76/0.72  fof(f28,plain,(
% 2.76/0.72    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.76/0.72    inference(flattening,[],[f27])).
% 2.76/0.72  fof(f27,plain,(
% 2.76/0.72    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.76/0.72    inference(ennf_transformation,[],[f15])).
% 2.76/0.72  fof(f15,axiom,(
% 2.76/0.72    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))))))),
% 2.76/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tmap_1)).
% 2.76/0.72  fof(f350,plain,(
% 2.76/0.72    ( ! [X4,X2,X0,X5,X3,X1] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k3_tmap_1(X3,X1,X4,X0,X5)) | k3_tmap_1(X3,X1,X4,X0,X5) = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~sP4(X1,X0,X5,X4,X3)) )),
% 2.76/0.72    inference(subsumption_resolution,[],[f349,f117])).
% 2.76/0.72  fof(f349,plain,(
% 2.76/0.72    ( ! [X4,X2,X0,X5,X3,X1] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k3_tmap_1(X3,X1,X4,X0,X5)) | k3_tmap_1(X3,X1,X4,X0,X5) = X2 | ~v1_funct_1(k3_tmap_1(X3,X1,X4,X0,X5)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~sP4(X1,X0,X5,X4,X3)) )),
% 2.76/0.72    inference(subsumption_resolution,[],[f345,f118])).
% 2.76/0.72  fof(f345,plain,(
% 2.76/0.72    ( ! [X4,X2,X0,X5,X3,X1] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k3_tmap_1(X3,X1,X4,X0,X5)) | k3_tmap_1(X3,X1,X4,X0,X5) = X2 | ~v1_funct_2(k3_tmap_1(X3,X1,X4,X0,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X3,X1,X4,X0,X5)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~sP4(X1,X0,X5,X4,X3)) )),
% 2.76/0.72    inference(resolution,[],[f115,f119])).
% 2.76/0.72  fof(f856,plain,(
% 2.76/0.72    ~spl10_28 | spl10_32),
% 2.76/0.72    inference(avatar_split_clause,[],[f740,f853,f771])).
% 2.76/0.72  fof(f740,plain,(
% 2.76/0.72    v1_funct_2(k4_tmap_1(sK5,sK5),u1_struct_0(sK5),u1_struct_0(sK5)) | ~sP4(sK5,sK5,k4_tmap_1(sK5,sK5),sK5,sK5)),
% 2.76/0.72    inference(superposition,[],[f118,f736])).
% 2.76/0.72  fof(f802,plain,(
% 2.76/0.72    spl10_31),
% 2.76/0.72    inference(avatar_contradiction_clause,[],[f801])).
% 2.76/0.72  fof(f801,plain,(
% 2.76/0.72    $false | spl10_31),
% 2.76/0.72    inference(subsumption_resolution,[],[f800,f81])).
% 2.76/0.72  fof(f800,plain,(
% 2.76/0.72    ~l1_pre_topc(sK5) | spl10_31),
% 2.76/0.72    inference(resolution,[],[f791,f89])).
% 2.76/0.72  fof(f791,plain,(
% 2.76/0.72    ~m1_pre_topc(sK5,sK5) | spl10_31),
% 2.76/0.72    inference(avatar_component_clause,[],[f789])).
% 2.76/0.72  fof(f797,plain,(
% 2.76/0.72    spl10_30),
% 2.76/0.72    inference(avatar_contradiction_clause,[],[f796])).
% 2.76/0.72  fof(f796,plain,(
% 2.76/0.72    $false | spl10_30),
% 2.76/0.72    inference(subsumption_resolution,[],[f795,f79])).
% 2.76/0.72  fof(f795,plain,(
% 2.76/0.72    v2_struct_0(sK5) | spl10_30),
% 2.76/0.72    inference(subsumption_resolution,[],[f794,f80])).
% 2.76/0.72  fof(f794,plain,(
% 2.76/0.72    ~v2_pre_topc(sK5) | v2_struct_0(sK5) | spl10_30),
% 2.76/0.72    inference(subsumption_resolution,[],[f793,f81])).
% 2.76/0.72  fof(f793,plain,(
% 2.76/0.72    ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | spl10_30),
% 2.76/0.72    inference(resolution,[],[f787,f148])).
% 2.76/0.72  fof(f787,plain,(
% 2.76/0.72    ~sP1(sK5,sK5) | spl10_30),
% 2.76/0.72    inference(avatar_component_clause,[],[f785])).
% 2.76/0.72  fof(f792,plain,(
% 2.76/0.72    ~spl10_30 | ~spl10_31 | spl10_28),
% 2.76/0.72    inference(avatar_split_clause,[],[f783,f771,f789,f785])).
% 2.76/0.72  fof(f783,plain,(
% 2.76/0.72    ~m1_pre_topc(sK5,sK5) | ~sP1(sK5,sK5) | spl10_28),
% 2.76/0.72    inference(subsumption_resolution,[],[f782,f79])).
% 2.76/0.72  fof(f782,plain,(
% 2.76/0.72    ~m1_pre_topc(sK5,sK5) | v2_struct_0(sK5) | ~sP1(sK5,sK5) | spl10_28),
% 2.76/0.72    inference(subsumption_resolution,[],[f781,f80])).
% 2.76/0.72  fof(f781,plain,(
% 2.76/0.72    ~m1_pre_topc(sK5,sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~sP1(sK5,sK5) | spl10_28),
% 2.76/0.72    inference(subsumption_resolution,[],[f780,f81])).
% 2.76/0.72  fof(f780,plain,(
% 2.76/0.72    ~m1_pre_topc(sK5,sK5) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~sP1(sK5,sK5) | spl10_28),
% 2.76/0.72    inference(duplicate_literal_removal,[],[f779])).
% 2.76/0.72  fof(f779,plain,(
% 2.76/0.72    ~m1_pre_topc(sK5,sK5) | ~m1_pre_topc(sK5,sK5) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~sP1(sK5,sK5) | spl10_28),
% 2.76/0.72    inference(resolution,[],[f773,f422])).
% 2.76/0.72  fof(f773,plain,(
% 2.76/0.72    ~sP4(sK5,sK5,k4_tmap_1(sK5,sK5),sK5,sK5) | spl10_28),
% 2.76/0.72    inference(avatar_component_clause,[],[f771])).
% 2.76/0.72  fof(f778,plain,(
% 2.76/0.72    ~spl10_28 | spl10_29),
% 2.76/0.72    inference(avatar_split_clause,[],[f739,f775,f771])).
% 2.76/0.72  fof(f739,plain,(
% 2.76/0.72    v1_funct_1(k4_tmap_1(sK5,sK5)) | ~sP4(sK5,sK5,k4_tmap_1(sK5,sK5),sK5,sK5)),
% 2.76/0.72    inference(superposition,[],[f117,f736])).
% 2.76/0.72  fof(f311,plain,(
% 2.76/0.72    spl10_12),
% 2.76/0.72    inference(avatar_contradiction_clause,[],[f310])).
% 2.76/0.72  fof(f310,plain,(
% 2.76/0.72    $false | spl10_12),
% 2.76/0.72    inference(subsumption_resolution,[],[f309,f151])).
% 2.76/0.72  fof(f309,plain,(
% 2.76/0.72    ~sP1(sK5,sK6) | spl10_12),
% 2.76/0.72    inference(resolution,[],[f300,f105])).
% 2.76/0.72  fof(f300,plain,(
% 2.76/0.72    ~v1_funct_2(k4_tmap_1(sK5,sK6),u1_struct_0(sK6),u1_struct_0(sK5)) | spl10_12),
% 2.76/0.72    inference(avatar_component_clause,[],[f298])).
% 2.76/0.72  fof(f308,plain,(
% 2.76/0.72    spl10_11),
% 2.76/0.72    inference(avatar_contradiction_clause,[],[f307])).
% 2.76/0.72  fof(f307,plain,(
% 2.76/0.72    $false | spl10_11),
% 2.76/0.72    inference(subsumption_resolution,[],[f306,f151])).
% 2.76/0.72  fof(f306,plain,(
% 2.76/0.72    ~sP1(sK5,sK6) | spl10_11),
% 2.76/0.72    inference(resolution,[],[f296,f104])).
% 2.76/0.72  fof(f296,plain,(
% 2.76/0.72    ~v1_funct_1(k4_tmap_1(sK5,sK6)) | spl10_11),
% 2.76/0.72    inference(avatar_component_clause,[],[f294])).
% 2.76/0.72  fof(f305,plain,(
% 2.76/0.72    ~spl10_11 | ~spl10_12 | spl10_13),
% 2.76/0.72    inference(avatar_split_clause,[],[f286,f302,f298,f294])).
% 2.76/0.72  fof(f286,plain,(
% 2.76/0.72    sP3(u1_struct_0(sK6),k4_tmap_1(sK5,sK6),sK7,u1_struct_0(sK5)) | ~v1_funct_2(k4_tmap_1(sK5,sK6),u1_struct_0(sK6),u1_struct_0(sK5)) | ~v1_funct_1(k4_tmap_1(sK5,sK6))),
% 2.76/0.72    inference(subsumption_resolution,[],[f281,f151])).
% 2.76/0.72  fof(f281,plain,(
% 2.76/0.72    sP3(u1_struct_0(sK6),k4_tmap_1(sK5,sK6),sK7,u1_struct_0(sK5)) | ~v1_funct_2(k4_tmap_1(sK5,sK6),u1_struct_0(sK6),u1_struct_0(sK5)) | ~v1_funct_1(k4_tmap_1(sK5,sK6)) | ~sP1(sK5,sK6)),
% 2.76/0.72    inference(resolution,[],[f279,f106])).
% 2.76/0.72  fof(f279,plain,(
% 2.76/0.72    ( ! [X9] : (~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5)))) | sP3(u1_struct_0(sK6),X9,sK7,u1_struct_0(sK5)) | ~v1_funct_2(X9,u1_struct_0(sK6),u1_struct_0(sK5)) | ~v1_funct_1(X9)) )),
% 2.76/0.72    inference(subsumption_resolution,[],[f278,f84])).
% 2.76/0.72  fof(f278,plain,(
% 2.76/0.72    ( ! [X9] : (sP3(u1_struct_0(sK6),X9,sK7,u1_struct_0(sK5)) | ~v1_funct_1(sK7) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5)))) | ~v1_funct_2(X9,u1_struct_0(sK6),u1_struct_0(sK5)) | ~v1_funct_1(X9)) )),
% 2.76/0.72    inference(subsumption_resolution,[],[f272,f85])).
% 2.76/0.72  fof(f272,plain,(
% 2.76/0.72    ( ! [X9] : (sP3(u1_struct_0(sK6),X9,sK7,u1_struct_0(sK5)) | ~v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK5)) | ~v1_funct_1(sK7) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5)))) | ~v1_funct_2(X9,u1_struct_0(sK6),u1_struct_0(sK5)) | ~v1_funct_1(X9)) )),
% 2.76/0.72    inference(resolution,[],[f113,f86])).
% 2.76/0.72  fof(f113,plain,(
% 2.76/0.72    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP3(X0,X2,X3,X1) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.76/0.72    inference(cnf_transformation,[],[f58])).
% 2.76/0.72  fof(f58,plain,(
% 2.76/0.72    ! [X0,X1,X2] : (! [X3] : (sP3(X0,X2,X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.76/0.72    inference(definition_folding,[],[f46,f57,f56])).
% 2.76/0.72  fof(f46,plain,(
% 2.76/0.72    ! [X0,X1,X2] : (! [X3] : ((r2_funct_2(X0,X1,X2,X3) <=> ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.76/0.72    inference(flattening,[],[f45])).
% 2.76/0.72  fof(f45,plain,(
% 2.76/0.72    ! [X0,X1,X2] : (! [X3] : ((r2_funct_2(X0,X1,X2,X3) <=> ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.76/0.72    inference(ennf_transformation,[],[f3])).
% 2.76/0.72  fof(f3,axiom,(
% 2.76/0.72    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_funct_2(X0,X1,X2,X3) <=> ! [X4] : (m1_subset_1(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)))))),
% 2.76/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_2)).
% 2.76/0.72  % SZS output end Proof for theBenchmark
% 2.76/0.72  % (24541)------------------------------
% 2.76/0.72  % (24541)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.76/0.72  % (24541)Termination reason: Refutation
% 2.76/0.72  
% 2.76/0.72  % (24541)Memory used [KB]: 11897
% 2.76/0.72  % (24541)Time elapsed: 0.290 s
% 2.76/0.72  % (24541)------------------------------
% 2.76/0.72  % (24541)------------------------------
% 2.76/0.74  % (24515)Success in time 0.378 s
%------------------------------------------------------------------------------
