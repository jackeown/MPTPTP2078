%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tmap_1__t28_tmap_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:13 EDT 2019

% Result     : Theorem 44.97s
% Output     : Refutation 44.97s
% Verified   : 
% Statistics : Number of formulae       :  191 (1169 expanded)
%              Number of leaves         :   23 ( 542 expanded)
%              Depth                    :   35
%              Number of atoms          :  894 (15979 expanded)
%              Number of equality atoms :   24 (  40 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11693,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f800,f937,f994,f2555,f3942,f11459,f11517,f11692])).

fof(f11692,plain,(
    ~ spl9_124 ),
    inference(avatar_contradiction_clause,[],[f11691])).

fof(f11691,plain,
    ( $false
    | ~ spl9_124 ),
    inference(subsumption_resolution,[],[f11690,f3976])).

fof(f3976,plain,(
    m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) ),
    inference(subsumption_resolution,[],[f3953,f90])).

fof(f90,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK3,sK4))
    & ~ r1_tsep_1(sK1,sK2)
    & m1_pre_topc(sK2,sK4)
    & m1_pre_topc(sK1,sK3)
    & m1_pre_topc(sK4,sK0)
    & ~ v2_struct_0(sK4)
    & m1_pre_topc(sK3,sK0)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f49,f70,f69,f68,f67,f66])).

fof(f66,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4))
                        & ~ r1_tsep_1(X1,X2)
                        & m1_pre_topc(X2,X4)
                        & m1_pre_topc(X1,X3)
                        & m1_pre_topc(X4,X0)
                        & ~ v2_struct_0(X4) )
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
                  ( ? [X4] :
                      ( ~ m1_pre_topc(k2_tsep_1(sK0,X1,X2),k2_tsep_1(sK0,X3,X4))
                      & ~ r1_tsep_1(X1,X2)
                      & m1_pre_topc(X2,X4)
                      & m1_pre_topc(X1,X3)
                      & m1_pre_topc(X4,sK0)
                      & ~ v2_struct_0(X4) )
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

fof(f67,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4))
                      & ~ r1_tsep_1(X1,X2)
                      & m1_pre_topc(X2,X4)
                      & m1_pre_topc(X1,X3)
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ~ m1_pre_topc(k2_tsep_1(X0,sK1,X2),k2_tsep_1(X0,X3,X4))
                    & ~ r1_tsep_1(sK1,X2)
                    & m1_pre_topc(X2,X4)
                    & m1_pre_topc(sK1,X3)
                    & m1_pre_topc(X4,X0)
                    & ~ v2_struct_0(X4) )
                & m1_pre_topc(X3,X0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(sK1,X0)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4))
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X2,X4)
                  & m1_pre_topc(X1,X3)
                  & m1_pre_topc(X4,X0)
                  & ~ v2_struct_0(X4) )
              & m1_pre_topc(X3,X0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ~ m1_pre_topc(k2_tsep_1(X0,X1,sK2),k2_tsep_1(X0,X3,X4))
                & ~ r1_tsep_1(X1,sK2)
                & m1_pre_topc(sK2,X4)
                & m1_pre_topc(X1,X3)
                & m1_pre_topc(X4,X0)
                & ~ v2_struct_0(X4) )
            & m1_pre_topc(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK2,X0)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4))
              & ~ r1_tsep_1(X1,X2)
              & m1_pre_topc(X2,X4)
              & m1_pre_topc(X1,X3)
              & m1_pre_topc(X4,X0)
              & ~ v2_struct_0(X4) )
          & m1_pre_topc(X3,X0)
          & ~ v2_struct_0(X3) )
     => ( ? [X4] :
            ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,sK3,X4))
            & ~ r1_tsep_1(X1,X2)
            & m1_pre_topc(X2,X4)
            & m1_pre_topc(X1,sK3)
            & m1_pre_topc(X4,X0)
            & ~ v2_struct_0(X4) )
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4))
          & ~ r1_tsep_1(X1,X2)
          & m1_pre_topc(X2,X4)
          & m1_pre_topc(X1,X3)
          & m1_pre_topc(X4,X0)
          & ~ v2_struct_0(X4) )
     => ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,sK4))
        & ~ r1_tsep_1(X1,X2)
        & m1_pre_topc(X2,sK4)
        & m1_pre_topc(X1,X3)
        & m1_pre_topc(sK4,X0)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4))
                      & ~ r1_tsep_1(X1,X2)
                      & m1_pre_topc(X2,X4)
                      & m1_pre_topc(X1,X3)
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4))
                      & ~ r1_tsep_1(X1,X2)
                      & m1_pre_topc(X2,X4)
                      & m1_pre_topc(X1,X3)
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
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
                   => ! [X4] :
                        ( ( m1_pre_topc(X4,X0)
                          & ~ v2_struct_0(X4) )
                       => ( ( m1_pre_topc(X2,X4)
                            & m1_pre_topc(X1,X3) )
                         => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4))
                            | r1_tsep_1(X1,X2) ) ) ) ) ) ) ) ),
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
                 => ! [X4] :
                      ( ( m1_pre_topc(X4,X0)
                        & ~ v2_struct_0(X4) )
                     => ( ( m1_pre_topc(X2,X4)
                          & m1_pre_topc(X1,X3) )
                       => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4))
                          | r1_tsep_1(X1,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t28_tmap_1.p',t28_tmap_1)).

fof(f3953,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f448,f91])).

fof(f91,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f71])).

fof(f448,plain,(
    ! [X4] :
      ( ~ m1_pre_topc(X4,sK0)
      | m1_pre_topc(k2_tsep_1(sK0,sK1,X4),sK0)
      | v2_struct_0(X4) ) ),
    inference(subsumption_resolution,[],[f447,f85])).

fof(f85,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f71])).

fof(f447,plain,(
    ! [X4] :
      ( m1_pre_topc(k2_tsep_1(sK0,sK1,X4),sK0)
      | ~ m1_pre_topc(X4,sK0)
      | v2_struct_0(X4)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f446,f87])).

fof(f87,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f71])).

fof(f446,plain,(
    ! [X4] :
      ( m1_pre_topc(k2_tsep_1(sK0,sK1,X4),sK0)
      | ~ m1_pre_topc(X4,sK0)
      | v2_struct_0(X4)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f421,f88])).

fof(f88,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f71])).

fof(f421,plain,(
    ! [X4] :
      ( m1_pre_topc(k2_tsep_1(sK0,sK1,X4),sK0)
      | ~ m1_pre_topc(X4,sK0)
      | v2_struct_0(X4)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f89,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t28_tmap_1.p',dt_k2_tsep_1)).

fof(f89,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f71])).

fof(f11690,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | ~ spl9_124 ),
    inference(subsumption_resolution,[],[f11689,f87])).

fof(f11689,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | ~ spl9_124 ),
    inference(subsumption_resolution,[],[f11688,f4979])).

fof(f4979,plain,(
    m1_pre_topc(k2_tsep_1(sK0,sK3,sK4),sK0) ),
    inference(subsumption_resolution,[],[f4973,f94])).

fof(f94,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f71])).

fof(f4973,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK3,sK4),sK0)
    | v2_struct_0(sK4) ),
    inference(resolution,[],[f604,f95])).

fof(f95,plain,(
    m1_pre_topc(sK4,sK0) ),
    inference(cnf_transformation,[],[f71])).

fof(f604,plain,(
    ! [X4] :
      ( ~ m1_pre_topc(X4,sK0)
      | m1_pre_topc(k2_tsep_1(sK0,sK3,X4),sK0)
      | v2_struct_0(X4) ) ),
    inference(subsumption_resolution,[],[f603,f85])).

fof(f603,plain,(
    ! [X4] :
      ( m1_pre_topc(k2_tsep_1(sK0,sK3,X4),sK0)
      | ~ m1_pre_topc(X4,sK0)
      | v2_struct_0(X4)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f602,f87])).

fof(f602,plain,(
    ! [X4] :
      ( m1_pre_topc(k2_tsep_1(sK0,sK3,X4),sK0)
      | ~ m1_pre_topc(X4,sK0)
      | v2_struct_0(X4)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f577,f92])).

fof(f92,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f71])).

fof(f577,plain,(
    ! [X4] :
      ( m1_pre_topc(k2_tsep_1(sK0,sK3,X4),sK0)
      | ~ m1_pre_topc(X4,sK0)
      | v2_struct_0(X4)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f93,f102])).

fof(f93,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f71])).

fof(f11688,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK3,sK4),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | ~ spl9_124 ),
    inference(resolution,[],[f987,f86])).

fof(f86,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f71])).

fof(f987,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(X0)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK3,sK4),X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X0) )
    | ~ spl9_124 ),
    inference(avatar_component_clause,[],[f986])).

fof(f986,plain,
    ( spl9_124
  <=> ! [X0] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK3,sK4),X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_124])])).

fof(f11517,plain,
    ( ~ spl9_96
    | ~ spl9_122
    | spl9_127
    | spl9_129 ),
    inference(avatar_contradiction_clause,[],[f11516])).

fof(f11516,plain,
    ( $false
    | ~ spl9_96
    | ~ spl9_122
    | ~ spl9_127
    | ~ spl9_129 ),
    inference(subsumption_resolution,[],[f1010,f11476])).

fof(f11476,plain,
    ( r1_tsep_1(sK3,sK4)
    | ~ spl9_96
    | ~ spl9_122
    | ~ spl9_127 ),
    inference(subsumption_resolution,[],[f11475,f85])).

fof(f11475,plain,
    ( r1_tsep_1(sK3,sK4)
    | v2_struct_0(sK0)
    | ~ spl9_96
    | ~ spl9_122
    | ~ spl9_127 ),
    inference(subsumption_resolution,[],[f11474,f87])).

fof(f11474,plain,
    ( r1_tsep_1(sK3,sK4)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_96
    | ~ spl9_122
    | ~ spl9_127 ),
    inference(subsumption_resolution,[],[f11473,f92])).

fof(f11473,plain,
    ( r1_tsep_1(sK3,sK4)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_96
    | ~ spl9_122
    | ~ spl9_127 ),
    inference(subsumption_resolution,[],[f11472,f93])).

fof(f11472,plain,
    ( r1_tsep_1(sK3,sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_96
    | ~ spl9_122
    | ~ spl9_127 ),
    inference(subsumption_resolution,[],[f11471,f94])).

fof(f11471,plain,
    ( r1_tsep_1(sK3,sK4)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_96
    | ~ spl9_122
    | ~ spl9_127 ),
    inference(subsumption_resolution,[],[f11470,f95])).

fof(f11470,plain,
    ( r1_tsep_1(sK3,sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_96
    | ~ spl9_122
    | ~ spl9_127 ),
    inference(subsumption_resolution,[],[f11469,f1720])).

fof(f1720,plain,(
    ~ v2_struct_0(k2_tsep_1(sK0,sK3,sK4)) ),
    inference(subsumption_resolution,[],[f1718,f95])).

fof(f1718,plain,
    ( ~ m1_pre_topc(sK4,sK0)
    | ~ v2_struct_0(k2_tsep_1(sK0,sK3,sK4)) ),
    inference(resolution,[],[f592,f94])).

fof(f592,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK0)
      | ~ v2_struct_0(k2_tsep_1(sK0,sK3,X0)) ) ),
    inference(subsumption_resolution,[],[f591,f85])).

fof(f591,plain,(
    ! [X0] :
      ( ~ v2_struct_0(k2_tsep_1(sK0,sK3,X0))
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f590,f87])).

fof(f590,plain,(
    ! [X0] :
      ( ~ v2_struct_0(k2_tsep_1(sK0,sK3,X0))
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f573,f92])).

fof(f573,plain,(
    ! [X0] :
      ( ~ v2_struct_0(k2_tsep_1(sK0,sK3,X0))
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f93,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f11469,plain,
    ( v2_struct_0(k2_tsep_1(sK0,sK3,sK4))
    | r1_tsep_1(sK3,sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_96
    | ~ spl9_122
    | ~ spl9_127 ),
    inference(subsumption_resolution,[],[f11468,f1765])).

fof(f1765,plain,(
    v1_pre_topc(k2_tsep_1(sK0,sK3,sK4)) ),
    inference(subsumption_resolution,[],[f1763,f95])).

fof(f1763,plain,
    ( ~ m1_pre_topc(sK4,sK0)
    | v1_pre_topc(k2_tsep_1(sK0,sK3,sK4)) ),
    inference(resolution,[],[f598,f94])).

fof(f598,plain,(
    ! [X2] :
      ( v2_struct_0(X2)
      | ~ m1_pre_topc(X2,sK0)
      | v1_pre_topc(k2_tsep_1(sK0,sK3,X2)) ) ),
    inference(subsumption_resolution,[],[f597,f85])).

fof(f597,plain,(
    ! [X2] :
      ( v1_pre_topc(k2_tsep_1(sK0,sK3,X2))
      | ~ m1_pre_topc(X2,sK0)
      | v2_struct_0(X2)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f596,f87])).

fof(f596,plain,(
    ! [X2] :
      ( v1_pre_topc(k2_tsep_1(sK0,sK3,X2))
      | ~ m1_pre_topc(X2,sK0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f575,f92])).

fof(f575,plain,(
    ! [X2] :
      ( v1_pre_topc(k2_tsep_1(sK0,sK3,X2))
      | ~ m1_pre_topc(X2,sK0)
      | v2_struct_0(X2)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f93,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( v1_pre_topc(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f11468,plain,
    ( ~ v1_pre_topc(k2_tsep_1(sK0,sK3,sK4))
    | v2_struct_0(k2_tsep_1(sK0,sK3,sK4))
    | r1_tsep_1(sK3,sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_96
    | ~ spl9_122
    | ~ spl9_127 ),
    inference(subsumption_resolution,[],[f11467,f4979])).

fof(f11467,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK3,sK4),sK0)
    | ~ v1_pre_topc(k2_tsep_1(sK0,sK3,sK4))
    | v2_struct_0(k2_tsep_1(sK0,sK3,sK4))
    | r1_tsep_1(sK3,sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_96
    | ~ spl9_122
    | ~ spl9_127 ),
    inference(subsumption_resolution,[],[f10866,f11308])).

fof(f11308,plain,
    ( r1_tarski(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)),k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK4)))
    | ~ spl9_96
    | ~ spl9_122 ),
    inference(resolution,[],[f3946,f799])).

fof(f799,plain,
    ( r1_tarski(u1_struct_0(sK1),u1_struct_0(sK3))
    | ~ spl9_96 ),
    inference(avatar_component_clause,[],[f798])).

fof(f798,plain,
    ( spl9_96
  <=> r1_tarski(u1_struct_0(sK1),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_96])])).

fof(f3946,plain,
    ( ! [X4,X3] :
        ( ~ r1_tarski(X3,X4)
        | r1_tarski(k3_xboole_0(X3,u1_struct_0(sK2)),k3_xboole_0(X4,u1_struct_0(sK4))) )
    | ~ spl9_122 ),
    inference(resolution,[],[f936,f120])).

fof(f120,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t28_tmap_1.p',t27_xboole_1)).

fof(f936,plain,
    ( r1_tarski(u1_struct_0(sK2),u1_struct_0(sK4))
    | ~ spl9_122 ),
    inference(avatar_component_clause,[],[f935])).

fof(f935,plain,
    ( spl9_122
  <=> r1_tarski(u1_struct_0(sK2),u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_122])])).

fof(f10866,plain,
    ( ~ r1_tarski(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)),k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK4)))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK3,sK4),sK0)
    | ~ v1_pre_topc(k2_tsep_1(sK0,sK3,sK4))
    | v2_struct_0(k2_tsep_1(sK0,sK3,sK4))
    | r1_tsep_1(sK3,sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_127 ),
    inference(superposition,[],[f6533,f126])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( u1_struct_0(k2_tsep_1(X0,X1,X2)) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | ~ v1_pre_topc(k2_tsep_1(X0,X1,X2))
      | v2_struct_0(k2_tsep_1(X0,X1,X2))
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f103])).

fof(f103,plain,(
    ! [X2,X0,X3,X1] :
      ( u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
      | k2_tsep_1(X0,X1,X2) != X3
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_pre_topc(X3)
      | v2_struct_0(X3)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k2_tsep_1(X0,X1,X2) = X3
                      | u1_struct_0(X3) != k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                    & ( u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
                      | k2_tsep_1(X0,X1,X2) != X3 ) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k2_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k2_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
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
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( ~ r1_tsep_1(X1,X2)
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & v1_pre_topc(X3)
                      & ~ v2_struct_0(X3) )
                   => ( k2_tsep_1(X0,X1,X2) = X3
                    <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t28_tmap_1.p',d5_tsep_1)).

fof(f6533,plain,
    ( ~ r1_tarski(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)),u1_struct_0(k2_tsep_1(sK0,sK3,sK4)))
    | ~ spl9_127 ),
    inference(subsumption_resolution,[],[f6532,f85])).

fof(f6532,plain,
    ( ~ r1_tarski(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)),u1_struct_0(k2_tsep_1(sK0,sK3,sK4)))
    | v2_struct_0(sK0)
    | ~ spl9_127 ),
    inference(subsumption_resolution,[],[f6531,f87])).

fof(f6531,plain,
    ( ~ r1_tarski(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)),u1_struct_0(k2_tsep_1(sK0,sK3,sK4)))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_127 ),
    inference(subsumption_resolution,[],[f6530,f88])).

fof(f6530,plain,
    ( ~ r1_tarski(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)),u1_struct_0(k2_tsep_1(sK0,sK3,sK4)))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_127 ),
    inference(subsumption_resolution,[],[f6529,f89])).

fof(f6529,plain,
    ( ~ r1_tarski(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)),u1_struct_0(k2_tsep_1(sK0,sK3,sK4)))
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_127 ),
    inference(subsumption_resolution,[],[f6528,f90])).

fof(f6528,plain,
    ( ~ r1_tarski(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)),u1_struct_0(k2_tsep_1(sK0,sK3,sK4)))
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_127 ),
    inference(subsumption_resolution,[],[f6527,f91])).

fof(f6527,plain,
    ( ~ r1_tarski(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)),u1_struct_0(k2_tsep_1(sK0,sK3,sK4)))
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_127 ),
    inference(subsumption_resolution,[],[f6526,f98])).

fof(f98,plain,(
    ~ r1_tsep_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f71])).

fof(f6526,plain,
    ( ~ r1_tarski(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)),u1_struct_0(k2_tsep_1(sK0,sK3,sK4)))
    | r1_tsep_1(sK1,sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_127 ),
    inference(subsumption_resolution,[],[f6525,f1213])).

fof(f1213,plain,(
    ~ v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f1196,f91])).

fof(f1196,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) ),
    inference(resolution,[],[f436,f90])).

fof(f436,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK0)
      | ~ v2_struct_0(k2_tsep_1(sK0,sK1,X0)) ) ),
    inference(subsumption_resolution,[],[f435,f85])).

fof(f435,plain,(
    ! [X0] :
      ( ~ v2_struct_0(k2_tsep_1(sK0,sK1,X0))
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f434,f87])).

fof(f434,plain,(
    ! [X0] :
      ( ~ v2_struct_0(k2_tsep_1(sK0,sK1,X0))
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f417,f88])).

fof(f417,plain,(
    ! [X0] :
      ( ~ v2_struct_0(k2_tsep_1(sK0,sK1,X0))
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f89,f100])).

fof(f6525,plain,
    ( ~ r1_tarski(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)),u1_struct_0(k2_tsep_1(sK0,sK3,sK4)))
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | r1_tsep_1(sK1,sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_127 ),
    inference(subsumption_resolution,[],[f6524,f1281])).

fof(f1281,plain,(
    v1_pre_topc(k2_tsep_1(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f1277,f91])).

fof(f1277,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v1_pre_topc(k2_tsep_1(sK0,sK1,sK2)) ),
    inference(resolution,[],[f442,f90])).

fof(f442,plain,(
    ! [X2] :
      ( v2_struct_0(X2)
      | ~ m1_pre_topc(X2,sK0)
      | v1_pre_topc(k2_tsep_1(sK0,sK1,X2)) ) ),
    inference(subsumption_resolution,[],[f441,f85])).

fof(f441,plain,(
    ! [X2] :
      ( v1_pre_topc(k2_tsep_1(sK0,sK1,X2))
      | ~ m1_pre_topc(X2,sK0)
      | v2_struct_0(X2)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f440,f87])).

fof(f440,plain,(
    ! [X2] :
      ( v1_pre_topc(k2_tsep_1(sK0,sK1,X2))
      | ~ m1_pre_topc(X2,sK0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f419,f88])).

fof(f419,plain,(
    ! [X2] :
      ( v1_pre_topc(k2_tsep_1(sK0,sK1,X2))
      | ~ m1_pre_topc(X2,sK0)
      | v2_struct_0(X2)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f89,f101])).

fof(f6524,plain,
    ( ~ r1_tarski(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)),u1_struct_0(k2_tsep_1(sK0,sK3,sK4)))
    | ~ v1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | r1_tsep_1(sK1,sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_127 ),
    inference(subsumption_resolution,[],[f6514,f3976])).

fof(f6514,plain,
    ( ~ r1_tarski(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)),u1_struct_0(k2_tsep_1(sK0,sK3,sK4)))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | ~ v1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | r1_tsep_1(sK1,sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_127 ),
    inference(superposition,[],[f993,f126])).

fof(f993,plain,
    ( ~ r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(k2_tsep_1(sK0,sK3,sK4)))
    | ~ spl9_127 ),
    inference(avatar_component_clause,[],[f992])).

fof(f992,plain,
    ( spl9_127
  <=> ~ r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(k2_tsep_1(sK0,sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_127])])).

fof(f1010,plain,
    ( ~ r1_tsep_1(sK3,sK4)
    | ~ spl9_129 ),
    inference(avatar_component_clause,[],[f1009])).

fof(f1009,plain,
    ( spl9_129
  <=> ~ r1_tsep_1(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_129])])).

fof(f11459,plain,
    ( ~ spl9_96
    | ~ spl9_122
    | ~ spl9_128 ),
    inference(avatar_contradiction_clause,[],[f11458])).

fof(f11458,plain,
    ( $false
    | ~ spl9_96
    | ~ spl9_122
    | ~ spl9_128 ),
    inference(subsumption_resolution,[],[f11448,f1188])).

fof(f1188,plain,(
    k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) != k1_xboole_0 ),
    inference(resolution,[],[f965,f118])).

fof(f118,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t28_tmap_1.p',d7_xboole_0)).

fof(f965,plain,(
    ~ r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f964,f821])).

fof(f821,plain,(
    l1_struct_0(sK1) ),
    inference(resolution,[],[f481,f116])).

fof(f116,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t28_tmap_1.p',dt_l1_pre_topc)).

fof(f481,plain,(
    l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f426,f87])).

fof(f426,plain,
    ( l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f89,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t28_tmap_1.p',dt_m1_pre_topc)).

fof(f964,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ l1_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f960,f845])).

fof(f845,plain,(
    l1_struct_0(sK2) ),
    inference(resolution,[],[f562,f116])).

fof(f562,plain,(
    l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f507,f87])).

fof(f507,plain,
    ( l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f91,f109])).

fof(f960,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK1) ),
    inference(resolution,[],[f98,f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X0,X1)
      | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_tsep_1(X0,X1)
              | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
            & ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
              | ~ r1_tsep_1(X0,X1) ) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t28_tmap_1.p',d3_tsep_1)).

fof(f11448,plain,
    ( k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = k1_xboole_0
    | ~ spl9_96
    | ~ spl9_122
    | ~ spl9_128 ),
    inference(resolution,[],[f11235,f123])).

fof(f123,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t28_tmap_1.p',t3_xboole_1)).

fof(f11235,plain,
    ( r1_tarski(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)),k1_xboole_0)
    | ~ spl9_96
    | ~ spl9_122
    | ~ spl9_128 ),
    inference(forward_demodulation,[],[f11230,f1970])).

fof(f1970,plain,
    ( k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK4)) = k1_xboole_0
    | ~ spl9_128 ),
    inference(resolution,[],[f1039,f117])).

fof(f117,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f1039,plain,
    ( r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ spl9_128 ),
    inference(subsumption_resolution,[],[f1038,f958])).

fof(f958,plain,(
    l1_struct_0(sK3) ),
    inference(resolution,[],[f637,f116])).

fof(f637,plain,(
    l1_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f582,f87])).

fof(f582,plain,
    ( l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f93,f109])).

fof(f1038,plain,
    ( r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ l1_struct_0(sK3)
    | ~ spl9_128 ),
    inference(subsumption_resolution,[],[f1036,f980])).

fof(f980,plain,(
    l1_struct_0(sK4) ),
    inference(resolution,[],[f723,f116])).

fof(f723,plain,(
    l1_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f658,f87])).

fof(f658,plain,
    ( l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f95,f109])).

fof(f1036,plain,
    ( r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ l1_struct_0(sK4)
    | ~ l1_struct_0(sK3)
    | ~ spl9_128 ),
    inference(resolution,[],[f1013,f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f1013,plain,
    ( r1_tsep_1(sK3,sK4)
    | ~ spl9_128 ),
    inference(avatar_component_clause,[],[f1012])).

fof(f1012,plain,
    ( spl9_128
  <=> r1_tsep_1(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_128])])).

fof(f11230,plain,
    ( r1_tarski(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)),k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK4)))
    | ~ spl9_96
    | ~ spl9_122 ),
    inference(resolution,[],[f2558,f936])).

fof(f2558,plain,
    ( ! [X2,X1] :
        ( ~ r1_tarski(X1,X2)
        | r1_tarski(k3_xboole_0(u1_struct_0(sK1),X1),k3_xboole_0(u1_struct_0(sK3),X2)) )
    | ~ spl9_96 ),
    inference(resolution,[],[f799,f120])).

fof(f3942,plain,(
    ~ spl9_120 ),
    inference(avatar_contradiction_clause,[],[f3941])).

fof(f3941,plain,
    ( $false
    | ~ spl9_120 ),
    inference(subsumption_resolution,[],[f3940,f91])).

fof(f3940,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ spl9_120 ),
    inference(subsumption_resolution,[],[f3939,f87])).

fof(f3939,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ spl9_120 ),
    inference(subsumption_resolution,[],[f3938,f95])).

fof(f3938,plain,
    ( ~ m1_pre_topc(sK4,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ spl9_120 ),
    inference(resolution,[],[f930,f86])).

fof(f930,plain,
    ( ! [X16] :
        ( ~ v2_pre_topc(X16)
        | ~ m1_pre_topc(sK4,X16)
        | ~ l1_pre_topc(X16)
        | ~ m1_pre_topc(sK2,X16) )
    | ~ spl9_120 ),
    inference(avatar_component_clause,[],[f929])).

fof(f929,plain,
    ( spl9_120
  <=> ! [X16] :
        ( ~ m1_pre_topc(sK4,X16)
        | ~ v2_pre_topc(X16)
        | ~ l1_pre_topc(X16)
        | ~ m1_pre_topc(sK2,X16) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_120])])).

fof(f2555,plain,(
    ~ spl9_94 ),
    inference(avatar_contradiction_clause,[],[f2554])).

fof(f2554,plain,
    ( $false
    | ~ spl9_94 ),
    inference(subsumption_resolution,[],[f2553,f89])).

fof(f2553,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ spl9_94 ),
    inference(subsumption_resolution,[],[f2552,f87])).

fof(f2552,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ spl9_94 ),
    inference(subsumption_resolution,[],[f2551,f93])).

fof(f2551,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ spl9_94 ),
    inference(resolution,[],[f793,f86])).

fof(f793,plain,
    ( ! [X16] :
        ( ~ v2_pre_topc(X16)
        | ~ m1_pre_topc(sK3,X16)
        | ~ l1_pre_topc(X16)
        | ~ m1_pre_topc(sK1,X16) )
    | ~ spl9_94 ),
    inference(avatar_component_clause,[],[f792])).

fof(f792,plain,
    ( spl9_94
  <=> ! [X16] :
        ( ~ m1_pre_topc(sK3,X16)
        | ~ v2_pre_topc(X16)
        | ~ l1_pre_topc(X16)
        | ~ m1_pre_topc(sK1,X16) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_94])])).

fof(f994,plain,
    ( spl9_124
    | ~ spl9_127 ),
    inference(avatar_split_clause,[],[f982,f992,f986])).

fof(f982,plain,(
    ! [X0] :
      ( ~ r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(k2_tsep_1(sK0,sK3,sK4)))
      | ~ m1_pre_topc(k2_tsep_1(sK0,sK3,sK4),X0)
      | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(resolution,[],[f99,f111])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X1,X2)
      | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
                  | ~ m1_pre_topc(X1,X2) )
                & ( m1_pre_topc(X1,X2)
                  | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f39])).

fof(f39,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t28_tmap_1.p',t4_tsep_1)).

fof(f99,plain,(
    ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK3,sK4)) ),
    inference(cnf_transformation,[],[f71])).

fof(f937,plain,
    ( spl9_120
    | spl9_122 ),
    inference(avatar_split_clause,[],[f875,f935,f929])).

fof(f875,plain,(
    ! [X16] :
      ( r1_tarski(u1_struct_0(sK2),u1_struct_0(sK4))
      | ~ m1_pre_topc(sK4,X16)
      | ~ m1_pre_topc(sK2,X16)
      | ~ l1_pre_topc(X16)
      | ~ v2_pre_topc(X16) ) ),
    inference(resolution,[],[f97,f112])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f97,plain,(
    m1_pre_topc(sK2,sK4) ),
    inference(cnf_transformation,[],[f71])).

fof(f800,plain,
    ( spl9_94
    | spl9_96 ),
    inference(avatar_split_clause,[],[f738,f798,f792])).

fof(f738,plain,(
    ! [X16] :
      ( r1_tarski(u1_struct_0(sK1),u1_struct_0(sK3))
      | ~ m1_pre_topc(sK3,X16)
      | ~ m1_pre_topc(sK1,X16)
      | ~ l1_pre_topc(X16)
      | ~ v2_pre_topc(X16) ) ),
    inference(resolution,[],[f96,f112])).

fof(f96,plain,(
    m1_pre_topc(sK1,sK3) ),
    inference(cnf_transformation,[],[f71])).
%------------------------------------------------------------------------------
