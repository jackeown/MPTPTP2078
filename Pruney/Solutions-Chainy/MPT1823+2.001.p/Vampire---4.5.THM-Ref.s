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
% DateTime   : Thu Dec  3 13:19:47 EST 2020

% Result     : Theorem 1.53s
% Output     : Refutation 1.53s
% Verified   : 
% Statistics : Number of formulae       :  222 ( 951 expanded)
%              Number of leaves         :   31 ( 425 expanded)
%              Depth                    :   38
%              Number of atoms          : 1457 (11857 expanded)
%              Number of equality atoms :   42 ( 824 expanded)
%              Maximal formula depth    :   29 (   8 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f659,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f129,f134,f161,f186,f189,f344,f462,f483,f488,f633,f649,f658])).

fof(f658,plain,
    ( ~ spl8_5
    | spl8_9 ),
    inference(avatar_contradiction_clause,[],[f657])).

fof(f657,plain,
    ( $false
    | ~ spl8_5
    | spl8_9 ),
    inference(subsumption_resolution,[],[f656,f59])).

fof(f59,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,
    ( ~ r1_funct_2(u1_struct_0(sK3),u1_struct_0(sK4),u1_struct_0(k1_tsep_1(sK3,sK5,sK6)),u1_struct_0(sK4),sK7,k10_tmap_1(sK3,sK4,sK5,sK6,k2_tmap_1(sK3,sK4,sK7,sK5),k2_tmap_1(sK3,sK4,sK7,sK6)))
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    & v1_funct_2(sK7,u1_struct_0(sK3),u1_struct_0(sK4))
    & v1_funct_1(sK7)
    & sK3 = k1_tsep_1(sK3,sK5,sK6)
    & m1_pre_topc(sK6,sK3)
    & ~ v2_struct_0(sK6)
    & m1_pre_topc(sK5,sK3)
    & ~ v2_struct_0(sK5)
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4)
    & ~ v2_struct_0(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f15,f46,f45,f44,f43,f42])).

fof(f42,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3)))
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                    & k1_tsep_1(X0,X2,X3) = X0
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
                      ( ~ r1_funct_2(u1_struct_0(sK3),u1_struct_0(X1),u1_struct_0(k1_tsep_1(sK3,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(sK3,X1,X2,X3,k2_tmap_1(sK3,X1,X4,X2),k2_tmap_1(sK3,X1,X4,X3)))
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & sK3 = k1_tsep_1(sK3,X2,X3)
                  & m1_pre_topc(X3,sK3)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK3)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ~ r1_funct_2(u1_struct_0(sK3),u1_struct_0(X1),u1_struct_0(k1_tsep_1(sK3,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(sK3,X1,X2,X3,k2_tmap_1(sK3,X1,X4,X2),k2_tmap_1(sK3,X1,X4,X3)))
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
                    & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X1))
                    & v1_funct_1(X4) )
                & sK3 = k1_tsep_1(sK3,X2,X3)
                & m1_pre_topc(X3,sK3)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK3)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ~ r1_funct_2(u1_struct_0(sK3),u1_struct_0(sK4),u1_struct_0(k1_tsep_1(sK3,X2,X3)),u1_struct_0(sK4),X4,k10_tmap_1(sK3,sK4,X2,X3,k2_tmap_1(sK3,sK4,X4,X2),k2_tmap_1(sK3,sK4,X4,X3)))
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
                  & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK4))
                  & v1_funct_1(X4) )
              & sK3 = k1_tsep_1(sK3,X2,X3)
              & m1_pre_topc(X3,sK3)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK3)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK4)
      & v2_pre_topc(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ~ r1_funct_2(u1_struct_0(sK3),u1_struct_0(sK4),u1_struct_0(k1_tsep_1(sK3,X2,X3)),u1_struct_0(sK4),X4,k10_tmap_1(sK3,sK4,X2,X3,k2_tmap_1(sK3,sK4,X4,X2),k2_tmap_1(sK3,sK4,X4,X3)))
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
                & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK4))
                & v1_funct_1(X4) )
            & sK3 = k1_tsep_1(sK3,X2,X3)
            & m1_pre_topc(X3,sK3)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK3)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ~ r1_funct_2(u1_struct_0(sK3),u1_struct_0(sK4),u1_struct_0(k1_tsep_1(sK3,sK5,X3)),u1_struct_0(sK4),X4,k10_tmap_1(sK3,sK4,sK5,X3,k2_tmap_1(sK3,sK4,X4,sK5),k2_tmap_1(sK3,sK4,X4,X3)))
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
              & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK4))
              & v1_funct_1(X4) )
          & sK3 = k1_tsep_1(sK3,sK5,X3)
          & m1_pre_topc(X3,sK3)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK5,sK3)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ~ r1_funct_2(u1_struct_0(sK3),u1_struct_0(sK4),u1_struct_0(k1_tsep_1(sK3,sK5,X3)),u1_struct_0(sK4),X4,k10_tmap_1(sK3,sK4,sK5,X3,k2_tmap_1(sK3,sK4,X4,sK5),k2_tmap_1(sK3,sK4,X4,X3)))
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
            & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK4))
            & v1_funct_1(X4) )
        & sK3 = k1_tsep_1(sK3,sK5,X3)
        & m1_pre_topc(X3,sK3)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ~ r1_funct_2(u1_struct_0(sK3),u1_struct_0(sK4),u1_struct_0(k1_tsep_1(sK3,sK5,sK6)),u1_struct_0(sK4),X4,k10_tmap_1(sK3,sK4,sK5,sK6,k2_tmap_1(sK3,sK4,X4,sK5),k2_tmap_1(sK3,sK4,X4,sK6)))
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
          & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK4))
          & v1_funct_1(X4) )
      & sK3 = k1_tsep_1(sK3,sK5,sK6)
      & m1_pre_topc(sK6,sK3)
      & ~ v2_struct_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ? [X4] :
        ( ~ r1_funct_2(u1_struct_0(sK3),u1_struct_0(sK4),u1_struct_0(k1_tsep_1(sK3,sK5,sK6)),u1_struct_0(sK4),X4,k10_tmap_1(sK3,sK4,sK5,sK6,k2_tmap_1(sK3,sK4,X4,sK5),k2_tmap_1(sK3,sK4,X4,sK6)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
        & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK4))
        & v1_funct_1(X4) )
   => ( ~ r1_funct_2(u1_struct_0(sK3),u1_struct_0(sK4),u1_struct_0(k1_tsep_1(sK3,sK5,sK6)),u1_struct_0(sK4),sK7,k10_tmap_1(sK3,sK4,sK5,sK6,k2_tmap_1(sK3,sK4,sK7,sK5),k2_tmap_1(sK3,sK4,sK7,sK6)))
      & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
      & v1_funct_2(sK7,u1_struct_0(sK3),u1_struct_0(sK4))
      & v1_funct_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3)))
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & k1_tsep_1(X0,X2,X3) = X0
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3)))
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & k1_tsep_1(X0,X2,X3) = X0
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
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
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
                   => ( k1_tsep_1(X0,X2,X3) = X0
                     => ! [X4] :
                          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                            & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                            & v1_funct_1(X4) )
                         => r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3))) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
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
                 => ( k1_tsep_1(X0,X2,X3) = X0
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_tmap_1)).

fof(f656,plain,
    ( v2_struct_0(sK4)
    | ~ spl8_5
    | spl8_9 ),
    inference(subsumption_resolution,[],[f655,f156])).

fof(f156,plain,
    ( l1_struct_0(sK4)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f155])).

fof(f155,plain,
    ( spl8_5
  <=> l1_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f655,plain,
    ( ~ l1_struct_0(sK4)
    | v2_struct_0(sK4)
    | spl8_9 ),
    inference(resolution,[],[f654,f73])).

fof(f73,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f654,plain,
    ( v1_xboole_0(u1_struct_0(sK4))
    | spl8_9 ),
    inference(subsumption_resolution,[],[f653,f67])).

fof(f67,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f47])).

fof(f653,plain,
    ( ~ v1_funct_1(sK7)
    | v1_xboole_0(u1_struct_0(sK4))
    | spl8_9 ),
    inference(subsumption_resolution,[],[f652,f68])).

fof(f68,plain,(
    v1_funct_2(sK7,u1_struct_0(sK3),u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f47])).

fof(f652,plain,
    ( ~ v1_funct_2(sK7,u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ v1_funct_1(sK7)
    | v1_xboole_0(u1_struct_0(sK4))
    | spl8_9 ),
    inference(subsumption_resolution,[],[f651,f69])).

fof(f69,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) ),
    inference(cnf_transformation,[],[f47])).

fof(f651,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | ~ v1_funct_2(sK7,u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ v1_funct_1(sK7)
    | v1_xboole_0(u1_struct_0(sK4))
    | spl8_9 ),
    inference(duplicate_literal_removal,[],[f650])).

fof(f650,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | ~ v1_funct_2(sK7,u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | ~ v1_funct_2(sK7,u1_struct_0(sK3),u1_struct_0(sK4))
    | v1_xboole_0(u1_struct_0(sK4))
    | v1_xboole_0(u1_struct_0(sK4))
    | spl8_9 ),
    inference(resolution,[],[f343,f95])).

fof(f95,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r1_funct_2(X0,X1,X2,X3,X5,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X5,X0,X1)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(duplicate_literal_removal,[],[f94])).

fof(f94,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r1_funct_2(X0,X1,X2,X3,X5,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X5,X0,X1)
      | ~ v1_funct_1(X5)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      | X4 != X5
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
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
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f343,plain,
    ( ~ r1_funct_2(u1_struct_0(sK3),u1_struct_0(sK4),u1_struct_0(sK3),u1_struct_0(sK4),sK7,sK7)
    | spl8_9 ),
    inference(avatar_component_clause,[],[f341])).

fof(f341,plain,
    ( spl8_9
  <=> r1_funct_2(u1_struct_0(sK3),u1_struct_0(sK4),u1_struct_0(sK3),u1_struct_0(sK4),sK7,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f649,plain,
    ( ~ spl8_6
    | spl8_13 ),
    inference(avatar_contradiction_clause,[],[f648])).

fof(f648,plain,
    ( $false
    | ~ spl8_6
    | spl8_13 ),
    inference(subsumption_resolution,[],[f647,f99])).

fof(f99,plain,(
    l1_pre_topc(sK5) ),
    inference(subsumption_resolution,[],[f97,f58])).

fof(f58,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f97,plain,
    ( l1_pre_topc(sK5)
    | ~ l1_pre_topc(sK3) ),
    inference(resolution,[],[f72,f63])).

fof(f63,plain,(
    m1_pre_topc(sK5,sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f647,plain,
    ( ~ l1_pre_topc(sK5)
    | ~ spl8_6
    | spl8_13 ),
    inference(resolution,[],[f646,f71])).

fof(f71,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f646,plain,
    ( ~ l1_struct_0(sK5)
    | ~ spl8_6
    | spl8_13 ),
    inference(resolution,[],[f634,f160])).

fof(f160,plain,
    ( ! [X0] :
        ( sP1(sK4,X0,sK7,sK3)
        | ~ l1_struct_0(X0) )
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f159])).

fof(f159,plain,
    ( spl8_6
  <=> ! [X0] :
        ( ~ l1_struct_0(X0)
        | sP1(sK4,X0,sK7,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f634,plain,
    ( ~ sP1(sK4,sK5,sK7,sK3)
    | spl8_13 ),
    inference(resolution,[],[f461,f83])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k2_tmap_1(X3,X0,X2,X1)) )
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f50])).

fof(f50,plain,(
    ! [X1,X3,X2,X0] :
      ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ sP1(X1,X3,X2,X0) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X1,X3,X2,X0] :
      ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ sP1(X1,X3,X2,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f461,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK3,sK4,sK7,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))
    | spl8_13 ),
    inference(avatar_component_clause,[],[f459])).

fof(f459,plain,
    ( spl8_13
  <=> m1_subset_1(k2_tmap_1(sK3,sK4,sK7,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f633,plain,
    ( ~ spl8_6
    | spl8_12 ),
    inference(avatar_contradiction_clause,[],[f632])).

fof(f632,plain,
    ( $false
    | ~ spl8_6
    | spl8_12 ),
    inference(subsumption_resolution,[],[f631,f99])).

fof(f631,plain,
    ( ~ l1_pre_topc(sK5)
    | ~ spl8_6
    | spl8_12 ),
    inference(resolution,[],[f630,f71])).

fof(f630,plain,
    ( ~ l1_struct_0(sK5)
    | ~ spl8_6
    | spl8_12 ),
    inference(resolution,[],[f629,f160])).

fof(f629,plain,
    ( ~ sP1(sK4,sK5,sK7,sK3)
    | spl8_12 ),
    inference(resolution,[],[f457,f82])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0))
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f457,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK3,sK4,sK7,sK5),u1_struct_0(sK5),u1_struct_0(sK4))
    | spl8_12 ),
    inference(avatar_component_clause,[],[f455])).

fof(f455,plain,
    ( spl8_12
  <=> v1_funct_2(k2_tmap_1(sK3,sK4,sK7,sK5),u1_struct_0(sK5),u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f488,plain,
    ( ~ spl8_6
    | spl8_11 ),
    inference(avatar_contradiction_clause,[],[f487])).

fof(f487,plain,
    ( $false
    | ~ spl8_6
    | spl8_11 ),
    inference(subsumption_resolution,[],[f486,f99])).

fof(f486,plain,
    ( ~ l1_pre_topc(sK5)
    | ~ spl8_6
    | spl8_11 ),
    inference(resolution,[],[f485,f71])).

fof(f485,plain,
    ( ~ l1_struct_0(sK5)
    | ~ spl8_6
    | spl8_11 ),
    inference(resolution,[],[f484,f160])).

fof(f484,plain,
    ( ~ sP1(sK4,sK5,sK7,sK3)
    | spl8_11 ),
    inference(resolution,[],[f453,f81])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_tmap_1(X3,X0,X2,X1))
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f453,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK3,sK4,sK7,sK5))
    | spl8_11 ),
    inference(avatar_component_clause,[],[f451])).

fof(f451,plain,
    ( spl8_11
  <=> v1_funct_1(k2_tmap_1(sK3,sK4,sK7,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f483,plain,
    ( ~ spl8_6
    | spl8_10 ),
    inference(avatar_contradiction_clause,[],[f482])).

fof(f482,plain,
    ( $false
    | ~ spl8_6
    | spl8_10 ),
    inference(subsumption_resolution,[],[f481,f100])).

fof(f100,plain,(
    l1_pre_topc(sK6) ),
    inference(subsumption_resolution,[],[f98,f58])).

fof(f98,plain,
    ( l1_pre_topc(sK6)
    | ~ l1_pre_topc(sK3) ),
    inference(resolution,[],[f72,f65])).

fof(f65,plain,(
    m1_pre_topc(sK6,sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f481,plain,
    ( ~ l1_pre_topc(sK6)
    | ~ spl8_6
    | spl8_10 ),
    inference(resolution,[],[f480,f71])).

fof(f480,plain,
    ( ~ l1_struct_0(sK6)
    | ~ spl8_6
    | spl8_10 ),
    inference(resolution,[],[f449,f160])).

fof(f449,plain,
    ( ~ sP1(sK4,sK6,sK7,sK3)
    | spl8_10 ),
    inference(avatar_component_clause,[],[f447])).

fof(f447,plain,
    ( spl8_10
  <=> sP1(sK4,sK6,sK7,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f462,plain,
    ( ~ spl8_10
    | ~ spl8_11
    | ~ spl8_12
    | ~ spl8_13
    | spl8_8 ),
    inference(avatar_split_clause,[],[f445,f337,f459,f455,f451,f447])).

fof(f337,plain,
    ( spl8_8
  <=> sP2(sK4,sK6,sK5,sK3,k2_tmap_1(sK3,sK4,sK7,sK6),k2_tmap_1(sK3,sK4,sK7,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f445,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK3,sK4,sK7,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))
    | ~ v1_funct_2(k2_tmap_1(sK3,sK4,sK7,sK5),u1_struct_0(sK5),u1_struct_0(sK4))
    | ~ v1_funct_1(k2_tmap_1(sK3,sK4,sK7,sK5))
    | ~ sP1(sK4,sK6,sK7,sK3)
    | spl8_8 ),
    inference(subsumption_resolution,[],[f444,f56])).

fof(f56,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f444,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK3,sK4,sK7,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))
    | ~ v1_funct_2(k2_tmap_1(sK3,sK4,sK7,sK5),u1_struct_0(sK5),u1_struct_0(sK4))
    | ~ v1_funct_1(k2_tmap_1(sK3,sK4,sK7,sK5))
    | v2_struct_0(sK3)
    | ~ sP1(sK4,sK6,sK7,sK3)
    | spl8_8 ),
    inference(subsumption_resolution,[],[f443,f57])).

fof(f57,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f443,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK3,sK4,sK7,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))
    | ~ v1_funct_2(k2_tmap_1(sK3,sK4,sK7,sK5),u1_struct_0(sK5),u1_struct_0(sK4))
    | ~ v1_funct_1(k2_tmap_1(sK3,sK4,sK7,sK5))
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ sP1(sK4,sK6,sK7,sK3)
    | spl8_8 ),
    inference(subsumption_resolution,[],[f442,f58])).

fof(f442,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK3,sK4,sK7,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))
    | ~ v1_funct_2(k2_tmap_1(sK3,sK4,sK7,sK5),u1_struct_0(sK5),u1_struct_0(sK4))
    | ~ v1_funct_1(k2_tmap_1(sK3,sK4,sK7,sK5))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ sP1(sK4,sK6,sK7,sK3)
    | spl8_8 ),
    inference(subsumption_resolution,[],[f441,f59])).

fof(f441,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK3,sK4,sK7,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))
    | ~ v1_funct_2(k2_tmap_1(sK3,sK4,sK7,sK5),u1_struct_0(sK5),u1_struct_0(sK4))
    | ~ v1_funct_1(k2_tmap_1(sK3,sK4,sK7,sK5))
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ sP1(sK4,sK6,sK7,sK3)
    | spl8_8 ),
    inference(subsumption_resolution,[],[f440,f60])).

fof(f60,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f47])).

fof(f440,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK3,sK4,sK7,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))
    | ~ v1_funct_2(k2_tmap_1(sK3,sK4,sK7,sK5),u1_struct_0(sK5),u1_struct_0(sK4))
    | ~ v1_funct_1(k2_tmap_1(sK3,sK4,sK7,sK5))
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ sP1(sK4,sK6,sK7,sK3)
    | spl8_8 ),
    inference(subsumption_resolution,[],[f439,f61])).

fof(f61,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f47])).

fof(f439,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK3,sK4,sK7,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))
    | ~ v1_funct_2(k2_tmap_1(sK3,sK4,sK7,sK5),u1_struct_0(sK5),u1_struct_0(sK4))
    | ~ v1_funct_1(k2_tmap_1(sK3,sK4,sK7,sK5))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ sP1(sK4,sK6,sK7,sK3)
    | spl8_8 ),
    inference(subsumption_resolution,[],[f438,f62])).

fof(f62,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f47])).

fof(f438,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK3,sK4,sK7,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))
    | ~ v1_funct_2(k2_tmap_1(sK3,sK4,sK7,sK5),u1_struct_0(sK5),u1_struct_0(sK4))
    | ~ v1_funct_1(k2_tmap_1(sK3,sK4,sK7,sK5))
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ sP1(sK4,sK6,sK7,sK3)
    | spl8_8 ),
    inference(subsumption_resolution,[],[f437,f63])).

fof(f437,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK3,sK4,sK7,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))
    | ~ v1_funct_2(k2_tmap_1(sK3,sK4,sK7,sK5),u1_struct_0(sK5),u1_struct_0(sK4))
    | ~ v1_funct_1(k2_tmap_1(sK3,sK4,sK7,sK5))
    | ~ m1_pre_topc(sK5,sK3)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ sP1(sK4,sK6,sK7,sK3)
    | spl8_8 ),
    inference(subsumption_resolution,[],[f436,f64])).

fof(f64,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f47])).

fof(f436,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK3,sK4,sK7,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))
    | ~ v1_funct_2(k2_tmap_1(sK3,sK4,sK7,sK5),u1_struct_0(sK5),u1_struct_0(sK4))
    | ~ v1_funct_1(k2_tmap_1(sK3,sK4,sK7,sK5))
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(sK5,sK3)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ sP1(sK4,sK6,sK7,sK3)
    | spl8_8 ),
    inference(subsumption_resolution,[],[f432,f65])).

fof(f432,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK3,sK4,sK7,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))
    | ~ v1_funct_2(k2_tmap_1(sK3,sK4,sK7,sK5),u1_struct_0(sK5),u1_struct_0(sK4))
    | ~ v1_funct_1(k2_tmap_1(sK3,sK4,sK7,sK5))
    | ~ m1_pre_topc(sK6,sK3)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(sK5,sK3)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ sP1(sK4,sK6,sK7,sK3)
    | spl8_8 ),
    inference(resolution,[],[f228,f339])).

fof(f339,plain,
    ( ~ sP2(sK4,sK6,sK5,sK3,k2_tmap_1(sK3,sK4,sK7,sK6),k2_tmap_1(sK3,sK4,sK7,sK5))
    | spl8_8 ),
    inference(avatar_component_clause,[],[f337])).

fof(f228,plain,(
    ! [X6,X4,X8,X7,X5,X3,X9] :
      ( sP2(X3,X4,X5,X6,k2_tmap_1(X7,X3,X8,X4),X9)
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X3))))
      | ~ v1_funct_2(X9,u1_struct_0(X5),u1_struct_0(X3))
      | ~ v1_funct_1(X9)
      | ~ m1_pre_topc(X4,X6)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X5,X6)
      | v2_struct_0(X5)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6)
      | ~ sP1(X3,X4,X8,X7) ) ),
    inference(subsumption_resolution,[],[f227,f81])).

fof(f227,plain,(
    ! [X6,X4,X8,X7,X5,X3,X9] :
      ( sP2(X3,X4,X5,X6,k2_tmap_1(X7,X3,X8,X4),X9)
      | ~ v1_funct_1(k2_tmap_1(X7,X3,X8,X4))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X3))))
      | ~ v1_funct_2(X9,u1_struct_0(X5),u1_struct_0(X3))
      | ~ v1_funct_1(X9)
      | ~ m1_pre_topc(X4,X6)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X5,X6)
      | v2_struct_0(X5)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6)
      | ~ sP1(X3,X4,X8,X7) ) ),
    inference(subsumption_resolution,[],[f218,f82])).

fof(f218,plain,(
    ! [X6,X4,X8,X7,X5,X3,X9] :
      ( sP2(X3,X4,X5,X6,k2_tmap_1(X7,X3,X8,X4),X9)
      | ~ v1_funct_2(k2_tmap_1(X7,X3,X8,X4),u1_struct_0(X4),u1_struct_0(X3))
      | ~ v1_funct_1(k2_tmap_1(X7,X3,X8,X4))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X3))))
      | ~ v1_funct_2(X9,u1_struct_0(X5),u1_struct_0(X3))
      | ~ v1_funct_1(X9)
      | ~ m1_pre_topc(X4,X6)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X5,X6)
      | v2_struct_0(X5)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6)
      | ~ sP1(X3,X4,X8,X7) ) ),
    inference(resolution,[],[f92,f83])).

fof(f92,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | sP2(X1,X3,X2,X0,X5,X4)
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( sP2(X1,X3,X2,X0,X5,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f35,f40])).

fof(f40,plain,(
    ! [X1,X3,X2,X0,X5,X4] :
      ( ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
      | ~ sP2(X1,X3,X2,X0,X5,X4) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(X4)
        & m1_pre_topc(X3,X0)
        & ~ v2_struct_0(X3)
        & m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_tmap_1)).

fof(f344,plain,
    ( ~ spl8_8
    | ~ spl8_9
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f335,f131,f341,f337])).

fof(f131,plain,
    ( spl8_3
  <=> m1_pre_topc(sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f335,plain,
    ( ~ r1_funct_2(u1_struct_0(sK3),u1_struct_0(sK4),u1_struct_0(sK3),u1_struct_0(sK4),sK7,sK7)
    | ~ sP2(sK4,sK6,sK5,sK3,k2_tmap_1(sK3,sK4,sK7,sK6),k2_tmap_1(sK3,sK4,sK7,sK5))
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f334,f69])).

fof(f334,plain,
    ( ~ r1_funct_2(u1_struct_0(sK3),u1_struct_0(sK4),u1_struct_0(sK3),u1_struct_0(sK4),sK7,sK7)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | ~ sP2(sK4,sK6,sK5,sK3,k2_tmap_1(sK3,sK4,sK7,sK6),k2_tmap_1(sK3,sK4,sK7,sK5))
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f333,f59])).

fof(f333,plain,
    ( ~ r1_funct_2(u1_struct_0(sK3),u1_struct_0(sK4),u1_struct_0(sK3),u1_struct_0(sK4),sK7,sK7)
    | v2_struct_0(sK4)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | ~ sP2(sK4,sK6,sK5,sK3,k2_tmap_1(sK3,sK4,sK7,sK6),k2_tmap_1(sK3,sK4,sK7,sK5))
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f332,f60])).

fof(f332,plain,
    ( ~ r1_funct_2(u1_struct_0(sK3),u1_struct_0(sK4),u1_struct_0(sK3),u1_struct_0(sK4),sK7,sK7)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | ~ sP2(sK4,sK6,sK5,sK3,k2_tmap_1(sK3,sK4,sK7,sK6),k2_tmap_1(sK3,sK4,sK7,sK5))
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f331,f61])).

fof(f331,plain,
    ( ~ r1_funct_2(u1_struct_0(sK3),u1_struct_0(sK4),u1_struct_0(sK3),u1_struct_0(sK4),sK7,sK7)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | ~ sP2(sK4,sK6,sK5,sK3,k2_tmap_1(sK3,sK4,sK7,sK6),k2_tmap_1(sK3,sK4,sK7,sK5))
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f330,f67])).

fof(f330,plain,
    ( ~ r1_funct_2(u1_struct_0(sK3),u1_struct_0(sK4),u1_struct_0(sK3),u1_struct_0(sK4),sK7,sK7)
    | ~ v1_funct_1(sK7)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | ~ sP2(sK4,sK6,sK5,sK3,k2_tmap_1(sK3,sK4,sK7,sK6),k2_tmap_1(sK3,sK4,sK7,sK5))
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f299,f68])).

fof(f299,plain,
    ( ~ r1_funct_2(u1_struct_0(sK3),u1_struct_0(sK4),u1_struct_0(sK3),u1_struct_0(sK4),sK7,sK7)
    | ~ v1_funct_2(sK7,u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ v1_funct_1(sK7)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | ~ sP2(sK4,sK6,sK5,sK3,k2_tmap_1(sK3,sK4,sK7,sK6),k2_tmap_1(sK3,sK4,sK7,sK5))
    | ~ spl8_3 ),
    inference(superposition,[],[f115,f294])).

fof(f294,plain,
    ( ! [X0,X1] :
        ( k10_tmap_1(sK3,X1,sK5,sK6,k2_tmap_1(sK3,X1,X0,sK5),k2_tmap_1(sK3,X1,X0,sK6)) = X0
        | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1))
        | ~ v1_funct_1(X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
        | ~ sP2(X1,sK6,sK5,sK3,k2_tmap_1(sK3,X1,X0,sK6),k2_tmap_1(sK3,X1,X0,sK5)) )
    | ~ spl8_3 ),
    inference(duplicate_literal_removal,[],[f293])).

fof(f293,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
        | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1))
        | ~ v1_funct_1(X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | k10_tmap_1(sK3,X1,sK5,sK6,k2_tmap_1(sK3,X1,X0,sK5),k2_tmap_1(sK3,X1,X0,sK6)) = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
        | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1))
        | ~ v1_funct_1(X0)
        | ~ sP2(X1,sK6,sK5,sK3,k2_tmap_1(sK3,X1,X0,sK6),k2_tmap_1(sK3,X1,X0,sK5)) )
    | ~ spl8_3 ),
    inference(resolution,[],[f292,f183])).

fof(f183,plain,(
    ! [X14,X15,X13,X16] :
      ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(X13),X14,k10_tmap_1(sK3,X13,sK5,sK6,X15,X16))
      | k10_tmap_1(sK3,X13,sK5,sK6,X15,X16) = X14
      | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X13))))
      | ~ v1_funct_2(X14,u1_struct_0(sK3),u1_struct_0(X13))
      | ~ v1_funct_1(X14)
      | ~ sP2(X13,sK6,sK5,sK3,X16,X15) ) ),
    inference(subsumption_resolution,[],[f182,f89])).

fof(f89,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k10_tmap_1(X3,X0,X2,X1,X5,X4))
      | ~ sP2(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k10_tmap_1(X3,X0,X2,X1,X5,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
        & v1_funct_2(k10_tmap_1(X3,X0,X2,X1,X5,X4),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
        & v1_funct_1(k10_tmap_1(X3,X0,X2,X1,X5,X4)) )
      | ~ sP2(X0,X1,X2,X3,X4,X5) ) ),
    inference(rectify,[],[f54])).

fof(f54,plain,(
    ! [X1,X3,X2,X0,X5,X4] :
      ( ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
      | ~ sP2(X1,X3,X2,X0,X5,X4) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f182,plain,(
    ! [X14,X15,X13,X16] :
      ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(X13),X14,k10_tmap_1(sK3,X13,sK5,sK6,X15,X16))
      | k10_tmap_1(sK3,X13,sK5,sK6,X15,X16) = X14
      | ~ v1_funct_1(k10_tmap_1(sK3,X13,sK5,sK6,X15,X16))
      | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X13))))
      | ~ v1_funct_2(X14,u1_struct_0(sK3),u1_struct_0(X13))
      | ~ v1_funct_1(X14)
      | ~ sP2(X13,sK6,sK5,sK3,X16,X15) ) ),
    inference(subsumption_resolution,[],[f175,f136])).

fof(f136,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k10_tmap_1(sK3,X0,sK5,sK6,X1,X2),u1_struct_0(sK3),u1_struct_0(X0))
      | ~ sP2(X0,sK6,sK5,sK3,X2,X1) ) ),
    inference(superposition,[],[f90,f66])).

fof(f66,plain,(
    sK3 = k1_tsep_1(sK3,sK5,sK6) ),
    inference(cnf_transformation,[],[f47])).

fof(f90,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_2(k10_tmap_1(X3,X0,X2,X1,X5,X4),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
      | ~ sP2(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f175,plain,(
    ! [X14,X15,X13,X16] :
      ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(X13),X14,k10_tmap_1(sK3,X13,sK5,sK6,X15,X16))
      | k10_tmap_1(sK3,X13,sK5,sK6,X15,X16) = X14
      | ~ v1_funct_2(k10_tmap_1(sK3,X13,sK5,sK6,X15,X16),u1_struct_0(sK3),u1_struct_0(X13))
      | ~ v1_funct_1(k10_tmap_1(sK3,X13,sK5,sK6,X15,X16))
      | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X13))))
      | ~ v1_funct_2(X14,u1_struct_0(sK3),u1_struct_0(X13))
      | ~ v1_funct_1(X14)
      | ~ sP2(X13,sK6,sK5,sK3,X16,X15) ) ),
    inference(resolution,[],[f85,f138])).

fof(f138,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k10_tmap_1(sK3,X0,sK5,sK6,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
      | ~ sP2(X0,sK6,sK5,sK3,X2,X1) ) ),
    inference(superposition,[],[f91,f66])).

fof(f91,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k10_tmap_1(X3,X0,X2,X1,X5,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
      | ~ sP2(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_funct_2(X0,X1,X2,X3)
      | X2 = X3
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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

fof(f292,plain,
    ( ! [X0,X1] :
        ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0),X1,k10_tmap_1(sK3,X0,sK5,sK6,k2_tmap_1(sK3,X0,X1,sK5),k2_tmap_1(sK3,X0,X1,sK6)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f291,f56])).

fof(f291,plain,
    ( ! [X0,X1] :
        ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0),X1,k10_tmap_1(sK3,X0,sK5,sK6,k2_tmap_1(sK3,X0,X1,sK5),k2_tmap_1(sK3,X0,X1,sK6)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | v2_struct_0(sK3) )
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f290,f57])).

fof(f290,plain,
    ( ! [X0,X1] :
        ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0),X1,k10_tmap_1(sK3,X0,sK5,sK6,k2_tmap_1(sK3,X0,X1,sK5),k2_tmap_1(sK3,X0,X1,sK6)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3) )
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f289,f58])).

fof(f289,plain,
    ( ! [X0,X1] :
        ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0),X1,k10_tmap_1(sK3,X0,sK5,sK6,k2_tmap_1(sK3,X0,X1,sK5),k2_tmap_1(sK3,X0,X1,sK6)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3) )
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f288,f133])).

fof(f133,plain,
    ( m1_pre_topc(sK3,sK3)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f131])).

fof(f288,plain,
    ( ! [X0,X1] :
        ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0),X1,k10_tmap_1(sK3,X0,sK5,sK6,k2_tmap_1(sK3,X0,X1,sK5),k2_tmap_1(sK3,X0,X1,sK6)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK3,sK3)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3) )
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f286,f65])).

fof(f286,plain,
    ( ! [X0,X1] :
        ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0),X1,k10_tmap_1(sK3,X0,sK5,sK6,k2_tmap_1(sK3,X0,X1,sK5),k2_tmap_1(sK3,X0,X1,sK6)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK6,sK3)
        | ~ m1_pre_topc(sK3,sK3)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3) )
    | ~ spl8_3 ),
    inference(duplicate_literal_removal,[],[f285])).

fof(f285,plain,
    ( ! [X0,X1] :
        ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0),X1,k10_tmap_1(sK3,X0,sK5,sK6,k2_tmap_1(sK3,X0,X1,sK5),k2_tmap_1(sK3,X0,X1,sK6)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK6,sK3)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ m1_pre_topc(sK6,sK3)
        | ~ m1_pre_topc(sK3,sK3)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3) )
    | ~ spl8_3 ),
    inference(superposition,[],[f278,f211])).

fof(f211,plain,(
    ! [X6,X10,X8,X7,X9] :
      ( k2_tmap_1(X6,X7,X8,X9) = k3_tmap_1(X10,X7,X6,X9,X8)
      | ~ m1_pre_topc(X9,X6)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(X7))))
      | ~ v1_funct_2(X8,u1_struct_0(X6),u1_struct_0(X7))
      | ~ v1_funct_1(X8)
      | ~ m1_pre_topc(X9,X10)
      | ~ m1_pre_topc(X6,X10)
      | ~ l1_pre_topc(X7)
      | ~ v2_pre_topc(X7)
      | v2_struct_0(X7)
      | ~ l1_pre_topc(X10)
      | ~ v2_pre_topc(X10)
      | v2_struct_0(X10)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6) ) ),
    inference(subsumption_resolution,[],[f209,f72])).

fof(f209,plain,(
    ! [X6,X10,X8,X7,X9] :
      ( k2_tmap_1(X6,X7,X8,X9) = k3_tmap_1(X10,X7,X6,X9,X8)
      | ~ m1_pre_topc(X9,X6)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(X7))))
      | ~ v1_funct_2(X8,u1_struct_0(X6),u1_struct_0(X7))
      | ~ v1_funct_1(X8)
      | ~ m1_pre_topc(X9,X10)
      | ~ m1_pre_topc(X6,X10)
      | ~ l1_pre_topc(X7)
      | ~ v2_pre_topc(X7)
      | v2_struct_0(X7)
      | ~ l1_pre_topc(X10)
      | ~ v2_pre_topc(X10)
      | v2_struct_0(X10)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6) ) ),
    inference(duplicate_literal_removal,[],[f206])).

fof(f206,plain,(
    ! [X6,X10,X8,X7,X9] :
      ( k2_tmap_1(X6,X7,X8,X9) = k3_tmap_1(X10,X7,X6,X9,X8)
      | ~ m1_pre_topc(X9,X6)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(X7))))
      | ~ v1_funct_2(X8,u1_struct_0(X6),u1_struct_0(X7))
      | ~ v1_funct_1(X8)
      | ~ m1_pre_topc(X9,X10)
      | ~ m1_pre_topc(X6,X10)
      | ~ l1_pre_topc(X7)
      | ~ v2_pre_topc(X7)
      | v2_struct_0(X7)
      | ~ l1_pre_topc(X10)
      | ~ v2_pre_topc(X10)
      | v2_struct_0(X10)
      | ~ m1_pre_topc(X9,X6)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(X7))))
      | ~ v1_funct_2(X8,u1_struct_0(X6),u1_struct_0(X7))
      | ~ v1_funct_1(X8)
      | ~ l1_pre_topc(X7)
      | ~ v2_pre_topc(X7)
      | v2_struct_0(X7)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6) ) ),
    inference(superposition,[],[f74,f76])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f74,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
      | ~ m1_pre_topc(X3,X2)
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
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f278,plain,
    ( ! [X0,X1] :
        ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0),X1,k10_tmap_1(sK3,X0,sK5,sK6,k2_tmap_1(sK3,X0,X1,sK5),k3_tmap_1(sK3,X0,sK3,sK6,X1)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f277,f56])).

fof(f277,plain,
    ( ! [X0,X1] :
        ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0),X1,k10_tmap_1(sK3,X0,sK5,sK6,k2_tmap_1(sK3,X0,X1,sK5),k3_tmap_1(sK3,X0,sK3,sK6,X1)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | v2_struct_0(sK3) )
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f276,f57])).

fof(f276,plain,
    ( ! [X0,X1] :
        ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0),X1,k10_tmap_1(sK3,X0,sK5,sK6,k2_tmap_1(sK3,X0,X1,sK5),k3_tmap_1(sK3,X0,sK3,sK6,X1)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3) )
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f275,f58])).

fof(f275,plain,
    ( ! [X0,X1] :
        ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0),X1,k10_tmap_1(sK3,X0,sK5,sK6,k2_tmap_1(sK3,X0,X1,sK5),k3_tmap_1(sK3,X0,sK3,sK6,X1)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3) )
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f274,f133])).

fof(f274,plain,(
    ! [X0,X1] :
      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0),X1,k10_tmap_1(sK3,X0,sK5,sK6,k2_tmap_1(sK3,X0,X1,sK5),k3_tmap_1(sK3,X0,sK3,sK6,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(sK3,sK3)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f272,f63])).

fof(f272,plain,(
    ! [X0,X1] :
      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0),X1,k10_tmap_1(sK3,X0,sK5,sK6,k2_tmap_1(sK3,X0,X1,sK5),k3_tmap_1(sK3,X0,sK3,sK6,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(sK5,sK3)
      | ~ m1_pre_topc(sK3,sK3)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(duplicate_literal_removal,[],[f269])).

fof(f269,plain,(
    ! [X0,X1] :
      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0),X1,k10_tmap_1(sK3,X0,sK5,sK6,k2_tmap_1(sK3,X0,X1,sK5),k3_tmap_1(sK3,X0,sK3,sK6,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(sK5,sK3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ m1_pre_topc(sK5,sK3)
      | ~ m1_pre_topc(sK3,sK3)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(superposition,[],[f267,f211])).

fof(f267,plain,(
    ! [X0,X1] :
      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0),X1,k10_tmap_1(sK3,X0,sK5,sK6,k3_tmap_1(sK3,X0,sK3,sK5,X1),k3_tmap_1(sK3,X0,sK3,sK6,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f266,f56])).

fof(f266,plain,(
    ! [X0,X1] :
      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0),X1,k10_tmap_1(sK3,X0,sK5,sK6,k3_tmap_1(sK3,X0,sK3,sK5,X1),k3_tmap_1(sK3,X0,sK3,sK6,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f265,f57])).

fof(f265,plain,(
    ! [X0,X1] :
      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0),X1,k10_tmap_1(sK3,X0,sK5,sK6,k3_tmap_1(sK3,X0,sK3,sK5,X1),k3_tmap_1(sK3,X0,sK3,sK6,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f264,f58])).

fof(f264,plain,(
    ! [X0,X1] :
      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0),X1,k10_tmap_1(sK3,X0,sK5,sK6,k3_tmap_1(sK3,X0,sK3,sK5,X1),k3_tmap_1(sK3,X0,sK3,sK6,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f263,f62])).

fof(f263,plain,(
    ! [X0,X1] :
      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0),X1,k10_tmap_1(sK3,X0,sK5,sK6,k3_tmap_1(sK3,X0,sK3,sK5,X1),k3_tmap_1(sK3,X0,sK3,sK6,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | v2_struct_0(sK5)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f262,f63])).

fof(f262,plain,(
    ! [X0,X1] :
      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0),X1,k10_tmap_1(sK3,X0,sK5,sK6,k3_tmap_1(sK3,X0,sK3,sK5,X1),k3_tmap_1(sK3,X0,sK3,sK6,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ m1_pre_topc(sK5,sK3)
      | v2_struct_0(sK5)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f261,f64])).

fof(f261,plain,(
    ! [X0,X1] :
      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0),X1,k10_tmap_1(sK3,X0,sK5,sK6,k3_tmap_1(sK3,X0,sK3,sK5,X1),k3_tmap_1(sK3,X0,sK3,sK6,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | v2_struct_0(sK6)
      | ~ m1_pre_topc(sK5,sK3)
      | v2_struct_0(sK5)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f254,f65])).

fof(f254,plain,(
    ! [X0,X1] :
      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0),X1,k10_tmap_1(sK3,X0,sK5,sK6,k3_tmap_1(sK3,X0,sK3,sK5,X1),k3_tmap_1(sK3,X0,sK3,sK6,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ m1_pre_topc(sK6,sK3)
      | v2_struct_0(sK6)
      | ~ m1_pre_topc(sK5,sK3)
      | v2_struct_0(sK5)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(superposition,[],[f75,f66])).

fof(f75,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_funct_2(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r2_funct_2(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)))
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r2_funct_2(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)))
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => r2_funct_2(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_tmap_1)).

fof(f115,plain,(
    ~ r1_funct_2(u1_struct_0(sK3),u1_struct_0(sK4),u1_struct_0(sK3),u1_struct_0(sK4),sK7,k10_tmap_1(sK3,sK4,sK5,sK6,k2_tmap_1(sK3,sK4,sK7,sK5),k2_tmap_1(sK3,sK4,sK7,sK6))) ),
    inference(forward_demodulation,[],[f70,f66])).

fof(f70,plain,(
    ~ r1_funct_2(u1_struct_0(sK3),u1_struct_0(sK4),u1_struct_0(k1_tsep_1(sK3,sK5,sK6)),u1_struct_0(sK4),sK7,k10_tmap_1(sK3,sK4,sK5,sK6,k2_tmap_1(sK3,sK4,sK7,sK5),k2_tmap_1(sK3,sK4,sK7,sK6))) ),
    inference(cnf_transformation,[],[f47])).

fof(f189,plain,(
    spl8_5 ),
    inference(avatar_contradiction_clause,[],[f188])).

fof(f188,plain,
    ( $false
    | spl8_5 ),
    inference(subsumption_resolution,[],[f187,f61])).

fof(f187,plain,
    ( ~ l1_pre_topc(sK4)
    | spl8_5 ),
    inference(resolution,[],[f157,f71])).

fof(f157,plain,
    ( ~ l1_struct_0(sK4)
    | spl8_5 ),
    inference(avatar_component_clause,[],[f155])).

fof(f186,plain,(
    spl8_4 ),
    inference(avatar_contradiction_clause,[],[f185])).

fof(f185,plain,
    ( $false
    | spl8_4 ),
    inference(subsumption_resolution,[],[f184,f58])).

fof(f184,plain,
    ( ~ l1_pre_topc(sK3)
    | spl8_4 ),
    inference(resolution,[],[f153,f71])).

fof(f153,plain,
    ( ~ l1_struct_0(sK3)
    | spl8_4 ),
    inference(avatar_component_clause,[],[f151])).

fof(f151,plain,
    ( spl8_4
  <=> l1_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f161,plain,
    ( ~ spl8_4
    | ~ spl8_5
    | spl8_6 ),
    inference(avatar_split_clause,[],[f149,f159,f155,f151])).

fof(f149,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | sP1(sK4,X0,sK7,sK3)
      | ~ l1_struct_0(sK4)
      | ~ l1_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f148,f67])).

fof(f148,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | sP1(sK4,X0,sK7,sK3)
      | ~ v1_funct_1(sK7)
      | ~ l1_struct_0(sK4)
      | ~ l1_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f144,f68])).

fof(f144,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | sP1(sK4,X0,sK7,sK3)
      | ~ v1_funct_2(sK7,u1_struct_0(sK3),u1_struct_0(sK4))
      | ~ v1_funct_1(sK7)
      | ~ l1_struct_0(sK4)
      | ~ l1_struct_0(sK3) ) ),
    inference(resolution,[],[f84,f69])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | sP1(X1,X3,X2,X0)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( sP1(X1,X3,X2,X0)
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(definition_folding,[],[f29,f38])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( l1_struct_0(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(X2)
        & l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tmap_1)).

fof(f134,plain,
    ( ~ spl8_1
    | spl8_3 ),
    inference(avatar_split_clause,[],[f113,f131,f104])).

fof(f104,plain,
    ( spl8_1
  <=> sP0(sK3,sK6,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f113,plain,
    ( m1_pre_topc(sK3,sK3)
    | ~ sP0(sK3,sK6,sK5) ),
    inference(superposition,[],[f79,f66])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X2,X1),X0)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X2,X1),X0)
        & v1_pre_topc(k1_tsep_1(X0,X2,X1))
        & ~ v2_struct_0(k1_tsep_1(X0,X2,X1)) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f48])).

fof(f48,plain,(
    ! [X0,X2,X1] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ sP0(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X2,X1] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ sP0(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f129,plain,(
    spl8_1 ),
    inference(avatar_contradiction_clause,[],[f128])).

fof(f128,plain,
    ( $false
    | spl8_1 ),
    inference(subsumption_resolution,[],[f127,f56])).

fof(f127,plain,
    ( v2_struct_0(sK3)
    | spl8_1 ),
    inference(subsumption_resolution,[],[f126,f58])).

fof(f126,plain,
    ( ~ l1_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl8_1 ),
    inference(subsumption_resolution,[],[f125,f62])).

fof(f125,plain,
    ( v2_struct_0(sK5)
    | ~ l1_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl8_1 ),
    inference(subsumption_resolution,[],[f124,f63])).

fof(f124,plain,
    ( ~ m1_pre_topc(sK5,sK3)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl8_1 ),
    inference(subsumption_resolution,[],[f123,f64])).

fof(f123,plain,
    ( v2_struct_0(sK6)
    | ~ m1_pre_topc(sK5,sK3)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl8_1 ),
    inference(subsumption_resolution,[],[f122,f65])).

fof(f122,plain,
    ( ~ m1_pre_topc(sK6,sK3)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(sK5,sK3)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl8_1 ),
    inference(resolution,[],[f80,f106])).

fof(f106,plain,
    ( ~ sP0(sK3,sK6,sK5)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f104])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( sP0(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f27,f36])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tsep_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:52:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (17368)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.50  % (17377)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.51  % (17367)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.51  % (17369)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.51  % (17365)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (17370)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.51  % (17388)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.51  % (17386)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.51  % (17380)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.51  % (17382)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.51  % (17364)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.51  % (17378)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (17379)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.51  % (17385)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.52  % (17371)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.52  % (17383)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.52  % (17389)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.52  % (17384)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.52  % (17376)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.53  % (17372)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.54  % (17366)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.54  % (17387)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.54  % (17381)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.40/0.54  % (17370)Refutation not found, incomplete strategy% (17370)------------------------------
% 1.40/0.54  % (17370)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.54  % (17370)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.54  
% 1.40/0.54  % (17370)Memory used [KB]: 11001
% 1.40/0.54  % (17370)Time elapsed: 0.136 s
% 1.40/0.54  % (17370)------------------------------
% 1.40/0.54  % (17370)------------------------------
% 1.40/0.55  % (17390)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.53/0.56  % (17374)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.53/0.56  % (17375)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.53/0.57  % (17368)Refutation found. Thanks to Tanya!
% 1.53/0.57  % SZS status Theorem for theBenchmark
% 1.53/0.57  % SZS output start Proof for theBenchmark
% 1.53/0.57  fof(f659,plain,(
% 1.53/0.57    $false),
% 1.53/0.57    inference(avatar_sat_refutation,[],[f129,f134,f161,f186,f189,f344,f462,f483,f488,f633,f649,f658])).
% 1.53/0.57  fof(f658,plain,(
% 1.53/0.57    ~spl8_5 | spl8_9),
% 1.53/0.57    inference(avatar_contradiction_clause,[],[f657])).
% 1.53/0.57  fof(f657,plain,(
% 1.53/0.57    $false | (~spl8_5 | spl8_9)),
% 1.53/0.57    inference(subsumption_resolution,[],[f656,f59])).
% 1.53/0.57  fof(f59,plain,(
% 1.53/0.57    ~v2_struct_0(sK4)),
% 1.53/0.57    inference(cnf_transformation,[],[f47])).
% 1.53/0.57  fof(f47,plain,(
% 1.53/0.57    ((((~r1_funct_2(u1_struct_0(sK3),u1_struct_0(sK4),u1_struct_0(k1_tsep_1(sK3,sK5,sK6)),u1_struct_0(sK4),sK7,k10_tmap_1(sK3,sK4,sK5,sK6,k2_tmap_1(sK3,sK4,sK7,sK5),k2_tmap_1(sK3,sK4,sK7,sK6))) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) & v1_funct_2(sK7,u1_struct_0(sK3),u1_struct_0(sK4)) & v1_funct_1(sK7)) & sK3 = k1_tsep_1(sK3,sK5,sK6) & m1_pre_topc(sK6,sK3) & ~v2_struct_0(sK6)) & m1_pre_topc(sK5,sK3) & ~v2_struct_0(sK5)) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 1.53/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f15,f46,f45,f44,f43,f42])).
% 1.53/0.57  fof(f42,plain,(
% 1.53/0.57    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & k1_tsep_1(X0,X2,X3) = X0 & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r1_funct_2(u1_struct_0(sK3),u1_struct_0(X1),u1_struct_0(k1_tsep_1(sK3,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(sK3,X1,X2,X3,k2_tmap_1(sK3,X1,X4,X2),k2_tmap_1(sK3,X1,X4,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X1)) & v1_funct_1(X4)) & sK3 = k1_tsep_1(sK3,X2,X3) & m1_pre_topc(X3,sK3) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK3) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 1.53/0.57    introduced(choice_axiom,[])).
% 1.53/0.57  fof(f43,plain,(
% 1.53/0.57    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r1_funct_2(u1_struct_0(sK3),u1_struct_0(X1),u1_struct_0(k1_tsep_1(sK3,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(sK3,X1,X2,X3,k2_tmap_1(sK3,X1,X4,X2),k2_tmap_1(sK3,X1,X4,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X1)) & v1_funct_1(X4)) & sK3 = k1_tsep_1(sK3,X2,X3) & m1_pre_topc(X3,sK3) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK3) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (~r1_funct_2(u1_struct_0(sK3),u1_struct_0(sK4),u1_struct_0(k1_tsep_1(sK3,X2,X3)),u1_struct_0(sK4),X4,k10_tmap_1(sK3,sK4,X2,X3,k2_tmap_1(sK3,sK4,X4,X2),k2_tmap_1(sK3,sK4,X4,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK4)) & v1_funct_1(X4)) & sK3 = k1_tsep_1(sK3,X2,X3) & m1_pre_topc(X3,sK3) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK3) & ~v2_struct_0(X2)) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4))),
% 1.53/0.57    introduced(choice_axiom,[])).
% 1.53/0.57  fof(f44,plain,(
% 1.53/0.57    ? [X2] : (? [X3] : (? [X4] : (~r1_funct_2(u1_struct_0(sK3),u1_struct_0(sK4),u1_struct_0(k1_tsep_1(sK3,X2,X3)),u1_struct_0(sK4),X4,k10_tmap_1(sK3,sK4,X2,X3,k2_tmap_1(sK3,sK4,X4,X2),k2_tmap_1(sK3,sK4,X4,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK4)) & v1_funct_1(X4)) & sK3 = k1_tsep_1(sK3,X2,X3) & m1_pre_topc(X3,sK3) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK3) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (~r1_funct_2(u1_struct_0(sK3),u1_struct_0(sK4),u1_struct_0(k1_tsep_1(sK3,sK5,X3)),u1_struct_0(sK4),X4,k10_tmap_1(sK3,sK4,sK5,X3,k2_tmap_1(sK3,sK4,X4,sK5),k2_tmap_1(sK3,sK4,X4,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK4)) & v1_funct_1(X4)) & sK3 = k1_tsep_1(sK3,sK5,X3) & m1_pre_topc(X3,sK3) & ~v2_struct_0(X3)) & m1_pre_topc(sK5,sK3) & ~v2_struct_0(sK5))),
% 1.53/0.57    introduced(choice_axiom,[])).
% 1.53/0.57  fof(f45,plain,(
% 1.53/0.57    ? [X3] : (? [X4] : (~r1_funct_2(u1_struct_0(sK3),u1_struct_0(sK4),u1_struct_0(k1_tsep_1(sK3,sK5,X3)),u1_struct_0(sK4),X4,k10_tmap_1(sK3,sK4,sK5,X3,k2_tmap_1(sK3,sK4,X4,sK5),k2_tmap_1(sK3,sK4,X4,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK4)) & v1_funct_1(X4)) & sK3 = k1_tsep_1(sK3,sK5,X3) & m1_pre_topc(X3,sK3) & ~v2_struct_0(X3)) => (? [X4] : (~r1_funct_2(u1_struct_0(sK3),u1_struct_0(sK4),u1_struct_0(k1_tsep_1(sK3,sK5,sK6)),u1_struct_0(sK4),X4,k10_tmap_1(sK3,sK4,sK5,sK6,k2_tmap_1(sK3,sK4,X4,sK5),k2_tmap_1(sK3,sK4,X4,sK6))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK4)) & v1_funct_1(X4)) & sK3 = k1_tsep_1(sK3,sK5,sK6) & m1_pre_topc(sK6,sK3) & ~v2_struct_0(sK6))),
% 1.53/0.57    introduced(choice_axiom,[])).
% 1.53/0.57  fof(f46,plain,(
% 1.53/0.57    ? [X4] : (~r1_funct_2(u1_struct_0(sK3),u1_struct_0(sK4),u1_struct_0(k1_tsep_1(sK3,sK5,sK6)),u1_struct_0(sK4),X4,k10_tmap_1(sK3,sK4,sK5,sK6,k2_tmap_1(sK3,sK4,X4,sK5),k2_tmap_1(sK3,sK4,X4,sK6))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK4)) & v1_funct_1(X4)) => (~r1_funct_2(u1_struct_0(sK3),u1_struct_0(sK4),u1_struct_0(k1_tsep_1(sK3,sK5,sK6)),u1_struct_0(sK4),sK7,k10_tmap_1(sK3,sK4,sK5,sK6,k2_tmap_1(sK3,sK4,sK7,sK5),k2_tmap_1(sK3,sK4,sK7,sK6))) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) & v1_funct_2(sK7,u1_struct_0(sK3),u1_struct_0(sK4)) & v1_funct_1(sK7))),
% 1.53/0.57    introduced(choice_axiom,[])).
% 1.53/0.57  fof(f15,plain,(
% 1.53/0.57    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & k1_tsep_1(X0,X2,X3) = X0 & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.53/0.57    inference(flattening,[],[f14])).
% 1.53/0.57  fof(f14,plain,(
% 1.53/0.57    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4))) & k1_tsep_1(X0,X2,X3) = X0) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.53/0.57    inference(ennf_transformation,[],[f13])).
% 1.53/0.57  fof(f13,negated_conjecture,(
% 1.53/0.57    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (k1_tsep_1(X0,X2,X3) = X0 => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3)))))))))),
% 1.53/0.57    inference(negated_conjecture,[],[f12])).
% 1.53/0.57  fof(f12,conjecture,(
% 1.53/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (k1_tsep_1(X0,X2,X3) = X0 => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3)))))))))),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_tmap_1)).
% 1.53/0.57  fof(f656,plain,(
% 1.53/0.57    v2_struct_0(sK4) | (~spl8_5 | spl8_9)),
% 1.53/0.57    inference(subsumption_resolution,[],[f655,f156])).
% 1.53/0.57  fof(f156,plain,(
% 1.53/0.57    l1_struct_0(sK4) | ~spl8_5),
% 1.53/0.57    inference(avatar_component_clause,[],[f155])).
% 1.53/0.57  fof(f155,plain,(
% 1.53/0.57    spl8_5 <=> l1_struct_0(sK4)),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 1.53/0.57  fof(f655,plain,(
% 1.53/0.57    ~l1_struct_0(sK4) | v2_struct_0(sK4) | spl8_9),
% 1.53/0.57    inference(resolution,[],[f654,f73])).
% 1.53/0.57  fof(f73,plain,(
% 1.53/0.57    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f19])).
% 1.53/0.57  fof(f19,plain,(
% 1.53/0.57    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.53/0.57    inference(flattening,[],[f18])).
% 1.53/0.57  fof(f18,plain,(
% 1.53/0.57    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.53/0.57    inference(ennf_transformation,[],[f4])).
% 1.53/0.57  fof(f4,axiom,(
% 1.53/0.57    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 1.53/0.57  fof(f654,plain,(
% 1.53/0.57    v1_xboole_0(u1_struct_0(sK4)) | spl8_9),
% 1.53/0.57    inference(subsumption_resolution,[],[f653,f67])).
% 1.53/0.57  fof(f67,plain,(
% 1.53/0.57    v1_funct_1(sK7)),
% 1.53/0.57    inference(cnf_transformation,[],[f47])).
% 1.53/0.57  fof(f653,plain,(
% 1.53/0.57    ~v1_funct_1(sK7) | v1_xboole_0(u1_struct_0(sK4)) | spl8_9),
% 1.53/0.57    inference(subsumption_resolution,[],[f652,f68])).
% 1.53/0.57  fof(f68,plain,(
% 1.53/0.57    v1_funct_2(sK7,u1_struct_0(sK3),u1_struct_0(sK4))),
% 1.53/0.57    inference(cnf_transformation,[],[f47])).
% 1.53/0.57  fof(f652,plain,(
% 1.53/0.57    ~v1_funct_2(sK7,u1_struct_0(sK3),u1_struct_0(sK4)) | ~v1_funct_1(sK7) | v1_xboole_0(u1_struct_0(sK4)) | spl8_9),
% 1.53/0.57    inference(subsumption_resolution,[],[f651,f69])).
% 1.53/0.57  fof(f69,plain,(
% 1.53/0.57    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))),
% 1.53/0.57    inference(cnf_transformation,[],[f47])).
% 1.53/0.57  fof(f651,plain,(
% 1.53/0.57    ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) | ~v1_funct_2(sK7,u1_struct_0(sK3),u1_struct_0(sK4)) | ~v1_funct_1(sK7) | v1_xboole_0(u1_struct_0(sK4)) | spl8_9),
% 1.53/0.57    inference(duplicate_literal_removal,[],[f650])).
% 1.53/0.57  fof(f650,plain,(
% 1.53/0.57    ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) | ~v1_funct_2(sK7,u1_struct_0(sK3),u1_struct_0(sK4)) | ~v1_funct_1(sK7) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) | ~v1_funct_2(sK7,u1_struct_0(sK3),u1_struct_0(sK4)) | v1_xboole_0(u1_struct_0(sK4)) | v1_xboole_0(u1_struct_0(sK4)) | spl8_9),
% 1.53/0.57    inference(resolution,[],[f343,f95])).
% 1.53/0.57  fof(f95,plain,(
% 1.53/0.57    ( ! [X2,X0,X5,X3,X1] : (r1_funct_2(X0,X1,X2,X3,X5,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X5,X0,X1) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 1.53/0.57    inference(duplicate_literal_removal,[],[f94])).
% 1.53/0.57  fof(f94,plain,(
% 1.53/0.57    ( ! [X2,X0,X5,X3,X1] : (r1_funct_2(X0,X1,X2,X3,X5,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X5,X0,X1) | ~v1_funct_1(X5) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 1.53/0.57    inference(equality_resolution,[],[f88])).
% 1.53/0.57  fof(f88,plain,(
% 1.53/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f53])).
% 1.53/0.57  fof(f53,plain,(
% 1.53/0.57    ! [X0,X1,X2,X3,X4,X5] : (((r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 != X5) & (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 1.53/0.57    inference(nnf_transformation,[],[f33])).
% 1.53/0.57  fof(f33,plain,(
% 1.53/0.57    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 1.53/0.57    inference(flattening,[],[f32])).
% 1.53/0.57  fof(f32,plain,(
% 1.53/0.57    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 1.53/0.57    inference(ennf_transformation,[],[f5])).
% 1.53/0.57  fof(f5,axiom,(
% 1.53/0.57    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => (r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5))),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_funct_2)).
% 1.53/0.57  fof(f343,plain,(
% 1.53/0.57    ~r1_funct_2(u1_struct_0(sK3),u1_struct_0(sK4),u1_struct_0(sK3),u1_struct_0(sK4),sK7,sK7) | spl8_9),
% 1.53/0.57    inference(avatar_component_clause,[],[f341])).
% 1.53/0.57  fof(f341,plain,(
% 1.53/0.57    spl8_9 <=> r1_funct_2(u1_struct_0(sK3),u1_struct_0(sK4),u1_struct_0(sK3),u1_struct_0(sK4),sK7,sK7)),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 1.53/0.57  fof(f649,plain,(
% 1.53/0.57    ~spl8_6 | spl8_13),
% 1.53/0.57    inference(avatar_contradiction_clause,[],[f648])).
% 1.53/0.57  fof(f648,plain,(
% 1.53/0.57    $false | (~spl8_6 | spl8_13)),
% 1.53/0.57    inference(subsumption_resolution,[],[f647,f99])).
% 1.53/0.57  fof(f99,plain,(
% 1.53/0.57    l1_pre_topc(sK5)),
% 1.53/0.57    inference(subsumption_resolution,[],[f97,f58])).
% 1.53/0.57  fof(f58,plain,(
% 1.53/0.57    l1_pre_topc(sK3)),
% 1.53/0.57    inference(cnf_transformation,[],[f47])).
% 1.53/0.57  fof(f97,plain,(
% 1.53/0.57    l1_pre_topc(sK5) | ~l1_pre_topc(sK3)),
% 1.53/0.57    inference(resolution,[],[f72,f63])).
% 1.53/0.57  fof(f63,plain,(
% 1.53/0.57    m1_pre_topc(sK5,sK3)),
% 1.53/0.57    inference(cnf_transformation,[],[f47])).
% 1.53/0.57  fof(f72,plain,(
% 1.53/0.57    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f17])).
% 1.53/0.57  fof(f17,plain,(
% 1.53/0.57    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.53/0.57    inference(ennf_transformation,[],[f3])).
% 1.53/0.57  fof(f3,axiom,(
% 1.53/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.53/0.57  fof(f647,plain,(
% 1.53/0.57    ~l1_pre_topc(sK5) | (~spl8_6 | spl8_13)),
% 1.53/0.57    inference(resolution,[],[f646,f71])).
% 1.53/0.57  fof(f71,plain,(
% 1.53/0.57    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f16])).
% 1.53/0.57  fof(f16,plain,(
% 1.53/0.57    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.53/0.57    inference(ennf_transformation,[],[f2])).
% 1.53/0.57  fof(f2,axiom,(
% 1.53/0.57    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.53/0.57  fof(f646,plain,(
% 1.53/0.57    ~l1_struct_0(sK5) | (~spl8_6 | spl8_13)),
% 1.53/0.57    inference(resolution,[],[f634,f160])).
% 1.53/0.57  fof(f160,plain,(
% 1.53/0.57    ( ! [X0] : (sP1(sK4,X0,sK7,sK3) | ~l1_struct_0(X0)) ) | ~spl8_6),
% 1.53/0.57    inference(avatar_component_clause,[],[f159])).
% 1.53/0.57  fof(f159,plain,(
% 1.53/0.57    spl8_6 <=> ! [X0] : (~l1_struct_0(X0) | sP1(sK4,X0,sK7,sK3))),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 1.53/0.57  fof(f634,plain,(
% 1.53/0.57    ~sP1(sK4,sK5,sK7,sK3) | spl8_13),
% 1.53/0.57    inference(resolution,[],[f461,f83])).
% 1.53/0.57  fof(f83,plain,(
% 1.53/0.57    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~sP1(X0,X1,X2,X3)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f51])).
% 1.53/0.57  fof(f51,plain,(
% 1.53/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k2_tmap_1(X3,X0,X2,X1))) | ~sP1(X0,X1,X2,X3))),
% 1.53/0.57    inference(rectify,[],[f50])).
% 1.53/0.57  fof(f50,plain,(
% 1.53/0.57    ! [X1,X3,X2,X0] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | ~sP1(X1,X3,X2,X0))),
% 1.53/0.57    inference(nnf_transformation,[],[f38])).
% 1.53/0.57  fof(f38,plain,(
% 1.53/0.57    ! [X1,X3,X2,X0] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | ~sP1(X1,X3,X2,X0))),
% 1.53/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.53/0.57  fof(f461,plain,(
% 1.53/0.57    ~m1_subset_1(k2_tmap_1(sK3,sK4,sK7,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4)))) | spl8_13),
% 1.53/0.57    inference(avatar_component_clause,[],[f459])).
% 1.53/0.57  fof(f459,plain,(
% 1.53/0.57    spl8_13 <=> m1_subset_1(k2_tmap_1(sK3,sK4,sK7,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 1.53/0.57  fof(f633,plain,(
% 1.53/0.57    ~spl8_6 | spl8_12),
% 1.53/0.57    inference(avatar_contradiction_clause,[],[f632])).
% 1.53/0.57  fof(f632,plain,(
% 1.53/0.57    $false | (~spl8_6 | spl8_12)),
% 1.53/0.57    inference(subsumption_resolution,[],[f631,f99])).
% 1.53/0.57  fof(f631,plain,(
% 1.53/0.57    ~l1_pre_topc(sK5) | (~spl8_6 | spl8_12)),
% 1.53/0.57    inference(resolution,[],[f630,f71])).
% 1.53/0.57  fof(f630,plain,(
% 1.53/0.57    ~l1_struct_0(sK5) | (~spl8_6 | spl8_12)),
% 1.53/0.57    inference(resolution,[],[f629,f160])).
% 1.53/0.57  fof(f629,plain,(
% 1.53/0.57    ~sP1(sK4,sK5,sK7,sK3) | spl8_12),
% 1.53/0.57    inference(resolution,[],[f457,f82])).
% 1.53/0.57  fof(f82,plain,(
% 1.53/0.57    ( ! [X2,X0,X3,X1] : (v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0)) | ~sP1(X0,X1,X2,X3)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f51])).
% 1.53/0.57  fof(f457,plain,(
% 1.53/0.57    ~v1_funct_2(k2_tmap_1(sK3,sK4,sK7,sK5),u1_struct_0(sK5),u1_struct_0(sK4)) | spl8_12),
% 1.53/0.57    inference(avatar_component_clause,[],[f455])).
% 1.53/0.57  fof(f455,plain,(
% 1.53/0.57    spl8_12 <=> v1_funct_2(k2_tmap_1(sK3,sK4,sK7,sK5),u1_struct_0(sK5),u1_struct_0(sK4))),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 1.53/0.57  fof(f488,plain,(
% 1.53/0.57    ~spl8_6 | spl8_11),
% 1.53/0.57    inference(avatar_contradiction_clause,[],[f487])).
% 1.53/0.57  fof(f487,plain,(
% 1.53/0.57    $false | (~spl8_6 | spl8_11)),
% 1.53/0.57    inference(subsumption_resolution,[],[f486,f99])).
% 1.53/0.57  fof(f486,plain,(
% 1.53/0.57    ~l1_pre_topc(sK5) | (~spl8_6 | spl8_11)),
% 1.53/0.57    inference(resolution,[],[f485,f71])).
% 1.53/0.57  fof(f485,plain,(
% 1.53/0.57    ~l1_struct_0(sK5) | (~spl8_6 | spl8_11)),
% 1.53/0.57    inference(resolution,[],[f484,f160])).
% 1.53/0.57  fof(f484,plain,(
% 1.53/0.57    ~sP1(sK4,sK5,sK7,sK3) | spl8_11),
% 1.53/0.57    inference(resolution,[],[f453,f81])).
% 1.53/0.58  fof(f81,plain,(
% 1.53/0.58    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_tmap_1(X3,X0,X2,X1)) | ~sP1(X0,X1,X2,X3)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f51])).
% 1.53/0.58  fof(f453,plain,(
% 1.53/0.58    ~v1_funct_1(k2_tmap_1(sK3,sK4,sK7,sK5)) | spl8_11),
% 1.53/0.58    inference(avatar_component_clause,[],[f451])).
% 1.53/0.58  fof(f451,plain,(
% 1.53/0.58    spl8_11 <=> v1_funct_1(k2_tmap_1(sK3,sK4,sK7,sK5))),
% 1.53/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 1.53/0.58  fof(f483,plain,(
% 1.53/0.58    ~spl8_6 | spl8_10),
% 1.53/0.58    inference(avatar_contradiction_clause,[],[f482])).
% 1.53/0.58  fof(f482,plain,(
% 1.53/0.58    $false | (~spl8_6 | spl8_10)),
% 1.53/0.58    inference(subsumption_resolution,[],[f481,f100])).
% 1.53/0.58  fof(f100,plain,(
% 1.53/0.58    l1_pre_topc(sK6)),
% 1.53/0.58    inference(subsumption_resolution,[],[f98,f58])).
% 1.53/0.58  fof(f98,plain,(
% 1.53/0.58    l1_pre_topc(sK6) | ~l1_pre_topc(sK3)),
% 1.53/0.58    inference(resolution,[],[f72,f65])).
% 1.53/0.58  fof(f65,plain,(
% 1.53/0.58    m1_pre_topc(sK6,sK3)),
% 1.53/0.58    inference(cnf_transformation,[],[f47])).
% 1.53/0.58  fof(f481,plain,(
% 1.53/0.58    ~l1_pre_topc(sK6) | (~spl8_6 | spl8_10)),
% 1.53/0.58    inference(resolution,[],[f480,f71])).
% 1.53/0.58  fof(f480,plain,(
% 1.53/0.58    ~l1_struct_0(sK6) | (~spl8_6 | spl8_10)),
% 1.53/0.58    inference(resolution,[],[f449,f160])).
% 1.53/0.58  fof(f449,plain,(
% 1.53/0.58    ~sP1(sK4,sK6,sK7,sK3) | spl8_10),
% 1.53/0.58    inference(avatar_component_clause,[],[f447])).
% 1.53/0.58  fof(f447,plain,(
% 1.53/0.58    spl8_10 <=> sP1(sK4,sK6,sK7,sK3)),
% 1.53/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 1.53/0.58  fof(f462,plain,(
% 1.53/0.58    ~spl8_10 | ~spl8_11 | ~spl8_12 | ~spl8_13 | spl8_8),
% 1.53/0.58    inference(avatar_split_clause,[],[f445,f337,f459,f455,f451,f447])).
% 1.53/0.58  fof(f337,plain,(
% 1.53/0.58    spl8_8 <=> sP2(sK4,sK6,sK5,sK3,k2_tmap_1(sK3,sK4,sK7,sK6),k2_tmap_1(sK3,sK4,sK7,sK5))),
% 1.53/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 1.53/0.58  fof(f445,plain,(
% 1.53/0.58    ~m1_subset_1(k2_tmap_1(sK3,sK4,sK7,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4)))) | ~v1_funct_2(k2_tmap_1(sK3,sK4,sK7,sK5),u1_struct_0(sK5),u1_struct_0(sK4)) | ~v1_funct_1(k2_tmap_1(sK3,sK4,sK7,sK5)) | ~sP1(sK4,sK6,sK7,sK3) | spl8_8),
% 1.53/0.58    inference(subsumption_resolution,[],[f444,f56])).
% 1.53/0.58  fof(f56,plain,(
% 1.53/0.58    ~v2_struct_0(sK3)),
% 1.53/0.58    inference(cnf_transformation,[],[f47])).
% 1.53/0.58  fof(f444,plain,(
% 1.53/0.58    ~m1_subset_1(k2_tmap_1(sK3,sK4,sK7,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4)))) | ~v1_funct_2(k2_tmap_1(sK3,sK4,sK7,sK5),u1_struct_0(sK5),u1_struct_0(sK4)) | ~v1_funct_1(k2_tmap_1(sK3,sK4,sK7,sK5)) | v2_struct_0(sK3) | ~sP1(sK4,sK6,sK7,sK3) | spl8_8),
% 1.53/0.58    inference(subsumption_resolution,[],[f443,f57])).
% 1.53/0.58  fof(f57,plain,(
% 1.53/0.58    v2_pre_topc(sK3)),
% 1.53/0.58    inference(cnf_transformation,[],[f47])).
% 1.53/0.58  fof(f443,plain,(
% 1.53/0.58    ~m1_subset_1(k2_tmap_1(sK3,sK4,sK7,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4)))) | ~v1_funct_2(k2_tmap_1(sK3,sK4,sK7,sK5),u1_struct_0(sK5),u1_struct_0(sK4)) | ~v1_funct_1(k2_tmap_1(sK3,sK4,sK7,sK5)) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~sP1(sK4,sK6,sK7,sK3) | spl8_8),
% 1.53/0.58    inference(subsumption_resolution,[],[f442,f58])).
% 1.53/0.58  fof(f442,plain,(
% 1.53/0.58    ~m1_subset_1(k2_tmap_1(sK3,sK4,sK7,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4)))) | ~v1_funct_2(k2_tmap_1(sK3,sK4,sK7,sK5),u1_struct_0(sK5),u1_struct_0(sK4)) | ~v1_funct_1(k2_tmap_1(sK3,sK4,sK7,sK5)) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~sP1(sK4,sK6,sK7,sK3) | spl8_8),
% 1.53/0.58    inference(subsumption_resolution,[],[f441,f59])).
% 1.53/0.58  fof(f441,plain,(
% 1.53/0.58    ~m1_subset_1(k2_tmap_1(sK3,sK4,sK7,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4)))) | ~v1_funct_2(k2_tmap_1(sK3,sK4,sK7,sK5),u1_struct_0(sK5),u1_struct_0(sK4)) | ~v1_funct_1(k2_tmap_1(sK3,sK4,sK7,sK5)) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~sP1(sK4,sK6,sK7,sK3) | spl8_8),
% 1.53/0.58    inference(subsumption_resolution,[],[f440,f60])).
% 1.53/0.58  fof(f60,plain,(
% 1.53/0.58    v2_pre_topc(sK4)),
% 1.53/0.58    inference(cnf_transformation,[],[f47])).
% 1.53/0.58  fof(f440,plain,(
% 1.53/0.58    ~m1_subset_1(k2_tmap_1(sK3,sK4,sK7,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4)))) | ~v1_funct_2(k2_tmap_1(sK3,sK4,sK7,sK5),u1_struct_0(sK5),u1_struct_0(sK4)) | ~v1_funct_1(k2_tmap_1(sK3,sK4,sK7,sK5)) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~sP1(sK4,sK6,sK7,sK3) | spl8_8),
% 1.53/0.58    inference(subsumption_resolution,[],[f439,f61])).
% 1.53/0.58  fof(f61,plain,(
% 1.53/0.58    l1_pre_topc(sK4)),
% 1.53/0.58    inference(cnf_transformation,[],[f47])).
% 1.53/0.58  fof(f439,plain,(
% 1.53/0.58    ~m1_subset_1(k2_tmap_1(sK3,sK4,sK7,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4)))) | ~v1_funct_2(k2_tmap_1(sK3,sK4,sK7,sK5),u1_struct_0(sK5),u1_struct_0(sK4)) | ~v1_funct_1(k2_tmap_1(sK3,sK4,sK7,sK5)) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~sP1(sK4,sK6,sK7,sK3) | spl8_8),
% 1.53/0.58    inference(subsumption_resolution,[],[f438,f62])).
% 1.53/0.58  fof(f62,plain,(
% 1.53/0.58    ~v2_struct_0(sK5)),
% 1.53/0.58    inference(cnf_transformation,[],[f47])).
% 1.53/0.58  fof(f438,plain,(
% 1.53/0.58    ~m1_subset_1(k2_tmap_1(sK3,sK4,sK7,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4)))) | ~v1_funct_2(k2_tmap_1(sK3,sK4,sK7,sK5),u1_struct_0(sK5),u1_struct_0(sK4)) | ~v1_funct_1(k2_tmap_1(sK3,sK4,sK7,sK5)) | v2_struct_0(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~sP1(sK4,sK6,sK7,sK3) | spl8_8),
% 1.53/0.58    inference(subsumption_resolution,[],[f437,f63])).
% 1.53/0.58  fof(f437,plain,(
% 1.53/0.58    ~m1_subset_1(k2_tmap_1(sK3,sK4,sK7,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4)))) | ~v1_funct_2(k2_tmap_1(sK3,sK4,sK7,sK5),u1_struct_0(sK5),u1_struct_0(sK4)) | ~v1_funct_1(k2_tmap_1(sK3,sK4,sK7,sK5)) | ~m1_pre_topc(sK5,sK3) | v2_struct_0(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~sP1(sK4,sK6,sK7,sK3) | spl8_8),
% 1.53/0.58    inference(subsumption_resolution,[],[f436,f64])).
% 1.53/0.58  fof(f64,plain,(
% 1.53/0.58    ~v2_struct_0(sK6)),
% 1.53/0.58    inference(cnf_transformation,[],[f47])).
% 1.53/0.58  fof(f436,plain,(
% 1.53/0.58    ~m1_subset_1(k2_tmap_1(sK3,sK4,sK7,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4)))) | ~v1_funct_2(k2_tmap_1(sK3,sK4,sK7,sK5),u1_struct_0(sK5),u1_struct_0(sK4)) | ~v1_funct_1(k2_tmap_1(sK3,sK4,sK7,sK5)) | v2_struct_0(sK6) | ~m1_pre_topc(sK5,sK3) | v2_struct_0(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~sP1(sK4,sK6,sK7,sK3) | spl8_8),
% 1.53/0.58    inference(subsumption_resolution,[],[f432,f65])).
% 1.53/0.58  fof(f432,plain,(
% 1.53/0.58    ~m1_subset_1(k2_tmap_1(sK3,sK4,sK7,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4)))) | ~v1_funct_2(k2_tmap_1(sK3,sK4,sK7,sK5),u1_struct_0(sK5),u1_struct_0(sK4)) | ~v1_funct_1(k2_tmap_1(sK3,sK4,sK7,sK5)) | ~m1_pre_topc(sK6,sK3) | v2_struct_0(sK6) | ~m1_pre_topc(sK5,sK3) | v2_struct_0(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~sP1(sK4,sK6,sK7,sK3) | spl8_8),
% 1.53/0.58    inference(resolution,[],[f228,f339])).
% 1.53/0.58  fof(f339,plain,(
% 1.53/0.58    ~sP2(sK4,sK6,sK5,sK3,k2_tmap_1(sK3,sK4,sK7,sK6),k2_tmap_1(sK3,sK4,sK7,sK5)) | spl8_8),
% 1.53/0.58    inference(avatar_component_clause,[],[f337])).
% 1.53/0.58  fof(f228,plain,(
% 1.53/0.58    ( ! [X6,X4,X8,X7,X5,X3,X9] : (sP2(X3,X4,X5,X6,k2_tmap_1(X7,X3,X8,X4),X9) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X3)))) | ~v1_funct_2(X9,u1_struct_0(X5),u1_struct_0(X3)) | ~v1_funct_1(X9) | ~m1_pre_topc(X4,X6) | v2_struct_0(X4) | ~m1_pre_topc(X5,X6) | v2_struct_0(X5) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6) | ~sP1(X3,X4,X8,X7)) )),
% 1.53/0.58    inference(subsumption_resolution,[],[f227,f81])).
% 1.53/0.58  fof(f227,plain,(
% 1.53/0.58    ( ! [X6,X4,X8,X7,X5,X3,X9] : (sP2(X3,X4,X5,X6,k2_tmap_1(X7,X3,X8,X4),X9) | ~v1_funct_1(k2_tmap_1(X7,X3,X8,X4)) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X3)))) | ~v1_funct_2(X9,u1_struct_0(X5),u1_struct_0(X3)) | ~v1_funct_1(X9) | ~m1_pre_topc(X4,X6) | v2_struct_0(X4) | ~m1_pre_topc(X5,X6) | v2_struct_0(X5) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6) | ~sP1(X3,X4,X8,X7)) )),
% 1.53/0.58    inference(subsumption_resolution,[],[f218,f82])).
% 1.53/0.58  fof(f218,plain,(
% 1.53/0.58    ( ! [X6,X4,X8,X7,X5,X3,X9] : (sP2(X3,X4,X5,X6,k2_tmap_1(X7,X3,X8,X4),X9) | ~v1_funct_2(k2_tmap_1(X7,X3,X8,X4),u1_struct_0(X4),u1_struct_0(X3)) | ~v1_funct_1(k2_tmap_1(X7,X3,X8,X4)) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X3)))) | ~v1_funct_2(X9,u1_struct_0(X5),u1_struct_0(X3)) | ~v1_funct_1(X9) | ~m1_pre_topc(X4,X6) | v2_struct_0(X4) | ~m1_pre_topc(X5,X6) | v2_struct_0(X5) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6) | ~sP1(X3,X4,X8,X7)) )),
% 1.53/0.58    inference(resolution,[],[f92,f83])).
% 1.53/0.58  fof(f92,plain,(
% 1.53/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | sP2(X1,X3,X2,X0,X5,X4) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f41])).
% 1.53/0.58  fof(f41,plain,(
% 1.53/0.58    ! [X0,X1,X2,X3,X4,X5] : (sP2(X1,X3,X2,X0,X5,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.53/0.58    inference(definition_folding,[],[f35,f40])).
% 1.53/0.58  fof(f40,plain,(
% 1.53/0.58    ! [X1,X3,X2,X0,X5,X4] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | ~sP2(X1,X3,X2,X0,X5,X4))),
% 1.53/0.58    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 1.53/0.58  fof(f35,plain,(
% 1.53/0.58    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.53/0.58    inference(flattening,[],[f34])).
% 1.53/0.58  fof(f34,plain,(
% 1.53/0.58    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.53/0.58    inference(ennf_transformation,[],[f8])).
% 1.53/0.58  fof(f8,axiom,(
% 1.53/0.58    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 1.53/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_tmap_1)).
% 1.53/0.58  fof(f344,plain,(
% 1.53/0.58    ~spl8_8 | ~spl8_9 | ~spl8_3),
% 1.53/0.58    inference(avatar_split_clause,[],[f335,f131,f341,f337])).
% 1.53/0.58  fof(f131,plain,(
% 1.53/0.58    spl8_3 <=> m1_pre_topc(sK3,sK3)),
% 1.53/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 1.53/0.58  fof(f335,plain,(
% 1.53/0.58    ~r1_funct_2(u1_struct_0(sK3),u1_struct_0(sK4),u1_struct_0(sK3),u1_struct_0(sK4),sK7,sK7) | ~sP2(sK4,sK6,sK5,sK3,k2_tmap_1(sK3,sK4,sK7,sK6),k2_tmap_1(sK3,sK4,sK7,sK5)) | ~spl8_3),
% 1.53/0.58    inference(subsumption_resolution,[],[f334,f69])).
% 1.53/0.58  fof(f334,plain,(
% 1.53/0.58    ~r1_funct_2(u1_struct_0(sK3),u1_struct_0(sK4),u1_struct_0(sK3),u1_struct_0(sK4),sK7,sK7) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) | ~sP2(sK4,sK6,sK5,sK3,k2_tmap_1(sK3,sK4,sK7,sK6),k2_tmap_1(sK3,sK4,sK7,sK5)) | ~spl8_3),
% 1.53/0.58    inference(subsumption_resolution,[],[f333,f59])).
% 1.53/0.58  fof(f333,plain,(
% 1.53/0.58    ~r1_funct_2(u1_struct_0(sK3),u1_struct_0(sK4),u1_struct_0(sK3),u1_struct_0(sK4),sK7,sK7) | v2_struct_0(sK4) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) | ~sP2(sK4,sK6,sK5,sK3,k2_tmap_1(sK3,sK4,sK7,sK6),k2_tmap_1(sK3,sK4,sK7,sK5)) | ~spl8_3),
% 1.53/0.58    inference(subsumption_resolution,[],[f332,f60])).
% 1.53/0.58  fof(f332,plain,(
% 1.53/0.58    ~r1_funct_2(u1_struct_0(sK3),u1_struct_0(sK4),u1_struct_0(sK3),u1_struct_0(sK4),sK7,sK7) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) | ~sP2(sK4,sK6,sK5,sK3,k2_tmap_1(sK3,sK4,sK7,sK6),k2_tmap_1(sK3,sK4,sK7,sK5)) | ~spl8_3),
% 1.53/0.58    inference(subsumption_resolution,[],[f331,f61])).
% 1.53/0.58  fof(f331,plain,(
% 1.53/0.58    ~r1_funct_2(u1_struct_0(sK3),u1_struct_0(sK4),u1_struct_0(sK3),u1_struct_0(sK4),sK7,sK7) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) | ~sP2(sK4,sK6,sK5,sK3,k2_tmap_1(sK3,sK4,sK7,sK6),k2_tmap_1(sK3,sK4,sK7,sK5)) | ~spl8_3),
% 1.53/0.58    inference(subsumption_resolution,[],[f330,f67])).
% 1.53/0.58  fof(f330,plain,(
% 1.53/0.58    ~r1_funct_2(u1_struct_0(sK3),u1_struct_0(sK4),u1_struct_0(sK3),u1_struct_0(sK4),sK7,sK7) | ~v1_funct_1(sK7) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) | ~sP2(sK4,sK6,sK5,sK3,k2_tmap_1(sK3,sK4,sK7,sK6),k2_tmap_1(sK3,sK4,sK7,sK5)) | ~spl8_3),
% 1.53/0.58    inference(subsumption_resolution,[],[f299,f68])).
% 1.53/0.58  fof(f299,plain,(
% 1.53/0.58    ~r1_funct_2(u1_struct_0(sK3),u1_struct_0(sK4),u1_struct_0(sK3),u1_struct_0(sK4),sK7,sK7) | ~v1_funct_2(sK7,u1_struct_0(sK3),u1_struct_0(sK4)) | ~v1_funct_1(sK7) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) | ~sP2(sK4,sK6,sK5,sK3,k2_tmap_1(sK3,sK4,sK7,sK6),k2_tmap_1(sK3,sK4,sK7,sK5)) | ~spl8_3),
% 1.53/0.58    inference(superposition,[],[f115,f294])).
% 1.53/0.58  fof(f294,plain,(
% 1.53/0.58    ( ! [X0,X1] : (k10_tmap_1(sK3,X1,sK5,sK6,k2_tmap_1(sK3,X1,X0,sK5),k2_tmap_1(sK3,X1,X0,sK6)) = X0 | ~v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) | ~sP2(X1,sK6,sK5,sK3,k2_tmap_1(sK3,X1,X0,sK6),k2_tmap_1(sK3,X1,X0,sK5))) ) | ~spl8_3),
% 1.53/0.58    inference(duplicate_literal_removal,[],[f293])).
% 1.53/0.58  fof(f293,plain,(
% 1.53/0.58    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) | ~v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | k10_tmap_1(sK3,X1,sK5,sK6,k2_tmap_1(sK3,X1,X0,sK5),k2_tmap_1(sK3,X1,X0,sK6)) = X0 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) | ~v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~sP2(X1,sK6,sK5,sK3,k2_tmap_1(sK3,X1,X0,sK6),k2_tmap_1(sK3,X1,X0,sK5))) ) | ~spl8_3),
% 1.53/0.58    inference(resolution,[],[f292,f183])).
% 1.53/0.58  fof(f183,plain,(
% 1.53/0.58    ( ! [X14,X15,X13,X16] : (~r2_funct_2(u1_struct_0(sK3),u1_struct_0(X13),X14,k10_tmap_1(sK3,X13,sK5,sK6,X15,X16)) | k10_tmap_1(sK3,X13,sK5,sK6,X15,X16) = X14 | ~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X13)))) | ~v1_funct_2(X14,u1_struct_0(sK3),u1_struct_0(X13)) | ~v1_funct_1(X14) | ~sP2(X13,sK6,sK5,sK3,X16,X15)) )),
% 1.53/0.58    inference(subsumption_resolution,[],[f182,f89])).
% 1.53/0.58  fof(f89,plain,(
% 1.53/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k10_tmap_1(X3,X0,X2,X1,X5,X4)) | ~sP2(X0,X1,X2,X3,X4,X5)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f55])).
% 1.53/0.58  fof(f55,plain,(
% 1.53/0.58    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k10_tmap_1(X3,X0,X2,X1,X5,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) & v1_funct_2(k10_tmap_1(X3,X0,X2,X1,X5,X4),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) & v1_funct_1(k10_tmap_1(X3,X0,X2,X1,X5,X4))) | ~sP2(X0,X1,X2,X3,X4,X5))),
% 1.53/0.58    inference(rectify,[],[f54])).
% 1.53/0.58  fof(f54,plain,(
% 1.53/0.58    ! [X1,X3,X2,X0,X5,X4] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | ~sP2(X1,X3,X2,X0,X5,X4))),
% 1.53/0.58    inference(nnf_transformation,[],[f40])).
% 1.53/0.58  fof(f182,plain,(
% 1.53/0.58    ( ! [X14,X15,X13,X16] : (~r2_funct_2(u1_struct_0(sK3),u1_struct_0(X13),X14,k10_tmap_1(sK3,X13,sK5,sK6,X15,X16)) | k10_tmap_1(sK3,X13,sK5,sK6,X15,X16) = X14 | ~v1_funct_1(k10_tmap_1(sK3,X13,sK5,sK6,X15,X16)) | ~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X13)))) | ~v1_funct_2(X14,u1_struct_0(sK3),u1_struct_0(X13)) | ~v1_funct_1(X14) | ~sP2(X13,sK6,sK5,sK3,X16,X15)) )),
% 1.53/0.58    inference(subsumption_resolution,[],[f175,f136])).
% 1.53/0.58  fof(f136,plain,(
% 1.53/0.58    ( ! [X2,X0,X1] : (v1_funct_2(k10_tmap_1(sK3,X0,sK5,sK6,X1,X2),u1_struct_0(sK3),u1_struct_0(X0)) | ~sP2(X0,sK6,sK5,sK3,X2,X1)) )),
% 1.53/0.58    inference(superposition,[],[f90,f66])).
% 1.53/0.58  fof(f66,plain,(
% 1.53/0.58    sK3 = k1_tsep_1(sK3,sK5,sK6)),
% 1.53/0.58    inference(cnf_transformation,[],[f47])).
% 1.53/0.58  fof(f90,plain,(
% 1.53/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k10_tmap_1(X3,X0,X2,X1,X5,X4),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) | ~sP2(X0,X1,X2,X3,X4,X5)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f55])).
% 1.53/0.58  fof(f175,plain,(
% 1.53/0.58    ( ! [X14,X15,X13,X16] : (~r2_funct_2(u1_struct_0(sK3),u1_struct_0(X13),X14,k10_tmap_1(sK3,X13,sK5,sK6,X15,X16)) | k10_tmap_1(sK3,X13,sK5,sK6,X15,X16) = X14 | ~v1_funct_2(k10_tmap_1(sK3,X13,sK5,sK6,X15,X16),u1_struct_0(sK3),u1_struct_0(X13)) | ~v1_funct_1(k10_tmap_1(sK3,X13,sK5,sK6,X15,X16)) | ~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X13)))) | ~v1_funct_2(X14,u1_struct_0(sK3),u1_struct_0(X13)) | ~v1_funct_1(X14) | ~sP2(X13,sK6,sK5,sK3,X16,X15)) )),
% 1.53/0.58    inference(resolution,[],[f85,f138])).
% 1.53/0.58  fof(f138,plain,(
% 1.53/0.58    ( ! [X2,X0,X1] : (m1_subset_1(k10_tmap_1(sK3,X0,sK5,sK6,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~sP2(X0,sK6,sK5,sK3,X2,X1)) )),
% 1.53/0.58    inference(superposition,[],[f91,f66])).
% 1.53/0.58  fof(f91,plain,(
% 1.53/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k10_tmap_1(X3,X0,X2,X1,X5,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) | ~sP2(X0,X1,X2,X3,X4,X5)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f55])).
% 1.53/0.58  fof(f85,plain,(
% 1.53/0.58    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_funct_2(X0,X1,X2,X3) | X2 = X3 | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f52])).
% 1.53/0.58  fof(f52,plain,(
% 1.53/0.58    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.53/0.58    inference(nnf_transformation,[],[f31])).
% 1.53/0.58  fof(f31,plain,(
% 1.53/0.58    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.53/0.58    inference(flattening,[],[f30])).
% 1.53/0.58  fof(f30,plain,(
% 1.53/0.58    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.53/0.58    inference(ennf_transformation,[],[f1])).
% 1.53/0.58  fof(f1,axiom,(
% 1.53/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 1.53/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).
% 1.53/0.58  fof(f292,plain,(
% 1.53/0.58    ( ! [X0,X1] : (r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0),X1,k10_tmap_1(sK3,X0,sK5,sK6,k2_tmap_1(sK3,X0,X1,sK5),k2_tmap_1(sK3,X0,X1,sK6))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) ) | ~spl8_3),
% 1.53/0.58    inference(subsumption_resolution,[],[f291,f56])).
% 1.53/0.58  fof(f291,plain,(
% 1.53/0.58    ( ! [X0,X1] : (r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0),X1,k10_tmap_1(sK3,X0,sK5,sK6,k2_tmap_1(sK3,X0,X1,sK5),k2_tmap_1(sK3,X0,X1,sK6))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v2_struct_0(sK3)) ) | ~spl8_3),
% 1.53/0.58    inference(subsumption_resolution,[],[f290,f57])).
% 1.53/0.58  fof(f290,plain,(
% 1.53/0.58    ( ! [X0,X1] : (r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0),X1,k10_tmap_1(sK3,X0,sK5,sK6,k2_tmap_1(sK3,X0,X1,sK5),k2_tmap_1(sK3,X0,X1,sK6))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) ) | ~spl8_3),
% 1.53/0.58    inference(subsumption_resolution,[],[f289,f58])).
% 1.53/0.58  fof(f289,plain,(
% 1.53/0.58    ( ! [X0,X1] : (r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0),X1,k10_tmap_1(sK3,X0,sK5,sK6,k2_tmap_1(sK3,X0,X1,sK5),k2_tmap_1(sK3,X0,X1,sK6))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) ) | ~spl8_3),
% 1.53/0.58    inference(subsumption_resolution,[],[f288,f133])).
% 1.53/0.58  fof(f133,plain,(
% 1.53/0.58    m1_pre_topc(sK3,sK3) | ~spl8_3),
% 1.53/0.58    inference(avatar_component_clause,[],[f131])).
% 1.53/0.58  fof(f288,plain,(
% 1.53/0.58    ( ! [X0,X1] : (r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0),X1,k10_tmap_1(sK3,X0,sK5,sK6,k2_tmap_1(sK3,X0,X1,sK5),k2_tmap_1(sK3,X0,X1,sK6))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(sK3,sK3) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) ) | ~spl8_3),
% 1.53/0.58    inference(subsumption_resolution,[],[f286,f65])).
% 1.53/0.58  fof(f286,plain,(
% 1.53/0.58    ( ! [X0,X1] : (r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0),X1,k10_tmap_1(sK3,X0,sK5,sK6,k2_tmap_1(sK3,X0,X1,sK5),k2_tmap_1(sK3,X0,X1,sK6))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(sK6,sK3) | ~m1_pre_topc(sK3,sK3) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) ) | ~spl8_3),
% 1.53/0.58    inference(duplicate_literal_removal,[],[f285])).
% 1.53/0.58  fof(f285,plain,(
% 1.53/0.58    ( ! [X0,X1] : (r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0),X1,k10_tmap_1(sK3,X0,sK5,sK6,k2_tmap_1(sK3,X0,X1,sK5),k2_tmap_1(sK3,X0,X1,sK6))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(sK6,sK3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~m1_pre_topc(sK6,sK3) | ~m1_pre_topc(sK3,sK3) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) ) | ~spl8_3),
% 1.53/0.58    inference(superposition,[],[f278,f211])).
% 1.53/0.58  fof(f211,plain,(
% 1.53/0.58    ( ! [X6,X10,X8,X7,X9] : (k2_tmap_1(X6,X7,X8,X9) = k3_tmap_1(X10,X7,X6,X9,X8) | ~m1_pre_topc(X9,X6) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(X7)))) | ~v1_funct_2(X8,u1_struct_0(X6),u1_struct_0(X7)) | ~v1_funct_1(X8) | ~m1_pre_topc(X9,X10) | ~m1_pre_topc(X6,X10) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7) | v2_struct_0(X7) | ~l1_pre_topc(X10) | ~v2_pre_topc(X10) | v2_struct_0(X10) | ~v2_pre_topc(X6) | v2_struct_0(X6)) )),
% 1.53/0.58    inference(subsumption_resolution,[],[f209,f72])).
% 1.53/0.58  fof(f209,plain,(
% 1.53/0.58    ( ! [X6,X10,X8,X7,X9] : (k2_tmap_1(X6,X7,X8,X9) = k3_tmap_1(X10,X7,X6,X9,X8) | ~m1_pre_topc(X9,X6) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(X7)))) | ~v1_funct_2(X8,u1_struct_0(X6),u1_struct_0(X7)) | ~v1_funct_1(X8) | ~m1_pre_topc(X9,X10) | ~m1_pre_topc(X6,X10) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7) | v2_struct_0(X7) | ~l1_pre_topc(X10) | ~v2_pre_topc(X10) | v2_struct_0(X10) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6)) )),
% 1.53/0.58    inference(duplicate_literal_removal,[],[f206])).
% 1.53/0.58  fof(f206,plain,(
% 1.53/0.58    ( ! [X6,X10,X8,X7,X9] : (k2_tmap_1(X6,X7,X8,X9) = k3_tmap_1(X10,X7,X6,X9,X8) | ~m1_pre_topc(X9,X6) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(X7)))) | ~v1_funct_2(X8,u1_struct_0(X6),u1_struct_0(X7)) | ~v1_funct_1(X8) | ~m1_pre_topc(X9,X10) | ~m1_pre_topc(X6,X10) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7) | v2_struct_0(X7) | ~l1_pre_topc(X10) | ~v2_pre_topc(X10) | v2_struct_0(X10) | ~m1_pre_topc(X9,X6) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(X7)))) | ~v1_funct_2(X8,u1_struct_0(X6),u1_struct_0(X7)) | ~v1_funct_1(X8) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7) | v2_struct_0(X7) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6)) )),
% 1.53/0.58    inference(superposition,[],[f74,f76])).
% 1.53/0.58  fof(f76,plain,(
% 1.53/0.58    ( ! [X2,X0,X3,X1] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f25])).
% 1.53/0.58  fof(f25,plain,(
% 1.53/0.58    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.53/0.58    inference(flattening,[],[f24])).
% 1.53/0.58  fof(f24,plain,(
% 1.53/0.58    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.53/0.58    inference(ennf_transformation,[],[f6])).
% 1.53/0.58  fof(f6,axiom,(
% 1.53/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 1.53/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).
% 1.53/0.58  fof(f74,plain,(
% 1.53/0.58    ( ! [X4,X2,X0,X3,X1] : (k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f21])).
% 1.53/0.58  fof(f21,plain,(
% 1.53/0.58    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.53/0.58    inference(flattening,[],[f20])).
% 1.53/0.58  fof(f20,plain,(
% 1.53/0.58    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.53/0.58    inference(ennf_transformation,[],[f7])).
% 1.53/0.58  fof(f7,axiom,(
% 1.53/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))))))))),
% 1.53/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).
% 1.53/0.58  fof(f278,plain,(
% 1.53/0.58    ( ! [X0,X1] : (r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0),X1,k10_tmap_1(sK3,X0,sK5,sK6,k2_tmap_1(sK3,X0,X1,sK5),k3_tmap_1(sK3,X0,sK3,sK6,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) ) | ~spl8_3),
% 1.53/0.58    inference(subsumption_resolution,[],[f277,f56])).
% 1.53/0.58  fof(f277,plain,(
% 1.53/0.58    ( ! [X0,X1] : (r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0),X1,k10_tmap_1(sK3,X0,sK5,sK6,k2_tmap_1(sK3,X0,X1,sK5),k3_tmap_1(sK3,X0,sK3,sK6,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v2_struct_0(sK3)) ) | ~spl8_3),
% 1.53/0.58    inference(subsumption_resolution,[],[f276,f57])).
% 1.53/0.58  fof(f276,plain,(
% 1.53/0.58    ( ! [X0,X1] : (r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0),X1,k10_tmap_1(sK3,X0,sK5,sK6,k2_tmap_1(sK3,X0,X1,sK5),k3_tmap_1(sK3,X0,sK3,sK6,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) ) | ~spl8_3),
% 1.53/0.58    inference(subsumption_resolution,[],[f275,f58])).
% 1.53/0.58  fof(f275,plain,(
% 1.53/0.58    ( ! [X0,X1] : (r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0),X1,k10_tmap_1(sK3,X0,sK5,sK6,k2_tmap_1(sK3,X0,X1,sK5),k3_tmap_1(sK3,X0,sK3,sK6,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) ) | ~spl8_3),
% 1.53/0.58    inference(subsumption_resolution,[],[f274,f133])).
% 1.53/0.58  fof(f274,plain,(
% 1.53/0.58    ( ! [X0,X1] : (r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0),X1,k10_tmap_1(sK3,X0,sK5,sK6,k2_tmap_1(sK3,X0,X1,sK5),k3_tmap_1(sK3,X0,sK3,sK6,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(sK3,sK3) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) )),
% 1.53/0.58    inference(subsumption_resolution,[],[f272,f63])).
% 1.53/0.58  fof(f272,plain,(
% 1.53/0.58    ( ! [X0,X1] : (r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0),X1,k10_tmap_1(sK3,X0,sK5,sK6,k2_tmap_1(sK3,X0,X1,sK5),k3_tmap_1(sK3,X0,sK3,sK6,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(sK5,sK3) | ~m1_pre_topc(sK3,sK3) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) )),
% 1.53/0.58    inference(duplicate_literal_removal,[],[f269])).
% 1.53/0.58  fof(f269,plain,(
% 1.53/0.58    ( ! [X0,X1] : (r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0),X1,k10_tmap_1(sK3,X0,sK5,sK6,k2_tmap_1(sK3,X0,X1,sK5),k3_tmap_1(sK3,X0,sK3,sK6,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(sK5,sK3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~m1_pre_topc(sK5,sK3) | ~m1_pre_topc(sK3,sK3) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) )),
% 1.53/0.58    inference(superposition,[],[f267,f211])).
% 1.53/0.58  fof(f267,plain,(
% 1.53/0.58    ( ! [X0,X1] : (r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0),X1,k10_tmap_1(sK3,X0,sK5,sK6,k3_tmap_1(sK3,X0,sK3,sK5,X1),k3_tmap_1(sK3,X0,sK3,sK6,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.53/0.58    inference(subsumption_resolution,[],[f266,f56])).
% 1.53/0.58  fof(f266,plain,(
% 1.53/0.58    ( ! [X0,X1] : (r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0),X1,k10_tmap_1(sK3,X0,sK5,sK6,k3_tmap_1(sK3,X0,sK3,sK5,X1),k3_tmap_1(sK3,X0,sK3,sK6,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v2_struct_0(sK3)) )),
% 1.53/0.58    inference(subsumption_resolution,[],[f265,f57])).
% 1.53/0.58  fof(f265,plain,(
% 1.53/0.58    ( ! [X0,X1] : (r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0),X1,k10_tmap_1(sK3,X0,sK5,sK6,k3_tmap_1(sK3,X0,sK3,sK5,X1),k3_tmap_1(sK3,X0,sK3,sK6,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) )),
% 1.53/0.58    inference(subsumption_resolution,[],[f264,f58])).
% 1.53/0.58  fof(f264,plain,(
% 1.53/0.58    ( ! [X0,X1] : (r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0),X1,k10_tmap_1(sK3,X0,sK5,sK6,k3_tmap_1(sK3,X0,sK3,sK5,X1),k3_tmap_1(sK3,X0,sK3,sK6,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) )),
% 1.53/0.58    inference(subsumption_resolution,[],[f263,f62])).
% 1.53/0.58  fof(f263,plain,(
% 1.53/0.58    ( ! [X0,X1] : (r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0),X1,k10_tmap_1(sK3,X0,sK5,sK6,k3_tmap_1(sK3,X0,sK3,sK5,X1),k3_tmap_1(sK3,X0,sK3,sK6,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0)) | ~v1_funct_1(X1) | v2_struct_0(sK5) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) )),
% 1.53/0.58    inference(subsumption_resolution,[],[f262,f63])).
% 1.53/0.58  fof(f262,plain,(
% 1.53/0.58    ( ! [X0,X1] : (r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0),X1,k10_tmap_1(sK3,X0,sK5,sK6,k3_tmap_1(sK3,X0,sK3,sK5,X1),k3_tmap_1(sK3,X0,sK3,sK6,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~m1_pre_topc(sK5,sK3) | v2_struct_0(sK5) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) )),
% 1.53/0.58    inference(subsumption_resolution,[],[f261,f64])).
% 1.53/0.58  fof(f261,plain,(
% 1.53/0.58    ( ! [X0,X1] : (r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0),X1,k10_tmap_1(sK3,X0,sK5,sK6,k3_tmap_1(sK3,X0,sK3,sK5,X1),k3_tmap_1(sK3,X0,sK3,sK6,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0)) | ~v1_funct_1(X1) | v2_struct_0(sK6) | ~m1_pre_topc(sK5,sK3) | v2_struct_0(sK5) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) )),
% 1.53/0.58    inference(subsumption_resolution,[],[f254,f65])).
% 1.53/0.58  fof(f254,plain,(
% 1.53/0.58    ( ! [X0,X1] : (r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0),X1,k10_tmap_1(sK3,X0,sK5,sK6,k3_tmap_1(sK3,X0,sK3,sK5,X1),k3_tmap_1(sK3,X0,sK3,sK6,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~m1_pre_topc(sK6,sK3) | v2_struct_0(sK6) | ~m1_pre_topc(sK5,sK3) | v2_struct_0(sK5) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) )),
% 1.53/0.58    inference(superposition,[],[f75,f66])).
% 1.53/0.58  fof(f75,plain,(
% 1.53/0.58    ( ! [X4,X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f23])).
% 1.53/0.58  fof(f23,plain,(
% 1.53/0.58    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r2_funct_2(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.53/0.58    inference(flattening,[],[f22])).
% 1.53/0.58  fof(f22,plain,(
% 1.53/0.58    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r2_funct_2(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.53/0.58    inference(ennf_transformation,[],[f11])).
% 1.53/0.58  fof(f11,axiom,(
% 1.53/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) => r2_funct_2(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))))))))),
% 1.53/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_tmap_1)).
% 1.53/0.58  fof(f115,plain,(
% 1.53/0.58    ~r1_funct_2(u1_struct_0(sK3),u1_struct_0(sK4),u1_struct_0(sK3),u1_struct_0(sK4),sK7,k10_tmap_1(sK3,sK4,sK5,sK6,k2_tmap_1(sK3,sK4,sK7,sK5),k2_tmap_1(sK3,sK4,sK7,sK6)))),
% 1.53/0.58    inference(forward_demodulation,[],[f70,f66])).
% 1.53/0.58  fof(f70,plain,(
% 1.53/0.58    ~r1_funct_2(u1_struct_0(sK3),u1_struct_0(sK4),u1_struct_0(k1_tsep_1(sK3,sK5,sK6)),u1_struct_0(sK4),sK7,k10_tmap_1(sK3,sK4,sK5,sK6,k2_tmap_1(sK3,sK4,sK7,sK5),k2_tmap_1(sK3,sK4,sK7,sK6)))),
% 1.53/0.58    inference(cnf_transformation,[],[f47])).
% 1.53/0.58  fof(f189,plain,(
% 1.53/0.58    spl8_5),
% 1.53/0.58    inference(avatar_contradiction_clause,[],[f188])).
% 1.53/0.58  fof(f188,plain,(
% 1.53/0.58    $false | spl8_5),
% 1.53/0.58    inference(subsumption_resolution,[],[f187,f61])).
% 1.53/0.58  fof(f187,plain,(
% 1.53/0.58    ~l1_pre_topc(sK4) | spl8_5),
% 1.53/0.58    inference(resolution,[],[f157,f71])).
% 1.53/0.58  fof(f157,plain,(
% 1.53/0.58    ~l1_struct_0(sK4) | spl8_5),
% 1.53/0.58    inference(avatar_component_clause,[],[f155])).
% 1.53/0.58  fof(f186,plain,(
% 1.53/0.58    spl8_4),
% 1.53/0.58    inference(avatar_contradiction_clause,[],[f185])).
% 1.53/0.58  fof(f185,plain,(
% 1.53/0.58    $false | spl8_4),
% 1.53/0.58    inference(subsumption_resolution,[],[f184,f58])).
% 1.53/0.58  fof(f184,plain,(
% 1.53/0.58    ~l1_pre_topc(sK3) | spl8_4),
% 1.53/0.58    inference(resolution,[],[f153,f71])).
% 1.53/0.58  fof(f153,plain,(
% 1.53/0.58    ~l1_struct_0(sK3) | spl8_4),
% 1.53/0.58    inference(avatar_component_clause,[],[f151])).
% 1.53/0.58  fof(f151,plain,(
% 1.53/0.58    spl8_4 <=> l1_struct_0(sK3)),
% 1.53/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 1.53/0.58  fof(f161,plain,(
% 1.53/0.58    ~spl8_4 | ~spl8_5 | spl8_6),
% 1.53/0.58    inference(avatar_split_clause,[],[f149,f159,f155,f151])).
% 1.53/0.58  fof(f149,plain,(
% 1.53/0.58    ( ! [X0] : (~l1_struct_0(X0) | sP1(sK4,X0,sK7,sK3) | ~l1_struct_0(sK4) | ~l1_struct_0(sK3)) )),
% 1.53/0.58    inference(subsumption_resolution,[],[f148,f67])).
% 1.53/0.58  fof(f148,plain,(
% 1.53/0.58    ( ! [X0] : (~l1_struct_0(X0) | sP1(sK4,X0,sK7,sK3) | ~v1_funct_1(sK7) | ~l1_struct_0(sK4) | ~l1_struct_0(sK3)) )),
% 1.53/0.58    inference(subsumption_resolution,[],[f144,f68])).
% 1.53/0.58  fof(f144,plain,(
% 1.53/0.58    ( ! [X0] : (~l1_struct_0(X0) | sP1(sK4,X0,sK7,sK3) | ~v1_funct_2(sK7,u1_struct_0(sK3),u1_struct_0(sK4)) | ~v1_funct_1(sK7) | ~l1_struct_0(sK4) | ~l1_struct_0(sK3)) )),
% 1.53/0.58    inference(resolution,[],[f84,f69])).
% 1.53/0.58  fof(f84,plain,(
% 1.53/0.58    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~l1_struct_0(X3) | sP1(X1,X3,X2,X0) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f39])).
% 1.53/0.58  fof(f39,plain,(
% 1.53/0.58    ! [X0,X1,X2,X3] : (sP1(X1,X3,X2,X0) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 1.53/0.58    inference(definition_folding,[],[f29,f38])).
% 1.53/0.58  fof(f29,plain,(
% 1.53/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 1.53/0.58    inference(flattening,[],[f28])).
% 1.53/0.58  fof(f28,plain,(
% 1.53/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 1.53/0.58    inference(ennf_transformation,[],[f10])).
% 1.53/0.58  fof(f10,axiom,(
% 1.53/0.58    ! [X0,X1,X2,X3] : ((l1_struct_0(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2) & l1_struct_0(X1) & l1_struct_0(X0)) => (m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))),
% 1.53/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tmap_1)).
% 1.53/0.58  fof(f134,plain,(
% 1.53/0.58    ~spl8_1 | spl8_3),
% 1.53/0.58    inference(avatar_split_clause,[],[f113,f131,f104])).
% 1.53/0.58  fof(f104,plain,(
% 1.53/0.58    spl8_1 <=> sP0(sK3,sK6,sK5)),
% 1.53/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 1.53/0.58  fof(f113,plain,(
% 1.53/0.58    m1_pre_topc(sK3,sK3) | ~sP0(sK3,sK6,sK5)),
% 1.53/0.58    inference(superposition,[],[f79,f66])).
% 1.53/0.58  fof(f79,plain,(
% 1.53/0.58    ( ! [X2,X0,X1] : (m1_pre_topc(k1_tsep_1(X0,X2,X1),X0) | ~sP0(X0,X1,X2)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f49])).
% 1.53/0.58  fof(f49,plain,(
% 1.53/0.58    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X2,X1),X0) & v1_pre_topc(k1_tsep_1(X0,X2,X1)) & ~v2_struct_0(k1_tsep_1(X0,X2,X1))) | ~sP0(X0,X1,X2))),
% 1.53/0.58    inference(rectify,[],[f48])).
% 1.53/0.58  fof(f48,plain,(
% 1.53/0.58    ! [X0,X2,X1] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~sP0(X0,X2,X1))),
% 1.53/0.58    inference(nnf_transformation,[],[f36])).
% 1.53/0.58  fof(f36,plain,(
% 1.53/0.58    ! [X0,X2,X1] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~sP0(X0,X2,X1))),
% 1.53/0.58    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.53/0.58  fof(f129,plain,(
% 1.53/0.58    spl8_1),
% 1.53/0.58    inference(avatar_contradiction_clause,[],[f128])).
% 1.53/0.58  fof(f128,plain,(
% 1.53/0.58    $false | spl8_1),
% 1.53/0.58    inference(subsumption_resolution,[],[f127,f56])).
% 1.53/0.58  fof(f127,plain,(
% 1.53/0.58    v2_struct_0(sK3) | spl8_1),
% 1.53/0.58    inference(subsumption_resolution,[],[f126,f58])).
% 1.53/0.58  fof(f126,plain,(
% 1.53/0.58    ~l1_pre_topc(sK3) | v2_struct_0(sK3) | spl8_1),
% 1.53/0.58    inference(subsumption_resolution,[],[f125,f62])).
% 1.53/0.58  fof(f125,plain,(
% 1.53/0.58    v2_struct_0(sK5) | ~l1_pre_topc(sK3) | v2_struct_0(sK3) | spl8_1),
% 1.53/0.58    inference(subsumption_resolution,[],[f124,f63])).
% 1.53/0.58  fof(f124,plain,(
% 1.53/0.58    ~m1_pre_topc(sK5,sK3) | v2_struct_0(sK5) | ~l1_pre_topc(sK3) | v2_struct_0(sK3) | spl8_1),
% 1.53/0.58    inference(subsumption_resolution,[],[f123,f64])).
% 1.53/0.58  fof(f123,plain,(
% 1.53/0.58    v2_struct_0(sK6) | ~m1_pre_topc(sK5,sK3) | v2_struct_0(sK5) | ~l1_pre_topc(sK3) | v2_struct_0(sK3) | spl8_1),
% 1.53/0.58    inference(subsumption_resolution,[],[f122,f65])).
% 1.53/0.58  fof(f122,plain,(
% 1.53/0.58    ~m1_pre_topc(sK6,sK3) | v2_struct_0(sK6) | ~m1_pre_topc(sK5,sK3) | v2_struct_0(sK5) | ~l1_pre_topc(sK3) | v2_struct_0(sK3) | spl8_1),
% 1.53/0.58    inference(resolution,[],[f80,f106])).
% 1.53/0.58  fof(f106,plain,(
% 1.53/0.58    ~sP0(sK3,sK6,sK5) | spl8_1),
% 1.53/0.58    inference(avatar_component_clause,[],[f104])).
% 1.53/0.58  fof(f80,plain,(
% 1.53/0.58    ( ! [X2,X0,X1] : (sP0(X0,X2,X1) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f37])).
% 1.53/0.58  fof(f37,plain,(
% 1.53/0.58    ! [X0,X1,X2] : (sP0(X0,X2,X1) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.53/0.58    inference(definition_folding,[],[f27,f36])).
% 1.53/0.58  fof(f27,plain,(
% 1.53/0.58    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.53/0.58    inference(flattening,[],[f26])).
% 1.53/0.58  fof(f26,plain,(
% 1.53/0.58    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.53/0.58    inference(ennf_transformation,[],[f9])).
% 1.53/0.58  fof(f9,axiom,(
% 1.53/0.58    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 1.53/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tsep_1)).
% 1.53/0.58  % SZS output end Proof for theBenchmark
% 1.53/0.58  % (17368)------------------------------
% 1.53/0.58  % (17368)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.58  % (17368)Termination reason: Refutation
% 1.53/0.58  
% 1.53/0.58  % (17368)Memory used [KB]: 6780
% 1.53/0.58  % (17368)Time elapsed: 0.150 s
% 1.53/0.58  % (17368)------------------------------
% 1.53/0.58  % (17368)------------------------------
% 1.53/0.58  % (17361)Success in time 0.218 s
%------------------------------------------------------------------------------
