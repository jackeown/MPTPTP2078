%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:01 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  171 ( 701 expanded)
%              Number of leaves         :   22 ( 139 expanded)
%              Depth                    :   26
%              Number of atoms          :  807 (6968 expanded)
%              Number of equality atoms :   51 ( 686 expanded)
%              Maximal formula depth    :   28 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f694,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f140,f150,f353,f369,f391,f394,f693])).

fof(f693,plain,
    ( ~ spl7_13
    | ~ spl7_15
    | ~ spl7_16 ),
    inference(avatar_contradiction_clause,[],[f692])).

fof(f692,plain,
    ( $false
    | ~ spl7_13
    | ~ spl7_15
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f691,f59])).

fof(f59,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_tmap_1(X3,X1,X4,X5)
                              & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_tmap_1(X3,X1,X4,X5)
                              & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
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
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
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
                       => ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                         => ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X3))
                             => ! [X6] :
                                  ( m1_subset_1(X6,u1_struct_0(X2))
                                 => ( ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                      & X5 = X6 )
                                   => r1_tmap_1(X3,X1,X4,X5) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
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
                     => ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X2))
                               => ( ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                    & X5 = X6 )
                                 => r1_tmap_1(X3,X1,X4,X5) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tmap_1)).

fof(f691,plain,
    ( v2_struct_0(sK0)
    | ~ spl7_13
    | ~ spl7_15
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f690,f53])).

fof(f53,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f690,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_13
    | ~ spl7_15
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f689,f61])).

fof(f61,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f689,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_13
    | ~ spl7_15
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f688,f60])).

fof(f60,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f688,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_13
    | ~ spl7_15
    | ~ spl7_16 ),
    inference(resolution,[],[f687,f89])).

fof(f89,plain,(
    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
    inference(backward_demodulation,[],[f45,f44])).

fof(f44,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f19])).

fof(f45,plain,(
    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f19])).

fof(f687,plain,
    ( ! [X0] :
        ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),sK5)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X0) )
    | ~ spl7_13
    | ~ spl7_15
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f686,f46])).

fof(f46,plain,(
    ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f19])).

fof(f686,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK3,X0)
        | ~ r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),sK5)
        | r1_tmap_1(sK3,sK1,sK4,sK5) )
    | ~ spl7_13
    | ~ spl7_15
    | ~ spl7_16 ),
    inference(resolution,[],[f681,f90])).

fof(f90,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f43,f44])).

fof(f43,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f19])).

fof(f681,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK2))
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK3,X0)
        | ~ r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),X1)
        | r1_tmap_1(sK3,sK1,sK4,X1) )
    | ~ spl7_13
    | ~ spl7_15
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f680,f389])).

fof(f389,plain,
    ( m1_pre_topc(sK2,sK3)
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f388])).

fof(f388,plain,
    ( spl7_16
  <=> m1_pre_topc(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f680,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK2,sK3)
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | ~ r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),X1)
        | r1_tmap_1(sK3,sK1,sK4,X1) )
    | ~ spl7_13
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f679,f54])).

fof(f54,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f679,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(sK2)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK2,sK3)
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | ~ r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),X1)
        | r1_tmap_1(sK3,sK1,sK4,X1) )
    | ~ spl7_13
    | ~ spl7_15 ),
    inference(duplicate_literal_removal,[],[f677])).

fof(f677,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(sK2)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK2,sK3)
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | ~ r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),X1)
        | r1_tmap_1(sK3,sK1,sK4,X1) )
    | ~ spl7_13
    | ~ spl7_15 ),
    inference(resolution,[],[f676,f386])).

fof(f386,plain,
    ( v1_tsep_1(sK2,sK3)
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f384])).

fof(f384,plain,
    ( spl7_15
  <=> v1_tsep_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f676,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_tsep_1(X1,sK3)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(X2,u1_struct_0(sK2))
        | ~ m1_subset_1(X2,u1_struct_0(X1))
        | ~ r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),X2)
        | r1_tmap_1(sK3,sK1,sK4,X2) )
    | ~ spl7_13 ),
    inference(subsumption_resolution,[],[f675,f372])).

fof(f372,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ spl7_13 ),
    inference(backward_demodulation,[],[f50,f348])).

fof(f348,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK3)
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f346])).

fof(f346,plain,
    ( spl7_13
  <=> u1_struct_0(sK2) = u1_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f50,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f19])).

fof(f675,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ v1_tsep_1(X1,sK3)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(X2,u1_struct_0(sK2))
        | ~ m1_subset_1(X2,u1_struct_0(X1))
        | ~ r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),X2)
        | r1_tmap_1(sK3,sK1,sK4,X2) )
    | ~ spl7_13 ),
    inference(subsumption_resolution,[],[f674,f58])).

fof(f58,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f674,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ v1_tsep_1(X1,sK3)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(X2,u1_struct_0(sK2))
        | ~ m1_subset_1(X2,u1_struct_0(X1))
        | ~ r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),X2)
        | r1_tmap_1(sK3,sK1,sK4,X2) )
    | ~ spl7_13 ),
    inference(subsumption_resolution,[],[f673,f57])).

fof(f57,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f673,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ v1_tsep_1(X1,sK3)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(X2,u1_struct_0(sK2))
        | ~ m1_subset_1(X2,u1_struct_0(X1))
        | ~ r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),X2)
        | r1_tmap_1(sK3,sK1,sK4,X2) )
    | ~ spl7_13 ),
    inference(subsumption_resolution,[],[f671,f56])).

fof(f56,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f671,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_pre_topc(X0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ v1_tsep_1(X1,sK3)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(X2,u1_struct_0(sK2))
        | ~ m1_subset_1(X2,u1_struct_0(X1))
        | ~ r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),X2)
        | r1_tmap_1(sK3,sK1,sK4,X2) )
    | ~ spl7_13 ),
    inference(resolution,[],[f636,f371])).

fof(f371,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ spl7_13 ),
    inference(backward_demodulation,[],[f49,f348])).

fof(f49,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f636,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v1_tsep_1(X2,sK3)
        | ~ m1_pre_topc(X2,sK3)
        | ~ m1_subset_1(X3,u1_struct_0(sK2))
        | ~ m1_subset_1(X3,u1_struct_0(X2))
        | ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,sK3,X2,sK4),X3)
        | r1_tmap_1(sK3,X0,sK4,X3) )
    | ~ spl7_13 ),
    inference(subsumption_resolution,[],[f629,f52])).

fof(f52,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f629,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X2)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v1_tsep_1(X2,sK3)
        | ~ m1_pre_topc(X2,sK3)
        | ~ m1_subset_1(X3,u1_struct_0(sK2))
        | ~ m1_subset_1(X3,u1_struct_0(X2))
        | ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,sK3,X2,sK4),X3)
        | r1_tmap_1(sK3,X0,sK4,X3) )
    | ~ spl7_13 ),
    inference(superposition,[],[f627,f348])).

fof(f627,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_tsep_1(X2,X3)
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X2))
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X4)
      | r1_tmap_1(X3,X1,sK4,X4) ) ),
    inference(subsumption_resolution,[],[f626,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X1)
      | m1_pre_topc(X2,X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tsep_1)).

fof(f626,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X0)
      | ~ v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_tsep_1(X2,X3)
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X2))
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X4)
      | r1_tmap_1(X3,X1,sK4,X4) ) ),
    inference(resolution,[],[f84,f48])).

fof(f48,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f19])).

fof(f84,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X0)
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_tsep_1(X2,X3)
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
      | r1_tmap_1(X3,X1,X4,X6) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_tsep_1(X2,X3)
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | X5 != X6
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
      | r1_tmap_1(X3,X1,X4,X5) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X3,X1,X4,X5)
                              <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) )
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X2)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ v1_tsep_1(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
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
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X3,X1,X4,X5)
                              <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) )
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X2)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ v1_tsep_1(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
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
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( ( m1_pre_topc(X2,X3)
                          & v1_tsep_1(X2,X3) )
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X2))
                               => ( X5 = X6
                                 => ( r1_tmap_1(X3,X1,X4,X5)
                                  <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_tmap_1)).

fof(f394,plain,(
    spl7_16 ),
    inference(avatar_contradiction_clause,[],[f393])).

fof(f393,plain,
    ( $false
    | spl7_16 ),
    inference(subsumption_resolution,[],[f392,f106])).

fof(f106,plain,(
    m1_pre_topc(sK2,sK2) ),
    inference(resolution,[],[f101,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f101,plain,(
    l1_pre_topc(sK2) ),
    inference(resolution,[],[f98,f55])).

fof(f55,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f98,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,sK0)
      | l1_pre_topc(X1) ) ),
    inference(resolution,[],[f67,f61])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f392,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | spl7_16 ),
    inference(resolution,[],[f390,f357])).

fof(f357,plain,(
    ! [X1] :
      ( m1_pre_topc(X1,sK3)
      | ~ m1_pre_topc(X1,sK2) ) ),
    inference(subsumption_resolution,[],[f356,f100])).

fof(f100,plain,(
    l1_pre_topc(sK3) ),
    inference(resolution,[],[f98,f53])).

fof(f356,plain,(
    ! [X1] :
      ( ~ l1_pre_topc(sK3)
      | ~ m1_pre_topc(X1,sK2)
      | m1_pre_topc(X1,sK3) ) ),
    inference(trivial_inequality_removal,[],[f355])).

fof(f355,plain,(
    ! [X1] :
      ( sK3 != sK3
      | ~ l1_pre_topc(sK3)
      | ~ m1_pre_topc(X1,sK2)
      | m1_pre_topc(X1,sK3) ) ),
    inference(superposition,[],[f329,f175])).

fof(f175,plain,(
    sK3 = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) ),
    inference(subsumption_resolution,[],[f171,f100])).

fof(f171,plain,
    ( ~ l1_pre_topc(sK3)
    | sK3 = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) ),
    inference(resolution,[],[f65,f169])).

fof(f169,plain,(
    v1_pre_topc(sK3) ),
    inference(forward_demodulation,[],[f168,f51])).

fof(f51,plain,(
    sK3 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f19])).

fof(f168,plain,(
    v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(subsumption_resolution,[],[f164,f101])).

fof(f164,plain,
    ( ~ l1_pre_topc(sK2)
    | v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(resolution,[],[f72,f54])).

fof(f72,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & ~ v2_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & ~ v2_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & ~ v2_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_pre_topc)).

fof(f65,plain,(
    ! [X0] :
      ( ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(f329,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK3
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,sK2)
      | m1_pre_topc(X1,X0) ) ),
    inference(subsumption_resolution,[],[f323,f101])).

fof(f323,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK3
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(sK2)
      | ~ m1_pre_topc(X1,sK2)
      | m1_pre_topc(X1,X0) ) ),
    inference(superposition,[],[f320,f51])).

fof(f320,plain,(
    ! [X2,X0,X1] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X2)
      | ~ m1_pre_topc(X1,X2)
      | m1_pre_topc(X1,X0) ) ),
    inference(subsumption_resolution,[],[f313,f67])).

fof(f313,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
      | ~ l1_pre_topc(X2)
      | ~ m1_pre_topc(X1,X2)
      | m1_pre_topc(X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f312])).

fof(f312,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
      | ~ l1_pre_topc(X2)
      | ~ m1_pre_topc(X1,X2)
      | m1_pre_topc(X1,X0) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X2)
      | ~ l1_pre_topc(X3)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X2,X0)
      | m1_pre_topc(X3,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( m1_pre_topc(X3,X1)
                  | ~ m1_pre_topc(X2,X0)
                  | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                  | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  | ~ l1_pre_topc(X3) )
              | ~ l1_pre_topc(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( m1_pre_topc(X3,X1)
                  | ~ m1_pre_topc(X2,X0)
                  | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                  | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  | ~ l1_pre_topc(X3) )
              | ~ l1_pre_topc(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( l1_pre_topc(X2)
             => ! [X3] :
                  ( l1_pre_topc(X3)
                 => ( ( m1_pre_topc(X2,X0)
                      & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                      & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                   => m1_pre_topc(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_pre_topc)).

fof(f390,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | spl7_16 ),
    inference(avatar_component_clause,[],[f388])).

fof(f391,plain,
    ( spl7_15
    | ~ spl7_16
    | ~ spl7_4
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f382,f346,f137,f388,f384])).

fof(f137,plain,
    ( spl7_4
  <=> v3_pre_topc(u1_struct_0(sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f382,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | v1_tsep_1(sK2,sK3)
    | ~ spl7_4
    | ~ spl7_13 ),
    inference(resolution,[],[f374,f214])).

fof(f214,plain,(
    ! [X3] :
      ( ~ v3_pre_topc(u1_struct_0(X3),sK3)
      | ~ m1_pre_topc(X3,sK3)
      | v1_tsep_1(X3,sK3) ) ),
    inference(subsumption_resolution,[],[f210,f100])).

fof(f210,plain,(
    ! [X3] :
      ( ~ l1_pre_topc(sK3)
      | ~ m1_pre_topc(X3,sK3)
      | ~ v3_pre_topc(u1_struct_0(X3),sK3)
      | v1_tsep_1(X3,sK3) ) ),
    inference(resolution,[],[f92,f146])).

fof(f146,plain,(
    v2_pre_topc(sK3) ),
    inference(resolution,[],[f144,f53])).

fof(f144,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,sK0)
      | v2_pre_topc(X1) ) ),
    inference(subsumption_resolution,[],[f142,f61])).

fof(f142,plain,(
    ! [X1] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_pre_topc(X1,sK0)
      | v2_pre_topc(X1) ) ),
    inference(resolution,[],[f74,f60])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | v1_tsep_1(X1,X0) ) ),
    inference(subsumption_resolution,[],[f85,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | v1_tsep_1(X1,X0) ) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X2
      | ~ v3_pre_topc(X2,X0)
      | v1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> v3_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> v3_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                <=> v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tsep_1)).

fof(f374,plain,
    ( v3_pre_topc(u1_struct_0(sK2),sK3)
    | ~ spl7_4
    | ~ spl7_13 ),
    inference(backward_demodulation,[],[f139,f348])).

fof(f139,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK3)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f137])).

fof(f369,plain,(
    spl7_14 ),
    inference(avatar_contradiction_clause,[],[f368])).

fof(f368,plain,
    ( $false
    | spl7_14 ),
    inference(subsumption_resolution,[],[f366,f352])).

fof(f352,plain,
    ( ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3))
    | spl7_14 ),
    inference(avatar_component_clause,[],[f350])).

fof(f350,plain,
    ( spl7_14
  <=> r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f366,plain,(
    r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(resolution,[],[f363,f106])).

fof(f363,plain,(
    ! [X7] :
      ( ~ m1_pre_topc(X7,sK2)
      | r1_tarski(u1_struct_0(X7),u1_struct_0(sK3)) ) ),
    inference(resolution,[],[f357,f251])).

fof(f251,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK3)
      | r1_tarski(u1_struct_0(X0),u1_struct_0(sK3)) ) ),
    inference(resolution,[],[f247,f53])).

fof(f247,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK0)
      | ~ m1_pre_topc(X1,X0)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f243,f61])).

fof(f243,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_pre_topc(X0,sK0)
      | ~ m1_pre_topc(X1,X0)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ),
    inference(resolution,[],[f91,f60])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X2)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) ),
    inference(subsumption_resolution,[],[f76,f75])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X2)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).

fof(f353,plain,
    ( spl7_13
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f344,f350,f346])).

fof(f344,plain,
    ( ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3))
    | u1_struct_0(sK2) = u1_struct_0(sK3) ),
    inference(resolution,[],[f341,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f341,plain,(
    r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2)) ),
    inference(resolution,[],[f335,f252])).

fof(f252,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,sK2)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(sK2)) ) ),
    inference(resolution,[],[f247,f55])).

fof(f335,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(resolution,[],[f334,f104])).

fof(f104,plain,(
    m1_pre_topc(sK3,sK3) ),
    inference(resolution,[],[f100,f64])).

fof(f334,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,sK3)
      | m1_pre_topc(X1,sK2) ) ),
    inference(subsumption_resolution,[],[f333,f100])).

fof(f333,plain,(
    ! [X1] :
      ( ~ l1_pre_topc(sK3)
      | ~ m1_pre_topc(X1,sK3)
      | m1_pre_topc(X1,sK2) ) ),
    inference(trivial_inequality_removal,[],[f332])).

fof(f332,plain,(
    ! [X1] :
      ( sK3 != sK3
      | ~ l1_pre_topc(sK3)
      | ~ m1_pre_topc(X1,sK3)
      | m1_pre_topc(X1,sK2) ) ),
    inference(superposition,[],[f327,f175])).

fof(f327,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK3
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | m1_pre_topc(X1,sK2) ) ),
    inference(subsumption_resolution,[],[f321,f101])).

fof(f321,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK3
      | ~ l1_pre_topc(sK2)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | m1_pre_topc(X1,sK2) ) ),
    inference(superposition,[],[f320,f51])).

fof(f150,plain,(
    spl7_3 ),
    inference(avatar_contradiction_clause,[],[f149])).

fof(f149,plain,
    ( $false
    | spl7_3 ),
    inference(subsumption_resolution,[],[f146,f135])).

fof(f135,plain,
    ( ~ v2_pre_topc(sK3)
    | spl7_3 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl7_3
  <=> v2_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f140,plain,
    ( ~ spl7_3
    | spl7_4 ),
    inference(avatar_split_clause,[],[f131,f137,f133])).

fof(f131,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f116,f100])).

% (12692)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
fof(f116,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(superposition,[],[f73,f112])).

fof(f112,plain,(
    u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(resolution,[],[f96,f100])).

fof(f96,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(resolution,[],[f62,f63])).

fof(f63,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f62,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f73,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:52:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (12690)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.50  % (12708)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.50  % (12700)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (12687)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.51  % (12706)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.51  % (12690)Refutation not found, incomplete strategy% (12690)------------------------------
% 0.21/0.51  % (12690)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (12685)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.51  % (12704)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.51  % (12698)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.51  % (12699)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (12690)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (12690)Memory used [KB]: 6268
% 0.21/0.51  % (12696)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.51  % (12690)Time elapsed: 0.096 s
% 0.21/0.51  % (12690)------------------------------
% 0.21/0.51  % (12690)------------------------------
% 0.21/0.52  % (12709)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.52  % (12710)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.52  % (12708)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f694,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f140,f150,f353,f369,f391,f394,f693])).
% 0.21/0.52  fof(f693,plain,(
% 0.21/0.52    ~spl7_13 | ~spl7_15 | ~spl7_16),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f692])).
% 0.21/0.52  fof(f692,plain,(
% 0.21/0.52    $false | (~spl7_13 | ~spl7_15 | ~spl7_16)),
% 0.21/0.52    inference(subsumption_resolution,[],[f691,f59])).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    ~v2_struct_0(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X3,X1,X4,X5) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f17])).
% 0.21/0.52  fof(f17,negated_conjecture,(
% 0.21/0.52    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 0.21/0.52    inference(negated_conjecture,[],[f16])).
% 0.21/0.52  fof(f16,conjecture,(
% 0.21/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tmap_1)).
% 0.21/0.52  fof(f691,plain,(
% 0.21/0.52    v2_struct_0(sK0) | (~spl7_13 | ~spl7_15 | ~spl7_16)),
% 0.21/0.52    inference(subsumption_resolution,[],[f690,f53])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    m1_pre_topc(sK3,sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f690,plain,(
% 0.21/0.52    ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK0) | (~spl7_13 | ~spl7_15 | ~spl7_16)),
% 0.21/0.52    inference(subsumption_resolution,[],[f689,f61])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    l1_pre_topc(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f689,plain,(
% 0.21/0.52    ~l1_pre_topc(sK0) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK0) | (~spl7_13 | ~spl7_15 | ~spl7_16)),
% 0.21/0.52    inference(subsumption_resolution,[],[f688,f60])).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    v2_pre_topc(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f688,plain,(
% 0.21/0.52    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK0) | (~spl7_13 | ~spl7_15 | ~spl7_16)),
% 0.21/0.52    inference(resolution,[],[f687,f89])).
% 0.21/0.52  fof(f89,plain,(
% 0.21/0.52    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)),
% 0.21/0.52    inference(backward_demodulation,[],[f45,f44])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    sK5 = sK6),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f687,plain,(
% 0.21/0.52    ( ! [X0] : (~r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),sK5) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X0)) ) | (~spl7_13 | ~spl7_15 | ~spl7_16)),
% 0.21/0.52    inference(subsumption_resolution,[],[f686,f46])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    ~r1_tmap_1(sK3,sK1,sK4,sK5)),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f686,plain,(
% 0.21/0.52    ( ! [X0] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK3,X0) | ~r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),sK5) | r1_tmap_1(sK3,sK1,sK4,sK5)) ) | (~spl7_13 | ~spl7_15 | ~spl7_16)),
% 0.21/0.52    inference(resolution,[],[f681,f90])).
% 0.21/0.52  fof(f90,plain,(
% 0.21/0.52    m1_subset_1(sK5,u1_struct_0(sK2))),
% 0.21/0.52    inference(forward_demodulation,[],[f43,f44])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    m1_subset_1(sK6,u1_struct_0(sK2))),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f681,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(sK2)) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK3,X0) | ~r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),X1) | r1_tmap_1(sK3,sK1,sK4,X1)) ) | (~spl7_13 | ~spl7_15 | ~spl7_16)),
% 0.21/0.52    inference(subsumption_resolution,[],[f680,f389])).
% 0.21/0.52  fof(f389,plain,(
% 0.21/0.52    m1_pre_topc(sK2,sK3) | ~spl7_16),
% 0.21/0.52    inference(avatar_component_clause,[],[f388])).
% 0.21/0.52  fof(f388,plain,(
% 0.21/0.52    spl7_16 <=> m1_pre_topc(sK2,sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 0.21/0.52  fof(f680,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_pre_topc(sK3,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(X1,u1_struct_0(sK2)) | ~r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),X1) | r1_tmap_1(sK3,sK1,sK4,X1)) ) | (~spl7_13 | ~spl7_15)),
% 0.21/0.52    inference(subsumption_resolution,[],[f679,f54])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    ~v2_struct_0(sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f679,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v2_struct_0(sK2) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(X1,u1_struct_0(sK2)) | ~r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),X1) | r1_tmap_1(sK3,sK1,sK4,X1)) ) | (~spl7_13 | ~spl7_15)),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f677])).
% 0.21/0.52  fof(f677,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v2_struct_0(sK2) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(X1,u1_struct_0(sK2)) | ~m1_subset_1(X1,u1_struct_0(sK2)) | ~r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),X1) | r1_tmap_1(sK3,sK1,sK4,X1)) ) | (~spl7_13 | ~spl7_15)),
% 0.21/0.52    inference(resolution,[],[f676,f386])).
% 0.21/0.52  fof(f386,plain,(
% 0.21/0.52    v1_tsep_1(sK2,sK3) | ~spl7_15),
% 0.21/0.52    inference(avatar_component_clause,[],[f384])).
% 0.21/0.52  fof(f384,plain,(
% 0.21/0.52    spl7_15 <=> v1_tsep_1(sK2,sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 0.21/0.52  fof(f676,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~v1_tsep_1(X1,sK3) | v2_struct_0(X1) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(X2,u1_struct_0(sK2)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),X2) | r1_tmap_1(sK3,sK1,sK4,X2)) ) | ~spl7_13),
% 0.21/0.52    inference(subsumption_resolution,[],[f675,f372])).
% 0.21/0.52  fof(f372,plain,(
% 0.21/0.52    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~spl7_13),
% 0.21/0.52    inference(backward_demodulation,[],[f50,f348])).
% 0.21/0.52  fof(f348,plain,(
% 0.21/0.52    u1_struct_0(sK2) = u1_struct_0(sK3) | ~spl7_13),
% 0.21/0.52    inference(avatar_component_clause,[],[f346])).
% 0.21/0.52  fof(f346,plain,(
% 0.21/0.52    spl7_13 <=> u1_struct_0(sK2) = u1_struct_0(sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f675,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_tsep_1(X1,sK3) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(X2,u1_struct_0(sK2)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),X2) | r1_tmap_1(sK3,sK1,sK4,X2)) ) | ~spl7_13),
% 0.21/0.52    inference(subsumption_resolution,[],[f674,f58])).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    l1_pre_topc(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f674,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~l1_pre_topc(sK1) | v2_struct_0(X1) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_tsep_1(X1,sK3) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(X2,u1_struct_0(sK2)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),X2) | r1_tmap_1(sK3,sK1,sK4,X2)) ) | ~spl7_13),
% 0.21/0.52    inference(subsumption_resolution,[],[f673,f57])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    v2_pre_topc(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f673,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X1) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_tsep_1(X1,sK3) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(X2,u1_struct_0(sK2)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),X2) | r1_tmap_1(sK3,sK1,sK4,X2)) ) | ~spl7_13),
% 0.21/0.52    inference(subsumption_resolution,[],[f671,f56])).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    ~v2_struct_0(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f671,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X1) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_tsep_1(X1,sK3) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(X2,u1_struct_0(sK2)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),X2) | r1_tmap_1(sK3,sK1,sK4,X2)) ) | ~spl7_13),
% 0.21/0.52    inference(resolution,[],[f636,f371])).
% 0.21/0.52  fof(f371,plain,(
% 0.21/0.52    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~spl7_13),
% 0.21/0.52    inference(backward_demodulation,[],[f49,f348])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f636,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(X0)) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X2) | ~m1_pre_topc(sK3,X1) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~v1_tsep_1(X2,sK3) | ~m1_pre_topc(X2,sK3) | ~m1_subset_1(X3,u1_struct_0(sK2)) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,sK3,X2,sK4),X3) | r1_tmap_1(sK3,X0,sK4,X3)) ) | ~spl7_13),
% 0.21/0.52    inference(subsumption_resolution,[],[f629,f52])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    ~v2_struct_0(sK3)),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f629,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(X0)) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X2) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,X1) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~v1_tsep_1(X2,sK3) | ~m1_pre_topc(X2,sK3) | ~m1_subset_1(X3,u1_struct_0(sK2)) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,sK3,X2,sK4),X3) | r1_tmap_1(sK3,X0,sK4,X3)) ) | ~spl7_13),
% 0.21/0.52    inference(superposition,[],[f627,f348])).
% 0.21/0.52  fof(f627,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_tsep_1(X2,X3) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X2)) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X4) | r1_tmap_1(X3,X1,sK4,X4)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f626,f75])).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X1) | m1_pre_topc(X2,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,axiom,(
% 0.21/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tsep_1)).
% 0.21/0.52  fof(f626,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X0) | ~v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_tsep_1(X2,X3) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X2)) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X4) | r1_tmap_1(X3,X1,sK4,X4)) )),
% 0.21/0.52    inference(resolution,[],[f84,f48])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    v1_funct_1(sK4)),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f84,plain,(
% 0.21/0.52    ( ! [X6,X4,X2,X0,X3,X1] : (~v1_funct_1(X4) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X0) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_tsep_1(X2,X3) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X6)) )),
% 0.21/0.52    inference(equality_resolution,[],[f69])).
% 0.21/0.52  fof(f69,plain,(
% 0.21/0.52    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_tsep_1(X2,X3) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X2)) | X5 != X6 | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X5)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6) | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | (~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,axiom,(
% 0.21/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)))))))))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_tmap_1)).
% 0.21/0.52  fof(f394,plain,(
% 0.21/0.52    spl7_16),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f393])).
% 0.21/0.52  fof(f393,plain,(
% 0.21/0.52    $false | spl7_16),
% 0.21/0.52    inference(subsumption_resolution,[],[f392,f106])).
% 0.21/0.52  fof(f106,plain,(
% 0.21/0.52    m1_pre_topc(sK2,sK2)),
% 0.21/0.52    inference(resolution,[],[f101,f64])).
% 0.21/0.52  fof(f64,plain,(
% 0.21/0.52    ( ! [X0] : (~l1_pre_topc(X0) | m1_pre_topc(X0,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).
% 0.21/0.52  fof(f101,plain,(
% 0.21/0.52    l1_pre_topc(sK2)),
% 0.21/0.52    inference(resolution,[],[f98,f55])).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    m1_pre_topc(sK2,sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f98,plain,(
% 0.21/0.52    ( ! [X1] : (~m1_pre_topc(X1,sK0) | l1_pre_topc(X1)) )),
% 0.21/0.52    inference(resolution,[],[f67,f61])).
% 0.21/0.52  fof(f67,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.52  fof(f392,plain,(
% 0.21/0.52    ~m1_pre_topc(sK2,sK2) | spl7_16),
% 0.21/0.52    inference(resolution,[],[f390,f357])).
% 0.21/0.52  fof(f357,plain,(
% 0.21/0.52    ( ! [X1] : (m1_pre_topc(X1,sK3) | ~m1_pre_topc(X1,sK2)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f356,f100])).
% 0.21/0.52  fof(f100,plain,(
% 0.21/0.52    l1_pre_topc(sK3)),
% 0.21/0.52    inference(resolution,[],[f98,f53])).
% 0.21/0.52  fof(f356,plain,(
% 0.21/0.52    ( ! [X1] : (~l1_pre_topc(sK3) | ~m1_pre_topc(X1,sK2) | m1_pre_topc(X1,sK3)) )),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f355])).
% 0.21/0.52  fof(f355,plain,(
% 0.21/0.52    ( ! [X1] : (sK3 != sK3 | ~l1_pre_topc(sK3) | ~m1_pre_topc(X1,sK2) | m1_pre_topc(X1,sK3)) )),
% 0.21/0.52    inference(superposition,[],[f329,f175])).
% 0.21/0.52  fof(f175,plain,(
% 0.21/0.52    sK3 = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),
% 0.21/0.52    inference(subsumption_resolution,[],[f171,f100])).
% 0.21/0.52  fof(f171,plain,(
% 0.21/0.52    ~l1_pre_topc(sK3) | sK3 = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),
% 0.21/0.52    inference(resolution,[],[f65,f169])).
% 0.21/0.52  fof(f169,plain,(
% 0.21/0.52    v1_pre_topc(sK3)),
% 0.21/0.52    inference(forward_demodulation,[],[f168,f51])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    sK3 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f168,plain,(
% 0.21/0.52    v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))),
% 0.21/0.52    inference(subsumption_resolution,[],[f164,f101])).
% 0.21/0.52  fof(f164,plain,(
% 0.21/0.52    ~l1_pre_topc(sK2) | v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))),
% 0.21/0.52    inference(resolution,[],[f72,f54])).
% 0.21/0.52  fof(f72,plain,(
% 0.21/0.52    ( ! [X0] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ! [X0] : ((v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & ~v2_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ! [X0] : ((v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & ~v2_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & ~v2_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_pre_topc)).
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_pre_topc(X0) | ~l1_pre_topc(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).
% 0.21/0.52  fof(f329,plain,(
% 0.21/0.52    ( ! [X0,X1] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK3 | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,sK2) | m1_pre_topc(X1,X0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f323,f101])).
% 0.21/0.52  fof(f323,plain,(
% 0.21/0.52    ( ! [X0,X1] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK3 | ~l1_pre_topc(X0) | ~l1_pre_topc(sK2) | ~m1_pre_topc(X1,sK2) | m1_pre_topc(X1,X0)) )),
% 0.21/0.52    inference(superposition,[],[f320,f51])).
% 0.21/0.52  fof(f320,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) | ~l1_pre_topc(X0) | ~l1_pre_topc(X2) | ~m1_pre_topc(X1,X2) | m1_pre_topc(X1,X0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f313,f67])).
% 0.21/0.52  fof(f313,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~l1_pre_topc(X1) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) | ~l1_pre_topc(X2) | ~m1_pre_topc(X1,X2) | m1_pre_topc(X1,X0)) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f312])).
% 0.21/0.52  fof(f312,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~l1_pre_topc(X1) | ~l1_pre_topc(X1) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) | ~l1_pre_topc(X2) | ~m1_pre_topc(X1,X2) | m1_pre_topc(X1,X0)) )),
% 0.21/0.52    inference(equality_resolution,[],[f66])).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) | ~l1_pre_topc(X1) | ~l1_pre_topc(X2) | ~l1_pre_topc(X3) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~m1_pre_topc(X2,X0) | m1_pre_topc(X3,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (m1_pre_topc(X3,X1) | ~m1_pre_topc(X2,X0) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | ~l1_pre_topc(X3)) | ~l1_pre_topc(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((m1_pre_topc(X3,X1) | (~m1_pre_topc(X2,X0) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X3)) | ~l1_pre_topc(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (l1_pre_topc(X2) => ! [X3] : (l1_pre_topc(X3) => ((m1_pre_topc(X2,X0) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => m1_pre_topc(X3,X1))))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_pre_topc)).
% 0.21/0.52  fof(f390,plain,(
% 0.21/0.52    ~m1_pre_topc(sK2,sK3) | spl7_16),
% 0.21/0.52    inference(avatar_component_clause,[],[f388])).
% 0.21/0.52  fof(f391,plain,(
% 0.21/0.52    spl7_15 | ~spl7_16 | ~spl7_4 | ~spl7_13),
% 0.21/0.52    inference(avatar_split_clause,[],[f382,f346,f137,f388,f384])).
% 0.21/0.52  fof(f137,plain,(
% 0.21/0.52    spl7_4 <=> v3_pre_topc(u1_struct_0(sK3),sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.21/0.52  fof(f382,plain,(
% 0.21/0.52    ~m1_pre_topc(sK2,sK3) | v1_tsep_1(sK2,sK3) | (~spl7_4 | ~spl7_13)),
% 0.21/0.52    inference(resolution,[],[f374,f214])).
% 0.21/0.52  fof(f214,plain,(
% 0.21/0.52    ( ! [X3] : (~v3_pre_topc(u1_struct_0(X3),sK3) | ~m1_pre_topc(X3,sK3) | v1_tsep_1(X3,sK3)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f210,f100])).
% 0.21/0.52  fof(f210,plain,(
% 0.21/0.52    ( ! [X3] : (~l1_pre_topc(sK3) | ~m1_pre_topc(X3,sK3) | ~v3_pre_topc(u1_struct_0(X3),sK3) | v1_tsep_1(X3,sK3)) )),
% 0.21/0.52    inference(resolution,[],[f92,f146])).
% 0.21/0.52  fof(f146,plain,(
% 0.21/0.52    v2_pre_topc(sK3)),
% 0.21/0.52    inference(resolution,[],[f144,f53])).
% 0.21/0.52  fof(f144,plain,(
% 0.21/0.52    ( ! [X1] : (~m1_pre_topc(X1,sK0) | v2_pre_topc(X1)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f142,f61])).
% 0.21/0.52  fof(f142,plain,(
% 0.21/0.52    ( ! [X1] : (~l1_pre_topc(sK0) | ~m1_pre_topc(X1,sK0) | v2_pre_topc(X1)) )),
% 0.21/0.52    inference(resolution,[],[f74,f60])).
% 0.21/0.52  fof(f74,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_pre_topc(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f36])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).
% 0.21/0.52  fof(f92,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v3_pre_topc(u1_struct_0(X1),X0) | v1_tsep_1(X1,X0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f85,f68])).
% 0.21/0.52  fof(f68,plain,(
% 0.21/0.52    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.21/0.52  fof(f85,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(u1_struct_0(X1),X0) | v1_tsep_1(X1,X0)) )),
% 0.21/0.52    inference(equality_resolution,[],[f79])).
% 0.21/0.52  fof(f79,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X1) != X2 | ~v3_pre_topc(X2,X0) | v1_tsep_1(X1,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f42])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f41])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,axiom,(
% 0.21/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tsep_1)).
% 0.21/0.52  fof(f374,plain,(
% 0.21/0.52    v3_pre_topc(u1_struct_0(sK2),sK3) | (~spl7_4 | ~spl7_13)),
% 0.21/0.52    inference(backward_demodulation,[],[f139,f348])).
% 0.21/0.52  fof(f139,plain,(
% 0.21/0.52    v3_pre_topc(u1_struct_0(sK3),sK3) | ~spl7_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f137])).
% 0.21/0.52  fof(f369,plain,(
% 0.21/0.52    spl7_14),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f368])).
% 0.21/0.52  fof(f368,plain,(
% 0.21/0.52    $false | spl7_14),
% 0.21/0.52    inference(subsumption_resolution,[],[f366,f352])).
% 0.21/0.52  fof(f352,plain,(
% 0.21/0.52    ~r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) | spl7_14),
% 0.21/0.52    inference(avatar_component_clause,[],[f350])).
% 0.21/0.52  fof(f350,plain,(
% 0.21/0.52    spl7_14 <=> r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 0.21/0.52  fof(f366,plain,(
% 0.21/0.52    r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3))),
% 0.21/0.52    inference(resolution,[],[f363,f106])).
% 0.21/0.52  fof(f363,plain,(
% 0.21/0.52    ( ! [X7] : (~m1_pre_topc(X7,sK2) | r1_tarski(u1_struct_0(X7),u1_struct_0(sK3))) )),
% 0.21/0.52    inference(resolution,[],[f357,f251])).
% 0.21/0.52  fof(f251,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_pre_topc(X0,sK3) | r1_tarski(u1_struct_0(X0),u1_struct_0(sK3))) )),
% 0.21/0.52    inference(resolution,[],[f247,f53])).
% 0.21/0.52  fof(f247,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_pre_topc(X0,sK0) | ~m1_pre_topc(X1,X0) | r1_tarski(u1_struct_0(X1),u1_struct_0(X0))) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f243,f61])).
% 0.21/0.52  fof(f243,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~l1_pre_topc(sK0) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(X1,X0) | r1_tarski(u1_struct_0(X1),u1_struct_0(X0))) )),
% 0.21/0.52    inference(resolution,[],[f91,f60])).
% 0.21/0.52  fof(f91,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X2) | r1_tarski(u1_struct_0(X1),u1_struct_0(X2))) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f76,f75])).
% 0.21/0.52  fof(f76,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X2) | r1_tarski(u1_struct_0(X1),u1_struct_0(X2))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f40])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f39])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,axiom,(
% 0.21/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).
% 0.21/0.52  fof(f353,plain,(
% 0.21/0.52    spl7_13 | ~spl7_14),
% 0.21/0.52    inference(avatar_split_clause,[],[f344,f350,f346])).
% 0.21/0.52  fof(f344,plain,(
% 0.21/0.52    ~r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) | u1_struct_0(sK2) = u1_struct_0(sK3)),
% 0.21/0.52    inference(resolution,[],[f341,f82])).
% 0.21/0.52  fof(f82,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.52  fof(f341,plain,(
% 0.21/0.52    r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2))),
% 0.21/0.52    inference(resolution,[],[f335,f252])).
% 0.21/0.52  fof(f252,plain,(
% 0.21/0.52    ( ! [X1] : (~m1_pre_topc(X1,sK2) | r1_tarski(u1_struct_0(X1),u1_struct_0(sK2))) )),
% 0.21/0.52    inference(resolution,[],[f247,f55])).
% 0.21/0.52  fof(f335,plain,(
% 0.21/0.52    m1_pre_topc(sK3,sK2)),
% 0.21/0.52    inference(resolution,[],[f334,f104])).
% 0.21/0.52  fof(f104,plain,(
% 0.21/0.52    m1_pre_topc(sK3,sK3)),
% 0.21/0.52    inference(resolution,[],[f100,f64])).
% 0.21/0.52  fof(f334,plain,(
% 0.21/0.52    ( ! [X1] : (~m1_pre_topc(X1,sK3) | m1_pre_topc(X1,sK2)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f333,f100])).
% 0.21/0.52  fof(f333,plain,(
% 0.21/0.52    ( ! [X1] : (~l1_pre_topc(sK3) | ~m1_pre_topc(X1,sK3) | m1_pre_topc(X1,sK2)) )),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f332])).
% 0.21/0.52  fof(f332,plain,(
% 0.21/0.52    ( ! [X1] : (sK3 != sK3 | ~l1_pre_topc(sK3) | ~m1_pre_topc(X1,sK3) | m1_pre_topc(X1,sK2)) )),
% 0.21/0.52    inference(superposition,[],[f327,f175])).
% 0.21/0.52  fof(f327,plain,(
% 0.21/0.52    ( ! [X0,X1] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK3 | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | m1_pre_topc(X1,sK2)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f321,f101])).
% 0.21/0.52  fof(f321,plain,(
% 0.21/0.52    ( ! [X0,X1] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK3 | ~l1_pre_topc(sK2) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | m1_pre_topc(X1,sK2)) )),
% 0.21/0.52    inference(superposition,[],[f320,f51])).
% 0.21/0.52  fof(f150,plain,(
% 0.21/0.52    spl7_3),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f149])).
% 0.21/0.52  fof(f149,plain,(
% 0.21/0.52    $false | spl7_3),
% 0.21/0.52    inference(subsumption_resolution,[],[f146,f135])).
% 0.21/0.52  fof(f135,plain,(
% 0.21/0.52    ~v2_pre_topc(sK3) | spl7_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f133])).
% 0.21/0.52  fof(f133,plain,(
% 0.21/0.52    spl7_3 <=> v2_pre_topc(sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.21/0.52  fof(f140,plain,(
% 0.21/0.52    ~spl7_3 | spl7_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f131,f137,f133])).
% 0.21/0.52  fof(f131,plain,(
% 0.21/0.52    v3_pre_topc(u1_struct_0(sK3),sK3) | ~v2_pre_topc(sK3)),
% 0.21/0.52    inference(subsumption_resolution,[],[f116,f100])).
% 0.21/0.52  % (12692)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.52  fof(f116,plain,(
% 0.21/0.52    v3_pre_topc(u1_struct_0(sK3),sK3) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3)),
% 0.21/0.52    inference(superposition,[],[f73,f112])).
% 0.21/0.52  fof(f112,plain,(
% 0.21/0.52    u1_struct_0(sK3) = k2_struct_0(sK3)),
% 0.21/0.52    inference(resolution,[],[f96,f100])).
% 0.21/0.52  fof(f96,plain,(
% 0.21/0.52    ( ! [X0] : (~l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0)) )),
% 0.21/0.52    inference(resolution,[],[f62,f63])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.52  fof(f62,plain,(
% 0.21/0.52    ( ! [X0] : (~l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0] : (l1_struct_0(X0) => u1_struct_0(X0) = k2_struct_0(X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.52  fof(f73,plain,(
% 0.21/0.52    ( ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f34])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (12708)------------------------------
% 0.21/0.53  % (12708)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (12708)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (12708)Memory used [KB]: 11129
% 0.21/0.53  % (12708)Time elapsed: 0.055 s
% 0.21/0.53  % (12708)------------------------------
% 0.21/0.53  % (12708)------------------------------
% 0.21/0.53  % (12694)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.53  % (12681)Success in time 0.166 s
%------------------------------------------------------------------------------
