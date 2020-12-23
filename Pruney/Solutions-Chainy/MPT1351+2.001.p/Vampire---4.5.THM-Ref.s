%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:41 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  201 (1033 expanded)
%              Number of leaves         :   29 ( 428 expanded)
%              Depth                    :   23
%              Number of atoms          : 1096 (10735 expanded)
%              Number of equality atoms :   95 ( 186 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f400,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f149,f154,f157,f183,f189,f193,f275,f284,f287,f290,f293,f367,f399])).

fof(f399,plain,
    ( ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_13
    | ~ spl7_15 ),
    inference(avatar_contradiction_clause,[],[f398])).

fof(f398,plain,
    ( $false
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_13
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f397,f56])).

fof(f56,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( ~ v2_connsp_1(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK6),sK3)
    & v2_connsp_1(sK6,sK4)
    & v3_tops_2(sK5,sK3,sK4)
    & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    & v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))
    & v1_funct_1(sK5)
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4)
    & ~ v2_struct_0(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f13,f39,f38,f37,f36])).

fof(f36,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ v2_connsp_1(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    & v2_connsp_1(X3,X1)
                    & v3_tops_2(X2,X0,X1)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v2_connsp_1(k8_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X2,X3),sK3)
                  & v2_connsp_1(X3,X1)
                  & v3_tops_2(X2,sK3,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ v2_connsp_1(k8_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X2,X3),sK3)
                & v2_connsp_1(X3,X1)
                & v3_tops_2(X2,sK3,X1)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ v2_connsp_1(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),X2,X3),sK3)
              & v2_connsp_1(X3,sK4)
              & v3_tops_2(X2,sK3,sK4)
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4))) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
          & v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(sK4))
          & v1_funct_1(X2) )
      & l1_pre_topc(sK4)
      & v2_pre_topc(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ v2_connsp_1(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),X2,X3),sK3)
            & v2_connsp_1(X3,sK4)
            & v3_tops_2(X2,sK3,sK4)
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4))) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
        & v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(sK4))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ~ v2_connsp_1(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X3),sK3)
          & v2_connsp_1(X3,sK4)
          & v3_tops_2(sK5,sK3,sK4)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4))) )
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
      & v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X3] :
        ( ~ v2_connsp_1(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X3),sK3)
        & v2_connsp_1(X3,sK4)
        & v3_tops_2(sK5,sK3,sK4)
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4))) )
   => ( ~ v2_connsp_1(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK6),sK3)
      & v2_connsp_1(sK6,sK4)
      & v3_tops_2(sK5,sK3,sK4)
      & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v2_connsp_1(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                  & v2_connsp_1(X3,X1)
                  & v3_tops_2(X2,X0,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v2_connsp_1(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                  & v2_connsp_1(X3,X1)
                  & v3_tops_2(X2,X0,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
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
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( ( v2_connsp_1(X3,X1)
                        & v3_tops_2(X2,X0,X1) )
                     => v2_connsp_1(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
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
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( v2_connsp_1(X3,X1)
                      & v3_tops_2(X2,X0,X1) )
                   => v2_connsp_1(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_2)).

fof(f397,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_13
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f396,f58])).

fof(f58,plain,(
    v2_connsp_1(sK6,sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f396,plain,
    ( ~ v2_connsp_1(sK6,sK4)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_13
    | ~ spl7_15 ),
    inference(resolution,[],[f395,f59])).

fof(f59,plain,(
    ~ v2_connsp_1(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK6),sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f395,plain,
    ( ! [X0] :
        ( v2_connsp_1(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0),sK3)
        | ~ v2_connsp_1(X0,sK4)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) )
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_13
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f394,f50])).

fof(f50,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f394,plain,
    ( ! [X0] :
        ( v2_connsp_1(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0),sK3)
        | ~ v2_connsp_1(X0,sK4)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
        | v2_struct_0(sK4) )
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_13
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f393,f51])).

fof(f51,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f393,plain,
    ( ! [X0] :
        ( v2_connsp_1(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0),sK3)
        | ~ v2_connsp_1(X0,sK4)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
        | ~ v2_pre_topc(sK4)
        | v2_struct_0(sK4) )
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_13
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f392,f52])).

fof(f52,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f392,plain,
    ( ! [X0] :
        ( v2_connsp_1(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0),sK3)
        | ~ v2_connsp_1(X0,sK4)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
        | ~ l1_pre_topc(sK4)
        | ~ v2_pre_topc(sK4)
        | v2_struct_0(sK4) )
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_13
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f391,f47])).

fof(f47,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f391,plain,
    ( ! [X0] :
        ( v2_connsp_1(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0),sK3)
        | ~ v2_connsp_1(X0,sK4)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(sK4)
        | ~ v2_pre_topc(sK4)
        | v2_struct_0(sK4) )
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_13
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f390,f48])).

fof(f48,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f390,plain,
    ( ! [X0] :
        ( v2_connsp_1(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0),sK3)
        | ~ v2_connsp_1(X0,sK4)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(sK4)
        | ~ v2_pre_topc(sK4)
        | v2_struct_0(sK4) )
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_13
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f389,f49])).

fof(f49,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f389,plain,
    ( ! [X0] :
        ( v2_connsp_1(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0),sK3)
        | ~ v2_connsp_1(X0,sK4)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(sK4)
        | ~ v2_pre_topc(sK4)
        | v2_struct_0(sK4) )
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_13
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f388,f223])).

fof(f223,plain,
    ( v1_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f222])).

fof(f222,plain,
    ( spl7_7
  <=> v1_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f388,plain,
    ( ! [X0] :
        ( v2_connsp_1(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0),sK3)
        | ~ v2_connsp_1(X0,sK4)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
        | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(sK4)
        | ~ v2_pre_topc(sK4)
        | v2_struct_0(sK4) )
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_13
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f387,f227])).

fof(f227,plain,
    ( v1_funct_2(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f226])).

fof(f226,plain,
    ( spl7_8
  <=> v1_funct_2(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),u1_struct_0(sK4),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f387,plain,
    ( ! [X0] :
        ( v2_connsp_1(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0),sK3)
        | ~ v2_connsp_1(X0,sK4)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
        | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),u1_struct_0(sK4),u1_struct_0(sK3))
        | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(sK4)
        | ~ v2_pre_topc(sK4)
        | v2_struct_0(sK4) )
    | ~ spl7_9
    | ~ spl7_13
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f386,f231])).

fof(f231,plain,
    ( m1_subset_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f230])).

fof(f230,plain,
    ( spl7_9
  <=> m1_subset_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f386,plain,
    ( ! [X0] :
        ( v2_connsp_1(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0),sK3)
        | ~ v2_connsp_1(X0,sK4)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
        | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
        | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),u1_struct_0(sK4),u1_struct_0(sK3))
        | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(sK4)
        | ~ v2_pre_topc(sK4)
        | v2_struct_0(sK4) )
    | ~ spl7_13
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f385,f250])).

fof(f250,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK4,sK3)
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f249])).

fof(f249,plain,
    ( spl7_13
  <=> v5_pre_topc(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f385,plain,
    ( ! [X0] :
        ( v2_connsp_1(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0),sK3)
        | ~ v2_connsp_1(X0,sK4)
        | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK4,sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
        | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
        | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),u1_struct_0(sK4),u1_struct_0(sK3))
        | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(sK4)
        | ~ v2_pre_topc(sK4)
        | v2_struct_0(sK4) )
    | ~ spl7_15 ),
    inference(duplicate_literal_removal,[],[f384])).

fof(f384,plain,
    ( ! [X0] :
        ( v2_connsp_1(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0),sK3)
        | ~ v2_connsp_1(X0,sK4)
        | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK4,sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
        | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
        | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),u1_struct_0(sK4),u1_struct_0(sK3))
        | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(sK4)
        | ~ v2_pre_topc(sK4)
        | v2_struct_0(sK4)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) )
    | ~ spl7_15 ),
    inference(superposition,[],[f75,f283])).

fof(f283,plain,
    ( ! [X0] :
        ( k7_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),X0) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) )
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f282])).

fof(f282,plain,
    ( spl7_15
  <=> ! [X0] :
        ( k7_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),X0) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_connsp_1(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
      | ~ v2_connsp_1(X3,X0)
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
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
                  ( v2_connsp_1(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                  | ~ v2_connsp_1(X3,X0)
                  | ~ v5_pre_topc(X2,X0,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
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
                  ( v2_connsp_1(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                  | ~ v2_connsp_1(X3,X0)
                  | ~ v5_pre_topc(X2,X0,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( v2_connsp_1(X3,X0)
                      & v5_pre_topc(X2,X0,X1) )
                   => v2_connsp_1(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_tops_2)).

fof(f367,plain,(
    spl7_13 ),
    inference(avatar_contradiction_clause,[],[f366])).

fof(f366,plain,
    ( $false
    | spl7_13 ),
    inference(subsumption_resolution,[],[f365,f106])).

fof(f106,plain,(
    sP0(sK3,sK4,sK5) ),
    inference(subsumption_resolution,[],[f105,f57])).

fof(f57,plain,(
    v3_tops_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f105,plain,
    ( ~ v3_tops_2(sK5,sK3,sK4)
    | sP0(sK3,sK4,sK5) ),
    inference(resolution,[],[f101,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ v3_tops_2(X0,X2,X1)
      | sP0(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( ( v3_tops_2(X0,X2,X1)
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | ~ v3_tops_2(X0,X2,X1) ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ( ( v3_tops_2(X2,X0,X1)
          | ~ sP0(X0,X1,X2) )
        & ( sP0(X0,X1,X2)
          | ~ v3_tops_2(X2,X0,X1) ) )
      | ~ sP1(X2,X1,X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ( v3_tops_2(X2,X0,X1)
      <=> sP0(X0,X1,X2) )
      | ~ sP1(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f101,plain,(
    sP1(sK5,sK4,sK3) ),
    inference(subsumption_resolution,[],[f100,f49])).

fof(f100,plain,
    ( sP1(sK5,sK4,sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f99,f52])).

fof(f99,plain,
    ( sP1(sK5,sK4,sK3)
    | ~ l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f98,f53])).

fof(f53,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f40])).

fof(f98,plain,
    ( sP1(sK5,sK4,sK3)
    | ~ v1_funct_1(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f96,f54])).

fof(f54,plain,(
    v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f40])).

fof(f96,plain,
    ( sP1(sK5,sK4,sK3)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ v1_funct_1(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK3) ),
    inference(resolution,[],[f74,f55])).

fof(f55,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) ),
    inference(cnf_transformation,[],[f40])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | sP1(X2,X1,X0)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP1(X2,X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f24,f32,f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( sP0(X0,X1,X2)
    <=> ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
        & v5_pre_topc(X2,X0,X1)
        & v2_funct_1(X2)
        & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
        & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v3_tops_2(X2,X0,X1)
              <=> ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
                  & v5_pre_topc(X2,X0,X1)
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v3_tops_2(X2,X0,X1)
              <=> ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
                  & v5_pre_topc(X2,X0,X1)
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v3_tops_2(X2,X0,X1)
              <=> ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
                  & v5_pre_topc(X2,X0,X1)
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tops_2)).

fof(f365,plain,
    ( ~ sP0(sK3,sK4,sK5)
    | spl7_13 ),
    inference(resolution,[],[f251,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
        | ~ v5_pre_topc(X2,X0,X1)
        | ~ v2_funct_1(X2)
        | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
        | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0) )
      & ( ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
          & v5_pre_topc(X2,X0,X1)
          & v2_funct_1(X2)
          & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
          & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
        | ~ v5_pre_topc(X2,X0,X1)
        | ~ v2_funct_1(X2)
        | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
        | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0) )
      & ( ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
          & v5_pre_topc(X2,X0,X1)
          & v2_funct_1(X2)
          & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
          & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f251,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK4,sK3)
    | spl7_13 ),
    inference(avatar_component_clause,[],[f249])).

fof(f293,plain,(
    spl7_9 ),
    inference(avatar_contradiction_clause,[],[f292])).

fof(f292,plain,
    ( $false
    | spl7_9 ),
    inference(subsumption_resolution,[],[f291,f87])).

fof(f87,plain,(
    sP2(u1_struct_0(sK3),u1_struct_0(sK4),sK5) ),
    inference(subsumption_resolution,[],[f86,f53])).

fof(f86,plain,
    ( sP2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)
    | ~ v1_funct_1(sK5) ),
    inference(subsumption_resolution,[],[f84,f54])).

fof(f84,plain,
    ( sP2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ v1_funct_1(sK5) ),
    inference(resolution,[],[f79,f55])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP2(X0,X1,X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( sP2(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(definition_folding,[],[f28,f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ sP2(X0,X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_2)).

fof(f291,plain,
    ( ~ sP2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)
    | spl7_9 ),
    inference(resolution,[],[f232,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ sP2(X0,X1,X2) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f232,plain,
    ( ~ m1_subset_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | spl7_9 ),
    inference(avatar_component_clause,[],[f230])).

fof(f290,plain,(
    spl7_8 ),
    inference(avatar_contradiction_clause,[],[f289])).

fof(f289,plain,
    ( $false
    | spl7_8 ),
    inference(subsumption_resolution,[],[f288,f87])).

fof(f288,plain,
    ( ~ sP2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)
    | spl7_8 ),
    inference(resolution,[],[f228,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f228,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),u1_struct_0(sK4),u1_struct_0(sK3))
    | spl7_8 ),
    inference(avatar_component_clause,[],[f226])).

fof(f287,plain,(
    spl7_7 ),
    inference(avatar_contradiction_clause,[],[f286])).

fof(f286,plain,
    ( $false
    | spl7_7 ),
    inference(subsumption_resolution,[],[f285,f87])).

fof(f285,plain,
    ( ~ sP2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)
    | spl7_7 ),
    inference(resolution,[],[f224,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_tops_2(X0,X1,X2))
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f224,plain,
    ( ~ v1_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))
    | spl7_7 ),
    inference(avatar_component_clause,[],[f222])).

fof(f284,plain,
    ( ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | spl7_15
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f280,f176,f146,f142,f138,f282,f234,f230,f226,f222])).

fof(f234,plain,
    ( spl7_10
  <=> k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) = k2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f138,plain,
    ( spl7_1
  <=> l1_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f142,plain,
    ( spl7_2
  <=> l1_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f146,plain,
    ( spl7_3
  <=> v2_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f176,plain,
    ( spl7_5
  <=> sK5 = k2_tops_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f280,plain,
    ( ! [X0] :
        ( k7_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),X0) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0)
        | k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) != k2_struct_0(sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
        | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
        | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),u1_struct_0(sK4),u1_struct_0(sK3))
        | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) )
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f279,f143])).

fof(f143,plain,
    ( l1_struct_0(sK4)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f142])).

fof(f279,plain,
    ( ! [X0] :
        ( k7_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),X0) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0)
        | k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) != k2_struct_0(sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
        | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
        | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),u1_struct_0(sK4),u1_struct_0(sK3))
        | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))
        | ~ l1_struct_0(sK4) )
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f278,f139])).

fof(f139,plain,
    ( l1_struct_0(sK3)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f138])).

fof(f278,plain,
    ( ! [X0] :
        ( k7_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),X0) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0)
        | k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) != k2_struct_0(sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
        | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
        | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),u1_struct_0(sK4),u1_struct_0(sK3))
        | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))
        | ~ l1_struct_0(sK3)
        | ~ l1_struct_0(sK4) )
    | ~ spl7_3
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f277,f148])).

fof(f148,plain,
    ( v2_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f146])).

fof(f277,plain,
    ( ! [X0] :
        ( k7_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),X0) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0)
        | ~ v2_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))
        | k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) != k2_struct_0(sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
        | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
        | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),u1_struct_0(sK4),u1_struct_0(sK3))
        | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))
        | ~ l1_struct_0(sK3)
        | ~ l1_struct_0(sK4) )
    | ~ spl7_5 ),
    inference(superposition,[],[f61,f178])).

fof(f178,plain,
    ( sK5 = k2_tops_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f176])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3)
      | ~ v2_funct_1(X2)
      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3)
                  | ~ v2_funct_1(X2)
                  | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3)
                  | ~ v2_funct_1(X2)
                  | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( v2_funct_1(X2)
                      & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
                   => k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_tops_2)).

fof(f275,plain,
    ( ~ spl7_1
    | ~ spl7_2
    | ~ spl7_6
    | spl7_10 ),
    inference(avatar_contradiction_clause,[],[f274])).

% (6109)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% (6114)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% (6126)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% (6118)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% (6125)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% (6130)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% (6115)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% (6117)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
fof(f274,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_6
    | spl7_10 ),
    inference(subsumption_resolution,[],[f273,f139])).

fof(f273,plain,
    ( ~ l1_struct_0(sK3)
    | ~ spl7_2
    | ~ spl7_6
    | spl7_10 ),
    inference(subsumption_resolution,[],[f272,f50])).

fof(f272,plain,
    ( v2_struct_0(sK4)
    | ~ l1_struct_0(sK3)
    | ~ spl7_2
    | ~ spl7_6
    | spl7_10 ),
    inference(subsumption_resolution,[],[f271,f143])).

fof(f271,plain,
    ( ~ l1_struct_0(sK4)
    | v2_struct_0(sK4)
    | ~ l1_struct_0(sK3)
    | ~ spl7_6
    | spl7_10 ),
    inference(subsumption_resolution,[],[f270,f53])).

fof(f270,plain,
    ( ~ v1_funct_1(sK5)
    | ~ l1_struct_0(sK4)
    | v2_struct_0(sK4)
    | ~ l1_struct_0(sK3)
    | ~ spl7_6
    | spl7_10 ),
    inference(subsumption_resolution,[],[f269,f54])).

fof(f269,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ v1_funct_1(sK5)
    | ~ l1_struct_0(sK4)
    | v2_struct_0(sK4)
    | ~ l1_struct_0(sK3)
    | ~ spl7_6
    | spl7_10 ),
    inference(subsumption_resolution,[],[f268,f55])).

fof(f268,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ v1_funct_1(sK5)
    | ~ l1_struct_0(sK4)
    | v2_struct_0(sK4)
    | ~ l1_struct_0(sK3)
    | ~ spl7_6
    | spl7_10 ),
    inference(subsumption_resolution,[],[f267,f181])).

fof(f181,plain,
    ( k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) = k2_struct_0(sK4)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f180])).

fof(f180,plain,
    ( spl7_6
  <=> k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) = k2_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f267,plain,
    ( k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ v1_funct_1(sK5)
    | ~ l1_struct_0(sK4)
    | v2_struct_0(sK4)
    | ~ l1_struct_0(sK3)
    | spl7_10 ),
    inference(subsumption_resolution,[],[f266,f108])).

fof(f108,plain,(
    v2_funct_1(sK5) ),
    inference(resolution,[],[f106,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | v2_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f266,plain,
    ( ~ v2_funct_1(sK5)
    | k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ v1_funct_1(sK5)
    | ~ l1_struct_0(sK4)
    | v2_struct_0(sK4)
    | ~ l1_struct_0(sK3)
    | spl7_10 ),
    inference(trivial_inequality_removal,[],[f263])).

fof(f263,plain,
    ( k2_struct_0(sK3) != k2_struct_0(sK3)
    | ~ v2_funct_1(sK5)
    | k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ v1_funct_1(sK5)
    | ~ l1_struct_0(sK4)
    | v2_struct_0(sK4)
    | ~ l1_struct_0(sK3)
    | spl7_10 ),
    inference(superposition,[],[f236,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
      | ~ v2_funct_1(X2)
      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) )
              | ~ v2_funct_1(X2)
              | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) )
              | ~ v2_funct_1(X2)
              | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( ( l1_struct_0(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
               => ( k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                  & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_2)).

fof(f236,plain,
    ( k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) != k2_struct_0(sK3)
    | spl7_10 ),
    inference(avatar_component_clause,[],[f234])).

fof(f193,plain,(
    spl7_6 ),
    inference(avatar_contradiction_clause,[],[f192])).

fof(f192,plain,
    ( $false
    | spl7_6 ),
    inference(subsumption_resolution,[],[f191,f106])).

fof(f191,plain,
    ( ~ sP0(sK3,sK4,sK5)
    | spl7_6 ),
    inference(trivial_inequality_removal,[],[f190])).

fof(f190,plain,
    ( k2_struct_0(sK4) != k2_struct_0(sK4)
    | ~ sP0(sK3,sK4,sK5)
    | spl7_6 ),
    inference(superposition,[],[f182,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f182,plain,
    ( k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK4)
    | spl7_6 ),
    inference(avatar_component_clause,[],[f180])).

fof(f189,plain,(
    spl7_4 ),
    inference(avatar_contradiction_clause,[],[f188])).

fof(f188,plain,
    ( $false
    | spl7_4 ),
    inference(subsumption_resolution,[],[f187,f87])).

fof(f187,plain,
    ( ~ sP2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)
    | spl7_4 ),
    inference(resolution,[],[f174,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( sP2(X0,X1,k2_tops_2(X1,X0,X2))
      | ~ sP2(X1,X0,X2) ) ),
    inference(subsumption_resolution,[],[f88,f76])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( sP2(X0,X1,k2_tops_2(X1,X0,X2))
      | ~ v1_funct_1(k2_tops_2(X1,X0,X2))
      | ~ sP2(X1,X0,X2) ) ),
    inference(subsumption_resolution,[],[f85,f77])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( sP2(X0,X1,k2_tops_2(X1,X0,X2))
      | ~ v1_funct_2(k2_tops_2(X1,X0,X2),X0,X1)
      | ~ v1_funct_1(k2_tops_2(X1,X0,X2))
      | ~ sP2(X1,X0,X2) ) ),
    inference(resolution,[],[f79,f78])).

fof(f174,plain,
    ( ~ sP2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))
    | spl7_4 ),
    inference(avatar_component_clause,[],[f172])).

fof(f172,plain,
    ( spl7_4
  <=> sP2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f183,plain,
    ( ~ spl7_4
    | spl7_5
    | ~ spl7_6
    | ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f170,f142,f138,f180,f176,f172])).

fof(f170,plain,
    ( k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK4)
    | sK5 = k2_tops_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))
    | ~ sP2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))
    | ~ spl7_1
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f169,f139])).

fof(f169,plain,
    ( k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK4)
    | ~ l1_struct_0(sK3)
    | sK5 = k2_tops_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))
    | ~ sP2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f168,f50])).

fof(f168,plain,
    ( k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK4)
    | v2_struct_0(sK4)
    | ~ l1_struct_0(sK3)
    | sK5 = k2_tops_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))
    | ~ sP2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f167,f143])).

fof(f167,plain,
    ( k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK4)
    | ~ l1_struct_0(sK4)
    | v2_struct_0(sK4)
    | ~ l1_struct_0(sK3)
    | sK5 = k2_tops_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))
    | ~ sP2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) ),
    inference(subsumption_resolution,[],[f166,f53])).

fof(f166,plain,
    ( k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK4)
    | ~ v1_funct_1(sK5)
    | ~ l1_struct_0(sK4)
    | v2_struct_0(sK4)
    | ~ l1_struct_0(sK3)
    | sK5 = k2_tops_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))
    | ~ sP2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) ),
    inference(subsumption_resolution,[],[f165,f54])).

fof(f165,plain,
    ( k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK4)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ v1_funct_1(sK5)
    | ~ l1_struct_0(sK4)
    | v2_struct_0(sK4)
    | ~ l1_struct_0(sK3)
    | sK5 = k2_tops_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))
    | ~ sP2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) ),
    inference(subsumption_resolution,[],[f164,f55])).

fof(f164,plain,
    ( k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ v1_funct_1(sK5)
    | ~ l1_struct_0(sK4)
    | v2_struct_0(sK4)
    | ~ l1_struct_0(sK3)
    | sK5 = k2_tops_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))
    | ~ sP2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) ),
    inference(subsumption_resolution,[],[f162,f108])).

fof(f162,plain,
    ( ~ v2_funct_1(sK5)
    | k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ v1_funct_1(sK5)
    | ~ l1_struct_0(sK4)
    | v2_struct_0(sK4)
    | ~ l1_struct_0(sK3)
    | sK5 = k2_tops_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))
    | ~ sP2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) ),
    inference(resolution,[],[f62,f120])).

fof(f120,plain,(
    ! [X0] :
      ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK4),k2_tops_2(u1_struct_0(sK4),u1_struct_0(sK3),X0),sK5)
      | sK5 = k2_tops_2(u1_struct_0(sK4),u1_struct_0(sK3),X0)
      | ~ sP2(u1_struct_0(sK4),u1_struct_0(sK3),X0) ) ),
    inference(subsumption_resolution,[],[f119,f76])).

fof(f119,plain,(
    ! [X0] :
      ( sK5 = k2_tops_2(u1_struct_0(sK4),u1_struct_0(sK3),X0)
      | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK4),k2_tops_2(u1_struct_0(sK4),u1_struct_0(sK3),X0),sK5)
      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK4),u1_struct_0(sK3),X0))
      | ~ sP2(u1_struct_0(sK4),u1_struct_0(sK3),X0) ) ),
    inference(subsumption_resolution,[],[f118,f77])).

fof(f118,plain,(
    ! [X0] :
      ( sK5 = k2_tops_2(u1_struct_0(sK4),u1_struct_0(sK3),X0)
      | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK4),k2_tops_2(u1_struct_0(sK4),u1_struct_0(sK3),X0),sK5)
      | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK4),u1_struct_0(sK3),X0),u1_struct_0(sK3),u1_struct_0(sK4))
      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK4),u1_struct_0(sK3),X0))
      | ~ sP2(u1_struct_0(sK4),u1_struct_0(sK3),X0) ) ),
    inference(resolution,[],[f114,f78])).

fof(f114,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
      | sK5 = X0
      | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK4),X0,sK5)
      | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(sK4))
      | ~ v1_funct_1(X0) ) ),
    inference(subsumption_resolution,[],[f113,f53])).

fof(f113,plain,(
    ! [X0] :
      ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK4),X0,sK5)
      | sK5 = X0
      | ~ v1_funct_1(sK5)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
      | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(sK4))
      | ~ v1_funct_1(X0) ) ),
    inference(subsumption_resolution,[],[f111,f54])).

fof(f111,plain,(
    ! [X0] :
      ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK4),X0,sK5)
      | sK5 = X0
      | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))
      | ~ v1_funct_1(sK5)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
      | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(sK4))
      | ~ v1_funct_1(X0) ) ),
    inference(resolution,[],[f80,f55])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_funct_2(X0,X1,X2,X3)
      | X2 = X3
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f30])).

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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
              | ~ v2_funct_1(X2)
              | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
              | ~ v2_funct_1(X2)
              | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( ( l1_struct_0(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
               => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tops_2)).

fof(f157,plain,(
    spl7_2 ),
    inference(avatar_contradiction_clause,[],[f156])).

fof(f156,plain,
    ( $false
    | spl7_2 ),
    inference(subsumption_resolution,[],[f155,f52])).

fof(f155,plain,
    ( ~ l1_pre_topc(sK4)
    | spl7_2 ),
    inference(resolution,[],[f144,f65])).

fof(f65,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f144,plain,
    ( ~ l1_struct_0(sK4)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f142])).

fof(f154,plain,(
    spl7_1 ),
    inference(avatar_contradiction_clause,[],[f153])).

fof(f153,plain,
    ( $false
    | spl7_1 ),
    inference(subsumption_resolution,[],[f152,f49])).

fof(f152,plain,
    ( ~ l1_pre_topc(sK3)
    | spl7_1 ),
    inference(resolution,[],[f140,f65])).

fof(f140,plain,
    ( ~ l1_struct_0(sK3)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f138])).

fof(f149,plain,
    ( ~ spl7_1
    | ~ spl7_2
    | spl7_3 ),
    inference(avatar_split_clause,[],[f136,f146,f142,f138])).

fof(f136,plain,
    ( v2_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))
    | ~ l1_struct_0(sK4)
    | ~ l1_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f135,f106])).

fof(f135,plain,
    ( v2_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))
    | ~ l1_struct_0(sK4)
    | ~ l1_struct_0(sK3)
    | ~ sP0(sK3,sK4,sK5) ),
    inference(subsumption_resolution,[],[f134,f53])).

fof(f134,plain,
    ( v2_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))
    | ~ v1_funct_1(sK5)
    | ~ l1_struct_0(sK4)
    | ~ l1_struct_0(sK3)
    | ~ sP0(sK3,sK4,sK5) ),
    inference(subsumption_resolution,[],[f132,f54])).

fof(f132,plain,
    ( v2_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ v1_funct_1(sK5)
    | ~ l1_struct_0(sK4)
    | ~ l1_struct_0(sK3)
    | ~ sP0(sK3,sK4,sK5) ),
    inference(resolution,[],[f131,f55])).

fof(f131,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0)
      | ~ sP0(X0,X1,X2) ) ),
    inference(subsumption_resolution,[],[f130,f70])).

fof(f130,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0)
      | ~ sP0(X0,X1,X2) ) ),
    inference(trivial_inequality_removal,[],[f129])).

fof(f129,plain,(
    ! [X2,X0,X1] :
      ( k2_struct_0(X1) != k2_struct_0(X1)
      | ~ v2_funct_1(X2)
      | v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0)
      | ~ sP0(X0,X1,X2) ) ),
    inference(superposition,[],[f60,f69])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
      | ~ v2_funct_1(X2)
      | v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
              | ~ v2_funct_1(X2)
              | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
              | ~ v2_funct_1(X2)
              | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
               => v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_tops_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:16:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (6124)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.50  % (6110)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.50  % (6110)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f400,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f149,f154,f157,f183,f189,f193,f275,f284,f287,f290,f293,f367,f399])).
% 0.22/0.50  fof(f399,plain,(
% 0.22/0.50    ~spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_13 | ~spl7_15),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f398])).
% 0.22/0.50  fof(f398,plain,(
% 0.22/0.50    $false | (~spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_13 | ~spl7_15)),
% 0.22/0.50    inference(subsumption_resolution,[],[f397,f56])).
% 0.22/0.50  fof(f56,plain,(
% 0.22/0.50    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))),
% 0.22/0.50    inference(cnf_transformation,[],[f40])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    (((~v2_connsp_1(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK6),sK3) & v2_connsp_1(sK6,sK4) & v3_tops_2(sK5,sK3,sK4) & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) & v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) & v1_funct_1(sK5)) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f13,f39,f38,f37,f36])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v2_connsp_1(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v2_connsp_1(X3,X1) & v3_tops_2(X2,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~v2_connsp_1(k8_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X2,X3),sK3) & v2_connsp_1(X3,X1) & v3_tops_2(X2,sK3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    ? [X1] : (? [X2] : (? [X3] : (~v2_connsp_1(k8_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X2,X3),sK3) & v2_connsp_1(X3,X1) & v3_tops_2(X2,sK3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (~v2_connsp_1(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),X2,X3),sK3) & v2_connsp_1(X3,sK4) & v3_tops_2(X2,sK3,sK4) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) & v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(sK4)) & v1_funct_1(X2)) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    ? [X2] : (? [X3] : (~v2_connsp_1(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),X2,X3),sK3) & v2_connsp_1(X3,sK4) & v3_tops_2(X2,sK3,sK4) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) & v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(sK4)) & v1_funct_1(X2)) => (? [X3] : (~v2_connsp_1(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X3),sK3) & v2_connsp_1(X3,sK4) & v3_tops_2(sK5,sK3,sK4) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) & v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) & v1_funct_1(sK5))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f39,plain,(
% 0.22/0.50    ? [X3] : (~v2_connsp_1(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X3),sK3) & v2_connsp_1(X3,sK4) & v3_tops_2(sK5,sK3,sK4) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))) => (~v2_connsp_1(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK6),sK3) & v2_connsp_1(sK6,sK4) & v3_tops_2(sK5,sK3,sK4) & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v2_connsp_1(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v2_connsp_1(X3,X1) & v3_tops_2(X2,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f12])).
% 0.22/0.50  fof(f12,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v2_connsp_1(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & (v2_connsp_1(X3,X1) & v3_tops_2(X2,X0,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,negated_conjecture,(
% 0.22/0.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v2_connsp_1(X3,X1) & v3_tops_2(X2,X0,X1)) => v2_connsp_1(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0))))))),
% 0.22/0.50    inference(negated_conjecture,[],[f10])).
% 0.22/0.50  fof(f10,conjecture,(
% 0.22/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v2_connsp_1(X3,X1) & v3_tops_2(X2,X0,X1)) => v2_connsp_1(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0))))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_2)).
% 0.22/0.50  fof(f397,plain,(
% 0.22/0.50    ~m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) | (~spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_13 | ~spl7_15)),
% 0.22/0.50    inference(subsumption_resolution,[],[f396,f58])).
% 0.22/0.50  fof(f58,plain,(
% 0.22/0.50    v2_connsp_1(sK6,sK4)),
% 0.22/0.50    inference(cnf_transformation,[],[f40])).
% 0.22/0.50  fof(f396,plain,(
% 0.22/0.50    ~v2_connsp_1(sK6,sK4) | ~m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) | (~spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_13 | ~spl7_15)),
% 0.22/0.50    inference(resolution,[],[f395,f59])).
% 0.22/0.50  fof(f59,plain,(
% 0.22/0.50    ~v2_connsp_1(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK6),sK3)),
% 0.22/0.50    inference(cnf_transformation,[],[f40])).
% 0.22/0.50  fof(f395,plain,(
% 0.22/0.50    ( ! [X0] : (v2_connsp_1(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0),sK3) | ~v2_connsp_1(X0,sK4) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))) ) | (~spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_13 | ~spl7_15)),
% 0.22/0.50    inference(subsumption_resolution,[],[f394,f50])).
% 0.22/0.50  fof(f50,plain,(
% 0.22/0.50    ~v2_struct_0(sK4)),
% 0.22/0.50    inference(cnf_transformation,[],[f40])).
% 0.22/0.50  fof(f394,plain,(
% 0.22/0.50    ( ! [X0] : (v2_connsp_1(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0),sK3) | ~v2_connsp_1(X0,sK4) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) | v2_struct_0(sK4)) ) | (~spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_13 | ~spl7_15)),
% 0.22/0.50    inference(subsumption_resolution,[],[f393,f51])).
% 0.22/0.50  fof(f51,plain,(
% 0.22/0.50    v2_pre_topc(sK4)),
% 0.22/0.50    inference(cnf_transformation,[],[f40])).
% 0.22/0.50  fof(f393,plain,(
% 0.22/0.50    ( ! [X0] : (v2_connsp_1(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0),sK3) | ~v2_connsp_1(X0,sK4) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)) ) | (~spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_13 | ~spl7_15)),
% 0.22/0.50    inference(subsumption_resolution,[],[f392,f52])).
% 0.22/0.50  fof(f52,plain,(
% 0.22/0.50    l1_pre_topc(sK4)),
% 0.22/0.50    inference(cnf_transformation,[],[f40])).
% 0.22/0.50  fof(f392,plain,(
% 0.22/0.50    ( ! [X0] : (v2_connsp_1(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0),sK3) | ~v2_connsp_1(X0,sK4) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)) ) | (~spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_13 | ~spl7_15)),
% 0.22/0.50    inference(subsumption_resolution,[],[f391,f47])).
% 0.22/0.50  fof(f47,plain,(
% 0.22/0.50    ~v2_struct_0(sK3)),
% 0.22/0.50    inference(cnf_transformation,[],[f40])).
% 0.22/0.50  fof(f391,plain,(
% 0.22/0.50    ( ! [X0] : (v2_connsp_1(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0),sK3) | ~v2_connsp_1(X0,sK4) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) | v2_struct_0(sK3) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)) ) | (~spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_13 | ~spl7_15)),
% 0.22/0.50    inference(subsumption_resolution,[],[f390,f48])).
% 0.22/0.50  fof(f48,plain,(
% 0.22/0.50    v2_pre_topc(sK3)),
% 0.22/0.50    inference(cnf_transformation,[],[f40])).
% 0.22/0.50  fof(f390,plain,(
% 0.22/0.50    ( ! [X0] : (v2_connsp_1(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0),sK3) | ~v2_connsp_1(X0,sK4) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)) ) | (~spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_13 | ~spl7_15)),
% 0.22/0.50    inference(subsumption_resolution,[],[f389,f49])).
% 0.22/0.50  fof(f49,plain,(
% 0.22/0.50    l1_pre_topc(sK3)),
% 0.22/0.50    inference(cnf_transformation,[],[f40])).
% 0.22/0.50  fof(f389,plain,(
% 0.22/0.50    ( ! [X0] : (v2_connsp_1(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0),sK3) | ~v2_connsp_1(X0,sK4) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)) ) | (~spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_13 | ~spl7_15)),
% 0.22/0.50    inference(subsumption_resolution,[],[f388,f223])).
% 0.22/0.50  fof(f223,plain,(
% 0.22/0.50    v1_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) | ~spl7_7),
% 0.22/0.50    inference(avatar_component_clause,[],[f222])).
% 0.22/0.50  fof(f222,plain,(
% 0.22/0.50    spl7_7 <=> v1_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.22/0.50  fof(f388,plain,(
% 0.22/0.50    ( ! [X0] : (v2_connsp_1(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0),sK3) | ~v2_connsp_1(X0,sK4) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) | ~v1_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)) ) | (~spl7_8 | ~spl7_9 | ~spl7_13 | ~spl7_15)),
% 0.22/0.50    inference(subsumption_resolution,[],[f387,f227])).
% 0.22/0.50  fof(f227,plain,(
% 0.22/0.50    v1_funct_2(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),u1_struct_0(sK4),u1_struct_0(sK3)) | ~spl7_8),
% 0.22/0.50    inference(avatar_component_clause,[],[f226])).
% 0.22/0.50  fof(f226,plain,(
% 0.22/0.50    spl7_8 <=> v1_funct_2(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),u1_struct_0(sK4),u1_struct_0(sK3))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.22/0.50  fof(f387,plain,(
% 0.22/0.50    ( ! [X0] : (v2_connsp_1(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0),sK3) | ~v2_connsp_1(X0,sK4) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) | ~v1_funct_2(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)) ) | (~spl7_9 | ~spl7_13 | ~spl7_15)),
% 0.22/0.50    inference(subsumption_resolution,[],[f386,f231])).
% 0.22/0.50  fof(f231,plain,(
% 0.22/0.50    m1_subset_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~spl7_9),
% 0.22/0.50    inference(avatar_component_clause,[],[f230])).
% 0.22/0.50  fof(f230,plain,(
% 0.22/0.50    spl7_9 <=> m1_subset_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.22/0.50  fof(f386,plain,(
% 0.22/0.50    ( ! [X0] : (v2_connsp_1(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0),sK3) | ~v2_connsp_1(X0,sK4) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) | ~m1_subset_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)) ) | (~spl7_13 | ~spl7_15)),
% 0.22/0.50    inference(subsumption_resolution,[],[f385,f250])).
% 0.22/0.50  fof(f250,plain,(
% 0.22/0.50    v5_pre_topc(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK4,sK3) | ~spl7_13),
% 0.22/0.50    inference(avatar_component_clause,[],[f249])).
% 0.22/0.50  fof(f249,plain,(
% 0.22/0.50    spl7_13 <=> v5_pre_topc(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK4,sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.22/0.50  fof(f385,plain,(
% 0.22/0.50    ( ! [X0] : (v2_connsp_1(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0),sK3) | ~v2_connsp_1(X0,sK4) | ~v5_pre_topc(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK4,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) | ~m1_subset_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)) ) | ~spl7_15),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f384])).
% 0.22/0.50  fof(f384,plain,(
% 0.22/0.50    ( ! [X0] : (v2_connsp_1(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0),sK3) | ~v2_connsp_1(X0,sK4) | ~v5_pre_topc(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK4,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) | ~m1_subset_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))) ) | ~spl7_15),
% 0.22/0.50    inference(superposition,[],[f75,f283])).
% 0.22/0.50  fof(f283,plain,(
% 0.22/0.50    ( ! [X0] : (k7_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),X0) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))) ) | ~spl7_15),
% 0.22/0.50    inference(avatar_component_clause,[],[f282])).
% 0.22/0.50  fof(f282,plain,(
% 0.22/0.50    spl7_15 <=> ! [X0] : (k7_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),X0) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 0.22/0.50  fof(f75,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (v2_connsp_1(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) | ~v2_connsp_1(X3,X0) | ~v5_pre_topc(X2,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (v2_connsp_1(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) | ~v2_connsp_1(X3,X0) | ~v5_pre_topc(X2,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f25])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v2_connsp_1(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) | (~v2_connsp_1(X3,X0) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,axiom,(
% 0.22/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_connsp_1(X3,X0) & v5_pre_topc(X2,X0,X1)) => v2_connsp_1(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1))))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_tops_2)).
% 0.22/0.50  fof(f367,plain,(
% 0.22/0.50    spl7_13),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f366])).
% 0.22/0.50  fof(f366,plain,(
% 0.22/0.50    $false | spl7_13),
% 0.22/0.50    inference(subsumption_resolution,[],[f365,f106])).
% 0.22/0.50  fof(f106,plain,(
% 0.22/0.50    sP0(sK3,sK4,sK5)),
% 0.22/0.50    inference(subsumption_resolution,[],[f105,f57])).
% 0.22/0.50  fof(f57,plain,(
% 0.22/0.50    v3_tops_2(sK5,sK3,sK4)),
% 0.22/0.50    inference(cnf_transformation,[],[f40])).
% 0.22/0.50  fof(f105,plain,(
% 0.22/0.50    ~v3_tops_2(sK5,sK3,sK4) | sP0(sK3,sK4,sK5)),
% 0.22/0.50    inference(resolution,[],[f101,f66])).
% 0.22/0.50  fof(f66,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | ~v3_tops_2(X0,X2,X1) | sP0(X2,X1,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f42])).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (((v3_tops_2(X0,X2,X1) | ~sP0(X2,X1,X0)) & (sP0(X2,X1,X0) | ~v3_tops_2(X0,X2,X1))) | ~sP1(X0,X1,X2))),
% 0.22/0.50    inference(rectify,[],[f41])).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    ! [X2,X1,X0] : (((v3_tops_2(X2,X0,X1) | ~sP0(X0,X1,X2)) & (sP0(X0,X1,X2) | ~v3_tops_2(X2,X0,X1))) | ~sP1(X2,X1,X0))),
% 0.22/0.50    inference(nnf_transformation,[],[f32])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    ! [X2,X1,X0] : ((v3_tops_2(X2,X0,X1) <=> sP0(X0,X1,X2)) | ~sP1(X2,X1,X0))),
% 0.22/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.22/0.50  fof(f101,plain,(
% 0.22/0.50    sP1(sK5,sK4,sK3)),
% 0.22/0.50    inference(subsumption_resolution,[],[f100,f49])).
% 0.22/0.50  fof(f100,plain,(
% 0.22/0.50    sP1(sK5,sK4,sK3) | ~l1_pre_topc(sK3)),
% 0.22/0.50    inference(subsumption_resolution,[],[f99,f52])).
% 0.22/0.50  fof(f99,plain,(
% 0.22/0.50    sP1(sK5,sK4,sK3) | ~l1_pre_topc(sK4) | ~l1_pre_topc(sK3)),
% 0.22/0.50    inference(subsumption_resolution,[],[f98,f53])).
% 0.22/0.50  fof(f53,plain,(
% 0.22/0.50    v1_funct_1(sK5)),
% 0.22/0.50    inference(cnf_transformation,[],[f40])).
% 0.22/0.50  fof(f98,plain,(
% 0.22/0.50    sP1(sK5,sK4,sK3) | ~v1_funct_1(sK5) | ~l1_pre_topc(sK4) | ~l1_pre_topc(sK3)),
% 0.22/0.50    inference(subsumption_resolution,[],[f96,f54])).
% 0.22/0.50  fof(f54,plain,(
% 0.22/0.50    v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))),
% 0.22/0.50    inference(cnf_transformation,[],[f40])).
% 0.22/0.50  fof(f96,plain,(
% 0.22/0.50    sP1(sK5,sK4,sK3) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) | ~v1_funct_1(sK5) | ~l1_pre_topc(sK4) | ~l1_pre_topc(sK3)),
% 0.22/0.50    inference(resolution,[],[f74,f55])).
% 0.22/0.50  fof(f55,plain,(
% 0.22/0.50    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))),
% 0.22/0.50    inference(cnf_transformation,[],[f40])).
% 0.22/0.50  fof(f74,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | sP1(X2,X1,X0) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f33])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (sP1(X2,X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(definition_folding,[],[f24,f32,f31])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (sP0(X0,X1,X2) <=> (v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)))),
% 0.22/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : ((v3_tops_2(X2,X0,X1) <=> (v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(flattening,[],[f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : ((v3_tops_2(X2,X0,X1) <=> (v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_tops_2(X2,X0,X1) <=> (v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0))))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tops_2)).
% 0.22/0.50  fof(f365,plain,(
% 0.22/0.50    ~sP0(sK3,sK4,sK5) | spl7_13),
% 0.22/0.50    inference(resolution,[],[f251,f72])).
% 0.22/0.50  fof(f72,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~sP0(X0,X1,X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f44])).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ~v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~v5_pre_topc(X2,X0,X1) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0)) & ((v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)) | ~sP0(X0,X1,X2)))),
% 0.22/0.50    inference(flattening,[],[f43])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (~v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~v5_pre_topc(X2,X0,X1) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0))) & ((v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)) | ~sP0(X0,X1,X2)))),
% 0.22/0.50    inference(nnf_transformation,[],[f31])).
% 0.22/0.50  fof(f251,plain,(
% 0.22/0.50    ~v5_pre_topc(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK4,sK3) | spl7_13),
% 0.22/0.50    inference(avatar_component_clause,[],[f249])).
% 0.22/0.50  fof(f293,plain,(
% 0.22/0.50    spl7_9),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f292])).
% 0.22/0.50  fof(f292,plain,(
% 0.22/0.50    $false | spl7_9),
% 0.22/0.50    inference(subsumption_resolution,[],[f291,f87])).
% 0.22/0.50  fof(f87,plain,(
% 0.22/0.50    sP2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)),
% 0.22/0.50    inference(subsumption_resolution,[],[f86,f53])).
% 0.22/0.50  fof(f86,plain,(
% 0.22/0.50    sP2(u1_struct_0(sK3),u1_struct_0(sK4),sK5) | ~v1_funct_1(sK5)),
% 0.22/0.50    inference(subsumption_resolution,[],[f84,f54])).
% 0.22/0.50  fof(f84,plain,(
% 0.22/0.50    sP2(u1_struct_0(sK3),u1_struct_0(sK4),sK5) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) | ~v1_funct_1(sK5)),
% 0.22/0.50    inference(resolution,[],[f79,f55])).
% 0.22/0.50  fof(f79,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP2(X0,X1,X2) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f35])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (sP2(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.50    inference(definition_folding,[],[f28,f34])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | ~sP2(X0,X1,X2))),
% 0.22/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.50    inference(flattening,[],[f27])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.22/0.50    inference(ennf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_2)).
% 0.22/0.50  fof(f291,plain,(
% 0.22/0.50    ~sP2(u1_struct_0(sK3),u1_struct_0(sK4),sK5) | spl7_9),
% 0.22/0.50    inference(resolution,[],[f232,f78])).
% 0.22/0.50  fof(f78,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~sP2(X0,X1,X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f45])).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | ~sP2(X0,X1,X2))),
% 0.22/0.50    inference(nnf_transformation,[],[f34])).
% 0.22/0.50  fof(f232,plain,(
% 0.22/0.50    ~m1_subset_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | spl7_9),
% 0.22/0.50    inference(avatar_component_clause,[],[f230])).
% 0.22/0.50  fof(f290,plain,(
% 0.22/0.50    spl7_8),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f289])).
% 0.22/0.50  fof(f289,plain,(
% 0.22/0.50    $false | spl7_8),
% 0.22/0.50    inference(subsumption_resolution,[],[f288,f87])).
% 0.22/0.50  fof(f288,plain,(
% 0.22/0.50    ~sP2(u1_struct_0(sK3),u1_struct_0(sK4),sK5) | spl7_8),
% 0.22/0.50    inference(resolution,[],[f228,f77])).
% 0.22/0.50  fof(f77,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) | ~sP2(X0,X1,X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f45])).
% 0.22/0.50  fof(f228,plain,(
% 0.22/0.50    ~v1_funct_2(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),u1_struct_0(sK4),u1_struct_0(sK3)) | spl7_8),
% 0.22/0.50    inference(avatar_component_clause,[],[f226])).
% 0.22/0.50  fof(f287,plain,(
% 0.22/0.50    spl7_7),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f286])).
% 0.22/0.50  fof(f286,plain,(
% 0.22/0.50    $false | spl7_7),
% 0.22/0.50    inference(subsumption_resolution,[],[f285,f87])).
% 0.22/0.50  fof(f285,plain,(
% 0.22/0.50    ~sP2(u1_struct_0(sK3),u1_struct_0(sK4),sK5) | spl7_7),
% 0.22/0.50    inference(resolution,[],[f224,f76])).
% 0.22/0.50  fof(f76,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (v1_funct_1(k2_tops_2(X0,X1,X2)) | ~sP2(X0,X1,X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f45])).
% 0.22/0.50  fof(f224,plain,(
% 0.22/0.50    ~v1_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) | spl7_7),
% 0.22/0.50    inference(avatar_component_clause,[],[f222])).
% 0.22/0.50  fof(f284,plain,(
% 0.22/0.50    ~spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_10 | spl7_15 | ~spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_5),
% 0.22/0.50    inference(avatar_split_clause,[],[f280,f176,f146,f142,f138,f282,f234,f230,f226,f222])).
% 0.22/0.50  fof(f234,plain,(
% 0.22/0.50    spl7_10 <=> k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) = k2_struct_0(sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.22/0.50  fof(f138,plain,(
% 0.22/0.50    spl7_1 <=> l1_struct_0(sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.22/0.50  fof(f142,plain,(
% 0.22/0.50    spl7_2 <=> l1_struct_0(sK4)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.22/0.50  fof(f146,plain,(
% 0.22/0.50    spl7_3 <=> v2_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.22/0.50  fof(f176,plain,(
% 0.22/0.50    spl7_5 <=> sK5 = k2_tops_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.22/0.50  fof(f280,plain,(
% 0.22/0.50    ( ! [X0] : (k7_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),X0) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0) | k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) != k2_struct_0(sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) | ~m1_subset_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))) ) | (~spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_5)),
% 0.22/0.50    inference(subsumption_resolution,[],[f279,f143])).
% 0.22/0.50  fof(f143,plain,(
% 0.22/0.50    l1_struct_0(sK4) | ~spl7_2),
% 0.22/0.50    inference(avatar_component_clause,[],[f142])).
% 0.22/0.50  fof(f279,plain,(
% 0.22/0.50    ( ! [X0] : (k7_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),X0) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0) | k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) != k2_struct_0(sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) | ~m1_subset_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) | ~l1_struct_0(sK4)) ) | (~spl7_1 | ~spl7_3 | ~spl7_5)),
% 0.22/0.51    inference(subsumption_resolution,[],[f278,f139])).
% 0.22/0.51  fof(f139,plain,(
% 0.22/0.51    l1_struct_0(sK3) | ~spl7_1),
% 0.22/0.51    inference(avatar_component_clause,[],[f138])).
% 0.22/0.51  fof(f278,plain,(
% 0.22/0.51    ( ! [X0] : (k7_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),X0) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0) | k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) != k2_struct_0(sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) | ~m1_subset_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) | ~l1_struct_0(sK3) | ~l1_struct_0(sK4)) ) | (~spl7_3 | ~spl7_5)),
% 0.22/0.51    inference(subsumption_resolution,[],[f277,f148])).
% 0.22/0.51  fof(f148,plain,(
% 0.22/0.51    v2_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) | ~spl7_3),
% 0.22/0.51    inference(avatar_component_clause,[],[f146])).
% 0.22/0.51  fof(f277,plain,(
% 0.22/0.51    ( ! [X0] : (k7_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),X0) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0) | ~v2_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) | k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) != k2_struct_0(sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) | ~m1_subset_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) | ~l1_struct_0(sK3) | ~l1_struct_0(sK4)) ) | ~spl7_5),
% 0.22/0.51    inference(superposition,[],[f61,f178])).
% 0.22/0.51  fof(f178,plain,(
% 0.22/0.51    sK5 = k2_tops_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) | ~spl7_5),
% 0.22/0.51    inference(avatar_component_clause,[],[f176])).
% 0.22/0.51  fof(f61,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f17])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f16])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) | (~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f8])).
% 0.22/0.51  fof(f8,axiom,(
% 0.22/0.51    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3))))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_tops_2)).
% 0.22/0.51  fof(f275,plain,(
% 0.22/0.51    ~spl7_1 | ~spl7_2 | ~spl7_6 | spl7_10),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f274])).
% 0.22/0.51  % (6109)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.51  % (6114)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.51  % (6126)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.51  % (6118)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.51  % (6125)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.52  % (6130)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.52  % (6115)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.52  % (6117)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.52  fof(f274,plain,(
% 0.22/0.52    $false | (~spl7_1 | ~spl7_2 | ~spl7_6 | spl7_10)),
% 0.22/0.52    inference(subsumption_resolution,[],[f273,f139])).
% 0.22/0.52  fof(f273,plain,(
% 0.22/0.52    ~l1_struct_0(sK3) | (~spl7_2 | ~spl7_6 | spl7_10)),
% 0.22/0.52    inference(subsumption_resolution,[],[f272,f50])).
% 0.22/0.52  fof(f272,plain,(
% 0.22/0.52    v2_struct_0(sK4) | ~l1_struct_0(sK3) | (~spl7_2 | ~spl7_6 | spl7_10)),
% 0.22/0.52    inference(subsumption_resolution,[],[f271,f143])).
% 0.22/0.52  fof(f271,plain,(
% 0.22/0.52    ~l1_struct_0(sK4) | v2_struct_0(sK4) | ~l1_struct_0(sK3) | (~spl7_6 | spl7_10)),
% 0.22/0.52    inference(subsumption_resolution,[],[f270,f53])).
% 0.22/0.52  fof(f270,plain,(
% 0.22/0.52    ~v1_funct_1(sK5) | ~l1_struct_0(sK4) | v2_struct_0(sK4) | ~l1_struct_0(sK3) | (~spl7_6 | spl7_10)),
% 0.22/0.52    inference(subsumption_resolution,[],[f269,f54])).
% 0.22/0.52  fof(f269,plain,(
% 0.22/0.52    ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) | ~v1_funct_1(sK5) | ~l1_struct_0(sK4) | v2_struct_0(sK4) | ~l1_struct_0(sK3) | (~spl7_6 | spl7_10)),
% 0.22/0.52    inference(subsumption_resolution,[],[f268,f55])).
% 0.22/0.52  fof(f268,plain,(
% 0.22/0.52    ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) | ~v1_funct_1(sK5) | ~l1_struct_0(sK4) | v2_struct_0(sK4) | ~l1_struct_0(sK3) | (~spl7_6 | spl7_10)),
% 0.22/0.52    inference(subsumption_resolution,[],[f267,f181])).
% 0.22/0.52  fof(f181,plain,(
% 0.22/0.52    k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) = k2_struct_0(sK4) | ~spl7_6),
% 0.22/0.52    inference(avatar_component_clause,[],[f180])).
% 0.22/0.52  fof(f180,plain,(
% 0.22/0.52    spl7_6 <=> k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) = k2_struct_0(sK4)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.22/0.52  fof(f267,plain,(
% 0.22/0.52    k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK4) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) | ~v1_funct_1(sK5) | ~l1_struct_0(sK4) | v2_struct_0(sK4) | ~l1_struct_0(sK3) | spl7_10),
% 0.22/0.52    inference(subsumption_resolution,[],[f266,f108])).
% 0.22/0.52  fof(f108,plain,(
% 0.22/0.52    v2_funct_1(sK5)),
% 0.22/0.52    inference(resolution,[],[f106,f70])).
% 0.22/0.52  fof(f70,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | v2_funct_1(X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f44])).
% 0.22/0.52  fof(f266,plain,(
% 0.22/0.52    ~v2_funct_1(sK5) | k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK4) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) | ~v1_funct_1(sK5) | ~l1_struct_0(sK4) | v2_struct_0(sK4) | ~l1_struct_0(sK3) | spl7_10),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f263])).
% 0.22/0.52  fof(f263,plain,(
% 0.22/0.52    k2_struct_0(sK3) != k2_struct_0(sK3) | ~v2_funct_1(sK5) | k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK4) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) | ~v1_funct_1(sK5) | ~l1_struct_0(sK4) | v2_struct_0(sK4) | ~l1_struct_0(sK3) | spl7_10),
% 0.22/0.52    inference(superposition,[],[f236,f64])).
% 0.22/0.52  fof(f64,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | v2_struct_0(X1) | ~l1_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f21])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : ((k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_struct_0(X1) | v2_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f20])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : (((k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) | (~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_struct_0(X1) | v2_struct_0(X1))) | ~l1_struct_0(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_2)).
% 0.22/0.52  fof(f236,plain,(
% 0.22/0.52    k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) != k2_struct_0(sK3) | spl7_10),
% 0.22/0.52    inference(avatar_component_clause,[],[f234])).
% 0.22/0.52  fof(f193,plain,(
% 0.22/0.52    spl7_6),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f192])).
% 0.22/0.52  fof(f192,plain,(
% 0.22/0.52    $false | spl7_6),
% 0.22/0.52    inference(subsumption_resolution,[],[f191,f106])).
% 0.22/0.52  fof(f191,plain,(
% 0.22/0.52    ~sP0(sK3,sK4,sK5) | spl7_6),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f190])).
% 0.22/0.52  fof(f190,plain,(
% 0.22/0.52    k2_struct_0(sK4) != k2_struct_0(sK4) | ~sP0(sK3,sK4,sK5) | spl7_6),
% 0.22/0.52    inference(superposition,[],[f182,f69])).
% 0.22/0.52  fof(f69,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) | ~sP0(X0,X1,X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f44])).
% 0.22/0.52  fof(f182,plain,(
% 0.22/0.52    k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK4) | spl7_6),
% 0.22/0.52    inference(avatar_component_clause,[],[f180])).
% 0.22/0.52  fof(f189,plain,(
% 0.22/0.52    spl7_4),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f188])).
% 0.22/0.52  fof(f188,plain,(
% 0.22/0.52    $false | spl7_4),
% 0.22/0.52    inference(subsumption_resolution,[],[f187,f87])).
% 0.22/0.52  fof(f187,plain,(
% 0.22/0.52    ~sP2(u1_struct_0(sK3),u1_struct_0(sK4),sK5) | spl7_4),
% 0.22/0.52    inference(resolution,[],[f174,f89])).
% 0.22/0.52  fof(f89,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (sP2(X0,X1,k2_tops_2(X1,X0,X2)) | ~sP2(X1,X0,X2)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f88,f76])).
% 0.22/0.52  fof(f88,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (sP2(X0,X1,k2_tops_2(X1,X0,X2)) | ~v1_funct_1(k2_tops_2(X1,X0,X2)) | ~sP2(X1,X0,X2)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f85,f77])).
% 0.22/0.52  fof(f85,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (sP2(X0,X1,k2_tops_2(X1,X0,X2)) | ~v1_funct_2(k2_tops_2(X1,X0,X2),X0,X1) | ~v1_funct_1(k2_tops_2(X1,X0,X2)) | ~sP2(X1,X0,X2)) )),
% 0.22/0.52    inference(resolution,[],[f79,f78])).
% 0.22/0.52  fof(f174,plain,(
% 0.22/0.52    ~sP2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) | spl7_4),
% 0.22/0.52    inference(avatar_component_clause,[],[f172])).
% 0.22/0.52  fof(f172,plain,(
% 0.22/0.52    spl7_4 <=> sP2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.22/0.52  fof(f183,plain,(
% 0.22/0.52    ~spl7_4 | spl7_5 | ~spl7_6 | ~spl7_1 | ~spl7_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f170,f142,f138,f180,f176,f172])).
% 0.22/0.52  fof(f170,plain,(
% 0.22/0.52    k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK4) | sK5 = k2_tops_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) | ~sP2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) | (~spl7_1 | ~spl7_2)),
% 0.22/0.52    inference(subsumption_resolution,[],[f169,f139])).
% 0.22/0.52  fof(f169,plain,(
% 0.22/0.52    k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK4) | ~l1_struct_0(sK3) | sK5 = k2_tops_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) | ~sP2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) | ~spl7_2),
% 0.22/0.52    inference(subsumption_resolution,[],[f168,f50])).
% 0.22/0.52  fof(f168,plain,(
% 0.22/0.52    k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK4) | v2_struct_0(sK4) | ~l1_struct_0(sK3) | sK5 = k2_tops_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) | ~sP2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) | ~spl7_2),
% 0.22/0.52    inference(subsumption_resolution,[],[f167,f143])).
% 0.22/0.52  fof(f167,plain,(
% 0.22/0.52    k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK4) | ~l1_struct_0(sK4) | v2_struct_0(sK4) | ~l1_struct_0(sK3) | sK5 = k2_tops_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) | ~sP2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))),
% 0.22/0.52    inference(subsumption_resolution,[],[f166,f53])).
% 0.22/0.52  fof(f166,plain,(
% 0.22/0.52    k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK4) | ~v1_funct_1(sK5) | ~l1_struct_0(sK4) | v2_struct_0(sK4) | ~l1_struct_0(sK3) | sK5 = k2_tops_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) | ~sP2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))),
% 0.22/0.52    inference(subsumption_resolution,[],[f165,f54])).
% 0.22/0.52  fof(f165,plain,(
% 0.22/0.52    k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK4) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) | ~v1_funct_1(sK5) | ~l1_struct_0(sK4) | v2_struct_0(sK4) | ~l1_struct_0(sK3) | sK5 = k2_tops_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) | ~sP2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))),
% 0.22/0.52    inference(subsumption_resolution,[],[f164,f55])).
% 0.22/0.52  fof(f164,plain,(
% 0.22/0.52    k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK4) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) | ~v1_funct_1(sK5) | ~l1_struct_0(sK4) | v2_struct_0(sK4) | ~l1_struct_0(sK3) | sK5 = k2_tops_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) | ~sP2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))),
% 0.22/0.52    inference(subsumption_resolution,[],[f162,f108])).
% 0.22/0.52  fof(f162,plain,(
% 0.22/0.52    ~v2_funct_1(sK5) | k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK4) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) | ~v1_funct_1(sK5) | ~l1_struct_0(sK4) | v2_struct_0(sK4) | ~l1_struct_0(sK3) | sK5 = k2_tops_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) | ~sP2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))),
% 0.22/0.52    inference(resolution,[],[f62,f120])).
% 0.22/0.52  fof(f120,plain,(
% 0.22/0.52    ( ! [X0] : (~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK4),k2_tops_2(u1_struct_0(sK4),u1_struct_0(sK3),X0),sK5) | sK5 = k2_tops_2(u1_struct_0(sK4),u1_struct_0(sK3),X0) | ~sP2(u1_struct_0(sK4),u1_struct_0(sK3),X0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f119,f76])).
% 0.22/0.52  fof(f119,plain,(
% 0.22/0.52    ( ! [X0] : (sK5 = k2_tops_2(u1_struct_0(sK4),u1_struct_0(sK3),X0) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK4),k2_tops_2(u1_struct_0(sK4),u1_struct_0(sK3),X0),sK5) | ~v1_funct_1(k2_tops_2(u1_struct_0(sK4),u1_struct_0(sK3),X0)) | ~sP2(u1_struct_0(sK4),u1_struct_0(sK3),X0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f118,f77])).
% 0.22/0.52  fof(f118,plain,(
% 0.22/0.52    ( ! [X0] : (sK5 = k2_tops_2(u1_struct_0(sK4),u1_struct_0(sK3),X0) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK4),k2_tops_2(u1_struct_0(sK4),u1_struct_0(sK3),X0),sK5) | ~v1_funct_2(k2_tops_2(u1_struct_0(sK4),u1_struct_0(sK3),X0),u1_struct_0(sK3),u1_struct_0(sK4)) | ~v1_funct_1(k2_tops_2(u1_struct_0(sK4),u1_struct_0(sK3),X0)) | ~sP2(u1_struct_0(sK4),u1_struct_0(sK3),X0)) )),
% 0.22/0.52    inference(resolution,[],[f114,f78])).
% 0.22/0.52  fof(f114,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) | sK5 = X0 | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK4),X0,sK5) | ~v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(sK4)) | ~v1_funct_1(X0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f113,f53])).
% 0.22/0.52  fof(f113,plain,(
% 0.22/0.52    ( ! [X0] : (~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK4),X0,sK5) | sK5 = X0 | ~v1_funct_1(sK5) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) | ~v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(sK4)) | ~v1_funct_1(X0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f111,f54])).
% 0.22/0.52  fof(f111,plain,(
% 0.22/0.52    ( ! [X0] : (~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK4),X0,sK5) | sK5 = X0 | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) | ~v1_funct_1(sK5) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) | ~v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(sK4)) | ~v1_funct_1(X0)) )),
% 0.22/0.52    inference(resolution,[],[f80,f55])).
% 0.22/0.52  fof(f80,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_funct_2(X0,X1,X2,X3) | X2 = X3 | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f46])).
% 0.22/0.52  fof(f46,plain,(
% 0.22/0.52    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.52    inference(nnf_transformation,[],[f30])).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.52    inference(flattening,[],[f29])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.22/0.52    inference(ennf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).
% 0.22/0.52  fof(f62,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | v2_struct_0(X1) | ~l1_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f19])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : (r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_struct_0(X1) | v2_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f18])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : ((r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) | (~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_struct_0(X1) | v2_struct_0(X1))) | ~l1_struct_0(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,axiom,(
% 0.22/0.52    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tops_2)).
% 0.22/0.52  fof(f157,plain,(
% 0.22/0.52    spl7_2),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f156])).
% 0.22/0.52  fof(f156,plain,(
% 0.22/0.52    $false | spl7_2),
% 0.22/0.52    inference(subsumption_resolution,[],[f155,f52])).
% 0.22/0.52  fof(f155,plain,(
% 0.22/0.52    ~l1_pre_topc(sK4) | spl7_2),
% 0.22/0.52    inference(resolution,[],[f144,f65])).
% 0.22/0.52  fof(f65,plain,(
% 0.22/0.52    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.52  fof(f144,plain,(
% 0.22/0.52    ~l1_struct_0(sK4) | spl7_2),
% 0.22/0.52    inference(avatar_component_clause,[],[f142])).
% 0.22/0.52  fof(f154,plain,(
% 0.22/0.52    spl7_1),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f153])).
% 0.22/0.52  fof(f153,plain,(
% 0.22/0.52    $false | spl7_1),
% 0.22/0.52    inference(subsumption_resolution,[],[f152,f49])).
% 0.22/0.52  fof(f152,plain,(
% 0.22/0.52    ~l1_pre_topc(sK3) | spl7_1),
% 0.22/0.52    inference(resolution,[],[f140,f65])).
% 0.22/0.52  fof(f140,plain,(
% 0.22/0.52    ~l1_struct_0(sK3) | spl7_1),
% 0.22/0.52    inference(avatar_component_clause,[],[f138])).
% 0.22/0.52  fof(f149,plain,(
% 0.22/0.52    ~spl7_1 | ~spl7_2 | spl7_3),
% 0.22/0.52    inference(avatar_split_clause,[],[f136,f146,f142,f138])).
% 0.22/0.52  fof(f136,plain,(
% 0.22/0.52    v2_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) | ~l1_struct_0(sK4) | ~l1_struct_0(sK3)),
% 0.22/0.52    inference(subsumption_resolution,[],[f135,f106])).
% 0.22/0.52  fof(f135,plain,(
% 0.22/0.52    v2_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) | ~l1_struct_0(sK4) | ~l1_struct_0(sK3) | ~sP0(sK3,sK4,sK5)),
% 0.22/0.52    inference(subsumption_resolution,[],[f134,f53])).
% 0.22/0.52  fof(f134,plain,(
% 0.22/0.52    v2_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) | ~v1_funct_1(sK5) | ~l1_struct_0(sK4) | ~l1_struct_0(sK3) | ~sP0(sK3,sK4,sK5)),
% 0.22/0.52    inference(subsumption_resolution,[],[f132,f54])).
% 0.22/0.52  fof(f132,plain,(
% 0.22/0.52    v2_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) | ~v1_funct_1(sK5) | ~l1_struct_0(sK4) | ~l1_struct_0(sK3) | ~sP0(sK3,sK4,sK5)),
% 0.22/0.52    inference(resolution,[],[f131,f55])).
% 0.22/0.52  fof(f131,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0) | ~sP0(X0,X1,X2)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f130,f70])).
% 0.22/0.52  fof(f130,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0) | ~sP0(X0,X1,X2)) )),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f129])).
% 0.22/0.52  fof(f129,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k2_struct_0(X1) != k2_struct_0(X1) | ~v2_funct_1(X2) | v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0) | ~sP0(X0,X1,X2)) )),
% 0.22/0.52    inference(superposition,[],[f60,f69])).
% 0.22/0.52  fof(f60,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~v2_funct_1(X2) | v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f15])).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : (v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f14])).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : ((v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | (~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,axiom,(
% 0.22/0.52    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_tops_2)).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (6110)------------------------------
% 0.22/0.52  % (6110)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (6110)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (6110)Memory used [KB]: 6396
% 0.22/0.52  % (6110)Time elapsed: 0.094 s
% 0.22/0.52  % (6110)------------------------------
% 0.22/0.52  % (6110)------------------------------
% 0.22/0.52  % (6106)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.52  % (6128)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.53  % (6103)Success in time 0.163 s
%------------------------------------------------------------------------------
