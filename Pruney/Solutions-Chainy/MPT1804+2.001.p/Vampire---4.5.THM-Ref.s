%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:38 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  188 ( 872 expanded)
%              Number of leaves         :   26 ( 315 expanded)
%              Depth                    :   18
%              Number of atoms          :  853 (8376 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f265,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f108,f152,f162,f172,f219,f225,f231,f253,f264])).

fof(f264,plain,(
    ~ spl8_7 ),
    inference(avatar_contradiction_clause,[],[f263])).

fof(f263,plain,
    ( $false
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f262,f59])).

fof(f59,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,
    ( ( ~ m1_subset_1(k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(k8_tmap_1(sK4,sK5)))))
      | ~ v5_pre_topc(k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK6),sK6,k8_tmap_1(sK4,sK5))
      | ~ v1_funct_2(k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK6),u1_struct_0(sK6),u1_struct_0(k8_tmap_1(sK4,sK5)))
      | ~ v1_funct_1(k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK6)) )
    & r1_tsep_1(sK5,sK6)
    & m1_pre_topc(sK6,sK4)
    & ~ v2_struct_0(sK6)
    & m1_pre_topc(sK5,sK4)
    & ~ v2_struct_0(sK5)
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f17,f47,f46,f45])).

fof(f45,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))))
                  | ~ v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X2,k8_tmap_1(X0,X1))
                  | ~ v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))
                  | ~ v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2)) )
                & r1_tsep_1(X1,X2)
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_subset_1(k2_tmap_1(sK4,k8_tmap_1(sK4,X1),k9_tmap_1(sK4,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(sK4,X1)))))
                | ~ v5_pre_topc(k2_tmap_1(sK4,k8_tmap_1(sK4,X1),k9_tmap_1(sK4,X1),X2),X2,k8_tmap_1(sK4,X1))
                | ~ v1_funct_2(k2_tmap_1(sK4,k8_tmap_1(sK4,X1),k9_tmap_1(sK4,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(sK4,X1)))
                | ~ v1_funct_1(k2_tmap_1(sK4,k8_tmap_1(sK4,X1),k9_tmap_1(sK4,X1),X2)) )
              & r1_tsep_1(X1,X2)
              & m1_pre_topc(X2,sK4)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK4)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK4)
      & v2_pre_topc(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ m1_subset_1(k2_tmap_1(sK4,k8_tmap_1(sK4,X1),k9_tmap_1(sK4,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(sK4,X1)))))
              | ~ v5_pre_topc(k2_tmap_1(sK4,k8_tmap_1(sK4,X1),k9_tmap_1(sK4,X1),X2),X2,k8_tmap_1(sK4,X1))
              | ~ v1_funct_2(k2_tmap_1(sK4,k8_tmap_1(sK4,X1),k9_tmap_1(sK4,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(sK4,X1)))
              | ~ v1_funct_1(k2_tmap_1(sK4,k8_tmap_1(sK4,X1),k9_tmap_1(sK4,X1),X2)) )
            & r1_tsep_1(X1,X2)
            & m1_pre_topc(X2,sK4)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(X1,sK4)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ( ~ m1_subset_1(k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(sK4,sK5)))))
            | ~ v5_pre_topc(k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),X2),X2,k8_tmap_1(sK4,sK5))
            | ~ v1_funct_2(k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(sK4,sK5)))
            | ~ v1_funct_1(k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),X2)) )
          & r1_tsep_1(sK5,X2)
          & m1_pre_topc(X2,sK4)
          & ~ v2_struct_0(X2) )
      & m1_pre_topc(sK5,sK4)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ? [X2] :
        ( ( ~ m1_subset_1(k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(sK4,sK5)))))
          | ~ v5_pre_topc(k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),X2),X2,k8_tmap_1(sK4,sK5))
          | ~ v1_funct_2(k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(sK4,sK5)))
          | ~ v1_funct_1(k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),X2)) )
        & r1_tsep_1(sK5,X2)
        & m1_pre_topc(X2,sK4)
        & ~ v2_struct_0(X2) )
   => ( ( ~ m1_subset_1(k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(k8_tmap_1(sK4,sK5)))))
        | ~ v5_pre_topc(k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK6),sK6,k8_tmap_1(sK4,sK5))
        | ~ v1_funct_2(k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK6),u1_struct_0(sK6),u1_struct_0(k8_tmap_1(sK4,sK5)))
        | ~ v1_funct_1(k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK6)) )
      & r1_tsep_1(sK5,sK6)
      & m1_pre_topc(sK6,sK4)
      & ~ v2_struct_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))))
                | ~ v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X2,k8_tmap_1(X0,X1))
                | ~ v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))
                | ~ v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2)) )
              & r1_tsep_1(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))))
                | ~ v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X2,k8_tmap_1(X0,X1))
                | ~ v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))
                | ~ v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2)) )
              & r1_tsep_1(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
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
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ( r1_tsep_1(X1,X2)
                 => ( m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))))
                    & v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X2,k8_tmap_1(X0,X1))
                    & v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))
                    & v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
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
             => ( r1_tsep_1(X1,X2)
               => ( m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))))
                  & v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X2,k8_tmap_1(X0,X1))
                  & v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))
                  & v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_tmap_1)).

fof(f262,plain,
    ( v2_struct_0(sK4)
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f261,f60])).

fof(f60,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f261,plain,
    ( ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f260,f61])).

fof(f61,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f260,plain,
    ( ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f259,f63])).

fof(f63,plain,(
    m1_pre_topc(sK5,sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f259,plain,
    ( ~ m1_pre_topc(sK5,sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ spl8_7 ),
    inference(resolution,[],[f206,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v2_pre_topc(k8_tmap_1(X0,X1))
        & ~ v2_struct_0(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v2_pre_topc(k8_tmap_1(X0,X1))
        & ~ v2_struct_0(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_pre_topc(k8_tmap_1(X0,X1))
        & ~ v2_struct_0(k8_tmap_1(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1))
        & ~ v2_struct_0(k8_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_tmap_1)).

fof(f206,plain,
    ( v2_struct_0(k8_tmap_1(sK4,sK5))
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f204])).

fof(f204,plain,
    ( spl8_7
  <=> v2_struct_0(k8_tmap_1(sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f253,plain,
    ( spl8_3
    | ~ spl8_10 ),
    inference(avatar_contradiction_clause,[],[f252])).

fof(f252,plain,
    ( $false
    | spl8_3
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f251,f66])).

fof(f66,plain,(
    r1_tsep_1(sK5,sK6) ),
    inference(cnf_transformation,[],[f48])).

fof(f251,plain,
    ( ~ r1_tsep_1(sK5,sK6)
    | spl8_3
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f250,f59])).

fof(f250,plain,
    ( v2_struct_0(sK4)
    | ~ r1_tsep_1(sK5,sK6)
    | spl8_3
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f249,f60])).

fof(f249,plain,
    ( ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ r1_tsep_1(sK5,sK6)
    | spl8_3
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f248,f61])).

fof(f248,plain,
    ( ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ r1_tsep_1(sK5,sK6)
    | spl8_3
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f247,f62])).

fof(f62,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f48])).

fof(f247,plain,
    ( v2_struct_0(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ r1_tsep_1(sK5,sK6)
    | spl8_3
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f246,f63])).

fof(f246,plain,
    ( ~ m1_pre_topc(sK5,sK4)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ r1_tsep_1(sK5,sK6)
    | spl8_3
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f245,f64])).

fof(f64,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f48])).

fof(f245,plain,
    ( v2_struct_0(sK6)
    | ~ m1_pre_topc(sK5,sK4)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ r1_tsep_1(sK5,sK6)
    | spl8_3
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f242,f65])).

fof(f65,plain,(
    m1_pre_topc(sK6,sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f242,plain,
    ( ~ m1_pre_topc(sK6,sK4)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(sK5,sK4)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ r1_tsep_1(sK5,sK6)
    | spl8_3
    | ~ spl8_10 ),
    inference(resolution,[],[f241,f235])).

fof(f235,plain,
    ( ~ sP0(k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK6),k8_tmap_1(sK4,sK5),sK6)
    | spl8_3
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f233,f103])).

fof(f103,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK6),sK6,k8_tmap_1(sK4,sK5))
    | spl8_3 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl8_3
  <=> v5_pre_topc(k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK6),sK6,k8_tmap_1(sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f233,plain,
    ( ~ sP0(k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK6),k8_tmap_1(sK4,sK5),sK6)
    | v5_pre_topc(k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK6),sK6,k8_tmap_1(sK4,sK5))
    | ~ spl8_10 ),
    inference(resolution,[],[f218,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ sP0(X2,X1,X0)
      | v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( ( v5_pre_topc(X2,X0,X1)
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | ~ v5_pre_topc(X2,X0,X1) ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f49])).

fof(f49,plain,(
    ! [X1,X0,X2] :
      ( ( ( v5_pre_topc(X2,X1,X0)
          | ~ sP0(X2,X0,X1) )
        & ( sP0(X2,X0,X1)
          | ~ v5_pre_topc(X2,X1,X0) ) )
      | ~ sP1(X1,X0,X2) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X1,X0,X2] :
      ( ( v5_pre_topc(X2,X1,X0)
      <=> sP0(X2,X0,X1) )
      | ~ sP1(X1,X0,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f218,plain,
    ( sP1(sK6,k8_tmap_1(sK4,sK5),k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK6))
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f216])).

fof(f216,plain,
    ( spl8_10
  <=> sP1(sK6,k8_tmap_1(sK4,sK5),k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f241,plain,(
    ! [X2,X0,X1] :
      ( sP0(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),k8_tmap_1(X0,X1),X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ r1_tsep_1(X1,X2) ) ),
    inference(subsumption_resolution,[],[f240,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X2))
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ~ r1_tmap_1(X2,X1,X0,sK7(X0,X1,X2))
          & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X2)) ) )
      & ( ! [X4] :
            ( r1_tmap_1(X2,X1,X0,X4)
            | ~ m1_subset_1(X4,u1_struct_0(X2)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f52,f53])).

fof(f53,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_tmap_1(X2,X1,X0,X3)
          & m1_subset_1(X3,u1_struct_0(X2)) )
     => ( ~ r1_tmap_1(X2,X1,X0,sK7(X0,X1,X2))
        & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ~ r1_tmap_1(X2,X1,X0,X3)
            & m1_subset_1(X3,u1_struct_0(X2)) ) )
      & ( ! [X4] :
            ( r1_tmap_1(X2,X1,X0,X4)
            | ~ m1_subset_1(X4,u1_struct_0(X2)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ( sP0(X2,X0,X1)
        | ? [X3] :
            ( ~ r1_tmap_1(X1,X0,X2,X3)
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ! [X3] :
            ( r1_tmap_1(X1,X0,X2,X3)
            | ~ m1_subset_1(X3,u1_struct_0(X1)) )
        | ~ sP0(X2,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X0,X1)
    <=> ! [X3] :
          ( r1_tmap_1(X1,X0,X2,X3)
          | ~ m1_subset_1(X3,u1_struct_0(X1)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f240,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK7(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),k8_tmap_1(X0,X1),X2),u1_struct_0(X2))
      | ~ r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | sP0(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),k8_tmap_1(X0,X1),X2) ) ),
    inference(resolution,[],[f77,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tmap_1(X2,X1,X0,sK7(X0,X1,X2))
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
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
                  ( r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X2)) )
              | ~ r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
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
                  ( r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X2)) )
              | ~ r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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
             => ( r1_tsep_1(X1,X2)
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X2))
                   => r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_tmap_1)).

fof(f231,plain,(
    spl8_9 ),
    inference(avatar_contradiction_clause,[],[f230])).

fof(f230,plain,
    ( $false
    | spl8_9 ),
    inference(subsumption_resolution,[],[f229,f59])).

fof(f229,plain,
    ( v2_struct_0(sK4)
    | spl8_9 ),
    inference(subsumption_resolution,[],[f228,f60])).

fof(f228,plain,
    ( ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | spl8_9 ),
    inference(subsumption_resolution,[],[f227,f61])).

fof(f227,plain,
    ( ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | spl8_9 ),
    inference(subsumption_resolution,[],[f226,f63])).

fof(f226,plain,
    ( ~ m1_pre_topc(sK5,sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | spl8_9 ),
    inference(resolution,[],[f214,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_tmap_1)).

fof(f214,plain,
    ( ~ l1_pre_topc(k8_tmap_1(sK4,sK5))
    | spl8_9 ),
    inference(avatar_component_clause,[],[f212])).

fof(f212,plain,
    ( spl8_9
  <=> l1_pre_topc(k8_tmap_1(sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f225,plain,(
    spl8_8 ),
    inference(avatar_contradiction_clause,[],[f224])).

fof(f224,plain,
    ( $false
    | spl8_8 ),
    inference(subsumption_resolution,[],[f223,f59])).

fof(f223,plain,
    ( v2_struct_0(sK4)
    | spl8_8 ),
    inference(subsumption_resolution,[],[f222,f60])).

fof(f222,plain,
    ( ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | spl8_8 ),
    inference(subsumption_resolution,[],[f221,f61])).

fof(f221,plain,
    ( ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | spl8_8 ),
    inference(subsumption_resolution,[],[f220,f63])).

fof(f220,plain,
    ( ~ m1_pre_topc(sK5,sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | spl8_8 ),
    inference(resolution,[],[f210,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f210,plain,
    ( ~ v2_pre_topc(k8_tmap_1(sK4,sK5))
    | spl8_8 ),
    inference(avatar_component_clause,[],[f208])).

fof(f208,plain,
    ( spl8_8
  <=> v2_pre_topc(k8_tmap_1(sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f219,plain,
    ( spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | spl8_10
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f202,f105,f97,f93,f216,f212,f208,f204])).

fof(f93,plain,
    ( spl8_1
  <=> v1_funct_1(k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f97,plain,
    ( spl8_2
  <=> v1_funct_2(k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK6),u1_struct_0(sK6),u1_struct_0(k8_tmap_1(sK4,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f105,plain,
    ( spl8_4
  <=> m1_subset_1(k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(k8_tmap_1(sK4,sK5))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f202,plain,
    ( sP1(sK6,k8_tmap_1(sK4,sK5),k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK6))
    | ~ l1_pre_topc(k8_tmap_1(sK4,sK5))
    | ~ v2_pre_topc(k8_tmap_1(sK4,sK5))
    | v2_struct_0(k8_tmap_1(sK4,sK5))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f201,f64])).

fof(f201,plain,
    ( sP1(sK6,k8_tmap_1(sK4,sK5),k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK6))
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(k8_tmap_1(sK4,sK5))
    | ~ v2_pre_topc(k8_tmap_1(sK4,sK5))
    | v2_struct_0(k8_tmap_1(sK4,sK5))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f200,f123])).

fof(f123,plain,(
    v2_pre_topc(sK6) ),
    inference(subsumption_resolution,[],[f122,f60])).

fof(f122,plain,
    ( v2_pre_topc(sK6)
    | ~ v2_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f119,f61])).

fof(f119,plain,
    ( v2_pre_topc(sK6)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(resolution,[],[f78,f65])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f200,plain,
    ( sP1(sK6,k8_tmap_1(sK4,sK5),k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK6))
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(k8_tmap_1(sK4,sK5))
    | ~ v2_pre_topc(k8_tmap_1(sK4,sK5))
    | v2_struct_0(k8_tmap_1(sK4,sK5))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f199,f113])).

fof(f113,plain,(
    l1_pre_topc(sK6) ),
    inference(subsumption_resolution,[],[f111,f61])).

fof(f111,plain,
    ( l1_pre_topc(sK6)
    | ~ l1_pre_topc(sK4) ),
    inference(resolution,[],[f69,f65])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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

fof(f199,plain,
    ( sP1(sK6,k8_tmap_1(sK4,sK5),k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK6))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(k8_tmap_1(sK4,sK5))
    | ~ v2_pre_topc(k8_tmap_1(sK4,sK5))
    | v2_struct_0(k8_tmap_1(sK4,sK5))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f198,f94])).

fof(f94,plain,
    ( v1_funct_1(k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK6))
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f93])).

fof(f198,plain,
    ( sP1(sK6,k8_tmap_1(sK4,sK5),k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK6))
    | ~ v1_funct_1(k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK6))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(k8_tmap_1(sK4,sK5))
    | ~ v2_pre_topc(k8_tmap_1(sK4,sK5))
    | v2_struct_0(k8_tmap_1(sK4,sK5))
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f193,f98])).

fof(f98,plain,
    ( v1_funct_2(k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK6),u1_struct_0(sK6),u1_struct_0(k8_tmap_1(sK4,sK5)))
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f97])).

fof(f193,plain,
    ( sP1(sK6,k8_tmap_1(sK4,sK5),k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK6))
    | ~ v1_funct_2(k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK6),u1_struct_0(sK6),u1_struct_0(k8_tmap_1(sK4,sK5)))
    | ~ v1_funct_1(k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK6))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(k8_tmap_1(sK4,sK5))
    | ~ v2_pre_topc(k8_tmap_1(sK4,sK5))
    | v2_struct_0(k8_tmap_1(sK4,sK5))
    | ~ spl8_4 ),
    inference(resolution,[],[f76,f106])).

fof(f106,plain,
    ( m1_subset_1(k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(k8_tmap_1(sK4,sK5)))))
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f105])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | sP1(X1,X0,X2)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP1(X1,X0,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f23,f39,f38])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X1,X0)
              <=> ! [X3] :
                    ( r1_tmap_1(X1,X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
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
              ( ( v5_pre_topc(X2,X1,X0)
              <=> ! [X3] :
                    ( r1_tmap_1(X1,X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ( v5_pre_topc(X2,X1,X0)
              <=> ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X1))
                   => r1_tmap_1(X1,X0,X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tmap_1)).

fof(f172,plain,(
    spl8_4 ),
    inference(avatar_contradiction_clause,[],[f171])).

fof(f171,plain,
    ( $false
    | spl8_4 ),
    inference(subsumption_resolution,[],[f170,f63])).

fof(f170,plain,
    ( ~ m1_pre_topc(sK5,sK4)
    | spl8_4 ),
    inference(subsumption_resolution,[],[f169,f59])).

fof(f169,plain,
    ( v2_struct_0(sK4)
    | ~ m1_pre_topc(sK5,sK4)
    | spl8_4 ),
    inference(subsumption_resolution,[],[f168,f60])).

fof(f168,plain,
    ( ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK5,sK4)
    | spl8_4 ),
    inference(subsumption_resolution,[],[f167,f61])).

fof(f167,plain,
    ( ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK5,sK4)
    | spl8_4 ),
    inference(resolution,[],[f166,f134])).

fof(f134,plain,(
    ! [X0,X1] :
      ( l1_struct_0(k8_tmap_1(X1,X0))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X0,X1) ) ),
    inference(resolution,[],[f83,f68])).

fof(f68,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f166,plain,
    ( ~ l1_struct_0(k8_tmap_1(sK4,sK5))
    | spl8_4 ),
    inference(subsumption_resolution,[],[f165,f129])).

fof(f129,plain,(
    sP2(sK5,sK4) ),
    inference(subsumption_resolution,[],[f128,f59])).

fof(f128,plain,
    ( sP2(sK5,sK4)
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f127,f60])).

fof(f127,plain,
    ( sP2(sK5,sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f125,f61])).

fof(f125,plain,
    ( sP2(sK5,sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4) ),
    inference(resolution,[],[f87,f63])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | sP2(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( sP2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f35,f41])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) )
      | ~ sP2(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_tmap_1)).

fof(f165,plain,
    ( ~ l1_struct_0(k8_tmap_1(sK4,sK5))
    | ~ sP2(sK5,sK4)
    | spl8_4 ),
    inference(subsumption_resolution,[],[f164,f109])).

fof(f109,plain,(
    l1_struct_0(sK4) ),
    inference(resolution,[],[f68,f61])).

fof(f164,plain,
    ( ~ l1_struct_0(k8_tmap_1(sK4,sK5))
    | ~ l1_struct_0(sK4)
    | ~ sP2(sK5,sK4)
    | spl8_4 ),
    inference(subsumption_resolution,[],[f163,f115])).

fof(f115,plain,(
    l1_struct_0(sK6) ),
    inference(resolution,[],[f113,f68])).

fof(f163,plain,
    ( ~ l1_struct_0(sK6)
    | ~ l1_struct_0(k8_tmap_1(sK4,sK5))
    | ~ l1_struct_0(sK4)
    | ~ sP2(sK5,sK4)
    | spl8_4 ),
    inference(resolution,[],[f136,f140])).

fof(f140,plain,(
    ! [X2,X0,X1] :
      ( sP3(k8_tmap_1(X1,X2),X0,k9_tmap_1(X1,X2),X1)
      | ~ l1_struct_0(X0)
      | ~ l1_struct_0(k8_tmap_1(X1,X2))
      | ~ l1_struct_0(X1)
      | ~ sP2(X2,X1) ) ),
    inference(subsumption_resolution,[],[f139,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k9_tmap_1(X1,X0))
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k9_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X0)))))
        & v1_funct_2(k9_tmap_1(X1,X0),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X0)))
        & v1_funct_1(k9_tmap_1(X1,X0)) )
      | ~ sP2(X0,X1) ) ),
    inference(rectify,[],[f55])).

fof(f55,plain,(
    ! [X1,X0] :
      ( ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) )
      | ~ sP2(X1,X0) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f139,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | sP3(k8_tmap_1(X1,X2),X0,k9_tmap_1(X1,X2),X1)
      | ~ v1_funct_1(k9_tmap_1(X1,X2))
      | ~ l1_struct_0(k8_tmap_1(X1,X2))
      | ~ l1_struct_0(X1)
      | ~ sP2(X2,X1) ) ),
    inference(subsumption_resolution,[],[f137,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k9_tmap_1(X1,X0),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X0)))
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f137,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | sP3(k8_tmap_1(X1,X2),X0,k9_tmap_1(X1,X2),X1)
      | ~ v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
      | ~ v1_funct_1(k9_tmap_1(X1,X2))
      | ~ l1_struct_0(k8_tmap_1(X1,X2))
      | ~ l1_struct_0(X1)
      | ~ sP2(X2,X1) ) ),
    inference(resolution,[],[f91,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k9_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X0)))))
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | sP3(X1,X3,X2,X0)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( sP3(X1,X3,X2,X0)
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(definition_folding,[],[f37,f43])).

fof(f43,plain,(
    ! [X1,X3,X2,X0] :
      ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ sP3(X1,X3,X2,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f136,plain,
    ( ~ sP3(k8_tmap_1(sK4,sK5),sK6,k9_tmap_1(sK4,sK5),sK4)
    | spl8_4 ),
    inference(resolution,[],[f107,f90])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ sP3(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k2_tmap_1(X3,X0,X2,X1)) )
      | ~ sP3(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f57])).

fof(f57,plain,(
    ! [X1,X3,X2,X0] :
      ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ sP3(X1,X3,X2,X0) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f107,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(k8_tmap_1(sK4,sK5)))))
    | spl8_4 ),
    inference(avatar_component_clause,[],[f105])).

fof(f162,plain,(
    spl8_2 ),
    inference(avatar_contradiction_clause,[],[f161])).

fof(f161,plain,
    ( $false
    | spl8_2 ),
    inference(subsumption_resolution,[],[f160,f63])).

fof(f160,plain,
    ( ~ m1_pre_topc(sK5,sK4)
    | spl8_2 ),
    inference(subsumption_resolution,[],[f159,f59])).

fof(f159,plain,
    ( v2_struct_0(sK4)
    | ~ m1_pre_topc(sK5,sK4)
    | spl8_2 ),
    inference(subsumption_resolution,[],[f158,f60])).

fof(f158,plain,
    ( ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK5,sK4)
    | spl8_2 ),
    inference(subsumption_resolution,[],[f157,f61])).

fof(f157,plain,
    ( ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK5,sK4)
    | spl8_2 ),
    inference(resolution,[],[f156,f134])).

fof(f156,plain,
    ( ~ l1_struct_0(k8_tmap_1(sK4,sK5))
    | spl8_2 ),
    inference(subsumption_resolution,[],[f155,f129])).

fof(f155,plain,
    ( ~ l1_struct_0(k8_tmap_1(sK4,sK5))
    | ~ sP2(sK5,sK4)
    | spl8_2 ),
    inference(subsumption_resolution,[],[f154,f109])).

fof(f154,plain,
    ( ~ l1_struct_0(k8_tmap_1(sK4,sK5))
    | ~ l1_struct_0(sK4)
    | ~ sP2(sK5,sK4)
    | spl8_2 ),
    inference(subsumption_resolution,[],[f153,f115])).

fof(f153,plain,
    ( ~ l1_struct_0(sK6)
    | ~ l1_struct_0(k8_tmap_1(sK4,sK5))
    | ~ l1_struct_0(sK4)
    | ~ sP2(sK5,sK4)
    | spl8_2 ),
    inference(resolution,[],[f135,f140])).

fof(f135,plain,
    ( ~ sP3(k8_tmap_1(sK4,sK5),sK6,k9_tmap_1(sK4,sK5),sK4)
    | spl8_2 ),
    inference(resolution,[],[f99,f89])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0))
      | ~ sP3(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f99,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK6),u1_struct_0(sK6),u1_struct_0(k8_tmap_1(sK4,sK5)))
    | spl8_2 ),
    inference(avatar_component_clause,[],[f97])).

fof(f152,plain,(
    spl8_1 ),
    inference(avatar_contradiction_clause,[],[f151])).

fof(f151,plain,
    ( $false
    | spl8_1 ),
    inference(subsumption_resolution,[],[f150,f63])).

fof(f150,plain,
    ( ~ m1_pre_topc(sK5,sK4)
    | spl8_1 ),
    inference(subsumption_resolution,[],[f149,f59])).

fof(f149,plain,
    ( v2_struct_0(sK4)
    | ~ m1_pre_topc(sK5,sK4)
    | spl8_1 ),
    inference(subsumption_resolution,[],[f148,f60])).

fof(f148,plain,
    ( ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK5,sK4)
    | spl8_1 ),
    inference(subsumption_resolution,[],[f147,f61])).

fof(f147,plain,
    ( ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK5,sK4)
    | spl8_1 ),
    inference(resolution,[],[f146,f134])).

fof(f146,plain,
    ( ~ l1_struct_0(k8_tmap_1(sK4,sK5))
    | spl8_1 ),
    inference(subsumption_resolution,[],[f145,f129])).

fof(f145,plain,
    ( ~ l1_struct_0(k8_tmap_1(sK4,sK5))
    | ~ sP2(sK5,sK4)
    | spl8_1 ),
    inference(subsumption_resolution,[],[f144,f109])).

fof(f144,plain,
    ( ~ l1_struct_0(k8_tmap_1(sK4,sK5))
    | ~ l1_struct_0(sK4)
    | ~ sP2(sK5,sK4)
    | spl8_1 ),
    inference(subsumption_resolution,[],[f143,f115])).

fof(f143,plain,
    ( ~ l1_struct_0(sK6)
    | ~ l1_struct_0(k8_tmap_1(sK4,sK5))
    | ~ l1_struct_0(sK4)
    | ~ sP2(sK5,sK4)
    | spl8_1 ),
    inference(resolution,[],[f140,f124])).

fof(f124,plain,
    ( ~ sP3(k8_tmap_1(sK4,sK5),sK6,k9_tmap_1(sK4,sK5),sK4)
    | spl8_1 ),
    inference(resolution,[],[f88,f95])).

fof(f95,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK6))
    | spl8_1 ),
    inference(avatar_component_clause,[],[f93])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_tmap_1(X3,X0,X2,X1))
      | ~ sP3(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f108,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f67,f105,f101,f97,f93])).

fof(f67,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(k8_tmap_1(sK4,sK5)))))
    | ~ v5_pre_topc(k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK6),sK6,k8_tmap_1(sK4,sK5))
    | ~ v1_funct_2(k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK6),u1_struct_0(sK6),u1_struct_0(k8_tmap_1(sK4,sK5)))
    | ~ v1_funct_1(k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK6)) ),
    inference(cnf_transformation,[],[f48])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:32:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.48  % (13906)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.21/0.48  % (13915)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.21/0.48  % (13914)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.21/0.49  % (13916)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.21/0.49  % (13908)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.21/0.49  % (13907)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.21/0.49  % (13908)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f265,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f108,f152,f162,f172,f219,f225,f231,f253,f264])).
% 0.21/0.50  fof(f264,plain,(
% 0.21/0.50    ~spl8_7),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f263])).
% 0.21/0.50  fof(f263,plain,(
% 0.21/0.50    $false | ~spl8_7),
% 0.21/0.50    inference(subsumption_resolution,[],[f262,f59])).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    ~v2_struct_0(sK4)),
% 0.21/0.50    inference(cnf_transformation,[],[f48])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    (((~m1_subset_1(k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(k8_tmap_1(sK4,sK5))))) | ~v5_pre_topc(k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK6),sK6,k8_tmap_1(sK4,sK5)) | ~v1_funct_2(k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK6),u1_struct_0(sK6),u1_struct_0(k8_tmap_1(sK4,sK5))) | ~v1_funct_1(k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK6))) & r1_tsep_1(sK5,sK6) & m1_pre_topc(sK6,sK4) & ~v2_struct_0(sK6)) & m1_pre_topc(sK5,sK4) & ~v2_struct_0(sK5)) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f17,f47,f46,f45])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : ((~m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X2,k8_tmap_1(X0,X1)) | ~v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2))) & r1_tsep_1(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~m1_subset_1(k2_tmap_1(sK4,k8_tmap_1(sK4,X1),k9_tmap_1(sK4,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(sK4,X1))))) | ~v5_pre_topc(k2_tmap_1(sK4,k8_tmap_1(sK4,X1),k9_tmap_1(sK4,X1),X2),X2,k8_tmap_1(sK4,X1)) | ~v1_funct_2(k2_tmap_1(sK4,k8_tmap_1(sK4,X1),k9_tmap_1(sK4,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(sK4,X1))) | ~v1_funct_1(k2_tmap_1(sK4,k8_tmap_1(sK4,X1),k9_tmap_1(sK4,X1),X2))) & r1_tsep_1(X1,X2) & m1_pre_topc(X2,sK4) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK4) & ~v2_struct_0(X1)) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    ? [X1] : (? [X2] : ((~m1_subset_1(k2_tmap_1(sK4,k8_tmap_1(sK4,X1),k9_tmap_1(sK4,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(sK4,X1))))) | ~v5_pre_topc(k2_tmap_1(sK4,k8_tmap_1(sK4,X1),k9_tmap_1(sK4,X1),X2),X2,k8_tmap_1(sK4,X1)) | ~v1_funct_2(k2_tmap_1(sK4,k8_tmap_1(sK4,X1),k9_tmap_1(sK4,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(sK4,X1))) | ~v1_funct_1(k2_tmap_1(sK4,k8_tmap_1(sK4,X1),k9_tmap_1(sK4,X1),X2))) & r1_tsep_1(X1,X2) & m1_pre_topc(X2,sK4) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK4) & ~v2_struct_0(X1)) => (? [X2] : ((~m1_subset_1(k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(sK4,sK5))))) | ~v5_pre_topc(k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),X2),X2,k8_tmap_1(sK4,sK5)) | ~v1_funct_2(k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(sK4,sK5))) | ~v1_funct_1(k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),X2))) & r1_tsep_1(sK5,X2) & m1_pre_topc(X2,sK4) & ~v2_struct_0(X2)) & m1_pre_topc(sK5,sK4) & ~v2_struct_0(sK5))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    ? [X2] : ((~m1_subset_1(k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(sK4,sK5))))) | ~v5_pre_topc(k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),X2),X2,k8_tmap_1(sK4,sK5)) | ~v1_funct_2(k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(sK4,sK5))) | ~v1_funct_1(k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),X2))) & r1_tsep_1(sK5,X2) & m1_pre_topc(X2,sK4) & ~v2_struct_0(X2)) => ((~m1_subset_1(k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(k8_tmap_1(sK4,sK5))))) | ~v5_pre_topc(k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK6),sK6,k8_tmap_1(sK4,sK5)) | ~v1_funct_2(k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK6),u1_struct_0(sK6),u1_struct_0(k8_tmap_1(sK4,sK5))) | ~v1_funct_1(k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK6))) & r1_tsep_1(sK5,sK6) & m1_pre_topc(sK6,sK4) & ~v2_struct_0(sK6))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : ((~m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X2,k8_tmap_1(X0,X1)) | ~v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2))) & r1_tsep_1(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (((~m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X2,k8_tmap_1(X0,X1)) | ~v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2))) & r1_tsep_1(X1,X2)) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,negated_conjecture,(
% 0.21/0.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r1_tsep_1(X1,X2) => (m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1))))) & v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X2,k8_tmap_1(X0,X1)) & v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2)))))))),
% 0.21/0.50    inference(negated_conjecture,[],[f12])).
% 0.21/0.50  fof(f12,conjecture,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r1_tsep_1(X1,X2) => (m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1))))) & v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X2,k8_tmap_1(X0,X1)) & v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2)))))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_tmap_1)).
% 0.21/0.50  fof(f262,plain,(
% 0.21/0.50    v2_struct_0(sK4) | ~spl8_7),
% 0.21/0.50    inference(subsumption_resolution,[],[f261,f60])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    v2_pre_topc(sK4)),
% 0.21/0.50    inference(cnf_transformation,[],[f48])).
% 0.21/0.50  fof(f261,plain,(
% 0.21/0.50    ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~spl8_7),
% 0.21/0.50    inference(subsumption_resolution,[],[f260,f61])).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    l1_pre_topc(sK4)),
% 0.21/0.50    inference(cnf_transformation,[],[f48])).
% 0.21/0.50  fof(f260,plain,(
% 0.21/0.50    ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~spl8_7),
% 0.21/0.50    inference(subsumption_resolution,[],[f259,f63])).
% 0.21/0.50  fof(f63,plain,(
% 0.21/0.50    m1_pre_topc(sK5,sK4)),
% 0.21/0.50    inference(cnf_transformation,[],[f48])).
% 0.21/0.50  fof(f259,plain,(
% 0.21/0.50    ~m1_pre_topc(sK5,sK4) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~spl8_7),
% 0.21/0.50    inference(resolution,[],[f206,f80])).
% 0.21/0.50  fof(f80,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v2_struct_0(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ! [X0,X1] : ((v2_pre_topc(k8_tmap_1(X0,X1)) & ~v2_struct_0(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ! [X0,X1] : ((v2_pre_topc(k8_tmap_1(X0,X1)) & ~v2_struct_0(k8_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v2_pre_topc(k8_tmap_1(X0,X1)) & ~v2_struct_0(k8_tmap_1(X0,X1))))),
% 0.21/0.50    inference(pure_predicate_removal,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1)) & ~v2_struct_0(k8_tmap_1(X0,X1))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_tmap_1)).
% 0.21/0.50  fof(f206,plain,(
% 0.21/0.50    v2_struct_0(k8_tmap_1(sK4,sK5)) | ~spl8_7),
% 0.21/0.50    inference(avatar_component_clause,[],[f204])).
% 0.21/0.50  fof(f204,plain,(
% 0.21/0.50    spl8_7 <=> v2_struct_0(k8_tmap_1(sK4,sK5))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.21/0.50  fof(f253,plain,(
% 0.21/0.50    spl8_3 | ~spl8_10),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f252])).
% 0.21/0.50  fof(f252,plain,(
% 0.21/0.50    $false | (spl8_3 | ~spl8_10)),
% 0.21/0.50    inference(subsumption_resolution,[],[f251,f66])).
% 0.21/0.50  fof(f66,plain,(
% 0.21/0.50    r1_tsep_1(sK5,sK6)),
% 0.21/0.50    inference(cnf_transformation,[],[f48])).
% 0.21/0.50  fof(f251,plain,(
% 0.21/0.50    ~r1_tsep_1(sK5,sK6) | (spl8_3 | ~spl8_10)),
% 0.21/0.50    inference(subsumption_resolution,[],[f250,f59])).
% 0.21/0.50  fof(f250,plain,(
% 0.21/0.50    v2_struct_0(sK4) | ~r1_tsep_1(sK5,sK6) | (spl8_3 | ~spl8_10)),
% 0.21/0.50    inference(subsumption_resolution,[],[f249,f60])).
% 0.21/0.50  fof(f249,plain,(
% 0.21/0.50    ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~r1_tsep_1(sK5,sK6) | (spl8_3 | ~spl8_10)),
% 0.21/0.50    inference(subsumption_resolution,[],[f248,f61])).
% 0.21/0.50  fof(f248,plain,(
% 0.21/0.50    ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~r1_tsep_1(sK5,sK6) | (spl8_3 | ~spl8_10)),
% 0.21/0.50    inference(subsumption_resolution,[],[f247,f62])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    ~v2_struct_0(sK5)),
% 0.21/0.50    inference(cnf_transformation,[],[f48])).
% 0.21/0.51  fof(f247,plain,(
% 0.21/0.51    v2_struct_0(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~r1_tsep_1(sK5,sK6) | (spl8_3 | ~spl8_10)),
% 0.21/0.51    inference(subsumption_resolution,[],[f246,f63])).
% 0.21/0.51  fof(f246,plain,(
% 0.21/0.51    ~m1_pre_topc(sK5,sK4) | v2_struct_0(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~r1_tsep_1(sK5,sK6) | (spl8_3 | ~spl8_10)),
% 0.21/0.51    inference(subsumption_resolution,[],[f245,f64])).
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    ~v2_struct_0(sK6)),
% 0.21/0.51    inference(cnf_transformation,[],[f48])).
% 0.21/0.51  fof(f245,plain,(
% 0.21/0.51    v2_struct_0(sK6) | ~m1_pre_topc(sK5,sK4) | v2_struct_0(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~r1_tsep_1(sK5,sK6) | (spl8_3 | ~spl8_10)),
% 0.21/0.51    inference(subsumption_resolution,[],[f242,f65])).
% 0.21/0.51  fof(f65,plain,(
% 0.21/0.51    m1_pre_topc(sK6,sK4)),
% 0.21/0.51    inference(cnf_transformation,[],[f48])).
% 0.21/0.51  fof(f242,plain,(
% 0.21/0.51    ~m1_pre_topc(sK6,sK4) | v2_struct_0(sK6) | ~m1_pre_topc(sK5,sK4) | v2_struct_0(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~r1_tsep_1(sK5,sK6) | (spl8_3 | ~spl8_10)),
% 0.21/0.51    inference(resolution,[],[f241,f235])).
% 0.21/0.51  fof(f235,plain,(
% 0.21/0.51    ~sP0(k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK6),k8_tmap_1(sK4,sK5),sK6) | (spl8_3 | ~spl8_10)),
% 0.21/0.51    inference(subsumption_resolution,[],[f233,f103])).
% 0.21/0.51  fof(f103,plain,(
% 0.21/0.51    ~v5_pre_topc(k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK6),sK6,k8_tmap_1(sK4,sK5)) | spl8_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f101])).
% 0.21/0.51  fof(f101,plain,(
% 0.21/0.51    spl8_3 <=> v5_pre_topc(k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK6),sK6,k8_tmap_1(sK4,sK5))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.21/0.51  fof(f233,plain,(
% 0.21/0.51    ~sP0(k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK6),k8_tmap_1(sK4,sK5),sK6) | v5_pre_topc(k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK6),sK6,k8_tmap_1(sK4,sK5)) | ~spl8_10),
% 0.21/0.51    inference(resolution,[],[f218,f72])).
% 0.21/0.51  fof(f72,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | ~sP0(X2,X1,X0) | v5_pre_topc(X2,X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f50])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (((v5_pre_topc(X2,X0,X1) | ~sP0(X2,X1,X0)) & (sP0(X2,X1,X0) | ~v5_pre_topc(X2,X0,X1))) | ~sP1(X0,X1,X2))),
% 0.21/0.51    inference(rectify,[],[f49])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    ! [X1,X0,X2] : (((v5_pre_topc(X2,X1,X0) | ~sP0(X2,X0,X1)) & (sP0(X2,X0,X1) | ~v5_pre_topc(X2,X1,X0))) | ~sP1(X1,X0,X2))),
% 0.21/0.51    inference(nnf_transformation,[],[f39])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ! [X1,X0,X2] : ((v5_pre_topc(X2,X1,X0) <=> sP0(X2,X0,X1)) | ~sP1(X1,X0,X2))),
% 0.21/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.51  fof(f218,plain,(
% 0.21/0.51    sP1(sK6,k8_tmap_1(sK4,sK5),k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK6)) | ~spl8_10),
% 0.21/0.51    inference(avatar_component_clause,[],[f216])).
% 0.21/0.51  fof(f216,plain,(
% 0.21/0.51    spl8_10 <=> sP1(sK6,k8_tmap_1(sK4,sK5),k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK6))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.21/0.51  fof(f241,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (sP0(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),k8_tmap_1(X0,X1),X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~r1_tsep_1(X1,X2)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f240,f74])).
% 0.21/0.51  fof(f74,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X2)) | sP0(X0,X1,X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f54])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (~r1_tmap_1(X2,X1,X0,sK7(X0,X1,X2)) & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X2)))) & (! [X4] : (r1_tmap_1(X2,X1,X0,X4) | ~m1_subset_1(X4,u1_struct_0(X2))) | ~sP0(X0,X1,X2)))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f52,f53])).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    ! [X2,X1,X0] : (? [X3] : (~r1_tmap_1(X2,X1,X0,X3) & m1_subset_1(X3,u1_struct_0(X2))) => (~r1_tmap_1(X2,X1,X0,sK7(X0,X1,X2)) & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X2))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : (~r1_tmap_1(X2,X1,X0,X3) & m1_subset_1(X3,u1_struct_0(X2)))) & (! [X4] : (r1_tmap_1(X2,X1,X0,X4) | ~m1_subset_1(X4,u1_struct_0(X2))) | ~sP0(X0,X1,X2)))),
% 0.21/0.51    inference(rectify,[],[f51])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    ! [X2,X0,X1] : ((sP0(X2,X0,X1) | ? [X3] : (~r1_tmap_1(X1,X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X3] : (r1_tmap_1(X1,X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X1))) | ~sP0(X2,X0,X1)))),
% 0.21/0.51    inference(nnf_transformation,[],[f38])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ! [X2,X0,X1] : (sP0(X2,X0,X1) <=> ! [X3] : (r1_tmap_1(X1,X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X1))))),
% 0.21/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.51  fof(f240,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(sK7(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),k8_tmap_1(X0,X1),X2),u1_struct_0(X2)) | ~r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | sP0(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),k8_tmap_1(X0,X1),X2)) )),
% 0.21/0.51    inference(resolution,[],[f77,f75])).
% 0.21/0.51  fof(f75,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r1_tmap_1(X2,X1,X0,sK7(X0,X1,X2)) | sP0(X0,X1,X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f54])).
% 0.21/0.51  fof(f77,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3) | ~m1_subset_1(X3,u1_struct_0(X2))) | ~r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : (r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3) | ~m1_subset_1(X3,u1_struct_0(X2))) | ~r1_tsep_1(X1,X2)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,axiom,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r1_tsep_1(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X2)) => r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3))))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_tmap_1)).
% 0.21/0.51  fof(f231,plain,(
% 0.21/0.51    spl8_9),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f230])).
% 0.21/0.51  fof(f230,plain,(
% 0.21/0.51    $false | spl8_9),
% 0.21/0.51    inference(subsumption_resolution,[],[f229,f59])).
% 0.21/0.51  fof(f229,plain,(
% 0.21/0.51    v2_struct_0(sK4) | spl8_9),
% 0.21/0.51    inference(subsumption_resolution,[],[f228,f60])).
% 0.21/0.51  fof(f228,plain,(
% 0.21/0.51    ~v2_pre_topc(sK4) | v2_struct_0(sK4) | spl8_9),
% 0.21/0.51    inference(subsumption_resolution,[],[f227,f61])).
% 0.21/0.51  fof(f227,plain,(
% 0.21/0.51    ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | spl8_9),
% 0.21/0.51    inference(subsumption_resolution,[],[f226,f63])).
% 0.21/0.51  fof(f226,plain,(
% 0.21/0.51    ~m1_pre_topc(sK5,sK4) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | spl8_9),
% 0.21/0.51    inference(resolution,[],[f214,f83])).
% 0.21/0.51  fof(f83,plain,(
% 0.21/0.51    ( ! [X0,X1] : (l1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1))))),
% 0.21/0.51    inference(pure_predicate_removal,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_tmap_1)).
% 0.21/0.51  fof(f214,plain,(
% 0.21/0.51    ~l1_pre_topc(k8_tmap_1(sK4,sK5)) | spl8_9),
% 0.21/0.51    inference(avatar_component_clause,[],[f212])).
% 0.21/0.51  fof(f212,plain,(
% 0.21/0.51    spl8_9 <=> l1_pre_topc(k8_tmap_1(sK4,sK5))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.21/0.51  fof(f225,plain,(
% 0.21/0.51    spl8_8),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f224])).
% 0.21/0.51  fof(f224,plain,(
% 0.21/0.51    $false | spl8_8),
% 0.21/0.51    inference(subsumption_resolution,[],[f223,f59])).
% 0.21/0.51  fof(f223,plain,(
% 0.21/0.51    v2_struct_0(sK4) | spl8_8),
% 0.21/0.51    inference(subsumption_resolution,[],[f222,f60])).
% 0.21/0.51  fof(f222,plain,(
% 0.21/0.51    ~v2_pre_topc(sK4) | v2_struct_0(sK4) | spl8_8),
% 0.21/0.51    inference(subsumption_resolution,[],[f221,f61])).
% 0.21/0.51  fof(f221,plain,(
% 0.21/0.51    ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | spl8_8),
% 0.21/0.51    inference(subsumption_resolution,[],[f220,f63])).
% 0.21/0.51  fof(f220,plain,(
% 0.21/0.51    ~m1_pre_topc(sK5,sK4) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | spl8_8),
% 0.21/0.51    inference(resolution,[],[f210,f81])).
% 0.21/0.51  fof(f81,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v2_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f31])).
% 0.21/0.51  fof(f210,plain,(
% 0.21/0.51    ~v2_pre_topc(k8_tmap_1(sK4,sK5)) | spl8_8),
% 0.21/0.51    inference(avatar_component_clause,[],[f208])).
% 0.21/0.51  fof(f208,plain,(
% 0.21/0.51    spl8_8 <=> v2_pre_topc(k8_tmap_1(sK4,sK5))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.21/0.51  fof(f219,plain,(
% 0.21/0.51    spl8_7 | ~spl8_8 | ~spl8_9 | spl8_10 | ~spl8_1 | ~spl8_2 | ~spl8_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f202,f105,f97,f93,f216,f212,f208,f204])).
% 0.21/0.51  fof(f93,plain,(
% 0.21/0.51    spl8_1 <=> v1_funct_1(k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK6))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.21/0.51  fof(f97,plain,(
% 0.21/0.51    spl8_2 <=> v1_funct_2(k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK6),u1_struct_0(sK6),u1_struct_0(k8_tmap_1(sK4,sK5)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.21/0.51  fof(f105,plain,(
% 0.21/0.51    spl8_4 <=> m1_subset_1(k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(k8_tmap_1(sK4,sK5)))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.21/0.51  fof(f202,plain,(
% 0.21/0.51    sP1(sK6,k8_tmap_1(sK4,sK5),k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK6)) | ~l1_pre_topc(k8_tmap_1(sK4,sK5)) | ~v2_pre_topc(k8_tmap_1(sK4,sK5)) | v2_struct_0(k8_tmap_1(sK4,sK5)) | (~spl8_1 | ~spl8_2 | ~spl8_4)),
% 0.21/0.51    inference(subsumption_resolution,[],[f201,f64])).
% 0.21/0.51  fof(f201,plain,(
% 0.21/0.51    sP1(sK6,k8_tmap_1(sK4,sK5),k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK6)) | v2_struct_0(sK6) | ~l1_pre_topc(k8_tmap_1(sK4,sK5)) | ~v2_pre_topc(k8_tmap_1(sK4,sK5)) | v2_struct_0(k8_tmap_1(sK4,sK5)) | (~spl8_1 | ~spl8_2 | ~spl8_4)),
% 0.21/0.51    inference(subsumption_resolution,[],[f200,f123])).
% 0.21/0.51  fof(f123,plain,(
% 0.21/0.51    v2_pre_topc(sK6)),
% 0.21/0.51    inference(subsumption_resolution,[],[f122,f60])).
% 0.21/0.51  fof(f122,plain,(
% 0.21/0.51    v2_pre_topc(sK6) | ~v2_pre_topc(sK4)),
% 0.21/0.51    inference(subsumption_resolution,[],[f119,f61])).
% 0.21/0.51  fof(f119,plain,(
% 0.21/0.51    v2_pre_topc(sK6) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4)),
% 0.21/0.51    inference(resolution,[],[f78,f65])).
% 0.21/0.51  fof(f78,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.51    inference(flattening,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).
% 0.21/0.51  fof(f200,plain,(
% 0.21/0.51    sP1(sK6,k8_tmap_1(sK4,sK5),k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK6)) | ~v2_pre_topc(sK6) | v2_struct_0(sK6) | ~l1_pre_topc(k8_tmap_1(sK4,sK5)) | ~v2_pre_topc(k8_tmap_1(sK4,sK5)) | v2_struct_0(k8_tmap_1(sK4,sK5)) | (~spl8_1 | ~spl8_2 | ~spl8_4)),
% 0.21/0.51    inference(subsumption_resolution,[],[f199,f113])).
% 0.21/0.51  fof(f113,plain,(
% 0.21/0.51    l1_pre_topc(sK6)),
% 0.21/0.51    inference(subsumption_resolution,[],[f111,f61])).
% 0.21/0.51  fof(f111,plain,(
% 0.21/0.51    l1_pre_topc(sK6) | ~l1_pre_topc(sK4)),
% 0.21/0.51    inference(resolution,[],[f69,f65])).
% 0.21/0.51  fof(f69,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.51  fof(f199,plain,(
% 0.21/0.51    sP1(sK6,k8_tmap_1(sK4,sK5),k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK6)) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6) | ~l1_pre_topc(k8_tmap_1(sK4,sK5)) | ~v2_pre_topc(k8_tmap_1(sK4,sK5)) | v2_struct_0(k8_tmap_1(sK4,sK5)) | (~spl8_1 | ~spl8_2 | ~spl8_4)),
% 0.21/0.51    inference(subsumption_resolution,[],[f198,f94])).
% 0.21/0.51  fof(f94,plain,(
% 0.21/0.51    v1_funct_1(k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK6)) | ~spl8_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f93])).
% 0.21/0.51  fof(f198,plain,(
% 0.21/0.51    sP1(sK6,k8_tmap_1(sK4,sK5),k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK6)) | ~v1_funct_1(k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK6)) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6) | ~l1_pre_topc(k8_tmap_1(sK4,sK5)) | ~v2_pre_topc(k8_tmap_1(sK4,sK5)) | v2_struct_0(k8_tmap_1(sK4,sK5)) | (~spl8_2 | ~spl8_4)),
% 0.21/0.51    inference(subsumption_resolution,[],[f193,f98])).
% 0.21/0.51  fof(f98,plain,(
% 0.21/0.51    v1_funct_2(k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK6),u1_struct_0(sK6),u1_struct_0(k8_tmap_1(sK4,sK5))) | ~spl8_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f97])).
% 0.21/0.51  fof(f193,plain,(
% 0.21/0.51    sP1(sK6,k8_tmap_1(sK4,sK5),k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK6)) | ~v1_funct_2(k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK6),u1_struct_0(sK6),u1_struct_0(k8_tmap_1(sK4,sK5))) | ~v1_funct_1(k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK6)) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6) | ~l1_pre_topc(k8_tmap_1(sK4,sK5)) | ~v2_pre_topc(k8_tmap_1(sK4,sK5)) | v2_struct_0(k8_tmap_1(sK4,sK5)) | ~spl8_4),
% 0.21/0.51    inference(resolution,[],[f76,f106])).
% 0.21/0.51  fof(f106,plain,(
% 0.21/0.51    m1_subset_1(k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(k8_tmap_1(sK4,sK5))))) | ~spl8_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f105])).
% 0.21/0.51  fof(f76,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | sP1(X1,X0,X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f40])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (sP1(X1,X0,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(definition_folding,[],[f23,f39,f38])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X1,X0) <=> ! [X3] : (r1_tmap_1(X1,X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X1,X0) <=> ! [X3] : (r1_tmap_1(X1,X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,axiom,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (v5_pre_topc(X2,X1,X0) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => r1_tmap_1(X1,X0,X2,X3))))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tmap_1)).
% 0.21/0.51  fof(f172,plain,(
% 0.21/0.51    spl8_4),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f171])).
% 0.21/0.51  fof(f171,plain,(
% 0.21/0.51    $false | spl8_4),
% 0.21/0.51    inference(subsumption_resolution,[],[f170,f63])).
% 0.21/0.51  fof(f170,plain,(
% 0.21/0.51    ~m1_pre_topc(sK5,sK4) | spl8_4),
% 0.21/0.51    inference(subsumption_resolution,[],[f169,f59])).
% 0.21/0.51  fof(f169,plain,(
% 0.21/0.51    v2_struct_0(sK4) | ~m1_pre_topc(sK5,sK4) | spl8_4),
% 0.21/0.51    inference(subsumption_resolution,[],[f168,f60])).
% 0.21/0.51  fof(f168,plain,(
% 0.21/0.51    ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~m1_pre_topc(sK5,sK4) | spl8_4),
% 0.21/0.51    inference(subsumption_resolution,[],[f167,f61])).
% 0.21/0.51  fof(f167,plain,(
% 0.21/0.51    ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~m1_pre_topc(sK5,sK4) | spl8_4),
% 0.21/0.51    inference(resolution,[],[f166,f134])).
% 0.21/0.51  fof(f134,plain,(
% 0.21/0.51    ( ! [X0,X1] : (l1_struct_0(k8_tmap_1(X1,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~m1_pre_topc(X0,X1)) )),
% 0.21/0.51    inference(resolution,[],[f83,f68])).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.51  fof(f166,plain,(
% 0.21/0.51    ~l1_struct_0(k8_tmap_1(sK4,sK5)) | spl8_4),
% 0.21/0.51    inference(subsumption_resolution,[],[f165,f129])).
% 0.21/0.51  fof(f129,plain,(
% 0.21/0.51    sP2(sK5,sK4)),
% 0.21/0.51    inference(subsumption_resolution,[],[f128,f59])).
% 0.21/0.51  fof(f128,plain,(
% 0.21/0.51    sP2(sK5,sK4) | v2_struct_0(sK4)),
% 0.21/0.51    inference(subsumption_resolution,[],[f127,f60])).
% 0.21/0.51  fof(f127,plain,(
% 0.21/0.51    sP2(sK5,sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)),
% 0.21/0.51    inference(subsumption_resolution,[],[f125,f61])).
% 0.21/0.51  fof(f125,plain,(
% 0.21/0.51    sP2(sK5,sK4) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)),
% 0.21/0.51    inference(resolution,[],[f87,f63])).
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | sP2(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f42])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ! [X0,X1] : (sP2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(definition_folding,[],[f35,f41])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ! [X1,X0] : ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | ~sP2(X1,X0))),
% 0.21/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ! [X0,X1] : ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ! [X0,X1] : ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_tmap_1)).
% 0.21/0.51  fof(f165,plain,(
% 0.21/0.51    ~l1_struct_0(k8_tmap_1(sK4,sK5)) | ~sP2(sK5,sK4) | spl8_4),
% 0.21/0.51    inference(subsumption_resolution,[],[f164,f109])).
% 0.21/0.51  fof(f109,plain,(
% 0.21/0.51    l1_struct_0(sK4)),
% 0.21/0.51    inference(resolution,[],[f68,f61])).
% 0.21/0.51  fof(f164,plain,(
% 0.21/0.51    ~l1_struct_0(k8_tmap_1(sK4,sK5)) | ~l1_struct_0(sK4) | ~sP2(sK5,sK4) | spl8_4),
% 0.21/0.51    inference(subsumption_resolution,[],[f163,f115])).
% 0.21/0.51  fof(f115,plain,(
% 0.21/0.51    l1_struct_0(sK6)),
% 0.21/0.51    inference(resolution,[],[f113,f68])).
% 0.21/0.51  fof(f163,plain,(
% 0.21/0.51    ~l1_struct_0(sK6) | ~l1_struct_0(k8_tmap_1(sK4,sK5)) | ~l1_struct_0(sK4) | ~sP2(sK5,sK4) | spl8_4),
% 0.21/0.51    inference(resolution,[],[f136,f140])).
% 0.21/0.51  fof(f140,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (sP3(k8_tmap_1(X1,X2),X0,k9_tmap_1(X1,X2),X1) | ~l1_struct_0(X0) | ~l1_struct_0(k8_tmap_1(X1,X2)) | ~l1_struct_0(X1) | ~sP2(X2,X1)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f139,f84])).
% 0.21/0.51  fof(f84,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v1_funct_1(k9_tmap_1(X1,X0)) | ~sP2(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f56])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    ! [X0,X1] : ((m1_subset_1(k9_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X0))))) & v1_funct_2(k9_tmap_1(X1,X0),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X0))) & v1_funct_1(k9_tmap_1(X1,X0))) | ~sP2(X0,X1))),
% 0.21/0.51    inference(rectify,[],[f55])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    ! [X1,X0] : ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | ~sP2(X1,X0))),
% 0.21/0.51    inference(nnf_transformation,[],[f41])).
% 0.21/0.51  fof(f139,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~l1_struct_0(X0) | sP3(k8_tmap_1(X1,X2),X0,k9_tmap_1(X1,X2),X1) | ~v1_funct_1(k9_tmap_1(X1,X2)) | ~l1_struct_0(k8_tmap_1(X1,X2)) | ~l1_struct_0(X1) | ~sP2(X2,X1)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f137,f85])).
% 0.21/0.51  fof(f85,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v1_funct_2(k9_tmap_1(X1,X0),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X0))) | ~sP2(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f56])).
% 0.21/0.51  fof(f137,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~l1_struct_0(X0) | sP3(k8_tmap_1(X1,X2),X0,k9_tmap_1(X1,X2),X1) | ~v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))) | ~v1_funct_1(k9_tmap_1(X1,X2)) | ~l1_struct_0(k8_tmap_1(X1,X2)) | ~l1_struct_0(X1) | ~sP2(X2,X1)) )),
% 0.21/0.51    inference(resolution,[],[f91,f86])).
% 0.21/0.51  fof(f86,plain,(
% 0.21/0.51    ( ! [X0,X1] : (m1_subset_1(k9_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X0))))) | ~sP2(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f56])).
% 0.21/0.51  fof(f91,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~l1_struct_0(X3) | sP3(X1,X3,X2,X0) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f44])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (sP3(X1,X3,X2,X0) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 0.21/0.51    inference(definition_folding,[],[f37,f43])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    ! [X1,X3,X2,X0] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | ~sP3(X1,X3,X2,X0))),
% 0.21/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f36])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3] : ((l1_struct_0(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2) & l1_struct_0(X1) & l1_struct_0(X0)) => (m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tmap_1)).
% 0.21/0.51  fof(f136,plain,(
% 0.21/0.51    ~sP3(k8_tmap_1(sK4,sK5),sK6,k9_tmap_1(sK4,sK5),sK4) | spl8_4),
% 0.21/0.51    inference(resolution,[],[f107,f90])).
% 0.21/0.51  fof(f90,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~sP3(X0,X1,X2,X3)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f58])).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k2_tmap_1(X3,X0,X2,X1))) | ~sP3(X0,X1,X2,X3))),
% 0.21/0.51    inference(rectify,[],[f57])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    ! [X1,X3,X2,X0] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | ~sP3(X1,X3,X2,X0))),
% 0.21/0.51    inference(nnf_transformation,[],[f43])).
% 0.21/0.51  fof(f107,plain,(
% 0.21/0.51    ~m1_subset_1(k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(k8_tmap_1(sK4,sK5))))) | spl8_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f105])).
% 0.21/0.51  fof(f162,plain,(
% 0.21/0.51    spl8_2),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f161])).
% 0.21/0.51  fof(f161,plain,(
% 0.21/0.51    $false | spl8_2),
% 0.21/0.51    inference(subsumption_resolution,[],[f160,f63])).
% 0.21/0.51  fof(f160,plain,(
% 0.21/0.51    ~m1_pre_topc(sK5,sK4) | spl8_2),
% 0.21/0.51    inference(subsumption_resolution,[],[f159,f59])).
% 0.21/0.51  fof(f159,plain,(
% 0.21/0.51    v2_struct_0(sK4) | ~m1_pre_topc(sK5,sK4) | spl8_2),
% 0.21/0.51    inference(subsumption_resolution,[],[f158,f60])).
% 0.21/0.51  fof(f158,plain,(
% 0.21/0.51    ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~m1_pre_topc(sK5,sK4) | spl8_2),
% 0.21/0.51    inference(subsumption_resolution,[],[f157,f61])).
% 0.21/0.51  fof(f157,plain,(
% 0.21/0.51    ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~m1_pre_topc(sK5,sK4) | spl8_2),
% 0.21/0.51    inference(resolution,[],[f156,f134])).
% 0.21/0.51  fof(f156,plain,(
% 0.21/0.51    ~l1_struct_0(k8_tmap_1(sK4,sK5)) | spl8_2),
% 0.21/0.51    inference(subsumption_resolution,[],[f155,f129])).
% 0.21/0.51  fof(f155,plain,(
% 0.21/0.51    ~l1_struct_0(k8_tmap_1(sK4,sK5)) | ~sP2(sK5,sK4) | spl8_2),
% 0.21/0.51    inference(subsumption_resolution,[],[f154,f109])).
% 0.21/0.51  fof(f154,plain,(
% 0.21/0.51    ~l1_struct_0(k8_tmap_1(sK4,sK5)) | ~l1_struct_0(sK4) | ~sP2(sK5,sK4) | spl8_2),
% 0.21/0.51    inference(subsumption_resolution,[],[f153,f115])).
% 0.21/0.51  fof(f153,plain,(
% 0.21/0.51    ~l1_struct_0(sK6) | ~l1_struct_0(k8_tmap_1(sK4,sK5)) | ~l1_struct_0(sK4) | ~sP2(sK5,sK4) | spl8_2),
% 0.21/0.51    inference(resolution,[],[f135,f140])).
% 0.21/0.51  fof(f135,plain,(
% 0.21/0.51    ~sP3(k8_tmap_1(sK4,sK5),sK6,k9_tmap_1(sK4,sK5),sK4) | spl8_2),
% 0.21/0.51    inference(resolution,[],[f99,f89])).
% 0.21/0.51  fof(f89,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0)) | ~sP3(X0,X1,X2,X3)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f58])).
% 0.21/0.51  fof(f99,plain,(
% 0.21/0.51    ~v1_funct_2(k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK6),u1_struct_0(sK6),u1_struct_0(k8_tmap_1(sK4,sK5))) | spl8_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f97])).
% 0.21/0.51  fof(f152,plain,(
% 0.21/0.51    spl8_1),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f151])).
% 0.21/0.51  fof(f151,plain,(
% 0.21/0.51    $false | spl8_1),
% 0.21/0.51    inference(subsumption_resolution,[],[f150,f63])).
% 0.21/0.51  fof(f150,plain,(
% 0.21/0.51    ~m1_pre_topc(sK5,sK4) | spl8_1),
% 0.21/0.51    inference(subsumption_resolution,[],[f149,f59])).
% 0.21/0.51  fof(f149,plain,(
% 0.21/0.51    v2_struct_0(sK4) | ~m1_pre_topc(sK5,sK4) | spl8_1),
% 0.21/0.51    inference(subsumption_resolution,[],[f148,f60])).
% 0.21/0.51  fof(f148,plain,(
% 0.21/0.51    ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~m1_pre_topc(sK5,sK4) | spl8_1),
% 0.21/0.51    inference(subsumption_resolution,[],[f147,f61])).
% 0.21/0.51  fof(f147,plain,(
% 0.21/0.51    ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~m1_pre_topc(sK5,sK4) | spl8_1),
% 0.21/0.51    inference(resolution,[],[f146,f134])).
% 0.21/0.51  fof(f146,plain,(
% 0.21/0.51    ~l1_struct_0(k8_tmap_1(sK4,sK5)) | spl8_1),
% 0.21/0.51    inference(subsumption_resolution,[],[f145,f129])).
% 0.21/0.51  fof(f145,plain,(
% 0.21/0.51    ~l1_struct_0(k8_tmap_1(sK4,sK5)) | ~sP2(sK5,sK4) | spl8_1),
% 0.21/0.51    inference(subsumption_resolution,[],[f144,f109])).
% 0.21/0.51  fof(f144,plain,(
% 0.21/0.51    ~l1_struct_0(k8_tmap_1(sK4,sK5)) | ~l1_struct_0(sK4) | ~sP2(sK5,sK4) | spl8_1),
% 0.21/0.51    inference(subsumption_resolution,[],[f143,f115])).
% 0.21/0.51  fof(f143,plain,(
% 0.21/0.51    ~l1_struct_0(sK6) | ~l1_struct_0(k8_tmap_1(sK4,sK5)) | ~l1_struct_0(sK4) | ~sP2(sK5,sK4) | spl8_1),
% 0.21/0.51    inference(resolution,[],[f140,f124])).
% 0.21/0.51  fof(f124,plain,(
% 0.21/0.51    ~sP3(k8_tmap_1(sK4,sK5),sK6,k9_tmap_1(sK4,sK5),sK4) | spl8_1),
% 0.21/0.51    inference(resolution,[],[f88,f95])).
% 0.21/0.51  fof(f95,plain,(
% 0.21/0.51    ~v1_funct_1(k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK6)) | spl8_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f93])).
% 0.21/0.51  fof(f88,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_tmap_1(X3,X0,X2,X1)) | ~sP3(X0,X1,X2,X3)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f58])).
% 0.21/0.51  fof(f108,plain,(
% 0.21/0.51    ~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f67,f105,f101,f97,f93])).
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    ~m1_subset_1(k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(k8_tmap_1(sK4,sK5))))) | ~v5_pre_topc(k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK6),sK6,k8_tmap_1(sK4,sK5)) | ~v1_funct_2(k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK6),u1_struct_0(sK6),u1_struct_0(k8_tmap_1(sK4,sK5))) | ~v1_funct_1(k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK6))),
% 0.21/0.51    inference(cnf_transformation,[],[f48])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (13908)------------------------------
% 0.21/0.51  % (13908)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (13908)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (13908)Memory used [KB]: 5500
% 0.21/0.51  % (13908)Time elapsed: 0.077 s
% 0.21/0.51  % (13908)------------------------------
% 0.21/0.51  % (13908)------------------------------
% 0.21/0.51  % (13900)Success in time 0.15 s
%------------------------------------------------------------------------------
