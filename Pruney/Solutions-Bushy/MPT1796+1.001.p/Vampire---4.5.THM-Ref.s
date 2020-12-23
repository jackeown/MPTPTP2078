%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1796+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:34 EST 2020

% Result     : Theorem 1.55s
% Output     : Refutation 1.55s
% Verified   : 
% Statistics : Number of formulae       :  199 (1860 expanded)
%              Number of leaves         :   37 ( 745 expanded)
%              Depth                    :   16
%              Number of atoms          :  907 (18594 expanded)
%              Number of equality atoms :   25 (1832 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f767,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f101,f154,f181,f295,f319,f324,f413,f434,f447,f452,f454,f456,f472,f479,f542,f544,f546,f549,f754,f760,f762,f766])).

fof(f766,plain,
    ( spl4_4
    | ~ spl4_28 ),
    inference(avatar_contradiction_clause,[],[f765])).

fof(f765,plain,
    ( $false
    | spl4_4
    | ~ spl4_28 ),
    inference(subsumption_resolution,[],[f541,f764])).

fof(f764,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_relat_1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | spl4_4 ),
    inference(forward_demodulation,[],[f763,f178])).

fof(f178,plain,(
    k7_tmap_1(sK0,sK1) = k6_relat_1(u1_struct_0(sK0)) ),
    inference(global_subsumption,[],[f53,f54,f55,f170])).

fof(f170,plain,
    ( k7_tmap_1(sK0,sK1) = k6_relat_1(u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f56,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k7_tmap_1(X0,X1) = k6_relat_1(u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f66,f63])).

fof(f63,plain,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f66,plain,(
    ! [X0,X1] :
      ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
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
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_tmap_1)).

fof(f56,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,
    ( ( ~ m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1)))))
      | ~ v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),sK2,k6_tmap_1(sK0,sK1))
      | ~ v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1)))
      | ~ v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2)) )
    & sK1 = u1_struct_0(sK2)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f47,f46,f45])).

fof(f45,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))))
                  | ~ v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
                  | ~ v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
                  | ~ v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)) )
                & u1_struct_0(X2) = X1
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(sK0,X1)))))
                | ~ v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),X2),X2,k6_tmap_1(sK0,X1))
                | ~ v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(sK0,X1)))
                | ~ v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),X2)) )
              & u1_struct_0(X2) = X1
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(sK0,X1)))))
              | ~ v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),X2),X2,k6_tmap_1(sK0,X1))
              | ~ v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(sK0,X1)))
              | ~ v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),X2)) )
            & u1_struct_0(X2) = X1
            & m1_pre_topc(X2,sK0)
            & ~ v2_struct_0(X2) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ( ~ m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(sK0,sK1)))))
            | ~ v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X2),X2,k6_tmap_1(sK0,sK1))
            | ~ v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(sK0,sK1)))
            | ~ v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X2)) )
          & u1_struct_0(X2) = sK1
          & m1_pre_topc(X2,sK0)
          & ~ v2_struct_0(X2) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ? [X2] :
        ( ( ~ m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(sK0,sK1)))))
          | ~ v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X2),X2,k6_tmap_1(sK0,sK1))
          | ~ v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(sK0,sK1)))
          | ~ v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X2)) )
        & u1_struct_0(X2) = sK1
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ( ~ m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1)))))
        | ~ v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),sK2,k6_tmap_1(sK0,sK1))
        | ~ v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1)))
        | ~ v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2)) )
      & sK1 = u1_struct_0(sK2)
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))))
                | ~ v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
                | ~ v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
                | ~ v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)) )
              & u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))))
                | ~ v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
                | ~ v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
                | ~ v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)) )
              & u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
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
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ( u1_struct_0(X2) = X1
                 => ( m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))))
                    & v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
                    & v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
                    & v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( u1_struct_0(X2) = X1
               => ( m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))))
                  & v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
                  & v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
                  & v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_tmap_1)).

fof(f55,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f54,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f53,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f763,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | spl4_4 ),
    inference(forward_demodulation,[],[f100,f59])).

fof(f59,plain,(
    sK1 = u1_struct_0(sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f100,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | spl4_4 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl4_4
  <=> m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f541,plain,
    ( m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_relat_1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f428])).

fof(f428,plain,
    ( spl4_28
  <=> m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_relat_1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,u1_struct_0(k6_tmap_1(sK0,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f762,plain,
    ( spl4_3
    | ~ spl4_25 ),
    inference(avatar_contradiction_clause,[],[f761])).

fof(f761,plain,
    ( $false
    | spl4_3
    | ~ spl4_25 ),
    inference(subsumption_resolution,[],[f457,f420])).

fof(f420,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_relat_1(u1_struct_0(sK0)),sK2),sK2,k6_tmap_1(sK0,sK1))
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f419])).

fof(f419,plain,
    ( spl4_25
  <=> v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_relat_1(u1_struct_0(sK0)),sK2),sK2,k6_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f457,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_relat_1(u1_struct_0(sK0)),sK2),sK2,k6_tmap_1(sK0,sK1))
    | spl4_3 ),
    inference(forward_demodulation,[],[f97,f178])).

fof(f97,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),sK2,k6_tmap_1(sK0,sK1))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl4_3
  <=> v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),sK2,k6_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f760,plain,
    ( ~ spl4_29
    | ~ spl4_30
    | ~ spl4_31
    | ~ spl4_16
    | ~ spl4_15
    | ~ spl4_9
    | spl4_27 ),
    inference(avatar_split_clause,[],[f759,f425,f152,f287,f290,f445,f442,f439])).

fof(f439,plain,
    ( spl4_29
  <=> m1_subset_1(k6_relat_1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f442,plain,
    ( spl4_30
  <=> v1_funct_2(k6_relat_1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f445,plain,
    ( spl4_31
  <=> v1_funct_1(k6_relat_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f290,plain,
    ( spl4_16
  <=> l1_struct_0(k6_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f287,plain,
    ( spl4_15
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f152,plain,
    ( spl4_9
  <=> ! [X27,X26,X28] :
        ( v1_funct_2(k2_tmap_1(X26,X27,X28,sK2),sK1,u1_struct_0(X27))
        | ~ l1_struct_0(X26)
        | ~ l1_struct_0(X27)
        | ~ v1_funct_1(X28)
        | ~ v1_funct_2(X28,u1_struct_0(X26),u1_struct_0(X27))
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X26),u1_struct_0(X27)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f425,plain,
    ( spl4_27
  <=> v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_relat_1(u1_struct_0(sK0)),sK2),sK1,u1_struct_0(k6_tmap_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f759,plain,
    ( ~ l1_struct_0(sK0)
    | ~ l1_struct_0(k6_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k6_relat_1(u1_struct_0(sK0)))
    | ~ v1_funct_2(k6_relat_1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k6_relat_1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ spl4_9
    | spl4_27 ),
    inference(resolution,[],[f426,f153])).

fof(f153,plain,
    ( ! [X28,X26,X27] :
        ( v1_funct_2(k2_tmap_1(X26,X27,X28,sK2),sK1,u1_struct_0(X27))
        | ~ l1_struct_0(X26)
        | ~ l1_struct_0(X27)
        | ~ v1_funct_1(X28)
        | ~ v1_funct_2(X28,u1_struct_0(X26),u1_struct_0(X27))
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X26),u1_struct_0(X27)))) )
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f152])).

fof(f426,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_relat_1(u1_struct_0(sK0)),sK2),sK1,u1_struct_0(k6_tmap_1(sK0,sK1)))
    | spl4_27 ),
    inference(avatar_component_clause,[],[f425])).

fof(f754,plain,
    ( spl4_34
    | ~ spl4_35
    | ~ spl4_36
    | ~ spl4_24
    | ~ spl4_27
    | spl4_25
    | spl4_26
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f745,f428,f422,f419,f425,f416,f531,f528,f525])).

fof(f525,plain,
    ( spl4_34
  <=> v2_struct_0(k6_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f528,plain,
    ( spl4_35
  <=> v2_pre_topc(k6_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f531,plain,
    ( spl4_36
  <=> l1_pre_topc(k6_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f416,plain,
    ( spl4_24
  <=> v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_relat_1(u1_struct_0(sK0)),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f422,plain,
    ( spl4_26
  <=> m1_subset_1(sK3(k6_tmap_1(sK0,sK1),sK2,k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_relat_1(u1_struct_0(sK0)),sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f745,plain,
    ( m1_subset_1(sK3(k6_tmap_1(sK0,sK1),sK2,k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_relat_1(u1_struct_0(sK0)),sK2)),sK1)
    | v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_relat_1(u1_struct_0(sK0)),sK2),sK2,k6_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_relat_1(u1_struct_0(sK0)),sK2),sK1,u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_relat_1(u1_struct_0(sK0)),sK2))
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(k6_tmap_1(sK0,sK1))
    | v2_struct_0(k6_tmap_1(sK0,sK1))
    | ~ spl4_28 ),
    inference(resolution,[],[f541,f128])).

fof(f128,plain,(
    ! [X8,X9] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(sK1,u1_struct_0(X9))))
      | m1_subset_1(sK3(X9,sK2,X8),sK1)
      | v5_pre_topc(X8,sK2,X9)
      | ~ v1_funct_2(X8,sK1,u1_struct_0(X9))
      | ~ v1_funct_1(X8)
      | ~ l1_pre_topc(X9)
      | ~ v2_pre_topc(X9)
      | v2_struct_0(X9) ) ),
    inference(global_subsumption,[],[f57,f104,f105,f109])).

fof(f109,plain,(
    ! [X8,X9] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(sK1,u1_struct_0(X9))))
      | m1_subset_1(sK3(X9,sK2,X8),sK1)
      | v5_pre_topc(X8,sK2,X9)
      | ~ v1_funct_2(X8,sK1,u1_struct_0(X9))
      | ~ v1_funct_1(X8)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2)
      | ~ l1_pre_topc(X9)
      | ~ v2_pre_topc(X9)
      | v2_struct_0(X9) ) ),
    inference(superposition,[],[f69,f59])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))
      | v5_pre_topc(X2,X1,X0)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X1,X0)
                  | ( ~ r1_tmap_1(X1,X0,X2,sK3(X0,X1,X2))
                    & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1)) ) )
                & ( ! [X4] :
                      ( r1_tmap_1(X1,X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ v5_pre_topc(X2,X1,X0) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f50,f51])).

fof(f51,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_tmap_1(X1,X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_tmap_1(X1,X0,X2,sK3(X0,X1,X2))
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X1,X0)
                  | ? [X3] :
                      ( ~ r1_tmap_1(X1,X0,X2,X3)
                      & m1_subset_1(X3,u1_struct_0(X1)) ) )
                & ( ! [X4] :
                      ( r1_tmap_1(X1,X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ v5_pre_topc(X2,X1,X0) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X1,X0)
                  | ? [X3] :
                      ( ~ r1_tmap_1(X1,X0,X2,X3)
                      & m1_subset_1(X3,u1_struct_0(X1)) ) )
                & ( ! [X3] :
                      ( r1_tmap_1(X1,X0,X2,X3)
                      | ~ m1_subset_1(X3,u1_struct_0(X1)) )
                  | ~ v5_pre_topc(X2,X1,X0) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_tmap_1)).

fof(f105,plain,(
    l1_pre_topc(sK2) ),
    inference(global_subsumption,[],[f55,f103])).

fof(f103,plain,
    ( l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f58,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f58,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f104,plain,(
    v2_pre_topc(sK2) ),
    inference(global_subsumption,[],[f54,f55,f102])).

fof(f102,plain,
    ( v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f58,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f57,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f549,plain,(
    ~ spl4_34 ),
    inference(avatar_contradiction_clause,[],[f548])).

fof(f548,plain,
    ( $false
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f176,f526])).

fof(f526,plain,
    ( v2_struct_0(k6_tmap_1(sK0,sK1))
    | ~ spl4_34 ),
    inference(avatar_component_clause,[],[f525])).

fof(f176,plain,(
    ~ v2_struct_0(k6_tmap_1(sK0,sK1)) ),
    inference(global_subsumption,[],[f53,f54,f55,f168])).

fof(f168,plain,
    ( ~ v2_struct_0(k6_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f56,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_struct_0(k6_tmap_1(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v2_pre_topc(k6_tmap_1(X0,X1))
        & ~ v2_struct_0(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v2_pre_topc(k6_tmap_1(X0,X1))
        & ~ v2_struct_0(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_pre_topc(k6_tmap_1(X0,X1))
        & ~ v2_struct_0(k6_tmap_1(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1))
        & ~ v2_struct_0(k6_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_tmap_1)).

fof(f546,plain,(
    spl4_36 ),
    inference(avatar_contradiction_clause,[],[f545])).

fof(f545,plain,
    ( $false
    | spl4_36 ),
    inference(subsumption_resolution,[],[f175,f532])).

fof(f532,plain,
    ( ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | spl4_36 ),
    inference(avatar_component_clause,[],[f531])).

fof(f175,plain,(
    l1_pre_topc(k6_tmap_1(sK0,sK1)) ),
    inference(global_subsumption,[],[f53,f54,f55,f167])).

fof(f167,plain,
    ( l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f56,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | l1_pre_topc(k6_tmap_1(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_tmap_1)).

fof(f544,plain,(
    spl4_35 ),
    inference(avatar_contradiction_clause,[],[f543])).

fof(f543,plain,
    ( $false
    | spl4_35 ),
    inference(subsumption_resolution,[],[f174,f529])).

fof(f529,plain,
    ( ~ v2_pre_topc(k6_tmap_1(sK0,sK1))
    | spl4_35 ),
    inference(avatar_component_clause,[],[f528])).

fof(f174,plain,(
    v2_pre_topc(k6_tmap_1(sK0,sK1)) ),
    inference(global_subsumption,[],[f53,f54,f55,f166])).

fof(f166,plain,
    ( v2_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f56,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_pre_topc(k6_tmap_1(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f542,plain,
    ( ~ spl4_5
    | spl4_28
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f513,f298,f428,f137])).

fof(f137,plain,
    ( spl4_5
  <=> l1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f298,plain,
    ( spl4_18
  <=> ! [X1] :
        ( ~ l1_struct_0(X1)
        | m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_relat_1(u1_struct_0(sK0)),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(sK0,sK1))))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f513,plain,
    ( m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_relat_1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ l1_struct_0(sK2)
    | ~ spl4_18 ),
    inference(superposition,[],[f299,f59])).

fof(f299,plain,
    ( ! [X1] :
        ( m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_relat_1(u1_struct_0(sK0)),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(sK0,sK1)))))
        | ~ l1_struct_0(X1) )
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f298])).

fof(f479,plain,
    ( ~ spl4_17
    | spl4_24 ),
    inference(avatar_contradiction_clause,[],[f478])).

fof(f478,plain,
    ( $false
    | ~ spl4_17
    | spl4_24 ),
    inference(subsumption_resolution,[],[f105,f475])).

fof(f475,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ spl4_17
    | spl4_24 ),
    inference(resolution,[],[f473,f64])).

fof(f64,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f473,plain,
    ( ~ l1_struct_0(sK2)
    | ~ spl4_17
    | spl4_24 ),
    inference(resolution,[],[f417,f294])).

fof(f294,plain,
    ( ! [X0] :
        ( v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_relat_1(u1_struct_0(sK0)),X0))
        | ~ l1_struct_0(X0) )
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f293])).

fof(f293,plain,
    ( spl4_17
  <=> ! [X0] :
        ( ~ l1_struct_0(X0)
        | v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_relat_1(u1_struct_0(sK0)),X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f417,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_relat_1(u1_struct_0(sK0)),sK2))
    | spl4_24 ),
    inference(avatar_component_clause,[],[f416])).

fof(f472,plain,
    ( ~ spl4_15
    | ~ spl4_16
    | spl4_18 ),
    inference(avatar_split_clause,[],[f471,f298,f290,f287])).

fof(f471,plain,(
    ! [X1] :
      ( ~ l1_struct_0(X1)
      | m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_relat_1(u1_struct_0(sK0)),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(sK0,sK1)))))
      | ~ l1_struct_0(k6_tmap_1(sK0,sK1))
      | ~ l1_struct_0(sK0) ) ),
    inference(global_subsumption,[],[f182,f186,f466])).

fof(f466,plain,(
    ! [X1] :
      ( ~ l1_struct_0(X1)
      | m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_relat_1(u1_struct_0(sK0)),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(sK0,sK1)))))
      | ~ v1_funct_2(k6_relat_1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
      | ~ v1_funct_1(k6_relat_1(u1_struct_0(sK0)))
      | ~ l1_struct_0(k6_tmap_1(sK0,sK1))
      | ~ l1_struct_0(sK0) ) ),
    inference(resolution,[],[f187,f85])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f43,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tmap_1)).

fof(f187,plain,(
    m1_subset_1(k6_relat_1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) ),
    inference(global_subsumption,[],[f53,f54,f55,f56,f185])).

fof(f185,plain,
    ( m1_subset_1(k6_relat_1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f79,f178])).

fof(f79,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_tmap_1)).

fof(f186,plain,(
    v1_funct_2(k6_relat_1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) ),
    inference(global_subsumption,[],[f53,f54,f55,f56,f184])).

fof(f184,plain,
    ( v1_funct_2(k6_relat_1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f78,f178])).

fof(f78,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f182,plain,(
    v1_funct_1(k6_relat_1(u1_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f173,f178])).

fof(f173,plain,(
    v1_funct_1(k7_tmap_1(sK0,sK1)) ),
    inference(global_subsumption,[],[f53,f54,f55,f165])).

fof(f165,plain,
    ( v1_funct_1(k7_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f56,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_funct_1(k7_tmap_1(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f456,plain,(
    spl4_31 ),
    inference(avatar_contradiction_clause,[],[f455])).

fof(f455,plain,
    ( $false
    | spl4_31 ),
    inference(subsumption_resolution,[],[f182,f446])).

fof(f446,plain,
    ( ~ v1_funct_1(k6_relat_1(u1_struct_0(sK0)))
    | spl4_31 ),
    inference(avatar_component_clause,[],[f445])).

fof(f454,plain,(
    spl4_30 ),
    inference(avatar_contradiction_clause,[],[f453])).

fof(f453,plain,
    ( $false
    | spl4_30 ),
    inference(subsumption_resolution,[],[f186,f443])).

fof(f443,plain,
    ( ~ v1_funct_2(k6_relat_1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | spl4_30 ),
    inference(avatar_component_clause,[],[f442])).

fof(f452,plain,(
    spl4_29 ),
    inference(avatar_contradiction_clause,[],[f451])).

fof(f451,plain,
    ( $false
    | spl4_29 ),
    inference(subsumption_resolution,[],[f187,f440])).

fof(f440,plain,
    ( ~ m1_subset_1(k6_relat_1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | spl4_29 ),
    inference(avatar_component_clause,[],[f439])).

fof(f447,plain,
    ( ~ spl4_29
    | ~ spl4_30
    | ~ spl4_31
    | ~ spl4_16
    | ~ spl4_15
    | spl4_2
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f437,f152,f93,f287,f290,f445,f442,f439])).

fof(f93,plain,
    ( spl4_2
  <=> v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f437,plain,
    ( ~ l1_struct_0(sK0)
    | ~ l1_struct_0(k6_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k6_relat_1(u1_struct_0(sK0)))
    | ~ v1_funct_2(k6_relat_1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k6_relat_1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | spl4_2
    | ~ spl4_9 ),
    inference(resolution,[],[f436,f153])).

fof(f436,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_relat_1(u1_struct_0(sK0)),sK2),sK1,u1_struct_0(k6_tmap_1(sK0,sK1)))
    | spl4_2 ),
    inference(forward_demodulation,[],[f435,f178])).

fof(f435,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),sK1,u1_struct_0(k6_tmap_1(sK0,sK1)))
    | spl4_2 ),
    inference(forward_demodulation,[],[f94,f59])).

fof(f94,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f93])).

fof(f434,plain,
    ( ~ spl4_24
    | spl4_25
    | ~ spl4_26
    | ~ spl4_28
    | ~ spl4_27 ),
    inference(avatar_split_clause,[],[f433,f425,f428,f422,f419,f416])).

fof(f433,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_relat_1(u1_struct_0(sK0)),sK2),sK1,u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_relat_1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ m1_subset_1(sK3(k6_tmap_1(sK0,sK1),sK2,k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_relat_1(u1_struct_0(sK0)),sK2)),sK1)
    | v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_relat_1(u1_struct_0(sK0)),sK2),sK2,k6_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_relat_1(u1_struct_0(sK0)),sK2)) ),
    inference(global_subsumption,[],[f414])).

fof(f414,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_relat_1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_relat_1(u1_struct_0(sK0)),sK2),sK1,u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(sK3(k6_tmap_1(sK0,sK1),sK2,k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_relat_1(u1_struct_0(sK0)),sK2)),sK1)
    | v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_relat_1(u1_struct_0(sK0)),sK2),sK2,k6_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_relat_1(u1_struct_0(sK0)),sK2)) ),
    inference(global_subsumption,[],[f53,f54,f58,f56,f174,f176,f55,f175,f379])).

fof(f379,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_relat_1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_relat_1(u1_struct_0(sK0)),sK2),sK1,u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(sK3(k6_tmap_1(sK0,sK1),sK2,k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_relat_1(u1_struct_0(sK0)),sK2)),sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_relat_1(u1_struct_0(sK0)),sK2),sK2,k6_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_relat_1(u1_struct_0(sK0)),sK2))
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(k6_tmap_1(sK0,sK1))
    | v2_struct_0(k6_tmap_1(sK0,sK1)) ),
    inference(superposition,[],[f268,f178])).

fof(f268,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,sK1),k7_tmap_1(X0,sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,u1_struct_0(k6_tmap_1(X0,sK1)))))
      | ~ v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,sK1),k7_tmap_1(X0,sK1),sK2),sK1,u1_struct_0(k6_tmap_1(X0,sK1)))
      | ~ m1_subset_1(sK3(k6_tmap_1(X0,sK1),sK2,k2_tmap_1(X0,k6_tmap_1(X0,sK1),k7_tmap_1(X0,sK1),sK2)),sK1)
      | ~ m1_pre_topc(sK2,X0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,sK1),k7_tmap_1(X0,sK1),sK2),sK2,k6_tmap_1(X0,sK1))
      | ~ v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,sK1),k7_tmap_1(X0,sK1),sK2))
      | ~ l1_pre_topc(k6_tmap_1(X0,sK1))
      | ~ v2_pre_topc(k6_tmap_1(X0,sK1))
      | v2_struct_0(k6_tmap_1(X0,sK1)) ) ),
    inference(global_subsumption,[],[f57,f104,f105,f267])).

fof(f267,plain,(
    ! [X0] :
      ( ~ v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,sK1),k7_tmap_1(X0,sK1),sK2),sK1,u1_struct_0(k6_tmap_1(X0,sK1)))
      | ~ m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,sK1),k7_tmap_1(X0,sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,u1_struct_0(k6_tmap_1(X0,sK1)))))
      | ~ m1_subset_1(sK3(k6_tmap_1(X0,sK1),sK2,k2_tmap_1(X0,k6_tmap_1(X0,sK1),k7_tmap_1(X0,sK1),sK2)),sK1)
      | ~ m1_pre_topc(sK2,X0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,sK1),k7_tmap_1(X0,sK1),sK2),sK2,k6_tmap_1(X0,sK1))
      | ~ v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,sK1),k7_tmap_1(X0,sK1),sK2))
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2)
      | ~ l1_pre_topc(k6_tmap_1(X0,sK1))
      | ~ v2_pre_topc(k6_tmap_1(X0,sK1))
      | v2_struct_0(k6_tmap_1(X0,sK1)) ) ),
    inference(forward_demodulation,[],[f266,f59])).

fof(f266,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,sK1),k7_tmap_1(X0,sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,u1_struct_0(k6_tmap_1(X0,sK1)))))
      | ~ m1_subset_1(sK3(k6_tmap_1(X0,sK1),sK2,k2_tmap_1(X0,k6_tmap_1(X0,sK1),k7_tmap_1(X0,sK1),sK2)),sK1)
      | ~ m1_pre_topc(sK2,X0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,sK1),k7_tmap_1(X0,sK1),sK2),sK2,k6_tmap_1(X0,sK1))
      | ~ v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,sK1),k7_tmap_1(X0,sK1),sK2),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(X0,sK1)))
      | ~ v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,sK1),k7_tmap_1(X0,sK1),sK2))
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2)
      | ~ l1_pre_topc(k6_tmap_1(X0,sK1))
      | ~ v2_pre_topc(k6_tmap_1(X0,sK1))
      | v2_struct_0(k6_tmap_1(X0,sK1)) ) ),
    inference(forward_demodulation,[],[f264,f59])).

fof(f264,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3(k6_tmap_1(X0,sK1),sK2,k2_tmap_1(X0,k6_tmap_1(X0,sK1),k7_tmap_1(X0,sK1),sK2)),sK1)
      | ~ m1_pre_topc(sK2,X0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,sK1),k7_tmap_1(X0,sK1),sK2),sK2,k6_tmap_1(X0,sK1))
      | ~ m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,sK1),k7_tmap_1(X0,sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(X0,sK1)))))
      | ~ v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,sK1),k7_tmap_1(X0,sK1),sK2),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(X0,sK1)))
      | ~ v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,sK1),k7_tmap_1(X0,sK1),sK2))
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2)
      | ~ l1_pre_topc(k6_tmap_1(X0,sK1))
      | ~ v2_pre_topc(k6_tmap_1(X0,sK1))
      | v2_struct_0(k6_tmap_1(X0,sK1)) ) ),
    inference(resolution,[],[f164,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tmap_1(X1,X0,X2,sK3(X0,X1,X2))
      | v5_pre_topc(X2,X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f164,plain,(
    ! [X37,X36] :
      ( r1_tmap_1(sK2,k6_tmap_1(X36,sK1),k2_tmap_1(X36,k6_tmap_1(X36,sK1),k7_tmap_1(X36,sK1),sK2),X37)
      | ~ m1_subset_1(X37,sK1)
      | ~ m1_pre_topc(sK2,X36)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X36)))
      | ~ l1_pre_topc(X36)
      | ~ v2_pre_topc(X36)
      | v2_struct_0(X36) ) ),
    inference(global_subsumption,[],[f57,f124])).

fof(f124,plain,(
    ! [X37,X36] :
      ( r1_tmap_1(sK2,k6_tmap_1(X36,sK1),k2_tmap_1(X36,k6_tmap_1(X36,sK1),k7_tmap_1(X36,sK1),sK2),X37)
      | ~ m1_subset_1(X37,sK1)
      | ~ m1_pre_topc(sK2,X36)
      | v2_struct_0(sK2)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X36)))
      | ~ l1_pre_topc(X36)
      | ~ v2_pre_topc(X36)
      | v2_struct_0(X36) ) ),
    inference(superposition,[],[f88,f59])).

fof(f88,plain,(
    ! [X2,X0,X3] :
      ( r1_tmap_1(X2,k6_tmap_1(X0,u1_struct_0(X2)),k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X2)),k7_tmap_1(X0,u1_struct_0(X2)),X2),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | u1_struct_0(X2) != X1
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X2)) )
              | u1_struct_0(X2) != X1
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X2)) )
              | u1_struct_0(X2) != X1
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
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
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( u1_struct_0(X2) = X1
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X2))
                   => r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_tmap_1)).

fof(f413,plain,
    ( spl4_1
    | ~ spl4_17 ),
    inference(avatar_contradiction_clause,[],[f412])).

fof(f412,plain,
    ( $false
    | spl4_1
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f105,f404])).

fof(f404,plain,
    ( ~ l1_pre_topc(sK2)
    | spl4_1
    | ~ spl4_17 ),
    inference(resolution,[],[f403,f64])).

fof(f403,plain,
    ( ~ l1_struct_0(sK2)
    | spl4_1
    | ~ spl4_17 ),
    inference(resolution,[],[f294,f183])).

fof(f183,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_relat_1(u1_struct_0(sK0)),sK2))
    | spl4_1 ),
    inference(backward_demodulation,[],[f91,f178])).

fof(f91,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl4_1
  <=> v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f324,plain,(
    spl4_16 ),
    inference(avatar_contradiction_clause,[],[f323])).

fof(f323,plain,
    ( $false
    | spl4_16 ),
    inference(subsumption_resolution,[],[f175,f321])).

fof(f321,plain,
    ( ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | spl4_16 ),
    inference(resolution,[],[f291,f64])).

fof(f291,plain,
    ( ~ l1_struct_0(k6_tmap_1(sK0,sK1))
    | spl4_16 ),
    inference(avatar_component_clause,[],[f290])).

fof(f319,plain,(
    spl4_15 ),
    inference(avatar_contradiction_clause,[],[f318])).

fof(f318,plain,
    ( $false
    | spl4_15 ),
    inference(subsumption_resolution,[],[f55,f315])).

fof(f315,plain,
    ( ~ l1_pre_topc(sK0)
    | spl4_15 ),
    inference(resolution,[],[f288,f64])).

fof(f288,plain,
    ( ~ l1_struct_0(sK0)
    | spl4_15 ),
    inference(avatar_component_clause,[],[f287])).

fof(f295,plain,
    ( ~ spl4_15
    | ~ spl4_16
    | spl4_17 ),
    inference(avatar_split_clause,[],[f285,f293,f290,f287])).

fof(f285,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_relat_1(u1_struct_0(sK0)),X0))
      | ~ l1_struct_0(k6_tmap_1(sK0,sK1))
      | ~ l1_struct_0(sK0) ) ),
    inference(global_subsumption,[],[f182,f186,f279])).

fof(f279,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k6_relat_1(u1_struct_0(sK0)),X0))
      | ~ v1_funct_2(k6_relat_1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
      | ~ v1_funct_1(k6_relat_1(u1_struct_0(sK0)))
      | ~ l1_struct_0(k6_tmap_1(sK0,sK1))
      | ~ l1_struct_0(sK0) ) ),
    inference(resolution,[],[f187,f83])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f181,plain,(
    spl4_5 ),
    inference(avatar_contradiction_clause,[],[f180])).

fof(f180,plain,
    ( $false
    | spl4_5 ),
    inference(subsumption_resolution,[],[f105,f179])).

fof(f179,plain,
    ( ~ l1_pre_topc(sK2)
    | spl4_5 ),
    inference(resolution,[],[f138,f64])).

fof(f138,plain,
    ( ~ l1_struct_0(sK2)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f137])).

fof(f154,plain,
    ( ~ spl4_5
    | spl4_9 ),
    inference(avatar_split_clause,[],[f120,f152,f137])).

fof(f120,plain,(
    ! [X28,X26,X27] :
      ( v1_funct_2(k2_tmap_1(X26,X27,X28,sK2),sK1,u1_struct_0(X27))
      | ~ l1_struct_0(sK2)
      | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X26),u1_struct_0(X27))))
      | ~ v1_funct_2(X28,u1_struct_0(X26),u1_struct_0(X27))
      | ~ v1_funct_1(X28)
      | ~ l1_struct_0(X27)
      | ~ l1_struct_0(X26) ) ),
    inference(superposition,[],[f84,f59])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f101,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f60,f99,f96,f93,f90])).

fof(f60,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),sK2,k6_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2)) ),
    inference(cnf_transformation,[],[f48])).

%------------------------------------------------------------------------------
