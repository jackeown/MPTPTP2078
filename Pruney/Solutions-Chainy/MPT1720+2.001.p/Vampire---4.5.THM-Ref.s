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
% DateTime   : Thu Dec  3 13:18:02 EST 2020

% Result     : Theorem 5.65s
% Output     : Refutation 5.65s
% Verified   : 
% Statistics : Number of formulae       :  232 (3413 expanded)
%              Number of leaves         :   22 (1444 expanded)
%              Depth                    :   41
%              Number of atoms          : 1255 (37392 expanded)
%              Number of equality atoms :   68 ( 344 expanded)
%              Maximal formula depth    :   20 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15787,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1264,f1273,f1321,f1916,f1958,f15359,f15785])).

fof(f15785,plain,
    ( ~ spl4_62
    | ~ spl4_64
    | ~ spl4_65
    | ~ spl4_98
    | ~ spl4_99 ),
    inference(avatar_contradiction_clause,[],[f15784])).

fof(f15784,plain,
    ( $false
    | ~ spl4_62
    | ~ spl4_64
    | ~ spl4_65
    | ~ spl4_98
    | ~ spl4_99 ),
    inference(subsumption_resolution,[],[f15783,f44])).

fof(f44,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2)
    & m1_pre_topc(sK3,sK2)
    & m1_pre_topc(sK1,sK2)
    & m1_pre_topc(sK3,sK0)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f38,f37,f36,f35])).

fof(f35,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ m1_pre_topc(k1_tsep_1(X0,X1,X3),X2)
                    & m1_pre_topc(X3,X2)
                    & m1_pre_topc(X1,X2)
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
                  ( ~ m1_pre_topc(k1_tsep_1(sK0,X1,X3),X2)
                  & m1_pre_topc(X3,X2)
                  & m1_pre_topc(X1,X2)
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

fof(f36,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ m1_pre_topc(k1_tsep_1(sK0,X1,X3),X2)
                & m1_pre_topc(X3,X2)
                & m1_pre_topc(X1,X2)
                & m1_pre_topc(X3,sK0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,X3),X2)
              & m1_pre_topc(X3,X2)
              & m1_pre_topc(sK1,X2)
              & m1_pre_topc(X3,sK0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK0)
          & ~ v2_struct_0(X2) )
      & m1_pre_topc(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,X3),X2)
            & m1_pre_topc(X3,X2)
            & m1_pre_topc(sK1,X2)
            & m1_pre_topc(X3,sK0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,X3),sK2)
          & m1_pre_topc(X3,sK2)
          & m1_pre_topc(sK1,sK2)
          & m1_pre_topc(X3,sK0)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X3] :
        ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,X3),sK2)
        & m1_pre_topc(X3,sK2)
        & m1_pre_topc(sK1,sK2)
        & m1_pre_topc(X3,sK0)
        & ~ v2_struct_0(X3) )
   => ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2)
      & m1_pre_topc(sK3,sK2)
      & m1_pre_topc(sK1,sK2)
      & m1_pre_topc(sK3,sK0)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_pre_topc(k1_tsep_1(X0,X1,X3),X2)
                  & m1_pre_topc(X3,X2)
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_pre_topc(k1_tsep_1(X0,X1,X3),X2)
                  & m1_pre_topc(X3,X2)
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
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
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ( ( m1_pre_topc(X3,X2)
                        & m1_pre_topc(X1,X2) )
                     => m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) ) ) ) ) ) ),
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
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( ( m1_pre_topc(X3,X2)
                      & m1_pre_topc(X1,X2) )
                   => m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tmap_1)).

fof(f15783,plain,
    ( v2_struct_0(sK0)
    | ~ spl4_62
    | ~ spl4_64
    | ~ spl4_65
    | ~ spl4_98
    | ~ spl4_99 ),
    inference(subsumption_resolution,[],[f15782,f47])).

fof(f47,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f15782,plain,
    ( v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ spl4_62
    | ~ spl4_64
    | ~ spl4_65
    | ~ spl4_98
    | ~ spl4_99 ),
    inference(subsumption_resolution,[],[f15781,f48])).

fof(f48,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f15781,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ spl4_62
    | ~ spl4_64
    | ~ spl4_65
    | ~ spl4_98
    | ~ spl4_99 ),
    inference(subsumption_resolution,[],[f15780,f51])).

fof(f51,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f15780,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ spl4_62
    | ~ spl4_64
    | ~ spl4_65
    | ~ spl4_98
    | ~ spl4_99 ),
    inference(subsumption_resolution,[],[f15779,f52])).

fof(f52,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f15779,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ spl4_62
    | ~ spl4_64
    | ~ spl4_65
    | ~ spl4_98
    | ~ spl4_99 ),
    inference(subsumption_resolution,[],[f15778,f45])).

fof(f45,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f15778,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ spl4_62
    | ~ spl4_64
    | ~ spl4_65
    | ~ spl4_98
    | ~ spl4_99 ),
    inference(subsumption_resolution,[],[f15777,f46])).

fof(f46,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f15777,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ spl4_62
    | ~ spl4_64
    | ~ spl4_65
    | ~ spl4_98
    | ~ spl4_99 ),
    inference(subsumption_resolution,[],[f15697,f50])).

fof(f50,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f15697,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ spl4_62
    | ~ spl4_64
    | ~ spl4_65
    | ~ spl4_98
    | ~ spl4_99 ),
    inference(duplicate_literal_removal,[],[f15693])).

fof(f15693,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_62
    | ~ spl4_64
    | ~ spl4_65
    | ~ spl4_98
    | ~ spl4_99 ),
    inference(resolution,[],[f15550,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f5,axiom,(
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

fof(f15550,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X0)
        | ~ m1_pre_topc(sK2,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl4_62
    | ~ spl4_64
    | ~ spl4_65
    | ~ spl4_98
    | ~ spl4_99 ),
    inference(subsumption_resolution,[],[f15548,f55])).

fof(f55,plain,(
    ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f15548,plain,
    ( ! [X0] :
        ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2)
        | ~ m1_pre_topc(sK2,X0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl4_62
    | ~ spl4_64
    | ~ spl4_65
    | ~ spl4_98
    | ~ spl4_99 ),
    inference(resolution,[],[f15522,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).

fof(f15522,plain,
    ( r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(sK2))
    | ~ spl4_62
    | ~ spl4_64
    | ~ spl4_65
    | ~ spl4_98
    | ~ spl4_99 ),
    inference(resolution,[],[f15474,f4889])).

fof(f4889,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK1,sK2))
    | ~ spl4_99 ),
    inference(subsumption_resolution,[],[f4888,f51])).

fof(f4888,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(sK3)
    | ~ spl4_99 ),
    inference(subsumption_resolution,[],[f4887,f52])).

fof(f4887,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ spl4_99 ),
    inference(subsumption_resolution,[],[f4886,f47])).

fof(f4886,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ spl4_99 ),
    inference(subsumption_resolution,[],[f4885,f48])).

fof(f4885,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ spl4_99 ),
    inference(subsumption_resolution,[],[f4884,f54])).

fof(f54,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f4884,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(sK3,sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ spl4_99 ),
    inference(subsumption_resolution,[],[f4867,f1949])).

fof(f1949,plain,
    ( m1_pre_topc(sK1,sK1)
    | ~ spl4_99 ),
    inference(avatar_component_clause,[],[f1948])).

fof(f1948,plain,
    ( spl4_99
  <=> m1_pre_topc(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_99])])).

fof(f4867,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(sK1,sK1)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3) ),
    inference(superposition,[],[f830,f482])).

fof(f482,plain,(
    k1_tsep_1(sK0,sK1,sK3) = k1_tsep_1(sK0,sK3,sK1) ),
    inference(subsumption_resolution,[],[f475,f51])).

fof(f475,plain,
    ( k1_tsep_1(sK0,sK1,sK3) = k1_tsep_1(sK0,sK3,sK1)
    | v2_struct_0(sK3) ),
    inference(resolution,[],[f82,f52])).

fof(f82,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | k1_tsep_1(sK0,X0,sK1) = k1_tsep_1(sK0,sK1,X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f81,f44])).

fof(f81,plain,(
    ! [X0] :
      ( k1_tsep_1(sK0,X0,sK1) = k1_tsep_1(sK0,sK1,X0)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f80,f46])).

fof(f80,plain,(
    ! [X0] :
      ( k1_tsep_1(sK0,X0,sK1) = k1_tsep_1(sK0,sK1,X0)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f74,f47])).

fof(f74,plain,(
    ! [X0] :
      ( k1_tsep_1(sK0,X0,sK1) = k1_tsep_1(sK0,sK1,X0)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f48,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X2,X0)
      | k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k1_tsep_1)).

fof(f830,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_tsep_1(sK0,X0,X1),k1_tsep_1(sK0,sK1,sK2))
      | ~ m1_pre_topc(X1,sK1)
      | ~ m1_pre_topc(X0,sK2)
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f829,f44])).

fof(f829,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_tsep_1(sK0,X0,X1),k1_tsep_1(sK0,sK1,sK2))
      | ~ m1_pre_topc(X1,sK1)
      | ~ m1_pre_topc(X0,sK2)
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f828,f45])).

fof(f828,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_tsep_1(sK0,X0,X1),k1_tsep_1(sK0,sK1,sK2))
      | ~ m1_pre_topc(X1,sK1)
      | ~ m1_pre_topc(X0,sK2)
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f827,f46])).

fof(f827,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_tsep_1(sK0,X0,X1),k1_tsep_1(sK0,sK1,sK2))
      | ~ m1_pre_topc(X1,sK1)
      | ~ m1_pre_topc(X0,sK2)
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f826,f49])).

fof(f49,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f826,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_tsep_1(sK0,X0,X1),k1_tsep_1(sK0,sK1,sK2))
      | ~ m1_pre_topc(X1,sK1)
      | ~ m1_pre_topc(X0,sK2)
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f825,f50])).

fof(f825,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_tsep_1(sK0,X0,X1),k1_tsep_1(sK0,sK1,sK2))
      | ~ m1_pre_topc(X1,sK1)
      | ~ m1_pre_topc(X0,sK2)
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(sK2,sK0)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f824,f47])).

fof(f824,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_tsep_1(sK0,X0,X1),k1_tsep_1(sK0,sK1,sK2))
      | ~ m1_pre_topc(X1,sK1)
      | ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(sK2,sK0)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f821,f48])).

fof(f821,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_tsep_1(sK0,X0,X1),k1_tsep_1(sK0,sK1,sK2))
      | ~ m1_pre_topc(X1,sK1)
      | ~ m1_pre_topc(X0,sK2)
      | ~ m1_pre_topc(sK1,sK0)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(sK2,sK0)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f62,f481])).

fof(f481,plain,(
    k1_tsep_1(sK0,sK2,sK1) = k1_tsep_1(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f474,f49])).

fof(f474,plain,
    ( k1_tsep_1(sK0,sK2,sK1) = k1_tsep_1(sK0,sK1,sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f82,f50])).

fof(f62,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X3),k1_tsep_1(X0,X2,X4))
      | ~ m1_pre_topc(X3,X4)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X4,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
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
                      ( m1_pre_topc(k1_tsep_1(X0,X1,X3),k1_tsep_1(X0,X2,X4))
                      | ~ m1_pre_topc(X3,X4)
                      | ~ m1_pre_topc(X1,X2)
                      | ~ m1_pre_topc(X4,X0)
                      | v2_struct_0(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
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
                      ( m1_pre_topc(k1_tsep_1(X0,X1,X3),k1_tsep_1(X0,X2,X4))
                      | ~ m1_pre_topc(X3,X4)
                      | ~ m1_pre_topc(X1,X2)
                      | ~ m1_pre_topc(X4,X0)
                      | v2_struct_0(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
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
                     => ( ( m1_pre_topc(X3,X4)
                          & m1_pre_topc(X1,X2) )
                       => m1_pre_topc(k1_tsep_1(X0,X1,X3),k1_tsep_1(X0,X2,X4)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_tmap_1)).

fof(f15474,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(X1,k1_tsep_1(sK0,sK1,sK2))
        | r1_tarski(u1_struct_0(X1),u1_struct_0(sK2)) )
    | ~ spl4_62
    | ~ spl4_64
    | ~ spl4_65
    | ~ spl4_98
    | ~ spl4_99 ),
    inference(backward_demodulation,[],[f14646,f1915])).

fof(f1915,plain,
    ( u1_struct_0(sK2) = u1_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ spl4_98 ),
    inference(avatar_component_clause,[],[f1913])).

fof(f1913,plain,
    ( spl4_98
  <=> u1_struct_0(sK2) = u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_98])])).

fof(f14646,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(X1,k1_tsep_1(sK0,sK1,sK2))
        | r1_tarski(u1_struct_0(X1),u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) )
    | ~ spl4_62
    | ~ spl4_64
    | ~ spl4_65
    | ~ spl4_99 ),
    inference(forward_demodulation,[],[f14645,f9479])).

fof(f9479,plain,
    ( k1_tsep_1(sK0,sK1,sK2) = k1_tsep_1(sK2,sK1,sK2)
    | ~ spl4_62 ),
    inference(subsumption_resolution,[],[f9469,f47])).

fof(f9469,plain,
    ( k1_tsep_1(sK0,sK1,sK2) = k1_tsep_1(sK2,sK1,sK2)
    | v2_struct_0(sK1)
    | ~ spl4_62 ),
    inference(resolution,[],[f3579,f53])).

fof(f53,plain,(
    m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f3579,plain,
    ( ! [X2] :
        ( ~ m1_pre_topc(X2,sK2)
        | k1_tsep_1(sK0,sK1,sK2) = k1_tsep_1(sK2,X2,sK2)
        | v2_struct_0(X2) )
    | ~ spl4_62 ),
    inference(forward_demodulation,[],[f1346,f804])).

fof(f804,plain,(
    k1_tsep_1(sK0,sK2,sK2) = k1_tsep_1(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f803,f47])).

fof(f803,plain,
    ( k1_tsep_1(sK0,sK2,sK2) = k1_tsep_1(sK0,sK1,sK2)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f795,f48])).

fof(f795,plain,
    ( k1_tsep_1(sK0,sK2,sK2) = k1_tsep_1(sK0,sK1,sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f768,f53])).

fof(f768,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(X2,sK2)
      | k1_tsep_1(sK0,X2,sK2) = k1_tsep_1(sK0,sK2,sK2)
      | ~ m1_pre_topc(X2,sK0)
      | v2_struct_0(X2) ) ),
    inference(forward_demodulation,[],[f112,f116])).

fof(f116,plain,(
    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK2,sK2) ),
    inference(subsumption_resolution,[],[f115,f44])).

fof(f115,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK2,sK2)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f114,f45])).

fof(f114,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK2,sK2)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f113,f46])).

fof(f113,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK2,sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f100,f49])).

fof(f100,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK2,sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f50,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          | ~ m1_pre_topc(X1,X0)
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
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_tmap_1)).

fof(f112,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(X2,sK2)
      | k1_tsep_1(sK0,X2,sK2) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
      | ~ m1_pre_topc(X2,sK0)
      | v2_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f111,f44])).

fof(f111,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(X2,sK2)
      | k1_tsep_1(sK0,X2,sK2) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
      | ~ m1_pre_topc(X2,sK0)
      | v2_struct_0(X2)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f110,f45])).

fof(f110,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(X2,sK2)
      | k1_tsep_1(sK0,X2,sK2) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
      | ~ m1_pre_topc(X2,sK0)
      | v2_struct_0(X2)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f109,f46])).

fof(f109,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(X2,sK2)
      | k1_tsep_1(sK0,X2,sK2) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
      | ~ m1_pre_topc(X2,sK0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f99,f49])).

fof(f99,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(X2,sK2)
      | k1_tsep_1(sK0,X2,sK2) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(X2,sK0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f50,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X2)
      | k1_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X2)
                  | k1_tsep_1(X0,X1,X2) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) )
                & ( k1_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                  | ~ m1_pre_topc(X1,X2) ) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X2)
              <=> k1_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X2)
              <=> k1_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
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
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( m1_pre_topc(X1,X2)
              <=> k1_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_tsep_1)).

fof(f1346,plain,
    ( ! [X2] :
        ( k1_tsep_1(sK0,sK2,sK2) = k1_tsep_1(sK2,X2,sK2)
        | ~ m1_pre_topc(X2,sK2)
        | v2_struct_0(X2) )
    | ~ spl4_62 ),
    inference(forward_demodulation,[],[f1345,f116])).

fof(f1345,plain,
    ( ! [X2] :
        ( ~ m1_pre_topc(X2,sK2)
        | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK2,X2,sK2)
        | v2_struct_0(X2) )
    | ~ spl4_62 ),
    inference(subsumption_resolution,[],[f1344,f108])).

fof(f108,plain,(
    v2_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f107,f45])).

fof(f107,plain,
    ( v2_pre_topc(sK2)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f98,f46])).

fof(f98,plain,
    ( v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f50,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f1344,plain,
    ( ! [X2] :
        ( ~ m1_pre_topc(X2,sK2)
        | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK2,X2,sK2)
        | v2_struct_0(X2)
        | ~ v2_pre_topc(sK2) )
    | ~ spl4_62 ),
    inference(subsumption_resolution,[],[f1343,f117])).

fof(f117,plain,(
    l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f101,f46])).

fof(f101,plain,
    ( l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f50,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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

fof(f1343,plain,
    ( ! [X2] :
        ( ~ m1_pre_topc(X2,sK2)
        | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK2,X2,sK2)
        | v2_struct_0(X2)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2) )
    | ~ spl4_62 ),
    inference(subsumption_resolution,[],[f1335,f49])).

fof(f1335,plain,
    ( ! [X2] :
        ( ~ m1_pre_topc(X2,sK2)
        | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK2,X2,sK2)
        | v2_struct_0(sK2)
        | v2_struct_0(X2)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2) )
    | ~ spl4_62 ),
    inference(duplicate_literal_removal,[],[f1331])).

fof(f1331,plain,
    ( ! [X2] :
        ( ~ m1_pre_topc(X2,sK2)
        | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK2,X2,sK2)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(X2,sK2)
        | v2_struct_0(X2)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | ~ spl4_62 ),
    inference(resolution,[],[f1249,f60])).

fof(f1249,plain,
    ( m1_pre_topc(sK2,sK2)
    | ~ spl4_62 ),
    inference(avatar_component_clause,[],[f1248])).

fof(f1248,plain,
    ( spl4_62
  <=> m1_pre_topc(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_62])])).

fof(f14645,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(X1,k1_tsep_1(sK0,sK1,sK2))
        | r1_tarski(u1_struct_0(X1),u1_struct_0(k1_tsep_1(sK2,sK1,sK2))) )
    | ~ spl4_62
    | ~ spl4_64
    | ~ spl4_65
    | ~ spl4_99 ),
    inference(forward_demodulation,[],[f4624,f9479])).

fof(f4624,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(X1,k1_tsep_1(sK2,sK1,sK2))
        | r1_tarski(u1_struct_0(X1),u1_struct_0(k1_tsep_1(sK2,sK1,sK2))) )
    | ~ spl4_62
    | ~ spl4_64
    | ~ spl4_65
    | ~ spl4_99 ),
    inference(subsumption_resolution,[],[f4623,f1439])).

fof(f1439,plain,
    ( v2_pre_topc(k1_tsep_1(sK2,sK1,sK2))
    | ~ spl4_64 ),
    inference(subsumption_resolution,[],[f1438,f108])).

fof(f1438,plain,
    ( v2_pre_topc(k1_tsep_1(sK2,sK1,sK2))
    | ~ v2_pre_topc(sK2)
    | ~ spl4_64 ),
    inference(subsumption_resolution,[],[f1397,f117])).

fof(f1397,plain,
    ( v2_pre_topc(k1_tsep_1(sK2,sK1,sK2))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ spl4_64 ),
    inference(resolution,[],[f1263,f63])).

fof(f1263,plain,
    ( m1_pre_topc(k1_tsep_1(sK2,sK1,sK2),sK2)
    | ~ spl4_64 ),
    inference(avatar_component_clause,[],[f1261])).

fof(f1261,plain,
    ( spl4_64
  <=> m1_pre_topc(k1_tsep_1(sK2,sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_64])])).

fof(f4623,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(X1,k1_tsep_1(sK2,sK1,sK2))
        | r1_tarski(u1_struct_0(X1),u1_struct_0(k1_tsep_1(sK2,sK1,sK2)))
        | ~ v2_pre_topc(k1_tsep_1(sK2,sK1,sK2)) )
    | ~ spl4_62
    | ~ spl4_64
    | ~ spl4_65
    | ~ spl4_99 ),
    inference(subsumption_resolution,[],[f4619,f1448])).

fof(f1448,plain,
    ( l1_pre_topc(k1_tsep_1(sK2,sK1,sK2))
    | ~ spl4_64 ),
    inference(subsumption_resolution,[],[f1400,f117])).

fof(f1400,plain,
    ( l1_pre_topc(k1_tsep_1(sK2,sK1,sK2))
    | ~ l1_pre_topc(sK2)
    | ~ spl4_64 ),
    inference(resolution,[],[f1263,f57])).

fof(f4619,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(X1,k1_tsep_1(sK2,sK1,sK2))
        | r1_tarski(u1_struct_0(X1),u1_struct_0(k1_tsep_1(sK2,sK1,sK2)))
        | ~ l1_pre_topc(k1_tsep_1(sK2,sK1,sK2))
        | ~ v2_pre_topc(k1_tsep_1(sK2,sK1,sK2)) )
    | ~ spl4_62
    | ~ spl4_65
    | ~ spl4_99 ),
    inference(duplicate_literal_removal,[],[f4612])).

fof(f4612,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(X1,k1_tsep_1(sK2,sK1,sK2))
        | r1_tarski(u1_struct_0(X1),u1_struct_0(k1_tsep_1(sK2,sK1,sK2)))
        | ~ m1_pre_topc(X1,k1_tsep_1(sK2,sK1,sK2))
        | ~ l1_pre_topc(k1_tsep_1(sK2,sK1,sK2))
        | ~ v2_pre_topc(k1_tsep_1(sK2,sK1,sK2)) )
    | ~ spl4_62
    | ~ spl4_65
    | ~ spl4_99 ),
    inference(resolution,[],[f4430,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X2)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f4430,plain,
    ( m1_pre_topc(k1_tsep_1(sK2,sK1,sK2),k1_tsep_1(sK2,sK1,sK2))
    | ~ spl4_62
    | ~ spl4_65
    | ~ spl4_99 ),
    inference(subsumption_resolution,[],[f4429,f1949])).

fof(f4429,plain,
    ( m1_pre_topc(k1_tsep_1(sK2,sK1,sK2),k1_tsep_1(sK2,sK1,sK2))
    | ~ m1_pre_topc(sK1,sK1)
    | ~ spl4_62
    | ~ spl4_65 ),
    inference(subsumption_resolution,[],[f4428,f1249])).

fof(f4428,plain,
    ( m1_pre_topc(k1_tsep_1(sK2,sK1,sK2),k1_tsep_1(sK2,sK1,sK2))
    | ~ m1_pre_topc(sK2,sK2)
    | ~ m1_pre_topc(sK1,sK1)
    | ~ spl4_65 ),
    inference(subsumption_resolution,[],[f4427,f53])).

fof(f4427,plain,
    ( m1_pre_topc(k1_tsep_1(sK2,sK1,sK2),k1_tsep_1(sK2,sK1,sK2))
    | ~ m1_pre_topc(sK1,sK2)
    | ~ m1_pre_topc(sK2,sK2)
    | ~ m1_pre_topc(sK1,sK1)
    | ~ spl4_65 ),
    inference(subsumption_resolution,[],[f4426,f47])).

fof(f4426,plain,
    ( m1_pre_topc(k1_tsep_1(sK2,sK1,sK2),k1_tsep_1(sK2,sK1,sK2))
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK2)
    | ~ m1_pre_topc(sK2,sK2)
    | ~ m1_pre_topc(sK1,sK1)
    | ~ spl4_65 ),
    inference(subsumption_resolution,[],[f4394,f49])).

fof(f4394,plain,
    ( m1_pre_topc(k1_tsep_1(sK2,sK1,sK2),k1_tsep_1(sK2,sK1,sK2))
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK2)
    | ~ m1_pre_topc(sK2,sK2)
    | ~ m1_pre_topc(sK1,sK1)
    | ~ spl4_65 ),
    inference(superposition,[],[f1272,f626])).

fof(f626,plain,(
    k1_tsep_1(sK2,sK2,sK1) = k1_tsep_1(sK2,sK1,sK2) ),
    inference(subsumption_resolution,[],[f625,f117])).

fof(f625,plain,
    ( k1_tsep_1(sK2,sK2,sK1) = k1_tsep_1(sK2,sK1,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f619,f49])).

fof(f619,plain,
    ( k1_tsep_1(sK2,sK2,sK1) = k1_tsep_1(sK2,sK1,sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f148,f56])).

fof(f56,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f148,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | k1_tsep_1(sK2,X0,sK1) = k1_tsep_1(sK2,sK1,X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f147,f49])).

fof(f147,plain,(
    ! [X0] :
      ( k1_tsep_1(sK2,X0,sK1) = k1_tsep_1(sK2,sK1,X0)
      | ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f146,f117])).

fof(f146,plain,(
    ! [X0] :
      ( k1_tsep_1(sK2,X0,sK1) = k1_tsep_1(sK2,sK1,X0)
      | ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f140,f47])).

fof(f140,plain,(
    ! [X0] :
      ( k1_tsep_1(sK2,X0,sK1) = k1_tsep_1(sK2,sK1,X0)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f53,f69])).

fof(f1272,plain,
    ( ! [X0,X1] :
        ( m1_pre_topc(k1_tsep_1(sK2,X0,X1),k1_tsep_1(sK2,sK1,sK2))
        | v2_struct_0(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK2)
        | ~ m1_pre_topc(X0,sK2)
        | ~ m1_pre_topc(X1,sK1) )
    | ~ spl4_65 ),
    inference(avatar_component_clause,[],[f1271])).

fof(f1271,plain,
    ( spl4_65
  <=> ! [X1,X0] :
        ( m1_pre_topc(k1_tsep_1(sK2,X0,X1),k1_tsep_1(sK2,sK1,sK2))
        | v2_struct_0(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK2)
        | ~ m1_pre_topc(X0,sK2)
        | ~ m1_pre_topc(X1,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_65])])).

fof(f15359,plain,
    ( ~ spl4_62
    | ~ spl4_64
    | ~ spl4_65
    | spl4_97
    | ~ spl4_99 ),
    inference(avatar_contradiction_clause,[],[f15358])).

fof(f15358,plain,
    ( $false
    | ~ spl4_62
    | ~ spl4_64
    | ~ spl4_65
    | spl4_97
    | ~ spl4_99 ),
    inference(subsumption_resolution,[],[f15338,f1911])).

fof(f1911,plain,
    ( ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    | spl4_97 ),
    inference(avatar_component_clause,[],[f1909])).

fof(f1909,plain,
    ( spl4_97
  <=> r1_tarski(u1_struct_0(sK2),u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_97])])).

fof(f15338,plain,
    ( r1_tarski(u1_struct_0(sK2),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    | ~ spl4_62
    | ~ spl4_64
    | ~ spl4_65
    | ~ spl4_99 ),
    inference(resolution,[],[f14646,f844])).

fof(f844,plain,(
    m1_pre_topc(sK2,k1_tsep_1(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f843,f44])).

fof(f843,plain,
    ( m1_pre_topc(sK2,k1_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f842,f45])).

fof(f842,plain,
    ( m1_pre_topc(sK2,k1_tsep_1(sK0,sK1,sK2))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f841,f46])).

fof(f841,plain,
    ( m1_pre_topc(sK2,k1_tsep_1(sK0,sK1,sK2))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f840,f49])).

fof(f840,plain,
    ( m1_pre_topc(sK2,k1_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f839,f50])).

fof(f839,plain,
    ( m1_pre_topc(sK2,k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f838,f47])).

fof(f838,plain,
    ( m1_pre_topc(sK2,k1_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f823,f48])).

fof(f823,plain,
    ( m1_pre_topc(sK2,k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f59,f481])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
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
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_tsep_1)).

fof(f1958,plain,(
    spl4_99 ),
    inference(avatar_contradiction_clause,[],[f1957])).

fof(f1957,plain,
    ( $false
    | spl4_99 ),
    inference(subsumption_resolution,[],[f1956,f95])).

fof(f95,plain,(
    l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f79,f46])).

fof(f79,plain,
    ( l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f48,f57])).

fof(f1956,plain,
    ( ~ l1_pre_topc(sK1)
    | spl4_99 ),
    inference(resolution,[],[f1950,f56])).

fof(f1950,plain,
    ( ~ m1_pre_topc(sK1,sK1)
    | spl4_99 ),
    inference(avatar_component_clause,[],[f1948])).

fof(f1916,plain,
    ( ~ spl4_97
    | spl4_98
    | ~ spl4_62 ),
    inference(avatar_split_clause,[],[f1907,f1248,f1913,f1909])).

fof(f1907,plain,
    ( u1_struct_0(sK2) = u1_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    | ~ spl4_62 ),
    inference(resolution,[],[f1836,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1836,plain,
    ( r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK2))
    | ~ spl4_62 ),
    inference(subsumption_resolution,[],[f1835,f49])).

fof(f1835,plain,
    ( r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ spl4_62 ),
    inference(subsumption_resolution,[],[f1834,f1249])).

fof(f1834,plain,
    ( r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK2)
    | v2_struct_0(sK2)
    | ~ spl4_62 ),
    inference(subsumption_resolution,[],[f1833,f1529])).

fof(f1529,plain,(
    m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) ),
    inference(subsumption_resolution,[],[f1528,f44])).

fof(f1528,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1527,f46])).

fof(f1527,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1526,f49])).

fof(f1526,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1520,f50])).

fof(f1520,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f1513])).

fof(f1513,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f71,f804])).

fof(f1833,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK2)
    | v2_struct_0(sK2)
    | ~ spl4_62 ),
    inference(duplicate_literal_removal,[],[f1822])).

fof(f1822,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK2)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK2)
    | v2_struct_0(sK2)
    | ~ spl4_62 ),
    inference(superposition,[],[f349,f1821])).

fof(f1821,plain,
    ( k1_tsep_1(sK0,sK1,sK2) = k1_tsep_1(sK2,sK2,sK2)
    | ~ spl4_62 ),
    inference(forward_demodulation,[],[f1350,f804])).

fof(f1350,plain,
    ( k1_tsep_1(sK0,sK2,sK2) = k1_tsep_1(sK2,sK2,sK2)
    | ~ spl4_62 ),
    inference(forward_demodulation,[],[f1349,f116])).

fof(f1349,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK2,sK2,sK2)
    | ~ spl4_62 ),
    inference(subsumption_resolution,[],[f1348,f108])).

fof(f1348,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK2,sK2,sK2)
    | ~ v2_pre_topc(sK2)
    | ~ spl4_62 ),
    inference(subsumption_resolution,[],[f1347,f117])).

fof(f1347,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK2,sK2,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ spl4_62 ),
    inference(subsumption_resolution,[],[f1334,f49])).

fof(f1334,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK2,sK2,sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ spl4_62 ),
    inference(duplicate_literal_removal,[],[f1332])).

fof(f1332,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK2,sK2,sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl4_62 ),
    inference(resolution,[],[f1249,f58])).

fof(f349,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(k1_tsep_1(sK2,X0,X1),sK0)
      | r1_tarski(u1_struct_0(k1_tsep_1(sK2,X0,X1)),u1_struct_0(sK2))
      | ~ m1_pre_topc(X1,sK2)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f348,f49])).

fof(f348,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(k1_tsep_1(sK2,X0,X1)),u1_struct_0(sK2))
      | ~ m1_pre_topc(k1_tsep_1(sK2,X0,X1),sK0)
      | ~ m1_pre_topc(X1,sK2)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f343,f117])).

fof(f343,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(k1_tsep_1(sK2,X0,X1)),u1_struct_0(sK2))
      | ~ m1_pre_topc(k1_tsep_1(sK2,X0,X1),sK0)
      | ~ m1_pre_topc(X1,sK2)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f106,f71])).

fof(f106,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,sK2)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(sK2))
      | ~ m1_pre_topc(X1,sK0) ) ),
    inference(subsumption_resolution,[],[f105,f45])).

fof(f105,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,sK2)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(sK2))
      | ~ m1_pre_topc(X1,sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f97,f46])).

fof(f97,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,sK2)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(sK2))
      | ~ m1_pre_topc(X1,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(resolution,[],[f50,f65])).

fof(f1321,plain,(
    spl4_62 ),
    inference(avatar_contradiction_clause,[],[f1320])).

fof(f1320,plain,
    ( $false
    | spl4_62 ),
    inference(subsumption_resolution,[],[f1319,f117])).

fof(f1319,plain,
    ( ~ l1_pre_topc(sK2)
    | spl4_62 ),
    inference(resolution,[],[f1250,f56])).

fof(f1250,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | spl4_62 ),
    inference(avatar_component_clause,[],[f1248])).

fof(f1273,plain,
    ( ~ spl4_62
    | spl4_65 ),
    inference(avatar_split_clause,[],[f1269,f1271,f1248])).

fof(f1269,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_tsep_1(sK2,X0,X1),k1_tsep_1(sK2,sK1,sK2))
      | ~ m1_pre_topc(X1,sK1)
      | ~ m1_pre_topc(X0,sK2)
      | ~ m1_pre_topc(X1,sK2)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(sK2,sK2)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f1268,f108])).

fof(f1268,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_tsep_1(sK2,X0,X1),k1_tsep_1(sK2,sK1,sK2))
      | ~ m1_pre_topc(X1,sK1)
      | ~ m1_pre_topc(X0,sK2)
      | ~ m1_pre_topc(X1,sK2)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(sK2,sK2)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(sK2) ) ),
    inference(subsumption_resolution,[],[f1267,f117])).

fof(f1267,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_tsep_1(sK2,X0,X1),k1_tsep_1(sK2,sK1,sK2))
      | ~ m1_pre_topc(X1,sK1)
      | ~ m1_pre_topc(X0,sK2)
      | ~ m1_pre_topc(X1,sK2)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(sK2,sK2)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2) ) ),
    inference(subsumption_resolution,[],[f1266,f49])).

fof(f1266,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_tsep_1(sK2,X0,X1),k1_tsep_1(sK2,sK1,sK2))
      | ~ m1_pre_topc(X1,sK1)
      | ~ m1_pre_topc(X0,sK2)
      | ~ m1_pre_topc(X1,sK2)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(sK2,sK2)
      | v2_struct_0(sK2)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2) ) ),
    inference(subsumption_resolution,[],[f1265,f47])).

fof(f1265,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_tsep_1(sK2,X0,X1),k1_tsep_1(sK2,sK1,sK2))
      | ~ m1_pre_topc(X1,sK1)
      | ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(X1,sK2)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(sK2,sK2)
      | v2_struct_0(sK2)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2) ) ),
    inference(subsumption_resolution,[],[f1240,f53])).

fof(f1240,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_tsep_1(sK2,X0,X1),k1_tsep_1(sK2,sK1,sK2))
      | ~ m1_pre_topc(X1,sK1)
      | ~ m1_pre_topc(X0,sK2)
      | ~ m1_pre_topc(sK1,sK2)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(X1,sK2)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(sK2,sK2)
      | v2_struct_0(sK2)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2) ) ),
    inference(duplicate_literal_removal,[],[f1235])).

fof(f1235,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_tsep_1(sK2,X0,X1),k1_tsep_1(sK2,sK1,sK2))
      | ~ m1_pre_topc(X1,sK1)
      | ~ m1_pre_topc(X0,sK2)
      | ~ m1_pre_topc(sK1,sK2)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(X1,sK2)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(sK2,sK2)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(superposition,[],[f62,f626])).

fof(f1264,plain,
    ( ~ spl4_62
    | spl4_64 ),
    inference(avatar_split_clause,[],[f1259,f1261,f1248])).

fof(f1259,plain,
    ( m1_pre_topc(k1_tsep_1(sK2,sK1,sK2),sK2)
    | ~ m1_pre_topc(sK2,sK2) ),
    inference(subsumption_resolution,[],[f1258,f117])).

fof(f1258,plain,
    ( m1_pre_topc(k1_tsep_1(sK2,sK1,sK2),sK2)
    | ~ m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f1257,f49])).

fof(f1257,plain,
    ( m1_pre_topc(k1_tsep_1(sK2,sK1,sK2),sK2)
    | ~ m1_pre_topc(sK2,sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f1256,f47])).

fof(f1256,plain,
    ( m1_pre_topc(k1_tsep_1(sK2,sK1,sK2),sK2)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f1241,f53])).

fof(f1241,plain,
    ( m1_pre_topc(k1_tsep_1(sK2,sK1,sK2),sK2)
    | ~ m1_pre_topc(sK1,sK2)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(duplicate_literal_removal,[],[f1234])).

fof(f1234,plain,
    ( m1_pre_topc(k1_tsep_1(sK2,sK1,sK2),sK2)
    | ~ m1_pre_topc(sK1,sK2)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(superposition,[],[f71,f626])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:05:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (10739)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.49  % (10735)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.49  % (10738)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.50  % (10750)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.50  % (10739)Refutation not found, incomplete strategy% (10739)------------------------------
% 0.21/0.50  % (10739)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (10752)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.50  % (10739)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (10739)Memory used [KB]: 10618
% 0.21/0.50  % (10739)Time elapsed: 0.096 s
% 0.21/0.50  % (10739)------------------------------
% 0.21/0.50  % (10739)------------------------------
% 0.21/0.50  % (10733)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.50  % (10736)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.50  % (10744)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.50  % (10737)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (10747)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.51  % (10745)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.51  % (10734)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (10749)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.51  % (10741)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.51  % (10756)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.52  % (10751)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.52  % (10758)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.52  % (10742)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.52  % (10754)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.52  % (10748)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.52  % (10755)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.52  % (10746)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (10753)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.53  % (10757)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.53  % (10743)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.55  % (10740)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 2.08/0.67  % (10742)Refutation not found, incomplete strategy% (10742)------------------------------
% 2.08/0.67  % (10742)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.08/0.67  % (10742)Termination reason: Refutation not found, incomplete strategy
% 2.08/0.67  
% 2.08/0.67  % (10742)Memory used [KB]: 6140
% 2.08/0.67  % (10742)Time elapsed: 0.265 s
% 2.08/0.67  % (10742)------------------------------
% 2.08/0.67  % (10742)------------------------------
% 2.08/0.68  % (10733)Refutation not found, incomplete strategy% (10733)------------------------------
% 2.08/0.68  % (10733)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.08/0.68  % (10733)Termination reason: Refutation not found, incomplete strategy
% 2.08/0.68  
% 2.08/0.68  % (10733)Memory used [KB]: 12792
% 2.08/0.68  % (10733)Time elapsed: 0.262 s
% 2.08/0.68  % (10733)------------------------------
% 2.08/0.68  % (10733)------------------------------
% 3.21/0.83  % (10746)Refutation not found, incomplete strategy% (10746)------------------------------
% 3.21/0.83  % (10746)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.21/0.83  % (10746)Termination reason: Refutation not found, incomplete strategy
% 3.21/0.83  
% 3.21/0.83  % (10746)Memory used [KB]: 8443
% 3.21/0.83  % (10746)Time elapsed: 0.388 s
% 3.21/0.83  % (10746)------------------------------
% 3.21/0.83  % (10746)------------------------------
% 4.43/0.93  % (10747)Time limit reached!
% 4.43/0.93  % (10747)------------------------------
% 4.43/0.93  % (10747)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.43/0.93  % (10747)Termination reason: Time limit
% 4.43/0.93  % (10747)Termination phase: Saturation
% 4.43/0.93  
% 4.43/0.93  % (10747)Memory used [KB]: 7931
% 4.43/0.93  % (10747)Time elapsed: 0.500 s
% 4.43/0.93  % (10747)------------------------------
% 4.43/0.93  % (10747)------------------------------
% 5.65/1.11  % (10734)Refutation found. Thanks to Tanya!
% 5.65/1.11  % SZS status Theorem for theBenchmark
% 5.65/1.11  % SZS output start Proof for theBenchmark
% 5.65/1.11  fof(f15787,plain,(
% 5.65/1.11    $false),
% 5.65/1.11    inference(avatar_sat_refutation,[],[f1264,f1273,f1321,f1916,f1958,f15359,f15785])).
% 5.65/1.11  fof(f15785,plain,(
% 5.65/1.11    ~spl4_62 | ~spl4_64 | ~spl4_65 | ~spl4_98 | ~spl4_99),
% 5.65/1.11    inference(avatar_contradiction_clause,[],[f15784])).
% 5.65/1.11  fof(f15784,plain,(
% 5.65/1.11    $false | (~spl4_62 | ~spl4_64 | ~spl4_65 | ~spl4_98 | ~spl4_99)),
% 5.65/1.11    inference(subsumption_resolution,[],[f15783,f44])).
% 5.65/1.11  fof(f44,plain,(
% 5.65/1.11    ~v2_struct_0(sK0)),
% 5.65/1.11    inference(cnf_transformation,[],[f39])).
% 5.65/1.11  fof(f39,plain,(
% 5.65/1.11    (((~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) & m1_pre_topc(sK3,sK2) & m1_pre_topc(sK1,sK2) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 5.65/1.11    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f38,f37,f36,f35])).
% 5.65/1.11  fof(f35,plain,(
% 5.65/1.11    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(sK0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 5.65/1.11    introduced(choice_axiom,[])).
% 5.65/1.11  fof(f36,plain,(
% 5.65/1.11    ? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(sK0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(sK0,sK1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(sK1,X2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1))),
% 5.65/1.11    introduced(choice_axiom,[])).
% 5.65/1.11  fof(f37,plain,(
% 5.65/1.11    ? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(sK0,sK1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(sK1,X2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => (? [X3] : (~m1_pre_topc(k1_tsep_1(sK0,sK1,X3),sK2) & m1_pre_topc(X3,sK2) & m1_pre_topc(sK1,sK2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 5.65/1.11    introduced(choice_axiom,[])).
% 5.65/1.11  fof(f38,plain,(
% 5.65/1.11    ? [X3] : (~m1_pre_topc(k1_tsep_1(sK0,sK1,X3),sK2) & m1_pre_topc(X3,sK2) & m1_pre_topc(sK1,sK2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) => (~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) & m1_pre_topc(sK3,sK2) & m1_pre_topc(sK1,sK2) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3))),
% 5.65/1.11    introduced(choice_axiom,[])).
% 5.65/1.11  fof(f16,plain,(
% 5.65/1.11    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 5.65/1.11    inference(flattening,[],[f15])).
% 5.65/1.11  fof(f15,plain,(
% 5.65/1.11    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & (m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 5.65/1.11    inference(ennf_transformation,[],[f13])).
% 5.65/1.11  fof(f13,negated_conjecture,(
% 5.65/1.11    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ((m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2)) => m1_pre_topc(k1_tsep_1(X0,X1,X3),X2))))))),
% 5.65/1.11    inference(negated_conjecture,[],[f12])).
% 5.65/1.12  fof(f12,conjecture,(
% 5.65/1.12    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ((m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2)) => m1_pre_topc(k1_tsep_1(X0,X1,X3),X2))))))),
% 5.65/1.12    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tmap_1)).
% 5.65/1.12  fof(f15783,plain,(
% 5.65/1.12    v2_struct_0(sK0) | (~spl4_62 | ~spl4_64 | ~spl4_65 | ~spl4_98 | ~spl4_99)),
% 5.65/1.12    inference(subsumption_resolution,[],[f15782,f47])).
% 5.65/1.12  fof(f47,plain,(
% 5.65/1.12    ~v2_struct_0(sK1)),
% 5.65/1.12    inference(cnf_transformation,[],[f39])).
% 5.65/1.12  fof(f15782,plain,(
% 5.65/1.12    v2_struct_0(sK1) | v2_struct_0(sK0) | (~spl4_62 | ~spl4_64 | ~spl4_65 | ~spl4_98 | ~spl4_99)),
% 5.65/1.12    inference(subsumption_resolution,[],[f15781,f48])).
% 5.65/1.12  fof(f48,plain,(
% 5.65/1.12    m1_pre_topc(sK1,sK0)),
% 5.65/1.12    inference(cnf_transformation,[],[f39])).
% 5.65/1.12  fof(f15781,plain,(
% 5.65/1.12    ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | v2_struct_0(sK0) | (~spl4_62 | ~spl4_64 | ~spl4_65 | ~spl4_98 | ~spl4_99)),
% 5.65/1.12    inference(subsumption_resolution,[],[f15780,f51])).
% 5.65/1.12  fof(f51,plain,(
% 5.65/1.12    ~v2_struct_0(sK3)),
% 5.65/1.12    inference(cnf_transformation,[],[f39])).
% 5.65/1.12  fof(f15780,plain,(
% 5.65/1.12    v2_struct_0(sK3) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | v2_struct_0(sK0) | (~spl4_62 | ~spl4_64 | ~spl4_65 | ~spl4_98 | ~spl4_99)),
% 5.65/1.12    inference(subsumption_resolution,[],[f15779,f52])).
% 5.65/1.12  fof(f52,plain,(
% 5.65/1.12    m1_pre_topc(sK3,sK0)),
% 5.65/1.12    inference(cnf_transformation,[],[f39])).
% 5.65/1.12  fof(f15779,plain,(
% 5.65/1.12    ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | v2_struct_0(sK0) | (~spl4_62 | ~spl4_64 | ~spl4_65 | ~spl4_98 | ~spl4_99)),
% 5.65/1.12    inference(subsumption_resolution,[],[f15778,f45])).
% 5.65/1.12  fof(f45,plain,(
% 5.65/1.12    v2_pre_topc(sK0)),
% 5.65/1.12    inference(cnf_transformation,[],[f39])).
% 5.65/1.12  fof(f15778,plain,(
% 5.65/1.12    ~v2_pre_topc(sK0) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | v2_struct_0(sK0) | (~spl4_62 | ~spl4_64 | ~spl4_65 | ~spl4_98 | ~spl4_99)),
% 5.65/1.12    inference(subsumption_resolution,[],[f15777,f46])).
% 5.65/1.12  fof(f46,plain,(
% 5.65/1.12    l1_pre_topc(sK0)),
% 5.65/1.12    inference(cnf_transformation,[],[f39])).
% 5.65/1.12  fof(f15777,plain,(
% 5.65/1.12    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | v2_struct_0(sK0) | (~spl4_62 | ~spl4_64 | ~spl4_65 | ~spl4_98 | ~spl4_99)),
% 5.65/1.12    inference(subsumption_resolution,[],[f15697,f50])).
% 5.65/1.12  fof(f50,plain,(
% 5.65/1.12    m1_pre_topc(sK2,sK0)),
% 5.65/1.12    inference(cnf_transformation,[],[f39])).
% 5.65/1.12  fof(f15697,plain,(
% 5.65/1.12    ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | v2_struct_0(sK0) | (~spl4_62 | ~spl4_64 | ~spl4_65 | ~spl4_98 | ~spl4_99)),
% 5.65/1.12    inference(duplicate_literal_removal,[],[f15693])).
% 5.65/1.12  fof(f15693,plain,(
% 5.65/1.12    ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_62 | ~spl4_64 | ~spl4_65 | ~spl4_98 | ~spl4_99)),
% 5.65/1.12    inference(resolution,[],[f15550,f71])).
% 5.65/1.12  fof(f71,plain,(
% 5.65/1.12    ( ! [X2,X0,X1] : (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 5.65/1.12    inference(cnf_transformation,[],[f34])).
% 5.65/1.12  fof(f34,plain,(
% 5.65/1.12    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 5.65/1.12    inference(flattening,[],[f33])).
% 5.65/1.12  fof(f33,plain,(
% 5.65/1.12    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 5.65/1.12    inference(ennf_transformation,[],[f14])).
% 5.65/1.12  fof(f14,plain,(
% 5.65/1.12    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 5.65/1.12    inference(pure_predicate_removal,[],[f5])).
% 5.65/1.12  fof(f5,axiom,(
% 5.65/1.12    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 5.65/1.12    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tsep_1)).
% 5.65/1.12  fof(f15550,plain,(
% 5.65/1.12    ( ! [X0] : (~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X0) | ~m1_pre_topc(sK2,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | (~spl4_62 | ~spl4_64 | ~spl4_65 | ~spl4_98 | ~spl4_99)),
% 5.65/1.12    inference(subsumption_resolution,[],[f15548,f55])).
% 5.65/1.12  fof(f55,plain,(
% 5.65/1.12    ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2)),
% 5.65/1.12    inference(cnf_transformation,[],[f39])).
% 5.65/1.12  fof(f15548,plain,(
% 5.65/1.12    ( ! [X0] : (m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) | ~m1_pre_topc(sK2,X0) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | (~spl4_62 | ~spl4_64 | ~spl4_65 | ~spl4_98 | ~spl4_99)),
% 5.65/1.12    inference(resolution,[],[f15522,f64])).
% 5.65/1.12  fof(f64,plain,(
% 5.65/1.12    ( ! [X2,X0,X1] : (~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 5.65/1.12    inference(cnf_transformation,[],[f41])).
% 5.65/1.12  fof(f41,plain,(
% 5.65/1.12    ! [X0] : (! [X1] : (! [X2] : (((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 5.65/1.12    inference(nnf_transformation,[],[f30])).
% 5.65/1.12  fof(f30,plain,(
% 5.65/1.12    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 5.65/1.12    inference(flattening,[],[f29])).
% 5.65/1.12  fof(f29,plain,(
% 5.65/1.12    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 5.65/1.12    inference(ennf_transformation,[],[f11])).
% 5.65/1.12  fof(f11,axiom,(
% 5.65/1.12    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 5.65/1.12    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).
% 5.65/1.12  fof(f15522,plain,(
% 5.65/1.12    r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(sK2)) | (~spl4_62 | ~spl4_64 | ~spl4_65 | ~spl4_98 | ~spl4_99)),
% 5.65/1.12    inference(resolution,[],[f15474,f4889])).
% 5.65/1.12  fof(f4889,plain,(
% 5.65/1.12    m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK1,sK2)) | ~spl4_99),
% 5.65/1.12    inference(subsumption_resolution,[],[f4888,f51])).
% 5.65/1.12  fof(f4888,plain,(
% 5.65/1.12    m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK1,sK2)) | v2_struct_0(sK3) | ~spl4_99),
% 5.65/1.12    inference(subsumption_resolution,[],[f4887,f52])).
% 5.65/1.12  fof(f4887,plain,(
% 5.65/1.12    m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~spl4_99),
% 5.65/1.12    inference(subsumption_resolution,[],[f4886,f47])).
% 5.65/1.12  fof(f4886,plain,(
% 5.65/1.12    m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK1,sK2)) | v2_struct_0(sK1) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~spl4_99),
% 5.65/1.12    inference(subsumption_resolution,[],[f4885,f48])).
% 5.65/1.12  fof(f4885,plain,(
% 5.65/1.12    m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~spl4_99),
% 5.65/1.12    inference(subsumption_resolution,[],[f4884,f54])).
% 5.65/1.12  fof(f54,plain,(
% 5.65/1.12    m1_pre_topc(sK3,sK2)),
% 5.65/1.12    inference(cnf_transformation,[],[f39])).
% 5.65/1.12  fof(f4884,plain,(
% 5.65/1.12    m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(sK3,sK2) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~spl4_99),
% 5.65/1.12    inference(subsumption_resolution,[],[f4867,f1949])).
% 5.65/1.12  fof(f1949,plain,(
% 5.65/1.12    m1_pre_topc(sK1,sK1) | ~spl4_99),
% 5.65/1.12    inference(avatar_component_clause,[],[f1948])).
% 5.65/1.12  fof(f1948,plain,(
% 5.65/1.12    spl4_99 <=> m1_pre_topc(sK1,sK1)),
% 5.65/1.12    introduced(avatar_definition,[new_symbols(naming,[spl4_99])])).
% 5.65/1.12  fof(f4867,plain,(
% 5.65/1.12    m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(sK1,sK1) | ~m1_pre_topc(sK3,sK2) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3)),
% 5.65/1.12    inference(superposition,[],[f830,f482])).
% 5.65/1.12  fof(f482,plain,(
% 5.65/1.12    k1_tsep_1(sK0,sK1,sK3) = k1_tsep_1(sK0,sK3,sK1)),
% 5.65/1.12    inference(subsumption_resolution,[],[f475,f51])).
% 5.65/1.12  fof(f475,plain,(
% 5.65/1.12    k1_tsep_1(sK0,sK1,sK3) = k1_tsep_1(sK0,sK3,sK1) | v2_struct_0(sK3)),
% 5.65/1.12    inference(resolution,[],[f82,f52])).
% 5.65/1.12  fof(f82,plain,(
% 5.65/1.12    ( ! [X0] : (~m1_pre_topc(X0,sK0) | k1_tsep_1(sK0,X0,sK1) = k1_tsep_1(sK0,sK1,X0) | v2_struct_0(X0)) )),
% 5.65/1.12    inference(subsumption_resolution,[],[f81,f44])).
% 5.65/1.12  fof(f81,plain,(
% 5.65/1.12    ( ! [X0] : (k1_tsep_1(sK0,X0,sK1) = k1_tsep_1(sK0,sK1,X0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | v2_struct_0(sK0)) )),
% 5.65/1.12    inference(subsumption_resolution,[],[f80,f46])).
% 5.65/1.12  fof(f80,plain,(
% 5.65/1.12    ( ! [X0] : (k1_tsep_1(sK0,X0,sK1) = k1_tsep_1(sK0,sK1,X0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 5.65/1.12    inference(subsumption_resolution,[],[f74,f47])).
% 5.65/1.12  fof(f74,plain,(
% 5.65/1.12    ( ! [X0] : (k1_tsep_1(sK0,X0,sK1) = k1_tsep_1(sK0,sK1,X0) | v2_struct_0(sK1) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 5.65/1.12    inference(resolution,[],[f48,f69])).
% 5.65/1.12  fof(f69,plain,(
% 5.65/1.12    ( ! [X2,X0,X1] : (~m1_pre_topc(X2,X0) | k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 5.65/1.12    inference(cnf_transformation,[],[f32])).
% 5.65/1.12  fof(f32,plain,(
% 5.65/1.12    ! [X0,X1,X2] : (k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 5.65/1.12    inference(flattening,[],[f31])).
% 5.65/1.12  fof(f31,plain,(
% 5.65/1.12    ! [X0,X1,X2] : (k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 5.65/1.12    inference(ennf_transformation,[],[f4])).
% 5.65/1.12  fof(f4,axiom,(
% 5.65/1.12    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1))),
% 5.65/1.12    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k1_tsep_1)).
% 5.65/1.12  fof(f830,plain,(
% 5.65/1.12    ( ! [X0,X1] : (m1_pre_topc(k1_tsep_1(sK0,X0,X1),k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(X1,sK1) | ~m1_pre_topc(X0,sK2) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0)) )),
% 5.65/1.12    inference(subsumption_resolution,[],[f829,f44])).
% 5.65/1.12  fof(f829,plain,(
% 5.65/1.12    ( ! [X0,X1] : (m1_pre_topc(k1_tsep_1(sK0,X0,X1),k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(X1,sK1) | ~m1_pre_topc(X0,sK2) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | v2_struct_0(sK0)) )),
% 5.65/1.12    inference(subsumption_resolution,[],[f828,f45])).
% 5.65/1.12  fof(f828,plain,(
% 5.65/1.12    ( ! [X0,X1] : (m1_pre_topc(k1_tsep_1(sK0,X0,X1),k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(X1,sK1) | ~m1_pre_topc(X0,sK2) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 5.65/1.12    inference(subsumption_resolution,[],[f827,f46])).
% 5.65/1.12  fof(f827,plain,(
% 5.65/1.12    ( ! [X0,X1] : (m1_pre_topc(k1_tsep_1(sK0,X0,X1),k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(X1,sK1) | ~m1_pre_topc(X0,sK2) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 5.65/1.12    inference(subsumption_resolution,[],[f826,f49])).
% 5.65/1.12  fof(f49,plain,(
% 5.65/1.12    ~v2_struct_0(sK2)),
% 5.65/1.12    inference(cnf_transformation,[],[f39])).
% 5.65/1.12  fof(f826,plain,(
% 5.65/1.12    ( ! [X0,X1] : (m1_pre_topc(k1_tsep_1(sK0,X0,X1),k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(X1,sK1) | ~m1_pre_topc(X0,sK2) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | v2_struct_0(sK2) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 5.65/1.12    inference(subsumption_resolution,[],[f825,f50])).
% 5.65/1.12  fof(f825,plain,(
% 5.65/1.12    ( ! [X0,X1] : (m1_pre_topc(k1_tsep_1(sK0,X0,X1),k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(X1,sK1) | ~m1_pre_topc(X0,sK2) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 5.65/1.12    inference(subsumption_resolution,[],[f824,f47])).
% 5.65/1.12  fof(f824,plain,(
% 5.65/1.12    ( ! [X0,X1] : (m1_pre_topc(k1_tsep_1(sK0,X0,X1),k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(X1,sK1) | ~m1_pre_topc(X0,sK2) | v2_struct_0(sK1) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 5.65/1.12    inference(subsumption_resolution,[],[f821,f48])).
% 5.65/1.12  fof(f821,plain,(
% 5.65/1.12    ( ! [X0,X1] : (m1_pre_topc(k1_tsep_1(sK0,X0,X1),k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(X1,sK1) | ~m1_pre_topc(X0,sK2) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 5.65/1.12    inference(superposition,[],[f62,f481])).
% 5.65/1.12  fof(f481,plain,(
% 5.65/1.12    k1_tsep_1(sK0,sK2,sK1) = k1_tsep_1(sK0,sK1,sK2)),
% 5.65/1.12    inference(subsumption_resolution,[],[f474,f49])).
% 5.65/1.12  fof(f474,plain,(
% 5.65/1.12    k1_tsep_1(sK0,sK2,sK1) = k1_tsep_1(sK0,sK1,sK2) | v2_struct_0(sK2)),
% 5.65/1.12    inference(resolution,[],[f82,f50])).
% 5.65/1.12  fof(f62,plain,(
% 5.65/1.12    ( ! [X4,X2,X0,X3,X1] : (m1_pre_topc(k1_tsep_1(X0,X1,X3),k1_tsep_1(X0,X2,X4)) | ~m1_pre_topc(X3,X4) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 5.65/1.12    inference(cnf_transformation,[],[f26])).
% 5.65/1.12  fof(f26,plain,(
% 5.65/1.12    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (m1_pre_topc(k1_tsep_1(X0,X1,X3),k1_tsep_1(X0,X2,X4)) | ~m1_pre_topc(X3,X4) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 5.65/1.12    inference(flattening,[],[f25])).
% 5.65/1.12  fof(f25,plain,(
% 5.65/1.12    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((m1_pre_topc(k1_tsep_1(X0,X1,X3),k1_tsep_1(X0,X2,X4)) | (~m1_pre_topc(X3,X4) | ~m1_pre_topc(X1,X2))) | (~m1_pre_topc(X4,X0) | v2_struct_0(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 5.65/1.12    inference(ennf_transformation,[],[f9])).
% 5.65/1.12  fof(f9,axiom,(
% 5.65/1.12    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((m1_pre_topc(X3,X4) & m1_pre_topc(X1,X2)) => m1_pre_topc(k1_tsep_1(X0,X1,X3),k1_tsep_1(X0,X2,X4))))))))),
% 5.65/1.12    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_tmap_1)).
% 5.65/1.12  fof(f15474,plain,(
% 5.65/1.12    ( ! [X1] : (~m1_pre_topc(X1,k1_tsep_1(sK0,sK1,sK2)) | r1_tarski(u1_struct_0(X1),u1_struct_0(sK2))) ) | (~spl4_62 | ~spl4_64 | ~spl4_65 | ~spl4_98 | ~spl4_99)),
% 5.65/1.12    inference(backward_demodulation,[],[f14646,f1915])).
% 5.65/1.12  fof(f1915,plain,(
% 5.65/1.12    u1_struct_0(sK2) = u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~spl4_98),
% 5.65/1.12    inference(avatar_component_clause,[],[f1913])).
% 5.65/1.12  fof(f1913,plain,(
% 5.65/1.12    spl4_98 <=> u1_struct_0(sK2) = u1_struct_0(k1_tsep_1(sK0,sK1,sK2))),
% 5.65/1.12    introduced(avatar_definition,[new_symbols(naming,[spl4_98])])).
% 5.65/1.12  fof(f14646,plain,(
% 5.65/1.12    ( ! [X1] : (~m1_pre_topc(X1,k1_tsep_1(sK0,sK1,sK2)) | r1_tarski(u1_struct_0(X1),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))) ) | (~spl4_62 | ~spl4_64 | ~spl4_65 | ~spl4_99)),
% 5.65/1.12    inference(forward_demodulation,[],[f14645,f9479])).
% 5.65/1.12  fof(f9479,plain,(
% 5.65/1.12    k1_tsep_1(sK0,sK1,sK2) = k1_tsep_1(sK2,sK1,sK2) | ~spl4_62),
% 5.65/1.12    inference(subsumption_resolution,[],[f9469,f47])).
% 5.65/1.12  fof(f9469,plain,(
% 5.65/1.12    k1_tsep_1(sK0,sK1,sK2) = k1_tsep_1(sK2,sK1,sK2) | v2_struct_0(sK1) | ~spl4_62),
% 5.65/1.12    inference(resolution,[],[f3579,f53])).
% 5.65/1.12  fof(f53,plain,(
% 5.65/1.12    m1_pre_topc(sK1,sK2)),
% 5.65/1.12    inference(cnf_transformation,[],[f39])).
% 5.65/1.12  fof(f3579,plain,(
% 5.65/1.12    ( ! [X2] : (~m1_pre_topc(X2,sK2) | k1_tsep_1(sK0,sK1,sK2) = k1_tsep_1(sK2,X2,sK2) | v2_struct_0(X2)) ) | ~spl4_62),
% 5.65/1.12    inference(forward_demodulation,[],[f1346,f804])).
% 5.65/1.12  fof(f804,plain,(
% 5.65/1.12    k1_tsep_1(sK0,sK2,sK2) = k1_tsep_1(sK0,sK1,sK2)),
% 5.65/1.12    inference(subsumption_resolution,[],[f803,f47])).
% 5.65/1.12  fof(f803,plain,(
% 5.65/1.12    k1_tsep_1(sK0,sK2,sK2) = k1_tsep_1(sK0,sK1,sK2) | v2_struct_0(sK1)),
% 5.65/1.12    inference(subsumption_resolution,[],[f795,f48])).
% 5.65/1.12  fof(f795,plain,(
% 5.65/1.12    k1_tsep_1(sK0,sK2,sK2) = k1_tsep_1(sK0,sK1,sK2) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1)),
% 5.65/1.12    inference(resolution,[],[f768,f53])).
% 5.65/1.12  fof(f768,plain,(
% 5.65/1.12    ( ! [X2] : (~m1_pre_topc(X2,sK2) | k1_tsep_1(sK0,X2,sK2) = k1_tsep_1(sK0,sK2,sK2) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X2)) )),
% 5.65/1.12    inference(forward_demodulation,[],[f112,f116])).
% 5.65/1.12  fof(f116,plain,(
% 5.65/1.12    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK2,sK2)),
% 5.65/1.12    inference(subsumption_resolution,[],[f115,f44])).
% 5.65/1.12  fof(f115,plain,(
% 5.65/1.12    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK2,sK2) | v2_struct_0(sK0)),
% 5.65/1.12    inference(subsumption_resolution,[],[f114,f45])).
% 5.65/1.12  fof(f114,plain,(
% 5.65/1.12    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK2,sK2) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 5.65/1.12    inference(subsumption_resolution,[],[f113,f46])).
% 5.65/1.12  fof(f113,plain,(
% 5.65/1.12    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK2,sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 5.65/1.12    inference(subsumption_resolution,[],[f100,f49])).
% 5.65/1.12  fof(f100,plain,(
% 5.65/1.12    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK2,sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 5.65/1.12    inference(resolution,[],[f50,f58])).
% 5.65/1.12  fof(f58,plain,(
% 5.65/1.12    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 5.65/1.12    inference(cnf_transformation,[],[f20])).
% 5.65/1.12  fof(f20,plain,(
% 5.65/1.12    ! [X0] : (! [X1] : (k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 5.65/1.12    inference(flattening,[],[f19])).
% 5.65/1.12  fof(f19,plain,(
% 5.65/1.12    ! [X0] : (! [X1] : (k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 5.65/1.12    inference(ennf_transformation,[],[f8])).
% 5.65/1.12  fof(f8,axiom,(
% 5.65/1.12    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))),
% 5.65/1.12    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_tmap_1)).
% 5.65/1.12  fof(f112,plain,(
% 5.65/1.12    ( ! [X2] : (~m1_pre_topc(X2,sK2) | k1_tsep_1(sK0,X2,sK2) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X2)) )),
% 5.65/1.12    inference(subsumption_resolution,[],[f111,f44])).
% 5.65/1.12  fof(f111,plain,(
% 5.65/1.12    ( ! [X2] : (~m1_pre_topc(X2,sK2) | k1_tsep_1(sK0,X2,sK2) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X2) | v2_struct_0(sK0)) )),
% 5.65/1.12    inference(subsumption_resolution,[],[f110,f45])).
% 5.65/1.12  fof(f110,plain,(
% 5.65/1.12    ( ! [X2] : (~m1_pre_topc(X2,sK2) | k1_tsep_1(sK0,X2,sK2) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X2) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 5.65/1.12    inference(subsumption_resolution,[],[f109,f46])).
% 5.65/1.12  fof(f109,plain,(
% 5.65/1.12    ( ! [X2] : (~m1_pre_topc(X2,sK2) | k1_tsep_1(sK0,X2,sK2) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 5.65/1.12    inference(subsumption_resolution,[],[f99,f49])).
% 5.65/1.12  fof(f99,plain,(
% 5.65/1.12    ( ! [X2] : (~m1_pre_topc(X2,sK2) | k1_tsep_1(sK0,X2,sK2) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) | v2_struct_0(sK2) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 5.65/1.12    inference(resolution,[],[f50,f60])).
% 5.65/1.12  fof(f60,plain,(
% 5.65/1.12    ( ! [X2,X0,X1] : (~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X2) | k1_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 5.65/1.12    inference(cnf_transformation,[],[f40])).
% 5.65/1.12  fof(f40,plain,(
% 5.65/1.12    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X2) | k1_tsep_1(X0,X1,X2) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) & (k1_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) | ~m1_pre_topc(X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 5.65/1.12    inference(nnf_transformation,[],[f24])).
% 5.65/1.12  fof(f24,plain,(
% 5.65/1.12    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(X1,X2) <=> k1_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 5.65/1.12    inference(flattening,[],[f23])).
% 5.65/1.12  fof(f23,plain,(
% 5.65/1.12    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(X1,X2) <=> k1_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 5.65/1.12    inference(ennf_transformation,[],[f7])).
% 5.65/1.12  fof(f7,axiom,(
% 5.65/1.12    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (m1_pre_topc(X1,X2) <=> k1_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))),
% 5.65/1.12    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_tsep_1)).
% 5.65/1.12  fof(f1346,plain,(
% 5.65/1.12    ( ! [X2] : (k1_tsep_1(sK0,sK2,sK2) = k1_tsep_1(sK2,X2,sK2) | ~m1_pre_topc(X2,sK2) | v2_struct_0(X2)) ) | ~spl4_62),
% 5.65/1.12    inference(forward_demodulation,[],[f1345,f116])).
% 5.65/1.12  fof(f1345,plain,(
% 5.65/1.12    ( ! [X2] : (~m1_pre_topc(X2,sK2) | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK2,X2,sK2) | v2_struct_0(X2)) ) | ~spl4_62),
% 5.65/1.12    inference(subsumption_resolution,[],[f1344,f108])).
% 5.65/1.12  fof(f108,plain,(
% 5.65/1.12    v2_pre_topc(sK2)),
% 5.65/1.12    inference(subsumption_resolution,[],[f107,f45])).
% 5.65/1.12  fof(f107,plain,(
% 5.65/1.12    v2_pre_topc(sK2) | ~v2_pre_topc(sK0)),
% 5.65/1.12    inference(subsumption_resolution,[],[f98,f46])).
% 5.65/1.12  fof(f98,plain,(
% 5.65/1.12    v2_pre_topc(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 5.65/1.12    inference(resolution,[],[f50,f63])).
% 5.65/1.12  fof(f63,plain,(
% 5.65/1.12    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 5.65/1.12    inference(cnf_transformation,[],[f28])).
% 5.65/1.12  fof(f28,plain,(
% 5.65/1.12    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 5.65/1.12    inference(flattening,[],[f27])).
% 5.65/1.12  fof(f27,plain,(
% 5.65/1.12    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 5.65/1.12    inference(ennf_transformation,[],[f2])).
% 5.65/1.12  fof(f2,axiom,(
% 5.65/1.12    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 5.65/1.12    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).
% 5.65/1.12  fof(f1344,plain,(
% 5.65/1.12    ( ! [X2] : (~m1_pre_topc(X2,sK2) | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK2,X2,sK2) | v2_struct_0(X2) | ~v2_pre_topc(sK2)) ) | ~spl4_62),
% 5.65/1.12    inference(subsumption_resolution,[],[f1343,f117])).
% 5.65/1.12  fof(f117,plain,(
% 5.65/1.12    l1_pre_topc(sK2)),
% 5.65/1.12    inference(subsumption_resolution,[],[f101,f46])).
% 5.65/1.12  fof(f101,plain,(
% 5.65/1.12    l1_pre_topc(sK2) | ~l1_pre_topc(sK0)),
% 5.65/1.12    inference(resolution,[],[f50,f57])).
% 5.65/1.12  fof(f57,plain,(
% 5.65/1.12    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 5.65/1.12    inference(cnf_transformation,[],[f18])).
% 5.65/1.12  fof(f18,plain,(
% 5.65/1.12    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 5.65/1.12    inference(ennf_transformation,[],[f3])).
% 5.65/1.12  fof(f3,axiom,(
% 5.65/1.12    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 5.65/1.12    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 5.65/1.12  fof(f1343,plain,(
% 5.65/1.12    ( ! [X2] : (~m1_pre_topc(X2,sK2) | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK2,X2,sK2) | v2_struct_0(X2) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2)) ) | ~spl4_62),
% 5.65/1.12    inference(subsumption_resolution,[],[f1335,f49])).
% 5.65/1.12  fof(f1335,plain,(
% 5.65/1.12    ( ! [X2] : (~m1_pre_topc(X2,sK2) | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK2,X2,sK2) | v2_struct_0(sK2) | v2_struct_0(X2) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2)) ) | ~spl4_62),
% 5.65/1.12    inference(duplicate_literal_removal,[],[f1331])).
% 5.65/1.12  fof(f1331,plain,(
% 5.65/1.12    ( ! [X2] : (~m1_pre_topc(X2,sK2) | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK2,X2,sK2) | v2_struct_0(sK2) | ~m1_pre_topc(X2,sK2) | v2_struct_0(X2) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | ~spl4_62),
% 5.65/1.12    inference(resolution,[],[f1249,f60])).
% 5.65/1.12  fof(f1249,plain,(
% 5.65/1.12    m1_pre_topc(sK2,sK2) | ~spl4_62),
% 5.65/1.12    inference(avatar_component_clause,[],[f1248])).
% 5.65/1.12  fof(f1248,plain,(
% 5.65/1.12    spl4_62 <=> m1_pre_topc(sK2,sK2)),
% 5.65/1.12    introduced(avatar_definition,[new_symbols(naming,[spl4_62])])).
% 5.65/1.12  fof(f14645,plain,(
% 5.65/1.12    ( ! [X1] : (~m1_pre_topc(X1,k1_tsep_1(sK0,sK1,sK2)) | r1_tarski(u1_struct_0(X1),u1_struct_0(k1_tsep_1(sK2,sK1,sK2)))) ) | (~spl4_62 | ~spl4_64 | ~spl4_65 | ~spl4_99)),
% 5.65/1.12    inference(forward_demodulation,[],[f4624,f9479])).
% 5.65/1.12  fof(f4624,plain,(
% 5.65/1.12    ( ! [X1] : (~m1_pre_topc(X1,k1_tsep_1(sK2,sK1,sK2)) | r1_tarski(u1_struct_0(X1),u1_struct_0(k1_tsep_1(sK2,sK1,sK2)))) ) | (~spl4_62 | ~spl4_64 | ~spl4_65 | ~spl4_99)),
% 5.65/1.12    inference(subsumption_resolution,[],[f4623,f1439])).
% 5.65/1.12  fof(f1439,plain,(
% 5.65/1.12    v2_pre_topc(k1_tsep_1(sK2,sK1,sK2)) | ~spl4_64),
% 5.65/1.12    inference(subsumption_resolution,[],[f1438,f108])).
% 5.65/1.12  fof(f1438,plain,(
% 5.65/1.12    v2_pre_topc(k1_tsep_1(sK2,sK1,sK2)) | ~v2_pre_topc(sK2) | ~spl4_64),
% 5.65/1.12    inference(subsumption_resolution,[],[f1397,f117])).
% 5.65/1.12  fof(f1397,plain,(
% 5.65/1.12    v2_pre_topc(k1_tsep_1(sK2,sK1,sK2)) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | ~spl4_64),
% 5.65/1.12    inference(resolution,[],[f1263,f63])).
% 5.65/1.12  fof(f1263,plain,(
% 5.65/1.12    m1_pre_topc(k1_tsep_1(sK2,sK1,sK2),sK2) | ~spl4_64),
% 5.65/1.12    inference(avatar_component_clause,[],[f1261])).
% 5.65/1.12  fof(f1261,plain,(
% 5.65/1.12    spl4_64 <=> m1_pre_topc(k1_tsep_1(sK2,sK1,sK2),sK2)),
% 5.65/1.12    introduced(avatar_definition,[new_symbols(naming,[spl4_64])])).
% 5.65/1.12  fof(f4623,plain,(
% 5.65/1.12    ( ! [X1] : (~m1_pre_topc(X1,k1_tsep_1(sK2,sK1,sK2)) | r1_tarski(u1_struct_0(X1),u1_struct_0(k1_tsep_1(sK2,sK1,sK2))) | ~v2_pre_topc(k1_tsep_1(sK2,sK1,sK2))) ) | (~spl4_62 | ~spl4_64 | ~spl4_65 | ~spl4_99)),
% 5.65/1.12    inference(subsumption_resolution,[],[f4619,f1448])).
% 5.65/1.12  fof(f1448,plain,(
% 5.65/1.12    l1_pre_topc(k1_tsep_1(sK2,sK1,sK2)) | ~spl4_64),
% 5.65/1.12    inference(subsumption_resolution,[],[f1400,f117])).
% 5.65/1.12  fof(f1400,plain,(
% 5.65/1.12    l1_pre_topc(k1_tsep_1(sK2,sK1,sK2)) | ~l1_pre_topc(sK2) | ~spl4_64),
% 5.65/1.12    inference(resolution,[],[f1263,f57])).
% 5.65/1.12  fof(f4619,plain,(
% 5.65/1.12    ( ! [X1] : (~m1_pre_topc(X1,k1_tsep_1(sK2,sK1,sK2)) | r1_tarski(u1_struct_0(X1),u1_struct_0(k1_tsep_1(sK2,sK1,sK2))) | ~l1_pre_topc(k1_tsep_1(sK2,sK1,sK2)) | ~v2_pre_topc(k1_tsep_1(sK2,sK1,sK2))) ) | (~spl4_62 | ~spl4_65 | ~spl4_99)),
% 5.65/1.12    inference(duplicate_literal_removal,[],[f4612])).
% 5.65/1.12  fof(f4612,plain,(
% 5.65/1.12    ( ! [X1] : (~m1_pre_topc(X1,k1_tsep_1(sK2,sK1,sK2)) | r1_tarski(u1_struct_0(X1),u1_struct_0(k1_tsep_1(sK2,sK1,sK2))) | ~m1_pre_topc(X1,k1_tsep_1(sK2,sK1,sK2)) | ~l1_pre_topc(k1_tsep_1(sK2,sK1,sK2)) | ~v2_pre_topc(k1_tsep_1(sK2,sK1,sK2))) ) | (~spl4_62 | ~spl4_65 | ~spl4_99)),
% 5.65/1.12    inference(resolution,[],[f4430,f65])).
% 5.65/1.12  fof(f65,plain,(
% 5.65/1.12    ( ! [X2,X0,X1] : (~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X2) | r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 5.65/1.12    inference(cnf_transformation,[],[f41])).
% 5.65/1.12  fof(f4430,plain,(
% 5.65/1.12    m1_pre_topc(k1_tsep_1(sK2,sK1,sK2),k1_tsep_1(sK2,sK1,sK2)) | (~spl4_62 | ~spl4_65 | ~spl4_99)),
% 5.65/1.12    inference(subsumption_resolution,[],[f4429,f1949])).
% 5.65/1.12  fof(f4429,plain,(
% 5.65/1.12    m1_pre_topc(k1_tsep_1(sK2,sK1,sK2),k1_tsep_1(sK2,sK1,sK2)) | ~m1_pre_topc(sK1,sK1) | (~spl4_62 | ~spl4_65)),
% 5.65/1.12    inference(subsumption_resolution,[],[f4428,f1249])).
% 5.65/1.12  fof(f4428,plain,(
% 5.65/1.12    m1_pre_topc(k1_tsep_1(sK2,sK1,sK2),k1_tsep_1(sK2,sK1,sK2)) | ~m1_pre_topc(sK2,sK2) | ~m1_pre_topc(sK1,sK1) | ~spl4_65),
% 5.65/1.12    inference(subsumption_resolution,[],[f4427,f53])).
% 5.65/1.12  fof(f4427,plain,(
% 5.65/1.12    m1_pre_topc(k1_tsep_1(sK2,sK1,sK2),k1_tsep_1(sK2,sK1,sK2)) | ~m1_pre_topc(sK1,sK2) | ~m1_pre_topc(sK2,sK2) | ~m1_pre_topc(sK1,sK1) | ~spl4_65),
% 5.65/1.12    inference(subsumption_resolution,[],[f4426,f47])).
% 5.65/1.12  fof(f4426,plain,(
% 5.65/1.12    m1_pre_topc(k1_tsep_1(sK2,sK1,sK2),k1_tsep_1(sK2,sK1,sK2)) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK2) | ~m1_pre_topc(sK2,sK2) | ~m1_pre_topc(sK1,sK1) | ~spl4_65),
% 5.65/1.12    inference(subsumption_resolution,[],[f4394,f49])).
% 5.65/1.12  fof(f4394,plain,(
% 5.65/1.12    m1_pre_topc(k1_tsep_1(sK2,sK1,sK2),k1_tsep_1(sK2,sK1,sK2)) | v2_struct_0(sK2) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK2) | ~m1_pre_topc(sK2,sK2) | ~m1_pre_topc(sK1,sK1) | ~spl4_65),
% 5.65/1.12    inference(superposition,[],[f1272,f626])).
% 5.65/1.12  fof(f626,plain,(
% 5.65/1.12    k1_tsep_1(sK2,sK2,sK1) = k1_tsep_1(sK2,sK1,sK2)),
% 5.65/1.12    inference(subsumption_resolution,[],[f625,f117])).
% 5.65/1.12  fof(f625,plain,(
% 5.65/1.12    k1_tsep_1(sK2,sK2,sK1) = k1_tsep_1(sK2,sK1,sK2) | ~l1_pre_topc(sK2)),
% 5.65/1.12    inference(subsumption_resolution,[],[f619,f49])).
% 5.65/1.12  fof(f619,plain,(
% 5.65/1.12    k1_tsep_1(sK2,sK2,sK1) = k1_tsep_1(sK2,sK1,sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK2)),
% 5.65/1.12    inference(resolution,[],[f148,f56])).
% 5.65/1.12  fof(f56,plain,(
% 5.65/1.12    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 5.65/1.12    inference(cnf_transformation,[],[f17])).
% 5.65/1.12  fof(f17,plain,(
% 5.65/1.12    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 5.65/1.12    inference(ennf_transformation,[],[f10])).
% 5.65/1.12  fof(f10,axiom,(
% 5.65/1.12    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 5.65/1.12    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).
% 5.65/1.12  fof(f148,plain,(
% 5.65/1.12    ( ! [X0] : (~m1_pre_topc(X0,sK2) | k1_tsep_1(sK2,X0,sK1) = k1_tsep_1(sK2,sK1,X0) | v2_struct_0(X0)) )),
% 5.65/1.12    inference(subsumption_resolution,[],[f147,f49])).
% 5.65/1.12  fof(f147,plain,(
% 5.65/1.12    ( ! [X0] : (k1_tsep_1(sK2,X0,sK1) = k1_tsep_1(sK2,sK1,X0) | ~m1_pre_topc(X0,sK2) | v2_struct_0(X0) | v2_struct_0(sK2)) )),
% 5.65/1.12    inference(subsumption_resolution,[],[f146,f117])).
% 5.65/1.12  fof(f146,plain,(
% 5.65/1.12    ( ! [X0] : (k1_tsep_1(sK2,X0,sK1) = k1_tsep_1(sK2,sK1,X0) | ~m1_pre_topc(X0,sK2) | v2_struct_0(X0) | ~l1_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 5.65/1.12    inference(subsumption_resolution,[],[f140,f47])).
% 5.65/1.12  fof(f140,plain,(
% 5.65/1.12    ( ! [X0] : (k1_tsep_1(sK2,X0,sK1) = k1_tsep_1(sK2,sK1,X0) | v2_struct_0(sK1) | ~m1_pre_topc(X0,sK2) | v2_struct_0(X0) | ~l1_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 5.65/1.12    inference(resolution,[],[f53,f69])).
% 5.65/1.12  fof(f1272,plain,(
% 5.65/1.12    ( ! [X0,X1] : (m1_pre_topc(k1_tsep_1(sK2,X0,X1),k1_tsep_1(sK2,sK1,sK2)) | v2_struct_0(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK2) | ~m1_pre_topc(X0,sK2) | ~m1_pre_topc(X1,sK1)) ) | ~spl4_65),
% 5.65/1.12    inference(avatar_component_clause,[],[f1271])).
% 5.65/1.12  fof(f1271,plain,(
% 5.65/1.12    spl4_65 <=> ! [X1,X0] : (m1_pre_topc(k1_tsep_1(sK2,X0,X1),k1_tsep_1(sK2,sK1,sK2)) | v2_struct_0(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK2) | ~m1_pre_topc(X0,sK2) | ~m1_pre_topc(X1,sK1))),
% 5.65/1.12    introduced(avatar_definition,[new_symbols(naming,[spl4_65])])).
% 5.65/1.12  fof(f15359,plain,(
% 5.65/1.12    ~spl4_62 | ~spl4_64 | ~spl4_65 | spl4_97 | ~spl4_99),
% 5.65/1.12    inference(avatar_contradiction_clause,[],[f15358])).
% 5.65/1.12  fof(f15358,plain,(
% 5.65/1.12    $false | (~spl4_62 | ~spl4_64 | ~spl4_65 | spl4_97 | ~spl4_99)),
% 5.65/1.12    inference(subsumption_resolution,[],[f15338,f1911])).
% 5.65/1.12  fof(f1911,plain,(
% 5.65/1.12    ~r1_tarski(u1_struct_0(sK2),u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) | spl4_97),
% 5.65/1.12    inference(avatar_component_clause,[],[f1909])).
% 5.65/1.12  fof(f1909,plain,(
% 5.65/1.12    spl4_97 <=> r1_tarski(u1_struct_0(sK2),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))),
% 5.65/1.12    introduced(avatar_definition,[new_symbols(naming,[spl4_97])])).
% 5.65/1.12  fof(f15338,plain,(
% 5.65/1.12    r1_tarski(u1_struct_0(sK2),u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) | (~spl4_62 | ~spl4_64 | ~spl4_65 | ~spl4_99)),
% 5.65/1.12    inference(resolution,[],[f14646,f844])).
% 5.65/1.12  fof(f844,plain,(
% 5.65/1.12    m1_pre_topc(sK2,k1_tsep_1(sK0,sK1,sK2))),
% 5.65/1.12    inference(subsumption_resolution,[],[f843,f44])).
% 5.65/1.12  fof(f843,plain,(
% 5.65/1.12    m1_pre_topc(sK2,k1_tsep_1(sK0,sK1,sK2)) | v2_struct_0(sK0)),
% 5.65/1.12    inference(subsumption_resolution,[],[f842,f45])).
% 5.65/1.12  fof(f842,plain,(
% 5.65/1.12    m1_pre_topc(sK2,k1_tsep_1(sK0,sK1,sK2)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 5.65/1.12    inference(subsumption_resolution,[],[f841,f46])).
% 5.65/1.12  fof(f841,plain,(
% 5.65/1.12    m1_pre_topc(sK2,k1_tsep_1(sK0,sK1,sK2)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 5.65/1.12    inference(subsumption_resolution,[],[f840,f49])).
% 5.65/1.12  fof(f840,plain,(
% 5.65/1.12    m1_pre_topc(sK2,k1_tsep_1(sK0,sK1,sK2)) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 5.65/1.12    inference(subsumption_resolution,[],[f839,f50])).
% 5.65/1.12  fof(f839,plain,(
% 5.65/1.12    m1_pre_topc(sK2,k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 5.65/1.12    inference(subsumption_resolution,[],[f838,f47])).
% 5.65/1.12  fof(f838,plain,(
% 5.65/1.12    m1_pre_topc(sK2,k1_tsep_1(sK0,sK1,sK2)) | v2_struct_0(sK1) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 5.65/1.12    inference(subsumption_resolution,[],[f823,f48])).
% 5.65/1.12  fof(f823,plain,(
% 5.65/1.12    m1_pre_topc(sK2,k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 5.65/1.12    inference(superposition,[],[f59,f481])).
% 5.65/1.12  fof(f59,plain,(
% 5.65/1.12    ( ! [X2,X0,X1] : (m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 5.65/1.12    inference(cnf_transformation,[],[f22])).
% 5.65/1.12  fof(f22,plain,(
% 5.65/1.12    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 5.65/1.12    inference(flattening,[],[f21])).
% 5.65/1.12  fof(f21,plain,(
% 5.65/1.12    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 5.65/1.12    inference(ennf_transformation,[],[f6])).
% 5.65/1.12  fof(f6,axiom,(
% 5.65/1.12    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)))))),
% 5.65/1.12    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_tsep_1)).
% 5.65/1.12  fof(f1958,plain,(
% 5.65/1.12    spl4_99),
% 5.65/1.12    inference(avatar_contradiction_clause,[],[f1957])).
% 5.65/1.12  fof(f1957,plain,(
% 5.65/1.12    $false | spl4_99),
% 5.65/1.12    inference(subsumption_resolution,[],[f1956,f95])).
% 5.65/1.12  fof(f95,plain,(
% 5.65/1.12    l1_pre_topc(sK1)),
% 5.65/1.12    inference(subsumption_resolution,[],[f79,f46])).
% 5.65/1.12  fof(f79,plain,(
% 5.65/1.12    l1_pre_topc(sK1) | ~l1_pre_topc(sK0)),
% 5.65/1.12    inference(resolution,[],[f48,f57])).
% 5.65/1.12  fof(f1956,plain,(
% 5.65/1.12    ~l1_pre_topc(sK1) | spl4_99),
% 5.65/1.12    inference(resolution,[],[f1950,f56])).
% 5.65/1.12  fof(f1950,plain,(
% 5.65/1.12    ~m1_pre_topc(sK1,sK1) | spl4_99),
% 5.65/1.12    inference(avatar_component_clause,[],[f1948])).
% 5.65/1.12  fof(f1916,plain,(
% 5.65/1.12    ~spl4_97 | spl4_98 | ~spl4_62),
% 5.65/1.12    inference(avatar_split_clause,[],[f1907,f1248,f1913,f1909])).
% 5.65/1.12  fof(f1907,plain,(
% 5.65/1.12    u1_struct_0(sK2) = u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~r1_tarski(u1_struct_0(sK2),u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) | ~spl4_62),
% 5.65/1.12    inference(resolution,[],[f1836,f68])).
% 5.65/1.12  fof(f68,plain,(
% 5.65/1.12    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 5.65/1.12    inference(cnf_transformation,[],[f43])).
% 5.65/1.12  fof(f43,plain,(
% 5.65/1.12    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 5.65/1.12    inference(flattening,[],[f42])).
% 5.65/1.12  fof(f42,plain,(
% 5.65/1.12    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 5.65/1.12    inference(nnf_transformation,[],[f1])).
% 5.65/1.12  fof(f1,axiom,(
% 5.65/1.12    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 5.65/1.12    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 5.65/1.12  fof(f1836,plain,(
% 5.65/1.12    r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK2)) | ~spl4_62),
% 5.65/1.12    inference(subsumption_resolution,[],[f1835,f49])).
% 5.65/1.12  fof(f1835,plain,(
% 5.65/1.12    r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK2)) | v2_struct_0(sK2) | ~spl4_62),
% 5.65/1.12    inference(subsumption_resolution,[],[f1834,f1249])).
% 5.65/1.12  fof(f1834,plain,(
% 5.65/1.12    r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK2) | v2_struct_0(sK2) | ~spl4_62),
% 5.65/1.12    inference(subsumption_resolution,[],[f1833,f1529])).
% 5.65/1.12  fof(f1529,plain,(
% 5.65/1.12    m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)),
% 5.65/1.12    inference(subsumption_resolution,[],[f1528,f44])).
% 5.65/1.12  fof(f1528,plain,(
% 5.65/1.12    m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | v2_struct_0(sK0)),
% 5.65/1.12    inference(subsumption_resolution,[],[f1527,f46])).
% 5.65/1.12  fof(f1527,plain,(
% 5.65/1.12    m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 5.65/1.12    inference(subsumption_resolution,[],[f1526,f49])).
% 5.65/1.12  fof(f1526,plain,(
% 5.65/1.12    m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 5.65/1.12    inference(subsumption_resolution,[],[f1520,f50])).
% 5.65/1.12  fof(f1520,plain,(
% 5.65/1.12    m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 5.65/1.12    inference(duplicate_literal_removal,[],[f1513])).
% 5.65/1.12  fof(f1513,plain,(
% 5.65/1.12    m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 5.65/1.12    inference(superposition,[],[f71,f804])).
% 5.65/1.12  fof(f1833,plain,(
% 5.65/1.12    ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK2) | v2_struct_0(sK2) | ~spl4_62),
% 5.65/1.12    inference(duplicate_literal_removal,[],[f1822])).
% 5.65/1.12  fof(f1822,plain,(
% 5.65/1.12    ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK2) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK2) | v2_struct_0(sK2) | ~spl4_62),
% 5.65/1.12    inference(superposition,[],[f349,f1821])).
% 5.65/1.12  fof(f1821,plain,(
% 5.65/1.12    k1_tsep_1(sK0,sK1,sK2) = k1_tsep_1(sK2,sK2,sK2) | ~spl4_62),
% 5.65/1.12    inference(forward_demodulation,[],[f1350,f804])).
% 5.65/1.12  fof(f1350,plain,(
% 5.65/1.12    k1_tsep_1(sK0,sK2,sK2) = k1_tsep_1(sK2,sK2,sK2) | ~spl4_62),
% 5.65/1.12    inference(forward_demodulation,[],[f1349,f116])).
% 5.65/1.12  fof(f1349,plain,(
% 5.65/1.12    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK2,sK2,sK2) | ~spl4_62),
% 5.65/1.12    inference(subsumption_resolution,[],[f1348,f108])).
% 5.65/1.12  fof(f1348,plain,(
% 5.65/1.12    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK2,sK2,sK2) | ~v2_pre_topc(sK2) | ~spl4_62),
% 5.65/1.12    inference(subsumption_resolution,[],[f1347,f117])).
% 5.65/1.12  fof(f1347,plain,(
% 5.65/1.12    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK2,sK2,sK2) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | ~spl4_62),
% 5.65/1.12    inference(subsumption_resolution,[],[f1334,f49])).
% 5.65/1.12  fof(f1334,plain,(
% 5.65/1.12    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK2,sK2,sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | ~spl4_62),
% 5.65/1.12    inference(duplicate_literal_removal,[],[f1332])).
% 5.65/1.12  fof(f1332,plain,(
% 5.65/1.12    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK2,sK2,sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~spl4_62),
% 5.65/1.12    inference(resolution,[],[f1249,f58])).
% 5.65/1.12  fof(f349,plain,(
% 5.65/1.12    ( ! [X0,X1] : (~m1_pre_topc(k1_tsep_1(sK2,X0,X1),sK0) | r1_tarski(u1_struct_0(k1_tsep_1(sK2,X0,X1)),u1_struct_0(sK2)) | ~m1_pre_topc(X1,sK2) | v2_struct_0(X1) | ~m1_pre_topc(X0,sK2) | v2_struct_0(X0)) )),
% 5.65/1.12    inference(subsumption_resolution,[],[f348,f49])).
% 5.65/1.12  fof(f348,plain,(
% 5.65/1.12    ( ! [X0,X1] : (r1_tarski(u1_struct_0(k1_tsep_1(sK2,X0,X1)),u1_struct_0(sK2)) | ~m1_pre_topc(k1_tsep_1(sK2,X0,X1),sK0) | ~m1_pre_topc(X1,sK2) | v2_struct_0(X1) | ~m1_pre_topc(X0,sK2) | v2_struct_0(X0) | v2_struct_0(sK2)) )),
% 5.65/1.12    inference(subsumption_resolution,[],[f343,f117])).
% 5.65/1.12  fof(f343,plain,(
% 5.65/1.12    ( ! [X0,X1] : (r1_tarski(u1_struct_0(k1_tsep_1(sK2,X0,X1)),u1_struct_0(sK2)) | ~m1_pre_topc(k1_tsep_1(sK2,X0,X1),sK0) | ~m1_pre_topc(X1,sK2) | v2_struct_0(X1) | ~m1_pre_topc(X0,sK2) | v2_struct_0(X0) | ~l1_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 5.65/1.12    inference(resolution,[],[f106,f71])).
% 5.65/1.12  fof(f106,plain,(
% 5.65/1.12    ( ! [X1] : (~m1_pre_topc(X1,sK2) | r1_tarski(u1_struct_0(X1),u1_struct_0(sK2)) | ~m1_pre_topc(X1,sK0)) )),
% 5.65/1.12    inference(subsumption_resolution,[],[f105,f45])).
% 5.65/1.12  fof(f105,plain,(
% 5.65/1.12    ( ! [X1] : (~m1_pre_topc(X1,sK2) | r1_tarski(u1_struct_0(X1),u1_struct_0(sK2)) | ~m1_pre_topc(X1,sK0) | ~v2_pre_topc(sK0)) )),
% 5.65/1.12    inference(subsumption_resolution,[],[f97,f46])).
% 5.65/1.12  fof(f97,plain,(
% 5.65/1.12    ( ! [X1] : (~m1_pre_topc(X1,sK2) | r1_tarski(u1_struct_0(X1),u1_struct_0(sK2)) | ~m1_pre_topc(X1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 5.65/1.12    inference(resolution,[],[f50,f65])).
% 5.65/1.12  fof(f1321,plain,(
% 5.65/1.12    spl4_62),
% 5.65/1.12    inference(avatar_contradiction_clause,[],[f1320])).
% 5.65/1.12  fof(f1320,plain,(
% 5.65/1.12    $false | spl4_62),
% 5.65/1.12    inference(subsumption_resolution,[],[f1319,f117])).
% 5.65/1.12  fof(f1319,plain,(
% 5.65/1.12    ~l1_pre_topc(sK2) | spl4_62),
% 5.65/1.12    inference(resolution,[],[f1250,f56])).
% 5.65/1.12  fof(f1250,plain,(
% 5.65/1.12    ~m1_pre_topc(sK2,sK2) | spl4_62),
% 5.65/1.12    inference(avatar_component_clause,[],[f1248])).
% 5.65/1.12  fof(f1273,plain,(
% 5.65/1.12    ~spl4_62 | spl4_65),
% 5.65/1.12    inference(avatar_split_clause,[],[f1269,f1271,f1248])).
% 5.65/1.12  fof(f1269,plain,(
% 5.65/1.12    ( ! [X0,X1] : (m1_pre_topc(k1_tsep_1(sK2,X0,X1),k1_tsep_1(sK2,sK1,sK2)) | ~m1_pre_topc(X1,sK1) | ~m1_pre_topc(X0,sK2) | ~m1_pre_topc(X1,sK2) | v2_struct_0(X1) | ~m1_pre_topc(sK2,sK2) | v2_struct_0(X0)) )),
% 5.65/1.12    inference(subsumption_resolution,[],[f1268,f108])).
% 5.65/1.12  fof(f1268,plain,(
% 5.65/1.12    ( ! [X0,X1] : (m1_pre_topc(k1_tsep_1(sK2,X0,X1),k1_tsep_1(sK2,sK1,sK2)) | ~m1_pre_topc(X1,sK1) | ~m1_pre_topc(X0,sK2) | ~m1_pre_topc(X1,sK2) | v2_struct_0(X1) | ~m1_pre_topc(sK2,sK2) | v2_struct_0(X0) | ~v2_pre_topc(sK2)) )),
% 5.65/1.12    inference(subsumption_resolution,[],[f1267,f117])).
% 5.65/1.12  fof(f1267,plain,(
% 5.65/1.12    ( ! [X0,X1] : (m1_pre_topc(k1_tsep_1(sK2,X0,X1),k1_tsep_1(sK2,sK1,sK2)) | ~m1_pre_topc(X1,sK1) | ~m1_pre_topc(X0,sK2) | ~m1_pre_topc(X1,sK2) | v2_struct_0(X1) | ~m1_pre_topc(sK2,sK2) | v2_struct_0(X0) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2)) )),
% 5.65/1.12    inference(subsumption_resolution,[],[f1266,f49])).
% 5.65/1.12  fof(f1266,plain,(
% 5.65/1.12    ( ! [X0,X1] : (m1_pre_topc(k1_tsep_1(sK2,X0,X1),k1_tsep_1(sK2,sK1,sK2)) | ~m1_pre_topc(X1,sK1) | ~m1_pre_topc(X0,sK2) | ~m1_pre_topc(X1,sK2) | v2_struct_0(X1) | ~m1_pre_topc(sK2,sK2) | v2_struct_0(sK2) | v2_struct_0(X0) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2)) )),
% 5.65/1.12    inference(subsumption_resolution,[],[f1265,f47])).
% 5.65/1.12  fof(f1265,plain,(
% 5.65/1.12    ( ! [X0,X1] : (m1_pre_topc(k1_tsep_1(sK2,X0,X1),k1_tsep_1(sK2,sK1,sK2)) | ~m1_pre_topc(X1,sK1) | ~m1_pre_topc(X0,sK2) | v2_struct_0(sK1) | ~m1_pre_topc(X1,sK2) | v2_struct_0(X1) | ~m1_pre_topc(sK2,sK2) | v2_struct_0(sK2) | v2_struct_0(X0) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2)) )),
% 5.65/1.12    inference(subsumption_resolution,[],[f1240,f53])).
% 5.65/1.12  fof(f1240,plain,(
% 5.65/1.12    ( ! [X0,X1] : (m1_pre_topc(k1_tsep_1(sK2,X0,X1),k1_tsep_1(sK2,sK1,sK2)) | ~m1_pre_topc(X1,sK1) | ~m1_pre_topc(X0,sK2) | ~m1_pre_topc(sK1,sK2) | v2_struct_0(sK1) | ~m1_pre_topc(X1,sK2) | v2_struct_0(X1) | ~m1_pre_topc(sK2,sK2) | v2_struct_0(sK2) | v2_struct_0(X0) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2)) )),
% 5.65/1.12    inference(duplicate_literal_removal,[],[f1235])).
% 5.65/1.12  fof(f1235,plain,(
% 5.65/1.12    ( ! [X0,X1] : (m1_pre_topc(k1_tsep_1(sK2,X0,X1),k1_tsep_1(sK2,sK1,sK2)) | ~m1_pre_topc(X1,sK1) | ~m1_pre_topc(X0,sK2) | ~m1_pre_topc(sK1,sK2) | v2_struct_0(sK1) | ~m1_pre_topc(X1,sK2) | v2_struct_0(X1) | ~m1_pre_topc(sK2,sK2) | v2_struct_0(sK2) | ~m1_pre_topc(X0,sK2) | v2_struct_0(X0) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 5.65/1.12    inference(superposition,[],[f62,f626])).
% 5.65/1.12  fof(f1264,plain,(
% 5.65/1.12    ~spl4_62 | spl4_64),
% 5.65/1.12    inference(avatar_split_clause,[],[f1259,f1261,f1248])).
% 5.65/1.12  fof(f1259,plain,(
% 5.65/1.12    m1_pre_topc(k1_tsep_1(sK2,sK1,sK2),sK2) | ~m1_pre_topc(sK2,sK2)),
% 5.65/1.12    inference(subsumption_resolution,[],[f1258,f117])).
% 5.65/1.12  fof(f1258,plain,(
% 5.65/1.12    m1_pre_topc(k1_tsep_1(sK2,sK1,sK2),sK2) | ~m1_pre_topc(sK2,sK2) | ~l1_pre_topc(sK2)),
% 5.65/1.12    inference(subsumption_resolution,[],[f1257,f49])).
% 5.65/1.12  fof(f1257,plain,(
% 5.65/1.12    m1_pre_topc(k1_tsep_1(sK2,sK1,sK2),sK2) | ~m1_pre_topc(sK2,sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK2)),
% 5.65/1.12    inference(subsumption_resolution,[],[f1256,f47])).
% 5.65/1.12  fof(f1256,plain,(
% 5.65/1.12    m1_pre_topc(k1_tsep_1(sK2,sK1,sK2),sK2) | v2_struct_0(sK1) | ~m1_pre_topc(sK2,sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK2)),
% 5.65/1.12    inference(subsumption_resolution,[],[f1241,f53])).
% 5.65/1.12  fof(f1241,plain,(
% 5.65/1.12    m1_pre_topc(k1_tsep_1(sK2,sK1,sK2),sK2) | ~m1_pre_topc(sK1,sK2) | v2_struct_0(sK1) | ~m1_pre_topc(sK2,sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK2)),
% 5.65/1.12    inference(duplicate_literal_removal,[],[f1234])).
% 5.65/1.12  fof(f1234,plain,(
% 5.65/1.12    m1_pre_topc(k1_tsep_1(sK2,sK1,sK2),sK2) | ~m1_pre_topc(sK1,sK2) | v2_struct_0(sK1) | ~m1_pre_topc(sK2,sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK2) | v2_struct_0(sK2)),
% 5.65/1.12    inference(superposition,[],[f71,f626])).
% 5.65/1.12  % SZS output end Proof for theBenchmark
% 5.65/1.12  % (10734)------------------------------
% 5.65/1.12  % (10734)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.65/1.12  % (10734)Termination reason: Refutation
% 5.65/1.12  
% 5.65/1.12  % (10734)Memory used [KB]: 17014
% 5.65/1.12  % (10734)Time elapsed: 0.699 s
% 5.65/1.12  % (10734)------------------------------
% 5.65/1.12  % (10734)------------------------------
% 5.65/1.12  % (10732)Success in time 0.762 s
%------------------------------------------------------------------------------
