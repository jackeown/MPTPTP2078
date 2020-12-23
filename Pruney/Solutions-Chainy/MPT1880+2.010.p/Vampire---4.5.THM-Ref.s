%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:52 EST 2020

% Result     : Theorem 1.78s
% Output     : Refutation 1.78s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 647 expanded)
%              Number of leaves         :   13 ( 197 expanded)
%              Depth                    :   25
%              Number of atoms          :  456 (4558 expanded)
%              Number of equality atoms :   68 ( 202 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f919,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f273,f918])).

fof(f918,plain,(
    ~ spl4_8 ),
    inference(avatar_contradiction_clause,[],[f917])).

fof(f917,plain,
    ( $false
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f916,f82])).

fof(f82,plain,(
    sK1 != sK2(sK0,sK1) ),
    inference(subsumption_resolution,[],[f81,f38])).

fof(f38,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ~ v3_tex_2(sK1,sK0)
    & v2_tex_2(sK1,sK0)
    & v1_tops_1(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f23,f22])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v3_tex_2(X1,X0)
            & v2_tex_2(X1,X0)
            & v1_tops_1(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ v3_tex_2(X1,sK0)
          & v2_tex_2(X1,sK0)
          & v1_tops_1(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X1] :
        ( ~ v3_tex_2(X1,sK0)
        & v2_tex_2(X1,sK0)
        & v1_tops_1(X1,sK0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ v3_tex_2(sK1,sK0)
      & v2_tex_2(sK1,sK0)
      & v1_tops_1(sK1,sK0)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_tex_2(X1,X0)
          & v2_tex_2(X1,X0)
          & v1_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_tex_2(X1,X0)
          & v2_tex_2(X1,X0)
          & v1_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ( v2_tex_2(X1,X0)
                & v1_tops_1(X1,X0) )
             => v3_tex_2(X1,X0) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v2_tex_2(X1,X0)
              & v1_tops_1(X1,X0) )
           => v3_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tex_2)).

fof(f81,plain,
    ( sK1 != sK2(sK0,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f80,f42])).

fof(f42,plain,(
    ~ v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f80,plain,
    ( sK1 != sK2(sK0,sK1)
    | v3_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f79,f41])).

fof(f41,plain,(
    v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f79,plain,
    ( sK1 != sK2(sK0,sK1)
    | ~ v2_tex_2(sK1,sK0)
    | v3_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f48,f39])).

fof(f39,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f24])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | sK2(X0,X1) != X1
      | ~ v2_tex_2(X1,X0)
      | v3_tex_2(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ( sK2(X0,X1) != X1
                & r1_tarski(X1,sK2(X0,X1))
                & v2_tex_2(sK2(X0,X1),X0)
                & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X3] :
                    ( X1 = X3
                    | ~ r1_tarski(X1,X3)
                    | ~ v2_tex_2(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f27,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r1_tarski(X1,X2)
          & v2_tex_2(X2,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( sK2(X0,X1) != X1
        & r1_tarski(X1,sK2(X0,X1))
        & v2_tex_2(sK2(X0,X1),X0)
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X3] :
                    ( X1 = X3
                    | ~ r1_tarski(X1,X3)
                    | ~ v2_tex_2(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X2] :
                    ( X1 = X2
                    | ~ r1_tarski(X1,X2)
                    | ~ v2_tex_2(X2,X0)
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X2] :
                    ( X1 = X2
                    | ~ r1_tarski(X1,X2)
                    | ~ v2_tex_2(X2,X0)
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r1_tarski(X1,X2)
                      & v2_tex_2(X2,X0) )
                   => X1 = X2 ) )
              & v2_tex_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).

fof(f916,plain,
    ( sK1 = sK2(sK0,sK1)
    | ~ spl4_8 ),
    inference(forward_demodulation,[],[f915,f314])).

fof(f314,plain,(
    sK1 = k9_subset_1(u1_struct_0(sK0),sK2(sK0,sK1),u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f313,f69])).

fof(f69,plain,(
    u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f68,f38])).

fof(f68,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f67,f40])).

fof(f40,plain,(
    v1_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f67,plain,
    ( ~ v1_tops_1(sK1,sK0)
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f49,f39])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tops_1(X1,X0)
      | u1_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | u1_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( u1_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_3)).

fof(f313,plain,(
    sK1 = k9_subset_1(u1_struct_0(sK0),sK2(sK0,sK1),k2_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f312,f36])).

fof(f36,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f312,plain,
    ( sK1 = k9_subset_1(u1_struct_0(sK0),sK2(sK0,sK1),k2_pre_topc(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f311,f37])).

fof(f37,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f311,plain,
    ( sK1 = k9_subset_1(u1_struct_0(sK0),sK2(sK0,sK1),k2_pre_topc(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f310,f38])).

fof(f310,plain,
    ( sK1 = k9_subset_1(u1_struct_0(sK0),sK2(sK0,sK1),k2_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f309,f74])).

fof(f74,plain,(
    v2_tex_2(sK2(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f73,f38])).

fof(f73,plain,
    ( v2_tex_2(sK2(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f72,f42])).

fof(f72,plain,
    ( v2_tex_2(sK2(sK0,sK1),sK0)
    | v3_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f71,f41])).

fof(f71,plain,
    ( v2_tex_2(sK2(sK0,sK1),sK0)
    | ~ v2_tex_2(sK1,sK0)
    | v3_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f46,f39])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tex_2(sK2(X0,X1),X0)
      | ~ v2_tex_2(X1,X0)
      | v3_tex_2(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f309,plain,
    ( ~ v2_tex_2(sK2(sK0,sK1),sK0)
    | sK1 = k9_subset_1(u1_struct_0(sK0),sK2(sK0,sK1),k2_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f307,f39])).

fof(f307,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(sK2(sK0,sK1),sK0)
    | sK1 = k9_subset_1(u1_struct_0(sK0),sK2(sK0,sK1),k2_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f136,f87])).

fof(f87,plain,(
    m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f86,f38])).

fof(f86,plain,
    ( m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f85,f42])).

fof(f85,plain,
    ( m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f84,f41])).

fof(f84,plain,
    ( m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(sK1,sK0)
    | v3_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f45,f39])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | v3_tex_2(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f136,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(sK2(sK0,sK1),X0)
      | sK1 = k9_subset_1(u1_struct_0(X0),sK2(sK0,sK1),k2_pre_topc(X0,sK1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f78,f52])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(X3,X1)
      | k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ( sK3(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK3(X0,X1)))
                & r1_tarski(sK3(X0,X1),X1)
                & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
                  | ~ r1_tarski(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f32,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( sK3(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK3(X0,X1)))
        & r1_tarski(sK3(X0,X1),X1)
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
                  | ~ r1_tarski(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
                  | ~ r1_tarski(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
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
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r1_tarski(X2,X1)
                 => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_tex_2)).

fof(f78,plain,(
    r1_tarski(sK1,sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f77,f38])).

fof(f77,plain,
    ( r1_tarski(sK1,sK2(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f76,f42])).

fof(f76,plain,
    ( r1_tarski(sK1,sK2(sK0,sK1))
    | v3_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f75,f41])).

fof(f75,plain,
    ( r1_tarski(sK1,sK2(sK0,sK1))
    | ~ v2_tex_2(sK1,sK0)
    | v3_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f47,f39])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(X1,sK2(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | v3_tex_2(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f915,plain,
    ( sK2(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),sK2(sK0,sK1),u1_struct_0(sK0))
    | ~ spl4_8 ),
    inference(forward_demodulation,[],[f914,f497])).

fof(f497,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,sK2(sK0,sK1))
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f196,f200])).

fof(f200,plain,
    ( v1_tops_1(sK2(sK0,sK1),sK0)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f199])).

fof(f199,plain,
    ( spl4_8
  <=> v1_tops_1(sK2(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f196,plain,
    ( ~ v1_tops_1(sK2(sK0,sK1),sK0)
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f154,f38])).

fof(f154,plain,
    ( ~ v1_tops_1(sK2(sK0,sK1),sK0)
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK2(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f87,f49])).

fof(f914,plain,(
    sK2(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),sK2(sK0,sK1),k2_pre_topc(sK0,sK2(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f913,f36])).

fof(f913,plain,
    ( sK2(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),sK2(sK0,sK1),k2_pre_topc(sK0,sK2(sK0,sK1)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f912,f37])).

fof(f912,plain,
    ( sK2(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),sK2(sK0,sK1),k2_pre_topc(sK0,sK2(sK0,sK1)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f911,f38])).

fof(f911,plain,
    ( sK2(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),sK2(sK0,sK1),k2_pre_topc(sK0,sK2(sK0,sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f910,f74])).

fof(f910,plain,
    ( sK2(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),sK2(sK0,sK1),k2_pre_topc(sK0,sK2(sK0,sK1)))
    | ~ v2_tex_2(sK2(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f637,f87])).

fof(f637,plain,(
    ! [X2] :
      ( ~ m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(X2)))
      | sK2(sK0,sK1) = k9_subset_1(u1_struct_0(X2),sK2(sK0,sK1),k2_pre_topc(X2,sK2(sK0,sK1)))
      | ~ v2_tex_2(sK2(sK0,sK1),X2)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2) ) ),
    inference(duplicate_literal_removal,[],[f635])).

fof(f635,plain,(
    ! [X2] :
      ( ~ m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(X2)))
      | sK2(sK0,sK1) = k9_subset_1(u1_struct_0(X2),sK2(sK0,sK1),k2_pre_topc(X2,sK2(sK0,sK1)))
      | ~ v2_tex_2(sK2(sK0,sK1),X2)
      | ~ m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2) ) ),
    inference(superposition,[],[f130,f597])).

fof(f597,plain,(
    sK2(sK0,sK1) = k3_xboole_0(sK2(sK0,sK1),sK2(sK0,sK1)) ),
    inference(superposition,[],[f159,f63])).

fof(f63,plain,(
    ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,X0) = X0 ),
    inference(resolution,[],[f59,f39])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X1) = X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

fof(f159,plain,(
    ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK2(sK0,sK1)) = k3_xboole_0(X0,sK2(sK0,sK1)) ),
    inference(resolution,[],[f87,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f130,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | k3_xboole_0(X1,X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k3_xboole_0(X1,X2)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f52,f56])).

fof(f56,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f273,plain,(
    spl4_8 ),
    inference(avatar_contradiction_clause,[],[f272])).

fof(f272,plain,
    ( $false
    | spl4_8 ),
    inference(subsumption_resolution,[],[f271,f38])).

fof(f271,plain,
    ( ~ l1_pre_topc(sK0)
    | spl4_8 ),
    inference(subsumption_resolution,[],[f270,f39])).

fof(f270,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl4_8 ),
    inference(subsumption_resolution,[],[f269,f201])).

fof(f201,plain,
    ( ~ v1_tops_1(sK2(sK0,sK1),sK0)
    | spl4_8 ),
    inference(avatar_component_clause,[],[f199])).

fof(f269,plain,
    ( v1_tops_1(sK2(sK0,sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f267,f40])).

fof(f267,plain,
    ( ~ v1_tops_1(sK1,sK0)
    | v1_tops_1(sK2(sK0,sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f138,f87])).

fof(f138,plain,(
    ! [X2] :
      ( ~ m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v1_tops_1(sK1,X2)
      | v1_tops_1(sK2(sK0,sK1),X2)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(resolution,[],[f78,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | v1_tops_1(X2,X0)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v1_tops_1(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ v1_tops_1(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v1_tops_1(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ v1_tops_1(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

% (2795)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% (2800)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% (2813)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X1,X2)
                  & v1_tops_1(X1,X0) )
               => v1_tops_1(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_tops_1)).

% (2811)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:04:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.52  % (2806)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.53  % (2788)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.53  % (2796)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.53  % (2798)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.54  % (2810)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.54  % (2797)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.54  % (2794)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.56  % (2792)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.56  % (2793)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.56  % (2791)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.56  % (2794)Refutation not found, incomplete strategy% (2794)------------------------------
% 0.21/0.56  % (2794)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (2794)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (2794)Memory used [KB]: 10746
% 0.21/0.56  % (2794)Time elapsed: 0.054 s
% 0.21/0.56  % (2794)------------------------------
% 0.21/0.56  % (2794)------------------------------
% 1.59/0.56  % (2788)Refutation not found, incomplete strategy% (2788)------------------------------
% 1.59/0.56  % (2788)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.56  % (2788)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.56  
% 1.59/0.56  % (2788)Memory used [KB]: 10618
% 1.59/0.56  % (2788)Time elapsed: 0.104 s
% 1.59/0.56  % (2788)------------------------------
% 1.59/0.56  % (2788)------------------------------
% 1.59/0.56  % (2790)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.59/0.57  % (2805)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.59/0.57  % (2802)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.59/0.57  % (2799)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.59/0.58  % (2808)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.59/0.58  % (2807)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.78/0.58  % (2801)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.78/0.58  % (2798)Refutation found. Thanks to Tanya!
% 1.78/0.58  % SZS status Theorem for theBenchmark
% 1.78/0.58  % SZS output start Proof for theBenchmark
% 1.78/0.58  fof(f919,plain,(
% 1.78/0.58    $false),
% 1.78/0.58    inference(avatar_sat_refutation,[],[f273,f918])).
% 1.78/0.58  fof(f918,plain,(
% 1.78/0.58    ~spl4_8),
% 1.78/0.58    inference(avatar_contradiction_clause,[],[f917])).
% 1.78/0.58  fof(f917,plain,(
% 1.78/0.58    $false | ~spl4_8),
% 1.78/0.58    inference(subsumption_resolution,[],[f916,f82])).
% 1.78/0.58  fof(f82,plain,(
% 1.78/0.58    sK1 != sK2(sK0,sK1)),
% 1.78/0.58    inference(subsumption_resolution,[],[f81,f38])).
% 1.78/0.58  fof(f38,plain,(
% 1.78/0.58    l1_pre_topc(sK0)),
% 1.78/0.58    inference(cnf_transformation,[],[f24])).
% 1.78/0.58  fof(f24,plain,(
% 1.78/0.58    (~v3_tex_2(sK1,sK0) & v2_tex_2(sK1,sK0) & v1_tops_1(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.78/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f23,f22])).
% 1.78/0.58  fof(f22,plain,(
% 1.78/0.58    ? [X0] : (? [X1] : (~v3_tex_2(X1,X0) & v2_tex_2(X1,X0) & v1_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (~v3_tex_2(X1,sK0) & v2_tex_2(X1,sK0) & v1_tops_1(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.78/0.58    introduced(choice_axiom,[])).
% 1.78/0.58  fof(f23,plain,(
% 1.78/0.58    ? [X1] : (~v3_tex_2(X1,sK0) & v2_tex_2(X1,sK0) & v1_tops_1(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (~v3_tex_2(sK1,sK0) & v2_tex_2(sK1,sK0) & v1_tops_1(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.78/0.58    introduced(choice_axiom,[])).
% 1.78/0.58  fof(f12,plain,(
% 1.78/0.58    ? [X0] : (? [X1] : (~v3_tex_2(X1,X0) & v2_tex_2(X1,X0) & v1_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.78/0.58    inference(flattening,[],[f11])).
% 1.78/0.58  fof(f11,plain,(
% 1.78/0.58    ? [X0] : (? [X1] : ((~v3_tex_2(X1,X0) & (v2_tex_2(X1,X0) & v1_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.78/0.58    inference(ennf_transformation,[],[f10])).
% 1.78/0.58  fof(f10,negated_conjecture,(
% 1.78/0.58    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & v1_tops_1(X1,X0)) => v3_tex_2(X1,X0))))),
% 1.78/0.58    inference(negated_conjecture,[],[f9])).
% 1.78/0.58  fof(f9,conjecture,(
% 1.78/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & v1_tops_1(X1,X0)) => v3_tex_2(X1,X0))))),
% 1.78/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tex_2)).
% 1.78/0.58  fof(f81,plain,(
% 1.78/0.58    sK1 != sK2(sK0,sK1) | ~l1_pre_topc(sK0)),
% 1.78/0.58    inference(subsumption_resolution,[],[f80,f42])).
% 1.78/0.58  fof(f42,plain,(
% 1.78/0.58    ~v3_tex_2(sK1,sK0)),
% 1.78/0.58    inference(cnf_transformation,[],[f24])).
% 1.78/0.58  fof(f80,plain,(
% 1.78/0.58    sK1 != sK2(sK0,sK1) | v3_tex_2(sK1,sK0) | ~l1_pre_topc(sK0)),
% 1.78/0.58    inference(subsumption_resolution,[],[f79,f41])).
% 1.78/0.58  fof(f41,plain,(
% 1.78/0.58    v2_tex_2(sK1,sK0)),
% 1.78/0.58    inference(cnf_transformation,[],[f24])).
% 1.78/0.58  fof(f79,plain,(
% 1.78/0.58    sK1 != sK2(sK0,sK1) | ~v2_tex_2(sK1,sK0) | v3_tex_2(sK1,sK0) | ~l1_pre_topc(sK0)),
% 1.78/0.58    inference(resolution,[],[f48,f39])).
% 1.78/0.58  fof(f39,plain,(
% 1.78/0.58    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.78/0.58    inference(cnf_transformation,[],[f24])).
% 1.78/0.58  fof(f48,plain,(
% 1.78/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | sK2(X0,X1) != X1 | ~v2_tex_2(X1,X0) | v3_tex_2(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.78/0.58    inference(cnf_transformation,[],[f29])).
% 1.78/0.58  fof(f29,plain,(
% 1.78/0.58    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (sK2(X0,X1) != X1 & r1_tarski(X1,sK2(X0,X1)) & v2_tex_2(sK2(X0,X1),X0) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.78/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f27,f28])).
% 1.78/0.58  fof(f28,plain,(
% 1.78/0.58    ! [X1,X0] : (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (sK2(X0,X1) != X1 & r1_tarski(X1,sK2(X0,X1)) & v2_tex_2(sK2(X0,X1),X0) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.78/0.58    introduced(choice_axiom,[])).
% 1.78/0.58  fof(f27,plain,(
% 1.78/0.58    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.78/0.58    inference(rectify,[],[f26])).
% 1.78/0.58  fof(f26,plain,(
% 1.78/0.58    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.78/0.58    inference(flattening,[],[f25])).
% 1.78/0.58  fof(f25,plain,(
% 1.78/0.58    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.78/0.58    inference(nnf_transformation,[],[f14])).
% 1.78/0.58  fof(f14,plain,(
% 1.78/0.58    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.78/0.58    inference(flattening,[],[f13])).
% 1.78/0.58  fof(f13,plain,(
% 1.78/0.58    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.78/0.58    inference(ennf_transformation,[],[f7])).
% 1.78/0.58  fof(f7,axiom,(
% 1.78/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 1.78/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).
% 1.78/0.58  fof(f916,plain,(
% 1.78/0.58    sK1 = sK2(sK0,sK1) | ~spl4_8),
% 1.78/0.58    inference(forward_demodulation,[],[f915,f314])).
% 1.78/0.58  fof(f314,plain,(
% 1.78/0.58    sK1 = k9_subset_1(u1_struct_0(sK0),sK2(sK0,sK1),u1_struct_0(sK0))),
% 1.78/0.58    inference(forward_demodulation,[],[f313,f69])).
% 1.78/0.58  fof(f69,plain,(
% 1.78/0.58    u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 1.78/0.58    inference(subsumption_resolution,[],[f68,f38])).
% 1.78/0.58  fof(f68,plain,(
% 1.78/0.58    u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | ~l1_pre_topc(sK0)),
% 1.78/0.58    inference(subsumption_resolution,[],[f67,f40])).
% 1.78/0.58  fof(f40,plain,(
% 1.78/0.58    v1_tops_1(sK1,sK0)),
% 1.78/0.58    inference(cnf_transformation,[],[f24])).
% 1.78/0.58  fof(f67,plain,(
% 1.78/0.58    ~v1_tops_1(sK1,sK0) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | ~l1_pre_topc(sK0)),
% 1.78/0.58    inference(resolution,[],[f49,f39])).
% 1.78/0.58  fof(f49,plain,(
% 1.78/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tops_1(X1,X0) | u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~l1_pre_topc(X0)) )),
% 1.78/0.58    inference(cnf_transformation,[],[f30])).
% 1.78/0.58  fof(f30,plain,(
% 1.78/0.58    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | u1_struct_0(X0) != k2_pre_topc(X0,X1)) & (u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.78/0.58    inference(nnf_transformation,[],[f15])).
% 1.78/0.58  fof(f15,plain,(
% 1.78/0.58    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.78/0.58    inference(ennf_transformation,[],[f6])).
% 1.78/0.58  fof(f6,axiom,(
% 1.78/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 1.78/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_3)).
% 1.78/0.58  fof(f313,plain,(
% 1.78/0.58    sK1 = k9_subset_1(u1_struct_0(sK0),sK2(sK0,sK1),k2_pre_topc(sK0,sK1))),
% 1.78/0.58    inference(subsumption_resolution,[],[f312,f36])).
% 1.78/0.58  fof(f36,plain,(
% 1.78/0.58    ~v2_struct_0(sK0)),
% 1.78/0.58    inference(cnf_transformation,[],[f24])).
% 1.78/0.58  fof(f312,plain,(
% 1.78/0.58    sK1 = k9_subset_1(u1_struct_0(sK0),sK2(sK0,sK1),k2_pre_topc(sK0,sK1)) | v2_struct_0(sK0)),
% 1.78/0.58    inference(subsumption_resolution,[],[f311,f37])).
% 1.78/0.58  fof(f37,plain,(
% 1.78/0.58    v2_pre_topc(sK0)),
% 1.78/0.58    inference(cnf_transformation,[],[f24])).
% 1.78/0.58  fof(f311,plain,(
% 1.78/0.58    sK1 = k9_subset_1(u1_struct_0(sK0),sK2(sK0,sK1),k2_pre_topc(sK0,sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.78/0.58    inference(subsumption_resolution,[],[f310,f38])).
% 1.78/0.58  fof(f310,plain,(
% 1.78/0.58    sK1 = k9_subset_1(u1_struct_0(sK0),sK2(sK0,sK1),k2_pre_topc(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.78/0.58    inference(subsumption_resolution,[],[f309,f74])).
% 1.78/0.58  fof(f74,plain,(
% 1.78/0.58    v2_tex_2(sK2(sK0,sK1),sK0)),
% 1.78/0.58    inference(subsumption_resolution,[],[f73,f38])).
% 1.78/0.58  fof(f73,plain,(
% 1.78/0.58    v2_tex_2(sK2(sK0,sK1),sK0) | ~l1_pre_topc(sK0)),
% 1.78/0.58    inference(subsumption_resolution,[],[f72,f42])).
% 1.78/0.58  fof(f72,plain,(
% 1.78/0.58    v2_tex_2(sK2(sK0,sK1),sK0) | v3_tex_2(sK1,sK0) | ~l1_pre_topc(sK0)),
% 1.78/0.58    inference(subsumption_resolution,[],[f71,f41])).
% 1.78/0.58  fof(f71,plain,(
% 1.78/0.58    v2_tex_2(sK2(sK0,sK1),sK0) | ~v2_tex_2(sK1,sK0) | v3_tex_2(sK1,sK0) | ~l1_pre_topc(sK0)),
% 1.78/0.58    inference(resolution,[],[f46,f39])).
% 1.78/0.58  fof(f46,plain,(
% 1.78/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tex_2(sK2(X0,X1),X0) | ~v2_tex_2(X1,X0) | v3_tex_2(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.78/0.58    inference(cnf_transformation,[],[f29])).
% 1.78/0.58  fof(f309,plain,(
% 1.78/0.58    ~v2_tex_2(sK2(sK0,sK1),sK0) | sK1 = k9_subset_1(u1_struct_0(sK0),sK2(sK0,sK1),k2_pre_topc(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.78/0.58    inference(subsumption_resolution,[],[f307,f39])).
% 1.78/0.58  fof(f307,plain,(
% 1.78/0.58    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(sK2(sK0,sK1),sK0) | sK1 = k9_subset_1(u1_struct_0(sK0),sK2(sK0,sK1),k2_pre_topc(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.78/0.58    inference(resolution,[],[f136,f87])).
% 1.78/0.58  fof(f87,plain,(
% 1.78/0.58    m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.78/0.58    inference(subsumption_resolution,[],[f86,f38])).
% 1.78/0.58  fof(f86,plain,(
% 1.78/0.58    m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 1.78/0.58    inference(subsumption_resolution,[],[f85,f42])).
% 1.78/0.58  fof(f85,plain,(
% 1.78/0.58    m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v3_tex_2(sK1,sK0) | ~l1_pre_topc(sK0)),
% 1.78/0.58    inference(subsumption_resolution,[],[f84,f41])).
% 1.78/0.58  fof(f84,plain,(
% 1.78/0.58    m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(sK1,sK0) | v3_tex_2(sK1,sK0) | ~l1_pre_topc(sK0)),
% 1.78/0.58    inference(resolution,[],[f45,f39])).
% 1.78/0.58  fof(f45,plain,(
% 1.78/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | v3_tex_2(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.78/0.58    inference(cnf_transformation,[],[f29])).
% 1.78/0.58  fof(f136,plain,(
% 1.78/0.58    ( ! [X0] : (~m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(sK2(sK0,sK1),X0) | sK1 = k9_subset_1(u1_struct_0(X0),sK2(sK0,sK1),k2_pre_topc(X0,sK1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.78/0.58    inference(resolution,[],[f78,f52])).
% 1.78/0.58  fof(f52,plain,(
% 1.78/0.58    ( ! [X0,X3,X1] : (~r1_tarski(X3,X1) | k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.78/0.58    inference(cnf_transformation,[],[f34])).
% 1.78/0.58  fof(f34,plain,(
% 1.78/0.58    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | (sK3(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK3(X0,X1))) & r1_tarski(sK3(X0,X1),X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.78/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f32,f33])).
% 1.78/0.58  fof(f33,plain,(
% 1.78/0.58    ! [X1,X0] : (? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (sK3(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK3(X0,X1))) & r1_tarski(sK3(X0,X1),X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.78/0.58    introduced(choice_axiom,[])).
% 1.78/0.58  fof(f32,plain,(
% 1.78/0.58    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.78/0.58    inference(rectify,[],[f31])).
% 1.78/0.58  fof(f31,plain,(
% 1.78/0.58    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.78/0.58    inference(nnf_transformation,[],[f19])).
% 1.78/0.58  fof(f19,plain,(
% 1.78/0.58    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.78/0.58    inference(flattening,[],[f18])).
% 1.78/0.58  fof(f18,plain,(
% 1.78/0.58    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.78/0.58    inference(ennf_transformation,[],[f8])).
% 1.78/0.58  fof(f8,axiom,(
% 1.78/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X2,X1) => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2)))))),
% 1.78/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_tex_2)).
% 1.78/0.58  fof(f78,plain,(
% 1.78/0.58    r1_tarski(sK1,sK2(sK0,sK1))),
% 1.78/0.58    inference(subsumption_resolution,[],[f77,f38])).
% 1.78/0.58  fof(f77,plain,(
% 1.78/0.58    r1_tarski(sK1,sK2(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 1.78/0.58    inference(subsumption_resolution,[],[f76,f42])).
% 1.78/0.58  fof(f76,plain,(
% 1.78/0.58    r1_tarski(sK1,sK2(sK0,sK1)) | v3_tex_2(sK1,sK0) | ~l1_pre_topc(sK0)),
% 1.78/0.58    inference(subsumption_resolution,[],[f75,f41])).
% 1.78/0.58  fof(f75,plain,(
% 1.78/0.58    r1_tarski(sK1,sK2(sK0,sK1)) | ~v2_tex_2(sK1,sK0) | v3_tex_2(sK1,sK0) | ~l1_pre_topc(sK0)),
% 1.78/0.58    inference(resolution,[],[f47,f39])).
% 1.78/0.58  fof(f47,plain,(
% 1.78/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(X1,sK2(X0,X1)) | ~v2_tex_2(X1,X0) | v3_tex_2(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.78/0.58    inference(cnf_transformation,[],[f29])).
% 1.78/0.58  fof(f915,plain,(
% 1.78/0.58    sK2(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),sK2(sK0,sK1),u1_struct_0(sK0)) | ~spl4_8),
% 1.78/0.58    inference(forward_demodulation,[],[f914,f497])).
% 1.78/0.58  fof(f497,plain,(
% 1.78/0.58    u1_struct_0(sK0) = k2_pre_topc(sK0,sK2(sK0,sK1)) | ~spl4_8),
% 1.78/0.58    inference(subsumption_resolution,[],[f196,f200])).
% 1.78/0.58  fof(f200,plain,(
% 1.78/0.58    v1_tops_1(sK2(sK0,sK1),sK0) | ~spl4_8),
% 1.78/0.58    inference(avatar_component_clause,[],[f199])).
% 1.78/0.58  fof(f199,plain,(
% 1.78/0.58    spl4_8 <=> v1_tops_1(sK2(sK0,sK1),sK0)),
% 1.78/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.78/0.58  fof(f196,plain,(
% 1.78/0.58    ~v1_tops_1(sK2(sK0,sK1),sK0) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK2(sK0,sK1))),
% 1.78/0.58    inference(subsumption_resolution,[],[f154,f38])).
% 1.78/0.58  fof(f154,plain,(
% 1.78/0.58    ~v1_tops_1(sK2(sK0,sK1),sK0) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK2(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 1.78/0.58    inference(resolution,[],[f87,f49])).
% 1.78/0.58  fof(f914,plain,(
% 1.78/0.58    sK2(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),sK2(sK0,sK1),k2_pre_topc(sK0,sK2(sK0,sK1)))),
% 1.78/0.58    inference(subsumption_resolution,[],[f913,f36])).
% 1.78/0.58  fof(f913,plain,(
% 1.78/0.58    sK2(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),sK2(sK0,sK1),k2_pre_topc(sK0,sK2(sK0,sK1))) | v2_struct_0(sK0)),
% 1.78/0.58    inference(subsumption_resolution,[],[f912,f37])).
% 1.78/0.58  fof(f912,plain,(
% 1.78/0.58    sK2(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),sK2(sK0,sK1),k2_pre_topc(sK0,sK2(sK0,sK1))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.78/0.58    inference(subsumption_resolution,[],[f911,f38])).
% 1.78/0.58  fof(f911,plain,(
% 1.78/0.58    sK2(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),sK2(sK0,sK1),k2_pre_topc(sK0,sK2(sK0,sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.78/0.58    inference(subsumption_resolution,[],[f910,f74])).
% 1.78/0.58  fof(f910,plain,(
% 1.78/0.58    sK2(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),sK2(sK0,sK1),k2_pre_topc(sK0,sK2(sK0,sK1))) | ~v2_tex_2(sK2(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.78/0.58    inference(resolution,[],[f637,f87])).
% 1.78/0.58  fof(f637,plain,(
% 1.78/0.58    ( ! [X2] : (~m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(X2))) | sK2(sK0,sK1) = k9_subset_1(u1_struct_0(X2),sK2(sK0,sK1),k2_pre_topc(X2,sK2(sK0,sK1))) | ~v2_tex_2(sK2(sK0,sK1),X2) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) )),
% 1.78/0.58    inference(duplicate_literal_removal,[],[f635])).
% 1.78/0.58  fof(f635,plain,(
% 1.78/0.58    ( ! [X2] : (~m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(X2))) | sK2(sK0,sK1) = k9_subset_1(u1_struct_0(X2),sK2(sK0,sK1),k2_pre_topc(X2,sK2(sK0,sK1))) | ~v2_tex_2(sK2(sK0,sK1),X2) | ~m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) )),
% 1.78/0.58    inference(superposition,[],[f130,f597])).
% 1.78/0.58  fof(f597,plain,(
% 1.78/0.58    sK2(sK0,sK1) = k3_xboole_0(sK2(sK0,sK1),sK2(sK0,sK1))),
% 1.78/0.58    inference(superposition,[],[f159,f63])).
% 1.78/0.58  fof(f63,plain,(
% 1.78/0.58    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),X0,X0) = X0) )),
% 1.78/0.58    inference(resolution,[],[f59,f39])).
% 1.78/0.58  fof(f59,plain,(
% 1.78/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X1) = X1) )),
% 1.78/0.58    inference(cnf_transformation,[],[f20])).
% 1.78/0.58  fof(f20,plain,(
% 1.78/0.58    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.78/0.58    inference(ennf_transformation,[],[f2])).
% 1.78/0.58  fof(f2,axiom,(
% 1.78/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X1) = X1)),
% 1.78/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k9_subset_1)).
% 1.78/0.58  fof(f159,plain,(
% 1.78/0.58    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),X0,sK2(sK0,sK1)) = k3_xboole_0(X0,sK2(sK0,sK1))) )),
% 1.78/0.58    inference(resolution,[],[f87,f60])).
% 1.78/0.58  fof(f60,plain,(
% 1.78/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 1.78/0.58    inference(cnf_transformation,[],[f21])).
% 1.78/0.58  fof(f21,plain,(
% 1.78/0.58    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.78/0.58    inference(ennf_transformation,[],[f3])).
% 1.78/0.58  fof(f3,axiom,(
% 1.78/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 1.78/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 1.78/0.58  fof(f130,plain,(
% 1.78/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | k3_xboole_0(X1,X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k3_xboole_0(X1,X2))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.78/0.58    inference(resolution,[],[f52,f56])).
% 1.78/0.58  fof(f56,plain,(
% 1.78/0.58    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.78/0.58    inference(cnf_transformation,[],[f1])).
% 1.78/0.58  fof(f1,axiom,(
% 1.78/0.58    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.78/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.78/0.58  fof(f273,plain,(
% 1.78/0.58    spl4_8),
% 1.78/0.58    inference(avatar_contradiction_clause,[],[f272])).
% 1.78/0.58  fof(f272,plain,(
% 1.78/0.58    $false | spl4_8),
% 1.78/0.58    inference(subsumption_resolution,[],[f271,f38])).
% 1.78/0.58  fof(f271,plain,(
% 1.78/0.58    ~l1_pre_topc(sK0) | spl4_8),
% 1.78/0.58    inference(subsumption_resolution,[],[f270,f39])).
% 1.78/0.58  fof(f270,plain,(
% 1.78/0.58    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl4_8),
% 1.78/0.58    inference(subsumption_resolution,[],[f269,f201])).
% 1.78/0.58  fof(f201,plain,(
% 1.78/0.58    ~v1_tops_1(sK2(sK0,sK1),sK0) | spl4_8),
% 1.78/0.58    inference(avatar_component_clause,[],[f199])).
% 1.78/0.58  fof(f269,plain,(
% 1.78/0.58    v1_tops_1(sK2(sK0,sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 1.78/0.58    inference(subsumption_resolution,[],[f267,f40])).
% 1.78/0.58  fof(f267,plain,(
% 1.78/0.58    ~v1_tops_1(sK1,sK0) | v1_tops_1(sK2(sK0,sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 1.78/0.58    inference(resolution,[],[f138,f87])).
% 1.78/0.58  fof(f138,plain,(
% 1.78/0.58    ( ! [X2] : (~m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(X2))) | ~v1_tops_1(sK1,X2) | v1_tops_1(sK2(sK0,sK1),X2) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 1.78/0.58    inference(resolution,[],[f78,f51])).
% 1.78/0.58  fof(f51,plain,(
% 1.78/0.58    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | v1_tops_1(X2,X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.78/0.58    inference(cnf_transformation,[],[f17])).
% 1.78/0.58  fof(f17,plain,(
% 1.78/0.58    ! [X0] : (! [X1] : (! [X2] : (v1_tops_1(X2,X0) | ~r1_tarski(X1,X2) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.78/0.58    inference(flattening,[],[f16])).
% 1.78/0.58  fof(f16,plain,(
% 1.78/0.58    ! [X0] : (! [X1] : (! [X2] : ((v1_tops_1(X2,X0) | (~r1_tarski(X1,X2) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.78/0.58    inference(ennf_transformation,[],[f5])).
% 1.78/0.59  % (2795)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.78/0.59  % (2800)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.78/0.59  % (2813)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.78/0.59  fof(f5,axiom,(
% 1.78/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v1_tops_1(X1,X0)) => v1_tops_1(X2,X0)))))),
% 1.78/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_tops_1)).
% 1.78/0.59  % (2811)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.78/0.59  % SZS output end Proof for theBenchmark
% 1.78/0.59  % (2798)------------------------------
% 1.78/0.59  % (2798)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.78/0.59  % (2798)Termination reason: Refutation
% 1.78/0.59  
% 1.78/0.59  % (2798)Memory used [KB]: 11129
% 1.78/0.59  % (2798)Time elapsed: 0.126 s
% 1.78/0.59  % (2798)------------------------------
% 1.78/0.59  % (2798)------------------------------
% 1.78/0.59  % (2787)Success in time 0.235 s
%------------------------------------------------------------------------------
