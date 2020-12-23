%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:44 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  126 (1410 expanded)
%              Number of leaves         :   17 ( 504 expanded)
%              Depth                    :   28
%              Number of atoms          :  555 (10525 expanded)
%              Number of equality atoms :   55 ( 285 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f371,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f107,f194,f242,f291,f370])).

fof(f370,plain,(
    ~ spl4_11 ),
    inference(avatar_contradiction_clause,[],[f369])).

fof(f369,plain,
    ( $false
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f368,f44])).

fof(f44,plain,(
    ~ v2_compts_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ~ v2_compts_1(sK2,sK0)
    & v4_pre_topc(sK2,sK0)
    & r1_tarski(sK2,sK1)
    & v2_compts_1(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f29,f28,f27])).

fof(f27,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v2_compts_1(X2,X0)
                & v4_pre_topc(X2,X0)
                & r1_tarski(X2,X1)
                & v2_compts_1(X1,X0)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_compts_1(X2,sK0)
              & v4_pre_topc(X2,sK0)
              & r1_tarski(X2,X1)
              & v2_compts_1(X1,sK0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v2_compts_1(X2,sK0)
            & v4_pre_topc(X2,sK0)
            & r1_tarski(X2,X1)
            & v2_compts_1(X1,sK0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ~ v2_compts_1(X2,sK0)
          & v4_pre_topc(X2,sK0)
          & r1_tarski(X2,sK1)
          & v2_compts_1(sK1,sK0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X2] :
        ( ~ v2_compts_1(X2,sK0)
        & v4_pre_topc(X2,sK0)
        & r1_tarski(X2,sK1)
        & v2_compts_1(sK1,sK0)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ v2_compts_1(sK2,sK0)
      & v4_pre_topc(sK2,sK0)
      & r1_tarski(sK2,sK1)
      & v2_compts_1(sK1,sK0)
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_compts_1(X2,X0)
              & v4_pre_topc(X2,X0)
              & r1_tarski(X2,X1)
              & v2_compts_1(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_compts_1(X2,X0)
              & v4_pre_topc(X2,X0)
              & r1_tarski(X2,X1)
              & v2_compts_1(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v4_pre_topc(X2,X0)
                    & r1_tarski(X2,X1)
                    & v2_compts_1(X1,X0) )
                 => v2_compts_1(X2,X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v4_pre_topc(X2,X0)
                  & r1_tarski(X2,X1)
                  & v2_compts_1(X1,X0) )
               => v2_compts_1(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_compts_1)).

fof(f368,plain,
    ( v2_compts_1(sK2,sK0)
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f367,f38])).

fof(f38,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f367,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_compts_1(sK2,sK0)
    | ~ spl4_11 ),
    inference(resolution,[],[f312,f75])).

fof(f75,plain,(
    m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f73,f38])).

fof(f73,plain,
    ( m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f60,f39])).

fof(f39,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f30])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_pre_topc)).

fof(f312,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(k1_pre_topc(sK0,sK1),X0)
        | ~ l1_pre_topc(X0)
        | v2_compts_1(sK2,X0) )
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f189,f195])).

fof(f195,plain,(
    ! [X0] :
      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f181,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).

fof(f181,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1)))) ),
    inference(forward_demodulation,[],[f180,f160])).

fof(f160,plain,(
    sK2 = sK3(k1_pre_topc(sK0,sK1),sK2) ),
    inference(subsumption_resolution,[],[f159,f38])).

fof(f159,plain,
    ( sK2 = sK3(k1_pre_topc(sK0,sK1),sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f158,f75])).

fof(f158,plain,
    ( sK2 = sK3(k1_pre_topc(sK0,sK1),sK2)
    | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f157,f42])).

fof(f42,plain,(
    r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f157,plain,
    ( sK2 = sK3(k1_pre_topc(sK0,sK1),sK2)
    | ~ r1_tarski(sK2,sK1)
    | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f156,f44])).

fof(f156,plain,
    ( sK2 = sK3(k1_pre_topc(sK0,sK1),sK2)
    | v2_compts_1(sK2,sK0)
    | ~ r1_tarski(sK2,sK1)
    | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f146,f40])).

fof(f40,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f30])).

fof(f146,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
      | sK3(k1_pre_topc(sK0,sK1),X2) = X2
      | v2_compts_1(X2,X3)
      | ~ r1_tarski(X2,sK1)
      | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),X3)
      | ~ l1_pre_topc(X3) ) ),
    inference(superposition,[],[f49,f137])).

fof(f137,plain,(
    sK1 = k2_struct_0(k1_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f136,f38])).

fof(f136,plain,
    ( sK1 = k2_struct_0(k1_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f135,f39])).

fof(f135,plain,
    ( sK1 = k2_struct_0(k1_pre_topc(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f133,f71])).

fof(f71,plain,(
    v1_pre_topc(k1_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f69,f38])).

fof(f69,plain,
    ( v1_pre_topc(k1_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f59,f39])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f133,plain,
    ( sK1 = k2_struct_0(k1_pre_topc(sK0,sK1))
    | ~ v1_pre_topc(k1_pre_topc(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f75,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | k2_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k2_struct_0(X2) = X1
      | k1_pre_topc(X0,X1) != X2
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_pre_topc(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k1_pre_topc(X0,X1) = X2
                  | k2_struct_0(X2) != X1 )
                & ( k2_struct_0(X2) = X1
                  | k1_pre_topc(X0,X1) != X2 ) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_pre_topc(X2) )
             => ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_pre_topc)).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,k2_struct_0(X1))
      | sK3(X1,X2) = X2
      | v2_compts_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v2_compts_1(X2,X0)
                  | ( ~ v2_compts_1(sK3(X1,X2),X1)
                    & sK3(X1,X2) = X2
                    & m1_subset_1(sK3(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v2_compts_1(X4,X1)
                      | X2 != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v2_compts_1(X2,X0) ) )
              | ~ r1_tarski(X2,k2_struct_0(X1))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f32,f33])).

fof(f33,plain,(
    ! [X2,X1] :
      ( ? [X3] :
          ( ~ v2_compts_1(X3,X1)
          & X2 = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v2_compts_1(sK3(X1,X2),X1)
        & sK3(X1,X2) = X2
        & m1_subset_1(sK3(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v2_compts_1(X2,X0)
                  | ? [X3] :
                      ( ~ v2_compts_1(X3,X1)
                      & X2 = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v2_compts_1(X4,X1)
                      | X2 != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v2_compts_1(X2,X0) ) )
              | ~ r1_tarski(X2,k2_struct_0(X1))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v2_compts_1(X2,X0)
                  | ? [X3] :
                      ( ~ v2_compts_1(X3,X1)
                      & X2 = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X3] :
                      ( v2_compts_1(X3,X1)
                      | X2 != X3
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v2_compts_1(X2,X0) ) )
              | ~ r1_tarski(X2,k2_struct_0(X1))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_compts_1(X2,X0)
              <=> ! [X3] :
                    ( v2_compts_1(X3,X1)
                    | X2 != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ r1_tarski(X2,k2_struct_0(X1))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_compts_1(X2,X0)
              <=> ! [X3] :
                    ( v2_compts_1(X3,X1)
                    | X2 != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ r1_tarski(X2,k2_struct_0(X1))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X2,k2_struct_0(X1))
               => ( v2_compts_1(X2,X0)
                <=> ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                     => ( X2 = X3
                       => v2_compts_1(X3,X1) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_compts_1)).

fof(f180,plain,(
    m1_subset_1(sK3(k1_pre_topc(sK0,sK1),sK2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1)))) ),
    inference(subsumption_resolution,[],[f179,f38])).

fof(f179,plain,
    ( m1_subset_1(sK3(k1_pre_topc(sK0,sK1),sK2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f178,f75])).

fof(f178,plain,
    ( m1_subset_1(sK3(k1_pre_topc(sK0,sK1),sK2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))
    | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f177,f42])).

fof(f177,plain,
    ( m1_subset_1(sK3(k1_pre_topc(sK0,sK1),sK2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))
    | ~ r1_tarski(sK2,sK1)
    | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f176,f44])).

fof(f176,plain,
    ( m1_subset_1(sK3(k1_pre_topc(sK0,sK1),sK2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))
    | v2_compts_1(sK2,sK0)
    | ~ r1_tarski(sK2,sK1)
    | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f145,f40])).

fof(f145,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | m1_subset_1(sK3(k1_pre_topc(sK0,sK1),X0),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))
      | v2_compts_1(X0,X1)
      | ~ r1_tarski(X0,sK1)
      | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),X1)
      | ~ l1_pre_topc(X1) ) ),
    inference(superposition,[],[f48,f137])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,k2_struct_0(X1))
      | m1_subset_1(sK3(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | v2_compts_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f189,plain,
    ( ! [X0] :
        ( v2_compts_1(sK2,X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) )
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f188])).

fof(f188,plain,
    ( spl4_11
  <=> ! [X0] :
        ( v2_compts_1(sK2,X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f291,plain,
    ( spl4_3
    | ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f290])).

fof(f290,plain,
    ( $false
    | spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f289,f38])).

fof(f289,plain,
    ( ~ l1_pre_topc(sK0)
    | spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f288,f254])).

fof(f254,plain,
    ( ~ v1_compts_1(k1_pre_topc(sK0,k1_xboole_0))
    | spl4_3
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f101,f106])).

fof(f106,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl4_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f101,plain,
    ( ~ v1_compts_1(k1_pre_topc(sK0,sK1))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl4_3
  <=> v1_compts_1(k1_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f288,plain,
    ( v1_compts_1(k1_pre_topc(sK0,k1_xboole_0))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f274,f258])).

fof(f258,plain,
    ( v2_compts_1(k1_xboole_0,sK0)
    | ~ spl4_4 ),
    inference(superposition,[],[f41,f106])).

fof(f41,plain,(
    v2_compts_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f274,plain,
    ( ~ v2_compts_1(k1_xboole_0,sK0)
    | v1_compts_1(k1_pre_topc(sK0,k1_xboole_0))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_4 ),
    inference(resolution,[],[f257,f63])).

fof(f63,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_compts_1(k1_xboole_0,X0)
      | v1_compts_1(k1_pre_topc(X0,k1_xboole_0))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v1_compts_1(k1_pre_topc(X0,X1))
      | ~ v2_compts_1(X1,X0)
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( ( ( v2_compts_1(X1,X0)
                  | ~ v1_compts_1(k1_pre_topc(X0,X1)) )
                & ( v1_compts_1(k1_pre_topc(X0,X1))
                  | ~ v2_compts_1(X1,X0) ) )
              | k1_xboole_0 = X1
              | ~ v2_pre_topc(X0) )
            & ( ( ( v2_compts_1(X1,X0)
                  | ~ v1_compts_1(k1_pre_topc(X0,X1)) )
                & ( v1_compts_1(k1_pre_topc(X0,X1))
                  | ~ v2_compts_1(X1,X0) ) )
              | k1_xboole_0 != X1 ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( ( v2_compts_1(X1,X0)
              <=> v1_compts_1(k1_pre_topc(X0,X1)) )
              | k1_xboole_0 = X1
              | ~ v2_pre_topc(X0) )
            & ( ( v2_compts_1(X1,X0)
              <=> v1_compts_1(k1_pre_topc(X0,X1)) )
              | k1_xboole_0 != X1 ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( ( v2_compts_1(X1,X0)
              <=> v1_compts_1(k1_pre_topc(X0,X1)) )
              | k1_xboole_0 = X1
              | ~ v2_pre_topc(X0) )
            & ( ( v2_compts_1(X1,X0)
              <=> v1_compts_1(k1_pre_topc(X0,X1)) )
              | k1_xboole_0 != X1 ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v2_pre_topc(X0)
             => ( ( v2_compts_1(X1,X0)
                <=> v1_compts_1(k1_pre_topc(X0,X1)) )
                | k1_xboole_0 = X1 ) )
            & ( k1_xboole_0 = X1
             => ( v2_compts_1(X1,X0)
              <=> v1_compts_1(k1_pre_topc(X0,X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_compts_1)).

fof(f257,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_4 ),
    inference(superposition,[],[f39,f106])).

fof(f242,plain,
    ( ~ spl4_3
    | spl4_12 ),
    inference(avatar_contradiction_clause,[],[f241])).

fof(f241,plain,
    ( $false
    | ~ spl4_3
    | spl4_12 ),
    inference(subsumption_resolution,[],[f240,f38])).

fof(f240,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl4_3
    | spl4_12 ),
    inference(subsumption_resolution,[],[f239,f43])).

fof(f43,plain,(
    v4_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f239,plain,
    ( ~ v4_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl4_3
    | spl4_12 ),
    inference(resolution,[],[f227,f75])).

fof(f227,plain,
    ( ! [X2] :
        ( ~ m1_pre_topc(k1_pre_topc(sK0,sK1),X2)
        | ~ v4_pre_topc(sK2,X2)
        | ~ l1_pre_topc(X2) )
    | ~ spl4_3
    | spl4_12 ),
    inference(subsumption_resolution,[],[f202,f221])).

fof(f221,plain,
    ( ~ v4_pre_topc(sK2,k1_pre_topc(sK0,sK1))
    | ~ spl4_3
    | spl4_12 ),
    inference(subsumption_resolution,[],[f220,f138])).

fof(f138,plain,(
    l1_pre_topc(k1_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f134,f38])).

fof(f134,plain,
    ( l1_pre_topc(k1_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f75,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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

fof(f220,plain,
    ( ~ v4_pre_topc(sK2,k1_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(k1_pre_topc(sK0,sK1))
    | ~ spl4_3
    | spl4_12 ),
    inference(subsumption_resolution,[],[f219,f193])).

fof(f193,plain,
    ( ~ v2_compts_1(sK2,k1_pre_topc(sK0,sK1))
    | spl4_12 ),
    inference(avatar_component_clause,[],[f191])).

fof(f191,plain,
    ( spl4_12
  <=> v2_compts_1(sK2,k1_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f219,plain,
    ( ~ v4_pre_topc(sK2,k1_pre_topc(sK0,sK1))
    | v2_compts_1(sK2,k1_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(k1_pre_topc(sK0,sK1))
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f198,f102])).

fof(f102,plain,
    ( v1_compts_1(k1_pre_topc(sK0,sK1))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f100])).

fof(f198,plain,
    ( ~ v4_pre_topc(sK2,k1_pre_topc(sK0,sK1))
    | ~ v1_compts_1(k1_pre_topc(sK0,sK1))
    | v2_compts_1(sK2,k1_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(k1_pre_topc(sK0,sK1)) ),
    inference(resolution,[],[f181,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ v1_compts_1(X0)
      | v2_compts_1(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_compts_1(X1,X0)
          | ~ v4_pre_topc(X1,X0)
          | ~ v1_compts_1(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_compts_1(X1,X0)
          | ~ v4_pre_topc(X1,X0)
          | ~ v1_compts_1(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v4_pre_topc(X1,X0)
              & v1_compts_1(X0) )
           => v2_compts_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_compts_1)).

fof(f202,plain,(
    ! [X2] :
      ( v4_pre_topc(sK2,k1_pre_topc(sK0,sK1))
      | ~ v4_pre_topc(sK2,X2)
      | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),X2)
      | ~ l1_pre_topc(X2) ) ),
    inference(resolution,[],[f181,f68])).

fof(f68,plain,(
    ! [X2,X0,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | v4_pre_topc(X3,X2)
      | ~ v4_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f64,f46])).

fof(f64,plain,(
    ! [X2,X0,X3] :
      ( v4_pre_topc(X3,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v4_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( v4_pre_topc(X3,X2)
      | X1 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v4_pre_topc(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v4_pre_topc(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( v4_pre_topc(X1,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( X1 = X3
                     => v4_pre_topc(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_tops_2)).

fof(f194,plain,
    ( spl4_11
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f186,f191,f188])).

fof(f186,plain,(
    ! [X0] :
      ( ~ v2_compts_1(sK2,k1_pre_topc(sK0,sK1))
      | v2_compts_1(sK2,X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f185,f42])).

fof(f185,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK2,sK1)
      | ~ v2_compts_1(sK2,k1_pre_topc(sK0,sK1))
      | v2_compts_1(sK2,X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(forward_demodulation,[],[f184,f137])).

fof(f184,plain,(
    ! [X0] :
      ( ~ v2_compts_1(sK2,k1_pre_topc(sK0,sK1))
      | v2_compts_1(sK2,X0)
      | ~ r1_tarski(sK2,k2_struct_0(k1_pre_topc(sK0,sK1)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f50,f160])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_compts_1(sK3(X1,X2),X1)
      | v2_compts_1(X2,X0)
      | ~ r1_tarski(X2,k2_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f107,plain,
    ( spl4_3
    | spl4_4 ),
    inference(avatar_split_clause,[],[f98,f104,f100])).

fof(f98,plain,
    ( k1_xboole_0 = sK1
    | v1_compts_1(k1_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f97,f38])).

fof(f97,plain,
    ( k1_xboole_0 = sK1
    | v1_compts_1(k1_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f96,f37])).

fof(f37,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f96,plain,
    ( k1_xboole_0 = sK1
    | ~ v2_pre_topc(sK0)
    | v1_compts_1(k1_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f94,f41])).

fof(f94,plain,
    ( ~ v2_compts_1(sK1,sK0)
    | k1_xboole_0 = sK1
    | ~ v2_pre_topc(sK0)
    | v1_compts_1(k1_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f53,f39])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_compts_1(X1,X0)
      | k1_xboole_0 = X1
      | ~ v2_pre_topc(X0)
      | v1_compts_1(k1_pre_topc(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:16:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.45  % (31673)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.46  % (31683)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.47  % (31673)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f371,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f107,f194,f242,f291,f370])).
% 0.21/0.47  fof(f370,plain,(
% 0.21/0.47    ~spl4_11),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f369])).
% 0.21/0.47  fof(f369,plain,(
% 0.21/0.47    $false | ~spl4_11),
% 0.21/0.47    inference(subsumption_resolution,[],[f368,f44])).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    ~v2_compts_1(sK2,sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f30])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    ((~v2_compts_1(sK2,sK0) & v4_pre_topc(sK2,sK0) & r1_tarski(sK2,sK1) & v2_compts_1(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f29,f28,f27])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : (~v2_compts_1(X2,X0) & v4_pre_topc(X2,X0) & r1_tarski(X2,X1) & v2_compts_1(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (~v2_compts_1(X2,sK0) & v4_pre_topc(X2,sK0) & r1_tarski(X2,X1) & v2_compts_1(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ? [X1] : (? [X2] : (~v2_compts_1(X2,sK0) & v4_pre_topc(X2,sK0) & r1_tarski(X2,X1) & v2_compts_1(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (~v2_compts_1(X2,sK0) & v4_pre_topc(X2,sK0) & r1_tarski(X2,sK1) & v2_compts_1(sK1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ? [X2] : (~v2_compts_1(X2,sK0) & v4_pre_topc(X2,sK0) & r1_tarski(X2,sK1) & v2_compts_1(sK1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (~v2_compts_1(sK2,sK0) & v4_pre_topc(sK2,sK0) & r1_tarski(sK2,sK1) & v2_compts_1(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : (~v2_compts_1(X2,X0) & v4_pre_topc(X2,X0) & r1_tarski(X2,X1) & v2_compts_1(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.47    inference(flattening,[],[f11])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : ((~v2_compts_1(X2,X0) & (v4_pre_topc(X2,X0) & r1_tarski(X2,X1) & v2_compts_1(X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,negated_conjecture,(
% 0.21/0.47    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X2,X0) & r1_tarski(X2,X1) & v2_compts_1(X1,X0)) => v2_compts_1(X2,X0)))))),
% 0.21/0.47    inference(negated_conjecture,[],[f9])).
% 0.21/0.47  fof(f9,conjecture,(
% 0.21/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X2,X0) & r1_tarski(X2,X1) & v2_compts_1(X1,X0)) => v2_compts_1(X2,X0)))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_compts_1)).
% 0.21/0.47  fof(f368,plain,(
% 0.21/0.47    v2_compts_1(sK2,sK0) | ~spl4_11),
% 0.21/0.47    inference(subsumption_resolution,[],[f367,f38])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    l1_pre_topc(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f30])).
% 0.21/0.47  fof(f367,plain,(
% 0.21/0.47    ~l1_pre_topc(sK0) | v2_compts_1(sK2,sK0) | ~spl4_11),
% 0.21/0.47    inference(resolution,[],[f312,f75])).
% 0.21/0.47  fof(f75,plain,(
% 0.21/0.47    m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f73,f38])).
% 0.21/0.47  fof(f73,plain,(
% 0.21/0.47    m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) | ~l1_pre_topc(sK0)),
% 0.21/0.47    inference(resolution,[],[f60,f39])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.47    inference(cnf_transformation,[],[f30])).
% 0.21/0.47  fof(f60,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f26])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(flattening,[],[f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => (m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_pre_topc)).
% 0.21/0.47  fof(f312,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_pre_topc(k1_pre_topc(sK0,sK1),X0) | ~l1_pre_topc(X0) | v2_compts_1(sK2,X0)) ) | ~spl4_11),
% 0.21/0.47    inference(subsumption_resolution,[],[f189,f195])).
% 0.21/0.47  fof(f195,plain,(
% 0.21/0.47    ( ! [X0] : (m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(k1_pre_topc(sK0,sK1),X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.47    inference(resolution,[],[f181,f46])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).
% 0.21/0.48  fof(f181,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))),
% 0.21/0.48    inference(forward_demodulation,[],[f180,f160])).
% 0.21/0.48  fof(f160,plain,(
% 0.21/0.48    sK2 = sK3(k1_pre_topc(sK0,sK1),sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f159,f38])).
% 0.21/0.48  fof(f159,plain,(
% 0.21/0.48    sK2 = sK3(k1_pre_topc(sK0,sK1),sK2) | ~l1_pre_topc(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f158,f75])).
% 0.21/0.48  fof(f158,plain,(
% 0.21/0.48    sK2 = sK3(k1_pre_topc(sK0,sK1),sK2) | ~m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) | ~l1_pre_topc(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f157,f42])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    r1_tarski(sK2,sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f30])).
% 0.21/0.48  fof(f157,plain,(
% 0.21/0.48    sK2 = sK3(k1_pre_topc(sK0,sK1),sK2) | ~r1_tarski(sK2,sK1) | ~m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) | ~l1_pre_topc(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f156,f44])).
% 0.21/0.48  fof(f156,plain,(
% 0.21/0.48    sK2 = sK3(k1_pre_topc(sK0,sK1),sK2) | v2_compts_1(sK2,sK0) | ~r1_tarski(sK2,sK1) | ~m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) | ~l1_pre_topc(sK0)),
% 0.21/0.48    inference(resolution,[],[f146,f40])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    inference(cnf_transformation,[],[f30])).
% 0.21/0.48  fof(f146,plain,(
% 0.21/0.48    ( ! [X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3))) | sK3(k1_pre_topc(sK0,sK1),X2) = X2 | v2_compts_1(X2,X3) | ~r1_tarski(X2,sK1) | ~m1_pre_topc(k1_pre_topc(sK0,sK1),X3) | ~l1_pre_topc(X3)) )),
% 0.21/0.48    inference(superposition,[],[f49,f137])).
% 0.21/0.48  fof(f137,plain,(
% 0.21/0.48    sK1 = k2_struct_0(k1_pre_topc(sK0,sK1))),
% 0.21/0.48    inference(subsumption_resolution,[],[f136,f38])).
% 0.21/0.48  fof(f136,plain,(
% 0.21/0.48    sK1 = k2_struct_0(k1_pre_topc(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f135,f39])).
% 0.21/0.48  fof(f135,plain,(
% 0.21/0.48    sK1 = k2_struct_0(k1_pre_topc(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f133,f71])).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    v1_pre_topc(k1_pre_topc(sK0,sK1))),
% 0.21/0.48    inference(subsumption_resolution,[],[f69,f38])).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    v1_pre_topc(k1_pre_topc(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 0.21/0.48    inference(resolution,[],[f59,f39])).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_pre_topc(k1_pre_topc(X0,X1)) | ~l1_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f26])).
% 0.21/0.48  fof(f133,plain,(
% 0.21/0.48    sK1 = k2_struct_0(k1_pre_topc(sK0,sK1)) | ~v1_pre_topc(k1_pre_topc(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 0.21/0.48    inference(resolution,[],[f75,f66])).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_pre_topc(k1_pre_topc(X0,X1),X0) | k2_struct_0(k1_pre_topc(X0,X1)) = X1 | ~v1_pre_topc(k1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.48    inference(equality_resolution,[],[f57])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k2_struct_0(X2) = X1 | k1_pre_topc(X0,X1) != X2 | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (((k1_pre_topc(X0,X1) = X2 | k2_struct_0(X2) != X1) & (k2_struct_0(X2) = X1 | k1_pre_topc(X0,X1) != X2)) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(nnf_transformation,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : ((k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(flattening,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : ((k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1) | (~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_pre_topc(X2)) => (k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_pre_topc)).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r1_tarski(X2,k2_struct_0(X1)) | sK3(X1,X2) = X2 | v2_compts_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (((v2_compts_1(X2,X0) | (~v2_compts_1(sK3(X1,X2),X1) & sK3(X1,X2) = X2 & m1_subset_1(sK3(X1,X2),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v2_compts_1(X4,X1) | X2 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_compts_1(X2,X0))) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f32,f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ! [X2,X1] : (? [X3] : (~v2_compts_1(X3,X1) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) => (~v2_compts_1(sK3(X1,X2),X1) & sK3(X1,X2) = X2 & m1_subset_1(sK3(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (((v2_compts_1(X2,X0) | ? [X3] : (~v2_compts_1(X3,X1) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v2_compts_1(X4,X1) | X2 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_compts_1(X2,X0))) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(rectify,[],[f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (((v2_compts_1(X2,X0) | ? [X3] : (~v2_compts_1(X3,X1) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (v2_compts_1(X3,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_compts_1(X2,X0))) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(nnf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : ((v2_compts_1(X2,X0) <=> ! [X3] : (v2_compts_1(X3,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(flattening,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (((v2_compts_1(X2,X0) <=> ! [X3] : ((v2_compts_1(X3,X1) | X2 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~r1_tarski(X2,k2_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X2,k2_struct_0(X1)) => (v2_compts_1(X2,X0) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (X2 = X3 => v2_compts_1(X3,X1))))))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_compts_1)).
% 0.21/0.48  fof(f180,plain,(
% 0.21/0.48    m1_subset_1(sK3(k1_pre_topc(sK0,sK1),sK2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))),
% 0.21/0.48    inference(subsumption_resolution,[],[f179,f38])).
% 0.21/0.48  fof(f179,plain,(
% 0.21/0.48    m1_subset_1(sK3(k1_pre_topc(sK0,sK1),sK2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1)))) | ~l1_pre_topc(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f178,f75])).
% 0.21/0.48  fof(f178,plain,(
% 0.21/0.48    m1_subset_1(sK3(k1_pre_topc(sK0,sK1),sK2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1)))) | ~m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) | ~l1_pre_topc(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f177,f42])).
% 0.21/0.48  fof(f177,plain,(
% 0.21/0.48    m1_subset_1(sK3(k1_pre_topc(sK0,sK1),sK2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1)))) | ~r1_tarski(sK2,sK1) | ~m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) | ~l1_pre_topc(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f176,f44])).
% 0.21/0.48  fof(f176,plain,(
% 0.21/0.48    m1_subset_1(sK3(k1_pre_topc(sK0,sK1),sK2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1)))) | v2_compts_1(sK2,sK0) | ~r1_tarski(sK2,sK1) | ~m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) | ~l1_pre_topc(sK0)),
% 0.21/0.48    inference(resolution,[],[f145,f40])).
% 0.21/0.48  fof(f145,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | m1_subset_1(sK3(k1_pre_topc(sK0,sK1),X0),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1)))) | v2_compts_1(X0,X1) | ~r1_tarski(X0,sK1) | ~m1_pre_topc(k1_pre_topc(sK0,sK1),X1) | ~l1_pre_topc(X1)) )),
% 0.21/0.48    inference(superposition,[],[f48,f137])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r1_tarski(X2,k2_struct_0(X1)) | m1_subset_1(sK3(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) | v2_compts_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f34])).
% 0.21/0.48  fof(f189,plain,(
% 0.21/0.48    ( ! [X0] : (v2_compts_1(sK2,X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(k1_pre_topc(sK0,sK1),X0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))) ) | ~spl4_11),
% 0.21/0.48    inference(avatar_component_clause,[],[f188])).
% 0.21/0.48  fof(f188,plain,(
% 0.21/0.48    spl4_11 <=> ! [X0] : (v2_compts_1(sK2,X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(k1_pre_topc(sK0,sK1),X0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.48  fof(f291,plain,(
% 0.21/0.48    spl4_3 | ~spl4_4),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f290])).
% 0.21/0.48  fof(f290,plain,(
% 0.21/0.48    $false | (spl4_3 | ~spl4_4)),
% 0.21/0.48    inference(subsumption_resolution,[],[f289,f38])).
% 0.21/0.48  fof(f289,plain,(
% 0.21/0.48    ~l1_pre_topc(sK0) | (spl4_3 | ~spl4_4)),
% 0.21/0.48    inference(subsumption_resolution,[],[f288,f254])).
% 0.21/0.48  fof(f254,plain,(
% 0.21/0.48    ~v1_compts_1(k1_pre_topc(sK0,k1_xboole_0)) | (spl4_3 | ~spl4_4)),
% 0.21/0.48    inference(forward_demodulation,[],[f101,f106])).
% 0.21/0.48  fof(f106,plain,(
% 0.21/0.48    k1_xboole_0 = sK1 | ~spl4_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f104])).
% 0.21/0.48  fof(f104,plain,(
% 0.21/0.48    spl4_4 <=> k1_xboole_0 = sK1),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.48  fof(f101,plain,(
% 0.21/0.48    ~v1_compts_1(k1_pre_topc(sK0,sK1)) | spl4_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f100])).
% 0.21/0.48  fof(f100,plain,(
% 0.21/0.48    spl4_3 <=> v1_compts_1(k1_pre_topc(sK0,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.48  fof(f288,plain,(
% 0.21/0.48    v1_compts_1(k1_pre_topc(sK0,k1_xboole_0)) | ~l1_pre_topc(sK0) | ~spl4_4),
% 0.21/0.48    inference(subsumption_resolution,[],[f274,f258])).
% 0.21/0.48  fof(f258,plain,(
% 0.21/0.48    v2_compts_1(k1_xboole_0,sK0) | ~spl4_4),
% 0.21/0.48    inference(superposition,[],[f41,f106])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    v2_compts_1(sK1,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f30])).
% 0.21/0.48  fof(f274,plain,(
% 0.21/0.48    ~v2_compts_1(k1_xboole_0,sK0) | v1_compts_1(k1_pre_topc(sK0,k1_xboole_0)) | ~l1_pre_topc(sK0) | ~spl4_4),
% 0.21/0.48    inference(resolution,[],[f257,f63])).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_compts_1(k1_xboole_0,X0) | v1_compts_1(k1_pre_topc(X0,k1_xboole_0)) | ~l1_pre_topc(X0)) )),
% 0.21/0.48    inference(equality_resolution,[],[f51])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v1_compts_1(k1_pre_topc(X0,X1)) | ~v2_compts_1(X1,X0) | k1_xboole_0 != X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f35])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (((((v2_compts_1(X1,X0) | ~v1_compts_1(k1_pre_topc(X0,X1))) & (v1_compts_1(k1_pre_topc(X0,X1)) | ~v2_compts_1(X1,X0))) | k1_xboole_0 = X1 | ~v2_pre_topc(X0)) & (((v2_compts_1(X1,X0) | ~v1_compts_1(k1_pre_topc(X0,X1))) & (v1_compts_1(k1_pre_topc(X0,X1)) | ~v2_compts_1(X1,X0))) | k1_xboole_0 != X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(nnf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((((v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1))) | k1_xboole_0 = X1 | ~v2_pre_topc(X0)) & ((v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1))) | k1_xboole_0 != X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(flattening,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (((((v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1))) | k1_xboole_0 = X1) | ~v2_pre_topc(X0)) & ((v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1))) | k1_xboole_0 != X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_pre_topc(X0) => ((v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1))) | k1_xboole_0 = X1)) & (k1_xboole_0 = X1 => (v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1)))))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_compts_1)).
% 0.21/0.48  fof(f257,plain,(
% 0.21/0.48    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_4),
% 0.21/0.48    inference(superposition,[],[f39,f106])).
% 0.21/0.48  fof(f242,plain,(
% 0.21/0.48    ~spl4_3 | spl4_12),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f241])).
% 0.21/0.48  fof(f241,plain,(
% 0.21/0.48    $false | (~spl4_3 | spl4_12)),
% 0.21/0.48    inference(subsumption_resolution,[],[f240,f38])).
% 0.21/0.48  fof(f240,plain,(
% 0.21/0.48    ~l1_pre_topc(sK0) | (~spl4_3 | spl4_12)),
% 0.21/0.48    inference(subsumption_resolution,[],[f239,f43])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    v4_pre_topc(sK2,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f30])).
% 0.21/0.48  fof(f239,plain,(
% 0.21/0.48    ~v4_pre_topc(sK2,sK0) | ~l1_pre_topc(sK0) | (~spl4_3 | spl4_12)),
% 0.21/0.48    inference(resolution,[],[f227,f75])).
% 0.21/0.48  fof(f227,plain,(
% 0.21/0.48    ( ! [X2] : (~m1_pre_topc(k1_pre_topc(sK0,sK1),X2) | ~v4_pre_topc(sK2,X2) | ~l1_pre_topc(X2)) ) | (~spl4_3 | spl4_12)),
% 0.21/0.48    inference(subsumption_resolution,[],[f202,f221])).
% 0.21/0.48  fof(f221,plain,(
% 0.21/0.48    ~v4_pre_topc(sK2,k1_pre_topc(sK0,sK1)) | (~spl4_3 | spl4_12)),
% 0.21/0.48    inference(subsumption_resolution,[],[f220,f138])).
% 0.21/0.48  fof(f138,plain,(
% 0.21/0.48    l1_pre_topc(k1_pre_topc(sK0,sK1))),
% 0.21/0.48    inference(subsumption_resolution,[],[f134,f38])).
% 0.21/0.48  fof(f134,plain,(
% 0.21/0.48    l1_pre_topc(k1_pre_topc(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 0.21/0.48    inference(resolution,[],[f75,f45])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.48  fof(f220,plain,(
% 0.21/0.48    ~v4_pre_topc(sK2,k1_pre_topc(sK0,sK1)) | ~l1_pre_topc(k1_pre_topc(sK0,sK1)) | (~spl4_3 | spl4_12)),
% 0.21/0.48    inference(subsumption_resolution,[],[f219,f193])).
% 0.21/0.48  fof(f193,plain,(
% 0.21/0.48    ~v2_compts_1(sK2,k1_pre_topc(sK0,sK1)) | spl4_12),
% 0.21/0.48    inference(avatar_component_clause,[],[f191])).
% 0.21/0.48  fof(f191,plain,(
% 0.21/0.48    spl4_12 <=> v2_compts_1(sK2,k1_pre_topc(sK0,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.21/0.48  fof(f219,plain,(
% 0.21/0.48    ~v4_pre_topc(sK2,k1_pre_topc(sK0,sK1)) | v2_compts_1(sK2,k1_pre_topc(sK0,sK1)) | ~l1_pre_topc(k1_pre_topc(sK0,sK1)) | ~spl4_3),
% 0.21/0.48    inference(subsumption_resolution,[],[f198,f102])).
% 0.21/0.48  fof(f102,plain,(
% 0.21/0.48    v1_compts_1(k1_pre_topc(sK0,sK1)) | ~spl4_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f100])).
% 0.21/0.48  fof(f198,plain,(
% 0.21/0.48    ~v4_pre_topc(sK2,k1_pre_topc(sK0,sK1)) | ~v1_compts_1(k1_pre_topc(sK0,sK1)) | v2_compts_1(sK2,k1_pre_topc(sK0,sK1)) | ~l1_pre_topc(k1_pre_topc(sK0,sK1))),
% 0.21/0.48    inference(resolution,[],[f181,f55])).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | ~v1_compts_1(X0) | v2_compts_1(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (v2_compts_1(X1,X0) | ~v4_pre_topc(X1,X0) | ~v1_compts_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(flattening,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((v2_compts_1(X1,X0) | (~v4_pre_topc(X1,X0) | ~v1_compts_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X1,X0) & v1_compts_1(X0)) => v2_compts_1(X1,X0))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_compts_1)).
% 0.21/0.48  fof(f202,plain,(
% 0.21/0.48    ( ! [X2] : (v4_pre_topc(sK2,k1_pre_topc(sK0,sK1)) | ~v4_pre_topc(sK2,X2) | ~m1_pre_topc(k1_pre_topc(sK0,sK1),X2) | ~l1_pre_topc(X2)) )),
% 0.21/0.48    inference(resolution,[],[f181,f68])).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    ( ! [X2,X0,X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | v4_pre_topc(X3,X2) | ~v4_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f64,f46])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    ( ! [X2,X0,X3] : (v4_pre_topc(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~v4_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.48    inference(equality_resolution,[],[f56])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (v4_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~v4_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (v4_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v4_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(flattening,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((v4_pre_topc(X3,X2) | X1 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v4_pre_topc(X1,X0)) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v4_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v4_pre_topc(X3,X2)))))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_tops_2)).
% 0.21/0.48  fof(f194,plain,(
% 0.21/0.48    spl4_11 | ~spl4_12),
% 0.21/0.48    inference(avatar_split_clause,[],[f186,f191,f188])).
% 0.21/0.48  fof(f186,plain,(
% 0.21/0.48    ( ! [X0] : (~v2_compts_1(sK2,k1_pre_topc(sK0,sK1)) | v2_compts_1(sK2,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(k1_pre_topc(sK0,sK1),X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f185,f42])).
% 0.21/0.48  fof(f185,plain,(
% 0.21/0.48    ( ! [X0] : (~r1_tarski(sK2,sK1) | ~v2_compts_1(sK2,k1_pre_topc(sK0,sK1)) | v2_compts_1(sK2,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(k1_pre_topc(sK0,sK1),X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.48    inference(forward_demodulation,[],[f184,f137])).
% 0.21/0.48  fof(f184,plain,(
% 0.21/0.48    ( ! [X0] : (~v2_compts_1(sK2,k1_pre_topc(sK0,sK1)) | v2_compts_1(sK2,X0) | ~r1_tarski(sK2,k2_struct_0(k1_pre_topc(sK0,sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(k1_pre_topc(sK0,sK1),X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.48    inference(superposition,[],[f50,f160])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~v2_compts_1(sK3(X1,X2),X1) | v2_compts_1(X2,X0) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f34])).
% 0.21/0.48  fof(f107,plain,(
% 0.21/0.48    spl4_3 | spl4_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f98,f104,f100])).
% 0.21/0.48  fof(f98,plain,(
% 0.21/0.48    k1_xboole_0 = sK1 | v1_compts_1(k1_pre_topc(sK0,sK1))),
% 0.21/0.48    inference(subsumption_resolution,[],[f97,f38])).
% 0.21/0.48  fof(f97,plain,(
% 0.21/0.48    k1_xboole_0 = sK1 | v1_compts_1(k1_pre_topc(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f96,f37])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    v2_pre_topc(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f30])).
% 0.21/0.48  fof(f96,plain,(
% 0.21/0.48    k1_xboole_0 = sK1 | ~v2_pre_topc(sK0) | v1_compts_1(k1_pre_topc(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f94,f41])).
% 0.21/0.48  fof(f94,plain,(
% 0.21/0.48    ~v2_compts_1(sK1,sK0) | k1_xboole_0 = sK1 | ~v2_pre_topc(sK0) | v1_compts_1(k1_pre_topc(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 0.21/0.48    inference(resolution,[],[f53,f39])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_compts_1(X1,X0) | k1_xboole_0 = X1 | ~v2_pre_topc(X0) | v1_compts_1(k1_pre_topc(X0,X1)) | ~l1_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f35])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (31673)------------------------------
% 0.21/0.48  % (31673)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (31673)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (31673)Memory used [KB]: 10746
% 0.21/0.48  % (31673)Time elapsed: 0.060 s
% 0.21/0.48  % (31673)------------------------------
% 0.21/0.48  % (31673)------------------------------
% 0.21/0.49  % (31661)Success in time 0.132 s
%------------------------------------------------------------------------------
