%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:06 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  169 (8199 expanded)
%              Number of leaves         :   14 (3421 expanded)
%              Depth                    :   93
%              Number of atoms          :  666 (71815 expanded)
%              Number of equality atoms :  130 (1626 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f388,plain,(
    $false ),
    inference(subsumption_resolution,[],[f387,f352])).

fof(f352,plain,(
    sP0(sK2,sK4) ),
    inference(subsumption_resolution,[],[f247,f351])).

fof(f351,plain,(
    v4_tops_1(sK3,sK1) ),
    inference(subsumption_resolution,[],[f350,f62])).

fof(f62,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f350,plain,
    ( ~ r1_tarski(sK3,sK3)
    | v4_tops_1(sK3,sK1) ),
    inference(backward_demodulation,[],[f239,f349])).

fof(f349,plain,(
    sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) ),
    inference(subsumption_resolution,[],[f348,f42])).

fof(f42,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ( ( ( ~ v4_tops_1(sK3,sK1)
          | ~ v3_pre_topc(sK3,sK1) )
        & v6_tops_1(sK3,sK1) )
      | sP0(sK2,sK4) )
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    & l1_pre_topc(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f25,f31,f30,f29,f28])).

fof(f28,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ( ( ~ v4_tops_1(X2,X0)
                          | ~ v3_pre_topc(X2,X0) )
                        & v6_tops_1(X2,X0) )
                      | sP0(X1,X3) )
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & l1_pre_topc(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( ~ v4_tops_1(X2,sK1)
                        | ~ v3_pre_topc(X2,sK1) )
                      & v6_tops_1(X2,sK1) )
                    | sP0(X1,X3) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ( ( ~ v4_tops_1(X2,sK1)
                      | ~ v3_pre_topc(X2,sK1) )
                    & v6_tops_1(X2,sK1) )
                  | sP0(X1,X3) )
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) )
        & l1_pre_topc(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ( ( ~ v4_tops_1(X2,sK1)
                    | ~ v3_pre_topc(X2,sK1) )
                  & v6_tops_1(X2,sK1) )
                | sP0(sK2,X3) )
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) )
      & l1_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ( ( ~ v4_tops_1(X2,sK1)
                  | ~ v3_pre_topc(X2,sK1) )
                & v6_tops_1(X2,sK1) )
              | sP0(sK2,X3) )
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) )
   => ( ? [X3] :
          ( ( ( ( ~ v4_tops_1(sK3,sK1)
                | ~ v3_pre_topc(sK3,sK1) )
              & v6_tops_1(sK3,sK1) )
            | sP0(sK2,X3) )
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X3] :
        ( ( ( ( ~ v4_tops_1(sK3,sK1)
              | ~ v3_pre_topc(sK3,sK1) )
            & v6_tops_1(sK3,sK1) )
          | sP0(sK2,X3) )
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
   => ( ( ( ( ~ v4_tops_1(sK3,sK1)
            | ~ v3_pre_topc(sK3,sK1) )
          & v6_tops_1(sK3,sK1) )
        | sP0(sK2,sK4) )
      & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( ~ v4_tops_1(X2,X0)
                        | ~ v3_pre_topc(X2,X0) )
                      & v6_tops_1(X2,X0) )
                    | sP0(X1,X3) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(definition_folding,[],[f12,f24])).

fof(f24,plain,(
    ! [X1,X3] :
      ( ( ~ v6_tops_1(X3,X1)
        & v4_tops_1(X3,X1)
        & v3_pre_topc(X3,X1) )
      | ~ sP0(X1,X3) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( ~ v4_tops_1(X2,X0)
                        | ~ v3_pre_topc(X2,X0) )
                      & v6_tops_1(X2,X0) )
                    | ( ~ v6_tops_1(X3,X1)
                      & v4_tops_1(X3,X1)
                      & v3_pre_topc(X3,X1) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( ~ v4_tops_1(X2,X0)
                        | ~ v3_pre_topc(X2,X0) )
                      & v6_tops_1(X2,X0) )
                    | ( ~ v6_tops_1(X3,X1)
                      & v4_tops_1(X3,X1)
                      & v3_pre_topc(X3,X1) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( ( v6_tops_1(X2,X0)
                       => ( v4_tops_1(X2,X0)
                          & v3_pre_topc(X2,X0) ) )
                      & ( ( v4_tops_1(X3,X1)
                          & v3_pre_topc(X3,X1) )
                       => v6_tops_1(X3,X1) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( v6_tops_1(X2,X0)
                     => ( v4_tops_1(X2,X0)
                        & v3_pre_topc(X2,X0) ) )
                    & ( ( v4_tops_1(X3,X1)
                        & v3_pre_topc(X3,X1) )
                     => v6_tops_1(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_tops_1)).

fof(f348,plain,
    ( sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3))
    | ~ l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f347,f44])).

fof(f44,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f32])).

fof(f347,plain,
    ( sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(duplicate_literal_removal,[],[f345])).

fof(f345,plain,
    ( sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3))
    | sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f344,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v6_tops_1(X1,X0)
      | k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v6_tops_1(X1,X0)
              | k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1 )
            & ( k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1
              | ~ v6_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v6_tops_1(X1,X0)
          <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v6_tops_1(X1,X0)
          <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_tops_1)).

fof(f344,plain,
    ( v6_tops_1(sK3,sK1)
    | sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) ),
    inference(resolution,[],[f343,f46])).

fof(f46,plain,
    ( sP0(sK2,sK4)
    | v6_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f343,plain,
    ( ~ sP0(sK2,sK4)
    | sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) ),
    inference(resolution,[],[f335,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v6_tops_1(X1,X0)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ~ v6_tops_1(X1,X0)
        & v4_tops_1(X1,X0)
        & v3_pre_topc(X1,X0) )
      | ~ sP0(X0,X1) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X1,X3] :
      ( ( ~ v6_tops_1(X3,X1)
        & v4_tops_1(X3,X1)
        & v3_pre_topc(X3,X1) )
      | ~ sP0(X1,X3) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f335,plain,
    ( v6_tops_1(sK4,sK2)
    | sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) ),
    inference(subsumption_resolution,[],[f334,f43])).

fof(f43,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f334,plain,
    ( v6_tops_1(sK4,sK2)
    | ~ l1_pre_topc(sK2)
    | sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) ),
    inference(subsumption_resolution,[],[f333,f45])).

fof(f45,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f32])).

fof(f333,plain,
    ( v6_tops_1(sK4,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) ),
    inference(trivial_inequality_removal,[],[f326])).

fof(f326,plain,
    ( sK4 != sK4
    | v6_tops_1(sK4,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) ),
    inference(superposition,[],[f50,f321])).

fof(f321,plain,
    ( sK4 = k1_tops_1(sK2,k2_pre_topc(sK2,sK4))
    | sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) ),
    inference(resolution,[],[f320,f84])).

fof(f84,plain,
    ( v4_tops_1(sK4,sK2)
    | sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) ),
    inference(subsumption_resolution,[],[f83,f42])).

fof(f83,plain,
    ( sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3))
    | ~ l1_pre_topc(sK1)
    | v4_tops_1(sK4,sK2) ),
    inference(subsumption_resolution,[],[f82,f44])).

fof(f82,plain,
    ( sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | v4_tops_1(sK4,sK2) ),
    inference(resolution,[],[f49,f67])).

fof(f67,plain,
    ( v6_tops_1(sK3,sK1)
    | v4_tops_1(sK4,sK2) ),
    inference(resolution,[],[f39,f46])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | v4_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f320,plain,
    ( ~ v4_tops_1(sK4,sK2)
    | sK4 = k1_tops_1(sK2,k2_pre_topc(sK2,sK4)) ),
    inference(subsumption_resolution,[],[f319,f43])).

fof(f319,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ v4_tops_1(sK4,sK2)
    | sK4 = k1_tops_1(sK2,k2_pre_topc(sK2,sK4)) ),
    inference(subsumption_resolution,[],[f318,f45])).

fof(f318,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | ~ v4_tops_1(sK4,sK2)
    | sK4 = k1_tops_1(sK2,k2_pre_topc(sK2,sK4)) ),
    inference(subsumption_resolution,[],[f317,f74])).

fof(f74,plain,(
    r1_tarski(sK4,k2_pre_topc(sK2,sK4)) ),
    inference(resolution,[],[f71,f45])).

fof(f71,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | r1_tarski(X1,k2_pre_topc(sK2,X1)) ) ),
    inference(resolution,[],[f48,f43])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(X1,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

fof(f317,plain,
    ( ~ r1_tarski(sK4,k2_pre_topc(sK2,sK4))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | ~ v4_tops_1(sK4,sK2)
    | sK4 = k1_tops_1(sK2,k2_pre_topc(sK2,sK4)) ),
    inference(duplicate_literal_removal,[],[f315])).

fof(f315,plain,
    ( ~ r1_tarski(sK4,k2_pre_topc(sK2,sK4))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | ~ v4_tops_1(sK4,sK2)
    | sK4 = k1_tops_1(sK2,k2_pre_topc(sK2,sK4)) ),
    inference(resolution,[],[f306,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tops_1(X1,k2_pre_topc(X1,X0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v4_tops_1(X0,X1)
      | k1_tops_1(X1,k2_pre_topc(X1,X0)) = X0 ) ),
    inference(resolution,[],[f51,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)
      | ~ v4_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_tops_1(X1,X0)
              | ~ r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              | ~ r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) )
            & ( ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
                & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) )
              | ~ v4_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_tops_1(X1,X0)
              | ~ r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              | ~ r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) )
            & ( ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
                & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) )
              | ~ v4_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_tops_1(X1,X0)
          <=> ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_tops_1(X1,X0)
          <=> ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tops_1)).

fof(f306,plain,(
    ! [X0] :
      ( r1_tarski(sK4,k1_tops_1(sK2,k2_pre_topc(sK2,X0)))
      | ~ r1_tarski(sK4,k2_pre_topc(sK2,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(subsumption_resolution,[],[f303,f43])).

fof(f303,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK4,k2_pre_topc(sK2,X0))
      | r1_tarski(sK4,k1_tops_1(sK2,k2_pre_topc(sK2,X0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_pre_topc(sK2) ) ),
    inference(resolution,[],[f283,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f283,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r1_tarski(sK4,X1)
      | r1_tarski(sK4,k1_tops_1(sK2,X1)) ) ),
    inference(subsumption_resolution,[],[f282,f43])).

fof(f282,plain,(
    ! [X1] :
      ( r1_tarski(sK4,k1_tops_1(sK2,X1))
      | ~ r1_tarski(sK4,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_pre_topc(sK2) ) ),
    inference(subsumption_resolution,[],[f272,f45])).

fof(f272,plain,(
    ! [X1] :
      ( r1_tarski(sK4,k1_tops_1(sK2,X1))
      | ~ r1_tarski(sK4,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_pre_topc(sK2) ) ),
    inference(superposition,[],[f54,f267])).

fof(f267,plain,(
    sK4 = k1_tops_1(sK2,sK4) ),
    inference(subsumption_resolution,[],[f266,f45])).

fof(f266,plain,
    ( sK4 = k1_tops_1(sK2,sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(duplicate_literal_removal,[],[f265])).

fof(f265,plain,
    ( sK4 = k1_tops_1(sK2,sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | sK4 = k1_tops_1(sK2,sK4) ),
    inference(resolution,[],[f261,f95])).

fof(f95,plain,(
    ! [X1] :
      ( ~ v3_pre_topc(X1,sK2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | k1_tops_1(sK2,X1) = X1 ) ),
    inference(resolution,[],[f92,f43])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X1)
      | ~ v3_pre_topc(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | k1_tops_1(X1,X0) = X0 ) ),
    inference(resolution,[],[f91,f44])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v3_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | k1_tops_1(X1,X0) = X0 ) ),
    inference(subsumption_resolution,[],[f90,f42])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_pre_topc(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(sK1)
      | k1_tops_1(X1,X0) = X0 ) ),
    inference(resolution,[],[f55,f41])).

fof(f41,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | k1_tops_1(X1,X3) = X3 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( k1_tops_1(X0,X2) = X2
                     => v3_pre_topc(X2,X0) )
                    & ( v3_pre_topc(X3,X1)
                     => k1_tops_1(X1,X3) = X3 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_1)).

fof(f261,plain,
    ( v3_pre_topc(sK4,sK2)
    | sK4 = k1_tops_1(sK2,sK4) ),
    inference(resolution,[],[f252,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f252,plain,
    ( sP0(sK2,sK4)
    | sK4 = k1_tops_1(sK2,sK4) ),
    inference(resolution,[],[f251,f247])).

fof(f251,plain,
    ( v4_tops_1(sK3,sK1)
    | sK4 = k1_tops_1(sK2,sK4) ),
    inference(subsumption_resolution,[],[f250,f62])).

fof(f250,plain,
    ( ~ r1_tarski(sK3,sK3)
    | v4_tops_1(sK3,sK1)
    | sK4 = k1_tops_1(sK2,sK4) ),
    inference(superposition,[],[f239,f106])).

fof(f106,plain,
    ( sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3))
    | sK4 = k1_tops_1(sK2,sK4) ),
    inference(subsumption_resolution,[],[f105,f42])).

fof(f105,plain,
    ( sK4 = k1_tops_1(sK2,sK4)
    | sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3))
    | ~ l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f103,f44])).

fof(f103,plain,
    ( sK4 = k1_tops_1(sK2,sK4)
    | sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f101,f49])).

fof(f101,plain,
    ( v6_tops_1(sK3,sK1)
    | sK4 = k1_tops_1(sK2,sK4) ),
    inference(subsumption_resolution,[],[f99,f45])).

fof(f99,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | sK4 = k1_tops_1(sK2,sK4)
    | v6_tops_1(sK3,sK1) ),
    inference(resolution,[],[f95,f66])).

fof(f66,plain,
    ( v3_pre_topc(sK4,sK2)
    | v6_tops_1(sK3,sK1) ),
    inference(resolution,[],[f38,f46])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1
      | v6_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f239,plain,
    ( ~ r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3)
    | v4_tops_1(sK3,sK1) ),
    inference(subsumption_resolution,[],[f238,f42])).

fof(f238,plain,
    ( v4_tops_1(sK3,sK1)
    | ~ r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3)
    | ~ l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f237,f44])).

fof(f237,plain,
    ( v4_tops_1(sK3,sK1)
    | ~ r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f229,f72])).

fof(f72,plain,(
    r1_tarski(sK3,k2_pre_topc(sK1,sK3)) ),
    inference(resolution,[],[f70,f44])).

fof(f70,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | r1_tarski(X0,k2_pre_topc(sK1,X0)) ) ),
    inference(resolution,[],[f48,f42])).

fof(f229,plain,
    ( ~ r1_tarski(sK3,k2_pre_topc(sK1,sK3))
    | v4_tops_1(sK3,sK1)
    | ~ r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(superposition,[],[f53,f227])).

fof(f227,plain,(
    sK3 = k1_tops_1(sK1,sK3) ),
    inference(subsumption_resolution,[],[f226,f42])).

fof(f226,plain,
    ( sK3 = k1_tops_1(sK1,sK3)
    | ~ l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f225,f44])).

fof(f225,plain,
    ( sK3 = k1_tops_1(sK1,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f220,f58])).

fof(f220,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | sK3 = k1_tops_1(sK1,sK3) ),
    inference(subsumption_resolution,[],[f219,f44])).

fof(f219,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | sK3 = k1_tops_1(sK1,sK3)
    | ~ m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(duplicate_literal_removal,[],[f208])).

fof(f208,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | sK3 = k1_tops_1(sK1,sK3)
    | ~ m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | sK3 = k1_tops_1(sK1,sK3) ),
    inference(superposition,[],[f98,f204])).

fof(f204,plain,
    ( sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3))
    | sK3 = k1_tops_1(sK1,sK3) ),
    inference(subsumption_resolution,[],[f203,f42])).

fof(f203,plain,
    ( sK3 = k1_tops_1(sK1,sK3)
    | sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3))
    | ~ l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f202,f44])).

fof(f202,plain,
    ( sK3 = k1_tops_1(sK1,sK3)
    | sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(duplicate_literal_removal,[],[f200])).

fof(f200,plain,
    ( sK3 = k1_tops_1(sK1,sK3)
    | sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3))
    | sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f199,f49])).

fof(f199,plain,
    ( v6_tops_1(sK3,sK1)
    | sK3 = k1_tops_1(sK1,sK3)
    | sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) ),
    inference(resolution,[],[f198,f46])).

fof(f198,plain,
    ( ~ sP0(sK2,sK4)
    | sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3))
    | sK3 = k1_tops_1(sK1,sK3) ),
    inference(resolution,[],[f190,f40])).

fof(f190,plain,
    ( v6_tops_1(sK4,sK2)
    | sK3 = k1_tops_1(sK1,sK3)
    | sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) ),
    inference(subsumption_resolution,[],[f189,f43])).

fof(f189,plain,
    ( v6_tops_1(sK4,sK2)
    | ~ l1_pre_topc(sK2)
    | sK3 = k1_tops_1(sK1,sK3)
    | sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) ),
    inference(subsumption_resolution,[],[f186,f45])).

fof(f186,plain,
    ( v6_tops_1(sK4,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | sK3 = k1_tops_1(sK1,sK3)
    | sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) ),
    inference(trivial_inequality_removal,[],[f179])).

fof(f179,plain,
    ( sK4 != sK4
    | v6_tops_1(sK4,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | sK3 = k1_tops_1(sK1,sK3)
    | sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) ),
    inference(superposition,[],[f50,f174])).

fof(f174,plain,
    ( sK4 = k1_tops_1(sK2,k2_pre_topc(sK2,sK4))
    | sK3 = k1_tops_1(sK1,sK3)
    | sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) ),
    inference(resolution,[],[f173,f84])).

fof(f173,plain,
    ( ~ v4_tops_1(sK4,sK2)
    | sK3 = k1_tops_1(sK1,sK3)
    | sK4 = k1_tops_1(sK2,k2_pre_topc(sK2,sK4)) ),
    inference(subsumption_resolution,[],[f172,f43])).

fof(f172,plain,
    ( sK3 = k1_tops_1(sK1,sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v4_tops_1(sK4,sK2)
    | sK4 = k1_tops_1(sK2,k2_pre_topc(sK2,sK4)) ),
    inference(subsumption_resolution,[],[f171,f45])).

fof(f171,plain,
    ( sK3 = k1_tops_1(sK1,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | ~ v4_tops_1(sK4,sK2)
    | sK4 = k1_tops_1(sK2,k2_pre_topc(sK2,sK4)) ),
    inference(subsumption_resolution,[],[f170,f74])).

fof(f170,plain,
    ( ~ r1_tarski(sK4,k2_pre_topc(sK2,sK4))
    | sK3 = k1_tops_1(sK1,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | ~ v4_tops_1(sK4,sK2)
    | sK4 = k1_tops_1(sK2,k2_pre_topc(sK2,sK4)) ),
    inference(duplicate_literal_removal,[],[f168])).

fof(f168,plain,
    ( ~ r1_tarski(sK4,k2_pre_topc(sK2,sK4))
    | sK3 = k1_tops_1(sK1,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | ~ v4_tops_1(sK4,sK2)
    | sK4 = k1_tops_1(sK2,k2_pre_topc(sK2,sK4)) ),
    inference(resolution,[],[f163,f85])).

fof(f163,plain,(
    ! [X0] :
      ( r1_tarski(sK4,k1_tops_1(sK2,k2_pre_topc(sK2,X0)))
      | ~ r1_tarski(sK4,k2_pre_topc(sK2,X0))
      | sK3 = k1_tops_1(sK1,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(subsumption_resolution,[],[f161,f43])).

fof(f161,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK4,k2_pre_topc(sK2,X0))
      | r1_tarski(sK4,k1_tops_1(sK2,k2_pre_topc(sK2,X0)))
      | sK3 = k1_tops_1(sK1,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_pre_topc(sK2) ) ),
    inference(resolution,[],[f149,f58])).

fof(f149,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r1_tarski(sK4,X1)
      | r1_tarski(sK4,k1_tops_1(sK2,X1))
      | sK3 = k1_tops_1(sK1,sK3) ) ),
    inference(subsumption_resolution,[],[f148,f43])).

fof(f148,plain,(
    ! [X1] :
      ( r1_tarski(sK4,k1_tops_1(sK2,X1))
      | ~ r1_tarski(sK4,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_pre_topc(sK2)
      | sK3 = k1_tops_1(sK1,sK3) ) ),
    inference(subsumption_resolution,[],[f138,f45])).

fof(f138,plain,(
    ! [X1] :
      ( r1_tarski(sK4,k1_tops_1(sK2,X1))
      | ~ r1_tarski(sK4,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_pre_topc(sK2)
      | sK3 = k1_tops_1(sK1,sK3) ) ),
    inference(superposition,[],[f54,f135])).

fof(f135,plain,
    ( sK4 = k1_tops_1(sK2,sK4)
    | sK3 = k1_tops_1(sK1,sK3) ),
    inference(subsumption_resolution,[],[f134,f44])).

fof(f134,plain,
    ( sK4 = k1_tops_1(sK2,sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | sK3 = k1_tops_1(sK1,sK3) ),
    inference(resolution,[],[f132,f94])).

fof(f94,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | k1_tops_1(sK1,X0) = X0 ) ),
    inference(resolution,[],[f92,f42])).

fof(f132,plain,
    ( v3_pre_topc(sK3,sK1)
    | sK4 = k1_tops_1(sK2,sK4) ),
    inference(subsumption_resolution,[],[f131,f42])).

fof(f131,plain,
    ( v3_pre_topc(sK3,sK1)
    | sK4 = k1_tops_1(sK2,sK4)
    | ~ l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f130,f44])).

fof(f130,plain,
    ( v3_pre_topc(sK3,sK1)
    | sK4 = k1_tops_1(sK2,sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f129,f58])).

fof(f129,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | v3_pre_topc(sK3,sK1)
    | sK4 = k1_tops_1(sK2,sK4) ),
    inference(subsumption_resolution,[],[f128,f41])).

fof(f128,plain,
    ( v3_pre_topc(sK3,sK1)
    | ~ m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK1)
    | sK4 = k1_tops_1(sK2,sK4) ),
    inference(subsumption_resolution,[],[f118,f42])).

fof(f118,plain,
    ( v3_pre_topc(sK3,sK1)
    | ~ m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | sK4 = k1_tops_1(sK2,sK4) ),
    inference(superposition,[],[f57,f106])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f98,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_tops_1(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1)))
      | k1_tops_1(sK1,X0) = k1_tops_1(sK1,k1_tops_1(sK1,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    inference(subsumption_resolution,[],[f97,f41])).

fof(f97,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_tops_1(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1)))
      | k1_tops_1(sK1,X0) = k1_tops_1(sK1,k1_tops_1(sK1,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v2_pre_topc(sK1) ) ),
    inference(subsumption_resolution,[],[f96,f42])).

fof(f96,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_tops_1(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1)))
      | k1_tops_1(sK1,X0) = k1_tops_1(sK1,k1_tops_1(sK1,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1) ) ),
    inference(resolution,[],[f94,f57])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
      | v4_tops_1(X1,X0)
      | ~ r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f247,plain,
    ( ~ v4_tops_1(sK3,sK1)
    | sP0(sK2,sK4) ),
    inference(subsumption_resolution,[],[f47,f246])).

fof(f246,plain,(
    v3_pre_topc(sK3,sK1) ),
    inference(subsumption_resolution,[],[f245,f41])).

fof(f245,plain,
    ( v3_pre_topc(sK3,sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f244,f42])).

fof(f244,plain,
    ( v3_pre_topc(sK3,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f235,f44])).

fof(f235,plain,
    ( v3_pre_topc(sK3,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(trivial_inequality_removal,[],[f232])).

fof(f232,plain,
    ( sK3 != sK3
    | v3_pre_topc(sK3,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(superposition,[],[f65,f227])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X1,X0) != X0
      | v3_pre_topc(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1) ) ),
    inference(duplicate_literal_removal,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | v3_pre_topc(X0,X1)
      | k1_tops_1(X1,X0) != X0
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1) ) ),
    inference(condensation,[],[f56])).

% (3011)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X2,X0)
      | k1_tops_1(X0,X2) != X2
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f47,plain,
    ( ~ v3_pre_topc(sK3,sK1)
    | ~ v4_tops_1(sK3,sK1)
    | sP0(sK2,sK4) ),
    inference(cnf_transformation,[],[f32])).

fof(f387,plain,(
    ~ sP0(sK2,sK4) ),
    inference(resolution,[],[f379,f40])).

fof(f379,plain,(
    v6_tops_1(sK4,sK2) ),
    inference(subsumption_resolution,[],[f378,f43])).

fof(f378,plain,
    ( v6_tops_1(sK4,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f377,f45])).

fof(f377,plain,
    ( v6_tops_1(sK4,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(trivial_inequality_removal,[],[f370])).

fof(f370,plain,
    ( sK4 != sK4
    | v6_tops_1(sK4,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(superposition,[],[f50,f355])).

fof(f355,plain,(
    sK4 = k1_tops_1(sK2,k2_pre_topc(sK2,sK4)) ),
    inference(subsumption_resolution,[],[f320,f353])).

fof(f353,plain,(
    v4_tops_1(sK4,sK2) ),
    inference(resolution,[],[f352,f39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:59:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.49  % (3016)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.19/0.50  % (3007)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.19/0.50  % (3002)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.19/0.50  % (3020)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.19/0.50  % (3007)Refutation found. Thanks to Tanya!
% 0.19/0.50  % SZS status Theorem for theBenchmark
% 0.19/0.50  % (3027)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.19/0.51  % (3018)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.19/0.51  % (3025)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.19/0.51  % (3010)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.19/0.51  % (3005)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.19/0.51  % (3017)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.19/0.51  % (3013)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.19/0.51  % (3009)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.19/0.51  % (3003)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.51  % (3026)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.19/0.51  % (3019)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.19/0.52  % (3015)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.19/0.52  % SZS output start Proof for theBenchmark
% 0.19/0.52  fof(f388,plain,(
% 0.19/0.52    $false),
% 0.19/0.52    inference(subsumption_resolution,[],[f387,f352])).
% 0.19/0.52  fof(f352,plain,(
% 0.19/0.52    sP0(sK2,sK4)),
% 0.19/0.52    inference(subsumption_resolution,[],[f247,f351])).
% 0.19/0.52  fof(f351,plain,(
% 0.19/0.52    v4_tops_1(sK3,sK1)),
% 0.19/0.52    inference(subsumption_resolution,[],[f350,f62])).
% 0.19/0.52  fof(f62,plain,(
% 0.19/0.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.19/0.52    inference(equality_resolution,[],[f60])).
% 0.19/0.52  fof(f60,plain,(
% 0.19/0.52    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.19/0.52    inference(cnf_transformation,[],[f37])).
% 0.19/0.52  fof(f37,plain,(
% 0.19/0.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.19/0.52    inference(flattening,[],[f36])).
% 0.19/0.52  fof(f36,plain,(
% 0.19/0.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.19/0.52    inference(nnf_transformation,[],[f1])).
% 0.19/0.52  fof(f1,axiom,(
% 0.19/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.19/0.52  fof(f350,plain,(
% 0.19/0.52    ~r1_tarski(sK3,sK3) | v4_tops_1(sK3,sK1)),
% 0.19/0.52    inference(backward_demodulation,[],[f239,f349])).
% 0.19/0.52  fof(f349,plain,(
% 0.19/0.52    sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3))),
% 0.19/0.52    inference(subsumption_resolution,[],[f348,f42])).
% 0.19/0.52  fof(f42,plain,(
% 0.19/0.52    l1_pre_topc(sK1)),
% 0.19/0.52    inference(cnf_transformation,[],[f32])).
% 0.19/0.52  fof(f32,plain,(
% 0.19/0.52    ((((((~v4_tops_1(sK3,sK1) | ~v3_pre_topc(sK3,sK1)) & v6_tops_1(sK3,sK1)) | sP0(sK2,sK4)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1)),
% 0.19/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f25,f31,f30,f29,f28])).
% 0.19/0.52  fof(f28,plain,(
% 0.19/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | sP0(X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,sK1) | ~v3_pre_topc(X2,sK1)) & v6_tops_1(X2,sK1)) | sP0(X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1))),
% 0.19/0.52    introduced(choice_axiom,[])).
% 0.19/0.52  fof(f29,plain,(
% 0.19/0.52    ? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,sK1) | ~v3_pre_topc(X2,sK1)) & v6_tops_1(X2,sK1)) | sP0(X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(X1)) => (? [X2] : (? [X3] : ((((~v4_tops_1(X2,sK1) | ~v3_pre_topc(X2,sK1)) & v6_tops_1(X2,sK1)) | sP0(sK2,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK2))),
% 0.19/0.52    introduced(choice_axiom,[])).
% 0.19/0.52  fof(f30,plain,(
% 0.19/0.52    ? [X2] : (? [X3] : ((((~v4_tops_1(X2,sK1) | ~v3_pre_topc(X2,sK1)) & v6_tops_1(X2,sK1)) | sP0(sK2,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))) => (? [X3] : ((((~v4_tops_1(sK3,sK1) | ~v3_pre_topc(sK3,sK1)) & v6_tops_1(sK3,sK1)) | sP0(sK2,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))))),
% 0.19/0.52    introduced(choice_axiom,[])).
% 0.19/0.52  fof(f31,plain,(
% 0.19/0.52    ? [X3] : ((((~v4_tops_1(sK3,sK1) | ~v3_pre_topc(sK3,sK1)) & v6_tops_1(sK3,sK1)) | sP0(sK2,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) => ((((~v4_tops_1(sK3,sK1) | ~v3_pre_topc(sK3,sK1)) & v6_tops_1(sK3,sK1)) | sP0(sK2,sK4)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))))),
% 0.19/0.52    introduced(choice_axiom,[])).
% 0.19/0.52  fof(f25,plain,(
% 0.19/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | sP0(X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.19/0.52    inference(definition_folding,[],[f12,f24])).
% 0.19/0.52  fof(f24,plain,(
% 0.19/0.52    ! [X1,X3] : ((~v6_tops_1(X3,X1) & v4_tops_1(X3,X1) & v3_pre_topc(X3,X1)) | ~sP0(X1,X3))),
% 0.19/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.19/0.52  fof(f12,plain,(
% 0.19/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | (~v6_tops_1(X3,X1) & v4_tops_1(X3,X1) & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.19/0.52    inference(flattening,[],[f11])).
% 0.19/0.52  fof(f11,plain,(
% 0.19/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | (~v6_tops_1(X3,X1) & (v4_tops_1(X3,X1) & v3_pre_topc(X3,X1)))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.19/0.52    inference(ennf_transformation,[],[f10])).
% 0.19/0.52  fof(f10,negated_conjecture,(
% 0.19/0.52    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v6_tops_1(X2,X0) => (v4_tops_1(X2,X0) & v3_pre_topc(X2,X0))) & ((v4_tops_1(X3,X1) & v3_pre_topc(X3,X1)) => v6_tops_1(X3,X1)))))))),
% 0.19/0.52    inference(negated_conjecture,[],[f9])).
% 0.19/0.52  fof(f9,conjecture,(
% 0.19/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v6_tops_1(X2,X0) => (v4_tops_1(X2,X0) & v3_pre_topc(X2,X0))) & ((v4_tops_1(X3,X1) & v3_pre_topc(X3,X1)) => v6_tops_1(X3,X1)))))))),
% 0.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_tops_1)).
% 0.19/0.52  fof(f348,plain,(
% 0.19/0.52    sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) | ~l1_pre_topc(sK1)),
% 0.19/0.52    inference(subsumption_resolution,[],[f347,f44])).
% 0.19/0.52  fof(f44,plain,(
% 0.19/0.52    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.19/0.52    inference(cnf_transformation,[],[f32])).
% 0.19/0.52  fof(f347,plain,(
% 0.19/0.52    sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1)),
% 0.19/0.52    inference(duplicate_literal_removal,[],[f345])).
% 0.19/0.52  fof(f345,plain,(
% 0.19/0.52    sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) | sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1)),
% 0.19/0.52    inference(resolution,[],[f344,f49])).
% 0.19/0.52  fof(f49,plain,(
% 0.19/0.52    ( ! [X0,X1] : (~v6_tops_1(X1,X0) | k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f33])).
% 0.19/0.52  fof(f33,plain,(
% 0.19/0.52    ! [X0] : (! [X1] : (((v6_tops_1(X1,X0) | k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1) & (k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 | ~v6_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.19/0.52    inference(nnf_transformation,[],[f14])).
% 0.19/0.52  fof(f14,plain,(
% 0.19/0.52    ! [X0] : (! [X1] : ((v6_tops_1(X1,X0) <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.19/0.52    inference(ennf_transformation,[],[f5])).
% 0.19/0.52  fof(f5,axiom,(
% 0.19/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v6_tops_1(X1,X0) <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1)))),
% 0.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_tops_1)).
% 0.19/0.52  fof(f344,plain,(
% 0.19/0.52    v6_tops_1(sK3,sK1) | sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3))),
% 0.19/0.52    inference(resolution,[],[f343,f46])).
% 0.19/0.52  fof(f46,plain,(
% 0.19/0.52    sP0(sK2,sK4) | v6_tops_1(sK3,sK1)),
% 0.19/0.52    inference(cnf_transformation,[],[f32])).
% 0.19/0.52  fof(f343,plain,(
% 0.19/0.52    ~sP0(sK2,sK4) | sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3))),
% 0.19/0.52    inference(resolution,[],[f335,f40])).
% 0.19/0.52  fof(f40,plain,(
% 0.19/0.52    ( ! [X0,X1] : (~v6_tops_1(X1,X0) | ~sP0(X0,X1)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f27])).
% 0.19/0.52  fof(f27,plain,(
% 0.19/0.52    ! [X0,X1] : ((~v6_tops_1(X1,X0) & v4_tops_1(X1,X0) & v3_pre_topc(X1,X0)) | ~sP0(X0,X1))),
% 0.19/0.52    inference(rectify,[],[f26])).
% 0.19/0.52  fof(f26,plain,(
% 0.19/0.52    ! [X1,X3] : ((~v6_tops_1(X3,X1) & v4_tops_1(X3,X1) & v3_pre_topc(X3,X1)) | ~sP0(X1,X3))),
% 0.19/0.52    inference(nnf_transformation,[],[f24])).
% 0.19/0.52  fof(f335,plain,(
% 0.19/0.52    v6_tops_1(sK4,sK2) | sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3))),
% 0.19/0.52    inference(subsumption_resolution,[],[f334,f43])).
% 0.19/0.52  fof(f43,plain,(
% 0.19/0.52    l1_pre_topc(sK2)),
% 0.19/0.52    inference(cnf_transformation,[],[f32])).
% 0.19/0.52  fof(f334,plain,(
% 0.19/0.52    v6_tops_1(sK4,sK2) | ~l1_pre_topc(sK2) | sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3))),
% 0.19/0.52    inference(subsumption_resolution,[],[f333,f45])).
% 0.19/0.52  fof(f45,plain,(
% 0.19/0.52    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.19/0.52    inference(cnf_transformation,[],[f32])).
% 0.19/0.52  fof(f333,plain,(
% 0.19/0.52    v6_tops_1(sK4,sK2) | ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2) | sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3))),
% 0.19/0.52    inference(trivial_inequality_removal,[],[f326])).
% 0.19/0.52  fof(f326,plain,(
% 0.19/0.52    sK4 != sK4 | v6_tops_1(sK4,sK2) | ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2) | sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3))),
% 0.19/0.52    inference(superposition,[],[f50,f321])).
% 0.19/0.52  fof(f321,plain,(
% 0.19/0.52    sK4 = k1_tops_1(sK2,k2_pre_topc(sK2,sK4)) | sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3))),
% 0.19/0.52    inference(resolution,[],[f320,f84])).
% 0.19/0.52  fof(f84,plain,(
% 0.19/0.52    v4_tops_1(sK4,sK2) | sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3))),
% 0.19/0.52    inference(subsumption_resolution,[],[f83,f42])).
% 0.19/0.52  fof(f83,plain,(
% 0.19/0.52    sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) | ~l1_pre_topc(sK1) | v4_tops_1(sK4,sK2)),
% 0.19/0.52    inference(subsumption_resolution,[],[f82,f44])).
% 0.19/0.52  fof(f82,plain,(
% 0.19/0.52    sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1) | v4_tops_1(sK4,sK2)),
% 0.19/0.52    inference(resolution,[],[f49,f67])).
% 0.19/0.52  fof(f67,plain,(
% 0.19/0.52    v6_tops_1(sK3,sK1) | v4_tops_1(sK4,sK2)),
% 0.19/0.52    inference(resolution,[],[f39,f46])).
% 0.19/0.52  fof(f39,plain,(
% 0.19/0.52    ( ! [X0,X1] : (~sP0(X0,X1) | v4_tops_1(X1,X0)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f27])).
% 0.19/0.52  fof(f320,plain,(
% 0.19/0.52    ~v4_tops_1(sK4,sK2) | sK4 = k1_tops_1(sK2,k2_pre_topc(sK2,sK4))),
% 0.19/0.52    inference(subsumption_resolution,[],[f319,f43])).
% 0.19/0.52  fof(f319,plain,(
% 0.19/0.52    ~l1_pre_topc(sK2) | ~v4_tops_1(sK4,sK2) | sK4 = k1_tops_1(sK2,k2_pre_topc(sK2,sK4))),
% 0.19/0.52    inference(subsumption_resolution,[],[f318,f45])).
% 0.19/0.52  fof(f318,plain,(
% 0.19/0.52    ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2) | ~v4_tops_1(sK4,sK2) | sK4 = k1_tops_1(sK2,k2_pre_topc(sK2,sK4))),
% 0.19/0.52    inference(subsumption_resolution,[],[f317,f74])).
% 0.19/0.52  fof(f74,plain,(
% 0.19/0.52    r1_tarski(sK4,k2_pre_topc(sK2,sK4))),
% 0.19/0.52    inference(resolution,[],[f71,f45])).
% 0.19/0.52  fof(f71,plain,(
% 0.19/0.52    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) | r1_tarski(X1,k2_pre_topc(sK2,X1))) )),
% 0.19/0.52    inference(resolution,[],[f48,f43])).
% 0.19/0.52  fof(f48,plain,(
% 0.19/0.52    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(X1,k2_pre_topc(X0,X1))) )),
% 0.19/0.52    inference(cnf_transformation,[],[f13])).
% 0.19/0.52  fof(f13,plain,(
% 0.19/0.52    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.19/0.52    inference(ennf_transformation,[],[f3])).
% 0.19/0.52  fof(f3,axiom,(
% 0.19/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 0.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).
% 0.19/0.52  fof(f317,plain,(
% 0.19/0.52    ~r1_tarski(sK4,k2_pre_topc(sK2,sK4)) | ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2) | ~v4_tops_1(sK4,sK2) | sK4 = k1_tops_1(sK2,k2_pre_topc(sK2,sK4))),
% 0.19/0.52    inference(duplicate_literal_removal,[],[f315])).
% 0.19/0.52  fof(f315,plain,(
% 0.19/0.52    ~r1_tarski(sK4,k2_pre_topc(sK2,sK4)) | ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2) | ~v4_tops_1(sK4,sK2) | sK4 = k1_tops_1(sK2,k2_pre_topc(sK2,sK4))),
% 0.19/0.52    inference(resolution,[],[f306,f85])).
% 0.19/0.52  fof(f85,plain,(
% 0.19/0.52    ( ! [X0,X1] : (~r1_tarski(X0,k1_tops_1(X1,k2_pre_topc(X1,X0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~v4_tops_1(X0,X1) | k1_tops_1(X1,k2_pre_topc(X1,X0)) = X0) )),
% 0.19/0.52    inference(resolution,[],[f51,f61])).
% 0.19/0.52  fof(f61,plain,(
% 0.19/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.19/0.52    inference(cnf_transformation,[],[f37])).
% 0.19/0.52  fof(f51,plain,(
% 0.19/0.52    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) | ~v4_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f35])).
% 0.19/0.52  fof(f35,plain,(
% 0.19/0.52    ! [X0] : (! [X1] : (((v4_tops_1(X1,X0) | ~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) & ((r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) | ~v4_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.19/0.52    inference(flattening,[],[f34])).
% 0.19/0.52  fof(f34,plain,(
% 0.19/0.52    ! [X0] : (! [X1] : (((v4_tops_1(X1,X0) | (~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1))) & ((r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) | ~v4_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.19/0.52    inference(nnf_transformation,[],[f15])).
% 0.19/0.52  fof(f15,plain,(
% 0.19/0.52    ! [X0] : (! [X1] : ((v4_tops_1(X1,X0) <=> (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.19/0.52    inference(ennf_transformation,[],[f4])).
% 0.19/0.52  fof(f4,axiom,(
% 0.19/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_tops_1(X1,X0) <=> (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)))))),
% 0.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tops_1)).
% 0.19/0.52  fof(f306,plain,(
% 0.19/0.52    ( ! [X0] : (r1_tarski(sK4,k1_tops_1(sK2,k2_pre_topc(sK2,X0))) | ~r1_tarski(sK4,k2_pre_topc(sK2,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 0.19/0.52    inference(subsumption_resolution,[],[f303,f43])).
% 0.19/0.52  fof(f303,plain,(
% 0.19/0.52    ( ! [X0] : (~r1_tarski(sK4,k2_pre_topc(sK2,X0)) | r1_tarski(sK4,k1_tops_1(sK2,k2_pre_topc(sK2,X0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2)) )),
% 0.19/0.52    inference(resolution,[],[f283,f58])).
% 0.19/0.52  fof(f58,plain,(
% 0.19/0.52    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f23])).
% 0.19/0.52  fof(f23,plain,(
% 0.19/0.52    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.19/0.52    inference(flattening,[],[f22])).
% 0.19/0.52  fof(f22,plain,(
% 0.19/0.52    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.19/0.52    inference(ennf_transformation,[],[f2])).
% 0.19/0.52  fof(f2,axiom,(
% 0.19/0.52    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 0.19/0.52  fof(f283,plain,(
% 0.19/0.52    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) | ~r1_tarski(sK4,X1) | r1_tarski(sK4,k1_tops_1(sK2,X1))) )),
% 0.19/0.52    inference(subsumption_resolution,[],[f282,f43])).
% 0.19/0.52  fof(f282,plain,(
% 0.19/0.52    ( ! [X1] : (r1_tarski(sK4,k1_tops_1(sK2,X1)) | ~r1_tarski(sK4,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2)) )),
% 0.19/0.52    inference(subsumption_resolution,[],[f272,f45])).
% 0.19/0.52  fof(f272,plain,(
% 0.19/0.52    ( ! [X1] : (r1_tarski(sK4,k1_tops_1(sK2,X1)) | ~r1_tarski(sK4,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2)) )),
% 0.19/0.52    inference(superposition,[],[f54,f267])).
% 0.19/0.52  fof(f267,plain,(
% 0.19/0.52    sK4 = k1_tops_1(sK2,sK4)),
% 0.19/0.52    inference(subsumption_resolution,[],[f266,f45])).
% 0.19/0.52  fof(f266,plain,(
% 0.19/0.52    sK4 = k1_tops_1(sK2,sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.19/0.52    inference(duplicate_literal_removal,[],[f265])).
% 0.19/0.52  fof(f265,plain,(
% 0.19/0.52    sK4 = k1_tops_1(sK2,sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) | sK4 = k1_tops_1(sK2,sK4)),
% 0.19/0.52    inference(resolution,[],[f261,f95])).
% 0.19/0.52  fof(f95,plain,(
% 0.19/0.52    ( ! [X1] : (~v3_pre_topc(X1,sK2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) | k1_tops_1(sK2,X1) = X1) )),
% 0.19/0.52    inference(resolution,[],[f92,f43])).
% 0.19/0.52  fof(f92,plain,(
% 0.19/0.52    ( ! [X0,X1] : (~l1_pre_topc(X1) | ~v3_pre_topc(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | k1_tops_1(X1,X0) = X0) )),
% 0.19/0.52    inference(resolution,[],[f91,f44])).
% 0.19/0.52  fof(f91,plain,(
% 0.19/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_pre_topc(X0,X1) | ~l1_pre_topc(X1) | k1_tops_1(X1,X0) = X0) )),
% 0.19/0.52    inference(subsumption_resolution,[],[f90,f42])).
% 0.19/0.52  fof(f90,plain,(
% 0.19/0.52    ( ! [X2,X0,X1] : (~v3_pre_topc(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(sK1) | k1_tops_1(X1,X0) = X0) )),
% 0.19/0.52    inference(resolution,[],[f55,f41])).
% 0.19/0.52  fof(f41,plain,(
% 0.19/0.52    v2_pre_topc(sK1)),
% 0.19/0.52    inference(cnf_transformation,[],[f32])).
% 0.19/0.52  fof(f55,plain,(
% 0.19/0.52    ( ! [X2,X0,X3,X1] : (~v2_pre_topc(X0) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | k1_tops_1(X1,X3) = X3) )),
% 0.19/0.52    inference(cnf_transformation,[],[f19])).
% 0.19/0.52  fof(f19,plain,(
% 0.19/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.19/0.52    inference(flattening,[],[f18])).
% 0.19/0.52  fof(f18,plain,(
% 0.19/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.19/0.52    inference(ennf_transformation,[],[f8])).
% 0.19/0.52  fof(f8,axiom,(
% 0.19/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 0.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_1)).
% 0.19/0.52  fof(f261,plain,(
% 0.19/0.52    v3_pre_topc(sK4,sK2) | sK4 = k1_tops_1(sK2,sK4)),
% 0.19/0.52    inference(resolution,[],[f252,f38])).
% 0.19/0.52  fof(f38,plain,(
% 0.19/0.52    ( ! [X0,X1] : (~sP0(X0,X1) | v3_pre_topc(X1,X0)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f27])).
% 0.19/0.52  fof(f252,plain,(
% 0.19/0.52    sP0(sK2,sK4) | sK4 = k1_tops_1(sK2,sK4)),
% 0.19/0.52    inference(resolution,[],[f251,f247])).
% 0.19/0.52  fof(f251,plain,(
% 0.19/0.52    v4_tops_1(sK3,sK1) | sK4 = k1_tops_1(sK2,sK4)),
% 0.19/0.52    inference(subsumption_resolution,[],[f250,f62])).
% 0.19/0.52  fof(f250,plain,(
% 0.19/0.52    ~r1_tarski(sK3,sK3) | v4_tops_1(sK3,sK1) | sK4 = k1_tops_1(sK2,sK4)),
% 0.19/0.52    inference(superposition,[],[f239,f106])).
% 0.19/0.52  fof(f106,plain,(
% 0.19/0.52    sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) | sK4 = k1_tops_1(sK2,sK4)),
% 0.19/0.52    inference(subsumption_resolution,[],[f105,f42])).
% 0.19/0.52  fof(f105,plain,(
% 0.19/0.52    sK4 = k1_tops_1(sK2,sK4) | sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) | ~l1_pre_topc(sK1)),
% 0.19/0.52    inference(subsumption_resolution,[],[f103,f44])).
% 0.19/0.52  fof(f103,plain,(
% 0.19/0.52    sK4 = k1_tops_1(sK2,sK4) | sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1)),
% 0.19/0.52    inference(resolution,[],[f101,f49])).
% 0.19/0.52  fof(f101,plain,(
% 0.19/0.52    v6_tops_1(sK3,sK1) | sK4 = k1_tops_1(sK2,sK4)),
% 0.19/0.52    inference(subsumption_resolution,[],[f99,f45])).
% 0.19/0.52  fof(f99,plain,(
% 0.19/0.52    ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) | sK4 = k1_tops_1(sK2,sK4) | v6_tops_1(sK3,sK1)),
% 0.19/0.52    inference(resolution,[],[f95,f66])).
% 0.19/0.52  fof(f66,plain,(
% 0.19/0.52    v3_pre_topc(sK4,sK2) | v6_tops_1(sK3,sK1)),
% 0.19/0.52    inference(resolution,[],[f38,f46])).
% 0.19/0.52  fof(f54,plain,(
% 0.19/0.52    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f17])).
% 0.19/0.52  fof(f17,plain,(
% 0.19/0.52    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.19/0.52    inference(flattening,[],[f16])).
% 0.19/0.52  fof(f16,plain,(
% 0.19/0.52    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.19/0.52    inference(ennf_transformation,[],[f7])).
% 0.19/0.52  fof(f7,axiom,(
% 0.19/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 0.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).
% 0.19/0.52  fof(f50,plain,(
% 0.19/0.52    ( ! [X0,X1] : (k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1 | v6_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f33])).
% 0.19/0.52  fof(f239,plain,(
% 0.19/0.52    ~r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3) | v4_tops_1(sK3,sK1)),
% 0.19/0.52    inference(subsumption_resolution,[],[f238,f42])).
% 0.19/0.52  fof(f238,plain,(
% 0.19/0.52    v4_tops_1(sK3,sK1) | ~r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3) | ~l1_pre_topc(sK1)),
% 0.19/0.52    inference(subsumption_resolution,[],[f237,f44])).
% 0.19/0.52  fof(f237,plain,(
% 0.19/0.52    v4_tops_1(sK3,sK1) | ~r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1)),
% 0.19/0.52    inference(subsumption_resolution,[],[f229,f72])).
% 0.19/0.52  fof(f72,plain,(
% 0.19/0.52    r1_tarski(sK3,k2_pre_topc(sK1,sK3))),
% 0.19/0.52    inference(resolution,[],[f70,f44])).
% 0.19/0.52  fof(f70,plain,(
% 0.19/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | r1_tarski(X0,k2_pre_topc(sK1,X0))) )),
% 0.19/0.52    inference(resolution,[],[f48,f42])).
% 0.19/0.52  fof(f229,plain,(
% 0.19/0.52    ~r1_tarski(sK3,k2_pre_topc(sK1,sK3)) | v4_tops_1(sK3,sK1) | ~r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1)),
% 0.19/0.52    inference(superposition,[],[f53,f227])).
% 0.19/0.52  fof(f227,plain,(
% 0.19/0.52    sK3 = k1_tops_1(sK1,sK3)),
% 0.19/0.52    inference(subsumption_resolution,[],[f226,f42])).
% 0.19/0.52  fof(f226,plain,(
% 0.19/0.52    sK3 = k1_tops_1(sK1,sK3) | ~l1_pre_topc(sK1)),
% 0.19/0.52    inference(subsumption_resolution,[],[f225,f44])).
% 0.19/0.52  fof(f225,plain,(
% 0.19/0.52    sK3 = k1_tops_1(sK1,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1)),
% 0.19/0.52    inference(resolution,[],[f220,f58])).
% 0.19/0.52  fof(f220,plain,(
% 0.19/0.52    ~m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) | sK3 = k1_tops_1(sK1,sK3)),
% 0.19/0.52    inference(subsumption_resolution,[],[f219,f44])).
% 0.19/0.52  fof(f219,plain,(
% 0.19/0.52    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) | sK3 = k1_tops_1(sK1,sK3) | ~m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.19/0.52    inference(duplicate_literal_removal,[],[f208])).
% 0.19/0.52  fof(f208,plain,(
% 0.19/0.52    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) | sK3 = k1_tops_1(sK1,sK3) | ~m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) | sK3 = k1_tops_1(sK1,sK3)),
% 0.19/0.52    inference(superposition,[],[f98,f204])).
% 0.19/0.52  fof(f204,plain,(
% 0.19/0.52    sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) | sK3 = k1_tops_1(sK1,sK3)),
% 0.19/0.52    inference(subsumption_resolution,[],[f203,f42])).
% 0.19/0.52  fof(f203,plain,(
% 0.19/0.52    sK3 = k1_tops_1(sK1,sK3) | sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) | ~l1_pre_topc(sK1)),
% 0.19/0.52    inference(subsumption_resolution,[],[f202,f44])).
% 0.19/0.52  fof(f202,plain,(
% 0.19/0.52    sK3 = k1_tops_1(sK1,sK3) | sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1)),
% 0.19/0.52    inference(duplicate_literal_removal,[],[f200])).
% 0.19/0.52  fof(f200,plain,(
% 0.19/0.52    sK3 = k1_tops_1(sK1,sK3) | sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) | sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1)),
% 0.19/0.52    inference(resolution,[],[f199,f49])).
% 0.19/0.52  fof(f199,plain,(
% 0.19/0.52    v6_tops_1(sK3,sK1) | sK3 = k1_tops_1(sK1,sK3) | sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3))),
% 0.19/0.52    inference(resolution,[],[f198,f46])).
% 0.19/0.52  fof(f198,plain,(
% 0.19/0.52    ~sP0(sK2,sK4) | sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) | sK3 = k1_tops_1(sK1,sK3)),
% 0.19/0.52    inference(resolution,[],[f190,f40])).
% 0.19/0.52  fof(f190,plain,(
% 0.19/0.52    v6_tops_1(sK4,sK2) | sK3 = k1_tops_1(sK1,sK3) | sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3))),
% 0.19/0.52    inference(subsumption_resolution,[],[f189,f43])).
% 0.19/0.52  fof(f189,plain,(
% 0.19/0.52    v6_tops_1(sK4,sK2) | ~l1_pre_topc(sK2) | sK3 = k1_tops_1(sK1,sK3) | sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3))),
% 0.19/0.52    inference(subsumption_resolution,[],[f186,f45])).
% 0.19/0.52  fof(f186,plain,(
% 0.19/0.52    v6_tops_1(sK4,sK2) | ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2) | sK3 = k1_tops_1(sK1,sK3) | sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3))),
% 0.19/0.52    inference(trivial_inequality_removal,[],[f179])).
% 0.19/0.52  fof(f179,plain,(
% 0.19/0.52    sK4 != sK4 | v6_tops_1(sK4,sK2) | ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2) | sK3 = k1_tops_1(sK1,sK3) | sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3))),
% 0.19/0.52    inference(superposition,[],[f50,f174])).
% 0.19/0.52  fof(f174,plain,(
% 0.19/0.52    sK4 = k1_tops_1(sK2,k2_pre_topc(sK2,sK4)) | sK3 = k1_tops_1(sK1,sK3) | sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3))),
% 0.19/0.52    inference(resolution,[],[f173,f84])).
% 0.19/0.52  fof(f173,plain,(
% 0.19/0.52    ~v4_tops_1(sK4,sK2) | sK3 = k1_tops_1(sK1,sK3) | sK4 = k1_tops_1(sK2,k2_pre_topc(sK2,sK4))),
% 0.19/0.52    inference(subsumption_resolution,[],[f172,f43])).
% 0.19/0.52  fof(f172,plain,(
% 0.19/0.52    sK3 = k1_tops_1(sK1,sK3) | ~l1_pre_topc(sK2) | ~v4_tops_1(sK4,sK2) | sK4 = k1_tops_1(sK2,k2_pre_topc(sK2,sK4))),
% 0.19/0.52    inference(subsumption_resolution,[],[f171,f45])).
% 0.19/0.52  fof(f171,plain,(
% 0.19/0.52    sK3 = k1_tops_1(sK1,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2) | ~v4_tops_1(sK4,sK2) | sK4 = k1_tops_1(sK2,k2_pre_topc(sK2,sK4))),
% 0.19/0.52    inference(subsumption_resolution,[],[f170,f74])).
% 0.19/0.52  fof(f170,plain,(
% 0.19/0.52    ~r1_tarski(sK4,k2_pre_topc(sK2,sK4)) | sK3 = k1_tops_1(sK1,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2) | ~v4_tops_1(sK4,sK2) | sK4 = k1_tops_1(sK2,k2_pre_topc(sK2,sK4))),
% 0.19/0.52    inference(duplicate_literal_removal,[],[f168])).
% 0.19/0.52  fof(f168,plain,(
% 0.19/0.52    ~r1_tarski(sK4,k2_pre_topc(sK2,sK4)) | sK3 = k1_tops_1(sK1,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2) | ~v4_tops_1(sK4,sK2) | sK4 = k1_tops_1(sK2,k2_pre_topc(sK2,sK4))),
% 0.19/0.52    inference(resolution,[],[f163,f85])).
% 0.19/0.52  fof(f163,plain,(
% 0.19/0.52    ( ! [X0] : (r1_tarski(sK4,k1_tops_1(sK2,k2_pre_topc(sK2,X0))) | ~r1_tarski(sK4,k2_pre_topc(sK2,X0)) | sK3 = k1_tops_1(sK1,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 0.19/0.52    inference(subsumption_resolution,[],[f161,f43])).
% 0.19/0.52  fof(f161,plain,(
% 0.19/0.52    ( ! [X0] : (~r1_tarski(sK4,k2_pre_topc(sK2,X0)) | r1_tarski(sK4,k1_tops_1(sK2,k2_pre_topc(sK2,X0))) | sK3 = k1_tops_1(sK1,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2)) )),
% 0.19/0.52    inference(resolution,[],[f149,f58])).
% 0.19/0.52  fof(f149,plain,(
% 0.19/0.52    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) | ~r1_tarski(sK4,X1) | r1_tarski(sK4,k1_tops_1(sK2,X1)) | sK3 = k1_tops_1(sK1,sK3)) )),
% 0.19/0.52    inference(subsumption_resolution,[],[f148,f43])).
% 0.19/0.52  fof(f148,plain,(
% 0.19/0.52    ( ! [X1] : (r1_tarski(sK4,k1_tops_1(sK2,X1)) | ~r1_tarski(sK4,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2) | sK3 = k1_tops_1(sK1,sK3)) )),
% 0.19/0.52    inference(subsumption_resolution,[],[f138,f45])).
% 0.19/0.52  fof(f138,plain,(
% 0.19/0.52    ( ! [X1] : (r1_tarski(sK4,k1_tops_1(sK2,X1)) | ~r1_tarski(sK4,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2) | sK3 = k1_tops_1(sK1,sK3)) )),
% 0.19/0.52    inference(superposition,[],[f54,f135])).
% 0.19/0.52  fof(f135,plain,(
% 0.19/0.52    sK4 = k1_tops_1(sK2,sK4) | sK3 = k1_tops_1(sK1,sK3)),
% 0.19/0.52    inference(subsumption_resolution,[],[f134,f44])).
% 0.19/0.52  fof(f134,plain,(
% 0.19/0.52    sK4 = k1_tops_1(sK2,sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) | sK3 = k1_tops_1(sK1,sK3)),
% 0.19/0.52    inference(resolution,[],[f132,f94])).
% 0.19/0.52  fof(f94,plain,(
% 0.19/0.52    ( ! [X0] : (~v3_pre_topc(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | k1_tops_1(sK1,X0) = X0) )),
% 0.19/0.52    inference(resolution,[],[f92,f42])).
% 0.19/0.52  fof(f132,plain,(
% 0.19/0.52    v3_pre_topc(sK3,sK1) | sK4 = k1_tops_1(sK2,sK4)),
% 0.19/0.52    inference(subsumption_resolution,[],[f131,f42])).
% 0.19/0.52  fof(f131,plain,(
% 0.19/0.52    v3_pre_topc(sK3,sK1) | sK4 = k1_tops_1(sK2,sK4) | ~l1_pre_topc(sK1)),
% 0.19/0.52    inference(subsumption_resolution,[],[f130,f44])).
% 0.19/0.52  fof(f130,plain,(
% 0.19/0.52    v3_pre_topc(sK3,sK1) | sK4 = k1_tops_1(sK2,sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1)),
% 0.19/0.52    inference(resolution,[],[f129,f58])).
% 0.19/0.52  fof(f129,plain,(
% 0.19/0.52    ~m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) | v3_pre_topc(sK3,sK1) | sK4 = k1_tops_1(sK2,sK4)),
% 0.19/0.52    inference(subsumption_resolution,[],[f128,f41])).
% 0.19/0.52  fof(f128,plain,(
% 0.19/0.52    v3_pre_topc(sK3,sK1) | ~m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) | ~v2_pre_topc(sK1) | sK4 = k1_tops_1(sK2,sK4)),
% 0.19/0.52    inference(subsumption_resolution,[],[f118,f42])).
% 0.19/0.52  fof(f118,plain,(
% 0.19/0.52    v3_pre_topc(sK3,sK1) | ~m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | sK4 = k1_tops_1(sK2,sK4)),
% 0.19/0.52    inference(superposition,[],[f57,f106])).
% 0.19/0.52  fof(f57,plain,(
% 0.19/0.52    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f21])).
% 0.19/0.52  fof(f21,plain,(
% 0.19/0.52    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.19/0.52    inference(flattening,[],[f20])).
% 0.19/0.52  fof(f20,plain,(
% 0.19/0.52    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.19/0.52    inference(ennf_transformation,[],[f6])).
% 0.19/0.52  fof(f6,axiom,(
% 0.19/0.52    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 0.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).
% 0.19/0.52  fof(f98,plain,(
% 0.19/0.52    ( ! [X0] : (~m1_subset_1(k1_tops_1(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) | k1_tops_1(sK1,X0) = k1_tops_1(sK1,k1_tops_1(sK1,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))) )),
% 0.19/0.52    inference(subsumption_resolution,[],[f97,f41])).
% 0.19/0.52  fof(f97,plain,(
% 0.19/0.52    ( ! [X0] : (~m1_subset_1(k1_tops_1(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) | k1_tops_1(sK1,X0) = k1_tops_1(sK1,k1_tops_1(sK1,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~v2_pre_topc(sK1)) )),
% 0.19/0.52    inference(subsumption_resolution,[],[f96,f42])).
% 0.19/0.52  fof(f96,plain,(
% 0.19/0.52    ( ! [X0] : (~m1_subset_1(k1_tops_1(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) | k1_tops_1(sK1,X0) = k1_tops_1(sK1,k1_tops_1(sK1,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1)) )),
% 0.19/0.52    inference(resolution,[],[f94,f57])).
% 0.19/0.52  fof(f53,plain,(
% 0.19/0.52    ( ! [X0,X1] : (~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | v4_tops_1(X1,X0) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f35])).
% 0.19/0.52  fof(f247,plain,(
% 0.19/0.52    ~v4_tops_1(sK3,sK1) | sP0(sK2,sK4)),
% 0.19/0.52    inference(subsumption_resolution,[],[f47,f246])).
% 0.19/0.52  fof(f246,plain,(
% 0.19/0.52    v3_pre_topc(sK3,sK1)),
% 0.19/0.52    inference(subsumption_resolution,[],[f245,f41])).
% 0.19/0.52  fof(f245,plain,(
% 0.19/0.52    v3_pre_topc(sK3,sK1) | ~v2_pre_topc(sK1)),
% 0.19/0.52    inference(subsumption_resolution,[],[f244,f42])).
% 0.19/0.52  fof(f244,plain,(
% 0.19/0.52    v3_pre_topc(sK3,sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1)),
% 0.19/0.52    inference(subsumption_resolution,[],[f235,f44])).
% 0.19/0.52  fof(f235,plain,(
% 0.19/0.52    v3_pre_topc(sK3,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1)),
% 0.19/0.52    inference(trivial_inequality_removal,[],[f232])).
% 0.19/0.52  fof(f232,plain,(
% 0.19/0.52    sK3 != sK3 | v3_pre_topc(sK3,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1)),
% 0.19/0.52    inference(superposition,[],[f65,f227])).
% 0.19/0.52  fof(f65,plain,(
% 0.19/0.52    ( ! [X0,X1] : (k1_tops_1(X1,X0) != X0 | v3_pre_topc(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) )),
% 0.19/0.52    inference(duplicate_literal_removal,[],[f64])).
% 0.19/0.52  fof(f64,plain,(
% 0.19/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | v3_pre_topc(X0,X1) | k1_tops_1(X1,X0) != X0 | ~l1_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) )),
% 0.19/0.52    inference(condensation,[],[f56])).
% 0.19/0.52  % (3011)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.19/0.52  fof(f56,plain,(
% 0.19/0.52    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f19])).
% 0.19/0.52  fof(f47,plain,(
% 0.19/0.52    ~v3_pre_topc(sK3,sK1) | ~v4_tops_1(sK3,sK1) | sP0(sK2,sK4)),
% 0.19/0.52    inference(cnf_transformation,[],[f32])).
% 0.19/0.52  fof(f387,plain,(
% 0.19/0.52    ~sP0(sK2,sK4)),
% 0.19/0.52    inference(resolution,[],[f379,f40])).
% 0.19/0.52  fof(f379,plain,(
% 0.19/0.52    v6_tops_1(sK4,sK2)),
% 0.19/0.52    inference(subsumption_resolution,[],[f378,f43])).
% 0.19/0.52  fof(f378,plain,(
% 0.19/0.52    v6_tops_1(sK4,sK2) | ~l1_pre_topc(sK2)),
% 0.19/0.52    inference(subsumption_resolution,[],[f377,f45])).
% 0.19/0.52  fof(f377,plain,(
% 0.19/0.52    v6_tops_1(sK4,sK2) | ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2)),
% 0.19/0.52    inference(trivial_inequality_removal,[],[f370])).
% 0.19/0.52  fof(f370,plain,(
% 0.19/0.52    sK4 != sK4 | v6_tops_1(sK4,sK2) | ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2)),
% 0.19/0.52    inference(superposition,[],[f50,f355])).
% 0.19/0.52  fof(f355,plain,(
% 0.19/0.52    sK4 = k1_tops_1(sK2,k2_pre_topc(sK2,sK4))),
% 0.19/0.52    inference(subsumption_resolution,[],[f320,f353])).
% 0.19/0.52  fof(f353,plain,(
% 0.19/0.52    v4_tops_1(sK4,sK2)),
% 0.19/0.52    inference(resolution,[],[f352,f39])).
% 0.19/0.52  % SZS output end Proof for theBenchmark
% 0.19/0.52  % (3007)------------------------------
% 0.19/0.52  % (3007)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.52  % (3007)Termination reason: Refutation
% 0.19/0.52  
% 0.19/0.52  % (3007)Memory used [KB]: 6268
% 0.19/0.52  % (3007)Time elapsed: 0.111 s
% 0.19/0.52  % (3007)------------------------------
% 0.19/0.52  % (3007)------------------------------
% 0.19/0.53  % (3023)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.19/0.53  % (2995)Success in time 0.172 s
%------------------------------------------------------------------------------
