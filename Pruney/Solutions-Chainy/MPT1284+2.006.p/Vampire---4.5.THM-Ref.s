%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:05 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  160 (8514 expanded)
%              Number of leaves         :   14 (3494 expanded)
%              Depth                    :   72
%              Number of atoms          :  568 (72370 expanded)
%              Number of equality atoms :  108 (1737 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f339,plain,(
    $false ),
    inference(subsumption_resolution,[],[f338,f305])).

fof(f305,plain,(
    sP0(sK2,sK4) ),
    inference(subsumption_resolution,[],[f233,f304])).

fof(f304,plain,(
    v4_tops_1(sK3,sK1) ),
    inference(subsumption_resolution,[],[f303,f62])).

% (24050)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f303,plain,
    ( ~ r1_tarski(sK3,sK3)
    | v4_tops_1(sK3,sK1) ),
    inference(backward_demodulation,[],[f229,f298])).

fof(f298,plain,(
    sK3 = k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) ),
    inference(subsumption_resolution,[],[f296,f44])).

fof(f44,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ( ( ( ~ v4_tops_1(sK3,sK1)
          | ~ v4_pre_topc(sK3,sK1) )
        & v5_tops_1(sK3,sK1) )
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
                          | ~ v4_pre_topc(X2,X0) )
                        & v5_tops_1(X2,X0) )
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
                        | ~ v4_pre_topc(X2,sK1) )
                      & v5_tops_1(X2,sK1) )
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
                      | ~ v4_pre_topc(X2,sK1) )
                    & v5_tops_1(X2,sK1) )
                  | sP0(X1,X3) )
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) )
        & l1_pre_topc(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ( ( ~ v4_tops_1(X2,sK1)
                    | ~ v4_pre_topc(X2,sK1) )
                  & v5_tops_1(X2,sK1) )
                | sP0(sK2,X3) )
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) )
      & l1_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ( ( ~ v4_tops_1(X2,sK1)
                  | ~ v4_pre_topc(X2,sK1) )
                & v5_tops_1(X2,sK1) )
              | sP0(sK2,X3) )
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) )
   => ( ? [X3] :
          ( ( ( ( ~ v4_tops_1(sK3,sK1)
                | ~ v4_pre_topc(sK3,sK1) )
              & v5_tops_1(sK3,sK1) )
            | sP0(sK2,X3) )
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X3] :
        ( ( ( ( ~ v4_tops_1(sK3,sK1)
              | ~ v4_pre_topc(sK3,sK1) )
            & v5_tops_1(sK3,sK1) )
          | sP0(sK2,X3) )
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
   => ( ( ( ( ~ v4_tops_1(sK3,sK1)
            | ~ v4_pre_topc(sK3,sK1) )
          & v5_tops_1(sK3,sK1) )
        | sP0(sK2,sK4) )
      & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( ~ v4_tops_1(X2,X0)
                        | ~ v4_pre_topc(X2,X0) )
                      & v5_tops_1(X2,X0) )
                    | sP0(X1,X3) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(definition_folding,[],[f12,f24])).

fof(f24,plain,(
    ! [X1,X3] :
      ( ( ~ v5_tops_1(X3,X1)
        & v4_tops_1(X3,X1)
        & v4_pre_topc(X3,X1) )
      | ~ sP0(X1,X3) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( ~ v4_tops_1(X2,X0)
                        | ~ v4_pre_topc(X2,X0) )
                      & v5_tops_1(X2,X0) )
                    | ( ~ v5_tops_1(X3,X1)
                      & v4_tops_1(X3,X1)
                      & v4_pre_topc(X3,X1) ) )
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
                        | ~ v4_pre_topc(X2,X0) )
                      & v5_tops_1(X2,X0) )
                    | ( ~ v5_tops_1(X3,X1)
                      & v4_tops_1(X3,X1)
                      & v4_pre_topc(X3,X1) ) )
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
                   => ( ( v5_tops_1(X2,X0)
                       => ( v4_tops_1(X2,X0)
                          & v4_pre_topc(X2,X0) ) )
                      & ( ( v4_tops_1(X3,X1)
                          & v4_pre_topc(X3,X1) )
                       => v5_tops_1(X3,X1) ) ) ) ) ) ) ),
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
                 => ( ( v5_tops_1(X2,X0)
                     => ( v4_tops_1(X2,X0)
                        & v4_pre_topc(X2,X0) ) )
                    & ( ( v4_tops_1(X3,X1)
                        & v4_pre_topc(X3,X1) )
                     => v5_tops_1(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_tops_1)).

fof(f296,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | sK3 = k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) ),
    inference(resolution,[],[f295,f83])).

fof(f83,plain,(
    ! [X0] :
      ( ~ v5_tops_1(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | k2_pre_topc(sK1,k1_tops_1(sK1,X0)) = X0 ) ),
    inference(resolution,[],[f51,f42])).

fof(f42,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v5_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_tops_1(X1,X0)
              | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1 )
            & ( k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1
              | ~ v5_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tops_1)).

fof(f295,plain,(
    v5_tops_1(sK3,sK1) ),
    inference(subsumption_resolution,[],[f294,f113])).

fof(f113,plain,
    ( v5_tops_1(sK3,sK1)
    | sK3 != k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) ),
    inference(resolution,[],[f111,f44])).

fof(f111,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | k2_pre_topc(sK1,k1_tops_1(sK1,X0)) != X0
      | v5_tops_1(X0,sK1) ) ),
    inference(resolution,[],[f52,f42])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v5_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f294,plain,
    ( sK3 = k2_pre_topc(sK1,k1_tops_1(sK1,sK3))
    | v5_tops_1(sK3,sK1) ),
    inference(resolution,[],[f293,f46])).

fof(f46,plain,
    ( sP0(sK2,sK4)
    | v5_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f293,plain,
    ( ~ sP0(sK2,sK4)
    | sK3 = k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) ),
    inference(resolution,[],[f289,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v5_tops_1(X1,X0)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ~ v5_tops_1(X1,X0)
        & v4_tops_1(X1,X0)
        & v4_pre_topc(X1,X0) )
      | ~ sP0(X0,X1) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X1,X3] :
      ( ( ~ v5_tops_1(X3,X1)
        & v4_tops_1(X3,X1)
        & v4_pre_topc(X3,X1) )
      | ~ sP0(X1,X3) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f289,plain,
    ( v5_tops_1(sK4,sK2)
    | sK3 = k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) ),
    inference(subsumption_resolution,[],[f287,f45])).

fof(f45,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f32])).

fof(f287,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | v5_tops_1(sK4,sK2)
    | sK3 = k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) ),
    inference(trivial_inequality_removal,[],[f284])).

fof(f284,plain,
    ( sK4 != sK4
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | v5_tops_1(sK4,sK2)
    | sK3 = k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) ),
    inference(superposition,[],[f112,f266])).

fof(f266,plain,
    ( sK4 = k2_pre_topc(sK2,k1_tops_1(sK2,sK4))
    | sK3 = k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) ),
    inference(subsumption_resolution,[],[f126,f263])).

fof(f263,plain,(
    r1_tarski(k2_pre_topc(sK2,k1_tops_1(sK2,sK4)),sK4) ),
    inference(backward_demodulation,[],[f166,f258])).

fof(f258,plain,(
    sK4 = k2_pre_topc(sK2,sK4) ),
    inference(subsumption_resolution,[],[f257,f43])).

fof(f43,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f257,plain,
    ( sK4 = k2_pre_topc(sK2,sK4)
    | ~ l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f256,f45])).

fof(f256,plain,
    ( sK4 = k2_pre_topc(sK2,sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(duplicate_literal_removal,[],[f255])).

fof(f255,plain,
    ( sK4 = k2_pre_topc(sK2,sK4)
    | sK4 = k2_pre_topc(sK2,sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f248,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f248,plain,
    ( v4_pre_topc(sK4,sK2)
    | sK4 = k2_pre_topc(sK2,sK4) ),
    inference(resolution,[],[f239,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f239,plain,
    ( sP0(sK2,sK4)
    | sK4 = k2_pre_topc(sK2,sK4) ),
    inference(resolution,[],[f238,f233])).

fof(f238,plain,
    ( v4_tops_1(sK3,sK1)
    | sK4 = k2_pre_topc(sK2,sK4) ),
    inference(subsumption_resolution,[],[f237,f62])).

fof(f237,plain,
    ( ~ r1_tarski(sK3,sK3)
    | v4_tops_1(sK3,sK1)
    | sK4 = k2_pre_topc(sK2,sK4) ),
    inference(superposition,[],[f229,f91])).

fof(f91,plain,
    ( sK3 = k2_pre_topc(sK1,k1_tops_1(sK1,sK3))
    | sK4 = k2_pre_topc(sK2,sK4) ),
    inference(subsumption_resolution,[],[f90,f43])).

fof(f90,plain,
    ( sK3 = k2_pre_topc(sK1,k1_tops_1(sK1,sK3))
    | sK4 = k2_pre_topc(sK2,sK4)
    | ~ l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f89,f45])).

fof(f89,plain,
    ( sK3 = k2_pre_topc(sK1,k1_tops_1(sK1,sK3))
    | sK4 = k2_pre_topc(sK2,sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f88,f49])).

fof(f88,plain,
    ( v4_pre_topc(sK4,sK2)
    | sK3 = k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) ),
    inference(subsumption_resolution,[],[f86,f44])).

fof(f86,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | sK3 = k2_pre_topc(sK1,k1_tops_1(sK1,sK3))
    | v4_pre_topc(sK4,sK2) ),
    inference(resolution,[],[f83,f64])).

fof(f64,plain,
    ( v5_tops_1(sK3,sK1)
    | v4_pre_topc(sK4,sK2) ),
    inference(resolution,[],[f38,f46])).

fof(f166,plain,(
    r1_tarski(k2_pre_topc(sK2,k1_tops_1(sK2,sK4)),k2_pre_topc(sK2,sK4)) ),
    inference(subsumption_resolution,[],[f164,f73])).

fof(f73,plain,(
    r1_tarski(k1_tops_1(sK2,sK4),sK4) ),
    inference(resolution,[],[f70,f45])).

fof(f70,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | r1_tarski(k1_tops_1(sK2,X1),X1) ) ),
    inference(resolution,[],[f48,f43])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(f164,plain,
    ( r1_tarski(k2_pre_topc(sK2,k1_tops_1(sK2,sK4)),k2_pre_topc(sK2,sK4))
    | ~ r1_tarski(k1_tops_1(sK2,sK4),sK4) ),
    inference(resolution,[],[f161,f45])).

fof(f161,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | r1_tarski(k2_pre_topc(sK2,k1_tops_1(sK2,sK4)),k2_pre_topc(sK2,X0))
      | ~ r1_tarski(k1_tops_1(sK2,sK4),X0) ) ),
    inference(resolution,[],[f136,f45])).

fof(f136,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r1_tarski(k1_tops_1(sK2,X2),X1)
      | r1_tarski(k2_pre_topc(sK2,k1_tops_1(sK2,X2)),k2_pre_topc(sK2,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(subsumption_resolution,[],[f135,f43])).

fof(f135,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r1_tarski(k1_tops_1(sK2,X2),X1)
      | r1_tarski(k2_pre_topc(sK2,k1_tops_1(sK2,X2)),k2_pre_topc(sK2,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_pre_topc(sK2) ) ),
    inference(resolution,[],[f129,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

% (24056)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

fof(f129,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r1_tarski(X2,X3)
      | r1_tarski(k2_pre_topc(sK2,X2),k2_pre_topc(sK2,X3)) ) ),
    inference(resolution,[],[f56,f43])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_pre_topc)).

fof(f126,plain,
    ( ~ r1_tarski(k2_pre_topc(sK2,k1_tops_1(sK2,sK4)),sK4)
    | sK3 = k2_pre_topc(sK1,k1_tops_1(sK1,sK3))
    | sK4 = k2_pre_topc(sK2,k1_tops_1(sK2,sK4)) ),
    inference(resolution,[],[f125,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f125,plain,
    ( r1_tarski(sK4,k2_pre_topc(sK2,k1_tops_1(sK2,sK4)))
    | sK3 = k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) ),
    inference(subsumption_resolution,[],[f124,f43])).

fof(f124,plain,
    ( r1_tarski(sK4,k2_pre_topc(sK2,k1_tops_1(sK2,sK4)))
    | ~ l1_pre_topc(sK2)
    | sK3 = k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) ),
    inference(subsumption_resolution,[],[f123,f45])).

fof(f123,plain,
    ( r1_tarski(sK4,k2_pre_topc(sK2,k1_tops_1(sK2,sK4)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | sK3 = k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) ),
    inference(resolution,[],[f54,f87])).

fof(f87,plain,
    ( v4_tops_1(sK4,sK2)
    | sK3 = k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) ),
    inference(subsumption_resolution,[],[f85,f44])).

fof(f85,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | sK3 = k2_pre_topc(sK1,k1_tops_1(sK1,sK3))
    | v4_tops_1(sK4,sK2) ),
    inference(resolution,[],[f83,f65])).

fof(f65,plain,
    ( v5_tops_1(sK3,sK1)
    | v4_tops_1(sK4,sK2) ),
    inference(resolution,[],[f39,f46])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | v4_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v4_tops_1(X1,X0)
      | r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
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
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_tops_1)).

fof(f112,plain,(
    ! [X1] :
      ( k2_pre_topc(sK2,k1_tops_1(sK2,X1)) != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | v5_tops_1(X1,sK2) ) ),
    inference(resolution,[],[f52,f43])).

fof(f229,plain,
    ( ~ r1_tarski(sK3,k2_pre_topc(sK1,k1_tops_1(sK1,sK3)))
    | v4_tops_1(sK3,sK1) ),
    inference(subsumption_resolution,[],[f228,f44])).

fof(f228,plain,
    ( ~ r1_tarski(sK3,k2_pre_topc(sK1,k1_tops_1(sK1,sK3)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | v4_tops_1(sK3,sK1) ),
    inference(subsumption_resolution,[],[f223,f71])).

fof(f71,plain,(
    r1_tarski(k1_tops_1(sK1,sK3),sK3) ),
    inference(resolution,[],[f69,f44])).

fof(f69,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | r1_tarski(k1_tops_1(sK1,X0),X0) ) ),
    inference(resolution,[],[f48,f42])).

fof(f223,plain,
    ( ~ r1_tarski(k1_tops_1(sK1,sK3),sK3)
    | ~ r1_tarski(sK3,k2_pre_topc(sK1,k1_tops_1(sK1,sK3)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | v4_tops_1(sK3,sK1) ),
    inference(superposition,[],[f140,f212])).

fof(f212,plain,(
    sK3 = k2_pre_topc(sK1,sK3) ),
    inference(subsumption_resolution,[],[f211,f42])).

fof(f211,plain,
    ( sK3 = k2_pre_topc(sK1,sK3)
    | ~ l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f210,f44])).

fof(f210,plain,
    ( sK3 = k2_pre_topc(sK1,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f203,f58])).

fof(f203,plain,
    ( ~ m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | sK3 = k2_pre_topc(sK1,sK3) ),
    inference(subsumption_resolution,[],[f201,f44])).

fof(f201,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | sK3 = k2_pre_topc(sK1,sK3) ),
    inference(duplicate_literal_removal,[],[f197])).

fof(f197,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | sK3 = k2_pre_topc(sK1,sK3)
    | sK3 = k2_pre_topc(sK1,sK3) ),
    inference(superposition,[],[f149,f194])).

fof(f194,plain,
    ( sK3 = k2_pre_topc(sK1,k1_tops_1(sK1,sK3))
    | sK3 = k2_pre_topc(sK1,sK3) ),
    inference(subsumption_resolution,[],[f192,f44])).

fof(f192,plain,
    ( sK3 = k2_pre_topc(sK1,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | sK3 = k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) ),
    inference(resolution,[],[f191,f83])).

fof(f191,plain,
    ( v5_tops_1(sK3,sK1)
    | sK3 = k2_pre_topc(sK1,sK3) ),
    inference(subsumption_resolution,[],[f190,f113])).

fof(f190,plain,
    ( sK3 = k2_pre_topc(sK1,sK3)
    | sK3 = k2_pre_topc(sK1,k1_tops_1(sK1,sK3))
    | v5_tops_1(sK3,sK1) ),
    inference(resolution,[],[f189,f46])).

fof(f189,plain,
    ( ~ sP0(sK2,sK4)
    | sK3 = k2_pre_topc(sK1,sK3)
    | sK3 = k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) ),
    inference(resolution,[],[f185,f40])).

fof(f185,plain,
    ( v5_tops_1(sK4,sK2)
    | sK3 = k2_pre_topc(sK1,k1_tops_1(sK1,sK3))
    | sK3 = k2_pre_topc(sK1,sK3) ),
    inference(subsumption_resolution,[],[f182,f45])).

fof(f182,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | v5_tops_1(sK4,sK2)
    | sK3 = k2_pre_topc(sK1,k1_tops_1(sK1,sK3))
    | sK3 = k2_pre_topc(sK1,sK3) ),
    inference(trivial_inequality_removal,[],[f179])).

fof(f179,plain,
    ( sK4 != sK4
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | v5_tops_1(sK4,sK2)
    | sK3 = k2_pre_topc(sK1,k1_tops_1(sK1,sK3))
    | sK3 = k2_pre_topc(sK1,sK3) ),
    inference(superposition,[],[f112,f170])).

fof(f170,plain,
    ( sK4 = k2_pre_topc(sK2,k1_tops_1(sK2,sK4))
    | sK3 = k2_pre_topc(sK1,k1_tops_1(sK1,sK3))
    | sK3 = k2_pre_topc(sK1,sK3) ),
    inference(resolution,[],[f169,f126])).

fof(f169,plain,
    ( r1_tarski(k2_pre_topc(sK2,k1_tops_1(sK2,sK4)),sK4)
    | sK3 = k2_pre_topc(sK1,sK3) ),
    inference(superposition,[],[f166,f105])).

fof(f105,plain,
    ( sK4 = k2_pre_topc(sK2,sK4)
    | sK3 = k2_pre_topc(sK1,sK3) ),
    inference(subsumption_resolution,[],[f104,f42])).

fof(f104,plain,
    ( sK4 = k2_pre_topc(sK2,sK4)
    | sK3 = k2_pre_topc(sK1,sK3)
    | ~ l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f103,f44])).

fof(f103,plain,
    ( sK4 = k2_pre_topc(sK2,sK4)
    | sK3 = k2_pre_topc(sK1,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f102,f49])).

fof(f102,plain,
    ( v4_pre_topc(sK3,sK1)
    | sK4 = k2_pre_topc(sK2,sK4) ),
    inference(subsumption_resolution,[],[f101,f42])).

fof(f101,plain,
    ( v4_pre_topc(sK3,sK1)
    | sK4 = k2_pre_topc(sK2,sK4)
    | ~ l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f100,f44])).

fof(f100,plain,
    ( v4_pre_topc(sK3,sK1)
    | sK4 = k2_pre_topc(sK2,sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f99,f58])).

fof(f99,plain,
    ( ~ m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | v4_pre_topc(sK3,sK1)
    | sK4 = k2_pre_topc(sK2,sK4) ),
    inference(subsumption_resolution,[],[f98,f41])).

fof(f41,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f98,plain,
    ( v4_pre_topc(sK3,sK1)
    | ~ m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK1)
    | sK4 = k2_pre_topc(sK2,sK4) ),
    inference(subsumption_resolution,[],[f93,f42])).

fof(f93,plain,
    ( v4_pre_topc(sK3,sK1)
    | ~ m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | sK4 = k2_pre_topc(sK2,sK4) ),
    inference(superposition,[],[f57,f91])).

% (24059)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
fof(f57,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).

fof(f149,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k2_pre_topc(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | k2_pre_topc(sK1,X0) = k2_pre_topc(sK1,k2_pre_topc(sK1,X0)) ) ),
    inference(subsumption_resolution,[],[f148,f42])).

fof(f148,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k2_pre_topc(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ l1_pre_topc(sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | k2_pre_topc(sK1,X0) = k2_pre_topc(sK1,k2_pre_topc(sK1,X0)) ) ),
    inference(resolution,[],[f82,f41])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) ) ),
    inference(duplicate_literal_removal,[],[f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(resolution,[],[f49,f57])).

fof(f140,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,X0)),X0)
      | ~ r1_tarski(X0,k2_pre_topc(sK1,k1_tops_1(sK1,X0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | v4_tops_1(X0,sK1) ) ),
    inference(resolution,[],[f55,f42])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
      | ~ r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f233,plain,
    ( ~ v4_tops_1(sK3,sK1)
    | sP0(sK2,sK4) ),
    inference(subsumption_resolution,[],[f47,f232])).

fof(f232,plain,(
    v4_pre_topc(sK3,sK1) ),
    inference(subsumption_resolution,[],[f231,f42])).

fof(f231,plain,
    ( v4_pre_topc(sK3,sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f230,f44])).

fof(f230,plain,
    ( v4_pre_topc(sK3,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f226,f41])).

fof(f226,plain,
    ( v4_pre_topc(sK3,sK1)
    | ~ v2_pre_topc(sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(trivial_inequality_removal,[],[f224])).

fof(f224,plain,
    ( sK3 != sK3
    | v4_pre_topc(sK3,sK1)
    | ~ v2_pre_topc(sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(superposition,[],[f50,f212])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) != X1
      | v4_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f47,plain,
    ( ~ v4_tops_1(sK3,sK1)
    | ~ v4_pre_topc(sK3,sK1)
    | sP0(sK2,sK4) ),
    inference(cnf_transformation,[],[f32])).

fof(f338,plain,(
    ~ sP0(sK2,sK4) ),
    inference(resolution,[],[f334,f40])).

fof(f334,plain,(
    v5_tops_1(sK4,sK2) ),
    inference(subsumption_resolution,[],[f333,f45])).

fof(f333,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | v5_tops_1(sK4,sK2) ),
    inference(trivial_inequality_removal,[],[f330])).

fof(f330,plain,
    ( sK4 != sK4
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | v5_tops_1(sK4,sK2) ),
    inference(superposition,[],[f112,f312])).

fof(f312,plain,(
    sK4 = k2_pre_topc(sK2,k1_tops_1(sK2,sK4)) ),
    inference(subsumption_resolution,[],[f267,f311])).

fof(f311,plain,(
    r1_tarski(sK4,k2_pre_topc(sK2,k1_tops_1(sK2,sK4))) ),
    inference(subsumption_resolution,[],[f310,f43])).

fof(f310,plain,
    ( r1_tarski(sK4,k2_pre_topc(sK2,k1_tops_1(sK2,sK4)))
    | ~ l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f308,f45])).

fof(f308,plain,
    ( r1_tarski(sK4,k2_pre_topc(sK2,k1_tops_1(sK2,sK4)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f306,f54])).

fof(f306,plain,(
    v4_tops_1(sK4,sK2) ),
    inference(resolution,[],[f305,f39])).

fof(f267,plain,
    ( sK4 = k2_pre_topc(sK2,k1_tops_1(sK2,sK4))
    | ~ r1_tarski(sK4,k2_pre_topc(sK2,k1_tops_1(sK2,sK4))) ),
    inference(forward_demodulation,[],[f264,f258])).

fof(f264,plain,
    ( ~ r1_tarski(sK4,k2_pre_topc(sK2,k1_tops_1(sK2,sK4)))
    | k2_pre_topc(sK2,sK4) = k2_pre_topc(sK2,k1_tops_1(sK2,sK4)) ),
    inference(backward_demodulation,[],[f168,f258])).

fof(f168,plain,
    ( ~ r1_tarski(k2_pre_topc(sK2,sK4),k2_pre_topc(sK2,k1_tops_1(sK2,sK4)))
    | k2_pre_topc(sK2,sK4) = k2_pre_topc(sK2,k1_tops_1(sK2,sK4)) ),
    inference(resolution,[],[f166,f61])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:09:44 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.22/0.56  % (24048)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.57  % (24046)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.57  % (24051)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.57  % (24045)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.57  % (24054)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.57  % (24049)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.58  % (24067)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.58  % (24057)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.58  % (24061)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.58  % (24064)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.58  % (24046)Refutation found. Thanks to Tanya!
% 0.22/0.58  % SZS status Theorem for theBenchmark
% 0.22/0.58  % SZS output start Proof for theBenchmark
% 0.22/0.58  fof(f339,plain,(
% 0.22/0.58    $false),
% 0.22/0.58    inference(subsumption_resolution,[],[f338,f305])).
% 0.22/0.58  fof(f305,plain,(
% 0.22/0.58    sP0(sK2,sK4)),
% 0.22/0.58    inference(subsumption_resolution,[],[f233,f304])).
% 0.22/0.58  fof(f304,plain,(
% 0.22/0.58    v4_tops_1(sK3,sK1)),
% 0.22/0.58    inference(subsumption_resolution,[],[f303,f62])).
% 0.22/0.58  % (24050)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.58  fof(f62,plain,(
% 0.22/0.58    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.58    inference(equality_resolution,[],[f60])).
% 0.22/0.58  fof(f60,plain,(
% 0.22/0.58    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.58    inference(cnf_transformation,[],[f37])).
% 0.22/0.58  fof(f37,plain,(
% 0.22/0.58    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.58    inference(flattening,[],[f36])).
% 0.22/0.58  fof(f36,plain,(
% 0.22/0.58    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.58    inference(nnf_transformation,[],[f1])).
% 0.22/0.58  fof(f1,axiom,(
% 0.22/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.58  fof(f303,plain,(
% 0.22/0.58    ~r1_tarski(sK3,sK3) | v4_tops_1(sK3,sK1)),
% 0.22/0.58    inference(backward_demodulation,[],[f229,f298])).
% 0.22/0.58  fof(f298,plain,(
% 0.22/0.58    sK3 = k2_pre_topc(sK1,k1_tops_1(sK1,sK3))),
% 0.22/0.58    inference(subsumption_resolution,[],[f296,f44])).
% 0.22/0.58  fof(f44,plain,(
% 0.22/0.58    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.22/0.58    inference(cnf_transformation,[],[f32])).
% 0.22/0.58  fof(f32,plain,(
% 0.22/0.58    ((((((~v4_tops_1(sK3,sK1) | ~v4_pre_topc(sK3,sK1)) & v5_tops_1(sK3,sK1)) | sP0(sK2,sK4)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1)),
% 0.22/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f25,f31,f30,f29,f28])).
% 0.22/0.58  fof(f28,plain,(
% 0.22/0.58    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v4_pre_topc(X2,X0)) & v5_tops_1(X2,X0)) | sP0(X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,sK1) | ~v4_pre_topc(X2,sK1)) & v5_tops_1(X2,sK1)) | sP0(X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1))),
% 0.22/0.58    introduced(choice_axiom,[])).
% 0.22/0.58  fof(f29,plain,(
% 0.22/0.58    ? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,sK1) | ~v4_pre_topc(X2,sK1)) & v5_tops_1(X2,sK1)) | sP0(X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(X1)) => (? [X2] : (? [X3] : ((((~v4_tops_1(X2,sK1) | ~v4_pre_topc(X2,sK1)) & v5_tops_1(X2,sK1)) | sP0(sK2,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK2))),
% 0.22/0.58    introduced(choice_axiom,[])).
% 0.22/0.58  fof(f30,plain,(
% 0.22/0.58    ? [X2] : (? [X3] : ((((~v4_tops_1(X2,sK1) | ~v4_pre_topc(X2,sK1)) & v5_tops_1(X2,sK1)) | sP0(sK2,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))) => (? [X3] : ((((~v4_tops_1(sK3,sK1) | ~v4_pre_topc(sK3,sK1)) & v5_tops_1(sK3,sK1)) | sP0(sK2,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))))),
% 0.22/0.58    introduced(choice_axiom,[])).
% 0.22/0.58  fof(f31,plain,(
% 0.22/0.58    ? [X3] : ((((~v4_tops_1(sK3,sK1) | ~v4_pre_topc(sK3,sK1)) & v5_tops_1(sK3,sK1)) | sP0(sK2,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) => ((((~v4_tops_1(sK3,sK1) | ~v4_pre_topc(sK3,sK1)) & v5_tops_1(sK3,sK1)) | sP0(sK2,sK4)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))))),
% 0.22/0.58    introduced(choice_axiom,[])).
% 0.22/0.58  fof(f25,plain,(
% 0.22/0.58    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v4_pre_topc(X2,X0)) & v5_tops_1(X2,X0)) | sP0(X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.22/0.58    inference(definition_folding,[],[f12,f24])).
% 0.22/0.58  fof(f24,plain,(
% 0.22/0.58    ! [X1,X3] : ((~v5_tops_1(X3,X1) & v4_tops_1(X3,X1) & v4_pre_topc(X3,X1)) | ~sP0(X1,X3))),
% 0.22/0.58    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.58  fof(f12,plain,(
% 0.22/0.58    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v4_pre_topc(X2,X0)) & v5_tops_1(X2,X0)) | (~v5_tops_1(X3,X1) & v4_tops_1(X3,X1) & v4_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.22/0.58    inference(flattening,[],[f11])).
% 0.22/0.58  fof(f11,plain,(
% 0.22/0.58    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v4_pre_topc(X2,X0)) & v5_tops_1(X2,X0)) | (~v5_tops_1(X3,X1) & (v4_tops_1(X3,X1) & v4_pre_topc(X3,X1)))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.22/0.58    inference(ennf_transformation,[],[f10])).
% 0.22/0.58  fof(f10,negated_conjecture,(
% 0.22/0.58    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v5_tops_1(X2,X0) => (v4_tops_1(X2,X0) & v4_pre_topc(X2,X0))) & ((v4_tops_1(X3,X1) & v4_pre_topc(X3,X1)) => v5_tops_1(X3,X1)))))))),
% 0.22/0.58    inference(negated_conjecture,[],[f9])).
% 0.22/0.58  fof(f9,conjecture,(
% 0.22/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v5_tops_1(X2,X0) => (v4_tops_1(X2,X0) & v4_pre_topc(X2,X0))) & ((v4_tops_1(X3,X1) & v4_pre_topc(X3,X1)) => v5_tops_1(X3,X1)))))))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_tops_1)).
% 0.22/0.58  fof(f296,plain,(
% 0.22/0.58    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) | sK3 = k2_pre_topc(sK1,k1_tops_1(sK1,sK3))),
% 0.22/0.58    inference(resolution,[],[f295,f83])).
% 0.22/0.58  fof(f83,plain,(
% 0.22/0.58    ( ! [X0] : (~v5_tops_1(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | k2_pre_topc(sK1,k1_tops_1(sK1,X0)) = X0) )),
% 0.22/0.58    inference(resolution,[],[f51,f42])).
% 0.22/0.58  fof(f42,plain,(
% 0.22/0.58    l1_pre_topc(sK1)),
% 0.22/0.58    inference(cnf_transformation,[],[f32])).
% 0.22/0.58  fof(f51,plain,(
% 0.22/0.58    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v5_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1) )),
% 0.22/0.58    inference(cnf_transformation,[],[f33])).
% 0.22/0.58  fof(f33,plain,(
% 0.22/0.58    ! [X0] : (! [X1] : (((v5_tops_1(X1,X0) | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1) & (k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 | ~v5_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.58    inference(nnf_transformation,[],[f16])).
% 0.22/0.58  fof(f16,plain,(
% 0.22/0.58    ! [X0] : (! [X1] : ((v5_tops_1(X1,X0) <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.58    inference(ennf_transformation,[],[f5])).
% 0.22/0.58  fof(f5,axiom,(
% 0.22/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v5_tops_1(X1,X0) <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1)))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tops_1)).
% 0.22/0.58  fof(f295,plain,(
% 0.22/0.58    v5_tops_1(sK3,sK1)),
% 0.22/0.58    inference(subsumption_resolution,[],[f294,f113])).
% 0.22/0.58  fof(f113,plain,(
% 0.22/0.58    v5_tops_1(sK3,sK1) | sK3 != k2_pre_topc(sK1,k1_tops_1(sK1,sK3))),
% 0.22/0.58    inference(resolution,[],[f111,f44])).
% 0.22/0.58  fof(f111,plain,(
% 0.22/0.58    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | k2_pre_topc(sK1,k1_tops_1(sK1,X0)) != X0 | v5_tops_1(X0,sK1)) )),
% 0.22/0.58    inference(resolution,[],[f52,f42])).
% 0.22/0.58  fof(f52,plain,(
% 0.22/0.58    ( ! [X0,X1] : (~l1_pre_topc(X0) | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v5_tops_1(X1,X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f33])).
% 0.22/0.58  fof(f294,plain,(
% 0.22/0.58    sK3 = k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) | v5_tops_1(sK3,sK1)),
% 0.22/0.58    inference(resolution,[],[f293,f46])).
% 0.22/0.58  fof(f46,plain,(
% 0.22/0.58    sP0(sK2,sK4) | v5_tops_1(sK3,sK1)),
% 0.22/0.58    inference(cnf_transformation,[],[f32])).
% 0.22/0.58  fof(f293,plain,(
% 0.22/0.58    ~sP0(sK2,sK4) | sK3 = k2_pre_topc(sK1,k1_tops_1(sK1,sK3))),
% 0.22/0.58    inference(resolution,[],[f289,f40])).
% 0.22/0.58  fof(f40,plain,(
% 0.22/0.58    ( ! [X0,X1] : (~v5_tops_1(X1,X0) | ~sP0(X0,X1)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f27])).
% 0.22/0.58  fof(f27,plain,(
% 0.22/0.58    ! [X0,X1] : ((~v5_tops_1(X1,X0) & v4_tops_1(X1,X0) & v4_pre_topc(X1,X0)) | ~sP0(X0,X1))),
% 0.22/0.58    inference(rectify,[],[f26])).
% 0.22/0.58  fof(f26,plain,(
% 0.22/0.58    ! [X1,X3] : ((~v5_tops_1(X3,X1) & v4_tops_1(X3,X1) & v4_pre_topc(X3,X1)) | ~sP0(X1,X3))),
% 0.22/0.58    inference(nnf_transformation,[],[f24])).
% 0.22/0.58  fof(f289,plain,(
% 0.22/0.58    v5_tops_1(sK4,sK2) | sK3 = k2_pre_topc(sK1,k1_tops_1(sK1,sK3))),
% 0.22/0.58    inference(subsumption_resolution,[],[f287,f45])).
% 0.22/0.58  fof(f45,plain,(
% 0.22/0.58    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.22/0.58    inference(cnf_transformation,[],[f32])).
% 0.22/0.58  fof(f287,plain,(
% 0.22/0.58    ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) | v5_tops_1(sK4,sK2) | sK3 = k2_pre_topc(sK1,k1_tops_1(sK1,sK3))),
% 0.22/0.58    inference(trivial_inequality_removal,[],[f284])).
% 0.22/0.58  fof(f284,plain,(
% 0.22/0.58    sK4 != sK4 | ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) | v5_tops_1(sK4,sK2) | sK3 = k2_pre_topc(sK1,k1_tops_1(sK1,sK3))),
% 0.22/0.58    inference(superposition,[],[f112,f266])).
% 0.22/0.58  fof(f266,plain,(
% 0.22/0.58    sK4 = k2_pre_topc(sK2,k1_tops_1(sK2,sK4)) | sK3 = k2_pre_topc(sK1,k1_tops_1(sK1,sK3))),
% 0.22/0.58    inference(subsumption_resolution,[],[f126,f263])).
% 0.22/0.58  fof(f263,plain,(
% 0.22/0.58    r1_tarski(k2_pre_topc(sK2,k1_tops_1(sK2,sK4)),sK4)),
% 0.22/0.58    inference(backward_demodulation,[],[f166,f258])).
% 0.22/0.58  fof(f258,plain,(
% 0.22/0.58    sK4 = k2_pre_topc(sK2,sK4)),
% 0.22/0.58    inference(subsumption_resolution,[],[f257,f43])).
% 0.22/0.58  fof(f43,plain,(
% 0.22/0.58    l1_pre_topc(sK2)),
% 0.22/0.58    inference(cnf_transformation,[],[f32])).
% 0.22/0.58  fof(f257,plain,(
% 0.22/0.58    sK4 = k2_pre_topc(sK2,sK4) | ~l1_pre_topc(sK2)),
% 0.22/0.58    inference(subsumption_resolution,[],[f256,f45])).
% 0.22/0.58  fof(f256,plain,(
% 0.22/0.58    sK4 = k2_pre_topc(sK2,sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2)),
% 0.22/0.58    inference(duplicate_literal_removal,[],[f255])).
% 0.22/0.58  fof(f255,plain,(
% 0.22/0.58    sK4 = k2_pre_topc(sK2,sK4) | sK4 = k2_pre_topc(sK2,sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2)),
% 0.22/0.58    inference(resolution,[],[f248,f49])).
% 0.22/0.58  fof(f49,plain,(
% 0.22/0.58    ( ! [X0,X1] : (~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f15])).
% 0.22/0.58  fof(f15,plain,(
% 0.22/0.58    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.58    inference(flattening,[],[f14])).
% 0.22/0.58  fof(f14,plain,(
% 0.22/0.58    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.58    inference(ennf_transformation,[],[f3])).
% 0.22/0.58  fof(f3,axiom,(
% 0.22/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 0.22/0.58  fof(f248,plain,(
% 0.22/0.58    v4_pre_topc(sK4,sK2) | sK4 = k2_pre_topc(sK2,sK4)),
% 0.22/0.58    inference(resolution,[],[f239,f38])).
% 0.22/0.58  fof(f38,plain,(
% 0.22/0.58    ( ! [X0,X1] : (~sP0(X0,X1) | v4_pre_topc(X1,X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f27])).
% 0.22/0.58  fof(f239,plain,(
% 0.22/0.58    sP0(sK2,sK4) | sK4 = k2_pre_topc(sK2,sK4)),
% 0.22/0.58    inference(resolution,[],[f238,f233])).
% 0.22/0.58  fof(f238,plain,(
% 0.22/0.58    v4_tops_1(sK3,sK1) | sK4 = k2_pre_topc(sK2,sK4)),
% 0.22/0.58    inference(subsumption_resolution,[],[f237,f62])).
% 0.22/0.58  fof(f237,plain,(
% 0.22/0.58    ~r1_tarski(sK3,sK3) | v4_tops_1(sK3,sK1) | sK4 = k2_pre_topc(sK2,sK4)),
% 0.22/0.58    inference(superposition,[],[f229,f91])).
% 0.22/0.58  fof(f91,plain,(
% 0.22/0.58    sK3 = k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) | sK4 = k2_pre_topc(sK2,sK4)),
% 0.22/0.58    inference(subsumption_resolution,[],[f90,f43])).
% 0.22/0.58  fof(f90,plain,(
% 0.22/0.58    sK3 = k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) | sK4 = k2_pre_topc(sK2,sK4) | ~l1_pre_topc(sK2)),
% 0.22/0.58    inference(subsumption_resolution,[],[f89,f45])).
% 0.22/0.58  fof(f89,plain,(
% 0.22/0.58    sK3 = k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) | sK4 = k2_pre_topc(sK2,sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2)),
% 0.22/0.58    inference(resolution,[],[f88,f49])).
% 0.22/0.58  fof(f88,plain,(
% 0.22/0.58    v4_pre_topc(sK4,sK2) | sK3 = k2_pre_topc(sK1,k1_tops_1(sK1,sK3))),
% 0.22/0.58    inference(subsumption_resolution,[],[f86,f44])).
% 0.22/0.58  fof(f86,plain,(
% 0.22/0.58    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) | sK3 = k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) | v4_pre_topc(sK4,sK2)),
% 0.22/0.58    inference(resolution,[],[f83,f64])).
% 0.22/0.58  fof(f64,plain,(
% 0.22/0.58    v5_tops_1(sK3,sK1) | v4_pre_topc(sK4,sK2)),
% 0.22/0.58    inference(resolution,[],[f38,f46])).
% 0.22/0.58  fof(f166,plain,(
% 0.22/0.58    r1_tarski(k2_pre_topc(sK2,k1_tops_1(sK2,sK4)),k2_pre_topc(sK2,sK4))),
% 0.22/0.58    inference(subsumption_resolution,[],[f164,f73])).
% 0.22/0.58  fof(f73,plain,(
% 0.22/0.58    r1_tarski(k1_tops_1(sK2,sK4),sK4)),
% 0.22/0.58    inference(resolution,[],[f70,f45])).
% 0.22/0.58  fof(f70,plain,(
% 0.22/0.58    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) | r1_tarski(k1_tops_1(sK2,X1),X1)) )),
% 0.22/0.58    inference(resolution,[],[f48,f43])).
% 0.22/0.58  fof(f48,plain,(
% 0.22/0.58    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),X1)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f13])).
% 0.22/0.58  fof(f13,plain,(
% 0.22/0.58    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.58    inference(ennf_transformation,[],[f8])).
% 0.22/0.58  fof(f8,axiom,(
% 0.22/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).
% 0.22/0.58  fof(f164,plain,(
% 0.22/0.58    r1_tarski(k2_pre_topc(sK2,k1_tops_1(sK2,sK4)),k2_pre_topc(sK2,sK4)) | ~r1_tarski(k1_tops_1(sK2,sK4),sK4)),
% 0.22/0.58    inference(resolution,[],[f161,f45])).
% 0.22/0.58  fof(f161,plain,(
% 0.22/0.58    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | r1_tarski(k2_pre_topc(sK2,k1_tops_1(sK2,sK4)),k2_pre_topc(sK2,X0)) | ~r1_tarski(k1_tops_1(sK2,sK4),X0)) )),
% 0.22/0.58    inference(resolution,[],[f136,f45])).
% 0.22/0.58  fof(f136,plain,(
% 0.22/0.58    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) | ~r1_tarski(k1_tops_1(sK2,X2),X1) | r1_tarski(k2_pre_topc(sK2,k1_tops_1(sK2,X2)),k2_pre_topc(sK2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f135,f43])).
% 0.22/0.58  fof(f135,plain,(
% 0.22/0.58    ( ! [X2,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) | ~r1_tarski(k1_tops_1(sK2,X2),X1) | r1_tarski(k2_pre_topc(sK2,k1_tops_1(sK2,X2)),k2_pre_topc(sK2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2)) )),
% 0.22/0.58    inference(resolution,[],[f129,f58])).
% 0.22/0.58  fof(f58,plain,(
% 0.22/0.58    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f23])).
% 0.22/0.58  fof(f23,plain,(
% 0.22/0.58    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.58    inference(flattening,[],[f22])).
% 0.22/0.58  fof(f22,plain,(
% 0.22/0.58    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.22/0.58    inference(ennf_transformation,[],[f6])).
% 0.22/0.58  % (24056)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.58  fof(f6,axiom,(
% 0.22/0.58    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).
% 0.22/0.58  fof(f129,plain,(
% 0.22/0.58    ( ! [X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) | ~r1_tarski(X2,X3) | r1_tarski(k2_pre_topc(sK2,X2),k2_pre_topc(sK2,X3))) )),
% 0.22/0.58    inference(resolution,[],[f56,f43])).
% 0.22/0.58  fof(f56,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) )),
% 0.22/0.58    inference(cnf_transformation,[],[f19])).
% 0.22/0.58  fof(f19,plain,(
% 0.22/0.58    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.58    inference(flattening,[],[f18])).
% 0.22/0.58  fof(f18,plain,(
% 0.22/0.58    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.58    inference(ennf_transformation,[],[f2])).
% 0.22/0.58  fof(f2,axiom,(
% 0.22/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))))))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_pre_topc)).
% 0.22/0.58  fof(f126,plain,(
% 0.22/0.58    ~r1_tarski(k2_pre_topc(sK2,k1_tops_1(sK2,sK4)),sK4) | sK3 = k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) | sK4 = k2_pre_topc(sK2,k1_tops_1(sK2,sK4))),
% 0.22/0.58    inference(resolution,[],[f125,f61])).
% 0.22/0.58  fof(f61,plain,(
% 0.22/0.58    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.22/0.58    inference(cnf_transformation,[],[f37])).
% 0.22/0.58  fof(f125,plain,(
% 0.22/0.58    r1_tarski(sK4,k2_pre_topc(sK2,k1_tops_1(sK2,sK4))) | sK3 = k2_pre_topc(sK1,k1_tops_1(sK1,sK3))),
% 0.22/0.58    inference(subsumption_resolution,[],[f124,f43])).
% 0.22/0.58  fof(f124,plain,(
% 0.22/0.58    r1_tarski(sK4,k2_pre_topc(sK2,k1_tops_1(sK2,sK4))) | ~l1_pre_topc(sK2) | sK3 = k2_pre_topc(sK1,k1_tops_1(sK1,sK3))),
% 0.22/0.58    inference(subsumption_resolution,[],[f123,f45])).
% 0.22/0.58  fof(f123,plain,(
% 0.22/0.58    r1_tarski(sK4,k2_pre_topc(sK2,k1_tops_1(sK2,sK4))) | ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2) | sK3 = k2_pre_topc(sK1,k1_tops_1(sK1,sK3))),
% 0.22/0.58    inference(resolution,[],[f54,f87])).
% 0.22/0.58  fof(f87,plain,(
% 0.22/0.58    v4_tops_1(sK4,sK2) | sK3 = k2_pre_topc(sK1,k1_tops_1(sK1,sK3))),
% 0.22/0.58    inference(subsumption_resolution,[],[f85,f44])).
% 0.22/0.58  fof(f85,plain,(
% 0.22/0.58    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) | sK3 = k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) | v4_tops_1(sK4,sK2)),
% 0.22/0.58    inference(resolution,[],[f83,f65])).
% 0.22/0.58  fof(f65,plain,(
% 0.22/0.58    v5_tops_1(sK3,sK1) | v4_tops_1(sK4,sK2)),
% 0.22/0.58    inference(resolution,[],[f39,f46])).
% 0.22/0.58  fof(f39,plain,(
% 0.22/0.58    ( ! [X0,X1] : (~sP0(X0,X1) | v4_tops_1(X1,X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f27])).
% 0.22/0.58  fof(f54,plain,(
% 0.22/0.58    ( ! [X0,X1] : (~v4_tops_1(X1,X0) | r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f35])).
% 0.22/0.58  fof(f35,plain,(
% 0.22/0.58    ! [X0] : (! [X1] : (((v4_tops_1(X1,X0) | ~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) & ((r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) | ~v4_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.58    inference(flattening,[],[f34])).
% 0.22/0.58  fof(f34,plain,(
% 0.22/0.58    ! [X0] : (! [X1] : (((v4_tops_1(X1,X0) | (~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1))) & ((r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) | ~v4_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.58    inference(nnf_transformation,[],[f17])).
% 0.22/0.58  fof(f17,plain,(
% 0.22/0.58    ! [X0] : (! [X1] : ((v4_tops_1(X1,X0) <=> (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.58    inference(ennf_transformation,[],[f4])).
% 0.22/0.58  fof(f4,axiom,(
% 0.22/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_tops_1(X1,X0) <=> (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)))))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_tops_1)).
% 0.22/0.58  fof(f112,plain,(
% 0.22/0.58    ( ! [X1] : (k2_pre_topc(sK2,k1_tops_1(sK2,X1)) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) | v5_tops_1(X1,sK2)) )),
% 0.22/0.58    inference(resolution,[],[f52,f43])).
% 0.22/0.58  fof(f229,plain,(
% 0.22/0.58    ~r1_tarski(sK3,k2_pre_topc(sK1,k1_tops_1(sK1,sK3))) | v4_tops_1(sK3,sK1)),
% 0.22/0.58    inference(subsumption_resolution,[],[f228,f44])).
% 0.22/0.58  fof(f228,plain,(
% 0.22/0.58    ~r1_tarski(sK3,k2_pre_topc(sK1,k1_tops_1(sK1,sK3))) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) | v4_tops_1(sK3,sK1)),
% 0.22/0.58    inference(subsumption_resolution,[],[f223,f71])).
% 0.22/0.58  fof(f71,plain,(
% 0.22/0.58    r1_tarski(k1_tops_1(sK1,sK3),sK3)),
% 0.22/0.58    inference(resolution,[],[f69,f44])).
% 0.22/0.58  fof(f69,plain,(
% 0.22/0.58    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | r1_tarski(k1_tops_1(sK1,X0),X0)) )),
% 0.22/0.58    inference(resolution,[],[f48,f42])).
% 0.22/0.58  fof(f223,plain,(
% 0.22/0.58    ~r1_tarski(k1_tops_1(sK1,sK3),sK3) | ~r1_tarski(sK3,k2_pre_topc(sK1,k1_tops_1(sK1,sK3))) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) | v4_tops_1(sK3,sK1)),
% 0.22/0.58    inference(superposition,[],[f140,f212])).
% 0.22/0.58  fof(f212,plain,(
% 0.22/0.58    sK3 = k2_pre_topc(sK1,sK3)),
% 0.22/0.58    inference(subsumption_resolution,[],[f211,f42])).
% 0.22/0.58  fof(f211,plain,(
% 0.22/0.58    sK3 = k2_pre_topc(sK1,sK3) | ~l1_pre_topc(sK1)),
% 0.22/0.58    inference(subsumption_resolution,[],[f210,f44])).
% 0.22/0.58  fof(f210,plain,(
% 0.22/0.58    sK3 = k2_pre_topc(sK1,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1)),
% 0.22/0.58    inference(resolution,[],[f203,f58])).
% 0.22/0.58  fof(f203,plain,(
% 0.22/0.58    ~m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) | sK3 = k2_pre_topc(sK1,sK3)),
% 0.22/0.58    inference(subsumption_resolution,[],[f201,f44])).
% 0.22/0.58  fof(f201,plain,(
% 0.22/0.58    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) | sK3 = k2_pre_topc(sK1,sK3)),
% 0.22/0.58    inference(duplicate_literal_removal,[],[f197])).
% 0.22/0.58  fof(f197,plain,(
% 0.22/0.58    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) | sK3 = k2_pre_topc(sK1,sK3) | sK3 = k2_pre_topc(sK1,sK3)),
% 0.22/0.58    inference(superposition,[],[f149,f194])).
% 0.22/0.58  fof(f194,plain,(
% 0.22/0.58    sK3 = k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) | sK3 = k2_pre_topc(sK1,sK3)),
% 0.22/0.58    inference(subsumption_resolution,[],[f192,f44])).
% 0.22/0.58  fof(f192,plain,(
% 0.22/0.58    sK3 = k2_pre_topc(sK1,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) | sK3 = k2_pre_topc(sK1,k1_tops_1(sK1,sK3))),
% 0.22/0.58    inference(resolution,[],[f191,f83])).
% 0.22/0.58  fof(f191,plain,(
% 0.22/0.58    v5_tops_1(sK3,sK1) | sK3 = k2_pre_topc(sK1,sK3)),
% 0.22/0.58    inference(subsumption_resolution,[],[f190,f113])).
% 0.22/0.58  fof(f190,plain,(
% 0.22/0.58    sK3 = k2_pre_topc(sK1,sK3) | sK3 = k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) | v5_tops_1(sK3,sK1)),
% 0.22/0.58    inference(resolution,[],[f189,f46])).
% 0.22/0.58  fof(f189,plain,(
% 0.22/0.58    ~sP0(sK2,sK4) | sK3 = k2_pre_topc(sK1,sK3) | sK3 = k2_pre_topc(sK1,k1_tops_1(sK1,sK3))),
% 0.22/0.58    inference(resolution,[],[f185,f40])).
% 0.22/0.58  fof(f185,plain,(
% 0.22/0.58    v5_tops_1(sK4,sK2) | sK3 = k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) | sK3 = k2_pre_topc(sK1,sK3)),
% 0.22/0.58    inference(subsumption_resolution,[],[f182,f45])).
% 0.22/0.58  fof(f182,plain,(
% 0.22/0.58    ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) | v5_tops_1(sK4,sK2) | sK3 = k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) | sK3 = k2_pre_topc(sK1,sK3)),
% 0.22/0.58    inference(trivial_inequality_removal,[],[f179])).
% 0.22/0.58  fof(f179,plain,(
% 0.22/0.58    sK4 != sK4 | ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) | v5_tops_1(sK4,sK2) | sK3 = k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) | sK3 = k2_pre_topc(sK1,sK3)),
% 0.22/0.58    inference(superposition,[],[f112,f170])).
% 0.22/0.58  fof(f170,plain,(
% 0.22/0.58    sK4 = k2_pre_topc(sK2,k1_tops_1(sK2,sK4)) | sK3 = k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) | sK3 = k2_pre_topc(sK1,sK3)),
% 0.22/0.58    inference(resolution,[],[f169,f126])).
% 0.22/0.58  fof(f169,plain,(
% 0.22/0.58    r1_tarski(k2_pre_topc(sK2,k1_tops_1(sK2,sK4)),sK4) | sK3 = k2_pre_topc(sK1,sK3)),
% 0.22/0.58    inference(superposition,[],[f166,f105])).
% 0.22/0.58  fof(f105,plain,(
% 0.22/0.58    sK4 = k2_pre_topc(sK2,sK4) | sK3 = k2_pre_topc(sK1,sK3)),
% 0.22/0.58    inference(subsumption_resolution,[],[f104,f42])).
% 0.22/0.58  fof(f104,plain,(
% 0.22/0.58    sK4 = k2_pre_topc(sK2,sK4) | sK3 = k2_pre_topc(sK1,sK3) | ~l1_pre_topc(sK1)),
% 0.22/0.58    inference(subsumption_resolution,[],[f103,f44])).
% 0.22/0.58  fof(f103,plain,(
% 0.22/0.58    sK4 = k2_pre_topc(sK2,sK4) | sK3 = k2_pre_topc(sK1,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1)),
% 0.22/0.58    inference(resolution,[],[f102,f49])).
% 0.22/0.58  fof(f102,plain,(
% 0.22/0.58    v4_pre_topc(sK3,sK1) | sK4 = k2_pre_topc(sK2,sK4)),
% 0.22/0.58    inference(subsumption_resolution,[],[f101,f42])).
% 0.22/0.58  fof(f101,plain,(
% 0.22/0.58    v4_pre_topc(sK3,sK1) | sK4 = k2_pre_topc(sK2,sK4) | ~l1_pre_topc(sK1)),
% 0.22/0.58    inference(subsumption_resolution,[],[f100,f44])).
% 0.22/0.58  fof(f100,plain,(
% 0.22/0.58    v4_pre_topc(sK3,sK1) | sK4 = k2_pre_topc(sK2,sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1)),
% 0.22/0.58    inference(resolution,[],[f99,f58])).
% 0.22/0.58  fof(f99,plain,(
% 0.22/0.58    ~m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) | v4_pre_topc(sK3,sK1) | sK4 = k2_pre_topc(sK2,sK4)),
% 0.22/0.58    inference(subsumption_resolution,[],[f98,f41])).
% 0.22/0.58  fof(f41,plain,(
% 0.22/0.58    v2_pre_topc(sK1)),
% 0.22/0.58    inference(cnf_transformation,[],[f32])).
% 0.22/0.58  fof(f98,plain,(
% 0.22/0.58    v4_pre_topc(sK3,sK1) | ~m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) | ~v2_pre_topc(sK1) | sK4 = k2_pre_topc(sK2,sK4)),
% 0.22/0.58    inference(subsumption_resolution,[],[f93,f42])).
% 0.22/0.58  fof(f93,plain,(
% 0.22/0.58    v4_pre_topc(sK3,sK1) | ~m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | sK4 = k2_pre_topc(sK2,sK4)),
% 0.22/0.58    inference(superposition,[],[f57,f91])).
% 0.22/0.58  % (24059)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.58  fof(f57,plain,(
% 0.22/0.58    ( ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f21])).
% 0.22/0.58  fof(f21,plain,(
% 0.22/0.58    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.58    inference(flattening,[],[f20])).
% 0.22/0.58  fof(f20,plain,(
% 0.22/0.58    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.58    inference(ennf_transformation,[],[f7])).
% 0.22/0.58  fof(f7,axiom,(
% 0.22/0.58    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_pre_topc(X0,X1),X0))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).
% 0.22/0.58  fof(f149,plain,(
% 0.22/0.58    ( ! [X0] : (~m1_subset_1(k2_pre_topc(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | k2_pre_topc(sK1,X0) = k2_pre_topc(sK1,k2_pre_topc(sK1,X0))) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f148,f42])).
% 0.22/0.58  fof(f148,plain,(
% 0.22/0.58    ( ! [X0] : (~m1_subset_1(k2_pre_topc(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | k2_pre_topc(sK1,X0) = k2_pre_topc(sK1,k2_pre_topc(sK1,X0))) )),
% 0.22/0.58    inference(resolution,[],[f82,f41])).
% 0.22/0.58  fof(f82,plain,(
% 0.22/0.58    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))) )),
% 0.22/0.58    inference(duplicate_literal_removal,[],[f81])).
% 0.22/0.58  fof(f81,plain,(
% 0.22/0.58    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | ~m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.58    inference(resolution,[],[f49,f57])).
% 0.22/0.58  fof(f140,plain,(
% 0.22/0.58    ( ! [X0] : (~r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,X0)),X0) | ~r1_tarski(X0,k2_pre_topc(sK1,k1_tops_1(sK1,X0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | v4_tops_1(X0,sK1)) )),
% 0.22/0.58    inference(resolution,[],[f55,f42])).
% 0.22/0.58  fof(f55,plain,(
% 0.22/0.58    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v4_tops_1(X1,X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f35])).
% 0.22/0.58  fof(f233,plain,(
% 0.22/0.58    ~v4_tops_1(sK3,sK1) | sP0(sK2,sK4)),
% 0.22/0.58    inference(subsumption_resolution,[],[f47,f232])).
% 0.22/0.58  fof(f232,plain,(
% 0.22/0.58    v4_pre_topc(sK3,sK1)),
% 0.22/0.58    inference(subsumption_resolution,[],[f231,f42])).
% 0.22/0.58  fof(f231,plain,(
% 0.22/0.58    v4_pre_topc(sK3,sK1) | ~l1_pre_topc(sK1)),
% 0.22/0.58    inference(subsumption_resolution,[],[f230,f44])).
% 0.22/0.58  fof(f230,plain,(
% 0.22/0.58    v4_pre_topc(sK3,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1)),
% 0.22/0.58    inference(subsumption_resolution,[],[f226,f41])).
% 0.22/0.58  fof(f226,plain,(
% 0.22/0.58    v4_pre_topc(sK3,sK1) | ~v2_pre_topc(sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1)),
% 0.22/0.58    inference(trivial_inequality_removal,[],[f224])).
% 0.22/0.58  fof(f224,plain,(
% 0.22/0.58    sK3 != sK3 | v4_pre_topc(sK3,sK1) | ~v2_pre_topc(sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1)),
% 0.22/0.58    inference(superposition,[],[f50,f212])).
% 0.22/0.58  fof(f50,plain,(
% 0.22/0.58    ( ! [X0,X1] : (k2_pre_topc(X0,X1) != X1 | v4_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f15])).
% 0.22/0.58  fof(f47,plain,(
% 0.22/0.58    ~v4_tops_1(sK3,sK1) | ~v4_pre_topc(sK3,sK1) | sP0(sK2,sK4)),
% 0.22/0.58    inference(cnf_transformation,[],[f32])).
% 0.22/0.58  fof(f338,plain,(
% 0.22/0.58    ~sP0(sK2,sK4)),
% 0.22/0.58    inference(resolution,[],[f334,f40])).
% 0.22/0.58  fof(f334,plain,(
% 0.22/0.58    v5_tops_1(sK4,sK2)),
% 0.22/0.58    inference(subsumption_resolution,[],[f333,f45])).
% 0.22/0.58  fof(f333,plain,(
% 0.22/0.58    ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) | v5_tops_1(sK4,sK2)),
% 0.22/0.58    inference(trivial_inequality_removal,[],[f330])).
% 0.22/0.58  fof(f330,plain,(
% 0.22/0.58    sK4 != sK4 | ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) | v5_tops_1(sK4,sK2)),
% 0.22/0.58    inference(superposition,[],[f112,f312])).
% 0.22/0.58  fof(f312,plain,(
% 0.22/0.58    sK4 = k2_pre_topc(sK2,k1_tops_1(sK2,sK4))),
% 0.22/0.58    inference(subsumption_resolution,[],[f267,f311])).
% 0.22/0.58  fof(f311,plain,(
% 0.22/0.58    r1_tarski(sK4,k2_pre_topc(sK2,k1_tops_1(sK2,sK4)))),
% 0.22/0.58    inference(subsumption_resolution,[],[f310,f43])).
% 0.22/0.58  fof(f310,plain,(
% 0.22/0.58    r1_tarski(sK4,k2_pre_topc(sK2,k1_tops_1(sK2,sK4))) | ~l1_pre_topc(sK2)),
% 0.22/0.58    inference(subsumption_resolution,[],[f308,f45])).
% 0.22/0.58  fof(f308,plain,(
% 0.22/0.58    r1_tarski(sK4,k2_pre_topc(sK2,k1_tops_1(sK2,sK4))) | ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2)),
% 0.22/0.58    inference(resolution,[],[f306,f54])).
% 0.22/0.58  fof(f306,plain,(
% 0.22/0.58    v4_tops_1(sK4,sK2)),
% 0.22/0.58    inference(resolution,[],[f305,f39])).
% 0.22/0.58  fof(f267,plain,(
% 0.22/0.58    sK4 = k2_pre_topc(sK2,k1_tops_1(sK2,sK4)) | ~r1_tarski(sK4,k2_pre_topc(sK2,k1_tops_1(sK2,sK4)))),
% 0.22/0.58    inference(forward_demodulation,[],[f264,f258])).
% 0.22/0.58  fof(f264,plain,(
% 0.22/0.58    ~r1_tarski(sK4,k2_pre_topc(sK2,k1_tops_1(sK2,sK4))) | k2_pre_topc(sK2,sK4) = k2_pre_topc(sK2,k1_tops_1(sK2,sK4))),
% 0.22/0.58    inference(backward_demodulation,[],[f168,f258])).
% 0.22/0.58  fof(f168,plain,(
% 0.22/0.58    ~r1_tarski(k2_pre_topc(sK2,sK4),k2_pre_topc(sK2,k1_tops_1(sK2,sK4))) | k2_pre_topc(sK2,sK4) = k2_pre_topc(sK2,k1_tops_1(sK2,sK4))),
% 0.22/0.58    inference(resolution,[],[f166,f61])).
% 0.22/0.58  % SZS output end Proof for theBenchmark
% 0.22/0.58  % (24046)------------------------------
% 0.22/0.58  % (24046)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (24046)Termination reason: Refutation
% 0.22/0.58  
% 0.22/0.58  % (24046)Memory used [KB]: 6268
% 0.22/0.58  % (24046)Time elapsed: 0.134 s
% 0.22/0.58  % (24046)------------------------------
% 0.22/0.58  % (24046)------------------------------
% 0.22/0.59  % (24047)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.59  % (24042)Success in time 0.212 s
%------------------------------------------------------------------------------
