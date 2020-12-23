%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:18 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   97 (1770 expanded)
%              Number of leaves         :   13 ( 671 expanded)
%              Depth                    :   27
%              Number of atoms          :  307 (12058 expanded)
%              Number of equality atoms :   82 (3164 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f253,plain,(
    $false ),
    inference(global_subsumption,[],[f92,f242,f252])).

fof(f252,plain,(
    v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK2),sK0) ),
    inference(subsumption_resolution,[],[f251,f32])).

fof(f32,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ( ( ~ v3_pre_topc(sK2,sK0)
        & sK2 = k1_tops_1(sK0,sK2) )
      | ( sK3 != k1_tops_1(sK1,sK3)
        & v3_pre_topc(sK3,sK1) ) )
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f26,f25,f24,f23])).

fof(f23,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ( ~ v3_pre_topc(X2,X0)
                        & k1_tops_1(X0,X2) = X2 )
                      | ( k1_tops_1(X1,X3) != X3
                        & v3_pre_topc(X3,X1) ) )
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & l1_pre_topc(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ~ v3_pre_topc(X2,sK0)
                      & k1_tops_1(sK0,X2) = X2 )
                    | ( k1_tops_1(X1,X3) != X3
                      & v3_pre_topc(X3,X1) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ( ~ v3_pre_topc(X2,sK0)
                    & k1_tops_1(sK0,X2) = X2 )
                  | ( k1_tops_1(X1,X3) != X3
                    & v3_pre_topc(X3,X1) ) )
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & l1_pre_topc(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ( ~ v3_pre_topc(X2,sK0)
                  & k1_tops_1(sK0,X2) = X2 )
                | ( k1_tops_1(sK1,X3) != X3
                  & v3_pre_topc(X3,sK1) ) )
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ( ~ v3_pre_topc(X2,sK0)
                & k1_tops_1(sK0,X2) = X2 )
              | ( k1_tops_1(sK1,X3) != X3
                & v3_pre_topc(X3,sK1) ) )
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X3] :
          ( ( ( ~ v3_pre_topc(sK2,sK0)
              & sK2 = k1_tops_1(sK0,sK2) )
            | ( k1_tops_1(sK1,X3) != X3
              & v3_pre_topc(X3,sK1) ) )
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X3] :
        ( ( ( ~ v3_pre_topc(sK2,sK0)
            & sK2 = k1_tops_1(sK0,sK2) )
          | ( k1_tops_1(sK1,X3) != X3
            & v3_pre_topc(X3,sK1) ) )
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
   => ( ( ( ~ v3_pre_topc(sK2,sK0)
          & sK2 = k1_tops_1(sK0,sK2) )
        | ( sK3 != k1_tops_1(sK1,sK3)
          & v3_pre_topc(sK3,sK1) ) )
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ~ v3_pre_topc(X2,X0)
                      & k1_tops_1(X0,X2) = X2 )
                    | ( k1_tops_1(X1,X3) != X3
                      & v3_pre_topc(X3,X1) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ~ v3_pre_topc(X2,X0)
                      & k1_tops_1(X0,X2) = X2 )
                    | ( k1_tops_1(X1,X3) != X3
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
                   => ( ( k1_tops_1(X0,X2) = X2
                       => v3_pre_topc(X2,X0) )
                      & ( v3_pre_topc(X3,X1)
                       => k1_tops_1(X1,X3) = X3 ) ) ) ) ) ) ),
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
                 => ( ( k1_tops_1(X0,X2) = X2
                     => v3_pre_topc(X2,X0) )
                    & ( v3_pre_topc(X3,X1)
                     => k1_tops_1(X1,X3) = X3 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).

fof(f251,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK2),sK0) ),
    inference(forward_demodulation,[],[f250,f244])).

fof(f244,plain,(
    sK2 = k1_tops_1(sK0,sK2) ),
    inference(subsumption_resolution,[],[f35,f242])).

fof(f35,plain,
    ( sK3 != k1_tops_1(sK1,sK3)
    | sK2 = k1_tops_1(sK0,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f250,plain,
    ( v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK2),sK0)
    | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f248,f65])).

fof(f65,plain,(
    k3_subset_1(u1_struct_0(sK0),sK2) = k4_xboole_0(u1_struct_0(sK0),sK2) ),
    inference(superposition,[],[f63,f54])).

fof(f54,plain,(
    sK2 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2)) ),
    inference(subsumption_resolution,[],[f51,f32])).

fof(f51,plain,
    ( sK2 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f48,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f48,plain,(
    sK2 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2)) ),
    inference(resolution,[],[f45,f32])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f63,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k3_subset_1(X0,k3_subset_1(X0,k4_xboole_0(X0,X1))) ),
    inference(resolution,[],[f50,f43])).

fof(f43,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(resolution,[],[f45,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f248,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK2),sK0)
    | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f202,f244])).

fof(f202,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK2)),sK0) ),
    inference(resolution,[],[f79,f32])).

fof(f79,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X0)),sK0)
      | ~ m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f78,f29])).

fof(f29,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f78,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X0)),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f77,f30])).

fof(f30,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f77,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X0)),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(resolution,[],[f75,f46])).

fof(f46,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f75,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0) ) ),
    inference(resolution,[],[f41,f30])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_tops_1)).

fof(f242,plain,(
    sK3 = k1_tops_1(sK1,sK3) ),
    inference(forward_demodulation,[],[f240,f58])).

fof(f58,plain,(
    sK3 = k3_subset_1(u1_struct_0(sK1),k4_xboole_0(u1_struct_0(sK1),sK3)) ),
    inference(subsumption_resolution,[],[f55,f33])).

fof(f33,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f27])).

fof(f55,plain,
    ( sK3 = k3_subset_1(u1_struct_0(sK1),k4_xboole_0(u1_struct_0(sK1),sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(superposition,[],[f49,f44])).

fof(f49,plain,(
    sK3 = k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),sK3)) ),
    inference(resolution,[],[f45,f33])).

fof(f240,plain,(
    k1_tops_1(sK1,sK3) = k3_subset_1(u1_struct_0(sK1),k4_xboole_0(u1_struct_0(sK1),sK3)) ),
    inference(backward_demodulation,[],[f159,f239])).

fof(f239,plain,(
    k4_xboole_0(u1_struct_0(sK1),sK3) = k2_pre_topc(sK1,k4_xboole_0(u1_struct_0(sK1),sK3)) ),
    inference(subsumption_resolution,[],[f238,f233])).

fof(f233,plain,
    ( ~ v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK2),sK0)
    | k4_xboole_0(u1_struct_0(sK1),sK3) = k2_pre_topc(sK1,k4_xboole_0(u1_struct_0(sK1),sK3)) ),
    inference(forward_demodulation,[],[f232,f65])).

fof(f232,plain,
    ( k4_xboole_0(u1_struct_0(sK1),sK3) = k2_pre_topc(sK1,k4_xboole_0(u1_struct_0(sK1),sK3))
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK2),sK0) ),
    inference(subsumption_resolution,[],[f231,f32])).

fof(f231,plain,
    ( k4_xboole_0(u1_struct_0(sK1),sK3) = k2_pre_topc(sK1,k4_xboole_0(u1_struct_0(sK1),sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK2),sK0) ),
    inference(resolution,[],[f227,f86])).

fof(f86,plain,(
    ! [X0] :
      ( v3_pre_topc(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0) ) ),
    inference(resolution,[],[f42,f30])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f227,plain,
    ( ~ v3_pre_topc(sK2,sK0)
    | k4_xboole_0(u1_struct_0(sK1),sK3) = k2_pre_topc(sK1,k4_xboole_0(u1_struct_0(sK1),sK3)) ),
    inference(resolution,[],[f225,f36])).

fof(f36,plain,
    ( v3_pre_topc(sK3,sK1)
    | ~ v3_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f225,plain,
    ( ~ v3_pre_topc(sK3,sK1)
    | k4_xboole_0(u1_struct_0(sK1),sK3) = k2_pre_topc(sK1,k4_xboole_0(u1_struct_0(sK1),sK3)) ),
    inference(subsumption_resolution,[],[f224,f43])).

fof(f224,plain,
    ( k4_xboole_0(u1_struct_0(sK1),sK3) = k2_pre_topc(sK1,k4_xboole_0(u1_struct_0(sK1),sK3))
    | ~ v3_pre_topc(sK3,sK1)
    | ~ r1_tarski(k4_xboole_0(u1_struct_0(sK1),sK3),u1_struct_0(sK1)) ),
    inference(resolution,[],[f84,f47])).

fof(f84,plain,
    ( ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK1),sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | k4_xboole_0(u1_struct_0(sK1),sK3) = k2_pre_topc(sK1,k4_xboole_0(u1_struct_0(sK1),sK3))
    | ~ v3_pre_topc(sK3,sK1) ),
    inference(subsumption_resolution,[],[f83,f31])).

fof(f31,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f83,plain,
    ( ~ v3_pre_topc(sK3,sK1)
    | k4_xboole_0(u1_struct_0(sK1),sK3) = k2_pre_topc(sK1,k4_xboole_0(u1_struct_0(sK1),sK3))
    | ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK1),sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f82,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f82,plain,
    ( v4_pre_topc(k4_xboole_0(u1_struct_0(sK1),sK3),sK1)
    | ~ v3_pre_topc(sK3,sK1) ),
    inference(forward_demodulation,[],[f80,f66])).

fof(f66,plain,(
    k3_subset_1(u1_struct_0(sK1),sK3) = k4_xboole_0(u1_struct_0(sK1),sK3) ),
    inference(superposition,[],[f63,f58])).

fof(f80,plain,
    ( ~ v3_pre_topc(sK3,sK1)
    | v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK3),sK1) ),
    inference(resolution,[],[f76,f33])).

fof(f76,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v3_pre_topc(X1,sK1)
      | v4_pre_topc(k3_subset_1(u1_struct_0(sK1),X1),sK1) ) ),
    inference(resolution,[],[f41,f31])).

fof(f238,plain,
    ( v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK2),sK0)
    | k4_xboole_0(u1_struct_0(sK1),sK3) = k2_pre_topc(sK1,k4_xboole_0(u1_struct_0(sK1),sK3)) ),
    inference(forward_demodulation,[],[f237,f65])).

fof(f237,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK2),sK0)
    | k4_xboole_0(u1_struct_0(sK1),sK3) = k2_pre_topc(sK1,k4_xboole_0(u1_struct_0(sK1),sK3)) ),
    inference(subsumption_resolution,[],[f234,f97])).

fof(f97,plain,(
    r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(superposition,[],[f43,f95])).

fof(f95,plain,(
    sK2 = k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2)) ),
    inference(subsumption_resolution,[],[f94,f43])).

fof(f94,plain,
    ( sK2 = k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2))
    | ~ r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK2),u1_struct_0(sK0)) ),
    inference(resolution,[],[f59,f47])).

fof(f59,plain,
    ( ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | sK2 = k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2)) ),
    inference(superposition,[],[f54,f44])).

fof(f234,plain,
    ( ~ r1_tarski(sK2,u1_struct_0(sK0))
    | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK2),sK0)
    | k4_xboole_0(u1_struct_0(sK1),sK3) = k2_pre_topc(sK1,k4_xboole_0(u1_struct_0(sK1),sK3)) ),
    inference(superposition,[],[f204,f226])).

fof(f226,plain,
    ( sK2 = k1_tops_1(sK0,sK2)
    | k4_xboole_0(u1_struct_0(sK1),sK3) = k2_pre_topc(sK1,k4_xboole_0(u1_struct_0(sK1),sK3)) ),
    inference(resolution,[],[f225,f34])).

fof(f34,plain,
    ( v3_pre_topc(sK3,sK1)
    | sK2 = k1_tops_1(sK0,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f204,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))
    | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK2)),sK0) ),
    inference(resolution,[],[f202,f47])).

fof(f159,plain,(
    k1_tops_1(sK1,sK3) = k3_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,k4_xboole_0(u1_struct_0(sK1),sK3))) ),
    inference(forward_demodulation,[],[f157,f66])).

fof(f157,plain,(
    k1_tops_1(sK1,sK3) = k3_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK3))) ),
    inference(resolution,[],[f147,f33])).

fof(f147,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | k1_tops_1(sK1,X1) = k3_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),X1))) ) ),
    inference(resolution,[],[f38,f31])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

fof(f92,plain,
    ( ~ v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK2),sK0)
    | sK3 != k1_tops_1(sK1,sK3) ),
    inference(forward_demodulation,[],[f91,f65])).

fof(f91,plain,
    ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK2),sK0)
    | sK3 != k1_tops_1(sK1,sK3) ),
    inference(subsumption_resolution,[],[f88,f32])).

fof(f88,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK2),sK0)
    | sK3 != k1_tops_1(sK1,sK3) ),
    inference(resolution,[],[f86,f37])).

fof(f37,plain,
    ( ~ v3_pre_topc(sK2,sK0)
    | sK3 != k1_tops_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:30:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.42  % (19005)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.43  % (19005)Refutation not found, incomplete strategy% (19005)------------------------------
% 0.21/0.43  % (19005)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (19018)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.21/0.43  % (19005)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.43  
% 0.21/0.43  % (19005)Memory used [KB]: 10746
% 0.21/0.43  % (19005)Time elapsed: 0.038 s
% 0.21/0.43  % (19005)------------------------------
% 0.21/0.43  % (19005)------------------------------
% 0.21/0.45  % (19018)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.45  % SZS output start Proof for theBenchmark
% 0.21/0.45  fof(f253,plain,(
% 0.21/0.45    $false),
% 0.21/0.45    inference(global_subsumption,[],[f92,f242,f252])).
% 0.21/0.45  fof(f252,plain,(
% 0.21/0.45    v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK2),sK0)),
% 0.21/0.45    inference(subsumption_resolution,[],[f251,f32])).
% 0.21/0.45  fof(f32,plain,(
% 0.21/0.45    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.45    inference(cnf_transformation,[],[f27])).
% 0.21/0.45  fof(f27,plain,(
% 0.21/0.45    (((((~v3_pre_topc(sK2,sK0) & sK2 = k1_tops_1(sK0,sK2)) | (sK3 != k1_tops_1(sK1,sK3) & v3_pre_topc(sK3,sK1))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f26,f25,f24,f23])).
% 0.21/0.45  fof(f23,plain,(
% 0.21/0.45    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~v3_pre_topc(X2,X0) & k1_tops_1(X0,X2) = X2) | (k1_tops_1(X1,X3) != X3 & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : (((~v3_pre_topc(X2,sK0) & k1_tops_1(sK0,X2) = X2) | (k1_tops_1(X1,X3) != X3 & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f24,plain,(
% 0.21/0.45    ? [X1] : (? [X2] : (? [X3] : (((~v3_pre_topc(X2,sK0) & k1_tops_1(sK0,X2) = X2) | (k1_tops_1(X1,X3) != X3 & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(X1)) => (? [X2] : (? [X3] : (((~v3_pre_topc(X2,sK0) & k1_tops_1(sK0,X2) = X2) | (k1_tops_1(sK1,X3) != X3 & v3_pre_topc(X3,sK1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK1))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f25,plain,(
% 0.21/0.45    ? [X2] : (? [X3] : (((~v3_pre_topc(X2,sK0) & k1_tops_1(sK0,X2) = X2) | (k1_tops_1(sK1,X3) != X3 & v3_pre_topc(X3,sK1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X3] : (((~v3_pre_topc(sK2,sK0) & sK2 = k1_tops_1(sK0,sK2)) | (k1_tops_1(sK1,X3) != X3 & v3_pre_topc(X3,sK1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f26,plain,(
% 0.21/0.45    ? [X3] : (((~v3_pre_topc(sK2,sK0) & sK2 = k1_tops_1(sK0,sK2)) | (k1_tops_1(sK1,X3) != X3 & v3_pre_topc(X3,sK1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) => (((~v3_pre_topc(sK2,sK0) & sK2 = k1_tops_1(sK0,sK2)) | (sK3 != k1_tops_1(sK1,sK3) & v3_pre_topc(sK3,sK1))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f13,plain,(
% 0.21/0.45    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~v3_pre_topc(X2,X0) & k1_tops_1(X0,X2) = X2) | (k1_tops_1(X1,X3) != X3 & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.45    inference(flattening,[],[f12])).
% 0.21/0.45  fof(f12,plain,(
% 0.21/0.45    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~v3_pre_topc(X2,X0) & k1_tops_1(X0,X2) = X2) | (k1_tops_1(X1,X3) != X3 & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.21/0.45    inference(ennf_transformation,[],[f10])).
% 0.21/0.45  fof(f10,negated_conjecture,(
% 0.21/0.45    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 0.21/0.45    inference(negated_conjecture,[],[f9])).
% 0.21/0.45  fof(f9,conjecture,(
% 0.21/0.45    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).
% 0.21/0.45  fof(f251,plain,(
% 0.21/0.45    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK2),sK0)),
% 0.21/0.45    inference(forward_demodulation,[],[f250,f244])).
% 0.21/0.45  fof(f244,plain,(
% 0.21/0.45    sK2 = k1_tops_1(sK0,sK2)),
% 0.21/0.45    inference(subsumption_resolution,[],[f35,f242])).
% 0.21/0.45  fof(f35,plain,(
% 0.21/0.45    sK3 != k1_tops_1(sK1,sK3) | sK2 = k1_tops_1(sK0,sK2)),
% 0.21/0.45    inference(cnf_transformation,[],[f27])).
% 0.21/0.45  fof(f250,plain,(
% 0.21/0.45    v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK2),sK0) | ~m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.45    inference(forward_demodulation,[],[f248,f65])).
% 0.21/0.45  fof(f65,plain,(
% 0.21/0.45    k3_subset_1(u1_struct_0(sK0),sK2) = k4_xboole_0(u1_struct_0(sK0),sK2)),
% 0.21/0.45    inference(superposition,[],[f63,f54])).
% 0.21/0.45  fof(f54,plain,(
% 0.21/0.45    sK2 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2))),
% 0.21/0.45    inference(subsumption_resolution,[],[f51,f32])).
% 0.21/0.45  fof(f51,plain,(
% 0.21/0.45    sK2 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.45    inference(superposition,[],[f48,f44])).
% 0.21/0.45  fof(f44,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f18])).
% 0.21/0.45  fof(f18,plain,(
% 0.21/0.45    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.45    inference(ennf_transformation,[],[f2])).
% 0.21/0.45  fof(f2,axiom,(
% 0.21/0.45    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.21/0.45  fof(f48,plain,(
% 0.21/0.45    sK2 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2))),
% 0.21/0.45    inference(resolution,[],[f45,f32])).
% 0.21/0.45  fof(f45,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 0.21/0.45    inference(cnf_transformation,[],[f19])).
% 0.21/0.45  fof(f19,plain,(
% 0.21/0.45    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.45    inference(ennf_transformation,[],[f3])).
% 0.21/0.45  fof(f3,axiom,(
% 0.21/0.45    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.21/0.45  fof(f63,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,k3_subset_1(X0,k4_xboole_0(X0,X1)))) )),
% 0.21/0.45    inference(resolution,[],[f50,f43])).
% 0.21/0.45  fof(f43,plain,(
% 0.21/0.45    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f1])).
% 0.21/0.45  fof(f1,axiom,(
% 0.21/0.45    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.21/0.45  fof(f50,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~r1_tarski(X1,X0) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 0.21/0.45    inference(resolution,[],[f45,f47])).
% 0.21/0.45  fof(f47,plain,(
% 0.21/0.45    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f22])).
% 0.21/0.45  fof(f22,plain,(
% 0.21/0.45    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.45    inference(ennf_transformation,[],[f11])).
% 0.21/0.45  fof(f11,plain,(
% 0.21/0.45    ! [X0,X1] : (r1_tarski(X0,X1) => m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.21/0.45    inference(unused_predicate_definition_removal,[],[f4])).
% 0.21/0.45  fof(f4,axiom,(
% 0.21/0.45    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.45  fof(f248,plain,(
% 0.21/0.45    v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK2),sK0) | ~m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.45    inference(backward_demodulation,[],[f202,f244])).
% 0.21/0.45  fof(f202,plain,(
% 0.21/0.45    ~m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK2)),sK0)),
% 0.21/0.45    inference(resolution,[],[f79,f32])).
% 0.21/0.45  fof(f79,plain,(
% 0.21/0.45    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X0)),sK0) | ~m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.21/0.45    inference(subsumption_resolution,[],[f78,f29])).
% 0.21/0.45  fof(f29,plain,(
% 0.21/0.45    v2_pre_topc(sK0)),
% 0.21/0.45    inference(cnf_transformation,[],[f27])).
% 0.21/0.45  fof(f78,plain,(
% 0.21/0.45    ( ! [X0] : (~m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X0)),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0)) )),
% 0.21/0.45    inference(subsumption_resolution,[],[f77,f30])).
% 0.21/0.45  fof(f30,plain,(
% 0.21/0.45    l1_pre_topc(sK0)),
% 0.21/0.45    inference(cnf_transformation,[],[f27])).
% 0.21/0.45  fof(f77,plain,(
% 0.21/0.45    ( ! [X0] : (~m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X0)),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.21/0.45    inference(resolution,[],[f75,f46])).
% 0.21/0.45  fof(f46,plain,(
% 0.21/0.45    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f21])).
% 0.21/0.45  fof(f21,plain,(
% 0.21/0.45    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.45    inference(flattening,[],[f20])).
% 0.21/0.45  fof(f20,plain,(
% 0.21/0.45    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.45    inference(ennf_transformation,[],[f7])).
% 0.21/0.45  fof(f7,axiom,(
% 0.21/0.45    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).
% 0.21/0.45  fof(f75,plain,(
% 0.21/0.45    ( ! [X0] : (~v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)) )),
% 0.21/0.45    inference(resolution,[],[f41,f30])).
% 0.21/0.45  fof(f41,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f28])).
% 0.21/0.45  fof(f28,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.45    inference(nnf_transformation,[],[f17])).
% 0.21/0.45  fof(f17,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.45    inference(ennf_transformation,[],[f8])).
% 0.21/0.45  fof(f8,axiom,(
% 0.21/0.45    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_tops_1)).
% 0.21/0.45  fof(f242,plain,(
% 0.21/0.45    sK3 = k1_tops_1(sK1,sK3)),
% 0.21/0.45    inference(forward_demodulation,[],[f240,f58])).
% 0.21/0.45  fof(f58,plain,(
% 0.21/0.45    sK3 = k3_subset_1(u1_struct_0(sK1),k4_xboole_0(u1_struct_0(sK1),sK3))),
% 0.21/0.45    inference(subsumption_resolution,[],[f55,f33])).
% 0.21/0.45  fof(f33,plain,(
% 0.21/0.45    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.21/0.45    inference(cnf_transformation,[],[f27])).
% 0.21/0.45  fof(f55,plain,(
% 0.21/0.45    sK3 = k3_subset_1(u1_struct_0(sK1),k4_xboole_0(u1_struct_0(sK1),sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.21/0.45    inference(superposition,[],[f49,f44])).
% 0.21/0.45  fof(f49,plain,(
% 0.21/0.45    sK3 = k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),sK3))),
% 0.21/0.45    inference(resolution,[],[f45,f33])).
% 0.21/0.45  fof(f240,plain,(
% 0.21/0.45    k1_tops_1(sK1,sK3) = k3_subset_1(u1_struct_0(sK1),k4_xboole_0(u1_struct_0(sK1),sK3))),
% 0.21/0.45    inference(backward_demodulation,[],[f159,f239])).
% 0.21/0.45  fof(f239,plain,(
% 0.21/0.45    k4_xboole_0(u1_struct_0(sK1),sK3) = k2_pre_topc(sK1,k4_xboole_0(u1_struct_0(sK1),sK3))),
% 0.21/0.45    inference(subsumption_resolution,[],[f238,f233])).
% 0.21/0.45  fof(f233,plain,(
% 0.21/0.45    ~v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK2),sK0) | k4_xboole_0(u1_struct_0(sK1),sK3) = k2_pre_topc(sK1,k4_xboole_0(u1_struct_0(sK1),sK3))),
% 0.21/0.45    inference(forward_demodulation,[],[f232,f65])).
% 0.21/0.45  fof(f232,plain,(
% 0.21/0.45    k4_xboole_0(u1_struct_0(sK1),sK3) = k2_pre_topc(sK1,k4_xboole_0(u1_struct_0(sK1),sK3)) | ~v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK2),sK0)),
% 0.21/0.45    inference(subsumption_resolution,[],[f231,f32])).
% 0.21/0.45  fof(f231,plain,(
% 0.21/0.45    k4_xboole_0(u1_struct_0(sK1),sK3) = k2_pre_topc(sK1,k4_xboole_0(u1_struct_0(sK1),sK3)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK2),sK0)),
% 0.21/0.45    inference(resolution,[],[f227,f86])).
% 0.21/0.45  fof(f86,plain,(
% 0.21/0.45    ( ! [X0] : (v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)) )),
% 0.21/0.45    inference(resolution,[],[f42,f30])).
% 0.21/0.45  fof(f42,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(X1,X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f28])).
% 0.21/0.45  fof(f227,plain,(
% 0.21/0.45    ~v3_pre_topc(sK2,sK0) | k4_xboole_0(u1_struct_0(sK1),sK3) = k2_pre_topc(sK1,k4_xboole_0(u1_struct_0(sK1),sK3))),
% 0.21/0.45    inference(resolution,[],[f225,f36])).
% 0.21/0.45  fof(f36,plain,(
% 0.21/0.45    v3_pre_topc(sK3,sK1) | ~v3_pre_topc(sK2,sK0)),
% 0.21/0.45    inference(cnf_transformation,[],[f27])).
% 0.21/0.45  fof(f225,plain,(
% 0.21/0.45    ~v3_pre_topc(sK3,sK1) | k4_xboole_0(u1_struct_0(sK1),sK3) = k2_pre_topc(sK1,k4_xboole_0(u1_struct_0(sK1),sK3))),
% 0.21/0.45    inference(subsumption_resolution,[],[f224,f43])).
% 0.21/0.45  fof(f224,plain,(
% 0.21/0.45    k4_xboole_0(u1_struct_0(sK1),sK3) = k2_pre_topc(sK1,k4_xboole_0(u1_struct_0(sK1),sK3)) | ~v3_pre_topc(sK3,sK1) | ~r1_tarski(k4_xboole_0(u1_struct_0(sK1),sK3),u1_struct_0(sK1))),
% 0.21/0.45    inference(resolution,[],[f84,f47])).
% 0.21/0.45  fof(f84,plain,(
% 0.21/0.45    ~m1_subset_1(k4_xboole_0(u1_struct_0(sK1),sK3),k1_zfmisc_1(u1_struct_0(sK1))) | k4_xboole_0(u1_struct_0(sK1),sK3) = k2_pre_topc(sK1,k4_xboole_0(u1_struct_0(sK1),sK3)) | ~v3_pre_topc(sK3,sK1)),
% 0.21/0.45    inference(subsumption_resolution,[],[f83,f31])).
% 0.21/0.45  fof(f31,plain,(
% 0.21/0.45    l1_pre_topc(sK1)),
% 0.21/0.45    inference(cnf_transformation,[],[f27])).
% 0.21/0.45  fof(f83,plain,(
% 0.21/0.45    ~v3_pre_topc(sK3,sK1) | k4_xboole_0(u1_struct_0(sK1),sK3) = k2_pre_topc(sK1,k4_xboole_0(u1_struct_0(sK1),sK3)) | ~m1_subset_1(k4_xboole_0(u1_struct_0(sK1),sK3),k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1)),
% 0.21/0.45    inference(resolution,[],[f82,f39])).
% 0.21/0.45  fof(f39,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f16])).
% 0.21/0.45  fof(f16,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.45    inference(flattening,[],[f15])).
% 0.21/0.45  fof(f15,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.45    inference(ennf_transformation,[],[f5])).
% 0.21/0.45  fof(f5,axiom,(
% 0.21/0.45    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 0.21/0.45  fof(f82,plain,(
% 0.21/0.45    v4_pre_topc(k4_xboole_0(u1_struct_0(sK1),sK3),sK1) | ~v3_pre_topc(sK3,sK1)),
% 0.21/0.45    inference(forward_demodulation,[],[f80,f66])).
% 0.21/0.45  fof(f66,plain,(
% 0.21/0.45    k3_subset_1(u1_struct_0(sK1),sK3) = k4_xboole_0(u1_struct_0(sK1),sK3)),
% 0.21/0.45    inference(superposition,[],[f63,f58])).
% 0.21/0.45  fof(f80,plain,(
% 0.21/0.45    ~v3_pre_topc(sK3,sK1) | v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK3),sK1)),
% 0.21/0.45    inference(resolution,[],[f76,f33])).
% 0.21/0.45  fof(f76,plain,(
% 0.21/0.45    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | ~v3_pre_topc(X1,sK1) | v4_pre_topc(k3_subset_1(u1_struct_0(sK1),X1),sK1)) )),
% 0.21/0.45    inference(resolution,[],[f41,f31])).
% 0.21/0.45  fof(f238,plain,(
% 0.21/0.45    v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK2),sK0) | k4_xboole_0(u1_struct_0(sK1),sK3) = k2_pre_topc(sK1,k4_xboole_0(u1_struct_0(sK1),sK3))),
% 0.21/0.45    inference(forward_demodulation,[],[f237,f65])).
% 0.21/0.45  fof(f237,plain,(
% 0.21/0.45    v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK2),sK0) | k4_xboole_0(u1_struct_0(sK1),sK3) = k2_pre_topc(sK1,k4_xboole_0(u1_struct_0(sK1),sK3))),
% 0.21/0.45    inference(subsumption_resolution,[],[f234,f97])).
% 0.21/0.45  fof(f97,plain,(
% 0.21/0.45    r1_tarski(sK2,u1_struct_0(sK0))),
% 0.21/0.45    inference(superposition,[],[f43,f95])).
% 0.21/0.45  fof(f95,plain,(
% 0.21/0.45    sK2 = k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2))),
% 0.21/0.45    inference(subsumption_resolution,[],[f94,f43])).
% 0.21/0.45  fof(f94,plain,(
% 0.21/0.45    sK2 = k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2)) | ~r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK2),u1_struct_0(sK0))),
% 0.21/0.45    inference(resolution,[],[f59,f47])).
% 0.21/0.45  fof(f59,plain,(
% 0.21/0.45    ~m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) | sK2 = k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2))),
% 0.21/0.45    inference(superposition,[],[f54,f44])).
% 0.21/0.45  fof(f234,plain,(
% 0.21/0.45    ~r1_tarski(sK2,u1_struct_0(sK0)) | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK2),sK0) | k4_xboole_0(u1_struct_0(sK1),sK3) = k2_pre_topc(sK1,k4_xboole_0(u1_struct_0(sK1),sK3))),
% 0.21/0.45    inference(superposition,[],[f204,f226])).
% 0.21/0.45  fof(f226,plain,(
% 0.21/0.45    sK2 = k1_tops_1(sK0,sK2) | k4_xboole_0(u1_struct_0(sK1),sK3) = k2_pre_topc(sK1,k4_xboole_0(u1_struct_0(sK1),sK3))),
% 0.21/0.45    inference(resolution,[],[f225,f34])).
% 0.21/0.45  fof(f34,plain,(
% 0.21/0.45    v3_pre_topc(sK3,sK1) | sK2 = k1_tops_1(sK0,sK2)),
% 0.21/0.45    inference(cnf_transformation,[],[f27])).
% 0.21/0.45  fof(f204,plain,(
% 0.21/0.45    ~r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK2)),sK0)),
% 0.21/0.45    inference(resolution,[],[f202,f47])).
% 0.21/0.45  fof(f159,plain,(
% 0.21/0.45    k1_tops_1(sK1,sK3) = k3_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,k4_xboole_0(u1_struct_0(sK1),sK3)))),
% 0.21/0.45    inference(forward_demodulation,[],[f157,f66])).
% 0.21/0.45  fof(f157,plain,(
% 0.21/0.45    k1_tops_1(sK1,sK3) = k3_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK3)))),
% 0.21/0.45    inference(resolution,[],[f147,f33])).
% 0.21/0.45  fof(f147,plain,(
% 0.21/0.45    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | k1_tops_1(sK1,X1) = k3_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),X1)))) )),
% 0.21/0.45    inference(resolution,[],[f38,f31])).
% 0.21/0.45  fof(f38,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f14])).
% 0.21/0.45  fof(f14,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.45    inference(ennf_transformation,[],[f6])).
% 0.21/0.45  fof(f6,axiom,(
% 0.21/0.45    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).
% 0.21/0.45  fof(f92,plain,(
% 0.21/0.45    ~v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK2),sK0) | sK3 != k1_tops_1(sK1,sK3)),
% 0.21/0.45    inference(forward_demodulation,[],[f91,f65])).
% 0.21/0.45  fof(f91,plain,(
% 0.21/0.45    ~v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK2),sK0) | sK3 != k1_tops_1(sK1,sK3)),
% 0.21/0.45    inference(subsumption_resolution,[],[f88,f32])).
% 0.21/0.45  fof(f88,plain,(
% 0.21/0.45    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK2),sK0) | sK3 != k1_tops_1(sK1,sK3)),
% 0.21/0.45    inference(resolution,[],[f86,f37])).
% 0.21/0.45  fof(f37,plain,(
% 0.21/0.45    ~v3_pre_topc(sK2,sK0) | sK3 != k1_tops_1(sK1,sK3)),
% 0.21/0.45    inference(cnf_transformation,[],[f27])).
% 0.21/0.45  % SZS output end Proof for theBenchmark
% 0.21/0.45  % (19018)------------------------------
% 0.21/0.45  % (19018)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (19018)Termination reason: Refutation
% 0.21/0.45  
% 0.21/0.45  % (19018)Memory used [KB]: 6396
% 0.21/0.45  % (19018)Time elapsed: 0.056 s
% 0.21/0.45  % (19018)------------------------------
% 0.21/0.45  % (19018)------------------------------
% 0.21/0.45  % (18998)Success in time 0.093 s
%------------------------------------------------------------------------------
