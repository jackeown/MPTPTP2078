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
% DateTime   : Thu Dec  3 13:13:05 EST 2020

% Result     : Theorem 1.42s
% Output     : Refutation 1.42s
% Verified   : 
% Statistics : Number of formulae       :  149 (3694 expanded)
%              Number of leaves         :   18 (1506 expanded)
%              Depth                    :   64
%              Number of atoms          :  531 (30844 expanded)
%              Number of equality atoms :   64 ( 509 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f534,plain,(
    $false ),
    inference(subsumption_resolution,[],[f533,f485])).

fof(f485,plain,(
    sP0(sK2,sK4) ),
    inference(subsumption_resolution,[],[f351,f484])).

fof(f484,plain,(
    v4_tops_1(sK3,sK1) ),
    inference(subsumption_resolution,[],[f483,f96])).

fof(f96,plain,(
    r1_tarski(sK3,k2_pre_topc(sK1,sK3)) ),
    inference(resolution,[],[f94,f58])).

fof(f58,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,
    ( ( ( ( ~ v4_tops_1(sK3,sK1)
          | ~ v3_pre_topc(sK3,sK1) )
        & v6_tops_1(sK3,sK1) )
      | sP0(sK2,sK4) )
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    & l1_pre_topc(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f38,f44,f43,f42,f41])).

fof(f41,plain,
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

fof(f42,plain,
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

fof(f43,plain,
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

fof(f44,plain,
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

fof(f38,plain,(
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
    inference(definition_folding,[],[f18,f37])).

fof(f37,plain,(
    ! [X1,X3] :
      ( ( ~ v6_tops_1(X3,X1)
        & v4_tops_1(X3,X1)
        & v3_pre_topc(X3,X1) )
      | ~ sP0(X1,X3) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_tops_1)).

fof(f94,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | r1_tarski(X0,k2_pre_topc(sK1,X0)) ) ),
    inference(resolution,[],[f62,f56])).

fof(f56,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(X1,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

fof(f483,plain,
    ( ~ r1_tarski(sK3,k2_pre_topc(sK1,sK3))
    | v4_tops_1(sK3,sK1) ),
    inference(forward_demodulation,[],[f482,f386])).

fof(f386,plain,(
    sK3 = k1_tops_1(sK1,sK3) ),
    inference(forward_demodulation,[],[f385,f89])).

fof(f89,plain,(
    sK3 = k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),sK3)) ),
    inference(resolution,[],[f76,f58])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f385,plain,(
    k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),sK3)) = k1_tops_1(sK1,sK3) ),
    inference(backward_demodulation,[],[f174,f381])).

fof(f381,plain,(
    k3_subset_1(u1_struct_0(sK1),sK3) = k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK3)) ),
    inference(subsumption_resolution,[],[f380,f58])).

fof(f380,plain,
    ( k3_subset_1(u1_struct_0(sK1),sK3) = k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(resolution,[],[f370,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f370,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | k3_subset_1(u1_struct_0(sK1),sK3) = k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK3)) ),
    inference(subsumption_resolution,[],[f367,f56])).

fof(f367,plain,
    ( k3_subset_1(u1_struct_0(sK1),sK3) = k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK3))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f365,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f365,plain,(
    v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK3),sK1) ),
    inference(subsumption_resolution,[],[f364,f58])).

fof(f364,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK3),sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(resolution,[],[f350,f75])).

fof(f350,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK3),sK1) ),
    inference(subsumption_resolution,[],[f127,f348])).

fof(f348,plain,(
    v3_pre_topc(sK3,sK1) ),
    inference(subsumption_resolution,[],[f347,f58])).

fof(f347,plain,
    ( v3_pre_topc(sK3,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(resolution,[],[f344,f108])).

fof(f108,plain,(
    ! [X0] :
      ( m1_subset_1(k2_pre_topc(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    inference(resolution,[],[f79,f56])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f344,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | v3_pre_topc(sK3,sK1) ),
    inference(subsumption_resolution,[],[f343,f55])).

fof(f55,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f343,plain,
    ( v3_pre_topc(sK3,sK1)
    | ~ m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f339,f56])).

fof(f339,plain,
    ( v3_pre_topc(sK3,sK1)
    | ~ m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(superposition,[],[f77,f328])).

fof(f328,plain,(
    sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) ),
    inference(subsumption_resolution,[],[f327,f56])).

fof(f327,plain,
    ( sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3))
    | ~ l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f326,f58])).

fof(f326,plain,
    ( sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(duplicate_literal_removal,[],[f324])).

fof(f324,plain,
    ( sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3))
    | sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f323,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ v6_tops_1(X1,X0)
      | k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v6_tops_1(X1,X0)
              | k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1 )
            & ( k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1
              | ~ v6_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v6_tops_1(X1,X0)
          <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v6_tops_1(X1,X0)
          <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_tops_1)).

fof(f323,plain,
    ( v6_tops_1(sK3,sK1)
    | sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) ),
    inference(resolution,[],[f322,f60])).

fof(f60,plain,
    ( sP0(sK2,sK4)
    | v6_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f322,plain,
    ( ~ sP0(sK2,sK4)
    | sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) ),
    inference(resolution,[],[f319,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v6_tops_1(X1,X0)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ~ v6_tops_1(X1,X0)
        & v4_tops_1(X1,X0)
        & v3_pre_topc(X1,X0) )
      | ~ sP0(X0,X1) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X1,X3] :
      ( ( ~ v6_tops_1(X3,X1)
        & v4_tops_1(X3,X1)
        & v3_pre_topc(X3,X1) )
      | ~ sP0(X1,X3) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f319,plain,
    ( v6_tops_1(sK4,sK2)
    | sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) ),
    inference(subsumption_resolution,[],[f318,f57])).

fof(f57,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f318,plain,
    ( v6_tops_1(sK4,sK2)
    | ~ l1_pre_topc(sK2)
    | sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) ),
    inference(subsumption_resolution,[],[f317,f59])).

fof(f59,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f45])).

fof(f317,plain,
    ( v6_tops_1(sK4,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) ),
    inference(trivial_inequality_removal,[],[f314])).

fof(f314,plain,
    ( sK4 != sK4
    | v6_tops_1(sK4,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) ),
    inference(superposition,[],[f70,f308])).

fof(f308,plain,
    ( sK4 = k1_tops_1(sK2,k2_pre_topc(sK2,sK4))
    | sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) ),
    inference(subsumption_resolution,[],[f307,f56])).

fof(f307,plain,
    ( sK4 = k1_tops_1(sK2,k2_pre_topc(sK2,sK4))
    | sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3))
    | ~ l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f305,f58])).

fof(f305,plain,
    ( sK4 = k1_tops_1(sK2,k2_pre_topc(sK2,sK4))
    | sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f304,f69])).

fof(f304,plain,
    ( v6_tops_1(sK3,sK1)
    | sK4 = k1_tops_1(sK2,k2_pre_topc(sK2,sK4)) ),
    inference(subsumption_resolution,[],[f303,f86])).

fof(f86,plain,
    ( v6_tops_1(sK3,sK1)
    | v4_tops_1(sK4,sK2) ),
    inference(resolution,[],[f53,f60])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | v4_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f303,plain,
    ( v6_tops_1(sK3,sK1)
    | sK4 = k1_tops_1(sK2,k2_pre_topc(sK2,sK4))
    | ~ v4_tops_1(sK4,sK2) ),
    inference(subsumption_resolution,[],[f302,f57])).

fof(f302,plain,
    ( v6_tops_1(sK3,sK1)
    | sK4 = k1_tops_1(sK2,k2_pre_topc(sK2,sK4))
    | ~ v4_tops_1(sK4,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f301,f59])).

fof(f301,plain,
    ( v6_tops_1(sK3,sK1)
    | sK4 = k1_tops_1(sK2,k2_pre_topc(sK2,sK4))
    | ~ v4_tops_1(sK4,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f294,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)
      | ~ v4_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
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
    inference(flattening,[],[f48])).

fof(f48,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_tops_1(X1,X0)
          <=> ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_tops_1(X1,X0)
          <=> ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_tops_1)).

fof(f294,plain,
    ( ~ r1_tarski(k1_tops_1(sK2,k2_pre_topc(sK2,sK4)),sK4)
    | v6_tops_1(sK3,sK1)
    | sK4 = k1_tops_1(sK2,k2_pre_topc(sK2,sK4)) ),
    inference(resolution,[],[f292,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
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

fof(f292,plain,
    ( r1_tarski(sK4,k1_tops_1(sK2,k2_pre_topc(sK2,sK4)))
    | v6_tops_1(sK3,sK1) ),
    inference(subsumption_resolution,[],[f291,f59])).

fof(f291,plain,
    ( r1_tarski(sK4,k1_tops_1(sK2,k2_pre_topc(sK2,sK4)))
    | v6_tops_1(sK3,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(resolution,[],[f284,f109])).

fof(f109,plain,(
    ! [X1] :
      ( m1_subset_1(k2_pre_topc(sK2,X1),k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(resolution,[],[f79,f57])).

fof(f284,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(sK4,k1_tops_1(sK2,k2_pre_topc(sK2,sK4)))
    | v6_tops_1(sK3,sK1) ),
    inference(resolution,[],[f281,f99])).

fof(f99,plain,(
    r1_tarski(sK4,k2_pre_topc(sK2,sK4)) ),
    inference(resolution,[],[f95,f59])).

fof(f95,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | r1_tarski(X1,k2_pre_topc(sK2,X1)) ) ),
    inference(resolution,[],[f62,f57])).

fof(f281,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK4,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | r1_tarski(sK4,k1_tops_1(sK2,X0))
      | v6_tops_1(sK3,sK1) ) ),
    inference(subsumption_resolution,[],[f279,f59])).

fof(f279,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK4,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
      | r1_tarski(sK4,k1_tops_1(sK2,X0))
      | v6_tops_1(sK3,sK1) ) ),
    inference(resolution,[],[f274,f85])).

fof(f85,plain,
    ( v3_pre_topc(sK4,sK2)
    | v6_tops_1(sK3,sK1) ),
    inference(resolution,[],[f52,f60])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f274,plain,(
    ! [X2,X3] :
      ( ~ v3_pre_topc(X2,sK2)
      | ~ r1_tarski(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
      | r1_tarski(X2,k1_tops_1(sK2,X3)) ) ),
    inference(resolution,[],[f74,f57])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r1_tarski(X1,X2)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(X1,k1_tops_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X1,X2)
                  & v3_pre_topc(X1,X0) )
               => r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).

fof(f70,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1
      | v6_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f77,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f127,plain,
    ( ~ v3_pre_topc(sK3,sK1)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK3),sK1) ),
    inference(superposition,[],[f125,f89])).

fof(f125,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK1),X0),sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | v4_pre_topc(X0,sK1) ) ),
    inference(resolution,[],[f68,f56])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).

fof(f174,plain,(
    k1_tops_1(sK1,sK3) = k3_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK3))) ),
    inference(resolution,[],[f170,f58])).

fof(f170,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | k1_tops_1(sK1,X0) = k3_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),X0))) ) ),
    inference(resolution,[],[f63,f56])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

fof(f482,plain,
    ( ~ r1_tarski(sK3,k2_pre_topc(sK1,k1_tops_1(sK1,sK3)))
    | v4_tops_1(sK3,sK1) ),
    inference(subsumption_resolution,[],[f481,f58])).

fof(f481,plain,
    ( ~ r1_tarski(sK3,k2_pre_topc(sK1,k1_tops_1(sK1,sK3)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | v4_tops_1(sK3,sK1) ),
    inference(subsumption_resolution,[],[f479,f83])).

fof(f83,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f479,plain,
    ( ~ r1_tarski(sK3,sK3)
    | ~ r1_tarski(sK3,k2_pre_topc(sK1,k1_tops_1(sK1,sK3)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | v4_tops_1(sK3,sK1) ),
    inference(superposition,[],[f468,f328])).

fof(f468,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,X0)),X0)
      | ~ r1_tarski(X0,k2_pre_topc(sK1,k1_tops_1(sK1,X0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | v4_tops_1(X0,sK1) ) ),
    inference(resolution,[],[f73,f56])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
      | ~ r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f351,plain,
    ( ~ v4_tops_1(sK3,sK1)
    | sP0(sK2,sK4) ),
    inference(subsumption_resolution,[],[f61,f348])).

fof(f61,plain,
    ( ~ v3_pre_topc(sK3,sK1)
    | ~ v4_tops_1(sK3,sK1)
    | sP0(sK2,sK4) ),
    inference(cnf_transformation,[],[f45])).

fof(f533,plain,(
    ~ sP0(sK2,sK4) ),
    inference(resolution,[],[f526,f54])).

fof(f526,plain,(
    v6_tops_1(sK4,sK2) ),
    inference(subsumption_resolution,[],[f525,f57])).

fof(f525,plain,
    ( v6_tops_1(sK4,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f524,f59])).

fof(f524,plain,
    ( v6_tops_1(sK4,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(trivial_inequality_removal,[],[f521])).

fof(f521,plain,
    ( sK4 != sK4
    | v6_tops_1(sK4,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(superposition,[],[f70,f515])).

fof(f515,plain,(
    sK4 = k1_tops_1(sK2,k2_pre_topc(sK2,sK4)) ),
    inference(subsumption_resolution,[],[f514,f57])).

fof(f514,plain,
    ( sK4 = k1_tops_1(sK2,k2_pre_topc(sK2,sK4))
    | ~ l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f513,f59])).

fof(f513,plain,
    ( sK4 = k1_tops_1(sK2,k2_pre_topc(sK2,sK4))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f512,f486])).

fof(f486,plain,(
    v4_tops_1(sK4,sK2) ),
    inference(resolution,[],[f485,f53])).

fof(f512,plain,
    ( sK4 = k1_tops_1(sK2,k2_pre_topc(sK2,sK4))
    | ~ v4_tops_1(sK4,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f507,f71])).

fof(f507,plain,
    ( ~ r1_tarski(k1_tops_1(sK2,k2_pre_topc(sK2,sK4)),sK4)
    | sK4 = k1_tops_1(sK2,k2_pre_topc(sK2,sK4)) ),
    inference(resolution,[],[f505,f82])).

fof(f505,plain,(
    r1_tarski(sK4,k1_tops_1(sK2,k2_pre_topc(sK2,sK4))) ),
    inference(subsumption_resolution,[],[f504,f59])).

fof(f504,plain,
    ( r1_tarski(sK4,k1_tops_1(sK2,k2_pre_topc(sK2,sK4)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(resolution,[],[f491,f109])).

fof(f491,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(sK4,k1_tops_1(sK2,k2_pre_topc(sK2,sK4))) ),
    inference(resolution,[],[f490,f99])).

fof(f490,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK4,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | r1_tarski(sK4,k1_tops_1(sK2,X0)) ) ),
    inference(subsumption_resolution,[],[f489,f59])).

fof(f489,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK4,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
      | r1_tarski(sK4,k1_tops_1(sK2,X0)) ) ),
    inference(resolution,[],[f487,f274])).

fof(f487,plain,(
    v3_pre_topc(sK4,sK2) ),
    inference(resolution,[],[f485,f52])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:43:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (23768)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.51  % (23769)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (23790)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.51  % (23765)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.51  % (23780)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.52  % (23787)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.52  % (23771)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.52  % (23786)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.52  % (23774)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.52  % (23770)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.52  % (23784)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.52  % (23776)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.52  % (23773)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.53  % (23779)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.29/0.53  % (23778)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.29/0.53  % (23781)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.29/0.54  % (23782)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.29/0.54  % (23772)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.29/0.54  % (23766)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.29/0.54  % (23785)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.29/0.54  % (23777)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.29/0.54  % (23788)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.29/0.55  % (23775)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.29/0.55  % (23767)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.42/0.55  % (23789)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.42/0.55  % (23768)Refutation found. Thanks to Tanya!
% 1.42/0.55  % SZS status Theorem for theBenchmark
% 1.42/0.55  % SZS output start Proof for theBenchmark
% 1.42/0.55  fof(f534,plain,(
% 1.42/0.55    $false),
% 1.42/0.55    inference(subsumption_resolution,[],[f533,f485])).
% 1.42/0.55  fof(f485,plain,(
% 1.42/0.55    sP0(sK2,sK4)),
% 1.42/0.55    inference(subsumption_resolution,[],[f351,f484])).
% 1.42/0.55  fof(f484,plain,(
% 1.42/0.55    v4_tops_1(sK3,sK1)),
% 1.42/0.55    inference(subsumption_resolution,[],[f483,f96])).
% 1.42/0.55  fof(f96,plain,(
% 1.42/0.55    r1_tarski(sK3,k2_pre_topc(sK1,sK3))),
% 1.42/0.55    inference(resolution,[],[f94,f58])).
% 1.42/0.55  fof(f58,plain,(
% 1.42/0.55    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))),
% 1.42/0.55    inference(cnf_transformation,[],[f45])).
% 1.42/0.55  fof(f45,plain,(
% 1.42/0.55    ((((((~v4_tops_1(sK3,sK1) | ~v3_pre_topc(sK3,sK1)) & v6_tops_1(sK3,sK1)) | sP0(sK2,sK4)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1)),
% 1.42/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f38,f44,f43,f42,f41])).
% 1.42/0.55  fof(f41,plain,(
% 1.42/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | sP0(X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,sK1) | ~v3_pre_topc(X2,sK1)) & v6_tops_1(X2,sK1)) | sP0(X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1))),
% 1.42/0.55    introduced(choice_axiom,[])).
% 1.42/0.55  fof(f42,plain,(
% 1.42/0.55    ? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,sK1) | ~v3_pre_topc(X2,sK1)) & v6_tops_1(X2,sK1)) | sP0(X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(X1)) => (? [X2] : (? [X3] : ((((~v4_tops_1(X2,sK1) | ~v3_pre_topc(X2,sK1)) & v6_tops_1(X2,sK1)) | sP0(sK2,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK2))),
% 1.42/0.55    introduced(choice_axiom,[])).
% 1.42/0.55  fof(f43,plain,(
% 1.42/0.55    ? [X2] : (? [X3] : ((((~v4_tops_1(X2,sK1) | ~v3_pre_topc(X2,sK1)) & v6_tops_1(X2,sK1)) | sP0(sK2,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))) => (? [X3] : ((((~v4_tops_1(sK3,sK1) | ~v3_pre_topc(sK3,sK1)) & v6_tops_1(sK3,sK1)) | sP0(sK2,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))))),
% 1.42/0.55    introduced(choice_axiom,[])).
% 1.42/0.55  fof(f44,plain,(
% 1.42/0.55    ? [X3] : ((((~v4_tops_1(sK3,sK1) | ~v3_pre_topc(sK3,sK1)) & v6_tops_1(sK3,sK1)) | sP0(sK2,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) => ((((~v4_tops_1(sK3,sK1) | ~v3_pre_topc(sK3,sK1)) & v6_tops_1(sK3,sK1)) | sP0(sK2,sK4)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))))),
% 1.42/0.55    introduced(choice_axiom,[])).
% 1.42/0.55  fof(f38,plain,(
% 1.42/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | sP0(X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.42/0.55    inference(definition_folding,[],[f18,f37])).
% 1.42/0.55  fof(f37,plain,(
% 1.42/0.55    ! [X1,X3] : ((~v6_tops_1(X3,X1) & v4_tops_1(X3,X1) & v3_pre_topc(X3,X1)) | ~sP0(X1,X3))),
% 1.42/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.42/0.55  fof(f18,plain,(
% 1.42/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | (~v6_tops_1(X3,X1) & v4_tops_1(X3,X1) & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.42/0.55    inference(flattening,[],[f17])).
% 1.42/0.55  fof(f17,plain,(
% 1.42/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | (~v6_tops_1(X3,X1) & (v4_tops_1(X3,X1) & v3_pre_topc(X3,X1)))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.42/0.55    inference(ennf_transformation,[],[f16])).
% 1.42/0.55  fof(f16,negated_conjecture,(
% 1.42/0.55    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v6_tops_1(X2,X0) => (v4_tops_1(X2,X0) & v3_pre_topc(X2,X0))) & ((v4_tops_1(X3,X1) & v3_pre_topc(X3,X1)) => v6_tops_1(X3,X1)))))))),
% 1.42/0.55    inference(negated_conjecture,[],[f15])).
% 1.42/0.55  fof(f15,conjecture,(
% 1.42/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v6_tops_1(X2,X0) => (v4_tops_1(X2,X0) & v3_pre_topc(X2,X0))) & ((v4_tops_1(X3,X1) & v3_pre_topc(X3,X1)) => v6_tops_1(X3,X1)))))))),
% 1.42/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_tops_1)).
% 1.42/0.55  fof(f94,plain,(
% 1.42/0.55    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | r1_tarski(X0,k2_pre_topc(sK1,X0))) )),
% 1.42/0.55    inference(resolution,[],[f62,f56])).
% 1.42/0.55  fof(f56,plain,(
% 1.42/0.55    l1_pre_topc(sK1)),
% 1.42/0.55    inference(cnf_transformation,[],[f45])).
% 1.42/0.55  fof(f62,plain,(
% 1.42/0.55    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(X1,k2_pre_topc(X0,X1))) )),
% 1.42/0.55    inference(cnf_transformation,[],[f19])).
% 1.42/0.55  fof(f19,plain,(
% 1.42/0.55    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.42/0.55    inference(ennf_transformation,[],[f5])).
% 1.42/0.55  fof(f5,axiom,(
% 1.42/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 1.42/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).
% 1.42/0.55  fof(f483,plain,(
% 1.42/0.55    ~r1_tarski(sK3,k2_pre_topc(sK1,sK3)) | v4_tops_1(sK3,sK1)),
% 1.42/0.55    inference(forward_demodulation,[],[f482,f386])).
% 1.42/0.55  fof(f386,plain,(
% 1.42/0.55    sK3 = k1_tops_1(sK1,sK3)),
% 1.42/0.55    inference(forward_demodulation,[],[f385,f89])).
% 1.42/0.55  fof(f89,plain,(
% 1.42/0.55    sK3 = k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),sK3))),
% 1.42/0.55    inference(resolution,[],[f76,f58])).
% 1.42/0.55  fof(f76,plain,(
% 1.42/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 1.42/0.55    inference(cnf_transformation,[],[f30])).
% 1.42/0.55  fof(f30,plain,(
% 1.42/0.55    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.42/0.55    inference(ennf_transformation,[],[f3])).
% 1.42/0.55  fof(f3,axiom,(
% 1.42/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 1.42/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 1.42/0.55  fof(f385,plain,(
% 1.42/0.55    k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),sK3)) = k1_tops_1(sK1,sK3)),
% 1.42/0.55    inference(backward_demodulation,[],[f174,f381])).
% 1.42/0.55  fof(f381,plain,(
% 1.42/0.55    k3_subset_1(u1_struct_0(sK1),sK3) = k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK3))),
% 1.42/0.55    inference(subsumption_resolution,[],[f380,f58])).
% 1.42/0.55  fof(f380,plain,(
% 1.42/0.55    k3_subset_1(u1_struct_0(sK1),sK3) = k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))),
% 1.42/0.55    inference(resolution,[],[f370,f75])).
% 1.42/0.55  fof(f75,plain,(
% 1.42/0.55    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.42/0.55    inference(cnf_transformation,[],[f29])).
% 1.42/0.55  fof(f29,plain,(
% 1.42/0.55    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.42/0.55    inference(ennf_transformation,[],[f2])).
% 1.42/0.55  fof(f2,axiom,(
% 1.42/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.42/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 1.42/0.55  fof(f370,plain,(
% 1.42/0.55    ~m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK3),k1_zfmisc_1(u1_struct_0(sK1))) | k3_subset_1(u1_struct_0(sK1),sK3) = k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK3))),
% 1.42/0.55    inference(subsumption_resolution,[],[f367,f56])).
% 1.42/0.55  fof(f367,plain,(
% 1.42/0.55    k3_subset_1(u1_struct_0(sK1),sK3) = k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK3)) | ~m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK3),k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1)),
% 1.42/0.55    inference(resolution,[],[f365,f65])).
% 1.42/0.55  fof(f65,plain,(
% 1.42/0.55    ( ! [X0,X1] : (~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f23])).
% 1.42/0.55  fof(f23,plain,(
% 1.42/0.55    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.42/0.55    inference(flattening,[],[f22])).
% 1.42/0.55  fof(f22,plain,(
% 1.42/0.55    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.42/0.55    inference(ennf_transformation,[],[f6])).
% 1.42/0.55  fof(f6,axiom,(
% 1.42/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 1.42/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 1.42/0.55  fof(f365,plain,(
% 1.42/0.55    v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK3),sK1)),
% 1.42/0.55    inference(subsumption_resolution,[],[f364,f58])).
% 1.42/0.55  fof(f364,plain,(
% 1.42/0.55    v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK3),sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))),
% 1.42/0.55    inference(resolution,[],[f350,f75])).
% 1.42/0.55  fof(f350,plain,(
% 1.42/0.55    ~m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK3),k1_zfmisc_1(u1_struct_0(sK1))) | v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK3),sK1)),
% 1.42/0.55    inference(subsumption_resolution,[],[f127,f348])).
% 1.42/0.55  fof(f348,plain,(
% 1.42/0.55    v3_pre_topc(sK3,sK1)),
% 1.42/0.55    inference(subsumption_resolution,[],[f347,f58])).
% 1.42/0.55  fof(f347,plain,(
% 1.42/0.55    v3_pre_topc(sK3,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))),
% 1.42/0.55    inference(resolution,[],[f344,f108])).
% 1.42/0.55  fof(f108,plain,(
% 1.42/0.55    ( ! [X0] : (m1_subset_1(k2_pre_topc(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))) )),
% 1.42/0.55    inference(resolution,[],[f79,f56])).
% 1.42/0.55  fof(f79,plain,(
% 1.42/0.55    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 1.42/0.55    inference(cnf_transformation,[],[f36])).
% 1.42/0.55  fof(f36,plain,(
% 1.42/0.55    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.42/0.55    inference(flattening,[],[f35])).
% 1.42/0.55  fof(f35,plain,(
% 1.42/0.55    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.42/0.55    inference(ennf_transformation,[],[f4])).
% 1.42/0.55  fof(f4,axiom,(
% 1.42/0.55    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.42/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 1.42/0.55  fof(f344,plain,(
% 1.42/0.55    ~m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) | v3_pre_topc(sK3,sK1)),
% 1.42/0.55    inference(subsumption_resolution,[],[f343,f55])).
% 1.42/0.55  fof(f55,plain,(
% 1.42/0.55    v2_pre_topc(sK1)),
% 1.42/0.55    inference(cnf_transformation,[],[f45])).
% 1.42/0.55  fof(f343,plain,(
% 1.42/0.55    v3_pre_topc(sK3,sK1) | ~m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) | ~v2_pre_topc(sK1)),
% 1.42/0.55    inference(subsumption_resolution,[],[f339,f56])).
% 1.42/0.55  fof(f339,plain,(
% 1.42/0.55    v3_pre_topc(sK3,sK1) | ~m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1)),
% 1.42/0.55    inference(superposition,[],[f77,f328])).
% 1.42/0.55  fof(f328,plain,(
% 1.42/0.55    sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3))),
% 1.42/0.55    inference(subsumption_resolution,[],[f327,f56])).
% 1.42/0.55  fof(f327,plain,(
% 1.42/0.55    sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) | ~l1_pre_topc(sK1)),
% 1.42/0.55    inference(subsumption_resolution,[],[f326,f58])).
% 1.42/0.55  fof(f326,plain,(
% 1.42/0.55    sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1)),
% 1.42/0.55    inference(duplicate_literal_removal,[],[f324])).
% 1.42/0.55  fof(f324,plain,(
% 1.42/0.55    sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) | sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1)),
% 1.42/0.55    inference(resolution,[],[f323,f69])).
% 1.42/0.55  fof(f69,plain,(
% 1.42/0.55    ( ! [X0,X1] : (~v6_tops_1(X1,X0) | k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f47])).
% 1.42/0.55  fof(f47,plain,(
% 1.42/0.55    ! [X0] : (! [X1] : (((v6_tops_1(X1,X0) | k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1) & (k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 | ~v6_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.42/0.55    inference(nnf_transformation,[],[f25])).
% 1.42/0.55  fof(f25,plain,(
% 1.42/0.55    ! [X0] : (! [X1] : ((v6_tops_1(X1,X0) <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.42/0.55    inference(ennf_transformation,[],[f9])).
% 1.42/0.55  fof(f9,axiom,(
% 1.42/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v6_tops_1(X1,X0) <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1)))),
% 1.42/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_tops_1)).
% 1.42/0.55  fof(f323,plain,(
% 1.42/0.55    v6_tops_1(sK3,sK1) | sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3))),
% 1.42/0.55    inference(resolution,[],[f322,f60])).
% 1.42/0.55  fof(f60,plain,(
% 1.42/0.55    sP0(sK2,sK4) | v6_tops_1(sK3,sK1)),
% 1.42/0.55    inference(cnf_transformation,[],[f45])).
% 1.42/0.55  fof(f322,plain,(
% 1.42/0.55    ~sP0(sK2,sK4) | sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3))),
% 1.42/0.55    inference(resolution,[],[f319,f54])).
% 1.42/0.55  fof(f54,plain,(
% 1.42/0.55    ( ! [X0,X1] : (~v6_tops_1(X1,X0) | ~sP0(X0,X1)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f40])).
% 1.42/0.55  fof(f40,plain,(
% 1.42/0.55    ! [X0,X1] : ((~v6_tops_1(X1,X0) & v4_tops_1(X1,X0) & v3_pre_topc(X1,X0)) | ~sP0(X0,X1))),
% 1.42/0.55    inference(rectify,[],[f39])).
% 1.42/0.55  fof(f39,plain,(
% 1.42/0.55    ! [X1,X3] : ((~v6_tops_1(X3,X1) & v4_tops_1(X3,X1) & v3_pre_topc(X3,X1)) | ~sP0(X1,X3))),
% 1.42/0.55    inference(nnf_transformation,[],[f37])).
% 1.42/0.55  fof(f319,plain,(
% 1.42/0.55    v6_tops_1(sK4,sK2) | sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3))),
% 1.42/0.55    inference(subsumption_resolution,[],[f318,f57])).
% 1.42/0.55  fof(f57,plain,(
% 1.42/0.55    l1_pre_topc(sK2)),
% 1.42/0.55    inference(cnf_transformation,[],[f45])).
% 1.42/0.55  fof(f318,plain,(
% 1.42/0.55    v6_tops_1(sK4,sK2) | ~l1_pre_topc(sK2) | sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3))),
% 1.42/0.55    inference(subsumption_resolution,[],[f317,f59])).
% 1.42/0.55  fof(f59,plain,(
% 1.42/0.55    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))),
% 1.42/0.55    inference(cnf_transformation,[],[f45])).
% 1.42/0.55  fof(f317,plain,(
% 1.42/0.55    v6_tops_1(sK4,sK2) | ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2) | sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3))),
% 1.42/0.55    inference(trivial_inequality_removal,[],[f314])).
% 1.42/0.55  fof(f314,plain,(
% 1.42/0.55    sK4 != sK4 | v6_tops_1(sK4,sK2) | ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2) | sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3))),
% 1.42/0.55    inference(superposition,[],[f70,f308])).
% 1.42/0.55  fof(f308,plain,(
% 1.42/0.55    sK4 = k1_tops_1(sK2,k2_pre_topc(sK2,sK4)) | sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3))),
% 1.42/0.55    inference(subsumption_resolution,[],[f307,f56])).
% 1.42/0.55  fof(f307,plain,(
% 1.42/0.55    sK4 = k1_tops_1(sK2,k2_pre_topc(sK2,sK4)) | sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) | ~l1_pre_topc(sK1)),
% 1.42/0.55    inference(subsumption_resolution,[],[f305,f58])).
% 1.42/0.55  fof(f305,plain,(
% 1.42/0.55    sK4 = k1_tops_1(sK2,k2_pre_topc(sK2,sK4)) | sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1)),
% 1.42/0.55    inference(resolution,[],[f304,f69])).
% 1.42/0.55  fof(f304,plain,(
% 1.42/0.55    v6_tops_1(sK3,sK1) | sK4 = k1_tops_1(sK2,k2_pre_topc(sK2,sK4))),
% 1.42/0.55    inference(subsumption_resolution,[],[f303,f86])).
% 1.42/0.55  fof(f86,plain,(
% 1.42/0.55    v6_tops_1(sK3,sK1) | v4_tops_1(sK4,sK2)),
% 1.42/0.55    inference(resolution,[],[f53,f60])).
% 1.42/0.55  fof(f53,plain,(
% 1.42/0.55    ( ! [X0,X1] : (~sP0(X0,X1) | v4_tops_1(X1,X0)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f40])).
% 1.42/0.55  fof(f303,plain,(
% 1.42/0.55    v6_tops_1(sK3,sK1) | sK4 = k1_tops_1(sK2,k2_pre_topc(sK2,sK4)) | ~v4_tops_1(sK4,sK2)),
% 1.42/0.55    inference(subsumption_resolution,[],[f302,f57])).
% 1.42/0.55  fof(f302,plain,(
% 1.42/0.55    v6_tops_1(sK3,sK1) | sK4 = k1_tops_1(sK2,k2_pre_topc(sK2,sK4)) | ~v4_tops_1(sK4,sK2) | ~l1_pre_topc(sK2)),
% 1.42/0.55    inference(subsumption_resolution,[],[f301,f59])).
% 1.42/0.55  fof(f301,plain,(
% 1.42/0.55    v6_tops_1(sK3,sK1) | sK4 = k1_tops_1(sK2,k2_pre_topc(sK2,sK4)) | ~v4_tops_1(sK4,sK2) | ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2)),
% 1.42/0.55    inference(resolution,[],[f294,f71])).
% 1.42/0.55  fof(f71,plain,(
% 1.42/0.55    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) | ~v4_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f49])).
% 1.42/0.55  fof(f49,plain,(
% 1.42/0.55    ! [X0] : (! [X1] : (((v4_tops_1(X1,X0) | ~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) & ((r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) | ~v4_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.42/0.55    inference(flattening,[],[f48])).
% 1.42/0.55  fof(f48,plain,(
% 1.42/0.55    ! [X0] : (! [X1] : (((v4_tops_1(X1,X0) | (~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1))) & ((r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) | ~v4_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.42/0.55    inference(nnf_transformation,[],[f26])).
% 1.42/0.55  fof(f26,plain,(
% 1.42/0.55    ! [X0] : (! [X1] : ((v4_tops_1(X1,X0) <=> (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.42/0.55    inference(ennf_transformation,[],[f8])).
% 1.42/0.55  fof(f8,axiom,(
% 1.42/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_tops_1(X1,X0) <=> (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)))))),
% 1.42/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_tops_1)).
% 1.42/0.55  fof(f294,plain,(
% 1.42/0.55    ~r1_tarski(k1_tops_1(sK2,k2_pre_topc(sK2,sK4)),sK4) | v6_tops_1(sK3,sK1) | sK4 = k1_tops_1(sK2,k2_pre_topc(sK2,sK4))),
% 1.42/0.55    inference(resolution,[],[f292,f82])).
% 1.42/0.55  fof(f82,plain,(
% 1.42/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.42/0.55    inference(cnf_transformation,[],[f51])).
% 1.42/0.55  fof(f51,plain,(
% 1.42/0.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.42/0.55    inference(flattening,[],[f50])).
% 1.42/0.55  fof(f50,plain,(
% 1.42/0.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.42/0.55    inference(nnf_transformation,[],[f1])).
% 1.42/0.55  fof(f1,axiom,(
% 1.42/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.42/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.42/0.55  fof(f292,plain,(
% 1.42/0.55    r1_tarski(sK4,k1_tops_1(sK2,k2_pre_topc(sK2,sK4))) | v6_tops_1(sK3,sK1)),
% 1.42/0.55    inference(subsumption_resolution,[],[f291,f59])).
% 1.42/0.55  fof(f291,plain,(
% 1.42/0.55    r1_tarski(sK4,k1_tops_1(sK2,k2_pre_topc(sK2,sK4))) | v6_tops_1(sK3,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))),
% 1.42/0.55    inference(resolution,[],[f284,f109])).
% 1.42/0.55  fof(f109,plain,(
% 1.42/0.55    ( ! [X1] : (m1_subset_1(k2_pre_topc(sK2,X1),k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 1.42/0.55    inference(resolution,[],[f79,f57])).
% 1.42/0.55  fof(f284,plain,(
% 1.42/0.55    ~m1_subset_1(k2_pre_topc(sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2))) | r1_tarski(sK4,k1_tops_1(sK2,k2_pre_topc(sK2,sK4))) | v6_tops_1(sK3,sK1)),
% 1.42/0.55    inference(resolution,[],[f281,f99])).
% 1.42/0.55  fof(f99,plain,(
% 1.42/0.55    r1_tarski(sK4,k2_pre_topc(sK2,sK4))),
% 1.42/0.55    inference(resolution,[],[f95,f59])).
% 1.42/0.55  fof(f95,plain,(
% 1.42/0.55    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) | r1_tarski(X1,k2_pre_topc(sK2,X1))) )),
% 1.42/0.55    inference(resolution,[],[f62,f57])).
% 1.42/0.55  fof(f281,plain,(
% 1.42/0.55    ( ! [X0] : (~r1_tarski(sK4,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | r1_tarski(sK4,k1_tops_1(sK2,X0)) | v6_tops_1(sK3,sK1)) )),
% 1.42/0.55    inference(subsumption_resolution,[],[f279,f59])).
% 1.42/0.55  fof(f279,plain,(
% 1.42/0.55    ( ! [X0] : (~r1_tarski(sK4,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) | r1_tarski(sK4,k1_tops_1(sK2,X0)) | v6_tops_1(sK3,sK1)) )),
% 1.42/0.55    inference(resolution,[],[f274,f85])).
% 1.42/0.55  fof(f85,plain,(
% 1.42/0.55    v3_pre_topc(sK4,sK2) | v6_tops_1(sK3,sK1)),
% 1.42/0.55    inference(resolution,[],[f52,f60])).
% 1.42/0.55  fof(f52,plain,(
% 1.42/0.55    ( ! [X0,X1] : (~sP0(X0,X1) | v3_pre_topc(X1,X0)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f40])).
% 1.42/0.55  fof(f274,plain,(
% 1.42/0.55    ( ! [X2,X3] : (~v3_pre_topc(X2,sK2) | ~r1_tarski(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) | r1_tarski(X2,k1_tops_1(sK2,X3))) )),
% 1.42/0.55    inference(resolution,[],[f74,f57])).
% 1.42/0.55  fof(f74,plain,(
% 1.42/0.55    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(X1,k1_tops_1(X0,X2))) )),
% 1.42/0.55    inference(cnf_transformation,[],[f28])).
% 1.42/0.55  fof(f28,plain,(
% 1.42/0.55    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.42/0.55    inference(flattening,[],[f27])).
% 1.42/0.55  fof(f27,plain,(
% 1.42/0.55    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.42/0.55    inference(ennf_transformation,[],[f13])).
% 1.42/0.55  fof(f13,axiom,(
% 1.42/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 1.42/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).
% 1.42/0.55  fof(f70,plain,(
% 1.42/0.55    ( ! [X0,X1] : (k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1 | v6_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f47])).
% 1.42/0.55  fof(f77,plain,(
% 1.42/0.55    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f32])).
% 1.42/0.55  fof(f32,plain,(
% 1.42/0.55    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.42/0.55    inference(flattening,[],[f31])).
% 1.42/0.55  fof(f31,plain,(
% 1.42/0.55    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.42/0.55    inference(ennf_transformation,[],[f11])).
% 1.42/0.55  fof(f11,axiom,(
% 1.42/0.55    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 1.42/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).
% 1.42/0.55  fof(f127,plain,(
% 1.42/0.55    ~v3_pre_topc(sK3,sK1) | ~m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK3),k1_zfmisc_1(u1_struct_0(sK1))) | v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK3),sK1)),
% 1.42/0.55    inference(superposition,[],[f125,f89])).
% 1.42/0.55  fof(f125,plain,(
% 1.42/0.55    ( ! [X0] : (~v3_pre_topc(k3_subset_1(u1_struct_0(sK1),X0),sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | v4_pre_topc(X0,sK1)) )),
% 1.42/0.55    inference(resolution,[],[f68,f56])).
% 1.42/0.55  fof(f68,plain,(
% 1.42/0.55    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v4_pre_topc(X1,X0)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f46])).
% 1.42/0.55  fof(f46,plain,(
% 1.42/0.55    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.42/0.55    inference(nnf_transformation,[],[f24])).
% 1.42/0.55  fof(f24,plain,(
% 1.42/0.55    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.42/0.55    inference(ennf_transformation,[],[f12])).
% 1.42/0.55  fof(f12,axiom,(
% 1.42/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 1.42/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).
% 1.42/0.55  fof(f174,plain,(
% 1.42/0.55    k1_tops_1(sK1,sK3) = k3_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK3)))),
% 1.42/0.55    inference(resolution,[],[f170,f58])).
% 1.42/0.55  fof(f170,plain,(
% 1.42/0.55    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | k1_tops_1(sK1,X0) = k3_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),X0)))) )),
% 1.42/0.55    inference(resolution,[],[f63,f56])).
% 1.42/0.55  fof(f63,plain,(
% 1.42/0.55    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))) )),
% 1.42/0.55    inference(cnf_transformation,[],[f20])).
% 1.42/0.55  fof(f20,plain,(
% 1.42/0.55    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.42/0.55    inference(ennf_transformation,[],[f7])).
% 1.42/0.55  fof(f7,axiom,(
% 1.42/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 1.42/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).
% 1.42/0.55  fof(f482,plain,(
% 1.42/0.55    ~r1_tarski(sK3,k2_pre_topc(sK1,k1_tops_1(sK1,sK3))) | v4_tops_1(sK3,sK1)),
% 1.42/0.55    inference(subsumption_resolution,[],[f481,f58])).
% 1.42/0.55  fof(f481,plain,(
% 1.42/0.55    ~r1_tarski(sK3,k2_pre_topc(sK1,k1_tops_1(sK1,sK3))) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) | v4_tops_1(sK3,sK1)),
% 1.42/0.55    inference(subsumption_resolution,[],[f479,f83])).
% 1.42/0.55  fof(f83,plain,(
% 1.42/0.55    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.42/0.55    inference(equality_resolution,[],[f81])).
% 1.42/0.55  fof(f81,plain,(
% 1.42/0.55    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.42/0.55    inference(cnf_transformation,[],[f51])).
% 1.42/0.55  fof(f479,plain,(
% 1.42/0.55    ~r1_tarski(sK3,sK3) | ~r1_tarski(sK3,k2_pre_topc(sK1,k1_tops_1(sK1,sK3))) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) | v4_tops_1(sK3,sK1)),
% 1.42/0.55    inference(superposition,[],[f468,f328])).
% 1.42/0.55  fof(f468,plain,(
% 1.42/0.55    ( ! [X0] : (~r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,X0)),X0) | ~r1_tarski(X0,k2_pre_topc(sK1,k1_tops_1(sK1,X0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | v4_tops_1(X0,sK1)) )),
% 1.42/0.55    inference(resolution,[],[f73,f56])).
% 1.42/0.55  fof(f73,plain,(
% 1.42/0.55    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v4_tops_1(X1,X0)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f49])).
% 1.42/0.55  fof(f351,plain,(
% 1.42/0.55    ~v4_tops_1(sK3,sK1) | sP0(sK2,sK4)),
% 1.42/0.55    inference(subsumption_resolution,[],[f61,f348])).
% 1.42/0.55  fof(f61,plain,(
% 1.42/0.55    ~v3_pre_topc(sK3,sK1) | ~v4_tops_1(sK3,sK1) | sP0(sK2,sK4)),
% 1.42/0.55    inference(cnf_transformation,[],[f45])).
% 1.42/0.55  fof(f533,plain,(
% 1.42/0.55    ~sP0(sK2,sK4)),
% 1.42/0.55    inference(resolution,[],[f526,f54])).
% 1.42/0.55  fof(f526,plain,(
% 1.42/0.55    v6_tops_1(sK4,sK2)),
% 1.42/0.55    inference(subsumption_resolution,[],[f525,f57])).
% 1.42/0.55  fof(f525,plain,(
% 1.42/0.55    v6_tops_1(sK4,sK2) | ~l1_pre_topc(sK2)),
% 1.42/0.55    inference(subsumption_resolution,[],[f524,f59])).
% 1.42/0.55  fof(f524,plain,(
% 1.42/0.55    v6_tops_1(sK4,sK2) | ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2)),
% 1.42/0.55    inference(trivial_inequality_removal,[],[f521])).
% 1.42/0.55  fof(f521,plain,(
% 1.42/0.55    sK4 != sK4 | v6_tops_1(sK4,sK2) | ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2)),
% 1.42/0.55    inference(superposition,[],[f70,f515])).
% 1.42/0.55  fof(f515,plain,(
% 1.42/0.55    sK4 = k1_tops_1(sK2,k2_pre_topc(sK2,sK4))),
% 1.42/0.55    inference(subsumption_resolution,[],[f514,f57])).
% 1.42/0.55  fof(f514,plain,(
% 1.42/0.55    sK4 = k1_tops_1(sK2,k2_pre_topc(sK2,sK4)) | ~l1_pre_topc(sK2)),
% 1.42/0.55    inference(subsumption_resolution,[],[f513,f59])).
% 1.42/0.55  fof(f513,plain,(
% 1.42/0.55    sK4 = k1_tops_1(sK2,k2_pre_topc(sK2,sK4)) | ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2)),
% 1.42/0.55    inference(subsumption_resolution,[],[f512,f486])).
% 1.42/0.55  fof(f486,plain,(
% 1.42/0.55    v4_tops_1(sK4,sK2)),
% 1.42/0.55    inference(resolution,[],[f485,f53])).
% 1.42/0.55  fof(f512,plain,(
% 1.42/0.55    sK4 = k1_tops_1(sK2,k2_pre_topc(sK2,sK4)) | ~v4_tops_1(sK4,sK2) | ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2)),
% 1.42/0.55    inference(resolution,[],[f507,f71])).
% 1.42/0.55  fof(f507,plain,(
% 1.42/0.55    ~r1_tarski(k1_tops_1(sK2,k2_pre_topc(sK2,sK4)),sK4) | sK4 = k1_tops_1(sK2,k2_pre_topc(sK2,sK4))),
% 1.42/0.55    inference(resolution,[],[f505,f82])).
% 1.42/0.55  fof(f505,plain,(
% 1.42/0.55    r1_tarski(sK4,k1_tops_1(sK2,k2_pre_topc(sK2,sK4)))),
% 1.42/0.55    inference(subsumption_resolution,[],[f504,f59])).
% 1.42/0.55  fof(f504,plain,(
% 1.42/0.55    r1_tarski(sK4,k1_tops_1(sK2,k2_pre_topc(sK2,sK4))) | ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))),
% 1.42/0.55    inference(resolution,[],[f491,f109])).
% 1.42/0.55  fof(f491,plain,(
% 1.42/0.55    ~m1_subset_1(k2_pre_topc(sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2))) | r1_tarski(sK4,k1_tops_1(sK2,k2_pre_topc(sK2,sK4)))),
% 1.42/0.55    inference(resolution,[],[f490,f99])).
% 1.42/0.55  fof(f490,plain,(
% 1.42/0.55    ( ! [X0] : (~r1_tarski(sK4,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | r1_tarski(sK4,k1_tops_1(sK2,X0))) )),
% 1.42/0.55    inference(subsumption_resolution,[],[f489,f59])).
% 1.42/0.55  fof(f489,plain,(
% 1.42/0.55    ( ! [X0] : (~r1_tarski(sK4,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) | r1_tarski(sK4,k1_tops_1(sK2,X0))) )),
% 1.42/0.55    inference(resolution,[],[f487,f274])).
% 1.42/0.55  fof(f487,plain,(
% 1.42/0.55    v3_pre_topc(sK4,sK2)),
% 1.42/0.55    inference(resolution,[],[f485,f52])).
% 1.42/0.55  % SZS output end Proof for theBenchmark
% 1.42/0.55  % (23768)------------------------------
% 1.42/0.55  % (23768)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.55  % (23768)Termination reason: Refutation
% 1.42/0.55  
% 1.42/0.55  % (23768)Memory used [KB]: 6652
% 1.42/0.55  % (23768)Time elapsed: 0.117 s
% 1.42/0.55  % (23768)------------------------------
% 1.42/0.55  % (23768)------------------------------
% 1.42/0.56  % (23764)Success in time 0.189 s
%------------------------------------------------------------------------------
