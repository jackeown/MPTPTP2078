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
% DateTime   : Thu Dec  3 13:11:46 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  105 (1479 expanded)
%              Number of leaves         :   14 ( 390 expanded)
%              Depth                    :   26
%              Number of atoms          :  307 (7546 expanded)
%              Number of equality atoms :   92 (2004 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2220,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2121,f2125])).

fof(f2125,plain,(
    v3_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f113,f2122])).

fof(f2122,plain,(
    sK1 = k1_tops_1(sK0,sK1) ),
    inference(backward_demodulation,[],[f1424,f2111])).

fof(f2111,plain,(
    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f134,f2109])).

fof(f2109,plain,(
    k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),sK1) ),
    inference(backward_demodulation,[],[f133,f2108])).

fof(f2108,plain,(
    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f2104,f49])).

fof(f49,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | ~ v3_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | v3_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f42,f44,f43])).

fof(f43,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
              | ~ v3_pre_topc(X1,X0) )
            & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
              | v3_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
            | ~ v3_pre_topc(X1,sK0) )
          & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
            | v3_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X1] :
        ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
          | ~ v3_pre_topc(X1,sK0) )
        & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
          | v3_pre_topc(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
        | ~ v3_pre_topc(sK1,sK0) )
      & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
        | v3_pre_topc(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).

fof(f2104,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) ),
    inference(condensation,[],[f2091])).

fof(f2091,plain,(
    ! [X17] :
      ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(superposition,[],[f354,f1426])).

fof(f1426,plain,(
    ! [X3] :
      ( sK1 = k1_tops_1(sK0,sK1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(duplicate_literal_removal,[],[f1425])).

fof(f1425,plain,(
    ! [X3] :
      ( sK1 = k1_tops_1(sK0,sK1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | sK1 = k1_tops_1(sK0,sK1) ) ),
    inference(backward_demodulation,[],[f1243,f1424])).

fof(f1243,plain,(
    ! [X3] :
      ( sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | sK1 = k1_tops_1(sK0,sK1) ) ),
    inference(subsumption_resolution,[],[f1239,f125])).

fof(f125,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    inference(resolution,[],[f106,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f106,plain,(
    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f88,f48])).

fof(f48,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f88,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f49,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

fof(f1239,plain,(
    ! [X3] :
      ( sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | sK1 = k1_tops_1(sK0,sK1) ) ),
    inference(superposition,[],[f62,f403])).

fof(f403,plain,(
    ! [X0] :
      ( k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | sK1 = k1_tops_1(sK0,sK1) ) ),
    inference(subsumption_resolution,[],[f402,f48])).

fof(f402,plain,(
    ! [X0] :
      ( sK1 = k1_tops_1(sK0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),sK1) ) ),
    inference(resolution,[],[f177,f47])).

fof(f47,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f177,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X1)
      | sK1 = k1_tops_1(sK0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),sK1) ) ),
    inference(forward_demodulation,[],[f174,f133])).

fof(f174,plain,(
    ! [X0,X1] :
      ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
      | sK1 = k1_tops_1(sK0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1) ) ),
    inference(backward_demodulation,[],[f121,f161])).

fof(f161,plain,(
    ! [X8] : k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X8) = k4_xboole_0(k2_pre_topc(sK0,sK1),X8) ),
    inference(resolution,[],[f114,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f114,plain,(
    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f94,f48])).

fof(f94,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f49,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f121,plain,(
    ! [X0,X1] :
      ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | sK1 = k1_tops_1(sK0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1) ) ),
    inference(subsumption_resolution,[],[f120,f48])).

fof(f120,plain,(
    ! [X0,X1] :
      ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | sK1 = k1_tops_1(sK0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(sK0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1) ) ),
    inference(subsumption_resolution,[],[f119,f49])).

fof(f119,plain,(
    ! [X0,X1] :
      ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | sK1 = k1_tops_1(sK0,sK1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(sK0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1) ) ),
    inference(resolution,[],[f50,f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_tops_1(X1,X3) = X3
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
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

fof(f50,plain,
    ( v3_pre_topc(sK1,sK0)
    | k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f354,plain,(
    ! [X2] :
      ( k2_tops_1(sK0,X2) = k4_xboole_0(k2_pre_topc(sK0,X2),k1_tops_1(sK0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f349,f86])).

fof(f86,plain,(
    ! [X10] :
      ( ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(k2_pre_topc(sK0,X10),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f48,f65])).

fof(f349,plain,(
    ! [X2] :
      ( k2_tops_1(sK0,X2) = k4_xboole_0(k2_pre_topc(sK0,X2),k1_tops_1(sK0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(k2_pre_topc(sK0,X2),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(superposition,[],[f82,f70])).

fof(f82,plain,(
    ! [X2] :
      ( k2_tops_1(sK0,X2) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X2),k1_tops_1(sK0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f48,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

fof(f133,plain,(
    k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),sK1) ),
    inference(resolution,[],[f125,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f134,plain,(
    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),sK1)) ),
    inference(resolution,[],[f125,f62])).

fof(f1424,plain,(
    k1_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f1413,f1422])).

fof(f1422,plain,(
    k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f1412,f297])).

fof(f297,plain,(
    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f289,f114])).

fof(f289,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f108,f70])).

fof(f108,plain,(
    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f90,f48])).

fof(f90,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f49,f57])).

fof(f1412,plain,(
    k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k3_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f1123,f61])).

fof(f1123,plain,(
    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    inference(superposition,[],[f143,f253])).

fof(f253,plain,(
    k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f252,f48])).

fof(f252,plain,
    ( k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f249,f49])).

fof(f249,plain,
    ( k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(superposition,[],[f104,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

fof(f104,plain,(
    ! [X8] : k7_subset_1(u1_struct_0(sK0),sK1,X8) = k4_xboole_0(sK1,X8) ),
    inference(resolution,[],[f49,f70])).

fof(f143,plain,(
    ! [X3] : m1_subset_1(k4_xboole_0(sK1,X3),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    inference(backward_demodulation,[],[f139,f140])).

fof(f140,plain,(
    ! [X4] : k4_xboole_0(sK1,X4) = k7_subset_1(k2_pre_topc(sK0,sK1),sK1,X4) ),
    inference(resolution,[],[f125,f70])).

fof(f139,plain,(
    ! [X3] : m1_subset_1(k7_subset_1(k2_pre_topc(sK0,sK1),sK1,X3),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    inference(resolution,[],[f125,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_subset_1)).

fof(f1413,plain,(
    k1_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))) ),
    inference(resolution,[],[f1123,f62])).

fof(f113,plain,(
    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f112,f47])).

fof(f112,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f93,f48])).

fof(f93,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f49,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f2121,plain,(
    ~ v3_pre_topc(sK1,sK0) ),
    inference(trivial_inequality_removal,[],[f2113])).

fof(f2113,plain,
    ( k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f142,f2109])).

fof(f142,plain,
    ( k2_tops_1(sK0,sK1) != k3_subset_1(k2_pre_topc(sK0,sK1),sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f123,f133])).

fof(f123,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f122,f114])).

fof(f122,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f51,f70])).

fof(f51,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f45])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:31:39 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.46  % (4842)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.19/0.47  % (4839)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.19/0.47  % (4852)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.19/0.48  % (4860)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.19/0.48  % (4848)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.19/0.49  % (4857)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.19/0.49  % (4841)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.19/0.49  % (4844)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.19/0.49  % (4861)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.19/0.49  % (4853)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.19/0.50  % (4849)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.19/0.50  % (4858)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.19/0.50  % (4846)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.19/0.50  % (4840)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.19/0.50  % (4840)Refutation not found, incomplete strategy% (4840)------------------------------
% 0.19/0.50  % (4840)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (4840)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.50  
% 0.19/0.50  % (4840)Memory used [KB]: 10618
% 0.19/0.50  % (4840)Time elapsed: 0.094 s
% 0.19/0.50  % (4840)------------------------------
% 0.19/0.50  % (4840)------------------------------
% 0.19/0.50  % (4850)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.19/0.50  % (4851)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.19/0.50  % (4856)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.19/0.51  % (4838)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.19/0.52  % (4837)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.19/0.52  % (4862)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.19/0.52  % (4862)Refutation not found, incomplete strategy% (4862)------------------------------
% 0.19/0.52  % (4862)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.52  % (4862)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.52  
% 0.19/0.52  % (4862)Memory used [KB]: 10618
% 0.19/0.52  % (4862)Time elapsed: 0.083 s
% 0.19/0.52  % (4862)------------------------------
% 0.19/0.52  % (4862)------------------------------
% 0.19/0.52  % (4845)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.19/0.52  % (4855)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.19/0.53  % (4854)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.19/0.54  % (4859)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.19/0.60  % (4850)Refutation found. Thanks to Tanya!
% 0.19/0.60  % SZS status Theorem for theBenchmark
% 0.19/0.60  % SZS output start Proof for theBenchmark
% 0.19/0.60  fof(f2220,plain,(
% 0.19/0.60    $false),
% 0.19/0.60    inference(subsumption_resolution,[],[f2121,f2125])).
% 0.19/0.60  fof(f2125,plain,(
% 0.19/0.60    v3_pre_topc(sK1,sK0)),
% 0.19/0.60    inference(backward_demodulation,[],[f113,f2122])).
% 0.19/0.60  fof(f2122,plain,(
% 0.19/0.60    sK1 = k1_tops_1(sK0,sK1)),
% 0.19/0.60    inference(backward_demodulation,[],[f1424,f2111])).
% 0.19/0.60  fof(f2111,plain,(
% 0.19/0.60    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))),
% 0.19/0.60    inference(backward_demodulation,[],[f134,f2109])).
% 0.19/0.60  fof(f2109,plain,(
% 0.19/0.60    k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),sK1)),
% 0.19/0.60    inference(backward_demodulation,[],[f133,f2108])).
% 0.19/0.60  fof(f2108,plain,(
% 0.19/0.60    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)),
% 0.19/0.60    inference(subsumption_resolution,[],[f2104,f49])).
% 0.19/0.60  fof(f49,plain,(
% 0.19/0.60    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.19/0.60    inference(cnf_transformation,[],[f45])).
% 0.19/0.60  fof(f45,plain,(
% 0.19/0.60    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.19/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f42,f44,f43])).
% 0.19/0.60  fof(f43,plain,(
% 0.19/0.60    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.19/0.60    introduced(choice_axiom,[])).
% 0.19/0.60  fof(f44,plain,(
% 0.19/0.60    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.19/0.60    introduced(choice_axiom,[])).
% 0.19/0.60  fof(f42,plain,(
% 0.19/0.60    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.19/0.60    inference(flattening,[],[f41])).
% 0.19/0.60  fof(f41,plain,(
% 0.19/0.60    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.19/0.60    inference(nnf_transformation,[],[f22])).
% 0.19/0.60  fof(f22,plain,(
% 0.19/0.60    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.19/0.60    inference(flattening,[],[f21])).
% 0.19/0.60  fof(f21,plain,(
% 0.19/0.60    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.19/0.60    inference(ennf_transformation,[],[f20])).
% 0.19/0.60  fof(f20,negated_conjecture,(
% 0.19/0.60    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 0.19/0.60    inference(negated_conjecture,[],[f19])).
% 0.19/0.60  fof(f19,conjecture,(
% 0.19/0.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 0.19/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).
% 0.19/0.60  fof(f2104,plain,(
% 0.19/0.60    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)),
% 0.19/0.60    inference(condensation,[],[f2091])).
% 0.19/0.60  fof(f2091,plain,(
% 0.19/0.60    ( ! [X17] : (k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.19/0.60    inference(superposition,[],[f354,f1426])).
% 0.19/0.60  fof(f1426,plain,(
% 0.19/0.60    ( ! [X3] : (sK1 = k1_tops_1(sK0,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.19/0.60    inference(duplicate_literal_removal,[],[f1425])).
% 0.19/0.60  fof(f1425,plain,(
% 0.19/0.60    ( ! [X3] : (sK1 = k1_tops_1(sK0,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = k1_tops_1(sK0,sK1)) )),
% 0.19/0.60    inference(backward_demodulation,[],[f1243,f1424])).
% 0.19/0.60  fof(f1243,plain,(
% 0.19/0.60    ( ! [X3] : (sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = k1_tops_1(sK0,sK1)) )),
% 0.19/0.60    inference(subsumption_resolution,[],[f1239,f125])).
% 0.19/0.60  fof(f125,plain,(
% 0.19/0.60    m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 0.19/0.60    inference(resolution,[],[f106,f67])).
% 0.19/0.60  fof(f67,plain,(
% 0.19/0.60    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.19/0.60    inference(cnf_transformation,[],[f46])).
% 0.19/0.60  fof(f46,plain,(
% 0.19/0.60    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.19/0.60    inference(nnf_transformation,[],[f11])).
% 0.19/0.60  fof(f11,axiom,(
% 0.19/0.60    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.19/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.19/0.60  fof(f106,plain,(
% 0.19/0.60    r1_tarski(sK1,k2_pre_topc(sK0,sK1))),
% 0.19/0.60    inference(subsumption_resolution,[],[f88,f48])).
% 0.19/0.60  fof(f48,plain,(
% 0.19/0.60    l1_pre_topc(sK0)),
% 0.19/0.60    inference(cnf_transformation,[],[f45])).
% 0.19/0.60  fof(f88,plain,(
% 0.19/0.60    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 0.19/0.60    inference(resolution,[],[f49,f55])).
% 0.19/0.60  fof(f55,plain,(
% 0.19/0.60    ( ! [X0,X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.19/0.60    inference(cnf_transformation,[],[f23])).
% 0.19/0.60  fof(f23,plain,(
% 0.19/0.60    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.19/0.60    inference(ennf_transformation,[],[f14])).
% 0.19/0.60  fof(f14,axiom,(
% 0.19/0.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 0.19/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).
% 0.19/0.60  fof(f1239,plain,(
% 0.19/0.60    ( ! [X3] : (sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = k1_tops_1(sK0,sK1)) )),
% 0.19/0.60    inference(superposition,[],[f62,f403])).
% 0.19/0.60  fof(f403,plain,(
% 0.19/0.60    ( ! [X0] : (k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = k1_tops_1(sK0,sK1)) )),
% 0.19/0.60    inference(subsumption_resolution,[],[f402,f48])).
% 0.19/0.60  fof(f402,plain,(
% 0.19/0.60    ( ! [X0] : (sK1 = k1_tops_1(sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),sK1)) )),
% 0.19/0.60    inference(resolution,[],[f177,f47])).
% 0.19/0.60  fof(f47,plain,(
% 0.19/0.60    v2_pre_topc(sK0)),
% 0.19/0.60    inference(cnf_transformation,[],[f45])).
% 0.19/0.60  fof(f177,plain,(
% 0.19/0.60    ( ! [X0,X1] : (~v2_pre_topc(X1) | sK1 = k1_tops_1(sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),sK1)) )),
% 0.19/0.60    inference(forward_demodulation,[],[f174,f133])).
% 0.19/0.60  fof(f174,plain,(
% 0.19/0.60    ( ! [X0,X1] : (k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | sK1 = k1_tops_1(sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) )),
% 0.19/0.60    inference(backward_demodulation,[],[f121,f161])).
% 0.19/0.60  fof(f161,plain,(
% 0.19/0.60    ( ! [X8] : (k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X8) = k4_xboole_0(k2_pre_topc(sK0,sK1),X8)) )),
% 0.19/0.60    inference(resolution,[],[f114,f70])).
% 0.19/0.60  fof(f70,plain,(
% 0.19/0.60    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.19/0.60    inference(cnf_transformation,[],[f38])).
% 0.19/0.60  fof(f38,plain,(
% 0.19/0.60    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.60    inference(ennf_transformation,[],[f8])).
% 0.19/0.60  fof(f8,axiom,(
% 0.19/0.60    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.19/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.19/0.60  fof(f114,plain,(
% 0.19/0.60    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.19/0.60    inference(subsumption_resolution,[],[f94,f48])).
% 0.19/0.60  fof(f94,plain,(
% 0.19/0.60    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 0.19/0.60    inference(resolution,[],[f49,f65])).
% 0.19/0.60  fof(f65,plain,(
% 0.19/0.60    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.19/0.60    inference(cnf_transformation,[],[f35])).
% 0.19/0.60  fof(f35,plain,(
% 0.19/0.60    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.19/0.60    inference(flattening,[],[f34])).
% 0.19/0.60  fof(f34,plain,(
% 0.19/0.60    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.19/0.60    inference(ennf_transformation,[],[f13])).
% 0.19/0.60  fof(f13,axiom,(
% 0.19/0.60    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.19/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 0.19/0.60  fof(f121,plain,(
% 0.19/0.60    ( ! [X0,X1] : (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | sK1 = k1_tops_1(sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) )),
% 0.19/0.60    inference(subsumption_resolution,[],[f120,f48])).
% 0.19/0.60  fof(f120,plain,(
% 0.19/0.60    ( ! [X0,X1] : (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | sK1 = k1_tops_1(sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(sK0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) )),
% 0.19/0.60    inference(subsumption_resolution,[],[f119,f49])).
% 0.19/0.60  fof(f119,plain,(
% 0.19/0.60    ( ! [X0,X1] : (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | sK1 = k1_tops_1(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(sK0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) )),
% 0.19/0.60    inference(resolution,[],[f50,f58])).
% 0.19/0.60  fof(f58,plain,(
% 0.19/0.60    ( ! [X2,X0,X3,X1] : (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.19/0.60    inference(cnf_transformation,[],[f27])).
% 0.19/0.60  fof(f27,plain,(
% 0.19/0.60    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.19/0.60    inference(flattening,[],[f26])).
% 0.19/0.60  fof(f26,plain,(
% 0.19/0.60    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.19/0.60    inference(ennf_transformation,[],[f17])).
% 0.19/0.60  fof(f17,axiom,(
% 0.19/0.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 0.19/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_1)).
% 0.19/0.60  fof(f50,plain,(
% 0.19/0.60    v3_pre_topc(sK1,sK0) | k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)),
% 0.19/0.60    inference(cnf_transformation,[],[f45])).
% 0.19/0.60  fof(f62,plain,(
% 0.19/0.60    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.19/0.60    inference(cnf_transformation,[],[f30])).
% 0.19/0.60  fof(f30,plain,(
% 0.19/0.60    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.60    inference(ennf_transformation,[],[f7])).
% 0.19/0.60  fof(f7,axiom,(
% 0.19/0.60    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.19/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.19/0.60  fof(f354,plain,(
% 0.19/0.60    ( ! [X2] : (k2_tops_1(sK0,X2) = k4_xboole_0(k2_pre_topc(sK0,X2),k1_tops_1(sK0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.19/0.60    inference(subsumption_resolution,[],[f349,f86])).
% 0.19/0.60  fof(f86,plain,(
% 0.19/0.60    ( ! [X10] : (~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(k2_pre_topc(sK0,X10),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.19/0.60    inference(resolution,[],[f48,f65])).
% 0.19/0.60  fof(f349,plain,(
% 0.19/0.60    ( ! [X2] : (k2_tops_1(sK0,X2) = k4_xboole_0(k2_pre_topc(sK0,X2),k1_tops_1(sK0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k2_pre_topc(sK0,X2),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.19/0.60    inference(superposition,[],[f82,f70])).
% 0.19/0.60  fof(f82,plain,(
% 0.19/0.60    ( ! [X2] : (k2_tops_1(sK0,X2) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X2),k1_tops_1(sK0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.19/0.60    inference(resolution,[],[f48,f57])).
% 0.19/0.60  fof(f57,plain,(
% 0.19/0.60    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.19/0.60    inference(cnf_transformation,[],[f25])).
% 0.19/0.60  fof(f25,plain,(
% 0.19/0.60    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.19/0.60    inference(ennf_transformation,[],[f16])).
% 0.19/0.60  fof(f16,axiom,(
% 0.19/0.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 0.19/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).
% 0.19/0.60  fof(f133,plain,(
% 0.19/0.60    k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),sK1)),
% 0.19/0.60    inference(resolution,[],[f125,f61])).
% 0.19/0.60  fof(f61,plain,(
% 0.19/0.60    ( ! [X0,X1] : (k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.19/0.60    inference(cnf_transformation,[],[f29])).
% 0.19/0.60  fof(f29,plain,(
% 0.19/0.60    ! [X0,X1] : (k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.60    inference(ennf_transformation,[],[f2])).
% 0.19/0.60  fof(f2,axiom,(
% 0.19/0.60    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1))),
% 0.19/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 0.19/0.60  fof(f134,plain,(
% 0.19/0.60    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),sK1))),
% 0.19/0.60    inference(resolution,[],[f125,f62])).
% 0.19/0.60  fof(f1424,plain,(
% 0.19/0.60    k1_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))),
% 0.19/0.60    inference(forward_demodulation,[],[f1413,f1422])).
% 0.19/0.60  fof(f1422,plain,(
% 0.19/0.60    k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 0.19/0.60    inference(forward_demodulation,[],[f1412,f297])).
% 0.19/0.60  fof(f297,plain,(
% 0.19/0.60    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 0.19/0.60    inference(subsumption_resolution,[],[f289,f114])).
% 0.19/0.60  fof(f289,plain,(
% 0.19/0.60    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.19/0.60    inference(superposition,[],[f108,f70])).
% 0.19/0.60  fof(f108,plain,(
% 0.19/0.60    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 0.19/0.60    inference(subsumption_resolution,[],[f90,f48])).
% 0.19/0.60  fof(f90,plain,(
% 0.19/0.60    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 0.19/0.60    inference(resolution,[],[f49,f57])).
% 0.19/0.60  fof(f1412,plain,(
% 0.19/0.60    k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k3_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 0.19/0.60    inference(resolution,[],[f1123,f61])).
% 0.19/0.60  fof(f1123,plain,(
% 0.19/0.60    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 0.19/0.60    inference(superposition,[],[f143,f253])).
% 0.19/0.60  fof(f253,plain,(
% 0.19/0.60    k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 0.19/0.60    inference(subsumption_resolution,[],[f252,f48])).
% 0.19/0.60  fof(f252,plain,(
% 0.19/0.60    k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 0.19/0.60    inference(subsumption_resolution,[],[f249,f49])).
% 0.19/0.60  fof(f249,plain,(
% 0.19/0.60    k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 0.19/0.60    inference(superposition,[],[f104,f56])).
% 0.19/0.60  fof(f56,plain,(
% 0.19/0.60    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.19/0.60    inference(cnf_transformation,[],[f24])).
% 0.19/0.60  fof(f24,plain,(
% 0.19/0.60    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.19/0.60    inference(ennf_transformation,[],[f18])).
% 0.19/0.60  fof(f18,axiom,(
% 0.19/0.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 0.19/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).
% 0.19/0.60  fof(f104,plain,(
% 0.19/0.60    ( ! [X8] : (k7_subset_1(u1_struct_0(sK0),sK1,X8) = k4_xboole_0(sK1,X8)) )),
% 0.19/0.60    inference(resolution,[],[f49,f70])).
% 0.19/0.60  fof(f143,plain,(
% 0.19/0.60    ( ! [X3] : (m1_subset_1(k4_xboole_0(sK1,X3),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))) )),
% 0.19/0.60    inference(backward_demodulation,[],[f139,f140])).
% 0.19/0.60  fof(f140,plain,(
% 0.19/0.60    ( ! [X4] : (k4_xboole_0(sK1,X4) = k7_subset_1(k2_pre_topc(sK0,sK1),sK1,X4)) )),
% 0.19/0.60    inference(resolution,[],[f125,f70])).
% 0.19/0.60  fof(f139,plain,(
% 0.19/0.60    ( ! [X3] : (m1_subset_1(k7_subset_1(k2_pre_topc(sK0,sK1),sK1,X3),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))) )),
% 0.19/0.60    inference(resolution,[],[f125,f69])).
% 0.19/0.60  fof(f69,plain,(
% 0.19/0.60    ( ! [X2,X0,X1] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.19/0.60    inference(cnf_transformation,[],[f37])).
% 0.19/0.60  fof(f37,plain,(
% 0.19/0.60    ! [X0,X1,X2] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.60    inference(ennf_transformation,[],[f5])).
% 0.19/0.60  fof(f5,axiom,(
% 0.19/0.60    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.19/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_subset_1)).
% 0.19/0.60  fof(f1413,plain,(
% 0.19/0.60    k1_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)))),
% 0.19/0.60    inference(resolution,[],[f1123,f62])).
% 0.19/0.60  fof(f113,plain,(
% 0.19/0.60    v3_pre_topc(k1_tops_1(sK0,sK1),sK0)),
% 0.19/0.60    inference(subsumption_resolution,[],[f112,f47])).
% 0.19/0.60  fof(f112,plain,(
% 0.19/0.60    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | ~v2_pre_topc(sK0)),
% 0.19/0.60    inference(subsumption_resolution,[],[f93,f48])).
% 0.19/0.60  fof(f93,plain,(
% 0.19/0.60    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.19/0.60    inference(resolution,[],[f49,f64])).
% 0.19/0.60  fof(f64,plain,(
% 0.19/0.60    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.19/0.60    inference(cnf_transformation,[],[f33])).
% 0.19/0.60  fof(f33,plain,(
% 0.19/0.60    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.19/0.60    inference(flattening,[],[f32])).
% 0.19/0.60  fof(f32,plain,(
% 0.19/0.60    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.19/0.60    inference(ennf_transformation,[],[f15])).
% 0.19/0.60  fof(f15,axiom,(
% 0.19/0.60    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 0.19/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).
% 0.19/0.60  fof(f2121,plain,(
% 0.19/0.60    ~v3_pre_topc(sK1,sK0)),
% 0.19/0.60    inference(trivial_inequality_removal,[],[f2113])).
% 0.19/0.60  fof(f2113,plain,(
% 0.19/0.60    k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0)),
% 0.19/0.60    inference(backward_demodulation,[],[f142,f2109])).
% 0.19/0.60  fof(f142,plain,(
% 0.19/0.60    k2_tops_1(sK0,sK1) != k3_subset_1(k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)),
% 0.19/0.60    inference(backward_demodulation,[],[f123,f133])).
% 0.19/0.60  fof(f123,plain,(
% 0.19/0.60    k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)),
% 0.19/0.60    inference(subsumption_resolution,[],[f122,f114])).
% 0.19/0.60  fof(f122,plain,(
% 0.19/0.60    k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.19/0.60    inference(superposition,[],[f51,f70])).
% 0.19/0.60  fof(f51,plain,(
% 0.19/0.60    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)),
% 0.19/0.60    inference(cnf_transformation,[],[f45])).
% 0.19/0.60  % SZS output end Proof for theBenchmark
% 0.19/0.60  % (4850)------------------------------
% 0.19/0.60  % (4850)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.60  % (4850)Termination reason: Refutation
% 0.19/0.60  
% 0.19/0.60  % (4850)Memory used [KB]: 3070
% 0.19/0.60  % (4850)Time elapsed: 0.193 s
% 0.19/0.60  % (4850)------------------------------
% 0.19/0.60  % (4850)------------------------------
% 0.19/0.60  % (4835)Success in time 0.247 s
%------------------------------------------------------------------------------
