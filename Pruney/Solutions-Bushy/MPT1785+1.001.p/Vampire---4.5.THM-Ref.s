%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1785+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:32 EST 2020

% Result     : Theorem 1.80s
% Output     : Refutation 1.80s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 639 expanded)
%              Number of leaves         :   19 ( 203 expanded)
%              Depth                    :   15
%              Number of atoms          :  393 (2806 expanded)
%              Number of equality atoms :   59 ( 112 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f624,plain,(
    $false ),
    inference(subsumption_resolution,[],[f623,f103])).

fof(f103,plain,(
    ~ r2_hidden(sK3(a_2_1_tmap_1(sK0,sK1),k5_tmap_1(sK0,sK1)),k5_tmap_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f58,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f26,f44])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f58,plain,(
    ~ r1_tarski(a_2_1_tmap_1(sK0,sK1),k5_tmap_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( ~ r1_tarski(a_2_1_tmap_1(sK0,sK1),k5_tmap_1(sK0,sK1))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f40,f39])).

fof(f39,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(a_2_1_tmap_1(X0,X1),k5_tmap_1(X0,X1))
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(a_2_1_tmap_1(sK0,X1),k5_tmap_1(sK0,X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X1] :
        ( ~ r1_tarski(a_2_1_tmap_1(sK0,X1),k5_tmap_1(sK0,X1))
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ r1_tarski(a_2_1_tmap_1(sK0,sK1),k5_tmap_1(sK0,sK1))
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(a_2_1_tmap_1(X0,X1),k5_tmap_1(X0,X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(a_2_1_tmap_1(X0,X1),k5_tmap_1(X0,X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => r1_tarski(a_2_1_tmap_1(X0,X1),k5_tmap_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(a_2_1_tmap_1(X0,X1),k5_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_tmap_1)).

fof(f623,plain,(
    r2_hidden(sK3(a_2_1_tmap_1(sK0,sK1),k5_tmap_1(sK0,sK1)),k5_tmap_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f622,f513])).

fof(f513,plain,(
    sK3(a_2_1_tmap_1(sK0,sK1),k5_tmap_1(sK0,sK1)) = k3_xboole_0(sK1,sK4(sK3(a_2_1_tmap_1(sK0,sK1),k5_tmap_1(sK0,sK1)),sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f102,f184])).

fof(f184,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,a_2_1_tmap_1(sK0,sK1))
      | k3_xboole_0(sK1,sK4(X1,sK0,sK1)) = X1 ) ),
    inference(forward_demodulation,[],[f183,f65])).

fof(f65,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f183,plain,(
    ! [X1] :
      ( k3_xboole_0(sK4(X1,sK0,sK1),sK1) = X1
      | ~ r2_hidden(X1,a_2_1_tmap_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f182,f54])).

fof(f54,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f182,plain,(
    ! [X1] :
      ( k3_xboole_0(sK4(X1,sK0,sK1),sK1) = X1
      | ~ r2_hidden(X1,a_2_1_tmap_1(sK0,sK1))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f181,f55])).

fof(f55,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f181,plain,(
    ! [X1] :
      ( k3_xboole_0(sK4(X1,sK0,sK1),sK1) = X1
      | ~ r2_hidden(X1,a_2_1_tmap_1(sK0,sK1))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f180,f56])).

fof(f56,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f180,plain,(
    ! [X1] :
      ( k3_xboole_0(sK4(X1,sK0,sK1),sK1) = X1
      | ~ r2_hidden(X1,a_2_1_tmap_1(sK0,sK1))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f174,f57])).

fof(f57,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f41])).

fof(f174,plain,(
    ! [X1] :
      ( k3_xboole_0(sK4(X1,sK0,sK1),sK1) = X1
      | ~ r2_hidden(X1,a_2_1_tmap_1(sK0,sK1))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f90,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(u1_struct_0(X1),sK4(X0,X1,X2),X2) = X0
      | ~ r2_hidden(X0,a_2_1_tmap_1(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_tmap_1(X1,X2))
          | ! [X3] :
              ( ~ r2_hidden(X3,u1_pre_topc(X1))
              | k9_subset_1(u1_struct_0(X1),X3,X2) != X0
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
        & ( ( r2_hidden(sK4(X0,X1,X2),u1_pre_topc(X1))
            & k9_subset_1(u1_struct_0(X1),sK4(X0,X1,X2),X2) = X0
            & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ r2_hidden(X0,a_2_1_tmap_1(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f47,f48])).

fof(f48,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,u1_pre_topc(X1))
          & k9_subset_1(u1_struct_0(X1),X4,X2) = X0
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( r2_hidden(sK4(X0,X1,X2),u1_pre_topc(X1))
        & k9_subset_1(u1_struct_0(X1),sK4(X0,X1,X2),X2) = X0
        & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_tmap_1(X1,X2))
          | ! [X3] :
              ( ~ r2_hidden(X3,u1_pre_topc(X1))
              | k9_subset_1(u1_struct_0(X1),X3,X2) != X0
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,u1_pre_topc(X1))
              & k9_subset_1(u1_struct_0(X1),X4,X2) = X0
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ r2_hidden(X0,a_2_1_tmap_1(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_tmap_1(X1,X2))
          | ! [X3] :
              ( ~ r2_hidden(X3,u1_pre_topc(X1))
              | k9_subset_1(u1_struct_0(X1),X3,X2) != X0
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,u1_pre_topc(X1))
              & k9_subset_1(u1_struct_0(X1),X3,X2) = X0
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ r2_hidden(X0,a_2_1_tmap_1(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_tmap_1(X1,X2))
      <=> ? [X3] :
            ( r2_hidden(X3,u1_pre_topc(X1))
            & k9_subset_1(u1_struct_0(X1),X3,X2) = X0
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_tmap_1(X1,X2))
      <=> ? [X3] :
            ( r2_hidden(X3,u1_pre_topc(X1))
            & k9_subset_1(u1_struct_0(X1),X3,X2) = X0
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_1_tmap_1(X1,X2))
      <=> ? [X3] :
            ( r2_hidden(X3,u1_pre_topc(X1))
            & k9_subset_1(u1_struct_0(X1),X3,X2) = X0
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_1_tmap_1)).

fof(f90,plain,(
    ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK1) = k3_xboole_0(X0,sK1) ),
    inference(unit_resulting_resolution,[],[f57,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f102,plain,(
    r2_hidden(sK3(a_2_1_tmap_1(sK0,sK1),k5_tmap_1(sK0,sK1)),a_2_1_tmap_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f58,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f622,plain,(
    r2_hidden(k3_xboole_0(sK1,sK4(sK3(a_2_1_tmap_1(sK0,sK1),k5_tmap_1(sK0,sK1)),sK0,sK1)),k5_tmap_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f621,f65])).

fof(f621,plain,(
    r2_hidden(k3_xboole_0(sK4(sK3(a_2_1_tmap_1(sK0,sK1),k5_tmap_1(sK0,sK1)),sK0,sK1),sK1),k5_tmap_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f620,f251])).

fof(f251,plain,(
    ! [X0] : k3_xboole_0(X0,sK1) = k4_subset_1(u1_struct_0(sK0),k1_xboole_0,k3_xboole_0(X0,sK1)) ),
    inference(backward_demodulation,[],[f226,f250])).

fof(f250,plain,(
    ! [X0] : k3_xboole_0(X0,sK1) = k2_xboole_0(k1_xboole_0,k3_xboole_0(X0,sK1)) ),
    inference(backward_demodulation,[],[f241,f249])).

fof(f249,plain,(
    ! [X0] : k3_xboole_0(X0,sK1) = k4_subset_1(u1_struct_0(sK0),k3_xboole_0(X0,sK1),k1_xboole_0) ),
    inference(forward_demodulation,[],[f222,f60])).

fof(f60,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f222,plain,(
    ! [X0] : k4_subset_1(u1_struct_0(sK0),k3_xboole_0(X0,sK1),k1_xboole_0) = k2_xboole_0(k3_xboole_0(X0,sK1),k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f101,f106,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f106,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f87,f85,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f85,plain,(
    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(unit_resulting_resolution,[],[f56,f61])).

fof(f61,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f87,plain,(
    r2_hidden(k1_xboole_0,u1_pre_topc(sK0)) ),
    inference(unit_resulting_resolution,[],[f55,f56,f63])).

fof(f63,plain,(
    ! [X0] :
      ( r2_hidden(k1_xboole_0,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( r2_hidden(k1_xboole_0,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( r2_hidden(k1_xboole_0,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => r2_hidden(k1_xboole_0,u1_pre_topc(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_pre_topc)).

fof(f101,plain,(
    ! [X0] : m1_subset_1(k3_xboole_0(X0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f89,f90])).

fof(f89,plain,(
    ! [X0] : m1_subset_1(k9_subset_1(u1_struct_0(sK0),X0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f57,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f241,plain,(
    ! [X0] : k4_subset_1(u1_struct_0(sK0),k3_xboole_0(X0,sK1),k1_xboole_0) = k2_xboole_0(k1_xboole_0,k3_xboole_0(X0,sK1)) ),
    inference(backward_demodulation,[],[f234,f226])).

fof(f234,plain,(
    ! [X0] : k4_subset_1(u1_struct_0(sK0),k3_xboole_0(X0,sK1),k1_xboole_0) = k4_subset_1(u1_struct_0(sK0),k1_xboole_0,k3_xboole_0(X0,sK1)) ),
    inference(unit_resulting_resolution,[],[f101,f106,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k4_subset_1)).

fof(f226,plain,(
    ! [X0] : k4_subset_1(u1_struct_0(sK0),k1_xboole_0,k3_xboole_0(X0,sK1)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(X0,sK1)) ),
    inference(unit_resulting_resolution,[],[f101,f106,f81])).

fof(f620,plain,(
    r2_hidden(k4_subset_1(u1_struct_0(sK0),k1_xboole_0,k3_xboole_0(sK4(sK3(a_2_1_tmap_1(sK0,sK1),k5_tmap_1(sK0,sK1)),sK0,sK1),sK1)),k5_tmap_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f619,f90])).

fof(f619,plain,(
    r2_hidden(k4_subset_1(u1_struct_0(sK0),k1_xboole_0,k9_subset_1(u1_struct_0(sK0),sK4(sK3(a_2_1_tmap_1(sK0,sK1),k5_tmap_1(sK0,sK1)),sK0,sK1),sK1)),k5_tmap_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f547,f88])).

fof(f88,plain,(
    k5_tmap_1(sK0,sK1) = a_2_0_tmap_1(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f54,f55,f56,f57,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k5_tmap_1(X0,X1) = a_2_0_tmap_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k5_tmap_1(X0,X1) = a_2_0_tmap_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k5_tmap_1(X0,X1) = a_2_0_tmap_1(X0,X1)
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
         => k5_tmap_1(X0,X1) = a_2_0_tmap_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_tmap_1)).

fof(f547,plain,(
    r2_hidden(k4_subset_1(u1_struct_0(sK0),k1_xboole_0,k9_subset_1(u1_struct_0(sK0),sK4(sK3(a_2_1_tmap_1(sK0,sK1),k5_tmap_1(sK0,sK1)),sK0,sK1),sK1)),a_2_0_tmap_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f54,f55,f56,f57,f87,f106,f279,f277,f84])).

fof(f84,plain,(
    ! [X4,X2,X3,X1] :
      ( r2_hidden(k4_subset_1(u1_struct_0(X1),X3,k9_subset_1(u1_struct_0(X1),X4,X2)),a_2_0_tmap_1(X1,X2))
      | ~ r2_hidden(X4,u1_pre_topc(X1))
      | ~ r2_hidden(X3,u1_pre_topc(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_0_tmap_1(X1,X2))
      | ~ r2_hidden(X4,u1_pre_topc(X1))
      | ~ r2_hidden(X3,u1_pre_topc(X1))
      | k4_subset_1(u1_struct_0(X1),X3,k9_subset_1(u1_struct_0(X1),X4,X2)) != X0
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_tmap_1(X1,X2))
          | ! [X3,X4] :
              ( ~ r2_hidden(X4,u1_pre_topc(X1))
              | ~ r2_hidden(X3,u1_pre_topc(X1))
              | k4_subset_1(u1_struct_0(X1),X3,k9_subset_1(u1_struct_0(X1),X4,X2)) != X0
              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
        & ( ( r2_hidden(sK6(X0,X1,X2),u1_pre_topc(X1))
            & r2_hidden(sK5(X0,X1,X2),u1_pre_topc(X1))
            & k4_subset_1(u1_struct_0(X1),sK5(X0,X1,X2),k9_subset_1(u1_struct_0(X1),sK6(X0,X1,X2),X2)) = X0
            & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
            & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ r2_hidden(X0,a_2_0_tmap_1(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f51,f52])).

fof(f52,plain,(
    ! [X2,X1,X0] :
      ( ? [X5,X6] :
          ( r2_hidden(X6,u1_pre_topc(X1))
          & r2_hidden(X5,u1_pre_topc(X1))
          & k4_subset_1(u1_struct_0(X1),X5,k9_subset_1(u1_struct_0(X1),X6,X2)) = X0
          & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1)))
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( r2_hidden(sK6(X0,X1,X2),u1_pre_topc(X1))
        & r2_hidden(sK5(X0,X1,X2),u1_pre_topc(X1))
        & k4_subset_1(u1_struct_0(X1),sK5(X0,X1,X2),k9_subset_1(u1_struct_0(X1),sK6(X0,X1,X2),X2)) = X0
        & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
        & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_tmap_1(X1,X2))
          | ! [X3,X4] :
              ( ~ r2_hidden(X4,u1_pre_topc(X1))
              | ~ r2_hidden(X3,u1_pre_topc(X1))
              | k4_subset_1(u1_struct_0(X1),X3,k9_subset_1(u1_struct_0(X1),X4,X2)) != X0
              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
        & ( ? [X5,X6] :
              ( r2_hidden(X6,u1_pre_topc(X1))
              & r2_hidden(X5,u1_pre_topc(X1))
              & k4_subset_1(u1_struct_0(X1),X5,k9_subset_1(u1_struct_0(X1),X6,X2)) = X0
              & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1)))
              & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ r2_hidden(X0,a_2_0_tmap_1(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_tmap_1(X1,X2))
          | ! [X3,X4] :
              ( ~ r2_hidden(X4,u1_pre_topc(X1))
              | ~ r2_hidden(X3,u1_pre_topc(X1))
              | k4_subset_1(u1_struct_0(X1),X3,k9_subset_1(u1_struct_0(X1),X4,X2)) != X0
              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
        & ( ? [X3,X4] :
              ( r2_hidden(X4,u1_pre_topc(X1))
              & r2_hidden(X3,u1_pre_topc(X1))
              & k4_subset_1(u1_struct_0(X1),X3,k9_subset_1(u1_struct_0(X1),X4,X2)) = X0
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ r2_hidden(X0,a_2_0_tmap_1(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_tmap_1(X1,X2))
      <=> ? [X3,X4] :
            ( r2_hidden(X4,u1_pre_topc(X1))
            & r2_hidden(X3,u1_pre_topc(X1))
            & k4_subset_1(u1_struct_0(X1),X3,k9_subset_1(u1_struct_0(X1),X4,X2)) = X0
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_tmap_1(X1,X2))
      <=> ? [X3,X4] :
            ( r2_hidden(X4,u1_pre_topc(X1))
            & r2_hidden(X3,u1_pre_topc(X1))
            & k4_subset_1(u1_struct_0(X1),X3,k9_subset_1(u1_struct_0(X1),X4,X2)) = X0
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_0_tmap_1(X1,X2))
      <=> ? [X3,X4] :
            ( r2_hidden(X4,u1_pre_topc(X1))
            & r2_hidden(X3,u1_pre_topc(X1))
            & k4_subset_1(u1_struct_0(X1),X3,k9_subset_1(u1_struct_0(X1),X4,X2)) = X0
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_0_tmap_1)).

fof(f277,plain,(
    m1_subset_1(sK4(sK3(a_2_1_tmap_1(sK0,sK1),k5_tmap_1(sK0,sK1)),sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f54,f55,f56,f57,f102,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r2_hidden(X0,a_2_1_tmap_1(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f279,plain,(
    r2_hidden(sK4(sK3(a_2_1_tmap_1(sK0,sK1),k5_tmap_1(sK0,sK1)),sK0,sK1),u1_pre_topc(sK0)) ),
    inference(unit_resulting_resolution,[],[f54,f55,f56,f57,f102,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),u1_pre_topc(X1))
      | ~ r2_hidden(X0,a_2_1_tmap_1(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f49])).

%------------------------------------------------------------------------------
