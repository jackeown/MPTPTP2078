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
% DateTime   : Thu Dec  3 13:17:59 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 854 expanded)
%              Number of leaves         :   10 ( 148 expanded)
%              Depth                    :   26
%              Number of atoms          :  257 (5436 expanded)
%              Number of equality atoms :   10 (  40 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f210,plain,(
    $false ),
    inference(subsumption_resolution,[],[f209,f201])).

fof(f201,plain,(
    ~ r1_tsep_1(sK1,sK3) ),
    inference(resolution,[],[f200,f24])).

fof(f24,plain,
    ( ~ r1_tsep_1(sK3,sK1)
    | ~ r1_tsep_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0) )
              & m1_pre_topc(X2,X0) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0) )
              & m1_pre_topc(X2,X0) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_pre_topc(X1,X0)
           => ! [X2] :
                ( m1_pre_topc(X2,X0)
               => ! [X3] :
                    ( m1_pre_topc(X3,X0)
                   => ( m1_pre_topc(X1,X2)
                     => ( ( r1_tsep_1(X3,X1)
                          & r1_tsep_1(X1,X3) )
                        | ( ~ r1_tsep_1(X3,X2)
                          & ~ r1_tsep_1(X2,X3) ) ) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
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
                   => ( m1_pre_topc(X1,X2)
                     => ( ( r1_tsep_1(X3,X1)
                          & r1_tsep_1(X1,X3) )
                        | ( ~ r1_tsep_1(X3,X2)
                          & ~ r1_tsep_1(X2,X3) ) ) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,negated_conjecture,(
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
                   => ( m1_pre_topc(X1,X2)
                     => ( ( r1_tsep_1(X3,X1)
                          & r1_tsep_1(X1,X3) )
                        | ( ~ r1_tsep_1(X3,X2)
                          & ~ r1_tsep_1(X2,X3) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
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
                 => ( m1_pre_topc(X1,X2)
                   => ( ( r1_tsep_1(X3,X1)
                        & r1_tsep_1(X1,X3) )
                      | ( ~ r1_tsep_1(X3,X2)
                        & ~ r1_tsep_1(X2,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tmap_1)).

fof(f200,plain,(
    r1_tsep_1(sK3,sK1) ),
    inference(resolution,[],[f198,f176])).

fof(f176,plain,
    ( ~ r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK1))
    | r1_tsep_1(sK3,sK1) ),
    inference(subsumption_resolution,[],[f173,f75])).

fof(f75,plain,(
    l1_struct_0(sK1) ),
    inference(resolution,[],[f74,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f74,plain,(
    l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f71,f30])).

fof(f30,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f71,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK1) ),
    inference(resolution,[],[f29,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f29,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f173,plain,
    ( ~ r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK1))
    | ~ l1_struct_0(sK1)
    | r1_tsep_1(sK3,sK1) ),
    inference(superposition,[],[f116,f95])).

fof(f95,plain,(
    k2_struct_0(sK1) = u1_struct_0(sK1) ),
    inference(resolution,[],[f75,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f116,plain,(
    ! [X1] :
      ( ~ r1_xboole_0(k2_struct_0(sK3),u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | r1_tsep_1(sK3,X1) ) ),
    inference(subsumption_resolution,[],[f114,f64])).

fof(f64,plain,(
    l1_struct_0(sK3) ),
    inference(resolution,[],[f60,f35])).

fof(f60,plain,(
    l1_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f58,f30])).

fof(f58,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK3) ),
    inference(resolution,[],[f26,f34])).

fof(f26,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f114,plain,(
    ! [X1] :
      ( ~ r1_xboole_0(k2_struct_0(sK3),u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(sK3)
      | r1_tsep_1(sK3,X1) ) ),
    inference(superposition,[],[f32,f76])).

fof(f76,plain,(
    k2_struct_0(sK3) = u1_struct_0(sK3) ),
    inference(resolution,[],[f64,f36])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0)
      | r1_tsep_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tsep_1)).

fof(f198,plain,(
    r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK1)) ),
    inference(resolution,[],[f197,f52])).

fof(f52,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f197,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_struct_0(sK3))
      | r1_xboole_0(X0,k2_struct_0(sK1)) ) ),
    inference(resolution,[],[f165,f102])).

fof(f102,plain,(
    r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f101,f76])).

fof(f101,plain,(
    r1_xboole_0(u1_struct_0(sK3),k2_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f100,f85])).

fof(f85,plain,(
    k2_struct_0(sK2) = u1_struct_0(sK2) ),
    inference(resolution,[],[f69,f36])).

fof(f69,plain,(
    l1_struct_0(sK2) ),
    inference(resolution,[],[f68,f35])).

fof(f68,plain,(
    l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f66,f30])).

fof(f66,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK2) ),
    inference(resolution,[],[f28,f34])).

fof(f28,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f100,plain,(
    r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f99,f64])).

fof(f99,plain,
    ( r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ l1_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f97,f69])).

fof(f97,plain,
    ( ~ l1_struct_0(sK2)
    | r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ l1_struct_0(sK3) ),
    inference(resolution,[],[f94,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f94,plain,(
    r1_tsep_1(sK3,sK2) ),
    inference(subsumption_resolution,[],[f93,f69])).

fof(f93,plain,
    ( ~ l1_struct_0(sK2)
    | r1_tsep_1(sK3,sK2) ),
    inference(subsumption_resolution,[],[f88,f64])).

fof(f88,plain,
    ( ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | r1_tsep_1(sK3,sK2) ),
    inference(resolution,[],[f84,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0)
      | r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( r1_tsep_1(X0,X1)
       => r1_tsep_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

fof(f84,plain,(
    r1_tsep_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f83,f64])).

fof(f83,plain,
    ( r1_tsep_1(sK2,sK3)
    | ~ l1_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f79,f69])).

fof(f79,plain,
    ( r1_tsep_1(sK2,sK3)
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK3) ),
    inference(duplicate_literal_removal,[],[f78])).

fof(f78,plain,
    ( r1_tsep_1(sK2,sK3)
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK3)
    | r1_tsep_1(sK2,sK3) ),
    inference(resolution,[],[f25,f31])).

fof(f25,plain,
    ( r1_tsep_1(sK3,sK2)
    | r1_tsep_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f14])).

fof(f165,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,k2_struct_0(sK2))
      | r1_xboole_0(X0,k2_struct_0(sK1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f146,f55])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( ~ sP7(X3,X0)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(general_splitting,[],[f37,f54_D])).

fof(f54,plain,(
    ! [X2,X0,X3] :
      ( ~ r1_tarski(X2,X3)
      | r1_xboole_0(X0,X2)
      | sP7(X3,X0) ) ),
    inference(cnf_transformation,[],[f54_D])).

fof(f54_D,plain,(
    ! [X0,X3] :
      ( ! [X2] :
          ( ~ r1_tarski(X2,X3)
          | r1_xboole_0(X0,X2) )
    <=> ~ sP7(X3,X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP7])])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X2,X3)
      | ~ r1_xboole_0(X1,X3)
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X1,X3)
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_xboole_1)).

fof(f146,plain,(
    ! [X0] :
      ( sP7(k2_struct_0(sK2),X0)
      | r1_xboole_0(X0,k2_struct_0(sK1)) ) ),
    inference(resolution,[],[f134,f54])).

fof(f134,plain,(
    r1_tarski(k2_struct_0(sK1),k2_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f133,f74])).

fof(f133,plain,
    ( r1_tarski(k2_struct_0(sK1),k2_struct_0(sK2))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f62,f68])).

fof(f62,plain,
    ( ~ l1_pre_topc(sK2)
    | r1_tarski(k2_struct_0(sK1),k2_struct_0(sK2))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f27,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X1)
      | r1_tarski(k2_struct_0(X1),k2_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X1,X0)
          <=> ( ! [X2] :
                  ( ( r2_hidden(X2,u1_pre_topc(X1))
                  <=> ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
              & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( r2_hidden(X2,u1_pre_topc(X1))
                  <=> ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) )
              & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_pre_topc)).

fof(f27,plain,(
    m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f209,plain,(
    r1_tsep_1(sK1,sK3) ),
    inference(subsumption_resolution,[],[f208,f64])).

fof(f208,plain,
    ( ~ l1_struct_0(sK3)
    | r1_tsep_1(sK1,sK3) ),
    inference(subsumption_resolution,[],[f203,f75])).

fof(f203,plain,
    ( ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK3)
    | r1_tsep_1(sK1,sK3) ),
    inference(resolution,[],[f200,f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:49:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (7815)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.48  % (7815)Refutation not found, incomplete strategy% (7815)------------------------------
% 0.21/0.48  % (7815)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (7822)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.48  % (7815)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (7815)Memory used [KB]: 1791
% 0.21/0.48  % (7815)Time elapsed: 0.062 s
% 0.21/0.48  % (7815)------------------------------
% 0.21/0.48  % (7815)------------------------------
% 0.21/0.50  % (7813)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.50  % (7821)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (7812)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (7811)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.51  % (7820)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.51  % (7825)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.52  % (7810)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.52  % (7816)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.52  % (7813)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f210,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(subsumption_resolution,[],[f209,f201])).
% 0.21/0.52  fof(f201,plain,(
% 0.21/0.52    ~r1_tsep_1(sK1,sK3)),
% 0.21/0.52    inference(resolution,[],[f200,f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ~r1_tsep_1(sK3,sK1) | ~r1_tsep_1(sK1,sK3)),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & (r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f13])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & (r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3))) & m1_pre_topc(X1,X2)) & m1_pre_topc(X3,X0)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => (m1_pre_topc(X1,X2) => ((r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3)) | (~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3))))))))),
% 0.21/0.52    inference(pure_predicate_removal,[],[f11])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3)) | (~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3))))))))),
% 0.21/0.52    inference(pure_predicate_removal,[],[f10])).
% 0.21/0.52  fof(f10,negated_conjecture,(
% 0.21/0.52    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3)) | (~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3))))))))),
% 0.21/0.52    inference(negated_conjecture,[],[f9])).
% 0.21/0.52  fof(f9,conjecture,(
% 0.21/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3)) | (~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3))))))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tmap_1)).
% 0.21/0.52  fof(f200,plain,(
% 0.21/0.52    r1_tsep_1(sK3,sK1)),
% 0.21/0.52    inference(resolution,[],[f198,f176])).
% 0.21/0.52  fof(f176,plain,(
% 0.21/0.52    ~r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK1)) | r1_tsep_1(sK3,sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f173,f75])).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    l1_struct_0(sK1)),
% 0.21/0.52    inference(resolution,[],[f74,f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.52  fof(f74,plain,(
% 0.21/0.52    l1_pre_topc(sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f71,f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    l1_pre_topc(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f71,plain,(
% 0.21/0.52    ~l1_pre_topc(sK0) | l1_pre_topc(sK1)),
% 0.21/0.52    inference(resolution,[],[f29,f34])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | l1_pre_topc(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    m1_pre_topc(sK1,sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f173,plain,(
% 0.21/0.52    ~r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK1)) | ~l1_struct_0(sK1) | r1_tsep_1(sK3,sK1)),
% 0.21/0.52    inference(superposition,[],[f116,f95])).
% 0.21/0.52  fof(f95,plain,(
% 0.21/0.52    k2_struct_0(sK1) = u1_struct_0(sK1)),
% 0.21/0.52    inference(resolution,[],[f75,f36])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.52  fof(f116,plain,(
% 0.21/0.52    ( ! [X1] : (~r1_xboole_0(k2_struct_0(sK3),u1_struct_0(X1)) | ~l1_struct_0(X1) | r1_tsep_1(sK3,X1)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f114,f64])).
% 0.21/0.52  fof(f64,plain,(
% 0.21/0.52    l1_struct_0(sK3)),
% 0.21/0.52    inference(resolution,[],[f60,f35])).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    l1_pre_topc(sK3)),
% 0.21/0.52    inference(subsumption_resolution,[],[f58,f30])).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    ~l1_pre_topc(sK0) | l1_pre_topc(sK3)),
% 0.21/0.52    inference(resolution,[],[f26,f34])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    m1_pre_topc(sK3,sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f114,plain,(
% 0.21/0.52    ( ! [X1] : (~r1_xboole_0(k2_struct_0(sK3),u1_struct_0(X1)) | ~l1_struct_0(X1) | ~l1_struct_0(sK3) | r1_tsep_1(sK3,X1)) )),
% 0.21/0.52    inference(superposition,[],[f32,f76])).
% 0.21/0.52  fof(f76,plain,(
% 0.21/0.52    k2_struct_0(sK3) = u1_struct_0(sK3)),
% 0.21/0.52    inference(resolution,[],[f64,f36])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~l1_struct_0(X1) | ~l1_struct_0(X0) | r1_tsep_1(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ((r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => (r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tsep_1)).
% 0.21/0.52  fof(f198,plain,(
% 0.21/0.52    r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK1))),
% 0.21/0.52    inference(resolution,[],[f197,f52])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.52    inference(equality_resolution,[],[f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.52  fof(f197,plain,(
% 0.21/0.52    ( ! [X0] : (~r1_tarski(X0,k2_struct_0(sK3)) | r1_xboole_0(X0,k2_struct_0(sK1))) )),
% 0.21/0.52    inference(resolution,[],[f165,f102])).
% 0.21/0.52  fof(f102,plain,(
% 0.21/0.52    r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK2))),
% 0.21/0.52    inference(forward_demodulation,[],[f101,f76])).
% 0.21/0.52  fof(f101,plain,(
% 0.21/0.52    r1_xboole_0(u1_struct_0(sK3),k2_struct_0(sK2))),
% 0.21/0.52    inference(forward_demodulation,[],[f100,f85])).
% 0.21/0.52  fof(f85,plain,(
% 0.21/0.52    k2_struct_0(sK2) = u1_struct_0(sK2)),
% 0.21/0.52    inference(resolution,[],[f69,f36])).
% 0.21/0.52  fof(f69,plain,(
% 0.21/0.52    l1_struct_0(sK2)),
% 0.21/0.52    inference(resolution,[],[f68,f35])).
% 0.21/0.52  fof(f68,plain,(
% 0.21/0.52    l1_pre_topc(sK2)),
% 0.21/0.52    inference(subsumption_resolution,[],[f66,f30])).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    ~l1_pre_topc(sK0) | l1_pre_topc(sK2)),
% 0.21/0.52    inference(resolution,[],[f28,f34])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    m1_pre_topc(sK2,sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f100,plain,(
% 0.21/0.52    r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2))),
% 0.21/0.52    inference(subsumption_resolution,[],[f99,f64])).
% 0.21/0.52  fof(f99,plain,(
% 0.21/0.52    r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2)) | ~l1_struct_0(sK3)),
% 0.21/0.52    inference(subsumption_resolution,[],[f97,f69])).
% 0.21/0.52  fof(f97,plain,(
% 0.21/0.52    ~l1_struct_0(sK2) | r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2)) | ~l1_struct_0(sK3)),
% 0.21/0.52    inference(resolution,[],[f94,f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~l1_struct_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f94,plain,(
% 0.21/0.52    r1_tsep_1(sK3,sK2)),
% 0.21/0.52    inference(subsumption_resolution,[],[f93,f69])).
% 0.21/0.52  fof(f93,plain,(
% 0.21/0.52    ~l1_struct_0(sK2) | r1_tsep_1(sK3,sK2)),
% 0.21/0.52    inference(subsumption_resolution,[],[f88,f64])).
% 0.21/0.52  fof(f88,plain,(
% 0.21/0.52    ~l1_struct_0(sK3) | ~l1_struct_0(sK2) | r1_tsep_1(sK3,sK2)),
% 0.21/0.52    inference(resolution,[],[f84,f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0) | r1_tsep_1(X1,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0,X1] : (r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ! [X0,X1] : ((r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1)) | (~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0,X1] : ((l1_struct_0(X1) & l1_struct_0(X0)) => (r1_tsep_1(X0,X1) => r1_tsep_1(X1,X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).
% 0.21/0.52  fof(f84,plain,(
% 0.21/0.52    r1_tsep_1(sK2,sK3)),
% 0.21/0.52    inference(subsumption_resolution,[],[f83,f64])).
% 0.21/0.52  fof(f83,plain,(
% 0.21/0.52    r1_tsep_1(sK2,sK3) | ~l1_struct_0(sK3)),
% 0.21/0.52    inference(subsumption_resolution,[],[f79,f69])).
% 0.21/0.52  fof(f79,plain,(
% 0.21/0.52    r1_tsep_1(sK2,sK3) | ~l1_struct_0(sK2) | ~l1_struct_0(sK3)),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f78])).
% 0.21/0.52  fof(f78,plain,(
% 0.21/0.52    r1_tsep_1(sK2,sK3) | ~l1_struct_0(sK2) | ~l1_struct_0(sK3) | r1_tsep_1(sK2,sK3)),
% 0.21/0.52    inference(resolution,[],[f25,f31])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    r1_tsep_1(sK3,sK2) | r1_tsep_1(sK2,sK3)),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f165,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_xboole_0(X1,k2_struct_0(sK2)) | r1_xboole_0(X0,k2_struct_0(sK1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(resolution,[],[f146,f55])).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    ( ! [X0,X3,X1] : (~sP7(X3,X0) | ~r1_xboole_0(X1,X3) | ~r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(general_splitting,[],[f37,f54_D])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    ( ! [X2,X0,X3] : (~r1_tarski(X2,X3) | r1_xboole_0(X0,X2) | sP7(X3,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f54_D])).
% 0.21/0.52  fof(f54_D,plain,(
% 0.21/0.52    ( ! [X0,X3] : (( ! [X2] : (~r1_tarski(X2,X3) | r1_xboole_0(X0,X2)) ) <=> ~sP7(X3,X0)) )),
% 0.21/0.52    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP7])])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X2,X3) | ~r1_xboole_0(X1,X3) | r1_xboole_0(X0,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X3) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))),
% 0.21/0.52    inference(flattening,[],[f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X3) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ((r1_xboole_0(X1,X3) & r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_xboole_1)).
% 0.21/0.52  fof(f146,plain,(
% 0.21/0.52    ( ! [X0] : (sP7(k2_struct_0(sK2),X0) | r1_xboole_0(X0,k2_struct_0(sK1))) )),
% 0.21/0.52    inference(resolution,[],[f134,f54])).
% 0.21/0.52  fof(f134,plain,(
% 0.21/0.52    r1_tarski(k2_struct_0(sK1),k2_struct_0(sK2))),
% 0.21/0.52    inference(subsumption_resolution,[],[f133,f74])).
% 0.21/0.52  fof(f133,plain,(
% 0.21/0.52    r1_tarski(k2_struct_0(sK1),k2_struct_0(sK2)) | ~l1_pre_topc(sK1)),
% 0.21/0.52    inference(resolution,[],[f62,f68])).
% 0.21/0.52  fof(f62,plain,(
% 0.21/0.52    ~l1_pre_topc(sK2) | r1_tarski(k2_struct_0(sK1),k2_struct_0(sK2)) | ~l1_pre_topc(sK1)),
% 0.21/0.52    inference(resolution,[],[f27,f50])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X1) | r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ((m1_pre_topc(X1,X0) <=> (! [X2] : ((r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => (r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_pre_topc)).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    m1_pre_topc(sK1,sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f209,plain,(
% 0.21/0.52    r1_tsep_1(sK1,sK3)),
% 0.21/0.52    inference(subsumption_resolution,[],[f208,f64])).
% 0.21/0.52  fof(f208,plain,(
% 0.21/0.52    ~l1_struct_0(sK3) | r1_tsep_1(sK1,sK3)),
% 0.21/0.52    inference(subsumption_resolution,[],[f203,f75])).
% 0.21/0.52  fof(f203,plain,(
% 0.21/0.52    ~l1_struct_0(sK1) | ~l1_struct_0(sK3) | r1_tsep_1(sK1,sK3)),
% 0.21/0.52    inference(resolution,[],[f200,f31])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (7813)------------------------------
% 0.21/0.52  % (7813)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (7813)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (7813)Memory used [KB]: 6268
% 0.21/0.52  % (7813)Time elapsed: 0.087 s
% 0.21/0.52  % (7813)------------------------------
% 0.21/0.52  % (7813)------------------------------
% 0.21/0.52  % (7807)Success in time 0.167 s
%------------------------------------------------------------------------------
