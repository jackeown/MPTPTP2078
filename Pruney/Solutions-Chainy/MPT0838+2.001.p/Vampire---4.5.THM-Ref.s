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
% DateTime   : Thu Dec  3 12:57:29 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 809 expanded)
%              Number of leaves         :   13 ( 176 expanded)
%              Depth                    :   22
%              Number of atoms          :  172 (2501 expanded)
%              Number of equality atoms :   22 ( 320 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f176,plain,(
    $false ),
    inference(subsumption_resolution,[],[f175,f158])).

fof(f158,plain,(
    k1_xboole_0 != k1_relset_1(sK0,sK1,k1_xboole_0) ),
    inference(backward_demodulation,[],[f32,f156])).

fof(f156,plain,(
    k1_xboole_0 = sK2 ),
    inference(resolution,[],[f151,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f151,plain,(
    v1_xboole_0(sK2) ),
    inference(resolution,[],[f144,f112])).

fof(f112,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
      | v1_xboole_0(X0) ) ),
    inference(backward_demodulation,[],[f95,f98])).

fof(f98,plain,(
    k1_xboole_0 = k2_relat_1(sK2) ),
    inference(resolution,[],[f93,f35])).

fof(f93,plain,(
    v1_xboole_0(k2_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f87,f37])).

fof(f37,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f87,plain,
    ( ~ r2_hidden(sK3(k2_relat_1(sK2)),k2_relat_1(sK2))
    | v1_xboole_0(k2_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f73,f84])).

fof(f84,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f48,f31])).

fof(f31,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k2_relset_1(X0,X1,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k1_relset_1(X0,X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k2_relset_1(X0,X1,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k1_relset_1(X0,X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,X1)
                       => ~ r2_hidden(X3,k2_relset_1(X0,X1,X2)) )
                    & k1_xboole_0 != k1_relset_1(X0,X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
             => ~ ( ! [X3] :
                      ( m1_subset_1(X3,X1)
                     => ~ r2_hidden(X3,k2_relset_1(X0,X1,X2)) )
                  & k1_xboole_0 != k1_relset_1(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_relset_1)).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f73,plain,
    ( ~ r2_hidden(sK3(k2_relat_1(sK2)),k2_relset_1(sK0,sK1,sK2))
    | v1_xboole_0(k2_relat_1(sK2)) ),
    inference(resolution,[],[f71,f51])).

fof(f51,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,k2_relset_1(sK0,sK1,sK2)) ) ),
    inference(resolution,[],[f30,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f30,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,sK1)
      | ~ r2_hidden(X3,k2_relset_1(sK0,sK1,sK2)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f71,plain,
    ( r2_hidden(sK3(k2_relat_1(sK2)),sK1)
    | v1_xboole_0(k2_relat_1(sK2)) ),
    inference(resolution,[],[f70,f37])).

fof(f70,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK2))
      | r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f68,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f68,plain,(
    r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(resolution,[],[f66,f63])).

fof(f63,plain,(
    ! [X0] :
      ( ~ v5_relat_1(sK2,X0)
      | r1_tarski(k2_relat_1(sK2),X0) ) ),
    inference(resolution,[],[f40,f57])).

fof(f57,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f46,f31])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f66,plain,(
    v5_relat_1(sK2,sK1) ),
    inference(resolution,[],[f49,f31])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(sK2))))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f93,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f144,plain,(
    ! [X0] : m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) ),
    inference(resolution,[],[f136,f31])).

fof(f136,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(subsumption_resolution,[],[f135,f115])).

fof(f115,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(subsumption_resolution,[],[f101,f114])).

fof(f114,plain,(
    ! [X0] : v5_relat_1(sK2,X0) ),
    inference(global_subsumption,[],[f61,f92])).

fof(f92,plain,(
    ! [X0] : r1_tarski(k2_relat_1(sK2),X0) ),
    inference(subsumption_resolution,[],[f86,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f86,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4(k2_relat_1(sK2),X0),k2_relat_1(sK2))
      | r1_tarski(k2_relat_1(sK2),X0) ) ),
    inference(backward_demodulation,[],[f75,f84])).

fof(f75,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4(k2_relat_1(sK2),X0),k2_relset_1(sK0,sK1,sK2))
      | r1_tarski(k2_relat_1(sK2),X0) ) ),
    inference(resolution,[],[f72,f51])).

fof(f72,plain,(
    ! [X0] :
      ( r2_hidden(sK4(k2_relat_1(sK2),X0),sK1)
      | r1_tarski(k2_relat_1(sK2),X0) ) ),
    inference(resolution,[],[f70,f44])).

fof(f61,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK2),X0)
      | v5_relat_1(sK2,X0) ) ),
    inference(resolution,[],[f39,f57])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f101,plain,(
    ! [X0] :
      ( r1_tarski(k1_xboole_0,X0)
      | ~ v5_relat_1(sK2,X0) ) ),
    inference(backward_demodulation,[],[f63,f98])).

fof(f135,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k1_xboole_0,X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(superposition,[],[f50,f98])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
     => ( r1_tarski(k2_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relset_1)).

fof(f32,plain,(
    k1_xboole_0 != k1_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f175,plain,(
    k1_xboole_0 = k1_relset_1(sK0,sK1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f161,f127])).

fof(f127,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f113,f35])).

fof(f113,plain,(
    v1_xboole_0(k1_relat_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f97,f98])).

fof(f97,plain,(
    v1_xboole_0(k1_relat_1(k2_relat_1(sK2))) ),
    inference(resolution,[],[f93,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_xboole_0(k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_relat_1)).

fof(f161,plain,(
    k1_relat_1(k1_xboole_0) = k1_relset_1(sK0,sK1,k1_xboole_0) ),
    inference(backward_demodulation,[],[f79,f156])).

fof(f79,plain,(
    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(resolution,[],[f47,f31])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:21:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.51  % (4640)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.51  % (4621)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.51  % (4634)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.51  % (4620)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (4626)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.52  % (4626)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f176,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(subsumption_resolution,[],[f175,f158])).
% 0.20/0.52  fof(f158,plain,(
% 0.20/0.52    k1_xboole_0 != k1_relset_1(sK0,sK1,k1_xboole_0)),
% 0.20/0.52    inference(backward_demodulation,[],[f32,f156])).
% 0.20/0.52  fof(f156,plain,(
% 0.20/0.52    k1_xboole_0 = sK2),
% 0.20/0.52    inference(resolution,[],[f151,f35])).
% 0.20/0.52  fof(f35,plain,(
% 0.20/0.52    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f18])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.20/0.52  fof(f151,plain,(
% 0.20/0.52    v1_xboole_0(sK2)),
% 0.20/0.52    inference(resolution,[],[f144,f112])).
% 0.20/0.52  fof(f112,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) | v1_xboole_0(X0)) )),
% 0.20/0.52    inference(backward_demodulation,[],[f95,f98])).
% 0.20/0.52  fof(f98,plain,(
% 0.20/0.52    k1_xboole_0 = k2_relat_1(sK2)),
% 0.20/0.52    inference(resolution,[],[f93,f35])).
% 0.20/0.52  fof(f93,plain,(
% 0.20/0.52    v1_xboole_0(k2_relat_1(sK2))),
% 0.20/0.52    inference(subsumption_resolution,[],[f87,f37])).
% 0.20/0.52  fof(f37,plain,(
% 0.20/0.52    ( ! [X0] : (r2_hidden(sK3(X0),X0) | v1_xboole_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.52  fof(f87,plain,(
% 0.20/0.52    ~r2_hidden(sK3(k2_relat_1(sK2)),k2_relat_1(sK2)) | v1_xboole_0(k2_relat_1(sK2))),
% 0.20/0.52    inference(backward_demodulation,[],[f73,f84])).
% 0.20/0.52  fof(f84,plain,(
% 0.20/0.52    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 0.20/0.52    inference(resolution,[],[f48,f31])).
% 0.20/0.52  fof(f31,plain,(
% 0.20/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.52    inference(cnf_transformation,[],[f17])).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.20/0.52    inference(flattening,[],[f16])).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f14])).
% 0.20/0.52  fof(f14,negated_conjecture,(
% 0.20/0.52    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k2_relset_1(X0,X1,X2))) & k1_xboole_0 != k1_relset_1(X0,X1,X2)))))),
% 0.20/0.52    inference(negated_conjecture,[],[f13])).
% 0.20/0.52  fof(f13,conjecture,(
% 0.20/0.52    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k2_relset_1(X0,X1,X2))) & k1_xboole_0 != k1_relset_1(X0,X1,X2)))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_relset_1)).
% 0.20/0.52  fof(f48,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f26])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.52    inference(ennf_transformation,[],[f11])).
% 0.20/0.52  fof(f11,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.20/0.52  fof(f73,plain,(
% 0.20/0.52    ~r2_hidden(sK3(k2_relat_1(sK2)),k2_relset_1(sK0,sK1,sK2)) | v1_xboole_0(k2_relat_1(sK2))),
% 0.20/0.52    inference(resolution,[],[f71,f51])).
% 0.20/0.52  fof(f51,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(X0,sK1) | ~r2_hidden(X0,k2_relset_1(sK0,sK1,sK2))) )),
% 0.20/0.52    inference(resolution,[],[f30,f42])).
% 0.20/0.52  fof(f42,plain,(
% 0.20/0.52    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f22])).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    ( ! [X3] : (~m1_subset_1(X3,sK1) | ~r2_hidden(X3,k2_relset_1(sK0,sK1,sK2))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f17])).
% 0.20/0.52  fof(f71,plain,(
% 0.20/0.52    r2_hidden(sK3(k2_relat_1(sK2)),sK1) | v1_xboole_0(k2_relat_1(sK2))),
% 0.20/0.52    inference(resolution,[],[f70,f37])).
% 0.20/0.52  fof(f70,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK2)) | r2_hidden(X0,sK1)) )),
% 0.20/0.52    inference(resolution,[],[f68,f43])).
% 0.20/0.52  fof(f43,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f23])).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.52  fof(f68,plain,(
% 0.20/0.52    r1_tarski(k2_relat_1(sK2),sK1)),
% 0.20/0.52    inference(resolution,[],[f66,f63])).
% 0.20/0.52  fof(f63,plain,(
% 0.20/0.52    ( ! [X0] : (~v5_relat_1(sK2,X0) | r1_tarski(k2_relat_1(sK2),X0)) )),
% 0.20/0.52    inference(resolution,[],[f40,f57])).
% 0.20/0.52  fof(f57,plain,(
% 0.20/0.52    v1_relat_1(sK2)),
% 0.20/0.52    inference(resolution,[],[f46,f31])).
% 0.20/0.52  fof(f46,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f24])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.52    inference(ennf_transformation,[],[f7])).
% 0.20/0.52  fof(f7,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.52  fof(f40,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f20])).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.20/0.52  fof(f66,plain,(
% 0.20/0.52    v5_relat_1(sK2,sK1)),
% 0.20/0.52    inference(resolution,[],[f49,f31])).
% 0.20/0.52  fof(f49,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f27])).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.52    inference(ennf_transformation,[],[f15])).
% 0.20/0.52  fof(f15,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 0.20/0.52    inference(pure_predicate_removal,[],[f8])).
% 0.20/0.52  fof(f8,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.52  fof(f95,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(sK2)))) | v1_xboole_0(X0)) )),
% 0.20/0.52    inference(resolution,[],[f93,f41])).
% 0.20/0.52  fof(f41,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_xboole_0(X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f21])).
% 0.20/0.52  fof(f21,plain,(
% 0.20/0.52    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f9])).
% 0.20/0.52  fof(f9,axiom,(
% 0.20/0.52    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).
% 0.20/0.52  fof(f144,plain,(
% 0.20/0.52    ( ! [X0] : (m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))) )),
% 0.20/0.52    inference(resolution,[],[f136,f31])).
% 0.20/0.52  fof(f136,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f135,f115])).
% 0.20/0.52  fof(f115,plain,(
% 0.20/0.52    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f101,f114])).
% 0.20/0.52  fof(f114,plain,(
% 0.20/0.52    ( ! [X0] : (v5_relat_1(sK2,X0)) )),
% 0.20/0.52    inference(global_subsumption,[],[f61,f92])).
% 0.20/0.52  fof(f92,plain,(
% 0.20/0.52    ( ! [X0] : (r1_tarski(k2_relat_1(sK2),X0)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f86,f44])).
% 0.20/0.52  fof(f44,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f23])).
% 0.20/0.52  fof(f86,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(sK4(k2_relat_1(sK2),X0),k2_relat_1(sK2)) | r1_tarski(k2_relat_1(sK2),X0)) )),
% 0.20/0.52    inference(backward_demodulation,[],[f75,f84])).
% 0.20/0.52  fof(f75,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(sK4(k2_relat_1(sK2),X0),k2_relset_1(sK0,sK1,sK2)) | r1_tarski(k2_relat_1(sK2),X0)) )),
% 0.20/0.52    inference(resolution,[],[f72,f51])).
% 0.20/0.52  fof(f72,plain,(
% 0.20/0.52    ( ! [X0] : (r2_hidden(sK4(k2_relat_1(sK2),X0),sK1) | r1_tarski(k2_relat_1(sK2),X0)) )),
% 0.20/0.52    inference(resolution,[],[f70,f44])).
% 0.20/0.52  fof(f61,plain,(
% 0.20/0.52    ( ! [X0] : (~r1_tarski(k2_relat_1(sK2),X0) | v5_relat_1(sK2,X0)) )),
% 0.20/0.52    inference(resolution,[],[f39,f57])).
% 0.20/0.52  fof(f39,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | v5_relat_1(X1,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f20])).
% 0.20/0.52  fof(f101,plain,(
% 0.20/0.52    ( ! [X0] : (r1_tarski(k1_xboole_0,X0) | ~v5_relat_1(sK2,X0)) )),
% 0.20/0.52    inference(backward_demodulation,[],[f63,f98])).
% 0.20/0.52  fof(f135,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r1_tarski(k1_xboole_0,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 0.20/0.52    inference(superposition,[],[f50,f98])).
% 0.20/0.52  fof(f50,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (~r1_tarski(k2_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f29])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 0.20/0.52    inference(flattening,[],[f28])).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 0.20/0.52    inference(ennf_transformation,[],[f12])).
% 0.20/0.52  fof(f12,axiom,(
% 0.20/0.52    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => (r1_tarski(k2_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relset_1)).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    k1_xboole_0 != k1_relset_1(sK0,sK1,sK2)),
% 0.20/0.52    inference(cnf_transformation,[],[f17])).
% 0.20/0.52  fof(f175,plain,(
% 0.20/0.52    k1_xboole_0 = k1_relset_1(sK0,sK1,k1_xboole_0)),
% 0.20/0.52    inference(forward_demodulation,[],[f161,f127])).
% 0.20/0.52  fof(f127,plain,(
% 0.20/0.52    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.52    inference(resolution,[],[f113,f35])).
% 0.20/0.52  fof(f113,plain,(
% 0.20/0.52    v1_xboole_0(k1_relat_1(k1_xboole_0))),
% 0.20/0.52    inference(backward_demodulation,[],[f97,f98])).
% 0.20/0.52  fof(f97,plain,(
% 0.20/0.52    v1_xboole_0(k1_relat_1(k2_relat_1(sK2)))),
% 0.20/0.52    inference(resolution,[],[f93,f36])).
% 0.20/0.52  fof(f36,plain,(
% 0.20/0.52    ( ! [X0] : (~v1_xboole_0(X0) | v1_xboole_0(k1_relat_1(X0))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f19])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    ! [X0] : (v1_xboole_0(k1_relat_1(X0)) | ~v1_xboole_0(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,axiom,(
% 0.20/0.52    ! [X0] : (v1_xboole_0(X0) => v1_xboole_0(k1_relat_1(X0)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_relat_1)).
% 0.20/0.52  fof(f161,plain,(
% 0.20/0.52    k1_relat_1(k1_xboole_0) = k1_relset_1(sK0,sK1,k1_xboole_0)),
% 0.20/0.52    inference(backward_demodulation,[],[f79,f156])).
% 0.20/0.52  fof(f79,plain,(
% 0.20/0.52    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)),
% 0.20/0.52    inference(resolution,[],[f47,f31])).
% 0.20/0.52  fof(f47,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f25])).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.52    inference(ennf_transformation,[],[f10])).
% 0.20/0.52  fof(f10,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (4626)------------------------------
% 0.20/0.52  % (4626)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (4626)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (4626)Memory used [KB]: 6268
% 0.20/0.52  % (4626)Time elapsed: 0.081 s
% 0.20/0.52  % (4626)------------------------------
% 0.20/0.52  % (4626)------------------------------
% 0.20/0.52  % (4619)Success in time 0.164 s
%------------------------------------------------------------------------------
