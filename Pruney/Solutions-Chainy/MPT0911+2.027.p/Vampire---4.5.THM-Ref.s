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
% DateTime   : Thu Dec  3 12:59:33 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  150 (8852 expanded)
%              Number of leaves         :   13 (2217 expanded)
%              Depth                    :   37
%              Number of atoms          :  422 (32353 expanded)
%              Number of equality atoms :  246 (17846 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f893,plain,(
    $false ),
    inference(subsumption_resolution,[],[f892,f168])).

fof(f168,plain,(
    sK3 != k2_mcart_1(sK4) ),
    inference(superposition,[],[f32,f167])).

fof(f167,plain,(
    k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4) ),
    inference(subsumption_resolution,[],[f166,f51])).

fof(f51,plain,(
    o_0_0_xboole_0 != sK0 ),
    inference(definition_unfolding,[],[f29,f33])).

fof(f33,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_xboole_0)).

fof(f29,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f16])).

% (32268)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
fof(f16,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k7_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X7
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k7_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X7
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
       => ( ! [X5] :
              ( m1_subset_1(X5,X0)
             => ! [X6] :
                  ( m1_subset_1(X6,X1)
                 => ! [X7] :
                      ( m1_subset_1(X7,X2)
                     => ( k3_mcart_1(X5,X6,X7) = X4
                       => X3 = X7 ) ) ) )
         => ( k7_mcart_1(X0,X1,X2,X4) = X3
            | k1_xboole_0 = X2
            | k1_xboole_0 = X1
            | k1_xboole_0 = X0 ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
     => ( ! [X5] :
            ( m1_subset_1(X5,X0)
           => ! [X6] :
                ( m1_subset_1(X6,X1)
               => ! [X7] :
                    ( m1_subset_1(X7,X2)
                   => ( k3_mcart_1(X5,X6,X7) = X4
                     => X3 = X7 ) ) ) )
       => ( k7_mcart_1(X0,X1,X2,X4) = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_mcart_1)).

fof(f166,plain,
    ( o_0_0_xboole_0 = sK0
    | k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4) ),
    inference(subsumption_resolution,[],[f165,f49])).

fof(f49,plain,(
    o_0_0_xboole_0 != sK2 ),
    inference(definition_unfolding,[],[f31,f33])).

fof(f31,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f16])).

fof(f165,plain,
    ( o_0_0_xboole_0 = sK2
    | o_0_0_xboole_0 = sK0
    | k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4) ),
    inference(subsumption_resolution,[],[f163,f50])).

fof(f50,plain,(
    o_0_0_xboole_0 != sK1 ),
    inference(definition_unfolding,[],[f30,f33])).

fof(f30,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f16])).

fof(f163,plain,
    ( o_0_0_xboole_0 = sK1
    | o_0_0_xboole_0 = sK2
    | o_0_0_xboole_0 = sK0
    | k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4) ),
    inference(resolution,[],[f57,f52])).

fof(f52,plain,(
    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f28,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f28,plain,(
    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X0
      | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) ) ),
    inference(definition_unfolding,[],[f48,f33,f33,f33,f43])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
            & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
            & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
                & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
                & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).

fof(f32,plain,(
    sK3 != k7_mcart_1(sK0,sK1,sK2,sK4) ),
    inference(cnf_transformation,[],[f16])).

fof(f892,plain,(
    sK3 = k2_mcart_1(sK4) ),
    inference(subsumption_resolution,[],[f891,f828])).

fof(f828,plain,(
    r2_hidden(k2_mcart_1(sK4),sK2) ),
    inference(subsumption_resolution,[],[f765,f660])).

fof(f660,plain,(
    ~ v1_xboole_0(o_0_0_xboole_0) ),
    inference(subsumption_resolution,[],[f659,f51])).

fof(f659,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | o_0_0_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f620,f50])).

fof(f620,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | o_0_0_xboole_0 = sK1
    | o_0_0_xboole_0 = sK0 ),
    inference(superposition,[],[f93,f506])).

fof(f506,plain,(
    o_0_0_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f505,f97])).

fof(f97,plain,
    ( r2_hidden(k2_mcart_1(sK4),sK2)
    | o_0_0_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f95,f49])).

fof(f95,plain,
    ( o_0_0_xboole_0 = sK2
    | o_0_0_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | r2_hidden(k2_mcart_1(sK4),sK2) ),
    inference(resolution,[],[f93,f67])).

fof(f67,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | r2_hidden(k2_mcart_1(sK4),sK2) ),
    inference(resolution,[],[f63,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k2_mcart_1(X0),X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f63,plain,
    ( r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(resolution,[],[f38,f52])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f505,plain,
    ( ~ r2_hidden(k2_mcart_1(sK4),sK2)
    | o_0_0_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f492,f168])).

fof(f492,plain,
    ( ~ r2_hidden(k2_mcart_1(sK4),sK2)
    | sK3 = k2_mcart_1(sK4)
    | o_0_0_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    inference(trivial_inequality_removal,[],[f491])).

fof(f491,plain,
    ( sK4 != sK4
    | ~ r2_hidden(k2_mcart_1(sK4),sK2)
    | sK3 = k2_mcart_1(sK4)
    | o_0_0_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f490])).

fof(f490,plain,
    ( sK4 != sK4
    | ~ r2_hidden(k2_mcart_1(sK4),sK2)
    | sK3 = k2_mcart_1(sK4)
    | o_0_0_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | o_0_0_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    inference(superposition,[],[f485,f113])).

fof(f113,plain,
    ( sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4))
    | o_0_0_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f105,f49])).

fof(f105,plain,
    ( sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4))
    | o_0_0_xboole_0 = sK2
    | o_0_0_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    inference(resolution,[],[f100,f93])).

fof(f100,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) ),
    inference(resolution,[],[f74,f63])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ),
    inference(resolution,[],[f37,f36])).

fof(f36,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r2_hidden(X0,X1)
      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,X1)
       => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_mcart_1)).

fof(f485,plain,(
    ! [X0] :
      ( sK4 != k4_tarski(k1_mcart_1(sK4),X0)
      | ~ r2_hidden(X0,sK2)
      | sK3 = X0
      | o_0_0_xboole_0 = k2_zfmisc_1(sK0,sK1) ) ),
    inference(subsumption_resolution,[],[f484,f99])).

fof(f99,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK4)),sK0)
    | o_0_0_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    inference(resolution,[],[f96,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f96,plain,
    ( r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,sK1))
    | o_0_0_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f94,f49])).

fof(f94,plain,
    ( o_0_0_xboole_0 = sK2
    | o_0_0_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f93,f68])).

fof(f68,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f63,f44])).

fof(f484,plain,(
    ! [X0] :
      ( sK4 != k4_tarski(k1_mcart_1(sK4),X0)
      | ~ r2_hidden(X0,sK2)
      | ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK4)),sK0)
      | sK3 = X0
      | o_0_0_xboole_0 = k2_zfmisc_1(sK0,sK1) ) ),
    inference(duplicate_literal_removal,[],[f476])).

fof(f476,plain,(
    ! [X0] :
      ( sK4 != k4_tarski(k1_mcart_1(sK4),X0)
      | ~ r2_hidden(X0,sK2)
      | ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK4)),sK0)
      | sK3 = X0
      | o_0_0_xboole_0 = k2_zfmisc_1(sK0,sK1)
      | o_0_0_xboole_0 = k2_zfmisc_1(sK0,sK1) ) ),
    inference(superposition,[],[f206,f101])).

fof(f101,plain,
    ( k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4)))
    | o_0_0_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    inference(resolution,[],[f74,f96])).

fof(f206,plain,(
    ! [X6,X7] :
      ( sK4 != k4_tarski(k4_tarski(X7,k2_mcart_1(k1_mcart_1(sK4))),X6)
      | ~ r2_hidden(X6,sK2)
      | ~ r2_hidden(X7,sK0)
      | sK3 = X6
      | o_0_0_xboole_0 = k2_zfmisc_1(sK0,sK1) ) ),
    inference(resolution,[],[f202,f98])).

fof(f98,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK4)),sK1)
    | o_0_0_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    inference(resolution,[],[f96,f45])).

fof(f202,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,sK1)
      | sK3 = X2
      | ~ r2_hidden(X2,sK2)
      | ~ r2_hidden(X0,sK0)
      | k4_tarski(k4_tarski(X0,X1),X2) != sK4 ) ),
    inference(resolution,[],[f201,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f201,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,sK1)
      | sK4 != k4_tarski(k4_tarski(X1,X0),X2)
      | sK3 = X2
      | ~ r2_hidden(X2,sK2)
      | ~ r2_hidden(X1,sK0) ) ),
    inference(resolution,[],[f127,f39])).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,sK0)
      | ~ m1_subset_1(X0,sK1)
      | sK4 != k4_tarski(k4_tarski(X1,X0),X2)
      | sK3 = X2
      | ~ r2_hidden(X2,sK2) ) ),
    inference(resolution,[],[f53,f39])).

fof(f53,plain,(
    ! [X6,X7,X5] :
      ( ~ m1_subset_1(X7,sK2)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X5,sK0)
      | sK4 != k4_tarski(k4_tarski(X5,X6),X7)
      | sK3 = X7 ) ),
    inference(definition_unfolding,[],[f27,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f27,plain,(
    ! [X6,X7,X5] :
      ( ~ m1_subset_1(X5,sK0)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X7,sK2)
      | k3_mcart_1(X5,X6,X7) != sK4
      | sK3 = X7 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_zfmisc_1(X0,X1))
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(subsumption_resolution,[],[f92,f54])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f34,f33])).

fof(f34,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f92,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ v1_xboole_0(k2_zfmisc_1(X0,X1))
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(superposition,[],[f35,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k2_zfmisc_1(X0,X1)) = X0
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f40,f33,f33])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
        & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( ~ ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
            & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t195_relat_1)).

fof(f35,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_relat_1)).

fof(f765,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | r2_hidden(k2_mcart_1(sK4),sK2) ),
    inference(backward_demodulation,[],[f509,f763])).

fof(f763,plain,(
    o_0_0_xboole_0 = k2_zfmisc_1(o_0_0_xboole_0,sK2) ),
    inference(subsumption_resolution,[],[f762,f515])).

fof(f515,plain,
    ( r2_hidden(k2_mcart_1(sK4),sK2)
    | o_0_0_xboole_0 = k2_zfmisc_1(o_0_0_xboole_0,sK2) ),
    inference(backward_demodulation,[],[f73,f506])).

fof(f73,plain,
    ( r2_hidden(k2_mcart_1(sK4),sK2)
    | o_0_0_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) ),
    inference(resolution,[],[f67,f54])).

fof(f762,plain,
    ( ~ r2_hidden(k2_mcart_1(sK4),sK2)
    | o_0_0_xboole_0 = k2_zfmisc_1(o_0_0_xboole_0,sK2) ),
    inference(subsumption_resolution,[],[f758,f168])).

fof(f758,plain,
    ( sK3 = k2_mcart_1(sK4)
    | ~ r2_hidden(k2_mcart_1(sK4),sK2)
    | o_0_0_xboole_0 = k2_zfmisc_1(o_0_0_xboole_0,sK2) ),
    inference(trivial_inequality_removal,[],[f757])).

fof(f757,plain,
    ( sK4 != sK4
    | sK3 = k2_mcart_1(sK4)
    | ~ r2_hidden(k2_mcart_1(sK4),sK2)
    | o_0_0_xboole_0 = k2_zfmisc_1(o_0_0_xboole_0,sK2) ),
    inference(duplicate_literal_removal,[],[f754])).

fof(f754,plain,
    ( sK4 != sK4
    | sK3 = k2_mcart_1(sK4)
    | ~ r2_hidden(k2_mcart_1(sK4),sK2)
    | o_0_0_xboole_0 = k2_zfmisc_1(o_0_0_xboole_0,sK2)
    | o_0_0_xboole_0 = k2_zfmisc_1(o_0_0_xboole_0,sK2) ),
    inference(superposition,[],[f752,f536])).

fof(f536,plain,
    ( sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4))
    | o_0_0_xboole_0 = k2_zfmisc_1(o_0_0_xboole_0,sK2) ),
    inference(backward_demodulation,[],[f106,f506])).

fof(f106,plain,
    ( sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4))
    | o_0_0_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) ),
    inference(resolution,[],[f100,f54])).

fof(f752,plain,(
    ! [X3] :
      ( sK4 != k4_tarski(k1_mcart_1(sK4),X3)
      | sK3 = X3
      | ~ r2_hidden(X3,sK2)
      | o_0_0_xboole_0 = k2_zfmisc_1(o_0_0_xboole_0,sK2) ) ),
    inference(subsumption_resolution,[],[f748,f522])).

fof(f522,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK4)),sK0)
    | o_0_0_xboole_0 = k2_zfmisc_1(o_0_0_xboole_0,sK2) ),
    inference(backward_demodulation,[],[f81,f506])).

fof(f81,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK4)),sK0)
    | o_0_0_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) ),
    inference(resolution,[],[f79,f44])).

fof(f79,plain,
    ( r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,sK1))
    | o_0_0_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) ),
    inference(resolution,[],[f68,f54])).

fof(f748,plain,(
    ! [X3] :
      ( sK4 != k4_tarski(k1_mcart_1(sK4),X3)
      | sK3 = X3
      | ~ r2_hidden(X3,sK2)
      | ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK4)),sK0)
      | o_0_0_xboole_0 = k2_zfmisc_1(o_0_0_xboole_0,sK2) ) ),
    inference(duplicate_literal_removal,[],[f746])).

fof(f746,plain,(
    ! [X3] :
      ( sK4 != k4_tarski(k1_mcart_1(sK4),X3)
      | sK3 = X3
      | ~ r2_hidden(X3,sK2)
      | ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK4)),sK0)
      | o_0_0_xboole_0 = k2_zfmisc_1(o_0_0_xboole_0,sK2)
      | o_0_0_xboole_0 = k2_zfmisc_1(o_0_0_xboole_0,sK2) ) ),
    inference(superposition,[],[f561,f535])).

fof(f535,plain,
    ( k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4)))
    | o_0_0_xboole_0 = k2_zfmisc_1(o_0_0_xboole_0,sK2) ),
    inference(backward_demodulation,[],[f104,f506])).

fof(f104,plain,
    ( k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4)))
    | o_0_0_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) ),
    inference(resolution,[],[f74,f79])).

fof(f561,plain,(
    ! [X0,X1] :
      ( sK4 != k4_tarski(k4_tarski(X1,k2_mcart_1(k1_mcart_1(sK4))),X0)
      | sK3 = X0
      | ~ r2_hidden(X0,sK2)
      | ~ r2_hidden(X1,sK0)
      | o_0_0_xboole_0 = k2_zfmisc_1(o_0_0_xboole_0,sK2) ) ),
    inference(backward_demodulation,[],[f203,f506])).

fof(f203,plain,(
    ! [X0,X1] :
      ( sK3 = X0
      | ~ r2_hidden(X0,sK2)
      | ~ r2_hidden(X1,sK0)
      | sK4 != k4_tarski(k4_tarski(X1,k2_mcart_1(k1_mcart_1(sK4))),X0)
      | o_0_0_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) ) ),
    inference(resolution,[],[f202,f80])).

fof(f80,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK4)),sK1)
    | o_0_0_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) ),
    inference(resolution,[],[f79,f45])).

fof(f509,plain,
    ( v1_xboole_0(k2_zfmisc_1(o_0_0_xboole_0,sK2))
    | r2_hidden(k2_mcart_1(sK4),sK2) ),
    inference(backward_demodulation,[],[f67,f506])).

fof(f891,plain,
    ( ~ r2_hidden(k2_mcart_1(sK4),sK2)
    | sK3 = k2_mcart_1(sK4) ),
    inference(trivial_inequality_removal,[],[f890])).

fof(f890,plain,
    ( sK4 != sK4
    | ~ r2_hidden(k2_mcart_1(sK4),sK2)
    | sK3 = k2_mcart_1(sK4) ),
    inference(superposition,[],[f882,f651])).

fof(f651,plain,(
    sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) ),
    inference(subsumption_resolution,[],[f626,f51])).

fof(f626,plain,
    ( o_0_0_xboole_0 = sK0
    | sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) ),
    inference(backward_demodulation,[],[f121,f625])).

fof(f625,plain,(
    sK0 = k1_relat_1(o_0_0_xboole_0) ),
    inference(subsumption_resolution,[],[f624,f51])).

fof(f624,plain,
    ( sK0 = k1_relat_1(o_0_0_xboole_0)
    | o_0_0_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f615,f50])).

fof(f615,plain,
    ( sK0 = k1_relat_1(o_0_0_xboole_0)
    | o_0_0_xboole_0 = sK1
    | o_0_0_xboole_0 = sK0 ),
    inference(superposition,[],[f56,f506])).

fof(f121,plain,
    ( sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4))
    | o_0_0_xboole_0 = k1_relat_1(o_0_0_xboole_0) ),
    inference(resolution,[],[f119,f60])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | o_0_0_xboole_0 = k1_relat_1(X0) ) ),
    inference(resolution,[],[f54,f35])).

fof(f119,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) ),
    inference(subsumption_resolution,[],[f116,f100])).

fof(f116,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) ),
    inference(superposition,[],[f35,f107])).

fof(f107,plain,
    ( o_0_0_xboole_0 = k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) ),
    inference(resolution,[],[f100,f60])).

fof(f882,plain,(
    ! [X0] :
      ( sK4 != k4_tarski(k1_mcart_1(sK4),X0)
      | ~ r2_hidden(X0,sK2)
      | sK3 = X0 ) ),
    inference(subsumption_resolution,[],[f881,f832])).

fof(f832,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1(sK4)),sK0) ),
    inference(subsumption_resolution,[],[f831,f51])).

fof(f831,plain,
    ( o_0_0_xboole_0 = sK0
    | r2_hidden(k1_mcart_1(k1_mcart_1(sK4)),sK0) ),
    inference(forward_demodulation,[],[f772,f625])).

fof(f772,plain,
    ( o_0_0_xboole_0 = k1_relat_1(o_0_0_xboole_0)
    | r2_hidden(k1_mcart_1(k1_mcart_1(sK4)),sK0) ),
    inference(backward_demodulation,[],[f526,f763])).

fof(f526,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK4)),sK0)
    | o_0_0_xboole_0 = k1_relat_1(k2_zfmisc_1(o_0_0_xboole_0,sK2)) ),
    inference(backward_demodulation,[],[f86,f506])).

fof(f86,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK4)),sK0)
    | o_0_0_xboole_0 = k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(resolution,[],[f78,f44])).

fof(f78,plain,
    ( r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,sK1))
    | o_0_0_xboole_0 = k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(resolution,[],[f68,f60])).

fof(f881,plain,(
    ! [X0] :
      ( sK4 != k4_tarski(k1_mcart_1(sK4),X0)
      | ~ r2_hidden(X0,sK2)
      | ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK4)),sK0)
      | sK3 = X0 ) ),
    inference(superposition,[],[f834,f652])).

fof(f652,plain,(
    k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))) ),
    inference(subsumption_resolution,[],[f635,f51])).

fof(f635,plain,
    ( o_0_0_xboole_0 = sK0
    | k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))) ),
    inference(backward_demodulation,[],[f228,f625])).

fof(f228,plain,
    ( k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4)))
    | o_0_0_xboole_0 = k1_relat_1(o_0_0_xboole_0) ),
    inference(resolution,[],[f226,f60])).

fof(f226,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))) ),
    inference(subsumption_resolution,[],[f224,f74])).

fof(f224,plain,
    ( k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4)))
    | v1_xboole_0(o_0_0_xboole_0)
    | r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f220,f68])).

fof(f220,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4)))
    | v1_xboole_0(o_0_0_xboole_0) ),
    inference(resolution,[],[f214,f35])).

fof(f214,plain,
    ( ~ v1_xboole_0(k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)))
    | v1_xboole_0(o_0_0_xboole_0)
    | k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))) ),
    inference(superposition,[],[f35,f102])).

fof(f102,plain,
    ( o_0_0_xboole_0 = k1_relat_1(k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)))
    | k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))) ),
    inference(resolution,[],[f74,f77])).

fof(f77,plain,
    ( r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,sK1))
    | o_0_0_xboole_0 = k1_relat_1(k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))) ),
    inference(resolution,[],[f68,f61])).

fof(f61,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | o_0_0_xboole_0 = k1_relat_1(k1_relat_1(X0)) ) ),
    inference(resolution,[],[f60,f35])).

fof(f834,plain,(
    ! [X2,X3] :
      ( sK4 != k4_tarski(k4_tarski(X3,k2_mcart_1(k1_mcart_1(sK4))),X2)
      | ~ r2_hidden(X2,sK2)
      | ~ r2_hidden(X3,sK0)
      | sK3 = X2 ) ),
    inference(subsumption_resolution,[],[f833,f51])).

fof(f833,plain,(
    ! [X2,X3] :
      ( o_0_0_xboole_0 = sK0
      | sK3 = X2
      | ~ r2_hidden(X2,sK2)
      | ~ r2_hidden(X3,sK0)
      | sK4 != k4_tarski(k4_tarski(X3,k2_mcart_1(k1_mcart_1(sK4))),X2) ) ),
    inference(forward_demodulation,[],[f789,f625])).

fof(f789,plain,(
    ! [X2,X3] :
      ( o_0_0_xboole_0 = k1_relat_1(o_0_0_xboole_0)
      | sK3 = X2
      | ~ r2_hidden(X2,sK2)
      | ~ r2_hidden(X3,sK0)
      | sK4 != k4_tarski(k4_tarski(X3,k2_mcart_1(k1_mcart_1(sK4))),X2) ) ),
    inference(backward_demodulation,[],[f562,f763])).

fof(f562,plain,(
    ! [X2,X3] :
      ( o_0_0_xboole_0 = k1_relat_1(k2_zfmisc_1(o_0_0_xboole_0,sK2))
      | sK3 = X2
      | ~ r2_hidden(X2,sK2)
      | ~ r2_hidden(X3,sK0)
      | sK4 != k4_tarski(k4_tarski(X3,k2_mcart_1(k1_mcart_1(sK4))),X2) ) ),
    inference(backward_demodulation,[],[f204,f506])).

fof(f204,plain,(
    ! [X2,X3] :
      ( sK3 = X2
      | ~ r2_hidden(X2,sK2)
      | ~ r2_hidden(X3,sK0)
      | sK4 != k4_tarski(k4_tarski(X3,k2_mcart_1(k1_mcart_1(sK4))),X2)
      | o_0_0_xboole_0 = k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ) ),
    inference(resolution,[],[f202,f85])).

fof(f85,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK4)),sK1)
    | o_0_0_xboole_0 = k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(resolution,[],[f78,f45])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:51:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.45  % (32263)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.19/0.48  % (32266)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.19/0.48  % (32271)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.19/0.49  % (32279)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.19/0.49  % (32266)Refutation not found, incomplete strategy% (32266)------------------------------
% 0.19/0.49  % (32266)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.49  % (32279)Refutation not found, incomplete strategy% (32279)------------------------------
% 0.19/0.49  % (32279)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.49  % (32279)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.49  
% 0.19/0.49  % (32279)Memory used [KB]: 10746
% 0.19/0.49  % (32279)Time elapsed: 0.115 s
% 0.19/0.49  % (32279)------------------------------
% 0.19/0.49  % (32279)------------------------------
% 0.19/0.49  % (32258)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.19/0.49  % (32266)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.49  
% 0.19/0.49  % (32266)Memory used [KB]: 10746
% 0.19/0.49  % (32266)Time elapsed: 0.098 s
% 0.19/0.49  % (32266)------------------------------
% 0.19/0.49  % (32266)------------------------------
% 0.19/0.50  % (32272)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.19/0.50  % (32272)Refutation not found, incomplete strategy% (32272)------------------------------
% 0.19/0.50  % (32272)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (32272)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.50  
% 0.19/0.50  % (32272)Memory used [KB]: 6140
% 0.19/0.50  % (32272)Time elapsed: 0.075 s
% 0.19/0.50  % (32272)------------------------------
% 0.19/0.50  % (32272)------------------------------
% 0.19/0.50  % (32265)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.19/0.50  % (32274)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.19/0.50  % (32281)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.19/0.50  % (32260)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.19/0.50  % (32274)Refutation not found, incomplete strategy% (32274)------------------------------
% 0.19/0.50  % (32274)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (32274)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.50  
% 0.19/0.50  % (32274)Memory used [KB]: 10618
% 0.19/0.50  % (32274)Time elapsed: 0.107 s
% 0.19/0.50  % (32274)------------------------------
% 0.19/0.50  % (32274)------------------------------
% 0.19/0.50  % (32262)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.19/0.51  % (32267)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.19/0.51  % (32267)Refutation not found, incomplete strategy% (32267)------------------------------
% 0.19/0.51  % (32267)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (32267)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.51  
% 0.19/0.51  % (32267)Memory used [KB]: 10618
% 0.19/0.51  % (32267)Time elapsed: 0.119 s
% 0.19/0.51  % (32267)------------------------------
% 0.19/0.51  % (32267)------------------------------
% 0.19/0.51  % (32280)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.19/0.51  % (32280)Refutation not found, incomplete strategy% (32280)------------------------------
% 0.19/0.51  % (32280)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (32280)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.51  
% 0.19/0.51  % (32280)Memory used [KB]: 1663
% 0.19/0.51  % (32280)Time elapsed: 0.084 s
% 0.19/0.51  % (32280)------------------------------
% 0.19/0.51  % (32280)------------------------------
% 0.19/0.51  % (32263)Refutation found. Thanks to Tanya!
% 0.19/0.51  % SZS status Theorem for theBenchmark
% 0.19/0.51  % SZS output start Proof for theBenchmark
% 0.19/0.51  fof(f893,plain,(
% 0.19/0.51    $false),
% 0.19/0.51    inference(subsumption_resolution,[],[f892,f168])).
% 0.19/0.51  fof(f168,plain,(
% 0.19/0.51    sK3 != k2_mcart_1(sK4)),
% 0.19/0.51    inference(superposition,[],[f32,f167])).
% 0.19/0.51  fof(f167,plain,(
% 0.19/0.51    k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4)),
% 0.19/0.51    inference(subsumption_resolution,[],[f166,f51])).
% 0.19/0.51  fof(f51,plain,(
% 0.19/0.51    o_0_0_xboole_0 != sK0),
% 0.19/0.51    inference(definition_unfolding,[],[f29,f33])).
% 0.19/0.51  fof(f33,plain,(
% 0.19/0.51    k1_xboole_0 = o_0_0_xboole_0),
% 0.19/0.51    inference(cnf_transformation,[],[f1])).
% 0.19/0.51  fof(f1,axiom,(
% 0.19/0.51    k1_xboole_0 = o_0_0_xboole_0),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_xboole_0)).
% 0.19/0.51  fof(f29,plain,(
% 0.19/0.51    k1_xboole_0 != sK0),
% 0.19/0.51    inference(cnf_transformation,[],[f16])).
% 0.19/0.51  % (32268)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.19/0.51  fof(f16,plain,(
% 0.19/0.51    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 0.19/0.51    inference(flattening,[],[f15])).
% 0.19/0.51  fof(f15,plain,(
% 0.19/0.51    ? [X0,X1,X2,X3,X4] : (((k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X5] : (! [X6] : (! [X7] : ((X3 = X7 | k3_mcart_1(X5,X6,X7) != X4) | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0))) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 0.19/0.51    inference(ennf_transformation,[],[f14])).
% 0.19/0.51  fof(f14,negated_conjecture,(
% 0.19/0.51    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.19/0.51    inference(negated_conjecture,[],[f13])).
% 0.19/0.51  fof(f13,conjecture,(
% 0.19/0.51    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_mcart_1)).
% 0.19/0.51  fof(f166,plain,(
% 0.19/0.51    o_0_0_xboole_0 = sK0 | k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4)),
% 0.19/0.51    inference(subsumption_resolution,[],[f165,f49])).
% 0.19/0.51  fof(f49,plain,(
% 0.19/0.51    o_0_0_xboole_0 != sK2),
% 0.19/0.51    inference(definition_unfolding,[],[f31,f33])).
% 0.19/0.51  fof(f31,plain,(
% 0.19/0.51    k1_xboole_0 != sK2),
% 0.19/0.51    inference(cnf_transformation,[],[f16])).
% 0.19/0.51  fof(f165,plain,(
% 0.19/0.51    o_0_0_xboole_0 = sK2 | o_0_0_xboole_0 = sK0 | k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4)),
% 0.19/0.51    inference(subsumption_resolution,[],[f163,f50])).
% 0.19/0.51  fof(f50,plain,(
% 0.19/0.51    o_0_0_xboole_0 != sK1),
% 0.19/0.51    inference(definition_unfolding,[],[f30,f33])).
% 0.19/0.51  fof(f30,plain,(
% 0.19/0.51    k1_xboole_0 != sK1),
% 0.19/0.51    inference(cnf_transformation,[],[f16])).
% 0.19/0.51  fof(f163,plain,(
% 0.19/0.51    o_0_0_xboole_0 = sK1 | o_0_0_xboole_0 = sK2 | o_0_0_xboole_0 = sK0 | k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4)),
% 0.19/0.51    inference(resolution,[],[f57,f52])).
% 0.19/0.51  fof(f52,plain,(
% 0.19/0.51    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 0.19/0.51    inference(definition_unfolding,[],[f28,f43])).
% 0.19/0.51  fof(f43,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f9])).
% 0.19/0.51  fof(f9,axiom,(
% 0.19/0.51    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.19/0.51  fof(f28,plain,(
% 0.19/0.51    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 0.19/0.51    inference(cnf_transformation,[],[f16])).
% 0.19/0.51  fof(f57,plain,(
% 0.19/0.51    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | o_0_0_xboole_0 = X1 | o_0_0_xboole_0 = X2 | o_0_0_xboole_0 = X0 | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)) )),
% 0.19/0.51    inference(definition_unfolding,[],[f48,f33,f33,f33,f43])).
% 0.19/0.51  fof(f48,plain,(
% 0.19/0.51    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f26])).
% 0.19/0.51  fof(f26,plain,(
% 0.19/0.51    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.19/0.51    inference(ennf_transformation,[],[f12])).
% 0.19/0.51  fof(f12,axiom,(
% 0.19/0.51    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).
% 0.19/0.51  fof(f32,plain,(
% 0.19/0.51    sK3 != k7_mcart_1(sK0,sK1,sK2,sK4)),
% 0.19/0.51    inference(cnf_transformation,[],[f16])).
% 0.19/0.51  fof(f892,plain,(
% 0.19/0.51    sK3 = k2_mcart_1(sK4)),
% 0.19/0.51    inference(subsumption_resolution,[],[f891,f828])).
% 0.19/0.51  fof(f828,plain,(
% 0.19/0.51    r2_hidden(k2_mcart_1(sK4),sK2)),
% 0.19/0.51    inference(subsumption_resolution,[],[f765,f660])).
% 0.19/0.51  fof(f660,plain,(
% 0.19/0.51    ~v1_xboole_0(o_0_0_xboole_0)),
% 0.19/0.51    inference(subsumption_resolution,[],[f659,f51])).
% 0.19/0.51  fof(f659,plain,(
% 0.19/0.51    ~v1_xboole_0(o_0_0_xboole_0) | o_0_0_xboole_0 = sK0),
% 0.19/0.51    inference(subsumption_resolution,[],[f620,f50])).
% 0.19/0.51  fof(f620,plain,(
% 0.19/0.51    ~v1_xboole_0(o_0_0_xboole_0) | o_0_0_xboole_0 = sK1 | o_0_0_xboole_0 = sK0),
% 0.19/0.51    inference(superposition,[],[f93,f506])).
% 0.19/0.51  fof(f506,plain,(
% 0.19/0.51    o_0_0_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.19/0.51    inference(subsumption_resolution,[],[f505,f97])).
% 0.19/0.51  fof(f97,plain,(
% 0.19/0.51    r2_hidden(k2_mcart_1(sK4),sK2) | o_0_0_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.19/0.51    inference(subsumption_resolution,[],[f95,f49])).
% 0.19/0.51  fof(f95,plain,(
% 0.19/0.51    o_0_0_xboole_0 = sK2 | o_0_0_xboole_0 = k2_zfmisc_1(sK0,sK1) | r2_hidden(k2_mcart_1(sK4),sK2)),
% 0.19/0.51    inference(resolution,[],[f93,f67])).
% 0.19/0.51  fof(f67,plain,(
% 0.19/0.51    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | r2_hidden(k2_mcart_1(sK4),sK2)),
% 0.19/0.51    inference(resolution,[],[f63,f45])).
% 0.19/0.51  fof(f45,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f25])).
% 0.19/0.51  fof(f25,plain,(
% 0.19/0.51    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.19/0.51    inference(ennf_transformation,[],[f10])).
% 0.19/0.51  fof(f10,axiom,(
% 0.19/0.51    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).
% 0.19/0.51  fof(f63,plain,(
% 0.19/0.51    r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 0.19/0.51    inference(resolution,[],[f38,f52])).
% 0.19/0.51  fof(f38,plain,(
% 0.19/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f22])).
% 0.19/0.51  fof(f22,plain,(
% 0.19/0.51    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.19/0.51    inference(flattening,[],[f21])).
% 0.19/0.51  fof(f21,plain,(
% 0.19/0.51    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.19/0.51    inference(ennf_transformation,[],[f4])).
% 0.19/0.51  fof(f4,axiom,(
% 0.19/0.51    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.19/0.51  fof(f505,plain,(
% 0.19/0.51    ~r2_hidden(k2_mcart_1(sK4),sK2) | o_0_0_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.19/0.51    inference(subsumption_resolution,[],[f492,f168])).
% 0.19/0.51  fof(f492,plain,(
% 0.19/0.51    ~r2_hidden(k2_mcart_1(sK4),sK2) | sK3 = k2_mcart_1(sK4) | o_0_0_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.19/0.51    inference(trivial_inequality_removal,[],[f491])).
% 0.19/0.51  fof(f491,plain,(
% 0.19/0.51    sK4 != sK4 | ~r2_hidden(k2_mcart_1(sK4),sK2) | sK3 = k2_mcart_1(sK4) | o_0_0_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.19/0.51    inference(duplicate_literal_removal,[],[f490])).
% 0.19/0.51  fof(f490,plain,(
% 0.19/0.51    sK4 != sK4 | ~r2_hidden(k2_mcart_1(sK4),sK2) | sK3 = k2_mcart_1(sK4) | o_0_0_xboole_0 = k2_zfmisc_1(sK0,sK1) | o_0_0_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.19/0.51    inference(superposition,[],[f485,f113])).
% 0.19/0.51  fof(f113,plain,(
% 0.19/0.51    sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) | o_0_0_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.19/0.51    inference(subsumption_resolution,[],[f105,f49])).
% 0.19/0.51  fof(f105,plain,(
% 0.19/0.51    sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) | o_0_0_xboole_0 = sK2 | o_0_0_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.19/0.51    inference(resolution,[],[f100,f93])).
% 0.19/0.51  fof(f100,plain,(
% 0.19/0.51    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4))),
% 0.19/0.51    inference(resolution,[],[f74,f63])).
% 0.19/0.51  fof(f74,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0) )),
% 0.19/0.51    inference(resolution,[],[f37,f36])).
% 0.19/0.51  fof(f36,plain,(
% 0.19/0.51    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.19/0.51    inference(cnf_transformation,[],[f6])).
% 0.19/0.51  fof(f6,axiom,(
% 0.19/0.51    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.19/0.51  fof(f37,plain,(
% 0.19/0.51    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r2_hidden(X0,X1) | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0) )),
% 0.19/0.51    inference(cnf_transformation,[],[f20])).
% 0.19/0.51  fof(f20,plain,(
% 0.19/0.51    ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1))),
% 0.19/0.51    inference(flattening,[],[f19])).
% 0.19/0.51  fof(f19,plain,(
% 0.19/0.51    ! [X0,X1] : ((k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1)) | ~v1_relat_1(X1))),
% 0.19/0.51    inference(ennf_transformation,[],[f11])).
% 0.19/0.51  fof(f11,axiom,(
% 0.19/0.51    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,X1) => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0))),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_mcart_1)).
% 0.19/0.51  fof(f485,plain,(
% 0.19/0.51    ( ! [X0] : (sK4 != k4_tarski(k1_mcart_1(sK4),X0) | ~r2_hidden(X0,sK2) | sK3 = X0 | o_0_0_xboole_0 = k2_zfmisc_1(sK0,sK1)) )),
% 0.19/0.51    inference(subsumption_resolution,[],[f484,f99])).
% 0.19/0.51  fof(f99,plain,(
% 0.19/0.51    r2_hidden(k1_mcart_1(k1_mcart_1(sK4)),sK0) | o_0_0_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.19/0.51    inference(resolution,[],[f96,f44])).
% 0.19/0.51  fof(f44,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f25])).
% 0.19/0.51  fof(f96,plain,(
% 0.19/0.51    r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,sK1)) | o_0_0_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.19/0.51    inference(subsumption_resolution,[],[f94,f49])).
% 0.19/0.51  fof(f94,plain,(
% 0.19/0.51    o_0_0_xboole_0 = sK2 | o_0_0_xboole_0 = k2_zfmisc_1(sK0,sK1) | r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,sK1))),
% 0.19/0.51    inference(resolution,[],[f93,f68])).
% 0.19/0.51  fof(f68,plain,(
% 0.19/0.51    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,sK1))),
% 0.19/0.51    inference(resolution,[],[f63,f44])).
% 0.19/0.51  fof(f484,plain,(
% 0.19/0.51    ( ! [X0] : (sK4 != k4_tarski(k1_mcart_1(sK4),X0) | ~r2_hidden(X0,sK2) | ~r2_hidden(k1_mcart_1(k1_mcart_1(sK4)),sK0) | sK3 = X0 | o_0_0_xboole_0 = k2_zfmisc_1(sK0,sK1)) )),
% 0.19/0.51    inference(duplicate_literal_removal,[],[f476])).
% 0.19/0.51  fof(f476,plain,(
% 0.19/0.51    ( ! [X0] : (sK4 != k4_tarski(k1_mcart_1(sK4),X0) | ~r2_hidden(X0,sK2) | ~r2_hidden(k1_mcart_1(k1_mcart_1(sK4)),sK0) | sK3 = X0 | o_0_0_xboole_0 = k2_zfmisc_1(sK0,sK1) | o_0_0_xboole_0 = k2_zfmisc_1(sK0,sK1)) )),
% 0.19/0.51    inference(superposition,[],[f206,f101])).
% 0.19/0.51  fof(f101,plain,(
% 0.19/0.51    k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))) | o_0_0_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.19/0.51    inference(resolution,[],[f74,f96])).
% 0.19/0.51  fof(f206,plain,(
% 0.19/0.51    ( ! [X6,X7] : (sK4 != k4_tarski(k4_tarski(X7,k2_mcart_1(k1_mcart_1(sK4))),X6) | ~r2_hidden(X6,sK2) | ~r2_hidden(X7,sK0) | sK3 = X6 | o_0_0_xboole_0 = k2_zfmisc_1(sK0,sK1)) )),
% 0.19/0.51    inference(resolution,[],[f202,f98])).
% 0.19/0.51  fof(f98,plain,(
% 0.19/0.51    r2_hidden(k2_mcart_1(k1_mcart_1(sK4)),sK1) | o_0_0_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.19/0.51    inference(resolution,[],[f96,f45])).
% 0.19/0.51  fof(f202,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X1,sK1) | sK3 = X2 | ~r2_hidden(X2,sK2) | ~r2_hidden(X0,sK0) | k4_tarski(k4_tarski(X0,X1),X2) != sK4) )),
% 0.19/0.51    inference(resolution,[],[f201,f39])).
% 0.19/0.51  fof(f39,plain,(
% 0.19/0.51    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f23])).
% 0.19/0.51  fof(f23,plain,(
% 0.19/0.51    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.19/0.51    inference(ennf_transformation,[],[f3])).
% 0.19/0.51  fof(f3,axiom,(
% 0.19/0.51    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 0.19/0.51  fof(f201,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X0,sK1) | sK4 != k4_tarski(k4_tarski(X1,X0),X2) | sK3 = X2 | ~r2_hidden(X2,sK2) | ~r2_hidden(X1,sK0)) )),
% 0.19/0.51    inference(resolution,[],[f127,f39])).
% 0.19/0.51  fof(f127,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X1,sK0) | ~m1_subset_1(X0,sK1) | sK4 != k4_tarski(k4_tarski(X1,X0),X2) | sK3 = X2 | ~r2_hidden(X2,sK2)) )),
% 0.19/0.51    inference(resolution,[],[f53,f39])).
% 0.19/0.51  fof(f53,plain,(
% 0.19/0.51    ( ! [X6,X7,X5] : (~m1_subset_1(X7,sK2) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X5,sK0) | sK4 != k4_tarski(k4_tarski(X5,X6),X7) | sK3 = X7) )),
% 0.19/0.51    inference(definition_unfolding,[],[f27,f42])).
% 0.19/0.51  fof(f42,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f8])).
% 0.19/0.51  fof(f8,axiom,(
% 0.19/0.51    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).
% 0.19/0.51  fof(f27,plain,(
% 0.19/0.51    ( ! [X6,X7,X5] : (~m1_subset_1(X5,sK0) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X7,sK2) | k3_mcart_1(X5,X6,X7) != sK4 | sK3 = X7) )),
% 0.19/0.51    inference(cnf_transformation,[],[f16])).
% 0.19/0.51  fof(f93,plain,(
% 0.19/0.51    ( ! [X0,X1] : (~v1_xboole_0(k2_zfmisc_1(X0,X1)) | o_0_0_xboole_0 = X1 | o_0_0_xboole_0 = X0) )),
% 0.19/0.51    inference(subsumption_resolution,[],[f92,f54])).
% 0.19/0.51  fof(f54,plain,(
% 0.19/0.51    ( ! [X0] : (~v1_xboole_0(X0) | o_0_0_xboole_0 = X0) )),
% 0.19/0.51    inference(definition_unfolding,[],[f34,f33])).
% 0.19/0.51  fof(f34,plain,(
% 0.19/0.51    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.19/0.51    inference(cnf_transformation,[],[f17])).
% 0.19/0.51  fof(f17,plain,(
% 0.19/0.51    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.19/0.51    inference(ennf_transformation,[],[f2])).
% 0.19/0.51  fof(f2,axiom,(
% 0.19/0.51    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.19/0.51  fof(f92,plain,(
% 0.19/0.51    ( ! [X0,X1] : (v1_xboole_0(X0) | ~v1_xboole_0(k2_zfmisc_1(X0,X1)) | o_0_0_xboole_0 = X1 | o_0_0_xboole_0 = X0) )),
% 0.19/0.51    inference(superposition,[],[f35,f56])).
% 0.19/0.51  fof(f56,plain,(
% 0.19/0.51    ( ! [X0,X1] : (k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 | o_0_0_xboole_0 = X1 | o_0_0_xboole_0 = X0) )),
% 0.19/0.51    inference(definition_unfolding,[],[f40,f33,f33])).
% 0.19/0.51  fof(f40,plain,(
% 0.19/0.51    ( ! [X0,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) )),
% 0.19/0.51    inference(cnf_transformation,[],[f24])).
% 0.19/0.51  fof(f24,plain,(
% 0.19/0.51    ! [X0,X1] : ((k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.19/0.51    inference(ennf_transformation,[],[f7])).
% 0.19/0.51  fof(f7,axiom,(
% 0.19/0.51    ! [X0,X1] : ~(~(k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t195_relat_1)).
% 0.19/0.51  fof(f35,plain,(
% 0.19/0.51    ( ! [X0] : (v1_xboole_0(k1_relat_1(X0)) | ~v1_xboole_0(X0)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f18])).
% 0.19/0.51  fof(f18,plain,(
% 0.19/0.51    ! [X0] : (v1_xboole_0(k1_relat_1(X0)) | ~v1_xboole_0(X0))),
% 0.19/0.51    inference(ennf_transformation,[],[f5])).
% 0.19/0.51  fof(f5,axiom,(
% 0.19/0.51    ! [X0] : (v1_xboole_0(X0) => v1_xboole_0(k1_relat_1(X0)))),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_relat_1)).
% 0.19/0.51  fof(f765,plain,(
% 0.19/0.51    v1_xboole_0(o_0_0_xboole_0) | r2_hidden(k2_mcart_1(sK4),sK2)),
% 0.19/0.51    inference(backward_demodulation,[],[f509,f763])).
% 0.19/0.51  fof(f763,plain,(
% 0.19/0.51    o_0_0_xboole_0 = k2_zfmisc_1(o_0_0_xboole_0,sK2)),
% 0.19/0.51    inference(subsumption_resolution,[],[f762,f515])).
% 0.19/0.51  fof(f515,plain,(
% 0.19/0.51    r2_hidden(k2_mcart_1(sK4),sK2) | o_0_0_xboole_0 = k2_zfmisc_1(o_0_0_xboole_0,sK2)),
% 0.19/0.51    inference(backward_demodulation,[],[f73,f506])).
% 0.19/0.51  fof(f73,plain,(
% 0.19/0.51    r2_hidden(k2_mcart_1(sK4),sK2) | o_0_0_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)),
% 0.19/0.51    inference(resolution,[],[f67,f54])).
% 0.19/0.51  fof(f762,plain,(
% 0.19/0.51    ~r2_hidden(k2_mcart_1(sK4),sK2) | o_0_0_xboole_0 = k2_zfmisc_1(o_0_0_xboole_0,sK2)),
% 0.19/0.51    inference(subsumption_resolution,[],[f758,f168])).
% 0.19/0.51  fof(f758,plain,(
% 0.19/0.51    sK3 = k2_mcart_1(sK4) | ~r2_hidden(k2_mcart_1(sK4),sK2) | o_0_0_xboole_0 = k2_zfmisc_1(o_0_0_xboole_0,sK2)),
% 0.19/0.51    inference(trivial_inequality_removal,[],[f757])).
% 0.19/0.51  fof(f757,plain,(
% 0.19/0.51    sK4 != sK4 | sK3 = k2_mcart_1(sK4) | ~r2_hidden(k2_mcart_1(sK4),sK2) | o_0_0_xboole_0 = k2_zfmisc_1(o_0_0_xboole_0,sK2)),
% 0.19/0.51    inference(duplicate_literal_removal,[],[f754])).
% 0.19/0.51  fof(f754,plain,(
% 0.19/0.51    sK4 != sK4 | sK3 = k2_mcart_1(sK4) | ~r2_hidden(k2_mcart_1(sK4),sK2) | o_0_0_xboole_0 = k2_zfmisc_1(o_0_0_xboole_0,sK2) | o_0_0_xboole_0 = k2_zfmisc_1(o_0_0_xboole_0,sK2)),
% 0.19/0.51    inference(superposition,[],[f752,f536])).
% 0.19/0.51  fof(f536,plain,(
% 0.19/0.51    sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) | o_0_0_xboole_0 = k2_zfmisc_1(o_0_0_xboole_0,sK2)),
% 0.19/0.51    inference(backward_demodulation,[],[f106,f506])).
% 0.19/0.51  fof(f106,plain,(
% 0.19/0.51    sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) | o_0_0_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)),
% 0.19/0.51    inference(resolution,[],[f100,f54])).
% 0.19/0.51  fof(f752,plain,(
% 0.19/0.51    ( ! [X3] : (sK4 != k4_tarski(k1_mcart_1(sK4),X3) | sK3 = X3 | ~r2_hidden(X3,sK2) | o_0_0_xboole_0 = k2_zfmisc_1(o_0_0_xboole_0,sK2)) )),
% 0.19/0.51    inference(subsumption_resolution,[],[f748,f522])).
% 0.19/0.51  fof(f522,plain,(
% 0.19/0.51    r2_hidden(k1_mcart_1(k1_mcart_1(sK4)),sK0) | o_0_0_xboole_0 = k2_zfmisc_1(o_0_0_xboole_0,sK2)),
% 0.19/0.51    inference(backward_demodulation,[],[f81,f506])).
% 0.19/0.51  fof(f81,plain,(
% 0.19/0.51    r2_hidden(k1_mcart_1(k1_mcart_1(sK4)),sK0) | o_0_0_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)),
% 0.19/0.51    inference(resolution,[],[f79,f44])).
% 0.19/0.51  fof(f79,plain,(
% 0.19/0.51    r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,sK1)) | o_0_0_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)),
% 0.19/0.51    inference(resolution,[],[f68,f54])).
% 0.19/0.51  fof(f748,plain,(
% 0.19/0.51    ( ! [X3] : (sK4 != k4_tarski(k1_mcart_1(sK4),X3) | sK3 = X3 | ~r2_hidden(X3,sK2) | ~r2_hidden(k1_mcart_1(k1_mcart_1(sK4)),sK0) | o_0_0_xboole_0 = k2_zfmisc_1(o_0_0_xboole_0,sK2)) )),
% 0.19/0.51    inference(duplicate_literal_removal,[],[f746])).
% 0.19/0.51  fof(f746,plain,(
% 0.19/0.51    ( ! [X3] : (sK4 != k4_tarski(k1_mcart_1(sK4),X3) | sK3 = X3 | ~r2_hidden(X3,sK2) | ~r2_hidden(k1_mcart_1(k1_mcart_1(sK4)),sK0) | o_0_0_xboole_0 = k2_zfmisc_1(o_0_0_xboole_0,sK2) | o_0_0_xboole_0 = k2_zfmisc_1(o_0_0_xboole_0,sK2)) )),
% 0.19/0.51    inference(superposition,[],[f561,f535])).
% 0.19/0.51  fof(f535,plain,(
% 0.19/0.51    k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))) | o_0_0_xboole_0 = k2_zfmisc_1(o_0_0_xboole_0,sK2)),
% 0.19/0.51    inference(backward_demodulation,[],[f104,f506])).
% 0.19/0.51  fof(f104,plain,(
% 0.19/0.51    k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))) | o_0_0_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)),
% 0.19/0.51    inference(resolution,[],[f74,f79])).
% 0.19/0.51  fof(f561,plain,(
% 0.19/0.51    ( ! [X0,X1] : (sK4 != k4_tarski(k4_tarski(X1,k2_mcart_1(k1_mcart_1(sK4))),X0) | sK3 = X0 | ~r2_hidden(X0,sK2) | ~r2_hidden(X1,sK0) | o_0_0_xboole_0 = k2_zfmisc_1(o_0_0_xboole_0,sK2)) )),
% 0.19/0.51    inference(backward_demodulation,[],[f203,f506])).
% 0.19/0.51  fof(f203,plain,(
% 0.19/0.51    ( ! [X0,X1] : (sK3 = X0 | ~r2_hidden(X0,sK2) | ~r2_hidden(X1,sK0) | sK4 != k4_tarski(k4_tarski(X1,k2_mcart_1(k1_mcart_1(sK4))),X0) | o_0_0_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) )),
% 0.19/0.51    inference(resolution,[],[f202,f80])).
% 0.19/0.51  fof(f80,plain,(
% 0.19/0.51    r2_hidden(k2_mcart_1(k1_mcart_1(sK4)),sK1) | o_0_0_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)),
% 0.19/0.51    inference(resolution,[],[f79,f45])).
% 0.19/0.51  fof(f509,plain,(
% 0.19/0.51    v1_xboole_0(k2_zfmisc_1(o_0_0_xboole_0,sK2)) | r2_hidden(k2_mcart_1(sK4),sK2)),
% 0.19/0.51    inference(backward_demodulation,[],[f67,f506])).
% 0.19/0.51  fof(f891,plain,(
% 0.19/0.51    ~r2_hidden(k2_mcart_1(sK4),sK2) | sK3 = k2_mcart_1(sK4)),
% 0.19/0.51    inference(trivial_inequality_removal,[],[f890])).
% 0.19/0.51  fof(f890,plain,(
% 0.19/0.51    sK4 != sK4 | ~r2_hidden(k2_mcart_1(sK4),sK2) | sK3 = k2_mcart_1(sK4)),
% 0.19/0.51    inference(superposition,[],[f882,f651])).
% 0.19/0.51  fof(f651,plain,(
% 0.19/0.51    sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4))),
% 0.19/0.51    inference(subsumption_resolution,[],[f626,f51])).
% 0.19/0.51  fof(f626,plain,(
% 0.19/0.51    o_0_0_xboole_0 = sK0 | sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4))),
% 0.19/0.51    inference(backward_demodulation,[],[f121,f625])).
% 0.19/0.51  fof(f625,plain,(
% 0.19/0.51    sK0 = k1_relat_1(o_0_0_xboole_0)),
% 0.19/0.51    inference(subsumption_resolution,[],[f624,f51])).
% 0.19/0.51  fof(f624,plain,(
% 0.19/0.51    sK0 = k1_relat_1(o_0_0_xboole_0) | o_0_0_xboole_0 = sK0),
% 0.19/0.51    inference(subsumption_resolution,[],[f615,f50])).
% 0.19/0.51  fof(f615,plain,(
% 0.19/0.51    sK0 = k1_relat_1(o_0_0_xboole_0) | o_0_0_xboole_0 = sK1 | o_0_0_xboole_0 = sK0),
% 0.19/0.51    inference(superposition,[],[f56,f506])).
% 0.19/0.51  fof(f121,plain,(
% 0.19/0.51    sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) | o_0_0_xboole_0 = k1_relat_1(o_0_0_xboole_0)),
% 0.19/0.51    inference(resolution,[],[f119,f60])).
% 0.19/0.51  fof(f60,plain,(
% 0.19/0.51    ( ! [X0] : (~v1_xboole_0(X0) | o_0_0_xboole_0 = k1_relat_1(X0)) )),
% 0.19/0.51    inference(resolution,[],[f54,f35])).
% 0.19/0.51  fof(f119,plain,(
% 0.19/0.51    v1_xboole_0(o_0_0_xboole_0) | sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4))),
% 0.19/0.51    inference(subsumption_resolution,[],[f116,f100])).
% 0.19/0.51  fof(f116,plain,(
% 0.19/0.51    v1_xboole_0(o_0_0_xboole_0) | ~v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4))),
% 0.19/0.51    inference(superposition,[],[f35,f107])).
% 0.19/0.51  fof(f107,plain,(
% 0.19/0.51    o_0_0_xboole_0 = k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4))),
% 0.19/0.51    inference(resolution,[],[f100,f60])).
% 0.19/0.51  fof(f882,plain,(
% 0.19/0.51    ( ! [X0] : (sK4 != k4_tarski(k1_mcart_1(sK4),X0) | ~r2_hidden(X0,sK2) | sK3 = X0) )),
% 0.19/0.51    inference(subsumption_resolution,[],[f881,f832])).
% 0.19/0.51  fof(f832,plain,(
% 0.19/0.51    r2_hidden(k1_mcart_1(k1_mcart_1(sK4)),sK0)),
% 0.19/0.51    inference(subsumption_resolution,[],[f831,f51])).
% 0.19/0.51  fof(f831,plain,(
% 0.19/0.51    o_0_0_xboole_0 = sK0 | r2_hidden(k1_mcart_1(k1_mcart_1(sK4)),sK0)),
% 0.19/0.51    inference(forward_demodulation,[],[f772,f625])).
% 0.19/0.51  fof(f772,plain,(
% 0.19/0.51    o_0_0_xboole_0 = k1_relat_1(o_0_0_xboole_0) | r2_hidden(k1_mcart_1(k1_mcart_1(sK4)),sK0)),
% 0.19/0.51    inference(backward_demodulation,[],[f526,f763])).
% 0.19/0.51  fof(f526,plain,(
% 0.19/0.51    r2_hidden(k1_mcart_1(k1_mcart_1(sK4)),sK0) | o_0_0_xboole_0 = k1_relat_1(k2_zfmisc_1(o_0_0_xboole_0,sK2))),
% 0.19/0.51    inference(backward_demodulation,[],[f86,f506])).
% 0.19/0.51  fof(f86,plain,(
% 0.19/0.51    r2_hidden(k1_mcart_1(k1_mcart_1(sK4)),sK0) | o_0_0_xboole_0 = k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 0.19/0.51    inference(resolution,[],[f78,f44])).
% 0.19/0.51  fof(f78,plain,(
% 0.19/0.51    r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,sK1)) | o_0_0_xboole_0 = k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 0.19/0.51    inference(resolution,[],[f68,f60])).
% 0.19/0.51  fof(f881,plain,(
% 0.19/0.51    ( ! [X0] : (sK4 != k4_tarski(k1_mcart_1(sK4),X0) | ~r2_hidden(X0,sK2) | ~r2_hidden(k1_mcart_1(k1_mcart_1(sK4)),sK0) | sK3 = X0) )),
% 0.19/0.51    inference(superposition,[],[f834,f652])).
% 0.19/0.51  fof(f652,plain,(
% 0.19/0.51    k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4)))),
% 0.19/0.51    inference(subsumption_resolution,[],[f635,f51])).
% 0.19/0.51  fof(f635,plain,(
% 0.19/0.51    o_0_0_xboole_0 = sK0 | k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4)))),
% 0.19/0.51    inference(backward_demodulation,[],[f228,f625])).
% 0.19/0.51  fof(f228,plain,(
% 0.19/0.51    k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))) | o_0_0_xboole_0 = k1_relat_1(o_0_0_xboole_0)),
% 0.19/0.51    inference(resolution,[],[f226,f60])).
% 0.19/0.51  fof(f226,plain,(
% 0.19/0.51    v1_xboole_0(o_0_0_xboole_0) | k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4)))),
% 0.19/0.51    inference(subsumption_resolution,[],[f224,f74])).
% 0.19/0.51  fof(f224,plain,(
% 0.19/0.51    k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))) | v1_xboole_0(o_0_0_xboole_0) | r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,sK1))),
% 0.19/0.51    inference(resolution,[],[f220,f68])).
% 0.19/0.51  fof(f220,plain,(
% 0.19/0.51    ~v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))) | v1_xboole_0(o_0_0_xboole_0)),
% 0.19/0.51    inference(resolution,[],[f214,f35])).
% 0.19/0.51  fof(f214,plain,(
% 0.19/0.51    ~v1_xboole_0(k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))) | v1_xboole_0(o_0_0_xboole_0) | k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4)))),
% 0.19/0.51    inference(superposition,[],[f35,f102])).
% 0.19/0.51  fof(f102,plain,(
% 0.19/0.51    o_0_0_xboole_0 = k1_relat_1(k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))) | k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4)))),
% 0.19/0.51    inference(resolution,[],[f74,f77])).
% 0.19/0.51  fof(f77,plain,(
% 0.19/0.51    r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,sK1)) | o_0_0_xboole_0 = k1_relat_1(k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)))),
% 0.19/0.51    inference(resolution,[],[f68,f61])).
% 0.19/0.51  fof(f61,plain,(
% 0.19/0.51    ( ! [X0] : (~v1_xboole_0(X0) | o_0_0_xboole_0 = k1_relat_1(k1_relat_1(X0))) )),
% 0.19/0.51    inference(resolution,[],[f60,f35])).
% 0.19/0.51  fof(f834,plain,(
% 0.19/0.51    ( ! [X2,X3] : (sK4 != k4_tarski(k4_tarski(X3,k2_mcart_1(k1_mcart_1(sK4))),X2) | ~r2_hidden(X2,sK2) | ~r2_hidden(X3,sK0) | sK3 = X2) )),
% 0.19/0.51    inference(subsumption_resolution,[],[f833,f51])).
% 0.19/0.51  fof(f833,plain,(
% 0.19/0.51    ( ! [X2,X3] : (o_0_0_xboole_0 = sK0 | sK3 = X2 | ~r2_hidden(X2,sK2) | ~r2_hidden(X3,sK0) | sK4 != k4_tarski(k4_tarski(X3,k2_mcart_1(k1_mcart_1(sK4))),X2)) )),
% 0.19/0.51    inference(forward_demodulation,[],[f789,f625])).
% 0.19/0.51  fof(f789,plain,(
% 0.19/0.51    ( ! [X2,X3] : (o_0_0_xboole_0 = k1_relat_1(o_0_0_xboole_0) | sK3 = X2 | ~r2_hidden(X2,sK2) | ~r2_hidden(X3,sK0) | sK4 != k4_tarski(k4_tarski(X3,k2_mcart_1(k1_mcart_1(sK4))),X2)) )),
% 0.19/0.51    inference(backward_demodulation,[],[f562,f763])).
% 0.19/0.51  fof(f562,plain,(
% 0.19/0.51    ( ! [X2,X3] : (o_0_0_xboole_0 = k1_relat_1(k2_zfmisc_1(o_0_0_xboole_0,sK2)) | sK3 = X2 | ~r2_hidden(X2,sK2) | ~r2_hidden(X3,sK0) | sK4 != k4_tarski(k4_tarski(X3,k2_mcart_1(k1_mcart_1(sK4))),X2)) )),
% 0.19/0.51    inference(backward_demodulation,[],[f204,f506])).
% 0.19/0.51  fof(f204,plain,(
% 0.19/0.51    ( ! [X2,X3] : (sK3 = X2 | ~r2_hidden(X2,sK2) | ~r2_hidden(X3,sK0) | sK4 != k4_tarski(k4_tarski(X3,k2_mcart_1(k1_mcart_1(sK4))),X2) | o_0_0_xboole_0 = k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))) )),
% 0.19/0.51    inference(resolution,[],[f202,f85])).
% 0.19/0.51  fof(f85,plain,(
% 0.19/0.51    r2_hidden(k2_mcart_1(k1_mcart_1(sK4)),sK1) | o_0_0_xboole_0 = k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 0.19/0.51    inference(resolution,[],[f78,f45])).
% 0.19/0.51  % SZS output end Proof for theBenchmark
% 0.19/0.51  % (32263)------------------------------
% 0.19/0.51  % (32263)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (32263)Termination reason: Refutation
% 0.19/0.51  
% 0.19/0.51  % (32263)Memory used [KB]: 6524
% 0.19/0.51  % (32263)Time elapsed: 0.143 s
% 0.19/0.51  % (32263)------------------------------
% 0.19/0.51  % (32263)------------------------------
% 0.19/0.52  % (32256)Success in time 0.166 s
%------------------------------------------------------------------------------
