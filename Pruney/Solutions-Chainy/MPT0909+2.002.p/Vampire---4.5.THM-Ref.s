%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:22 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 618 expanded)
%              Number of leaves         :   14 ( 139 expanded)
%              Depth                    :   34
%              Number of atoms          :  336 (2887 expanded)
%              Number of equality atoms :  169 (1529 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f312,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f311])).

fof(f311,plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(superposition,[],[f36,f254])).

fof(f254,plain,(
    ! [X1] : k1_xboole_0 = X1 ),
    inference(subsumption_resolution,[],[f178,f192])).

fof(f192,plain,(
    ! [X6] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X6) ),
    inference(forward_demodulation,[],[f188,f167])).

fof(f167,plain,(
    k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f90,f154])).

fof(f154,plain,(
    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) ),
    inference(duplicate_literal_removal,[],[f151])).

fof(f151,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) ),
    inference(resolution,[],[f148,f43])).

fof(f43,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5] :
                  ~ ( k4_mcart_1(X2,X3,X4,X5) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_mcart_1)).

fof(f148,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) ) ),
    inference(resolution,[],[f140,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f140,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) ),
    inference(resolution,[],[f136,f99])).

fof(f99,plain,
    ( r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(resolution,[],[f72,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f72,plain,(
    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f33,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f33,plain,(
    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k5_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X5
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k5_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X5
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
       => ( ! [X5] :
              ( m1_subset_1(X5,X0)
             => ! [X6] :
                  ( m1_subset_1(X6,X1)
                 => ! [X7] :
                      ( m1_subset_1(X7,X2)
                     => ( k3_mcart_1(X5,X6,X7) = X4
                       => X3 = X5 ) ) ) )
         => ( k5_mcart_1(X0,X1,X2,X4) = X3
            | k1_xboole_0 = X2
            | k1_xboole_0 = X1
            | k1_xboole_0 = X0 ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
     => ( ! [X5] :
            ( m1_subset_1(X5,X0)
           => ! [X6] :
                ( m1_subset_1(X6,X1)
               => ! [X7] :
                    ( m1_subset_1(X7,X2)
                   => ( k3_mcart_1(X5,X6,X7) = X4
                     => X3 = X5 ) ) ) )
       => ( k5_mcart_1(X0,X1,X2,X4) = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_mcart_1)).

% (1131)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
fof(f136,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(X4,sK1),X5))
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) ) ),
    inference(resolution,[],[f129,f43])).

fof(f129,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
      | ~ r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(X1,sK1),X2)) ) ),
    inference(resolution,[],[f128,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f128,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X0,sK1))
      | ~ r2_hidden(X1,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ) ),
    inference(resolution,[],[f124,f40])).

fof(f124,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
      | ~ r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X0,sK1)) ) ),
    inference(resolution,[],[f123,f99])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,X0),X1))
      | ~ r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X2,sK1)) ) ),
    inference(subsumption_resolution,[],[f122,f108])).

fof(f108,plain,(
    sK3 != k1_mcart_1(k1_mcart_1(sK4)) ),
    inference(subsumption_resolution,[],[f97,f72])).

fof(f97,plain,
    ( sK3 != k1_mcart_1(k1_mcart_1(sK4))
    | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(subsumption_resolution,[],[f96,f34])).

fof(f34,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f20])).

fof(f96,plain,
    ( sK3 != k1_mcart_1(k1_mcart_1(sK4))
    | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f95,f36])).

fof(f95,plain,
    ( sK3 != k1_mcart_1(k1_mcart_1(sK4))
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f94,f35])).

fof(f35,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f20])).

fof(f94,plain,
    ( sK3 != k1_mcart_1(k1_mcart_1(sK4))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f37,f76])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f53,f50])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
            & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
            & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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

fof(f37,plain,(
    sK3 != k5_mcart_1(sK0,sK1,sK2,sK4) ),
    inference(cnf_transformation,[],[f20])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,X0),X1))
      | ~ r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X2,sK1))
      | sK3 = k1_mcart_1(k1_mcart_1(sK4)) ) ),
    inference(trivial_inequality_removal,[],[f120])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,X0),X1))
      | ~ r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X2,sK1))
      | sK4 != sK4
      | sK3 = k1_mcart_1(k1_mcart_1(sK4)) ) ),
    inference(resolution,[],[f119,f105])).

fof(f105,plain,(
    m1_subset_1(k2_mcart_1(sK4),sK2) ),
    inference(subsumption_resolution,[],[f104,f34])).

fof(f104,plain,
    ( m1_subset_1(k2_mcart_1(sK4),sK2)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f103,f72])).

fof(f103,plain,
    ( m1_subset_1(k2_mcart_1(sK4),sK2)
    | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f102,f36])).

fof(f102,plain,
    ( m1_subset_1(k2_mcart_1(sK4),sK2)
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f101,f35])).

fof(f101,plain,
    ( m1_subset_1(k2_mcart_1(sK4),sK2)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f98,f74])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f55,f50])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f98,plain,(
    m1_subset_1(k7_mcart_1(sK0,sK1,sK2,sK4),sK2) ),
    inference(resolution,[],[f72,f77])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) ) ),
    inference(definition_unfolding,[],[f57,f50])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_mcart_1)).

fof(f119,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(k2_mcart_1(X0),sK2)
      | ~ r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK0,X1),X2))
      | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X3,sK1))
      | sK4 != X0
      | sK3 = k1_mcart_1(k1_mcart_1(X0)) ) ),
    inference(condensation,[],[f118])).

fof(f118,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(k2_mcart_1(X0),sK2)
      | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X1,sK1))
      | sK4 != X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X2,X3))
      | sK3 = k1_mcart_1(k1_mcart_1(X0))
      | ~ r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK0,X4),X5)) ) ),
    inference(resolution,[],[f117,f44])).

fof(f44,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f117,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X2)
      | ~ m1_subset_1(k2_mcart_1(X0),sK2)
      | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X1,sK1))
      | sK4 != X0
      | ~ r2_hidden(X0,X2)
      | sK3 = k1_mcart_1(k1_mcart_1(X0))
      | ~ r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK0,X3),X4)) ) ),
    inference(resolution,[],[f116,f51])).

fof(f116,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(sK0,X2))
      | sK3 = k1_mcart_1(k1_mcart_1(X0))
      | ~ m1_subset_1(k2_mcart_1(X0),sK2)
      | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X1,sK1))
      | sK4 != X0
      | ~ r2_hidden(X0,X3)
      | ~ v1_relat_1(X3) ) ),
    inference(superposition,[],[f115,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,X1)
       => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_mcart_1)).

fof(f115,plain,(
    ! [X2,X0,X3,X1] :
      ( sK4 != k4_tarski(X0,X2)
      | k1_mcart_1(X0) = sK3
      | ~ m1_subset_1(X2,sK2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,sK1))
      | ~ r2_hidden(X0,k2_zfmisc_1(sK0,X3)) ) ),
    inference(condensation,[],[f114])).

fof(f114,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | k1_mcart_1(X0) = sK3
      | ~ m1_subset_1(X3,sK2)
      | sK4 != k4_tarski(X0,X3)
      | ~ r2_hidden(X0,k2_zfmisc_1(X4,sK1))
      | ~ r2_hidden(X0,k2_zfmisc_1(sK0,X5)) ) ),
    inference(resolution,[],[f113,f44])).

fof(f113,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r2_hidden(X0,X1)
      | k1_mcart_1(X0) = sK3
      | ~ m1_subset_1(X2,sK2)
      | sK4 != k4_tarski(X0,X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X3,sK1))
      | ~ r2_hidden(X0,k2_zfmisc_1(sK0,X4)) ) ),
    inference(resolution,[],[f112,f51])).

fof(f112,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k1_mcart_1(X0),sK0)
      | k1_mcart_1(X0) = sK3
      | ~ r2_hidden(X0,X2)
      | ~ v1_relat_1(X2)
      | ~ m1_subset_1(X1,sK2)
      | k4_tarski(X0,X1) != sK4
      | ~ r2_hidden(X0,k2_zfmisc_1(X3,sK1)) ) ),
    inference(resolution,[],[f111,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k2_mcart_1(X1),sK1)
      | sK4 != k4_tarski(X1,X0)
      | sK3 = k1_mcart_1(X1)
      | ~ r2_hidden(X1,X2)
      | ~ v1_relat_1(X2)
      | ~ m1_subset_1(X0,sK2)
      | ~ r2_hidden(k1_mcart_1(X1),sK0) ) ),
    inference(resolution,[],[f110,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k1_mcart_1(X0),sK0)
      | ~ m1_subset_1(X1,sK2)
      | k4_tarski(X0,X1) != sK4
      | k1_mcart_1(X0) = sK3
      | ~ r2_hidden(X0,X2)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(k2_mcart_1(X0),sK1) ) ),
    inference(resolution,[],[f109,f47])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k2_mcart_1(X0),sK1)
      | k4_tarski(X0,X1) != sK4
      | ~ m1_subset_1(X1,sK2)
      | ~ m1_subset_1(k1_mcart_1(X0),sK0)
      | k1_mcart_1(X0) = sK3
      | ~ r2_hidden(X0,X2)
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f73,f45])).

fof(f73,plain,(
    ! [X6,X7,X5] :
      ( sK4 != k4_tarski(k4_tarski(X5,X6),X7)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X7,sK2)
      | ~ m1_subset_1(X5,sK0)
      | sK3 = X5 ) ),
    inference(definition_unfolding,[],[f32,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f32,plain,(
    ! [X6,X7,X5] :
      ( ~ m1_subset_1(X5,sK0)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X7,sK2)
      | k3_mcart_1(X5,X6,X7) != sK4
      | sK3 = X5 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f90,plain,(
    ! [X2,X0,X1] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),k1_xboole_0) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)
      | k1_xboole_0 != X3 ) ),
    inference(definition_unfolding,[],[f70,f71])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f56,f50])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)
      | k1_xboole_0 != X3 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_mcart_1)).

fof(f188,plain,(
    ! [X6] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),X6) ),
    inference(superposition,[],[f91,f167])).

fof(f91,plain,(
    ! [X0,X3,X1] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0),X3) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)
      | k1_xboole_0 != X2 ) ),
    inference(definition_unfolding,[],[f69,f71])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)
      | k1_xboole_0 != X2 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f178,plain,(
    ! [X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X1)
      | k1_xboole_0 = X1 ) ),
    inference(subsumption_resolution,[],[f177,f36])).

fof(f177,plain,(
    ! [X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X1)
      | k1_xboole_0 = sK2
      | k1_xboole_0 = X1 ) ),
    inference(subsumption_resolution,[],[f176,f35])).

fof(f176,plain,(
    ! [X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X1)
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = X1 ) ),
    inference(subsumption_resolution,[],[f166,f34])).

fof(f166,plain,(
    ! [X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X1)
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = X1 ) ),
    inference(superposition,[],[f82,f154])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3 ) ),
    inference(definition_unfolding,[],[f66,f71])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f36,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n003.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:09:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (1134)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.50  % (1134)Refutation not found, incomplete strategy% (1134)------------------------------
% 0.21/0.50  % (1134)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (1134)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (1134)Memory used [KB]: 10874
% 0.21/0.50  % (1134)Time elapsed: 0.074 s
% 0.21/0.50  % (1134)------------------------------
% 0.21/0.50  % (1134)------------------------------
% 0.21/0.50  % (1118)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.50  % (1132)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.51  % (1126)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.51  % (1117)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (1119)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (1116)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (1133)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.52  % (1121)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (1115)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (1121)Refutation not found, incomplete strategy% (1121)------------------------------
% 0.21/0.52  % (1121)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (1114)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (1125)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.52  % (1114)Refutation not found, incomplete strategy% (1114)------------------------------
% 0.21/0.52  % (1114)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (1114)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (1114)Memory used [KB]: 10746
% 0.21/0.52  % (1114)Time elapsed: 0.117 s
% 0.21/0.52  % (1114)------------------------------
% 0.21/0.52  % (1114)------------------------------
% 0.21/0.53  % (1137)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.53  % (1138)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.53  % (1141)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.53  % (1112)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (1139)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.53  % (1130)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.53  % (1112)Refutation not found, incomplete strategy% (1112)------------------------------
% 0.21/0.53  % (1112)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (1112)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (1112)Memory used [KB]: 1791
% 0.21/0.53  % (1112)Time elapsed: 0.128 s
% 0.21/0.53  % (1112)------------------------------
% 0.21/0.53  % (1112)------------------------------
% 0.21/0.53  % (1136)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.53  % (1122)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (1121)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (1121)Memory used [KB]: 10746
% 0.21/0.53  % (1121)Time elapsed: 0.102 s
% 0.21/0.53  % (1121)------------------------------
% 0.21/0.53  % (1121)------------------------------
% 0.21/0.54  % (1140)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (1133)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % (1113)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (1122)Refutation not found, incomplete strategy% (1122)------------------------------
% 0.21/0.54  % (1122)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (1122)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (1122)Memory used [KB]: 10618
% 0.21/0.54  % (1122)Time elapsed: 0.128 s
% 0.21/0.54  % (1122)------------------------------
% 0.21/0.54  % (1122)------------------------------
% 0.21/0.54  % (1128)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (1129)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (1129)Refutation not found, incomplete strategy% (1129)------------------------------
% 0.21/0.55  % (1129)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (1129)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (1129)Memory used [KB]: 10618
% 0.21/0.55  % (1129)Time elapsed: 0.141 s
% 0.21/0.55  % (1129)------------------------------
% 0.21/0.55  % (1129)------------------------------
% 0.21/0.55  % (1135)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.55  % SZS output start Proof for theBenchmark
% 0.21/0.55  fof(f312,plain,(
% 0.21/0.55    $false),
% 0.21/0.55    inference(trivial_inequality_removal,[],[f311])).
% 0.21/0.55  fof(f311,plain,(
% 0.21/0.55    k1_xboole_0 != k1_xboole_0),
% 0.21/0.55    inference(superposition,[],[f36,f254])).
% 0.21/0.55  fof(f254,plain,(
% 0.21/0.55    ( ! [X1] : (k1_xboole_0 = X1) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f178,f192])).
% 0.21/0.55  fof(f192,plain,(
% 0.21/0.55    ( ! [X6] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X6)) )),
% 0.21/0.55    inference(forward_demodulation,[],[f188,f167])).
% 0.21/0.55  fof(f167,plain,(
% 0.21/0.55    k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)),
% 0.21/0.55    inference(superposition,[],[f90,f154])).
% 0.21/0.55  fof(f154,plain,(
% 0.21/0.55    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f151])).
% 0.21/0.55  fof(f151,plain,(
% 0.21/0.55    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)),
% 0.21/0.55    inference(resolution,[],[f148,f43])).
% 0.21/0.55  fof(f43,plain,(
% 0.21/0.55    ( ! [X0] : (r2_hidden(sK6(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.55    inference(cnf_transformation,[],[f21])).
% 0.21/0.55  fof(f21,plain,(
% 0.21/0.55    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.21/0.55    inference(ennf_transformation,[],[f14])).
% 0.21/0.55  fof(f14,axiom,(
% 0.21/0.55    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5] : ~(k4_mcart_1(X2,X3,X4,X5) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_mcart_1)).
% 0.21/0.55  fof(f148,plain,(
% 0.21/0.55    ( ! [X0] : (~r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) )),
% 0.21/0.55    inference(resolution,[],[f140,f40])).
% 0.21/0.55  fof(f40,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~r2_hidden(X1,X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f1])).
% 0.21/0.55  fof(f1,axiom,(
% 0.21/0.55    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.55  fof(f140,plain,(
% 0.21/0.55    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)),
% 0.21/0.55    inference(resolution,[],[f136,f99])).
% 0.21/0.55  fof(f99,plain,(
% 0.21/0.55    r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 0.21/0.55    inference(resolution,[],[f72,f46])).
% 0.21/0.55  fof(f46,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f25])).
% 0.21/0.55  fof(f25,plain,(
% 0.21/0.55    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.55    inference(flattening,[],[f24])).
% 0.21/0.55  fof(f24,plain,(
% 0.21/0.55    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.55    inference(ennf_transformation,[],[f5])).
% 0.21/0.55  fof(f5,axiom,(
% 0.21/0.55    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.55  fof(f72,plain,(
% 0.21/0.55    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 0.21/0.55    inference(definition_unfolding,[],[f33,f50])).
% 0.21/0.55  fof(f50,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f9])).
% 0.21/0.55  fof(f9,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.21/0.55  fof(f33,plain,(
% 0.21/0.55    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 0.21/0.55    inference(cnf_transformation,[],[f20])).
% 0.21/0.55  fof(f20,plain,(
% 0.21/0.55    ? [X0,X1,X2,X3,X4] : (k5_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X5 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 0.21/0.55    inference(flattening,[],[f19])).
% 0.21/0.55  fof(f19,plain,(
% 0.21/0.55    ? [X0,X1,X2,X3,X4] : (((k5_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X5] : (! [X6] : (! [X7] : ((X3 = X5 | k3_mcart_1(X5,X6,X7) != X4) | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0))) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 0.21/0.55    inference(ennf_transformation,[],[f18])).
% 0.21/0.55  fof(f18,negated_conjecture,(
% 0.21/0.55    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X5)))) => (k5_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.21/0.55    inference(negated_conjecture,[],[f17])).
% 0.21/0.55  fof(f17,conjecture,(
% 0.21/0.55    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X5)))) => (k5_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_mcart_1)).
% 0.21/0.55  % (1131)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  fof(f136,plain,(
% 0.21/0.55    ( ! [X4,X5] : (~r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(X4,sK1),X5)) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) )),
% 0.21/0.55    inference(resolution,[],[f129,f43])).
% 0.21/0.55  fof(f129,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(X1,sK1),X2))) )),
% 0.21/0.55    inference(resolution,[],[f128,f51])).
% 0.21/0.55  fof(f51,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f28])).
% 0.21/0.55  fof(f28,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.21/0.55    inference(ennf_transformation,[],[f12])).
% 0.21/0.55  fof(f12,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).
% 0.21/0.55  fof(f128,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X0,sK1)) | ~r2_hidden(X1,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))) )),
% 0.21/0.55    inference(resolution,[],[f124,f40])).
% 0.21/0.55  fof(f124,plain,(
% 0.21/0.55    ( ! [X0] : (v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X0,sK1))) )),
% 0.21/0.55    inference(resolution,[],[f123,f99])).
% 0.21/0.55  fof(f123,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,X0),X1)) | ~r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X2,sK1))) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f122,f108])).
% 0.21/0.55  fof(f108,plain,(
% 0.21/0.55    sK3 != k1_mcart_1(k1_mcart_1(sK4))),
% 0.21/0.55    inference(subsumption_resolution,[],[f97,f72])).
% 0.21/0.55  fof(f97,plain,(
% 0.21/0.55    sK3 != k1_mcart_1(k1_mcart_1(sK4)) | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 0.21/0.55    inference(subsumption_resolution,[],[f96,f34])).
% 0.21/0.55  fof(f34,plain,(
% 0.21/0.55    k1_xboole_0 != sK0),
% 0.21/0.55    inference(cnf_transformation,[],[f20])).
% 0.21/0.55  fof(f96,plain,(
% 0.21/0.55    sK3 != k1_mcart_1(k1_mcart_1(sK4)) | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK0),
% 0.21/0.55    inference(subsumption_resolution,[],[f95,f36])).
% 0.21/0.55  fof(f95,plain,(
% 0.21/0.55    sK3 != k1_mcart_1(k1_mcart_1(sK4)) | k1_xboole_0 = sK2 | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK0),
% 0.21/0.55    inference(subsumption_resolution,[],[f94,f35])).
% 0.21/0.55  fof(f35,plain,(
% 0.21/0.55    k1_xboole_0 != sK1),
% 0.21/0.55    inference(cnf_transformation,[],[f20])).
% 0.21/0.55  fof(f94,plain,(
% 0.21/0.55    sK3 != k1_mcart_1(k1_mcart_1(sK4)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK0),
% 0.21/0.55    inference(superposition,[],[f37,f76])).
% 0.21/0.55  fof(f76,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X0) )),
% 0.21/0.55    inference(definition_unfolding,[],[f53,f50])).
% 0.21/0.55  fof(f53,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f29])).
% 0.21/0.55  fof(f29,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.55    inference(ennf_transformation,[],[f15])).
% 0.21/0.55  fof(f15,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).
% 0.21/0.55  fof(f37,plain,(
% 0.21/0.55    sK3 != k5_mcart_1(sK0,sK1,sK2,sK4)),
% 0.21/0.55    inference(cnf_transformation,[],[f20])).
% 0.21/0.55  fof(f122,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,X0),X1)) | ~r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X2,sK1)) | sK3 = k1_mcart_1(k1_mcart_1(sK4))) )),
% 0.21/0.55    inference(trivial_inequality_removal,[],[f120])).
% 0.21/0.55  fof(f120,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,X0),X1)) | ~r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X2,sK1)) | sK4 != sK4 | sK3 = k1_mcart_1(k1_mcart_1(sK4))) )),
% 0.21/0.55    inference(resolution,[],[f119,f105])).
% 0.21/0.55  fof(f105,plain,(
% 0.21/0.55    m1_subset_1(k2_mcart_1(sK4),sK2)),
% 0.21/0.55    inference(subsumption_resolution,[],[f104,f34])).
% 0.21/0.55  fof(f104,plain,(
% 0.21/0.55    m1_subset_1(k2_mcart_1(sK4),sK2) | k1_xboole_0 = sK0),
% 0.21/0.55    inference(subsumption_resolution,[],[f103,f72])).
% 0.21/0.55  fof(f103,plain,(
% 0.21/0.55    m1_subset_1(k2_mcart_1(sK4),sK2) | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK0),
% 0.21/0.55    inference(subsumption_resolution,[],[f102,f36])).
% 0.21/0.55  fof(f102,plain,(
% 0.21/0.55    m1_subset_1(k2_mcart_1(sK4),sK2) | k1_xboole_0 = sK2 | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK0),
% 0.21/0.55    inference(subsumption_resolution,[],[f101,f35])).
% 0.21/0.55  fof(f101,plain,(
% 0.21/0.55    m1_subset_1(k2_mcart_1(sK4),sK2) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK0),
% 0.21/0.55    inference(superposition,[],[f98,f74])).
% 0.21/0.55  fof(f74,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X0) )),
% 0.21/0.55    inference(definition_unfolding,[],[f55,f50])).
% 0.21/0.55  fof(f55,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f29])).
% 0.21/0.55  fof(f98,plain,(
% 0.21/0.55    m1_subset_1(k7_mcart_1(sK0,sK1,sK2,sK4),sK2)),
% 0.21/0.55    inference(resolution,[],[f72,f77])).
% 0.21/0.55  fof(f77,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)) )),
% 0.21/0.55    inference(definition_unfolding,[],[f57,f50])).
% 0.21/0.55  fof(f57,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f30])).
% 0.21/0.55  fof(f30,plain,(
% 0.21/0.55    ! [X0,X1,X2,X3] : (m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 0.21/0.55    inference(ennf_transformation,[],[f11])).
% 0.21/0.55  fof(f11,axiom,(
% 0.21/0.55    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_mcart_1)).
% 0.21/0.55  fof(f119,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(k2_mcart_1(X0),sK2) | ~r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK0,X1),X2)) | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X3,sK1)) | sK4 != X0 | sK3 = k1_mcart_1(k1_mcart_1(X0))) )),
% 0.21/0.55    inference(condensation,[],[f118])).
% 0.21/0.55  fof(f118,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(k2_mcart_1(X0),sK2) | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X1,sK1)) | sK4 != X0 | ~r2_hidden(X0,k2_zfmisc_1(X2,X3)) | sK3 = k1_mcart_1(k1_mcart_1(X0)) | ~r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK0,X4),X5))) )),
% 0.21/0.55    inference(resolution,[],[f117,f44])).
% 0.21/0.55  fof(f44,plain,(
% 0.21/0.55    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f6])).
% 0.21/0.55  fof(f6,axiom,(
% 0.21/0.55    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.55  fof(f117,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X3,X1] : (~v1_relat_1(X2) | ~m1_subset_1(k2_mcart_1(X0),sK2) | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X1,sK1)) | sK4 != X0 | ~r2_hidden(X0,X2) | sK3 = k1_mcart_1(k1_mcart_1(X0)) | ~r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK0,X3),X4))) )),
% 0.21/0.55    inference(resolution,[],[f116,f51])).
% 0.21/0.55  fof(f116,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(sK0,X2)) | sK3 = k1_mcart_1(k1_mcart_1(X0)) | ~m1_subset_1(k2_mcart_1(X0),sK2) | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X1,sK1)) | sK4 != X0 | ~r2_hidden(X0,X3) | ~v1_relat_1(X3)) )),
% 0.21/0.55    inference(superposition,[],[f115,f45])).
% 0.21/0.55  fof(f45,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f23])).
% 0.21/0.55  fof(f23,plain,(
% 0.21/0.55    ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1))),
% 0.21/0.55    inference(flattening,[],[f22])).
% 0.21/0.55  fof(f22,plain,(
% 0.21/0.55    ! [X0,X1] : ((k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1)) | ~v1_relat_1(X1))),
% 0.21/0.55    inference(ennf_transformation,[],[f13])).
% 0.21/0.55  fof(f13,axiom,(
% 0.21/0.55    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,X1) => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_mcart_1)).
% 0.21/0.55  fof(f115,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (sK4 != k4_tarski(X0,X2) | k1_mcart_1(X0) = sK3 | ~m1_subset_1(X2,sK2) | ~r2_hidden(X0,k2_zfmisc_1(X1,sK1)) | ~r2_hidden(X0,k2_zfmisc_1(sK0,X3))) )),
% 0.21/0.55    inference(condensation,[],[f114])).
% 0.21/0.55  fof(f114,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | k1_mcart_1(X0) = sK3 | ~m1_subset_1(X3,sK2) | sK4 != k4_tarski(X0,X3) | ~r2_hidden(X0,k2_zfmisc_1(X4,sK1)) | ~r2_hidden(X0,k2_zfmisc_1(sK0,X5))) )),
% 0.21/0.55    inference(resolution,[],[f113,f44])).
% 0.21/0.55  fof(f113,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X3,X1] : (~v1_relat_1(X1) | ~r2_hidden(X0,X1) | k1_mcart_1(X0) = sK3 | ~m1_subset_1(X2,sK2) | sK4 != k4_tarski(X0,X2) | ~r2_hidden(X0,k2_zfmisc_1(X3,sK1)) | ~r2_hidden(X0,k2_zfmisc_1(sK0,X4))) )),
% 0.21/0.55    inference(resolution,[],[f112,f51])).
% 0.21/0.55  fof(f112,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (~r2_hidden(k1_mcart_1(X0),sK0) | k1_mcart_1(X0) = sK3 | ~r2_hidden(X0,X2) | ~v1_relat_1(X2) | ~m1_subset_1(X1,sK2) | k4_tarski(X0,X1) != sK4 | ~r2_hidden(X0,k2_zfmisc_1(X3,sK1))) )),
% 0.21/0.55    inference(resolution,[],[f111,f52])).
% 0.21/0.55  fof(f52,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f28])).
% 0.21/0.55  fof(f111,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~r2_hidden(k2_mcart_1(X1),sK1) | sK4 != k4_tarski(X1,X0) | sK3 = k1_mcart_1(X1) | ~r2_hidden(X1,X2) | ~v1_relat_1(X2) | ~m1_subset_1(X0,sK2) | ~r2_hidden(k1_mcart_1(X1),sK0)) )),
% 0.21/0.55    inference(resolution,[],[f110,f47])).
% 0.21/0.55  fof(f47,plain,(
% 0.21/0.55    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f26])).
% 0.21/0.55  fof(f26,plain,(
% 0.21/0.55    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.21/0.55    inference(ennf_transformation,[],[f4])).
% 0.21/0.55  fof(f4,axiom,(
% 0.21/0.55    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 0.21/0.55  fof(f110,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(k1_mcart_1(X0),sK0) | ~m1_subset_1(X1,sK2) | k4_tarski(X0,X1) != sK4 | k1_mcart_1(X0) = sK3 | ~r2_hidden(X0,X2) | ~v1_relat_1(X2) | ~r2_hidden(k2_mcart_1(X0),sK1)) )),
% 0.21/0.55    inference(resolution,[],[f109,f47])).
% 0.21/0.55  fof(f109,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(k2_mcart_1(X0),sK1) | k4_tarski(X0,X1) != sK4 | ~m1_subset_1(X1,sK2) | ~m1_subset_1(k1_mcart_1(X0),sK0) | k1_mcart_1(X0) = sK3 | ~r2_hidden(X0,X2) | ~v1_relat_1(X2)) )),
% 0.21/0.55    inference(superposition,[],[f73,f45])).
% 0.21/0.55  fof(f73,plain,(
% 0.21/0.55    ( ! [X6,X7,X5] : (sK4 != k4_tarski(k4_tarski(X5,X6),X7) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X7,sK2) | ~m1_subset_1(X5,sK0) | sK3 = X5) )),
% 0.21/0.55    inference(definition_unfolding,[],[f32,f49])).
% 0.21/0.55  fof(f49,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f8])).
% 0.21/0.55  fof(f8,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).
% 0.21/0.55  fof(f32,plain,(
% 0.21/0.55    ( ! [X6,X7,X5] : (~m1_subset_1(X5,sK0) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X7,sK2) | k3_mcart_1(X5,X6,X7) != sK4 | sK3 = X5) )),
% 0.21/0.55    inference(cnf_transformation,[],[f20])).
% 0.21/0.55  fof(f90,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),k1_xboole_0)) )),
% 0.21/0.55    inference(equality_resolution,[],[f78])).
% 0.21/0.55  fof(f78,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) | k1_xboole_0 != X3) )),
% 0.21/0.55    inference(definition_unfolding,[],[f70,f71])).
% 0.21/0.55  fof(f71,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 0.21/0.55    inference(definition_unfolding,[],[f56,f50])).
% 0.21/0.55  fof(f56,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f10])).
% 0.21/0.55  fof(f10,axiom,(
% 0.21/0.55    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 0.21/0.55  fof(f70,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 != X3) )),
% 0.21/0.55    inference(cnf_transformation,[],[f16])).
% 0.21/0.55  fof(f16,axiom,(
% 0.21/0.55    ! [X0,X1,X2,X3] : ((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_mcart_1)).
% 0.21/0.55  fof(f188,plain,(
% 0.21/0.55    ( ! [X6] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),X6)) )),
% 0.21/0.55    inference(superposition,[],[f91,f167])).
% 0.21/0.55  fof(f91,plain,(
% 0.21/0.55    ( ! [X0,X3,X1] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0),X3)) )),
% 0.21/0.55    inference(equality_resolution,[],[f79])).
% 0.21/0.55  fof(f79,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) | k1_xboole_0 != X2) )),
% 0.21/0.55    inference(definition_unfolding,[],[f69,f71])).
% 0.21/0.55  fof(f69,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 != X2) )),
% 0.21/0.55    inference(cnf_transformation,[],[f16])).
% 0.21/0.55  fof(f178,plain,(
% 0.21/0.55    ( ! [X1] : (k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X1) | k1_xboole_0 = X1) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f177,f36])).
% 0.21/0.55  fof(f177,plain,(
% 0.21/0.55    ( ! [X1] : (k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X1) | k1_xboole_0 = sK2 | k1_xboole_0 = X1) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f176,f35])).
% 0.21/0.55  fof(f176,plain,(
% 0.21/0.55    ( ! [X1] : (k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X1) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = X1) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f166,f34])).
% 0.21/0.55  fof(f166,plain,(
% 0.21/0.55    ( ! [X1] : (k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X1) | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = X1) )),
% 0.21/0.55    inference(superposition,[],[f82,f154])).
% 0.21/0.55  fof(f82,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3) )),
% 0.21/0.55    inference(definition_unfolding,[],[f66,f71])).
% 0.21/0.55  fof(f66,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3) )),
% 0.21/0.55    inference(cnf_transformation,[],[f16])).
% 0.21/0.55  fof(f36,plain,(
% 0.21/0.55    k1_xboole_0 != sK2),
% 0.21/0.55    inference(cnf_transformation,[],[f20])).
% 0.21/0.55  % SZS output end Proof for theBenchmark
% 0.21/0.55  % (1133)------------------------------
% 0.21/0.55  % (1133)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (1133)Termination reason: Refutation
% 0.21/0.55  
% 0.21/0.55  % (1133)Memory used [KB]: 1918
% 0.21/0.55  % (1133)Time elapsed: 0.137 s
% 0.21/0.55  % (1133)------------------------------
% 0.21/0.55  % (1133)------------------------------
% 0.21/0.55  % (1111)Success in time 0.189 s
%------------------------------------------------------------------------------
