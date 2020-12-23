%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:21 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.41s
% Verified   : 
% Statistics : Number of formulae       :  104 (1831 expanded)
%              Number of leaves         :   16 ( 544 expanded)
%              Depth                    :   27
%              Number of atoms          :  345 (10012 expanded)
%              Number of equality atoms :  109 (1802 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f382,plain,(
    $false ),
    inference(subsumption_resolution,[],[f369,f76])).

fof(f76,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f369,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(backward_demodulation,[],[f159,f362])).

fof(f362,plain,(
    k1_xboole_0 = k1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f361,f268])).

fof(f268,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f262,f87])).

fof(f87,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f262,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f51,f260])).

fof(f260,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f259,f205])).

fof(f205,plain,(
    sK4 = k1_funct_1(sK3,sK5(sK4,sK2,sK3)) ),
    inference(subsumption_resolution,[],[f204,f101])).

fof(f101,plain,(
    v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f98,f69])).

fof(f69,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f98,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f51,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f204,plain,
    ( sK4 = k1_funct_1(sK3,sK5(sK4,sK2,sK3))
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f198,f49])).

fof(f49,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ! [X5] :
        ( k1_funct_1(sK3,X5) != sK4
        | ~ r2_hidden(X5,sK2)
        | ~ m1_subset_1(X5,sK0) )
    & r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f20,f34,f33])).

fof(f33,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ! [X5] :
                ( k1_funct_1(X3,X5) != X4
                | ~ r2_hidden(X5,X2)
                | ~ m1_subset_1(X5,X0) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(sK3,X5) != X4
              | ~ r2_hidden(X5,sK2)
              | ~ m1_subset_1(X5,sK0) )
          & r2_hidden(X4,k7_relset_1(sK0,sK1,sK3,sK2)) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X4] :
        ( ! [X5] :
            ( k1_funct_1(sK3,X5) != X4
            | ~ r2_hidden(X5,sK2)
            | ~ m1_subset_1(X5,sK0) )
        & r2_hidden(X4,k7_relset_1(sK0,sK1,sK3,sK2)) )
   => ( ! [X5] :
          ( k1_funct_1(sK3,X5) != sK4
          | ~ r2_hidden(X5,sK2)
          | ~ m1_subset_1(X5,sK0) )
      & r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ) ),
    introduced(choice_axiom,[])).

% (20639)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ( m1_subset_1(X5,X0)
                 => ~ ( k1_funct_1(X3,X5) = X4
                      & r2_hidden(X5,X2) ) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ~ ( ! [X5] :
                ( m1_subset_1(X5,X0)
               => ~ ( k1_funct_1(X3,X5) = X4
                    & r2_hidden(X5,X2) ) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_funct_2)).

fof(f198,plain,
    ( sK4 = k1_funct_1(sK3,sK5(sK4,sK2,sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f122,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(f122,plain,(
    r2_hidden(k4_tarski(sK5(sK4,sK2,sK3),sK4),sK3) ),
    inference(subsumption_resolution,[],[f116,f101])).

fof(f116,plain,
    ( r2_hidden(k4_tarski(sK5(sK4,sK2,sK3),sK4),sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f100,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK5(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK5(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK5(X0,X1,X2),X0),X2)
            & r2_hidden(sK5(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f40,f41])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK5(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK5(X0,X1,X2),X0),X2)
        & r2_hidden(sK5(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X4,X0),X2)
              & r2_hidden(X4,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X3,X0),X2)
              & r2_hidden(X3,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

fof(f100,plain,(
    r2_hidden(sK4,k9_relat_1(sK3,sK2)) ),
    inference(backward_demodulation,[],[f52,f97])).

fof(f97,plain,(
    ! [X0] : k7_relset_1(sK0,sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(resolution,[],[f51,f57])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f52,plain,(
    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f35])).

fof(f259,plain,
    ( k1_xboole_0 = sK1
    | sK4 != k1_funct_1(sK3,sK5(sK4,sK2,sK3)) ),
    inference(subsumption_resolution,[],[f257,f123])).

fof(f123,plain,(
    r2_hidden(sK5(sK4,sK2,sK3),sK2) ),
    inference(subsumption_resolution,[],[f117,f101])).

fof(f117,plain,
    ( r2_hidden(sK5(sK4,sK2,sK3),sK2)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f100,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f257,plain,
    ( k1_xboole_0 = sK1
    | ~ r2_hidden(sK5(sK4,sK2,sK3),sK2)
    | sK4 != k1_funct_1(sK3,sK5(sK4,sK2,sK3)) ),
    inference(resolution,[],[f190,f53])).

fof(f53,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,sK0)
      | ~ r2_hidden(X5,sK2)
      | k1_funct_1(sK3,X5) != sK4 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f190,plain,
    ( m1_subset_1(sK5(sK4,sK2,sK3),sK0)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f161,f156])).

fof(f156,plain,
    ( sK0 = k1_relat_1(sK3)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f155,f51])).

fof(f155,plain,
    ( sK0 = k1_relat_1(sK3)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f152,f50])).

fof(f50,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f152,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f94,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f94,plain,(
    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) ),
    inference(resolution,[],[f51,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f161,plain,(
    m1_subset_1(sK5(sK4,sK2,sK3),k1_relat_1(sK3)) ),
    inference(resolution,[],[f121,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f121,plain,(
    r2_hidden(sK5(sK4,sK2,sK3),k1_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f115,f101])).

fof(f115,plain,
    ( r2_hidden(sK5(sK4,sK2,sK3),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f100,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),k1_relat_1(X2))
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f51,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f35])).

fof(f361,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = k1_relat_1(sK3) ),
    inference(forward_demodulation,[],[f360,f87])).

fof(f360,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(forward_demodulation,[],[f350,f341])).

fof(f341,plain,(
    k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) ),
    inference(backward_demodulation,[],[f264,f337])).

fof(f337,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f327,f76])).

fof(f327,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f199,f281])).

fof(f281,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f280,f268])).

fof(f280,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0 ),
    inference(forward_demodulation,[],[f271,f87])).

fof(f271,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    inference(resolution,[],[f261,f84])).

fof(f84,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f261,plain,(
    v1_funct_2(sK3,sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f50,f260])).

fof(f199,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(resolution,[],[f122,f78])).

fof(f78,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK6(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f46,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK6(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f264,plain,(
    k1_relat_1(sK3) = k1_relset_1(sK0,k1_xboole_0,sK3) ),
    inference(backward_demodulation,[],[f94,f260])).

fof(f350,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(resolution,[],[f340,f86])).

fof(f86,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f340,plain,(
    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f261,f337])).

fof(f159,plain,(
    ~ v1_xboole_0(k1_relat_1(sK3)) ),
    inference(resolution,[],[f121,f78])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:24:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (20637)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.50  % (20656)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.50  % (20665)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.51  % (20659)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % (20637)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % (20649)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (20663)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.51  % (20645)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.51  % (20646)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.51  % (20659)Refutation not found, incomplete strategy% (20659)------------------------------
% 0.21/0.51  % (20659)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (20643)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (20641)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (20659)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (20659)Memory used [KB]: 10874
% 0.21/0.52  % (20659)Time elapsed: 0.069 s
% 0.21/0.52  % (20659)------------------------------
% 0.21/0.52  % (20659)------------------------------
% 0.21/0.52  % (20664)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.52  % (20648)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (20657)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.52  % (20648)Refutation not found, incomplete strategy% (20648)------------------------------
% 0.21/0.52  % (20648)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (20648)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (20648)Memory used [KB]: 10746
% 0.21/0.52  % (20648)Time elapsed: 0.122 s
% 0.21/0.52  % (20648)------------------------------
% 0.21/0.52  % (20648)------------------------------
% 0.21/0.53  % (20647)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (20642)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (20655)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.41/0.53  % SZS output start Proof for theBenchmark
% 1.41/0.53  fof(f382,plain,(
% 1.41/0.53    $false),
% 1.41/0.53    inference(subsumption_resolution,[],[f369,f76])).
% 1.41/0.53  fof(f76,plain,(
% 1.41/0.53    v1_xboole_0(k1_xboole_0)),
% 1.41/0.53    inference(cnf_transformation,[],[f3])).
% 1.41/0.53  fof(f3,axiom,(
% 1.41/0.53    v1_xboole_0(k1_xboole_0)),
% 1.41/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.41/0.53  fof(f369,plain,(
% 1.41/0.53    ~v1_xboole_0(k1_xboole_0)),
% 1.41/0.53    inference(backward_demodulation,[],[f159,f362])).
% 1.41/0.53  fof(f362,plain,(
% 1.41/0.53    k1_xboole_0 = k1_relat_1(sK3)),
% 1.41/0.53    inference(subsumption_resolution,[],[f361,f268])).
% 1.41/0.53  fof(f268,plain,(
% 1.41/0.53    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))),
% 1.41/0.53    inference(forward_demodulation,[],[f262,f87])).
% 1.41/0.53  fof(f87,plain,(
% 1.41/0.53    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.41/0.53    inference(equality_resolution,[],[f75])).
% 1.41/0.53  fof(f75,plain,(
% 1.41/0.53    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.41/0.53    inference(cnf_transformation,[],[f44])).
% 1.41/0.53  fof(f44,plain,(
% 1.41/0.53    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.41/0.53    inference(flattening,[],[f43])).
% 1.41/0.53  fof(f43,plain,(
% 1.41/0.53    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.41/0.53    inference(nnf_transformation,[],[f5])).
% 1.41/0.53  fof(f5,axiom,(
% 1.41/0.53    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.41/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.41/0.53  fof(f262,plain,(
% 1.41/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))),
% 1.41/0.53    inference(backward_demodulation,[],[f51,f260])).
% 1.41/0.53  fof(f260,plain,(
% 1.41/0.53    k1_xboole_0 = sK1),
% 1.41/0.53    inference(subsumption_resolution,[],[f259,f205])).
% 1.41/0.53  fof(f205,plain,(
% 1.41/0.53    sK4 = k1_funct_1(sK3,sK5(sK4,sK2,sK3))),
% 1.41/0.53    inference(subsumption_resolution,[],[f204,f101])).
% 1.41/0.53  fof(f101,plain,(
% 1.41/0.53    v1_relat_1(sK3)),
% 1.41/0.53    inference(subsumption_resolution,[],[f98,f69])).
% 1.41/0.53  fof(f69,plain,(
% 1.41/0.53    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.41/0.53    inference(cnf_transformation,[],[f11])).
% 1.41/0.53  fof(f11,axiom,(
% 1.41/0.53    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.41/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.41/0.53  fof(f98,plain,(
% 1.41/0.53    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 1.41/0.53    inference(resolution,[],[f51,f70])).
% 1.41/0.53  fof(f70,plain,(
% 1.41/0.53    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.41/0.53    inference(cnf_transformation,[],[f28])).
% 1.41/0.53  fof(f28,plain,(
% 1.41/0.53    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.41/0.53    inference(ennf_transformation,[],[f10])).
% 1.41/0.53  fof(f10,axiom,(
% 1.41/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.41/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.41/0.53  fof(f204,plain,(
% 1.41/0.53    sK4 = k1_funct_1(sK3,sK5(sK4,sK2,sK3)) | ~v1_relat_1(sK3)),
% 1.41/0.53    inference(subsumption_resolution,[],[f198,f49])).
% 1.41/0.53  fof(f49,plain,(
% 1.41/0.53    v1_funct_1(sK3)),
% 1.41/0.53    inference(cnf_transformation,[],[f35])).
% 1.41/0.53  fof(f35,plain,(
% 1.41/0.53    (! [X5] : (k1_funct_1(sK3,X5) != sK4 | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,sK0)) & r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 1.41/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f20,f34,f33])).
% 1.41/0.53  fof(f33,plain,(
% 1.41/0.53    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (! [X5] : (k1_funct_1(sK3,X5) != X4 | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,sK0)) & r2_hidden(X4,k7_relset_1(sK0,sK1,sK3,sK2))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 1.41/0.53    introduced(choice_axiom,[])).
% 1.41/0.53  fof(f34,plain,(
% 1.41/0.53    ? [X4] : (! [X5] : (k1_funct_1(sK3,X5) != X4 | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,sK0)) & r2_hidden(X4,k7_relset_1(sK0,sK1,sK3,sK2))) => (! [X5] : (k1_funct_1(sK3,X5) != sK4 | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,sK0)) & r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)))),
% 1.41/0.53    introduced(choice_axiom,[])).
% 1.41/0.53  % (20639)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.41/0.53  fof(f20,plain,(
% 1.41/0.53    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 1.41/0.53    inference(flattening,[],[f19])).
% 1.41/0.53  fof(f19,plain,(
% 1.41/0.53    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : ((k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2)) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 1.41/0.53    inference(ennf_transformation,[],[f18])).
% 1.41/0.53  fof(f18,negated_conjecture,(
% 1.41/0.53    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 1.41/0.53    inference(negated_conjecture,[],[f17])).
% 1.41/0.53  fof(f17,conjecture,(
% 1.41/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 1.41/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_funct_2)).
% 1.41/0.53  fof(f198,plain,(
% 1.41/0.53    sK4 = k1_funct_1(sK3,sK5(sK4,sK2,sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 1.41/0.53    inference(resolution,[],[f122,f55])).
% 1.41/0.53  fof(f55,plain,(
% 1.41/0.53    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.41/0.53    inference(cnf_transformation,[],[f37])).
% 1.41/0.53  fof(f37,plain,(
% 1.41/0.53    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.41/0.53    inference(flattening,[],[f36])).
% 1.41/0.53  fof(f36,plain,(
% 1.41/0.53    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.41/0.53    inference(nnf_transformation,[],[f22])).
% 1.41/0.53  fof(f22,plain,(
% 1.41/0.53    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.41/0.53    inference(flattening,[],[f21])).
% 1.41/0.53  fof(f21,plain,(
% 1.41/0.53    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.41/0.53    inference(ennf_transformation,[],[f13])).
% 1.41/0.53  fof(f13,axiom,(
% 1.41/0.53    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 1.41/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).
% 1.41/0.53  fof(f122,plain,(
% 1.41/0.53    r2_hidden(k4_tarski(sK5(sK4,sK2,sK3),sK4),sK3)),
% 1.41/0.53    inference(subsumption_resolution,[],[f116,f101])).
% 1.41/0.53  fof(f116,plain,(
% 1.41/0.53    r2_hidden(k4_tarski(sK5(sK4,sK2,sK3),sK4),sK3) | ~v1_relat_1(sK3)),
% 1.41/0.53    inference(resolution,[],[f100,f66])).
% 1.41/0.53  fof(f66,plain,(
% 1.41/0.53    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK5(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 1.41/0.53    inference(cnf_transformation,[],[f42])).
% 1.41/0.53  fof(f42,plain,(
% 1.41/0.53    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK5(X0,X1,X2),X0),X2) & r2_hidden(sK5(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.41/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f40,f41])).
% 1.41/0.53  fof(f41,plain,(
% 1.41/0.53    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK5(X0,X1,X2),X0),X2) & r2_hidden(sK5(X0,X1,X2),k1_relat_1(X2))))),
% 1.41/0.53    introduced(choice_axiom,[])).
% 1.41/0.53  fof(f40,plain,(
% 1.41/0.53    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.41/0.53    inference(rectify,[],[f39])).
% 1.41/0.53  fof(f39,plain,(
% 1.41/0.53    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.41/0.53    inference(nnf_transformation,[],[f27])).
% 1.41/0.53  fof(f27,plain,(
% 1.41/0.53    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 1.41/0.53    inference(ennf_transformation,[],[f12])).
% 1.41/0.53  fof(f12,axiom,(
% 1.41/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 1.41/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).
% 1.41/0.53  fof(f100,plain,(
% 1.41/0.53    r2_hidden(sK4,k9_relat_1(sK3,sK2))),
% 1.41/0.53    inference(backward_demodulation,[],[f52,f97])).
% 1.41/0.53  fof(f97,plain,(
% 1.41/0.53    ( ! [X0] : (k7_relset_1(sK0,sK1,sK3,X0) = k9_relat_1(sK3,X0)) )),
% 1.41/0.53    inference(resolution,[],[f51,f57])).
% 1.41/0.53  fof(f57,plain,(
% 1.41/0.53    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.41/0.53    inference(cnf_transformation,[],[f23])).
% 1.41/0.53  fof(f23,plain,(
% 1.41/0.53    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.41/0.53    inference(ennf_transformation,[],[f15])).
% 1.41/0.53  fof(f15,axiom,(
% 1.41/0.53    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 1.41/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 1.41/0.53  fof(f52,plain,(
% 1.41/0.53    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 1.41/0.53    inference(cnf_transformation,[],[f35])).
% 1.41/0.53  fof(f259,plain,(
% 1.41/0.53    k1_xboole_0 = sK1 | sK4 != k1_funct_1(sK3,sK5(sK4,sK2,sK3))),
% 1.41/0.53    inference(subsumption_resolution,[],[f257,f123])).
% 1.41/0.53  fof(f123,plain,(
% 1.41/0.53    r2_hidden(sK5(sK4,sK2,sK3),sK2)),
% 1.41/0.53    inference(subsumption_resolution,[],[f117,f101])).
% 1.41/0.53  fof(f117,plain,(
% 1.41/0.53    r2_hidden(sK5(sK4,sK2,sK3),sK2) | ~v1_relat_1(sK3)),
% 1.41/0.53    inference(resolution,[],[f100,f67])).
% 1.41/0.53  fof(f67,plain,(
% 1.41/0.53    ( ! [X2,X0,X1] : (r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 1.41/0.53    inference(cnf_transformation,[],[f42])).
% 1.41/0.53  fof(f257,plain,(
% 1.41/0.53    k1_xboole_0 = sK1 | ~r2_hidden(sK5(sK4,sK2,sK3),sK2) | sK4 != k1_funct_1(sK3,sK5(sK4,sK2,sK3))),
% 1.41/0.53    inference(resolution,[],[f190,f53])).
% 1.41/0.53  fof(f53,plain,(
% 1.41/0.53    ( ! [X5] : (~m1_subset_1(X5,sK0) | ~r2_hidden(X5,sK2) | k1_funct_1(sK3,X5) != sK4) )),
% 1.41/0.53    inference(cnf_transformation,[],[f35])).
% 1.41/0.53  fof(f190,plain,(
% 1.41/0.53    m1_subset_1(sK5(sK4,sK2,sK3),sK0) | k1_xboole_0 = sK1),
% 1.41/0.53    inference(superposition,[],[f161,f156])).
% 1.41/0.53  fof(f156,plain,(
% 1.41/0.53    sK0 = k1_relat_1(sK3) | k1_xboole_0 = sK1),
% 1.41/0.53    inference(subsumption_resolution,[],[f155,f51])).
% 1.41/0.53  fof(f155,plain,(
% 1.41/0.53    sK0 = k1_relat_1(sK3) | k1_xboole_0 = sK1 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.41/0.53    inference(subsumption_resolution,[],[f152,f50])).
% 1.41/0.53  fof(f50,plain,(
% 1.41/0.53    v1_funct_2(sK3,sK0,sK1)),
% 1.41/0.53    inference(cnf_transformation,[],[f35])).
% 1.41/0.53  fof(f152,plain,(
% 1.41/0.53    sK0 = k1_relat_1(sK3) | ~v1_funct_2(sK3,sK0,sK1) | k1_xboole_0 = sK1 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.41/0.53    inference(superposition,[],[f94,f59])).
% 1.41/0.53  fof(f59,plain,(
% 1.41/0.53    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.41/0.53    inference(cnf_transformation,[],[f38])).
% 1.41/0.53  fof(f38,plain,(
% 1.41/0.53    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.41/0.53    inference(nnf_transformation,[],[f26])).
% 1.41/0.53  fof(f26,plain,(
% 1.41/0.53    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.41/0.53    inference(flattening,[],[f25])).
% 1.41/0.53  fof(f25,plain,(
% 1.41/0.53    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.41/0.53    inference(ennf_transformation,[],[f16])).
% 1.41/0.53  fof(f16,axiom,(
% 1.41/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.41/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.41/0.53  fof(f94,plain,(
% 1.41/0.53    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)),
% 1.41/0.53    inference(resolution,[],[f51,f72])).
% 1.41/0.53  fof(f72,plain,(
% 1.41/0.53    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.41/0.53    inference(cnf_transformation,[],[f30])).
% 1.41/0.53  fof(f30,plain,(
% 1.41/0.53    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.41/0.53    inference(ennf_transformation,[],[f14])).
% 1.41/0.53  fof(f14,axiom,(
% 1.41/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 1.41/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.41/0.53  fof(f161,plain,(
% 1.41/0.53    m1_subset_1(sK5(sK4,sK2,sK3),k1_relat_1(sK3))),
% 1.41/0.53    inference(resolution,[],[f121,f58])).
% 1.41/0.53  fof(f58,plain,(
% 1.41/0.53    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 1.41/0.53    inference(cnf_transformation,[],[f24])).
% 1.41/0.53  fof(f24,plain,(
% 1.41/0.53    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.41/0.53    inference(ennf_transformation,[],[f7])).
% 1.41/0.53  fof(f7,axiom,(
% 1.41/0.53    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.41/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 1.41/0.53  fof(f121,plain,(
% 1.41/0.53    r2_hidden(sK5(sK4,sK2,sK3),k1_relat_1(sK3))),
% 1.41/0.53    inference(subsumption_resolution,[],[f115,f101])).
% 1.41/0.53  fof(f115,plain,(
% 1.41/0.53    r2_hidden(sK5(sK4,sK2,sK3),k1_relat_1(sK3)) | ~v1_relat_1(sK3)),
% 1.41/0.53    inference(resolution,[],[f100,f65])).
% 1.41/0.53  fof(f65,plain,(
% 1.41/0.53    ( ! [X2,X0,X1] : (r2_hidden(sK5(X0,X1,X2),k1_relat_1(X2)) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 1.41/0.53    inference(cnf_transformation,[],[f42])).
% 1.41/0.53  fof(f51,plain,(
% 1.41/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.41/0.53    inference(cnf_transformation,[],[f35])).
% 1.41/0.53  fof(f361,plain,(
% 1.41/0.53    ~m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k1_relat_1(sK3)),
% 1.41/0.53    inference(forward_demodulation,[],[f360,f87])).
% 1.41/0.53  fof(f360,plain,(
% 1.41/0.53    k1_xboole_0 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 1.41/0.53    inference(forward_demodulation,[],[f350,f341])).
% 1.41/0.53  fof(f341,plain,(
% 1.41/0.53    k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)),
% 1.41/0.53    inference(backward_demodulation,[],[f264,f337])).
% 1.41/0.53  fof(f337,plain,(
% 1.41/0.53    k1_xboole_0 = sK0),
% 1.41/0.53    inference(subsumption_resolution,[],[f327,f76])).
% 1.41/0.53  fof(f327,plain,(
% 1.41/0.53    ~v1_xboole_0(k1_xboole_0) | k1_xboole_0 = sK0),
% 1.41/0.53    inference(superposition,[],[f199,f281])).
% 1.41/0.53  fof(f281,plain,(
% 1.41/0.53    k1_xboole_0 = sK3 | k1_xboole_0 = sK0),
% 1.41/0.53    inference(subsumption_resolution,[],[f280,f268])).
% 1.41/0.53  fof(f280,plain,(
% 1.41/0.53    ~m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = sK3 | k1_xboole_0 = sK0),
% 1.41/0.53    inference(forward_demodulation,[],[f271,f87])).
% 1.41/0.53  fof(f271,plain,(
% 1.41/0.53    k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))),
% 1.41/0.53    inference(resolution,[],[f261,f84])).
% 1.41/0.53  fof(f84,plain,(
% 1.41/0.53    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 1.41/0.53    inference(equality_resolution,[],[f63])).
% 1.41/0.53  fof(f63,plain,(
% 1.41/0.53    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.41/0.53    inference(cnf_transformation,[],[f38])).
% 1.41/0.53  fof(f261,plain,(
% 1.41/0.53    v1_funct_2(sK3,sK0,k1_xboole_0)),
% 1.41/0.53    inference(backward_demodulation,[],[f50,f260])).
% 1.41/0.53  fof(f199,plain,(
% 1.41/0.53    ~v1_xboole_0(sK3)),
% 1.41/0.53    inference(resolution,[],[f122,f78])).
% 1.41/0.53  fof(f78,plain,(
% 1.41/0.53    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 1.41/0.53    inference(cnf_transformation,[],[f48])).
% 1.41/0.53  fof(f48,plain,(
% 1.41/0.53    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK6(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.41/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f46,f47])).
% 1.41/0.53  fof(f47,plain,(
% 1.41/0.53    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK6(X0),X0))),
% 1.41/0.53    introduced(choice_axiom,[])).
% 1.41/0.53  fof(f46,plain,(
% 1.41/0.53    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.41/0.53    inference(rectify,[],[f45])).
% 1.41/0.53  fof(f45,plain,(
% 1.41/0.53    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.41/0.53    inference(nnf_transformation,[],[f1])).
% 1.41/0.53  fof(f1,axiom,(
% 1.41/0.53    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.41/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.41/0.53  fof(f264,plain,(
% 1.41/0.53    k1_relat_1(sK3) = k1_relset_1(sK0,k1_xboole_0,sK3)),
% 1.41/0.53    inference(backward_demodulation,[],[f94,f260])).
% 1.41/0.53  fof(f350,plain,(
% 1.41/0.53    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 1.41/0.53    inference(resolution,[],[f340,f86])).
% 1.41/0.53  fof(f86,plain,(
% 1.41/0.53    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 1.41/0.53    inference(equality_resolution,[],[f60])).
% 1.41/0.53  fof(f60,plain,(
% 1.41/0.53    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.41/0.53    inference(cnf_transformation,[],[f38])).
% 1.41/0.53  fof(f340,plain,(
% 1.41/0.53    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)),
% 1.41/0.53    inference(backward_demodulation,[],[f261,f337])).
% 1.41/0.53  fof(f159,plain,(
% 1.41/0.53    ~v1_xboole_0(k1_relat_1(sK3))),
% 1.41/0.53    inference(resolution,[],[f121,f78])).
% 1.41/0.53  % SZS output end Proof for theBenchmark
% 1.41/0.53  % (20637)------------------------------
% 1.41/0.53  % (20637)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.53  % (20637)Termination reason: Refutation
% 1.41/0.53  
% 1.41/0.53  % (20637)Memory used [KB]: 1918
% 1.41/0.53  % (20637)Time elapsed: 0.108 s
% 1.41/0.53  % (20637)------------------------------
% 1.41/0.53  % (20637)------------------------------
% 1.41/0.53  % (20640)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.41/0.53  % (20636)Success in time 0.179 s
%------------------------------------------------------------------------------
