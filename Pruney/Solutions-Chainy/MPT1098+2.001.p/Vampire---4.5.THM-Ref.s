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
% DateTime   : Thu Dec  3 13:08:26 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 179 expanded)
%              Number of leaves         :   12 (  47 expanded)
%              Depth                    :   17
%              Number of atoms          :  217 ( 664 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f413,plain,(
    $false ),
    inference(subsumption_resolution,[],[f411,f81])).

fof(f81,plain,(
    v1_finset_1(sK3(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f70,f36])).

fof(f36,plain,(
    v1_finset_1(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ! [X3] :
        ( ~ r1_tarski(sK0,k2_zfmisc_1(X3,sK2))
        | ~ r1_tarski(X3,sK1)
        | ~ v1_finset_1(X3) )
    & r1_tarski(sK0,k2_zfmisc_1(sK1,sK2))
    & v1_finset_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f27])).

fof(f27,plain,
    ( ? [X0,X1,X2] :
        ( ! [X3] :
            ( ~ r1_tarski(X0,k2_zfmisc_1(X3,X2))
            | ~ r1_tarski(X3,X1)
            | ~ v1_finset_1(X3) )
        & r1_tarski(X0,k2_zfmisc_1(X1,X2))
        & v1_finset_1(X0) )
   => ( ! [X3] :
          ( ~ r1_tarski(sK0,k2_zfmisc_1(X3,sK2))
          | ~ r1_tarski(X3,sK1)
          | ~ v1_finset_1(X3) )
      & r1_tarski(sK0,k2_zfmisc_1(sK1,sK2))
      & v1_finset_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ! [X3] :
          ( ~ r1_tarski(X0,k2_zfmisc_1(X3,X2))
          | ~ r1_tarski(X3,X1)
          | ~ v1_finset_1(X3) )
      & r1_tarski(X0,k2_zfmisc_1(X1,X2))
      & v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ! [X3] :
              ~ ( r1_tarski(X0,k2_zfmisc_1(X3,X2))
                & r1_tarski(X3,X1)
                & v1_finset_1(X3) )
          & r1_tarski(X0,k2_zfmisc_1(X1,X2))
          & v1_finset_1(X0) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ! [X3] :
            ~ ( r1_tarski(X0,k2_zfmisc_1(X3,X2))
              & r1_tarski(X3,X1)
              & v1_finset_1(X3) )
        & r1_tarski(X0,k2_zfmisc_1(X1,X2))
        & v1_finset_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_finset_1)).

fof(f70,plain,
    ( v1_finset_1(sK3(sK0,sK1,sK2))
    | ~ v1_finset_1(sK0) ),
    inference(resolution,[],[f37,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( v1_finset_1(sK3(X0,X1,X2))
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | ~ v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_zfmisc_1(sK3(X0,X1,X2),sK4(X0,X1,X2)))
        & r1_tarski(sK4(X0,X1,X2),X2)
        & v1_finset_1(sK4(X0,X1,X2))
        & r1_tarski(sK3(X0,X1,X2),X1)
        & v1_finset_1(sK3(X0,X1,X2)) )
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | ~ v1_finset_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f26,f34])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( r1_tarski(X0,k2_zfmisc_1(X3,X4))
          & r1_tarski(X4,X2)
          & v1_finset_1(X4)
          & r1_tarski(X3,X1)
          & v1_finset_1(X3) )
     => ( r1_tarski(X0,k2_zfmisc_1(sK3(X0,X1,X2),sK4(X0,X1,X2)))
        & r1_tarski(sK4(X0,X1,X2),X2)
        & v1_finset_1(sK4(X0,X1,X2))
        & r1_tarski(sK3(X0,X1,X2),X1)
        & v1_finset_1(sK3(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ? [X3,X4] :
          ( r1_tarski(X0,k2_zfmisc_1(X3,X4))
          & r1_tarski(X4,X2)
          & v1_finset_1(X4)
          & r1_tarski(X3,X1)
          & v1_finset_1(X3) )
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | ~ v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ~ ( ! [X3,X4] :
            ~ ( r1_tarski(X0,k2_zfmisc_1(X3,X4))
              & r1_tarski(X4,X2)
              & v1_finset_1(X4)
              & r1_tarski(X3,X1)
              & v1_finset_1(X3) )
        & r1_tarski(X0,k2_zfmisc_1(X1,X2))
        & v1_finset_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_finset_1)).

fof(f37,plain,(
    r1_tarski(sK0,k2_zfmisc_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f28])).

fof(f411,plain,(
    ~ v1_finset_1(sK3(sK0,sK1,sK2)) ),
    inference(resolution,[],[f394,f376])).

fof(f376,plain,(
    ! [X0] :
      ( ~ v4_relat_1(sK0,X0)
      | ~ v1_finset_1(X0) ) ),
    inference(subsumption_resolution,[],[f368,f114])).

fof(f114,plain,(
    v1_relat_1(sK0) ),
    inference(resolution,[],[f75,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f75,plain,(
    m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(resolution,[],[f37,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f368,plain,(
    ! [X0] :
      ( ~ v1_finset_1(X0)
      | ~ v4_relat_1(sK0,X0)
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f347,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f347,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK0),X0)
      | ~ v1_finset_1(X0) ) ),
    inference(resolution,[],[f341,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v1_finset_1(X0)
      | ~ v1_finset_1(X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( v1_finset_1(X0)
      | ~ v1_finset_1(X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( v1_finset_1(X0)
      | ~ v1_finset_1(X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_finset_1(X1)
        & r1_tarski(X0,X1) )
     => v1_finset_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_finset_1)).

fof(f341,plain,(
    ~ v1_finset_1(k1_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f334,f149])).

fof(f149,plain,(
    r1_tarski(k1_relat_1(sK0),sK1) ),
    inference(subsumption_resolution,[],[f148,f114])).

fof(f148,plain,
    ( r1_tarski(k1_relat_1(sK0),sK1)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f112,f45])).

fof(f112,plain,(
    v4_relat_1(sK0,sK1) ),
    inference(resolution,[],[f75,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f334,plain,
    ( ~ r1_tarski(k1_relat_1(sK0),sK1)
    | ~ v1_finset_1(k1_relat_1(sK0)) ),
    inference(resolution,[],[f250,f63])).

fof(f63,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f250,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK0),X0)
      | ~ r1_tarski(X0,sK1)
      | ~ v1_finset_1(X0) ) ),
    inference(subsumption_resolution,[],[f249,f114])).

fof(f249,plain,(
    ! [X0] :
      ( ~ v1_finset_1(X0)
      | ~ r1_tarski(X0,sK1)
      | ~ r1_tarski(k1_relat_1(sK0),X0)
      | ~ v1_relat_1(sK0) ) ),
    inference(subsumption_resolution,[],[f247,f166])).

fof(f166,plain,(
    r1_tarski(k2_relat_1(sK0),sK2) ),
    inference(subsumption_resolution,[],[f165,f114])).

fof(f165,plain,
    ( r1_tarski(k2_relat_1(sK0),sK2)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f113,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f113,plain,(
    v5_relat_1(sK0,sK2) ),
    inference(resolution,[],[f75,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f247,plain,(
    ! [X0] :
      ( ~ v1_finset_1(X0)
      | ~ r1_tarski(X0,sK1)
      | ~ r1_tarski(k2_relat_1(sK0),sK2)
      | ~ r1_tarski(k1_relat_1(sK0),X0)
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f89,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(f89,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
      | ~ v1_finset_1(X0)
      | ~ r1_tarski(X0,sK1) ) ),
    inference(resolution,[],[f38,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f38,plain,(
    ! [X3] :
      ( ~ r1_tarski(sK0,k2_zfmisc_1(X3,sK2))
      | ~ r1_tarski(X3,sK1)
      | ~ v1_finset_1(X3) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f394,plain,(
    v4_relat_1(sK0,sK3(sK0,sK1,sK2)) ),
    inference(resolution,[],[f222,f55])).

fof(f222,plain,(
    m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(sK3(sK0,sK1,sK2),sK4(sK0,sK1,sK2)))) ),
    inference(resolution,[],[f85,f52])).

fof(f85,plain,(
    r1_tarski(sK0,k2_zfmisc_1(sK3(sK0,sK1,sK2),sK4(sK0,sK1,sK2))) ),
    inference(subsumption_resolution,[],[f74,f36])).

fof(f74,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(sK3(sK0,sK1,sK2),sK4(sK0,sK1,sK2)))
    | ~ v1_finset_1(sK0) ),
    inference(resolution,[],[f37,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_zfmisc_1(sK3(X0,X1,X2),sK4(X0,X1,X2)))
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | ~ v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:40:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.46  % (1291)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.19/0.46  % (1283)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.19/0.48  % (1291)Refutation found. Thanks to Tanya!
% 0.19/0.48  % SZS status Theorem for theBenchmark
% 0.19/0.49  % SZS output start Proof for theBenchmark
% 0.19/0.49  fof(f413,plain,(
% 0.19/0.49    $false),
% 0.19/0.49    inference(subsumption_resolution,[],[f411,f81])).
% 0.19/0.49  fof(f81,plain,(
% 0.19/0.49    v1_finset_1(sK3(sK0,sK1,sK2))),
% 0.19/0.49    inference(subsumption_resolution,[],[f70,f36])).
% 0.19/0.49  fof(f36,plain,(
% 0.19/0.49    v1_finset_1(sK0)),
% 0.19/0.49    inference(cnf_transformation,[],[f28])).
% 0.19/0.49  fof(f28,plain,(
% 0.19/0.49    ! [X3] : (~r1_tarski(sK0,k2_zfmisc_1(X3,sK2)) | ~r1_tarski(X3,sK1) | ~v1_finset_1(X3)) & r1_tarski(sK0,k2_zfmisc_1(sK1,sK2)) & v1_finset_1(sK0)),
% 0.19/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f27])).
% 0.19/0.49  fof(f27,plain,(
% 0.19/0.49    ? [X0,X1,X2] : (! [X3] : (~r1_tarski(X0,k2_zfmisc_1(X3,X2)) | ~r1_tarski(X3,X1) | ~v1_finset_1(X3)) & r1_tarski(X0,k2_zfmisc_1(X1,X2)) & v1_finset_1(X0)) => (! [X3] : (~r1_tarski(sK0,k2_zfmisc_1(X3,sK2)) | ~r1_tarski(X3,sK1) | ~v1_finset_1(X3)) & r1_tarski(sK0,k2_zfmisc_1(sK1,sK2)) & v1_finset_1(sK0))),
% 0.19/0.49    introduced(choice_axiom,[])).
% 0.19/0.49  fof(f15,plain,(
% 0.19/0.49    ? [X0,X1,X2] : (! [X3] : (~r1_tarski(X0,k2_zfmisc_1(X3,X2)) | ~r1_tarski(X3,X1) | ~v1_finset_1(X3)) & r1_tarski(X0,k2_zfmisc_1(X1,X2)) & v1_finset_1(X0))),
% 0.19/0.49    inference(ennf_transformation,[],[f14])).
% 0.19/0.49  fof(f14,negated_conjecture,(
% 0.19/0.49    ~! [X0,X1,X2] : ~(! [X3] : ~(r1_tarski(X0,k2_zfmisc_1(X3,X2)) & r1_tarski(X3,X1) & v1_finset_1(X3)) & r1_tarski(X0,k2_zfmisc_1(X1,X2)) & v1_finset_1(X0))),
% 0.19/0.49    inference(negated_conjecture,[],[f13])).
% 0.19/0.49  fof(f13,conjecture,(
% 0.19/0.49    ! [X0,X1,X2] : ~(! [X3] : ~(r1_tarski(X0,k2_zfmisc_1(X3,X2)) & r1_tarski(X3,X1) & v1_finset_1(X3)) & r1_tarski(X0,k2_zfmisc_1(X1,X2)) & v1_finset_1(X0))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_finset_1)).
% 0.19/0.49  fof(f70,plain,(
% 0.19/0.49    v1_finset_1(sK3(sK0,sK1,sK2)) | ~v1_finset_1(sK0)),
% 0.19/0.49    inference(resolution,[],[f37,f57])).
% 0.19/0.49  fof(f57,plain,(
% 0.19/0.49    ( ! [X2,X0,X1] : (v1_finset_1(sK3(X0,X1,X2)) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2)) | ~v1_finset_1(X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f35])).
% 0.19/0.49  fof(f35,plain,(
% 0.19/0.49    ! [X0,X1,X2] : ((r1_tarski(X0,k2_zfmisc_1(sK3(X0,X1,X2),sK4(X0,X1,X2))) & r1_tarski(sK4(X0,X1,X2),X2) & v1_finset_1(sK4(X0,X1,X2)) & r1_tarski(sK3(X0,X1,X2),X1) & v1_finset_1(sK3(X0,X1,X2))) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2)) | ~v1_finset_1(X0))),
% 0.19/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f26,f34])).
% 0.19/0.49  fof(f34,plain,(
% 0.19/0.49    ! [X2,X1,X0] : (? [X3,X4] : (r1_tarski(X0,k2_zfmisc_1(X3,X4)) & r1_tarski(X4,X2) & v1_finset_1(X4) & r1_tarski(X3,X1) & v1_finset_1(X3)) => (r1_tarski(X0,k2_zfmisc_1(sK3(X0,X1,X2),sK4(X0,X1,X2))) & r1_tarski(sK4(X0,X1,X2),X2) & v1_finset_1(sK4(X0,X1,X2)) & r1_tarski(sK3(X0,X1,X2),X1) & v1_finset_1(sK3(X0,X1,X2))))),
% 0.19/0.49    introduced(choice_axiom,[])).
% 0.19/0.49  fof(f26,plain,(
% 0.19/0.49    ! [X0,X1,X2] : (? [X3,X4] : (r1_tarski(X0,k2_zfmisc_1(X3,X4)) & r1_tarski(X4,X2) & v1_finset_1(X4) & r1_tarski(X3,X1) & v1_finset_1(X3)) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2)) | ~v1_finset_1(X0))),
% 0.19/0.49    inference(ennf_transformation,[],[f12])).
% 0.19/0.49  fof(f12,axiom,(
% 0.19/0.49    ! [X0,X1,X2] : ~(! [X3,X4] : ~(r1_tarski(X0,k2_zfmisc_1(X3,X4)) & r1_tarski(X4,X2) & v1_finset_1(X4) & r1_tarski(X3,X1) & v1_finset_1(X3)) & r1_tarski(X0,k2_zfmisc_1(X1,X2)) & v1_finset_1(X0))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_finset_1)).
% 0.19/0.49  fof(f37,plain,(
% 0.19/0.49    r1_tarski(sK0,k2_zfmisc_1(sK1,sK2))),
% 0.19/0.49    inference(cnf_transformation,[],[f28])).
% 0.19/0.49  fof(f411,plain,(
% 0.19/0.49    ~v1_finset_1(sK3(sK0,sK1,sK2))),
% 0.19/0.49    inference(resolution,[],[f394,f376])).
% 0.19/0.49  fof(f376,plain,(
% 0.19/0.49    ( ! [X0] : (~v4_relat_1(sK0,X0) | ~v1_finset_1(X0)) )),
% 0.19/0.49    inference(subsumption_resolution,[],[f368,f114])).
% 0.19/0.49  fof(f114,plain,(
% 0.19/0.49    v1_relat_1(sK0)),
% 0.19/0.49    inference(resolution,[],[f75,f54])).
% 0.19/0.49  fof(f54,plain,(
% 0.19/0.49    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.19/0.49    inference(cnf_transformation,[],[f24])).
% 0.19/0.49  fof(f24,plain,(
% 0.19/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.49    inference(ennf_transformation,[],[f8])).
% 0.19/0.49  fof(f8,axiom,(
% 0.19/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.19/0.49  fof(f75,plain,(
% 0.19/0.49    m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.19/0.49    inference(resolution,[],[f37,f52])).
% 0.19/0.49  fof(f52,plain,(
% 0.19/0.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f33])).
% 0.19/0.49  fof(f33,plain,(
% 0.19/0.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.19/0.49    inference(nnf_transformation,[],[f2])).
% 0.19/0.49  fof(f2,axiom,(
% 0.19/0.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.19/0.49  fof(f368,plain,(
% 0.19/0.49    ( ! [X0] : (~v1_finset_1(X0) | ~v4_relat_1(sK0,X0) | ~v1_relat_1(sK0)) )),
% 0.19/0.49    inference(resolution,[],[f347,f45])).
% 0.19/0.49  fof(f45,plain,(
% 0.19/0.49    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f30])).
% 0.19/0.49  fof(f30,plain,(
% 0.19/0.49    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.19/0.49    inference(nnf_transformation,[],[f19])).
% 0.19/0.49  fof(f19,plain,(
% 0.19/0.49    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.19/0.49    inference(ennf_transformation,[],[f3])).
% 0.19/0.49  fof(f3,axiom,(
% 0.19/0.49    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 0.19/0.49  fof(f347,plain,(
% 0.19/0.49    ( ! [X0] : (~r1_tarski(k1_relat_1(sK0),X0) | ~v1_finset_1(X0)) )),
% 0.19/0.49    inference(resolution,[],[f341,f47])).
% 0.19/0.49  fof(f47,plain,(
% 0.19/0.49    ( ! [X0,X1] : (v1_finset_1(X0) | ~v1_finset_1(X1) | ~r1_tarski(X0,X1)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f21])).
% 0.19/0.49  fof(f21,plain,(
% 0.19/0.49    ! [X0,X1] : (v1_finset_1(X0) | ~v1_finset_1(X1) | ~r1_tarski(X0,X1))),
% 0.19/0.49    inference(flattening,[],[f20])).
% 0.19/0.49  fof(f20,plain,(
% 0.19/0.49    ! [X0,X1] : (v1_finset_1(X0) | (~v1_finset_1(X1) | ~r1_tarski(X0,X1)))),
% 0.19/0.49    inference(ennf_transformation,[],[f11])).
% 0.19/0.49  fof(f11,axiom,(
% 0.19/0.49    ! [X0,X1] : ((v1_finset_1(X1) & r1_tarski(X0,X1)) => v1_finset_1(X0))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_finset_1)).
% 0.19/0.49  fof(f341,plain,(
% 0.19/0.49    ~v1_finset_1(k1_relat_1(sK0))),
% 0.19/0.49    inference(subsumption_resolution,[],[f334,f149])).
% 0.19/0.49  fof(f149,plain,(
% 0.19/0.49    r1_tarski(k1_relat_1(sK0),sK1)),
% 0.19/0.49    inference(subsumption_resolution,[],[f148,f114])).
% 0.19/0.49  fof(f148,plain,(
% 0.19/0.49    r1_tarski(k1_relat_1(sK0),sK1) | ~v1_relat_1(sK0)),
% 0.19/0.49    inference(resolution,[],[f112,f45])).
% 0.19/0.49  fof(f112,plain,(
% 0.19/0.49    v4_relat_1(sK0,sK1)),
% 0.19/0.49    inference(resolution,[],[f75,f55])).
% 0.19/0.49  fof(f55,plain,(
% 0.19/0.49    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.19/0.49    inference(cnf_transformation,[],[f25])).
% 0.19/0.49  fof(f25,plain,(
% 0.19/0.49    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.49    inference(ennf_transformation,[],[f9])).
% 0.19/0.49  fof(f9,axiom,(
% 0.19/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.19/0.49  fof(f334,plain,(
% 0.19/0.49    ~r1_tarski(k1_relat_1(sK0),sK1) | ~v1_finset_1(k1_relat_1(sK0))),
% 0.19/0.49    inference(resolution,[],[f250,f63])).
% 0.19/0.49  fof(f63,plain,(
% 0.19/0.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.19/0.49    inference(equality_resolution,[],[f48])).
% 0.19/0.49  fof(f48,plain,(
% 0.19/0.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.19/0.49    inference(cnf_transformation,[],[f32])).
% 0.19/0.49  fof(f32,plain,(
% 0.19/0.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.19/0.49    inference(flattening,[],[f31])).
% 0.19/0.49  fof(f31,plain,(
% 0.19/0.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.19/0.49    inference(nnf_transformation,[],[f1])).
% 0.19/0.49  fof(f1,axiom,(
% 0.19/0.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.19/0.49  fof(f250,plain,(
% 0.19/0.49    ( ! [X0] : (~r1_tarski(k1_relat_1(sK0),X0) | ~r1_tarski(X0,sK1) | ~v1_finset_1(X0)) )),
% 0.19/0.49    inference(subsumption_resolution,[],[f249,f114])).
% 0.19/0.49  fof(f249,plain,(
% 0.19/0.49    ( ! [X0] : (~v1_finset_1(X0) | ~r1_tarski(X0,sK1) | ~r1_tarski(k1_relat_1(sK0),X0) | ~v1_relat_1(sK0)) )),
% 0.19/0.49    inference(subsumption_resolution,[],[f247,f166])).
% 0.19/0.49  fof(f166,plain,(
% 0.19/0.49    r1_tarski(k2_relat_1(sK0),sK2)),
% 0.19/0.49    inference(subsumption_resolution,[],[f165,f114])).
% 0.19/0.49  fof(f165,plain,(
% 0.19/0.49    r1_tarski(k2_relat_1(sK0),sK2) | ~v1_relat_1(sK0)),
% 0.19/0.49    inference(resolution,[],[f113,f43])).
% 0.19/0.49  fof(f43,plain,(
% 0.19/0.49    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f29])).
% 0.19/0.49  fof(f29,plain,(
% 0.19/0.49    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.19/0.49    inference(nnf_transformation,[],[f18])).
% 0.19/0.49  fof(f18,plain,(
% 0.19/0.49    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.19/0.49    inference(ennf_transformation,[],[f4])).
% 0.19/0.49  fof(f4,axiom,(
% 0.19/0.49    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.19/0.49  fof(f113,plain,(
% 0.19/0.49    v5_relat_1(sK0,sK2)),
% 0.19/0.49    inference(resolution,[],[f75,f56])).
% 0.19/0.49  fof(f56,plain,(
% 0.19/0.49    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.19/0.49    inference(cnf_transformation,[],[f25])).
% 0.19/0.49  fof(f247,plain,(
% 0.19/0.49    ( ! [X0] : (~v1_finset_1(X0) | ~r1_tarski(X0,sK1) | ~r1_tarski(k2_relat_1(sK0),sK2) | ~r1_tarski(k1_relat_1(sK0),X0) | ~v1_relat_1(sK0)) )),
% 0.19/0.49    inference(resolution,[],[f89,f53])).
% 0.19/0.49  fof(f53,plain,(
% 0.19/0.49    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f23])).
% 0.19/0.49  fof(f23,plain,(
% 0.19/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.19/0.49    inference(flattening,[],[f22])).
% 0.19/0.49  fof(f22,plain,(
% 0.19/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 0.19/0.49    inference(ennf_transformation,[],[f10])).
% 0.19/0.49  fof(f10,axiom,(
% 0.19/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).
% 0.19/0.49  fof(f89,plain,(
% 0.19/0.49    ( ! [X0] : (~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) | ~v1_finset_1(X0) | ~r1_tarski(X0,sK1)) )),
% 0.19/0.49    inference(resolution,[],[f38,f51])).
% 0.19/0.49  fof(f51,plain,(
% 0.19/0.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.19/0.49    inference(cnf_transformation,[],[f33])).
% 0.19/0.49  fof(f38,plain,(
% 0.19/0.49    ( ! [X3] : (~r1_tarski(sK0,k2_zfmisc_1(X3,sK2)) | ~r1_tarski(X3,sK1) | ~v1_finset_1(X3)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f28])).
% 0.19/0.49  fof(f394,plain,(
% 0.19/0.49    v4_relat_1(sK0,sK3(sK0,sK1,sK2))),
% 0.19/0.49    inference(resolution,[],[f222,f55])).
% 0.19/0.49  fof(f222,plain,(
% 0.19/0.49    m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(sK3(sK0,sK1,sK2),sK4(sK0,sK1,sK2))))),
% 0.19/0.49    inference(resolution,[],[f85,f52])).
% 0.19/0.49  fof(f85,plain,(
% 0.19/0.49    r1_tarski(sK0,k2_zfmisc_1(sK3(sK0,sK1,sK2),sK4(sK0,sK1,sK2)))),
% 0.19/0.49    inference(subsumption_resolution,[],[f74,f36])).
% 0.19/0.49  fof(f74,plain,(
% 0.19/0.49    r1_tarski(sK0,k2_zfmisc_1(sK3(sK0,sK1,sK2),sK4(sK0,sK1,sK2))) | ~v1_finset_1(sK0)),
% 0.19/0.49    inference(resolution,[],[f37,f61])).
% 0.19/0.49  fof(f61,plain,(
% 0.19/0.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_zfmisc_1(sK3(X0,X1,X2),sK4(X0,X1,X2))) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2)) | ~v1_finset_1(X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f35])).
% 0.19/0.49  % SZS output end Proof for theBenchmark
% 0.19/0.49  % (1291)------------------------------
% 0.19/0.49  % (1291)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.49  % (1291)Termination reason: Refutation
% 0.19/0.49  
% 0.19/0.49  % (1291)Memory used [KB]: 1791
% 0.19/0.49  % (1291)Time elapsed: 0.075 s
% 0.19/0.49  % (1291)------------------------------
% 0.19/0.49  % (1291)------------------------------
% 0.19/0.49  % (1272)Success in time 0.138 s
%------------------------------------------------------------------------------
