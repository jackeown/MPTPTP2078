%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0368+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:50 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   40 (  57 expanded)
%              Number of leaves         :    6 (  13 expanded)
%              Depth                    :   12
%              Number of atoms          :   99 ( 161 expanded)
%              Number of equality atoms :   13 (  23 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f74,plain,(
    $false ),
    inference(subsumption_resolution,[],[f73,f16])).

fof(f16,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ m1_subset_1(X2,X0) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ m1_subset_1(X2,X0) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( ! [X2] :
              ( m1_subset_1(X2,X0)
             => r2_hidden(X2,X1) )
         => X0 = X1 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( ! [X2] :
            ( m1_subset_1(X2,X0)
           => r2_hidden(X2,X1) )
       => X0 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_subset_1)).

fof(f73,plain,(
    sK0 = sK1 ),
    inference(subsumption_resolution,[],[f70,f51])).

fof(f51,plain,(
    r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f49,f33])).

fof(f33,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f49,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK0)
      | r1_tarski(sK1,sK0) ) ),
    inference(resolution,[],[f48,f36])).

fof(f36,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,k1_zfmisc_1(X0))
      | ~ r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f48,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(sK0))
      | r1_tarski(sK1,sK0) ) ),
    inference(resolution,[],[f45,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

fof(f45,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f41,f35])).

fof(f35,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f41,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f21,f15])).

fof(f15,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f70,plain,
    ( ~ r1_tarski(sK1,sK0)
    | sK0 = sK1 ),
    inference(resolution,[],[f24,f67])).

fof(f67,plain,(
    r1_tarski(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f66])).

fof(f66,plain,
    ( r1_tarski(sK0,sK1)
    | r1_tarski(sK0,sK1) ),
    inference(resolution,[],[f64,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f64,plain,(
    ! [X3] :
      ( ~ r2_hidden(sK3(X3,sK1),sK0)
      | r1_tarski(X3,sK1) ) ),
    inference(resolution,[],[f27,f40])).

fof(f40,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f39,f32])).

fof(f39,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | v1_xboole_0(sK0)
      | r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f20,f14])).

fof(f14,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,sK0)
      | r2_hidden(X2,sK1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

%------------------------------------------------------------------------------
