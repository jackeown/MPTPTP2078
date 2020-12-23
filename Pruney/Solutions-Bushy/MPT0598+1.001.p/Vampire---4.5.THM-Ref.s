%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0598+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:16 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   40 (  94 expanded)
%              Number of leaves         :    8 (  28 expanded)
%              Depth                    :   11
%              Number of atoms          :  110 ( 330 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f46,plain,(
    $false ),
    inference(subsumption_resolution,[],[f45,f24])).

fof(f24,plain,(
    ~ r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ~ r2_hidden(sK2,sK0)
    & r2_hidden(sK2,k2_relat_1(sK1))
    & v5_relat_1(sK1,sK0)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f17,f16])).

fof(f16,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r2_hidden(X2,X0)
            & r2_hidden(X2,k2_relat_1(X1)) )
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ~ r2_hidden(X2,sK0)
          & r2_hidden(X2,k2_relat_1(sK1)) )
      & v5_relat_1(sK1,sK0)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X2] :
        ( ~ r2_hidden(X2,sK0)
        & r2_hidden(X2,k2_relat_1(sK1)) )
   => ( ~ r2_hidden(sK2,sK0)
      & r2_hidden(sK2,k2_relat_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,k2_relat_1(X1)) )
      & v5_relat_1(X1,X0)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,k2_relat_1(X1)) )
      & v5_relat_1(X1,X0)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v5_relat_1(X1,X0)
          & v1_relat_1(X1) )
       => ! [X2] :
            ( r2_hidden(X2,k2_relat_1(X1))
           => r2_hidden(X2,X0) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k2_relat_1(X1))
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t202_relat_1)).

fof(f45,plain,(
    r2_hidden(sK2,sK0) ),
    inference(subsumption_resolution,[],[f44,f42])).

fof(f42,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(resolution,[],[f39,f35])).

fof(f35,plain,(
    r1_tarski(k2_relat_1(sK1),sK0) ),
    inference(subsumption_resolution,[],[f34,f21])).

fof(f21,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f34,plain,
    ( r1_tarski(k2_relat_1(sK1),sK0)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f25,f22])).

fof(f22,plain,(
    v5_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f39,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK1),X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f36,f23])).

fof(f23,plain,(
    r2_hidden(sK2,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,X2)
      | ~ v1_xboole_0(X0)
      | ~ r1_tarski(X2,X0) ) ),
    inference(resolution,[],[f31,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f44,plain,
    ( v1_xboole_0(sK0)
    | r2_hidden(sK2,sK0) ),
    inference(resolution,[],[f43,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f43,plain,(
    m1_subset_1(sK2,sK0) ),
    inference(resolution,[],[f40,f35])).

fof(f40,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK1),X0)
      | m1_subset_1(sK2,X0) ) ),
    inference(resolution,[],[f37,f23])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | m1_subset_1(X0,X1)
      | ~ r1_tarski(X2,X1) ) ),
    inference(resolution,[],[f30,f29])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

%------------------------------------------------------------------------------
