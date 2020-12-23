%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1839+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:42 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   97 (1174 expanded)
%              Number of leaves         :   16 ( 339 expanded)
%              Depth                    :   29
%              Number of atoms          :  225 (3549 expanded)
%              Number of equality atoms :   40 ( 295 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f270,plain,(
    $false ),
    inference(subsumption_resolution,[],[f269,f55])).

fof(f55,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X0) ),
    inference(superposition,[],[f45,f46])).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f45,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f269,plain,(
    ~ r1_tarski(k3_xboole_0(sK0,sK1),sK1) ),
    inference(resolution,[],[f267,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f267,plain,(
    ~ m1_subset_1(k3_xboole_0(sK0,sK1),k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f263,f186])).

fof(f186,plain,(
    r2_hidden(sK2(sK0),k3_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f160,f179])).

fof(f179,plain,(
    sK2(sK0) = sK3(k3_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f176,f105])).

fof(f105,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_tarski(X0),sK0)
      | sK2(sK0) = X0 ) ),
    inference(superposition,[],[f47,f104])).

fof(f104,plain,(
    sK0 = k1_tarski(sK2(sK0)) ),
    inference(forward_demodulation,[],[f103,f63])).

fof(f63,plain,(
    sK0 = k6_domain_1(sK0,sK2(sK0)) ),
    inference(subsumption_resolution,[],[f62,f37])).

fof(f37,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ~ r1_tarski(sK0,sK1)
    & ~ v1_xboole_0(k3_xboole_0(sK0,sK1))
    & v1_zfmisc_1(sK0)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f28,f27])).

fof(f27,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(X0,X1)
            & ~ v1_xboole_0(k3_xboole_0(X0,X1)) )
        & v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(sK0,X1)
          & ~ v1_xboole_0(k3_xboole_0(sK0,X1)) )
      & v1_zfmisc_1(sK0)
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X1] :
        ( ~ r1_tarski(sK0,X1)
        & ~ v1_xboole_0(k3_xboole_0(sK0,X1)) )
   => ( ~ r1_tarski(sK0,sK1)
      & ~ v1_xboole_0(k3_xboole_0(sK0,sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X0,X1)
          & ~ v1_xboole_0(k3_xboole_0(X0,X1)) )
      & v1_zfmisc_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X0,X1)
          & ~ v1_xboole_0(k3_xboole_0(X0,X1)) )
      & v1_zfmisc_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_zfmisc_1(X0)
          & ~ v1_xboole_0(X0) )
       => ! [X1] :
            ( ~ v1_xboole_0(k3_xboole_0(X0,X1))
           => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( ~ v1_xboole_0(k3_xboole_0(X0,X1))
         => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tex_2)).

fof(f62,plain,
    ( sK0 = k6_domain_1(sK0,sK2(sK0))
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f42,f38])).

fof(f38,plain,(
    v1_zfmisc_1(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f42,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(X0)
      | k6_domain_1(X0,sK2(X0)) = X0
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ( k6_domain_1(X0,sK2(X0)) = X0
            & m1_subset_1(sK2(X0),X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f31,f32])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k6_domain_1(X0,X2) = X0
          & m1_subset_1(X2,X0) )
     => ( k6_domain_1(X0,sK2(X0)) = X0
        & m1_subset_1(sK2(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ? [X2] :
              ( k6_domain_1(X0,X2) = X0
              & m1_subset_1(X2,X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ? [X1] :
              ( k6_domain_1(X0,X1) = X0
              & m1_subset_1(X1,X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).

fof(f103,plain,(
    k6_domain_1(sK0,sK2(sK0)) = k1_tarski(sK2(sK0)) ),
    inference(subsumption_resolution,[],[f102,f37])).

fof(f102,plain,
    ( v1_xboole_0(sK0)
    | k6_domain_1(sK0,sK2(sK0)) = k1_tarski(sK2(sK0)) ),
    inference(resolution,[],[f67,f38])).

fof(f67,plain,(
    ! [X3] :
      ( ~ v1_zfmisc_1(X3)
      | v1_xboole_0(X3)
      | k6_domain_1(X3,sK2(X3)) = k1_tarski(sK2(X3)) ) ),
    inference(duplicate_literal_removal,[],[f66])).

fof(f66,plain,(
    ! [X3] :
      ( k6_domain_1(X3,sK2(X3)) = k1_tarski(sK2(X3))
      | v1_xboole_0(X3)
      | ~ v1_zfmisc_1(X3)
      | v1_xboole_0(X3) ) ),
    inference(resolution,[],[f48,f41])).

fof(f41,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(X0),X0)
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_zfmisc_1)).

fof(f176,plain,(
    r1_tarski(k1_tarski(sK3(k3_xboole_0(sK0,sK1))),sK0) ),
    inference(resolution,[],[f173,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f173,plain,(
    m1_subset_1(k1_tarski(sK3(k3_xboole_0(sK0,sK1))),k1_zfmisc_1(sK0)) ),
    inference(backward_demodulation,[],[f171,f172])).

fof(f172,plain,(
    k1_tarski(sK3(k3_xboole_0(sK0,sK1))) = k6_domain_1(sK0,sK3(k3_xboole_0(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f170,f37])).

fof(f170,plain,
    ( k1_tarski(sK3(k3_xboole_0(sK0,sK1))) = k6_domain_1(sK0,sK3(k3_xboole_0(sK0,sK1)))
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f167,f48])).

fof(f167,plain,(
    m1_subset_1(sK3(k3_xboole_0(sK0,sK1)),sK0) ),
    inference(resolution,[],[f166,f45])).

fof(f166,plain,(
    ! [X0] :
      ( ~ r1_tarski(k3_xboole_0(sK0,sK1),X0)
      | m1_subset_1(sK3(k3_xboole_0(sK0,sK1)),X0) ) ),
    inference(resolution,[],[f162,f52])).

fof(f162,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k3_xboole_0(sK0,sK1),k1_zfmisc_1(X0))
      | m1_subset_1(sK3(k3_xboole_0(sK0,sK1)),X0) ) ),
    inference(resolution,[],[f160,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f171,plain,(
    m1_subset_1(k6_domain_1(sK0,sK3(k3_xboole_0(sK0,sK1))),k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f169,f37])).

fof(f169,plain,
    ( m1_subset_1(k6_domain_1(sK0,sK3(k3_xboole_0(sK0,sK1))),k1_zfmisc_1(sK0))
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f167,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f160,plain,(
    r2_hidden(sK3(k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f156,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
     => r2_hidden(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_zfmisc_1)).

fof(f156,plain,(
    r1_tarski(k1_tarski(sK3(k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f153,f39])).

fof(f39,plain,(
    ~ v1_xboole_0(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f29])).

fof(f153,plain,
    ( r1_tarski(k1_tarski(sK3(k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,sK1))
    | v1_xboole_0(k3_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f78,f69])).

fof(f69,plain,(
    k6_domain_1(k3_xboole_0(sK0,sK1),sK3(k3_xboole_0(sK0,sK1))) = k1_tarski(sK3(k3_xboole_0(sK0,sK1))) ),
    inference(resolution,[],[f64,f39])).

fof(f64,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | k6_domain_1(X0,sK3(X0)) = k1_tarski(sK3(X0)) ) ),
    inference(resolution,[],[f48,f44])).

fof(f44,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f4,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f4,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f78,plain,(
    ! [X0] :
      ( r1_tarski(k6_domain_1(X0,sK3(X0)),X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f71,f51])).

fof(f71,plain,(
    ! [X0] :
      ( m1_subset_1(k6_domain_1(X0,sK3(X0)),k1_zfmisc_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f49,f44])).

fof(f263,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK1)) ) ),
    inference(resolution,[],[f262,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f262,plain,(
    v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f259,f40])).

fof(f40,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f259,plain,
    ( r1_tarski(sK0,sK1)
    | v1_xboole_0(sK1) ),
    inference(backward_demodulation,[],[f247,f257])).

fof(f257,plain,(
    sK0 = k6_domain_1(sK1,sK2(sK0)) ),
    inference(subsumption_resolution,[],[f256,f55])).

fof(f256,plain,
    ( sK0 = k6_domain_1(sK1,sK2(sK0))
    | ~ r1_tarski(k3_xboole_0(sK0,sK1),sK1) ),
    inference(resolution,[],[f254,f52])).

fof(f254,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK0,sK1),k1_zfmisc_1(sK1))
    | sK0 = k6_domain_1(sK1,sK2(sK0)) ),
    inference(resolution,[],[f244,f186])).

fof(f244,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
      | sK0 = k6_domain_1(sK1,sK2(sK0)) ) ),
    inference(resolution,[],[f209,f54])).

fof(f209,plain,
    ( v1_xboole_0(sK1)
    | sK0 = k6_domain_1(sK1,sK2(sK0)) ),
    inference(forward_demodulation,[],[f196,f104])).

fof(f196,plain,
    ( k1_tarski(sK2(sK0)) = k6_domain_1(sK1,sK2(sK0))
    | v1_xboole_0(sK1) ),
    inference(backward_demodulation,[],[f175,f179])).

fof(f175,plain,
    ( k1_tarski(sK3(k3_xboole_0(sK0,sK1))) = k6_domain_1(sK1,sK3(k3_xboole_0(sK0,sK1)))
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f168,f48])).

fof(f168,plain,(
    m1_subset_1(sK3(k3_xboole_0(sK0,sK1)),sK1) ),
    inference(resolution,[],[f166,f55])).

fof(f247,plain,
    ( r1_tarski(k6_domain_1(sK1,sK2(sK0)),sK1)
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f195,f51])).

fof(f195,plain,
    ( m1_subset_1(k6_domain_1(sK1,sK2(sK0)),k1_zfmisc_1(sK1))
    | v1_xboole_0(sK1) ),
    inference(backward_demodulation,[],[f174,f179])).

fof(f174,plain,
    ( m1_subset_1(k6_domain_1(sK1,sK3(k3_xboole_0(sK0,sK1))),k1_zfmisc_1(sK1))
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f168,f49])).

%------------------------------------------------------------------------------
