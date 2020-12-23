%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:37 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 859 expanded)
%              Number of leaves         :   12 ( 260 expanded)
%              Depth                    :   25
%              Number of atoms          :  268 (5646 expanded)
%              Number of equality atoms :   98 (1772 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (26783)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
fof(f323,plain,(
    $false ),
    inference(subsumption_resolution,[],[f322,f36])).

fof(f36,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( sK2 != sK3
    & k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
    & r2_hidden(sK3,sK0)
    & r2_hidden(sK2,sK0)
    & v2_funct_1(sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f21,f20])).

fof(f20,plain,
    ( ? [X0,X1] :
        ( ? [X2,X3] :
            ( X2 != X3
            & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        & v2_funct_1(X1)
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ? [X3,X2] :
          ( X2 != X3
          & k1_funct_1(sK1,X2) = k1_funct_1(sK1,X3)
          & r2_hidden(X3,sK0)
          & r2_hidden(X2,sK0) )
      & v2_funct_1(sK1)
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X3,X2] :
        ( X2 != X3
        & k1_funct_1(sK1,X2) = k1_funct_1(sK1,X3)
        & r2_hidden(X3,sK0)
        & r2_hidden(X2,sK0) )
   => ( sK2 != sK3
      & k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
      & r2_hidden(sK3,sK0)
      & r2_hidden(sK2,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ? [X2,X3] :
          ( X2 != X3
          & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
      & v2_funct_1(X1)
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ? [X2,X3] :
          ( X2 != X3
          & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
      & v2_funct_1(X1)
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( v2_funct_1(X1)
         => ! [X2,X3] :
              ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
                & r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => X2 = X3 ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ! [X2,X3] :
            ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_funct_2)).

fof(f322,plain,(
    sK2 = sK3 ),
    inference(forward_demodulation,[],[f321,f319])).

fof(f319,plain,(
    sK2 = k1_funct_1(k2_funct_1(k1_xboole_0),k1_funct_1(k1_xboole_0,sK2)) ),
    inference(resolution,[],[f301,f268])).

fof(f268,plain,(
    r2_hidden(sK2,k1_xboole_0) ),
    inference(superposition,[],[f33,f264])).

fof(f264,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f263,f36])).

fof(f263,plain,
    ( sK2 = sK3
    | k1_xboole_0 = sK0 ),
    inference(duplicate_literal_removal,[],[f260])).

fof(f260,plain,
    ( sK2 = sK3
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f259,f257])).

fof(f257,plain,
    ( sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f256,f33])).

fof(f256,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0
      | k1_xboole_0 = sK0 ) ),
    inference(subsumption_resolution,[],[f255,f31])).

fof(f31,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f22])).

fof(f255,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | k1_xboole_0 = sK0 ) ),
    inference(resolution,[],[f254,f30])).

fof(f30,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f254,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(sK1,X2,X0)
      | ~ r2_hidden(X1,X2)
      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X1)) = X1
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | k1_xboole_0 = X0 ) ),
    inference(subsumption_resolution,[],[f253,f29])).

fof(f29,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f253,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r2_hidden(X1,X2)
      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X1)) = X1
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ v1_funct_2(sK1,X2,X0)
      | ~ v1_funct_1(sK1) ) ),
    inference(resolution,[],[f53,f32])).

fof(f32,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_funct_1(X3)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( ( r2_hidden(X2,X0)
          & v2_funct_1(X3) )
       => ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_funct_2)).

fof(f259,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | k1_xboole_0 = sK0 ),
    inference(forward_demodulation,[],[f258,f35])).

fof(f35,plain,(
    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f258,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3))
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f256,f34])).

fof(f34,plain,(
    r2_hidden(sK3,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f33,plain,(
    r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f301,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | k1_funct_1(k2_funct_1(k1_xboole_0),k1_funct_1(k1_xboole_0,X0)) = X0 ) ),
    inference(forward_demodulation,[],[f300,f102])).

fof(f102,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f101,f79])).

fof(f79,plain,(
    ! [X0] : v4_relat_1(k1_xboole_0,X0) ),
    inference(resolution,[],[f74,f37])).

fof(f37,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | v4_relat_1(X0,X1) ) ),
    inference(resolution,[],[f51,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f101,plain,
    ( ~ v4_relat_1(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f72,f58])).

fof(f58,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f38,f56])).

fof(f56,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f38,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f72,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | k1_xboole_0 = k1_relat_1(X0) ) ),
    inference(resolution,[],[f66,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f66,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f45,f37])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
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

fof(f300,plain,(
    ! [X0] :
      ( k1_funct_1(k2_funct_1(k1_xboole_0),k1_funct_1(k1_xboole_0,X0)) = X0
      | ~ r2_hidden(X0,k1_relat_1(k1_xboole_0)) ) ),
    inference(subsumption_resolution,[],[f291,f58])).

fof(f291,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k1_xboole_0)
      | k1_funct_1(k2_funct_1(k1_xboole_0),k1_funct_1(k1_xboole_0,X0)) = X0
      | ~ r2_hidden(X0,k1_relat_1(k1_xboole_0)) ) ),
    inference(superposition,[],[f230,f278])).

fof(f278,plain,(
    k1_xboole_0 = sK1 ),
    inference(forward_demodulation,[],[f277,f56])).

fof(f277,plain,(
    sK1 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f276,f37])).

fof(f276,plain,
    ( ~ r1_tarski(k1_xboole_0,sK1)
    | sK1 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f271,f56])).

fof(f271,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),sK1)
    | sK1 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f68,f264])).

fof(f68,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK0),sK1)
    | sK1 = k2_zfmisc_1(sK0,sK0) ),
    inference(resolution,[],[f45,f60])).

fof(f60,plain,(
    r1_tarski(sK1,k2_zfmisc_1(sK0,sK0)) ),
    inference(resolution,[],[f46,f31])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f230,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK1)
      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0
      | ~ r2_hidden(X0,k1_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f229,f29])).

fof(f229,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f41,f32])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
        & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 )
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
        & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 )
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k1_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
          & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_funct_1)).

fof(f321,plain,(
    sK3 = k1_funct_1(k2_funct_1(k1_xboole_0),k1_funct_1(k1_xboole_0,sK2)) ),
    inference(forward_demodulation,[],[f320,f286])).

fof(f286,plain,(
    k1_funct_1(k1_xboole_0,sK2) = k1_funct_1(k1_xboole_0,sK3) ),
    inference(superposition,[],[f35,f278])).

fof(f320,plain,(
    sK3 = k1_funct_1(k2_funct_1(k1_xboole_0),k1_funct_1(k1_xboole_0,sK3)) ),
    inference(resolution,[],[f301,f269])).

fof(f269,plain,(
    r2_hidden(sK3,k1_xboole_0) ),
    inference(superposition,[],[f34,f264])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_vampire %s %d
% 0.13/0.32  % Computer   : n005.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % WCLimit    : 600
% 0.13/0.32  % DateTime   : Tue Dec  1 15:09:32 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.19/0.44  % (26788)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.19/0.46  % (26788)Refutation not found, incomplete strategy% (26788)------------------------------
% 0.19/0.46  % (26788)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.47  % (26794)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.19/0.47  % (26800)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.19/0.47  % (26804)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.19/0.47  % (26788)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.47  
% 0.19/0.47  % (26788)Memory used [KB]: 6140
% 0.19/0.47  % (26788)Time elapsed: 0.091 s
% 0.19/0.47  % (26788)------------------------------
% 0.19/0.47  % (26788)------------------------------
% 0.19/0.48  % (26795)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.19/0.48  % (26796)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.19/0.48  % (26786)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.19/0.49  % (26807)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.19/0.49  % (26793)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.19/0.49  % (26784)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.49  % (26796)Refutation not found, incomplete strategy% (26796)------------------------------
% 0.19/0.49  % (26796)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.49  % (26796)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.49  
% 0.19/0.49  % (26796)Memory used [KB]: 6268
% 0.19/0.49  % (26796)Time elapsed: 0.111 s
% 0.19/0.49  % (26796)------------------------------
% 0.19/0.49  % (26796)------------------------------
% 0.19/0.49  % (26804)Refutation found. Thanks to Tanya!
% 0.19/0.49  % SZS status Theorem for theBenchmark
% 0.19/0.49  % SZS output start Proof for theBenchmark
% 0.19/0.49  % (26783)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.19/0.49  fof(f323,plain,(
% 0.19/0.49    $false),
% 0.19/0.49    inference(subsumption_resolution,[],[f322,f36])).
% 0.19/0.49  fof(f36,plain,(
% 0.19/0.49    sK2 != sK3),
% 0.19/0.49    inference(cnf_transformation,[],[f22])).
% 0.19/0.49  fof(f22,plain,(
% 0.19/0.49    (sK2 != sK3 & k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) & r2_hidden(sK3,sK0) & r2_hidden(sK2,sK0)) & v2_funct_1(sK1) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 0.19/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f21,f20])).
% 0.19/0.49  fof(f20,plain,(
% 0.19/0.49    ? [X0,X1] : (? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) & v2_funct_1(X1) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X3,X2] : (X2 != X3 & k1_funct_1(sK1,X2) = k1_funct_1(sK1,X3) & r2_hidden(X3,sK0) & r2_hidden(X2,sK0)) & v2_funct_1(sK1) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 0.19/0.49    introduced(choice_axiom,[])).
% 0.19/0.49  fof(f21,plain,(
% 0.19/0.49    ? [X3,X2] : (X2 != X3 & k1_funct_1(sK1,X2) = k1_funct_1(sK1,X3) & r2_hidden(X3,sK0) & r2_hidden(X2,sK0)) => (sK2 != sK3 & k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) & r2_hidden(sK3,sK0) & r2_hidden(sK2,sK0))),
% 0.19/0.49    introduced(choice_axiom,[])).
% 0.19/0.49  fof(f13,plain,(
% 0.19/0.49    ? [X0,X1] : (? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) & v2_funct_1(X1) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.19/0.49    inference(flattening,[],[f12])).
% 0.19/0.49  fof(f12,plain,(
% 0.19/0.49    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & (k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0))) & v2_funct_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 0.19/0.49    inference(ennf_transformation,[],[f11])).
% 0.19/0.49  fof(f11,negated_conjecture,(
% 0.19/0.49    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) => ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 0.19/0.49    inference(negated_conjecture,[],[f10])).
% 0.19/0.49  fof(f10,conjecture,(
% 0.19/0.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) => ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_funct_2)).
% 0.19/0.49  fof(f322,plain,(
% 0.19/0.49    sK2 = sK3),
% 0.19/0.49    inference(forward_demodulation,[],[f321,f319])).
% 0.19/0.49  fof(f319,plain,(
% 0.19/0.49    sK2 = k1_funct_1(k2_funct_1(k1_xboole_0),k1_funct_1(k1_xboole_0,sK2))),
% 0.19/0.49    inference(resolution,[],[f301,f268])).
% 0.19/0.49  fof(f268,plain,(
% 0.19/0.49    r2_hidden(sK2,k1_xboole_0)),
% 0.19/0.49    inference(superposition,[],[f33,f264])).
% 0.19/0.49  fof(f264,plain,(
% 0.19/0.49    k1_xboole_0 = sK0),
% 0.19/0.49    inference(subsumption_resolution,[],[f263,f36])).
% 0.19/0.49  fof(f263,plain,(
% 0.19/0.49    sK2 = sK3 | k1_xboole_0 = sK0),
% 0.19/0.49    inference(duplicate_literal_removal,[],[f260])).
% 0.19/0.49  fof(f260,plain,(
% 0.19/0.49    sK2 = sK3 | k1_xboole_0 = sK0 | k1_xboole_0 = sK0),
% 0.19/0.49    inference(superposition,[],[f259,f257])).
% 0.19/0.49  fof(f257,plain,(
% 0.19/0.49    sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | k1_xboole_0 = sK0),
% 0.19/0.49    inference(resolution,[],[f256,f33])).
% 0.19/0.49  fof(f256,plain,(
% 0.19/0.49    ( ! [X0] : (~r2_hidden(X0,sK0) | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 | k1_xboole_0 = sK0) )),
% 0.19/0.49    inference(subsumption_resolution,[],[f255,f31])).
% 0.19/0.49  fof(f31,plain,(
% 0.19/0.49    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.19/0.49    inference(cnf_transformation,[],[f22])).
% 0.19/0.49  fof(f255,plain,(
% 0.19/0.49    ( ! [X0] : (~r2_hidden(X0,sK0) | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k1_xboole_0 = sK0) )),
% 0.19/0.49    inference(resolution,[],[f254,f30])).
% 0.19/0.49  fof(f30,plain,(
% 0.19/0.49    v1_funct_2(sK1,sK0,sK0)),
% 0.19/0.49    inference(cnf_transformation,[],[f22])).
% 0.19/0.49  fof(f254,plain,(
% 0.19/0.49    ( ! [X2,X0,X1] : (~v1_funct_2(sK1,X2,X0) | ~r2_hidden(X1,X2) | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X1)) = X1 | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | k1_xboole_0 = X0) )),
% 0.19/0.49    inference(subsumption_resolution,[],[f253,f29])).
% 0.19/0.49  fof(f29,plain,(
% 0.19/0.49    v1_funct_1(sK1)),
% 0.19/0.49    inference(cnf_transformation,[],[f22])).
% 0.19/0.49  fof(f253,plain,(
% 0.19/0.49    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | ~r2_hidden(X1,X2) | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X1)) = X1 | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_2(sK1,X2,X0) | ~v1_funct_1(sK1)) )),
% 0.19/0.49    inference(resolution,[],[f53,f32])).
% 0.19/0.49  fof(f32,plain,(
% 0.19/0.49    v2_funct_1(sK1)),
% 0.19/0.49    inference(cnf_transformation,[],[f22])).
% 0.19/0.49  fof(f53,plain,(
% 0.19/0.49    ( ! [X2,X0,X3,X1] : (~v2_funct_1(X3) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f19])).
% 0.19/0.49  fof(f19,plain,(
% 0.19/0.49    ! [X0,X1,X2,X3] : (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v2_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.19/0.49    inference(flattening,[],[f18])).
% 0.19/0.49  fof(f18,plain,(
% 0.19/0.49    ! [X0,X1,X2,X3] : (((k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1) | (~r2_hidden(X2,X0) | ~v2_funct_1(X3))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.19/0.49    inference(ennf_transformation,[],[f9])).
% 0.19/0.49  fof(f9,axiom,(
% 0.19/0.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((r2_hidden(X2,X0) & v2_funct_1(X3)) => (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1)))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_funct_2)).
% 0.19/0.49  fof(f259,plain,(
% 0.19/0.49    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | k1_xboole_0 = sK0),
% 0.19/0.49    inference(forward_demodulation,[],[f258,f35])).
% 0.19/0.49  fof(f35,plain,(
% 0.19/0.49    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)),
% 0.19/0.49    inference(cnf_transformation,[],[f22])).
% 0.19/0.49  fof(f258,plain,(
% 0.19/0.49    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3)) | k1_xboole_0 = sK0),
% 0.19/0.49    inference(resolution,[],[f256,f34])).
% 0.19/0.49  fof(f34,plain,(
% 0.19/0.49    r2_hidden(sK3,sK0)),
% 0.19/0.49    inference(cnf_transformation,[],[f22])).
% 0.19/0.49  fof(f33,plain,(
% 0.19/0.49    r2_hidden(sK2,sK0)),
% 0.19/0.49    inference(cnf_transformation,[],[f22])).
% 0.19/0.49  fof(f301,plain,(
% 0.19/0.49    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0) | k1_funct_1(k2_funct_1(k1_xboole_0),k1_funct_1(k1_xboole_0,X0)) = X0) )),
% 0.19/0.49    inference(forward_demodulation,[],[f300,f102])).
% 0.19/0.49  fof(f102,plain,(
% 0.19/0.49    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.19/0.49    inference(subsumption_resolution,[],[f101,f79])).
% 0.19/0.49  fof(f79,plain,(
% 0.19/0.49    ( ! [X0] : (v4_relat_1(k1_xboole_0,X0)) )),
% 0.19/0.49    inference(resolution,[],[f74,f37])).
% 0.19/0.49  fof(f37,plain,(
% 0.19/0.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f2])).
% 0.19/0.49  fof(f2,axiom,(
% 0.19/0.49    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.19/0.49  fof(f74,plain,(
% 0.19/0.49    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_zfmisc_1(X1,X2)) | v4_relat_1(X0,X1)) )),
% 0.19/0.49    inference(resolution,[],[f51,f47])).
% 0.19/0.49  fof(f47,plain,(
% 0.19/0.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f26])).
% 0.19/0.49  fof(f26,plain,(
% 0.19/0.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.19/0.49    inference(nnf_transformation,[],[f4])).
% 0.19/0.49  fof(f4,axiom,(
% 0.19/0.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.19/0.49  fof(f51,plain,(
% 0.19/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f17])).
% 0.19/0.49  fof(f17,plain,(
% 0.19/0.49    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.49    inference(ennf_transformation,[],[f8])).
% 0.19/0.49  fof(f8,axiom,(
% 0.19/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.19/0.49  fof(f101,plain,(
% 0.19/0.49    ~v4_relat_1(k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.19/0.49    inference(resolution,[],[f72,f58])).
% 0.19/0.49  fof(f58,plain,(
% 0.19/0.49    v1_relat_1(k1_xboole_0)),
% 0.19/0.49    inference(superposition,[],[f38,f56])).
% 0.19/0.49  fof(f56,plain,(
% 0.19/0.49    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.19/0.49    inference(equality_resolution,[],[f50])).
% 0.19/0.49  fof(f50,plain,(
% 0.19/0.49    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.19/0.49    inference(cnf_transformation,[],[f28])).
% 0.19/0.49  fof(f28,plain,(
% 0.19/0.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.19/0.49    inference(flattening,[],[f27])).
% 0.19/0.49  fof(f27,plain,(
% 0.19/0.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.19/0.49    inference(nnf_transformation,[],[f3])).
% 0.19/0.49  fof(f3,axiom,(
% 0.19/0.49    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.19/0.49  fof(f38,plain,(
% 0.19/0.49    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.19/0.49    inference(cnf_transformation,[],[f6])).
% 0.19/0.49  fof(f6,axiom,(
% 0.19/0.49    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.19/0.49  fof(f72,plain,(
% 0.19/0.49    ( ! [X0] : (~v1_relat_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | k1_xboole_0 = k1_relat_1(X0)) )),
% 0.19/0.49    inference(resolution,[],[f66,f39])).
% 0.19/0.49  fof(f39,plain,(
% 0.19/0.49    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f23])).
% 0.19/0.49  fof(f23,plain,(
% 0.19/0.49    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.19/0.49    inference(nnf_transformation,[],[f14])).
% 0.19/0.49  fof(f14,plain,(
% 0.19/0.49    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.19/0.49    inference(ennf_transformation,[],[f5])).
% 0.19/0.49  fof(f5,axiom,(
% 0.19/0.49    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 0.19/0.49  fof(f66,plain,(
% 0.19/0.49    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.19/0.49    inference(resolution,[],[f45,f37])).
% 0.19/0.49  fof(f45,plain,(
% 0.19/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.19/0.49    inference(cnf_transformation,[],[f25])).
% 0.19/0.49  fof(f25,plain,(
% 0.19/0.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.19/0.49    inference(flattening,[],[f24])).
% 0.19/0.49  fof(f24,plain,(
% 0.19/0.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.19/0.49    inference(nnf_transformation,[],[f1])).
% 0.19/0.49  fof(f1,axiom,(
% 0.19/0.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.19/0.49  fof(f300,plain,(
% 0.19/0.49    ( ! [X0] : (k1_funct_1(k2_funct_1(k1_xboole_0),k1_funct_1(k1_xboole_0,X0)) = X0 | ~r2_hidden(X0,k1_relat_1(k1_xboole_0))) )),
% 0.19/0.49    inference(subsumption_resolution,[],[f291,f58])).
% 0.19/0.49  fof(f291,plain,(
% 0.19/0.49    ( ! [X0] : (~v1_relat_1(k1_xboole_0) | k1_funct_1(k2_funct_1(k1_xboole_0),k1_funct_1(k1_xboole_0,X0)) = X0 | ~r2_hidden(X0,k1_relat_1(k1_xboole_0))) )),
% 0.19/0.49    inference(superposition,[],[f230,f278])).
% 0.19/0.49  fof(f278,plain,(
% 0.19/0.49    k1_xboole_0 = sK1),
% 0.19/0.49    inference(forward_demodulation,[],[f277,f56])).
% 0.19/0.49  fof(f277,plain,(
% 0.19/0.49    sK1 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)),
% 0.19/0.49    inference(subsumption_resolution,[],[f276,f37])).
% 0.19/0.49  fof(f276,plain,(
% 0.19/0.49    ~r1_tarski(k1_xboole_0,sK1) | sK1 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)),
% 0.19/0.49    inference(forward_demodulation,[],[f271,f56])).
% 0.19/0.49  fof(f271,plain,(
% 0.19/0.49    ~r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),sK1) | sK1 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)),
% 0.19/0.49    inference(superposition,[],[f68,f264])).
% 0.19/0.49  fof(f68,plain,(
% 0.19/0.49    ~r1_tarski(k2_zfmisc_1(sK0,sK0),sK1) | sK1 = k2_zfmisc_1(sK0,sK0)),
% 0.19/0.49    inference(resolution,[],[f45,f60])).
% 0.19/0.49  fof(f60,plain,(
% 0.19/0.49    r1_tarski(sK1,k2_zfmisc_1(sK0,sK0))),
% 0.19/0.49    inference(resolution,[],[f46,f31])).
% 0.19/0.49  fof(f46,plain,(
% 0.19/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f26])).
% 0.19/0.49  fof(f230,plain,(
% 0.19/0.49    ( ! [X0] : (~v1_relat_1(sK1) | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 | ~r2_hidden(X0,k1_relat_1(sK1))) )),
% 0.19/0.49    inference(subsumption_resolution,[],[f229,f29])).
% 0.19/0.49  fof(f229,plain,(
% 0.19/0.49    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 0.19/0.49    inference(resolution,[],[f41,f32])).
% 0.19/0.49  fof(f41,plain,(
% 0.19/0.49    ( ! [X0,X1] : (~v2_funct_1(X1) | ~r2_hidden(X0,k1_relat_1(X1)) | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f16])).
% 0.19/0.49  fof(f16,plain,(
% 0.19/0.49    ! [X0,X1] : ((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.19/0.49    inference(flattening,[],[f15])).
% 0.19/0.49  fof(f15,plain,(
% 0.19/0.49    ! [X0,X1] : (((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0) | (~r2_hidden(X0,k1_relat_1(X1)) | ~v2_funct_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.19/0.49    inference(ennf_transformation,[],[f7])).
% 0.19/0.49  fof(f7,axiom,(
% 0.19/0.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k1_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0)))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_funct_1)).
% 0.19/0.49  fof(f321,plain,(
% 0.19/0.49    sK3 = k1_funct_1(k2_funct_1(k1_xboole_0),k1_funct_1(k1_xboole_0,sK2))),
% 0.19/0.49    inference(forward_demodulation,[],[f320,f286])).
% 0.19/0.49  fof(f286,plain,(
% 0.19/0.49    k1_funct_1(k1_xboole_0,sK2) = k1_funct_1(k1_xboole_0,sK3)),
% 0.19/0.49    inference(superposition,[],[f35,f278])).
% 0.19/0.49  fof(f320,plain,(
% 0.19/0.49    sK3 = k1_funct_1(k2_funct_1(k1_xboole_0),k1_funct_1(k1_xboole_0,sK3))),
% 0.19/0.49    inference(resolution,[],[f301,f269])).
% 0.19/0.49  fof(f269,plain,(
% 0.19/0.49    r2_hidden(sK3,k1_xboole_0)),
% 0.19/0.49    inference(superposition,[],[f34,f264])).
% 0.19/0.49  % SZS output end Proof for theBenchmark
% 0.19/0.49  % (26804)------------------------------
% 0.19/0.49  % (26804)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.49  % (26804)Termination reason: Refutation
% 0.19/0.49  
% 0.19/0.49  % (26804)Memory used [KB]: 6268
% 0.19/0.49  % (26804)Time elapsed: 0.121 s
% 0.19/0.49  % (26804)------------------------------
% 0.19/0.49  % (26804)------------------------------
% 0.19/0.49  % (26798)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.19/0.50  % (26783)Refutation not found, incomplete strategy% (26783)------------------------------
% 0.19/0.50  % (26783)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (26783)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.50  
% 0.19/0.50  % (26783)Memory used [KB]: 10618
% 0.19/0.50  % (26783)Time elapsed: 0.104 s
% 0.19/0.50  % (26783)------------------------------
% 0.19/0.50  % (26783)------------------------------
% 0.19/0.50  % (26782)Success in time 0.158 s
%------------------------------------------------------------------------------
