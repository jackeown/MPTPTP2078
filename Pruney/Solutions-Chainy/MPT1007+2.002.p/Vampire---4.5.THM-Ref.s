%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:51 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 554 expanded)
%              Number of leaves         :   16 ( 145 expanded)
%              Depth                    :   17
%              Number of atoms          :  208 (1433 expanded)
%              Number of equality atoms :   43 ( 415 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f391,plain,(
    $false ),
    inference(resolution,[],[f383,f78])).

fof(f78,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f38,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f38,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

% (28634)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
fof(f383,plain,(
    r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0)),k1_xboole_0) ),
    inference(global_subsumption,[],[f74,f76,f246,f382])).

fof(f382,plain,
    ( r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0)),k1_xboole_0)
    | r2_hidden(k1_xboole_0,sK1)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f381,f39])).

fof(f39,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f381,plain,
    ( r2_hidden(k1_xboole_0,sK1)
    | ~ v1_funct_1(k1_xboole_0)
    | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f366,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_funct_1(X0,X1)
      | ~ v1_funct_1(X0)
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(X1,k1_relat_1(X0))
      | k1_xboole_0 = X2
      | k1_funct_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( ( ~ r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 ) )
          & ( r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).

fof(f366,plain,(
    r2_hidden(k1_funct_1(k1_xboole_0,sK3(k2_enumset1(sK0,sK0,sK0,sK0))),sK1) ),
    inference(unit_resulting_resolution,[],[f76,f36,f219,f218,f84,f63])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X1
      | r2_hidden(k1_funct_1(X3,X2),X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

fof(f84,plain,(
    ! [X0] : r2_hidden(sK3(k2_enumset1(X0,X0,X0,X0)),k2_enumset1(X0,X0,X0,X0)) ),
    inference(unit_resulting_resolution,[],[f68,f50])).

fof(f50,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f68,plain,(
    ! [X0] : ~ v1_xboole_0(k2_enumset1(X0,X0,X0,X0)) ),
    inference(definition_unfolding,[],[f41,f65])).

fof(f65,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f43,f64])).

fof(f64,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f55,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f55,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f43,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f41,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(f218,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(backward_demodulation,[],[f66,f208])).

fof(f208,plain,(
    k1_xboole_0 = sK2 ),
    inference(unit_resulting_resolution,[],[f205,f54])).

fof(f54,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4] :
                  ~ ( k3_mcart_1(X2,X3,X4) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).

fof(f205,plain,(
    ! [X0] : ~ r2_hidden(X0,sK2) ),
    inference(unit_resulting_resolution,[],[f200,f191])).

fof(f191,plain,(
    ! [X0] :
      ( r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0))
      | ~ r2_hidden(X0,sK2) ) ),
    inference(duplicate_literal_removal,[],[f190])).

fof(f190,plain,(
    ! [X0] :
      ( r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0))
      | ~ r2_hidden(X0,sK2)
      | ~ r2_hidden(X0,sK2) ) ),
    inference(superposition,[],[f165,f163])).

fof(f163,plain,(
    ! [X0] :
      ( k1_mcart_1(X0) = sK0
      | ~ r2_hidden(X0,sK2) ) ),
    inference(resolution,[],[f141,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),X2))
      | k1_mcart_1(X0) = X1 ) ),
    inference(definition_unfolding,[],[f61,f65])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))
      | k1_mcart_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & k1_mcart_1(X0) = X1 )
      | ~ r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & k1_mcart_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_mcart_1)).

fof(f141,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
      | ~ r2_hidden(X0,sK2) ) ),
    inference(resolution,[],[f56,f66])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f165,plain,(
    ! [X2] :
      ( r2_hidden(k1_mcart_1(X2),k2_enumset1(sK0,sK0,sK0,sK0))
      | ~ r2_hidden(X2,sK2) ) ),
    inference(resolution,[],[f141,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f200,plain,(
    ~ r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(unit_resulting_resolution,[],[f33,f36,f37,f67,f66,f63])).

fof(f67,plain,(
    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f34,f65])).

fof(f34,plain,(
    v1_funct_2(sK2,k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).

fof(f37,plain,(
    ~ r2_hidden(k1_funct_1(sK2,sK0),sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f33,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f66,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f35,f65])).

fof(f35,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f21])).

fof(f219,plain,(
    v1_funct_2(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(backward_demodulation,[],[f67,f208])).

fof(f36,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f21])).

fof(f246,plain,(
    ~ r2_hidden(k1_xboole_0,sK1) ),
    inference(global_subsumption,[],[f38,f74,f245])).

fof(f245,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ r2_hidden(k1_xboole_0,sK1) ),
    inference(forward_demodulation,[],[f244,f39])).

fof(f244,plain,
    ( ~ v1_xboole_0(k1_relat_1(k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0)
    | ~ r2_hidden(k1_xboole_0,sK1) ),
    inference(forward_demodulation,[],[f226,f208])).

fof(f226,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ r2_hidden(k1_xboole_0,sK1)
    | ~ v1_xboole_0(k1_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f170,f208])).

fof(f170,plain,
    ( ~ r2_hidden(k1_xboole_0,sK1)
    | ~ v1_relat_1(sK2)
    | ~ v1_xboole_0(k1_relat_1(sK2)) ),
    inference(resolution,[],[f169,f51])).

fof(f169,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ r2_hidden(k1_xboole_0,sK1)
    | ~ v1_relat_1(sK2) ),
    inference(global_subsumption,[],[f33,f168])).

fof(f168,plain,
    ( ~ r2_hidden(k1_xboole_0,sK1)
    | ~ v1_funct_1(sK2)
    | r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f37,f72])).

fof(f76,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f38,f45])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).

fof(f74,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f38,f44])).

fof(f44,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:25:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.54  % (28630)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.55  % (28654)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.55  % (28631)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.56  % (28639)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.57  % (28653)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.57  % (28635)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.57  % (28632)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.57  % (28629)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.57  % (28645)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.57  % (28633)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.58  % (28641)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.58  % (28652)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.58  % (28644)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.59  % (28639)Refutation not found, incomplete strategy% (28639)------------------------------
% 0.21/0.59  % (28639)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.59  % (28639)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.59  
% 0.21/0.59  % (28639)Memory used [KB]: 10618
% 0.21/0.59  % (28639)Time elapsed: 0.154 s
% 0.21/0.59  % (28639)------------------------------
% 0.21/0.59  % (28639)------------------------------
% 0.21/0.59  % (28653)Refutation found. Thanks to Tanya!
% 0.21/0.59  % SZS status Theorem for theBenchmark
% 0.21/0.59  % (28651)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.59  % SZS output start Proof for theBenchmark
% 0.21/0.59  fof(f391,plain,(
% 0.21/0.59    $false),
% 0.21/0.59    inference(resolution,[],[f383,f78])).
% 0.21/0.59  fof(f78,plain,(
% 0.21/0.59    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.59    inference(unit_resulting_resolution,[],[f38,f51])).
% 0.21/0.59  fof(f51,plain,(
% 0.21/0.59    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f1])).
% 0.21/0.59  fof(f1,axiom,(
% 0.21/0.59    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.59  fof(f38,plain,(
% 0.21/0.59    v1_xboole_0(k1_xboole_0)),
% 0.21/0.59    inference(cnf_transformation,[],[f2])).
% 0.21/0.59  fof(f2,axiom,(
% 0.21/0.59    v1_xboole_0(k1_xboole_0)),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.59  % (28634)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.59  fof(f383,plain,(
% 0.21/0.59    r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0)),k1_xboole_0)),
% 0.21/0.59    inference(global_subsumption,[],[f74,f76,f246,f382])).
% 0.21/0.59  fof(f382,plain,(
% 0.21/0.59    r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0)),k1_xboole_0) | r2_hidden(k1_xboole_0,sK1) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)),
% 0.21/0.59    inference(forward_demodulation,[],[f381,f39])).
% 0.21/0.59  fof(f39,plain,(
% 0.21/0.59    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.59    inference(cnf_transformation,[],[f10])).
% 0.21/0.59  fof(f10,axiom,(
% 0.21/0.59    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.59  fof(f381,plain,(
% 0.21/0.59    r2_hidden(k1_xboole_0,sK1) | ~v1_funct_1(k1_xboole_0) | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0)),
% 0.21/0.59    inference(superposition,[],[f366,f72])).
% 0.21/0.59  fof(f72,plain,(
% 0.21/0.59    ( ! [X0,X1] : (k1_xboole_0 = k1_funct_1(X0,X1) | ~v1_funct_1(X0) | r2_hidden(X1,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.59    inference(equality_resolution,[],[f47])).
% 0.21/0.59  fof(f47,plain,(
% 0.21/0.59    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(X1,k1_relat_1(X0)) | k1_xboole_0 = X2 | k1_funct_1(X0,X1) != X2) )),
% 0.21/0.59    inference(cnf_transformation,[],[f25])).
% 0.21/0.59  fof(f25,plain,(
% 0.21/0.59    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.59    inference(flattening,[],[f24])).
% 0.21/0.59  fof(f24,plain,(
% 0.21/0.59    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.59    inference(ennf_transformation,[],[f12])).
% 0.21/0.59  fof(f12,axiom,(
% 0.21/0.59    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : ((~r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2)) & (r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)))))),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).
% 0.21/0.59  fof(f366,plain,(
% 0.21/0.59    r2_hidden(k1_funct_1(k1_xboole_0,sK3(k2_enumset1(sK0,sK0,sK0,sK0))),sK1)),
% 0.21/0.59    inference(unit_resulting_resolution,[],[f76,f36,f219,f218,f84,f63])).
% 0.21/0.59  fof(f63,plain,(
% 0.21/0.59    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~r2_hidden(X2,X0) | k1_xboole_0 = X1 | r2_hidden(k1_funct_1(X3,X2),X1)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f32])).
% 0.21/0.59  fof(f32,plain,(
% 0.21/0.59    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.21/0.59    inference(flattening,[],[f31])).
% 0.21/0.59  fof(f31,plain,(
% 0.21/0.59    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.21/0.59    inference(ennf_transformation,[],[f17])).
% 0.21/0.59  fof(f17,axiom,(
% 0.21/0.59    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).
% 0.21/0.59  fof(f84,plain,(
% 0.21/0.59    ( ! [X0] : (r2_hidden(sK3(k2_enumset1(X0,X0,X0,X0)),k2_enumset1(X0,X0,X0,X0))) )),
% 0.21/0.59    inference(unit_resulting_resolution,[],[f68,f50])).
% 0.21/0.59  fof(f50,plain,(
% 0.21/0.59    ( ! [X0] : (r2_hidden(sK3(X0),X0) | v1_xboole_0(X0)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f1])).
% 0.21/0.59  fof(f68,plain,(
% 0.21/0.59    ( ! [X0] : (~v1_xboole_0(k2_enumset1(X0,X0,X0,X0))) )),
% 0.21/0.59    inference(definition_unfolding,[],[f41,f65])).
% 0.21/0.59  fof(f65,plain,(
% 0.21/0.59    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.21/0.59    inference(definition_unfolding,[],[f43,f64])).
% 0.21/0.59  fof(f64,plain,(
% 0.21/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.59    inference(definition_unfolding,[],[f55,f58])).
% 0.21/0.59  fof(f58,plain,(
% 0.21/0.59    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f6])).
% 0.21/0.59  fof(f6,axiom,(
% 0.21/0.59    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.59  fof(f55,plain,(
% 0.21/0.59    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f5])).
% 0.21/0.59  fof(f5,axiom,(
% 0.21/0.59    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.59  fof(f43,plain,(
% 0.21/0.59    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f4])).
% 0.21/0.59  fof(f4,axiom,(
% 0.21/0.59    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.59  fof(f41,plain,(
% 0.21/0.59    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 0.21/0.59    inference(cnf_transformation,[],[f7])).
% 0.21/0.59  fof(f7,axiom,(
% 0.21/0.59    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).
% 0.21/0.59  fof(f218,plain,(
% 0.21/0.59    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 0.21/0.59    inference(backward_demodulation,[],[f66,f208])).
% 0.21/0.59  fof(f208,plain,(
% 0.21/0.59    k1_xboole_0 = sK2),
% 0.21/0.59    inference(unit_resulting_resolution,[],[f205,f54])).
% 0.21/0.59  fof(f54,plain,(
% 0.21/0.59    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.59    inference(cnf_transformation,[],[f26])).
% 0.21/0.59  fof(f26,plain,(
% 0.21/0.59    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.21/0.59    inference(ennf_transformation,[],[f16])).
% 0.21/0.59  fof(f16,axiom,(
% 0.21/0.59    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4] : ~(k3_mcart_1(X2,X3,X4) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).
% 0.21/0.59  fof(f205,plain,(
% 0.21/0.59    ( ! [X0] : (~r2_hidden(X0,sK2)) )),
% 0.21/0.59    inference(unit_resulting_resolution,[],[f200,f191])).
% 0.21/0.59  fof(f191,plain,(
% 0.21/0.59    ( ! [X0] : (r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0)) | ~r2_hidden(X0,sK2)) )),
% 0.21/0.59    inference(duplicate_literal_removal,[],[f190])).
% 0.21/0.59  fof(f190,plain,(
% 0.21/0.59    ( ! [X0] : (r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0)) | ~r2_hidden(X0,sK2) | ~r2_hidden(X0,sK2)) )),
% 0.21/0.59    inference(superposition,[],[f165,f163])).
% 0.21/0.59  fof(f163,plain,(
% 0.21/0.59    ( ! [X0] : (k1_mcart_1(X0) = sK0 | ~r2_hidden(X0,sK2)) )),
% 0.21/0.59    inference(resolution,[],[f141,f70])).
% 0.21/0.59  fof(f70,plain,(
% 0.21/0.59    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),X2)) | k1_mcart_1(X0) = X1) )),
% 0.21/0.59    inference(definition_unfolding,[],[f61,f65])).
% 0.21/0.59  fof(f61,plain,(
% 0.21/0.59    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) | k1_mcart_1(X0) = X1) )),
% 0.21/0.59    inference(cnf_transformation,[],[f30])).
% 0.21/0.59  fof(f30,plain,(
% 0.21/0.59    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & k1_mcart_1(X0) = X1) | ~r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)))),
% 0.21/0.59    inference(ennf_transformation,[],[f15])).
% 0.21/0.59  fof(f15,axiom,(
% 0.21/0.59    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) => (r2_hidden(k2_mcart_1(X0),X2) & k1_mcart_1(X0) = X1))),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_mcart_1)).
% 0.21/0.59  fof(f141,plain,(
% 0.21/0.59    ( ! [X0] : (r2_hidden(X0,k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) | ~r2_hidden(X0,sK2)) )),
% 0.21/0.59    inference(resolution,[],[f56,f66])).
% 0.21/0.59  fof(f56,plain,(
% 0.21/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f27])).
% 0.21/0.59  fof(f27,plain,(
% 0.21/0.59    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.59    inference(ennf_transformation,[],[f8])).
% 0.21/0.59  fof(f8,axiom,(
% 0.21/0.59    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.21/0.59  fof(f165,plain,(
% 0.21/0.59    ( ! [X2] : (r2_hidden(k1_mcart_1(X2),k2_enumset1(sK0,sK0,sK0,sK0)) | ~r2_hidden(X2,sK2)) )),
% 0.21/0.59    inference(resolution,[],[f141,f59])).
% 0.21/0.59  fof(f59,plain,(
% 0.21/0.59    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f29])).
% 0.21/0.60  fof(f29,plain,(
% 0.21/0.60    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.21/0.60    inference(ennf_transformation,[],[f14])).
% 0.21/0.60  fof(f14,axiom,(
% 0.21/0.60    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).
% 0.21/0.60  fof(f200,plain,(
% 0.21/0.60    ~r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.21/0.60    inference(unit_resulting_resolution,[],[f33,f36,f37,f67,f66,f63])).
% 0.21/0.60  fof(f67,plain,(
% 0.21/0.60    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 0.21/0.60    inference(definition_unfolding,[],[f34,f65])).
% 0.21/0.60  fof(f34,plain,(
% 0.21/0.60    v1_funct_2(sK2,k1_tarski(sK0),sK1)),
% 0.21/0.60    inference(cnf_transformation,[],[f21])).
% 0.21/0.60  fof(f21,plain,(
% 0.21/0.60    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 0.21/0.60    inference(flattening,[],[f20])).
% 0.21/0.60  fof(f20,plain,(
% 0.21/0.60    ? [X0,X1,X2] : ((~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 0.21/0.60    inference(ennf_transformation,[],[f19])).
% 0.21/0.60  fof(f19,negated_conjecture,(
% 0.21/0.60    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 0.21/0.60    inference(negated_conjecture,[],[f18])).
% 0.21/0.60  fof(f18,conjecture,(
% 0.21/0.60    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).
% 0.21/0.60  fof(f37,plain,(
% 0.21/0.60    ~r2_hidden(k1_funct_1(sK2,sK0),sK1)),
% 0.21/0.60    inference(cnf_transformation,[],[f21])).
% 0.21/0.60  fof(f33,plain,(
% 0.21/0.60    v1_funct_1(sK2)),
% 0.21/0.60    inference(cnf_transformation,[],[f21])).
% 0.21/0.60  fof(f66,plain,(
% 0.21/0.60    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 0.21/0.60    inference(definition_unfolding,[],[f35,f65])).
% 0.21/0.60  fof(f35,plain,(
% 0.21/0.60    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 0.21/0.60    inference(cnf_transformation,[],[f21])).
% 0.21/0.60  fof(f219,plain,(
% 0.21/0.60    v1_funct_2(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 0.21/0.60    inference(backward_demodulation,[],[f67,f208])).
% 0.21/0.60  fof(f36,plain,(
% 0.21/0.60    k1_xboole_0 != sK1),
% 0.21/0.60    inference(cnf_transformation,[],[f21])).
% 0.21/0.60  fof(f246,plain,(
% 0.21/0.60    ~r2_hidden(k1_xboole_0,sK1)),
% 0.21/0.60    inference(global_subsumption,[],[f38,f74,f245])).
% 0.21/0.60  fof(f245,plain,(
% 0.21/0.60    ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~r2_hidden(k1_xboole_0,sK1)),
% 0.21/0.60    inference(forward_demodulation,[],[f244,f39])).
% 0.21/0.60  fof(f244,plain,(
% 0.21/0.60    ~v1_xboole_0(k1_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0) | ~r2_hidden(k1_xboole_0,sK1)),
% 0.21/0.60    inference(forward_demodulation,[],[f226,f208])).
% 0.21/0.60  fof(f226,plain,(
% 0.21/0.60    ~v1_relat_1(k1_xboole_0) | ~r2_hidden(k1_xboole_0,sK1) | ~v1_xboole_0(k1_relat_1(sK2))),
% 0.21/0.60    inference(backward_demodulation,[],[f170,f208])).
% 0.21/0.60  fof(f170,plain,(
% 0.21/0.60    ~r2_hidden(k1_xboole_0,sK1) | ~v1_relat_1(sK2) | ~v1_xboole_0(k1_relat_1(sK2))),
% 0.21/0.60    inference(resolution,[],[f169,f51])).
% 0.21/0.60  fof(f169,plain,(
% 0.21/0.60    r2_hidden(sK0,k1_relat_1(sK2)) | ~r2_hidden(k1_xboole_0,sK1) | ~v1_relat_1(sK2)),
% 0.21/0.60    inference(global_subsumption,[],[f33,f168])).
% 0.21/0.60  fof(f168,plain,(
% 0.21/0.60    ~r2_hidden(k1_xboole_0,sK1) | ~v1_funct_1(sK2) | r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 0.21/0.60    inference(superposition,[],[f37,f72])).
% 0.21/0.60  fof(f76,plain,(
% 0.21/0.60    v1_funct_1(k1_xboole_0)),
% 0.21/0.60    inference(unit_resulting_resolution,[],[f38,f45])).
% 0.21/0.60  fof(f45,plain,(
% 0.21/0.60    ( ! [X0] : (~v1_xboole_0(X0) | v1_funct_1(X0)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f23])).
% 0.21/0.60  fof(f23,plain,(
% 0.21/0.60    ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0))),
% 0.21/0.60    inference(ennf_transformation,[],[f11])).
% 0.21/0.60  fof(f11,axiom,(
% 0.21/0.60    ! [X0] : (v1_xboole_0(X0) => v1_funct_1(X0))),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).
% 0.21/0.60  fof(f74,plain,(
% 0.21/0.60    v1_relat_1(k1_xboole_0)),
% 0.21/0.60    inference(unit_resulting_resolution,[],[f38,f44])).
% 0.21/0.60  fof(f44,plain,(
% 0.21/0.60    ( ! [X0] : (~v1_xboole_0(X0) | v1_relat_1(X0)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f22])).
% 0.21/0.60  fof(f22,plain,(
% 0.21/0.60    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.21/0.60    inference(ennf_transformation,[],[f9])).
% 0.21/0.60  fof(f9,axiom,(
% 0.21/0.60    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).
% 0.21/0.60  % SZS output end Proof for theBenchmark
% 0.21/0.60  % (28653)------------------------------
% 0.21/0.60  % (28653)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.60  % (28653)Termination reason: Refutation
% 0.21/0.60  
% 0.21/0.60  % (28653)Memory used [KB]: 6524
% 0.21/0.60  % (28653)Time elapsed: 0.147 s
% 0.21/0.60  % (28653)------------------------------
% 0.21/0.60  % (28653)------------------------------
% 0.21/0.60  % (28628)Success in time 0.233 s
%------------------------------------------------------------------------------
