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
% DateTime   : Thu Dec  3 13:04:01 EST 2020

% Result     : Theorem 1.50s
% Output     : Refutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 390 expanded)
%              Number of leaves         :   19 ( 100 expanded)
%              Depth                    :   20
%              Number of atoms          :  234 ( 976 expanded)
%              Number of equality atoms :   63 ( 373 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f239,plain,(
    $false ),
    inference(subsumption_resolution,[],[f205,f47])).

fof(f47,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f205,plain,(
    k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f142,f178])).

fof(f178,plain,(
    k1_xboole_0 = sK2 ),
    inference(resolution,[],[f164,f55])).

fof(f55,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5,X6] :
              ( r1_xboole_0(X2,X0)
              | ~ r2_hidden(X6,X1)
              | ~ r2_hidden(X5,X6)
              | ~ r2_hidden(X4,X5)
              | ~ r2_hidden(X3,X4)
              | ~ r2_hidden(X2,X3) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5,X6] :
              ( r1_xboole_0(X2,X0)
              | ~ r2_hidden(X6,X1)
              | ~ r2_hidden(X5,X6)
              | ~ r2_hidden(X4,X5)
              | ~ r2_hidden(X3,X4)
              | ~ r2_hidden(X2,X3) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f21])).

% (21792)Refutation not found, incomplete strategy% (21792)------------------------------
% (21792)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (21792)Termination reason: Refutation not found, incomplete strategy

% (21792)Memory used [KB]: 10618
fof(f21,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5,X6] :
                  ( ( r2_hidden(X6,X1)
                    & r2_hidden(X5,X6)
                    & r2_hidden(X4,X5)
                    & r2_hidden(X3,X4)
                    & r2_hidden(X2,X3) )
                 => r1_xboole_0(X2,X0) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_mcart_1)).

% (21792)Time elapsed: 0.147 s
% (21792)------------------------------
% (21792)------------------------------
fof(f164,plain,(
    ! [X0] : ~ r2_hidden(X0,sK2) ),
    inference(resolution,[],[f163,f137])).

fof(f137,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_zfmisc_1(k1_relat_1(sK2),sK1))
      | ~ r2_hidden(X0,sK2) ) ),
    inference(backward_demodulation,[],[f108,f131])).

fof(f131,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) ),
    inference(forward_demodulation,[],[f111,f106])).

fof(f106,plain,(
    k1_relat_1(sK2) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) ),
    inference(resolution,[],[f88,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f88,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f44,f87])).

fof(f87,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f52,f86])).

fof(f86,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f58,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f58,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f52,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f44,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).

fof(f111,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) ),
    inference(subsumption_resolution,[],[f110,f89])).

fof(f89,plain,(
    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f43,f87])).

fof(f43,plain,(
    v1_funct_2(sK2,k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f110,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)
    | ~ v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(subsumption_resolution,[],[f103,f45])).

fof(f45,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f26])).

fof(f103,plain,
    ( k1_xboole_0 = sK1
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)
    | ~ v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(resolution,[],[f88,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f108,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
      | ~ r2_hidden(X0,sK2) ) ),
    inference(resolution,[],[f88,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f163,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(k1_relat_1(sK2),X1)) ),
    inference(condensation,[],[f161])).

fof(f161,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(k1_relat_1(sK2),X1))
      | ~ r2_hidden(X0,k2_zfmisc_1(k1_relat_1(sK2),X2)) ) ),
    inference(resolution,[],[f160,f156])).

fof(f156,plain,(
    ! [X4,X2,X3,X1] :
      ( r2_hidden(sK0,X2)
      | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,k2_zfmisc_1(k1_relat_1(sK2),X4)) ) ),
    inference(superposition,[],[f73,f139])).

fof(f139,plain,(
    ! [X0,X1] :
      ( k1_mcart_1(X0) = sK0
      | ~ r2_hidden(X0,k2_zfmisc_1(k1_relat_1(sK2),X1)) ) ),
    inference(superposition,[],[f92,f131])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),X2))
      | k1_mcart_1(X0) = X1 ) ),
    inference(definition_unfolding,[],[f84,f87])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))
      | k1_mcart_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & k1_mcart_1(X0) = X1 )
      | ~ r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & k1_mcart_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_mcart_1)).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f160,plain,(
    ~ r2_hidden(sK0,k1_relat_1(sK2)) ),
    inference(resolution,[],[f159,f125])).

fof(f125,plain,(
    ~ r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(sK2)) ),
    inference(resolution,[],[f121,f46])).

fof(f46,plain,(
    ~ r2_hidden(k1_funct_1(sK2,sK0),sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f121,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,k2_relat_1(sK2)) ) ),
    inference(resolution,[],[f119,f62])).

fof(f119,plain,(
    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f117,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f117,plain,(
    r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(subsumption_resolution,[],[f116,f56])).

fof(f56,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f116,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | ~ v1_relat_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
    inference(resolution,[],[f114,f88])).

fof(f114,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | r1_tarski(k2_relat_1(sK2),sK1)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f113,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f113,plain,
    ( ~ v1_relat_1(sK2)
    | r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(resolution,[],[f105,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f105,plain,(
    v5_relat_1(sK2,sK1) ),
    inference(resolution,[],[f88,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f159,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK2))
      | ~ r2_hidden(X0,k1_relat_1(sK2)) ) ),
    inference(subsumption_resolution,[],[f158,f56])).

fof(f158,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK2))
      | ~ r2_hidden(X0,k1_relat_1(sK2))
      | ~ v1_relat_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)) ) ),
    inference(resolution,[],[f126,f132])).

fof(f132,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) ),
    inference(backward_demodulation,[],[f88,f131])).

fof(f126,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X1))
      | r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK2))
      | ~ r2_hidden(X0,k1_relat_1(sK2))
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f101,f53])).

fof(f101,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK2)
      | ~ r2_hidden(X0,k1_relat_1(sK2))
      | r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK2)) ) ),
    inference(resolution,[],[f42,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

fof(f42,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f142,plain,(
    k1_xboole_0 != k1_relat_1(sK2) ),
    inference(superposition,[],[f140,f51])).

fof(f51,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f140,plain,(
    ! [X2] : k1_xboole_0 != k2_xboole_0(k1_relat_1(sK2),X2) ),
    inference(superposition,[],[f90,f131])).

fof(f90,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) ),
    inference(definition_unfolding,[],[f57,f87])).

fof(f57,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 21:08:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (21797)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.51  % (21782)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.51  % (21783)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.51  % (21784)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (21805)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.52  % (21789)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.52  % (21794)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (21804)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.53  % (21796)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.53  % (21799)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.53  % (21786)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.53  % (21807)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.53  % (21788)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.53  % (21809)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.53  % (21810)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.54  % (21785)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.54  % (21806)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.54  % (21800)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.54  % (21787)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.54  % (21793)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.54  % (21798)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.54  % (21793)Refutation not found, incomplete strategy% (21793)------------------------------
% 0.20/0.54  % (21793)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (21793)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (21793)Memory used [KB]: 10618
% 0.20/0.54  % (21793)Time elapsed: 0.137 s
% 0.20/0.54  % (21793)------------------------------
% 0.20/0.54  % (21793)------------------------------
% 0.20/0.54  % (21799)Refutation not found, incomplete strategy% (21799)------------------------------
% 0.20/0.54  % (21799)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (21799)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (21799)Memory used [KB]: 10618
% 0.20/0.54  % (21799)Time elapsed: 0.135 s
% 0.20/0.54  % (21799)------------------------------
% 0.20/0.54  % (21799)------------------------------
% 0.20/0.54  % (21792)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.54  % (21802)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.55  % (21791)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.50/0.55  % (21790)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.50/0.55  % (21803)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.50/0.55  % (21811)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.50/0.55  % (21803)Refutation found. Thanks to Tanya!
% 1.50/0.55  % SZS status Theorem for theBenchmark
% 1.50/0.55  % SZS output start Proof for theBenchmark
% 1.50/0.55  fof(f239,plain,(
% 1.50/0.55    $false),
% 1.50/0.55    inference(subsumption_resolution,[],[f205,f47])).
% 1.50/0.55  fof(f47,plain,(
% 1.50/0.55    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.50/0.55    inference(cnf_transformation,[],[f15])).
% 1.50/0.55  fof(f15,axiom,(
% 1.50/0.55    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.50/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 1.50/0.55  fof(f205,plain,(
% 1.50/0.55    k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 1.50/0.55    inference(backward_demodulation,[],[f142,f178])).
% 1.50/0.55  fof(f178,plain,(
% 1.50/0.55    k1_xboole_0 = sK2),
% 1.50/0.55    inference(resolution,[],[f164,f55])).
% 1.50/0.55  fof(f55,plain,(
% 1.50/0.55    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 1.50/0.55    inference(cnf_transformation,[],[f29])).
% 1.50/0.55  fof(f29,plain,(
% 1.50/0.55    ! [X0] : (? [X1] : (! [X2,X3,X4,X5,X6] : (r1_xboole_0(X2,X0) | ~r2_hidden(X6,X1) | ~r2_hidden(X5,X6) | ~r2_hidden(X4,X5) | ~r2_hidden(X3,X4) | ~r2_hidden(X2,X3)) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 1.50/0.55    inference(flattening,[],[f28])).
% 1.50/0.55  fof(f28,plain,(
% 1.50/0.55    ! [X0] : (? [X1] : (! [X2,X3,X4,X5,X6] : (r1_xboole_0(X2,X0) | (~r2_hidden(X6,X1) | ~r2_hidden(X5,X6) | ~r2_hidden(X4,X5) | ~r2_hidden(X3,X4) | ~r2_hidden(X2,X3))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 1.50/0.55    inference(ennf_transformation,[],[f21])).
% 1.50/0.55  % (21792)Refutation not found, incomplete strategy% (21792)------------------------------
% 1.50/0.55  % (21792)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.55  % (21792)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.55  
% 1.50/0.55  % (21792)Memory used [KB]: 10618
% 1.50/0.55  fof(f21,axiom,(
% 1.50/0.55    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5,X6] : ((r2_hidden(X6,X1) & r2_hidden(X5,X6) & r2_hidden(X4,X5) & r2_hidden(X3,X4) & r2_hidden(X2,X3)) => r1_xboole_0(X2,X0)) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 1.50/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_mcart_1)).
% 1.50/0.55  % (21792)Time elapsed: 0.147 s
% 1.50/0.55  % (21792)------------------------------
% 1.50/0.55  % (21792)------------------------------
% 1.50/0.55  fof(f164,plain,(
% 1.50/0.55    ( ! [X0] : (~r2_hidden(X0,sK2)) )),
% 1.50/0.55    inference(resolution,[],[f163,f137])).
% 1.50/0.55  fof(f137,plain,(
% 1.50/0.55    ( ! [X0] : (r2_hidden(X0,k2_zfmisc_1(k1_relat_1(sK2),sK1)) | ~r2_hidden(X0,sK2)) )),
% 1.50/0.55    inference(backward_demodulation,[],[f108,f131])).
% 1.50/0.55  fof(f131,plain,(
% 1.50/0.55    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)),
% 1.50/0.55    inference(forward_demodulation,[],[f111,f106])).
% 1.50/0.55  fof(f106,plain,(
% 1.50/0.55    k1_relat_1(sK2) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)),
% 1.50/0.55    inference(resolution,[],[f88,f75])).
% 1.50/0.55  fof(f75,plain,(
% 1.50/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.50/0.55    inference(cnf_transformation,[],[f37])).
% 1.50/0.55  fof(f37,plain,(
% 1.50/0.55    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.50/0.55    inference(ennf_transformation,[],[f18])).
% 1.50/0.55  fof(f18,axiom,(
% 1.50/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.50/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.50/0.55  fof(f88,plain,(
% 1.50/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 1.50/0.55    inference(definition_unfolding,[],[f44,f87])).
% 1.50/0.55  fof(f87,plain,(
% 1.50/0.55    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.50/0.55    inference(definition_unfolding,[],[f52,f86])).
% 1.50/0.55  fof(f86,plain,(
% 1.50/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.50/0.55    inference(definition_unfolding,[],[f58,f72])).
% 1.50/0.55  fof(f72,plain,(
% 1.50/0.55    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.50/0.55    inference(cnf_transformation,[],[f4])).
% 1.50/0.55  fof(f4,axiom,(
% 1.50/0.55    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.50/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.50/0.55  fof(f58,plain,(
% 1.50/0.55    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.50/0.55    inference(cnf_transformation,[],[f3])).
% 1.50/0.55  fof(f3,axiom,(
% 1.50/0.55    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.50/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.50/0.55  fof(f52,plain,(
% 1.50/0.55    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.50/0.55    inference(cnf_transformation,[],[f2])).
% 1.50/0.55  fof(f2,axiom,(
% 1.50/0.55    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.50/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.50/0.55  fof(f44,plain,(
% 1.50/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 1.50/0.55    inference(cnf_transformation,[],[f26])).
% 1.50/0.55  fof(f26,plain,(
% 1.50/0.55    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 1.50/0.55    inference(flattening,[],[f25])).
% 1.50/0.55  fof(f25,plain,(
% 1.50/0.55    ? [X0,X1,X2] : ((~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 1.50/0.55    inference(ennf_transformation,[],[f24])).
% 1.50/0.55  fof(f24,negated_conjecture,(
% 1.50/0.55    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 1.50/0.55    inference(negated_conjecture,[],[f23])).
% 1.50/0.55  fof(f23,conjecture,(
% 1.50/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 1.50/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).
% 1.50/0.55  fof(f111,plain,(
% 1.50/0.55    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)),
% 1.50/0.55    inference(subsumption_resolution,[],[f110,f89])).
% 1.50/0.55  fof(f89,plain,(
% 1.50/0.55    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 1.50/0.55    inference(definition_unfolding,[],[f43,f87])).
% 1.50/0.55  fof(f43,plain,(
% 1.50/0.55    v1_funct_2(sK2,k1_tarski(sK0),sK1)),
% 1.50/0.55    inference(cnf_transformation,[],[f26])).
% 1.50/0.55  fof(f110,plain,(
% 1.50/0.55    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) | ~v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 1.50/0.55    inference(subsumption_resolution,[],[f103,f45])).
% 1.50/0.55  fof(f45,plain,(
% 1.50/0.55    k1_xboole_0 != sK1),
% 1.50/0.55    inference(cnf_transformation,[],[f26])).
% 1.50/0.55  fof(f103,plain,(
% 1.50/0.55    k1_xboole_0 = sK1 | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) | ~v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 1.50/0.55    inference(resolution,[],[f88,f83])).
% 1.50/0.55  fof(f83,plain,(
% 1.50/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 1.50/0.55    inference(cnf_transformation,[],[f40])).
% 1.50/0.55  fof(f40,plain,(
% 1.50/0.55    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.50/0.55    inference(flattening,[],[f39])).
% 1.50/0.55  fof(f39,plain,(
% 1.50/0.55    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.50/0.55    inference(ennf_transformation,[],[f22])).
% 1.50/0.55  fof(f22,axiom,(
% 1.50/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.50/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.50/0.55  fof(f108,plain,(
% 1.50/0.55    ( ! [X0] : (r2_hidden(X0,k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) | ~r2_hidden(X0,sK2)) )),
% 1.50/0.55    inference(resolution,[],[f88,f62])).
% 1.50/0.55  fof(f62,plain,(
% 1.50/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 1.50/0.55    inference(cnf_transformation,[],[f33])).
% 1.50/0.55  fof(f33,plain,(
% 1.50/0.55    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.50/0.55    inference(ennf_transformation,[],[f9])).
% 1.50/0.55  fof(f9,axiom,(
% 1.50/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.50/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 1.50/0.55  fof(f163,plain,(
% 1.50/0.55    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(k1_relat_1(sK2),X1))) )),
% 1.50/0.55    inference(condensation,[],[f161])).
% 1.50/0.55  fof(f161,plain,(
% 1.50/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(k1_relat_1(sK2),X1)) | ~r2_hidden(X0,k2_zfmisc_1(k1_relat_1(sK2),X2))) )),
% 1.50/0.55    inference(resolution,[],[f160,f156])).
% 1.50/0.55  fof(f156,plain,(
% 1.50/0.55    ( ! [X4,X2,X3,X1] : (r2_hidden(sK0,X2) | ~r2_hidden(X1,k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,k2_zfmisc_1(k1_relat_1(sK2),X4))) )),
% 1.50/0.55    inference(superposition,[],[f73,f139])).
% 1.50/0.55  fof(f139,plain,(
% 1.50/0.55    ( ! [X0,X1] : (k1_mcart_1(X0) = sK0 | ~r2_hidden(X0,k2_zfmisc_1(k1_relat_1(sK2),X1))) )),
% 1.50/0.55    inference(superposition,[],[f92,f131])).
% 1.50/0.55  fof(f92,plain,(
% 1.50/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),X2)) | k1_mcart_1(X0) = X1) )),
% 1.50/0.55    inference(definition_unfolding,[],[f84,f87])).
% 1.50/0.55  fof(f84,plain,(
% 1.50/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) | k1_mcart_1(X0) = X1) )),
% 1.50/0.55    inference(cnf_transformation,[],[f41])).
% 1.50/0.55  fof(f41,plain,(
% 1.50/0.55    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & k1_mcart_1(X0) = X1) | ~r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)))),
% 1.50/0.55    inference(ennf_transformation,[],[f20])).
% 1.50/0.55  fof(f20,axiom,(
% 1.50/0.55    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) => (r2_hidden(k2_mcart_1(X0),X2) & k1_mcart_1(X0) = X1))),
% 1.50/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_mcart_1)).
% 1.50/0.55  fof(f73,plain,(
% 1.50/0.55    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 1.50/0.55    inference(cnf_transformation,[],[f36])).
% 1.50/0.55  fof(f36,plain,(
% 1.50/0.55    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 1.50/0.55    inference(ennf_transformation,[],[f19])).
% 1.50/0.55  fof(f19,axiom,(
% 1.50/0.55    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 1.50/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).
% 1.50/0.55  fof(f160,plain,(
% 1.50/0.55    ~r2_hidden(sK0,k1_relat_1(sK2))),
% 1.50/0.55    inference(resolution,[],[f159,f125])).
% 1.50/0.55  fof(f125,plain,(
% 1.50/0.55    ~r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(sK2))),
% 1.50/0.55    inference(resolution,[],[f121,f46])).
% 1.50/0.55  fof(f46,plain,(
% 1.50/0.55    ~r2_hidden(k1_funct_1(sK2,sK0),sK1)),
% 1.50/0.55    inference(cnf_transformation,[],[f26])).
% 1.50/0.55  fof(f121,plain,(
% 1.50/0.55    ( ! [X0] : (r2_hidden(X0,sK1) | ~r2_hidden(X0,k2_relat_1(sK2))) )),
% 1.50/0.55    inference(resolution,[],[f119,f62])).
% 1.50/0.55  fof(f119,plain,(
% 1.50/0.55    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))),
% 1.50/0.55    inference(resolution,[],[f117,f70])).
% 1.50/0.55  fof(f70,plain,(
% 1.50/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.50/0.55    inference(cnf_transformation,[],[f11])).
% 1.50/0.55  fof(f11,axiom,(
% 1.50/0.55    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.50/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.50/0.55  fof(f117,plain,(
% 1.50/0.55    r1_tarski(k2_relat_1(sK2),sK1)),
% 1.50/0.55    inference(subsumption_resolution,[],[f116,f56])).
% 1.50/0.55  fof(f56,plain,(
% 1.50/0.55    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.50/0.55    inference(cnf_transformation,[],[f14])).
% 1.50/0.55  fof(f14,axiom,(
% 1.50/0.55    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.50/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.50/0.55  fof(f116,plain,(
% 1.50/0.55    r1_tarski(k2_relat_1(sK2),sK1) | ~v1_relat_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))),
% 1.50/0.55    inference(resolution,[],[f114,f88])).
% 1.50/0.55  fof(f114,plain,(
% 1.50/0.55    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(X0)) | r1_tarski(k2_relat_1(sK2),sK1) | ~v1_relat_1(X0)) )),
% 1.50/0.55    inference(resolution,[],[f113,f53])).
% 1.50/0.55  fof(f53,plain,(
% 1.50/0.55    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.50/0.55    inference(cnf_transformation,[],[f27])).
% 1.50/0.55  fof(f27,plain,(
% 1.50/0.55    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.50/0.55    inference(ennf_transformation,[],[f12])).
% 1.50/0.55  fof(f12,axiom,(
% 1.50/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.50/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.50/0.55  fof(f113,plain,(
% 1.50/0.55    ~v1_relat_1(sK2) | r1_tarski(k2_relat_1(sK2),sK1)),
% 1.50/0.55    inference(resolution,[],[f105,f60])).
% 1.50/0.55  fof(f60,plain,(
% 1.50/0.55    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.50/0.55    inference(cnf_transformation,[],[f30])).
% 1.50/0.55  fof(f30,plain,(
% 1.50/0.55    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.50/0.55    inference(ennf_transformation,[],[f13])).
% 1.50/0.55  fof(f13,axiom,(
% 1.50/0.55    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.50/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 1.50/0.55  fof(f105,plain,(
% 1.50/0.55    v5_relat_1(sK2,sK1)),
% 1.50/0.55    inference(resolution,[],[f88,f77])).
% 1.50/0.55  fof(f77,plain,(
% 1.50/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.50/0.55    inference(cnf_transformation,[],[f38])).
% 1.50/0.55  fof(f38,plain,(
% 1.50/0.55    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.50/0.55    inference(ennf_transformation,[],[f17])).
% 1.50/0.55  fof(f17,axiom,(
% 1.50/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.50/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.50/0.55  fof(f159,plain,(
% 1.50/0.55    ( ! [X0] : (r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK2)) | ~r2_hidden(X0,k1_relat_1(sK2))) )),
% 1.50/0.55    inference(subsumption_resolution,[],[f158,f56])).
% 1.50/0.55  fof(f158,plain,(
% 1.50/0.55    ( ! [X0] : (r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK2)) | ~r2_hidden(X0,k1_relat_1(sK2)) | ~v1_relat_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) )),
% 1.50/0.55    inference(resolution,[],[f126,f132])).
% 1.50/0.55  fof(f132,plain,(
% 1.50/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))),
% 1.50/0.55    inference(backward_demodulation,[],[f88,f131])).
% 1.50/0.55  fof(f126,plain,(
% 1.50/0.55    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(X1)) | r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK2)) | ~r2_hidden(X0,k1_relat_1(sK2)) | ~v1_relat_1(X1)) )),
% 1.50/0.55    inference(resolution,[],[f101,f53])).
% 1.50/0.55  fof(f101,plain,(
% 1.50/0.55    ( ! [X0] : (~v1_relat_1(sK2) | ~r2_hidden(X0,k1_relat_1(sK2)) | r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK2))) )),
% 1.50/0.55    inference(resolution,[],[f42,f63])).
% 1.50/0.55  fof(f63,plain,(
% 1.50/0.55    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | ~r2_hidden(X0,k1_relat_1(X1)) | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))) )),
% 1.50/0.55    inference(cnf_transformation,[],[f35])).
% 1.50/0.55  fof(f35,plain,(
% 1.50/0.55    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.50/0.55    inference(flattening,[],[f34])).
% 1.50/0.55  fof(f34,plain,(
% 1.50/0.55    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.50/0.55    inference(ennf_transformation,[],[f16])).
% 1.50/0.55  fof(f16,axiom,(
% 1.50/0.55    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 1.50/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).
% 1.50/0.55  fof(f42,plain,(
% 1.50/0.55    v1_funct_1(sK2)),
% 1.50/0.55    inference(cnf_transformation,[],[f26])).
% 1.50/0.55  fof(f142,plain,(
% 1.50/0.55    k1_xboole_0 != k1_relat_1(sK2)),
% 1.50/0.55    inference(superposition,[],[f140,f51])).
% 1.50/0.55  fof(f51,plain,(
% 1.50/0.55    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.50/0.55    inference(cnf_transformation,[],[f1])).
% 1.50/0.55  fof(f1,axiom,(
% 1.50/0.55    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.50/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 1.50/0.55  fof(f140,plain,(
% 1.50/0.55    ( ! [X2] : (k1_xboole_0 != k2_xboole_0(k1_relat_1(sK2),X2)) )),
% 1.50/0.55    inference(superposition,[],[f90,f131])).
% 1.50/0.55  fof(f90,plain,(
% 1.50/0.55    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) )),
% 1.50/0.55    inference(definition_unfolding,[],[f57,f87])).
% 1.50/0.55  fof(f57,plain,(
% 1.50/0.55    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 1.50/0.55    inference(cnf_transformation,[],[f6])).
% 1.50/0.55  fof(f6,axiom,(
% 1.50/0.55    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 1.50/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 1.50/0.55  % SZS output end Proof for theBenchmark
% 1.50/0.55  % (21803)------------------------------
% 1.50/0.55  % (21803)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.55  % (21803)Termination reason: Refutation
% 1.50/0.55  
% 1.50/0.55  % (21803)Memory used [KB]: 1791
% 1.50/0.55  % (21803)Time elapsed: 0.146 s
% 1.50/0.55  % (21803)------------------------------
% 1.50/0.55  % (21803)------------------------------
% 1.50/0.56  % (21801)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.50/0.56  % (21795)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.62/0.57  % (21808)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.62/0.57  % (21781)Success in time 0.214 s
%------------------------------------------------------------------------------
