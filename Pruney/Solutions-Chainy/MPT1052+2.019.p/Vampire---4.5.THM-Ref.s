%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:05 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  119 (2219 expanded)
%              Number of leaves         :   19 ( 489 expanded)
%              Depth                    :   31
%              Number of atoms          :  318 (8187 expanded)
%              Number of equality atoms :  129 (2394 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f634,plain,(
    $false ),
    inference(subsumption_resolution,[],[f633,f257])).

% (14938)Termination reason: Refutation not found, incomplete strategy
fof(f257,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f219,f82])).

fof(f82,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f45])).

% (14938)Memory used [KB]: 10746
fof(f45,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f219,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f96,f215])).

fof(f215,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f214,f164])).

fof(f164,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f161])).

fof(f161,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f160,f123])).

fof(f123,plain,
    ( sK0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f122,f96])).

fof(f122,plain,
    ( sK0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f119,f95])).

fof(f95,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(resolution,[],[f51,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1) )
      | ~ r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
     => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1) ) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
     => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_2)).

fof(f51,plain,(
    r2_hidden(sK2,k1_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( ( ~ r1_tarski(k2_relat_1(sK2),sK1)
      | sK0 != k1_relat_1(sK2) )
    & r2_hidden(sK2,k1_funct_2(sK0,sK1))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f37])).

% (14938)Time elapsed: 0.131 s
fof(f37,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_tarski(k2_relat_1(X2),X1)
          | k1_relat_1(X2) != X0 )
        & r2_hidden(X2,k1_funct_2(X0,X1))
        & v1_relat_1(X2) )
   => ( ( ~ r1_tarski(k2_relat_1(sK2),sK1)
        | sK0 != k1_relat_1(sK2) )
      & r2_hidden(sK2,k1_funct_2(sK0,sK1))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

% (14938)------------------------------
% (14938)------------------------------
fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_tarski(k2_relat_1(X2),X1)
        | k1_relat_1(X2) != X0 )
      & r2_hidden(X2,k1_funct_2(X0,X1))
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_tarski(k2_relat_1(X2),X1)
        | k1_relat_1(X2) != X0 )
      & r2_hidden(X2,k1_funct_2(X0,X1))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r2_hidden(X2,k1_funct_2(X0,X1))
         => ( r1_tarski(k2_relat_1(X2),X1)
            & k1_relat_1(X2) = X0 ) ) ) ),
    inference(pure_predicate_removal,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(X2,k1_funct_2(X0,X1))
         => ( r1_tarski(k2_relat_1(X2),X1)
            & k1_relat_1(X2) = X0 ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X2,k1_funct_2(X0,X1))
       => ( r1_tarski(k2_relat_1(X2),X1)
          & k1_relat_1(X2) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_funct_2)).

fof(f119,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f105,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
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
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f34,plain,(
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

fof(f105,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f96,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f160,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f159,f50])).

fof(f50,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f159,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 != k1_relat_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f158,f53])).

fof(f53,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f158,plain,
    ( ~ r1_tarski(k1_xboole_0,sK1)
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_relat_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f153,f66])).

fof(f66,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

fof(f153,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK1)
    | k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f151])).

fof(f151,plain,
    ( sK0 != sK0
    | ~ r1_tarski(k2_relat_1(sK2),sK1)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f52,f123])).

fof(f52,plain,
    ( sK0 != k1_relat_1(sK2)
    | ~ r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f214,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f212,f157])).

fof(f157,plain,
    ( k1_xboole_0 = sK1
    | ~ m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f153,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
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

fof(f212,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f131,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
        & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( ~ ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
            & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).

fof(f131,plain,(
    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(k2_relat_1(k2_zfmisc_1(sK0,sK1)))) ),
    inference(resolution,[],[f115,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f115,plain,(
    r1_tarski(k2_relat_1(sK2),k2_relat_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f114,f50])).

fof(f114,plain,
    ( r1_tarski(k2_relat_1(sK2),k2_relat_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f111,f63])).

fof(f63,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f111,plain,
    ( r1_tarski(k2_relat_1(sK2),k2_relat_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f108,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(f108,plain,(
    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f96,f73])).

fof(f96,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f51,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f633,plain,(
    ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f632,f82])).

fof(f632,plain,(
    ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(subsumption_resolution,[],[f631,f577])).

fof(f577,plain,(
    k1_xboole_0 != k1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f506,f262])).

fof(f262,plain,(
    r1_tarski(k2_relat_1(sK2),k1_xboole_0) ),
    inference(forward_demodulation,[],[f261,f57])).

fof(f57,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f261,plain,(
    r1_tarski(k2_relat_1(sK2),k2_relat_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f230,f82])).

fof(f230,plain,(
    r1_tarski(k2_relat_1(sK2),k2_relat_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f115,f215])).

fof(f506,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | ~ r1_tarski(k2_relat_1(sK2),k1_xboole_0) ),
    inference(backward_demodulation,[],[f217,f501])).

fof(f501,plain,(
    k1_xboole_0 = sK0 ),
    inference(resolution,[],[f499,f72])).

fof(f72,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f499,plain,(
    v1_xboole_0(sK0) ),
    inference(backward_demodulation,[],[f71,f498])).

fof(f498,plain,(
    sK0 = sK4 ),
    inference(resolution,[],[f492,f71])).

fof(f492,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | sK0 = X0 ) ),
    inference(duplicate_literal_removal,[],[f486])).

fof(f486,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | sK0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f242,f72])).

fof(f242,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = sK0 ),
    inference(backward_demodulation,[],[f148,f215])).

fof(f148,plain,
    ( ~ v1_xboole_0(sK1)
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f116,f58])).

fof(f58,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f40,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
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

fof(f116,plain,
    ( r2_hidden(sK3(sK1),sK1)
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f104,f72])).

fof(f104,plain,
    ( v1_xboole_0(sK0)
    | r2_hidden(sK3(sK1),sK1) ),
    inference(resolution,[],[f100,f59])).

fof(f59,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK3(X0),X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f100,plain,
    ( ~ v1_xboole_0(sK1)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f97,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k1_funct_2(X0,X1))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k1_funct_2(X0,X1))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k1_funct_2(X0,X1))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => v1_xboole_0(k1_funct_2(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_2)).

fof(f97,plain,(
    ~ v1_xboole_0(k1_funct_2(sK0,sK1)) ),
    inference(resolution,[],[f51,f58])).

fof(f71,plain,(
    v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    v1_xboole_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f3,f46])).

fof(f46,plain,
    ( ? [X0] : v1_xboole_0(X0)
   => v1_xboole_0(sK4) ),
    introduced(choice_axiom,[])).

fof(f3,axiom,(
    ? [X0] : v1_xboole_0(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).

fof(f217,plain,
    ( sK0 != k1_relat_1(sK2)
    | ~ r1_tarski(k2_relat_1(sK2),k1_xboole_0) ),
    inference(backward_demodulation,[],[f52,f215])).

fof(f631,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(forward_demodulation,[],[f616,f514])).

fof(f514,plain,(
    k1_relat_1(sK2) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) ),
    inference(backward_demodulation,[],[f227,f501])).

fof(f227,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,k1_xboole_0,sK2) ),
    inference(backward_demodulation,[],[f105,f215])).

fof(f616,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(resolution,[],[f507,f88])).

fof(f88,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f507,plain,(
    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f218,f501])).

fof(f218,plain,(
    v1_funct_2(sK2,sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f95,f215])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n013.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:00:24 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (14936)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (14930)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.52  % (14931)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.52  % (14933)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.52  % (14957)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.53  % (14944)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.53  % (14956)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.53  % (14958)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.53  % (14940)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.53  % (14948)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.53  % (14932)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (14934)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (14940)Refutation not found, incomplete strategy% (14940)------------------------------
% 0.22/0.54  % (14940)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (14940)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (14940)Memory used [KB]: 10618
% 0.22/0.54  % (14940)Time elapsed: 0.101 s
% 0.22/0.54  % (14940)------------------------------
% 0.22/0.54  % (14940)------------------------------
% 0.22/0.54  % (14942)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (14937)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.54  % (14939)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.54  % (14932)Refutation not found, incomplete strategy% (14932)------------------------------
% 0.22/0.54  % (14932)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (14932)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (14932)Memory used [KB]: 10746
% 0.22/0.54  % (14932)Time elapsed: 0.104 s
% 0.22/0.54  % (14932)------------------------------
% 0.22/0.54  % (14932)------------------------------
% 0.22/0.54  % (14950)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.55  % (14935)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.55  % (14938)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.55  % (14950)Refutation not found, incomplete strategy% (14950)------------------------------
% 0.22/0.55  % (14950)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (14950)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (14950)Memory used [KB]: 10746
% 0.22/0.55  % (14950)Time elapsed: 0.140 s
% 0.22/0.55  % (14950)------------------------------
% 0.22/0.55  % (14950)------------------------------
% 0.22/0.55  % (14945)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.55  % (14946)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.55  % (14947)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.55  % (14938)Refutation not found, incomplete strategy% (14938)------------------------------
% 0.22/0.55  % (14938)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (14959)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.55  % (14943)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.56  % (14930)Refutation found. Thanks to Tanya!
% 0.22/0.56  % SZS status Theorem for theBenchmark
% 0.22/0.56  % SZS output start Proof for theBenchmark
% 0.22/0.56  fof(f634,plain,(
% 0.22/0.56    $false),
% 0.22/0.56    inference(subsumption_resolution,[],[f633,f257])).
% 0.22/0.56  % (14938)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  fof(f257,plain,(
% 0.22/0.56    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.56    inference(forward_demodulation,[],[f219,f82])).
% 0.22/0.56  
% 0.22/0.56  fof(f82,plain,(
% 0.22/0.56    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.22/0.56    inference(equality_resolution,[],[f70])).
% 0.22/0.56  fof(f70,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.22/0.56    inference(cnf_transformation,[],[f45])).
% 0.22/0.56  % (14938)Memory used [KB]: 10746
% 0.22/0.56  fof(f45,plain,(
% 0.22/0.56    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.22/0.56    inference(flattening,[],[f44])).
% 0.22/0.56  fof(f44,plain,(
% 0.22/0.56    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.22/0.56    inference(nnf_transformation,[],[f8])).
% 0.22/0.56  fof(f8,axiom,(
% 0.22/0.56    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.56  fof(f219,plain,(
% 0.22/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))),
% 0.22/0.56    inference(backward_demodulation,[],[f96,f215])).
% 0.22/0.56  fof(f215,plain,(
% 0.22/0.56    k1_xboole_0 = sK1),
% 0.22/0.56    inference(subsumption_resolution,[],[f214,f164])).
% 0.22/0.56  fof(f164,plain,(
% 0.22/0.56    k1_xboole_0 != sK0 | k1_xboole_0 = sK1),
% 0.22/0.56    inference(duplicate_literal_removal,[],[f161])).
% 0.22/0.56  fof(f161,plain,(
% 0.22/0.56    k1_xboole_0 != sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK1),
% 0.22/0.56    inference(superposition,[],[f160,f123])).
% 0.22/0.56  fof(f123,plain,(
% 0.22/0.56    sK0 = k1_relat_1(sK2) | k1_xboole_0 = sK1),
% 0.22/0.56    inference(subsumption_resolution,[],[f122,f96])).
% 0.22/0.56  fof(f122,plain,(
% 0.22/0.56    sK0 = k1_relat_1(sK2) | k1_xboole_0 = sK1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.56    inference(subsumption_resolution,[],[f119,f95])).
% 0.22/0.56  fof(f95,plain,(
% 0.22/0.56    v1_funct_2(sK2,sK0,sK1)),
% 0.22/0.56    inference(resolution,[],[f51,f61])).
% 0.22/0.56  fof(f61,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~r2_hidden(X2,k1_funct_2(X0,X1))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f29])).
% 0.22/0.56  fof(f29,plain,(
% 0.22/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1)) | ~r2_hidden(X2,k1_funct_2(X0,X1)))),
% 0.22/0.56    inference(ennf_transformation,[],[f23])).
% 0.22/0.56  fof(f23,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1)))),
% 0.22/0.56    inference(pure_predicate_removal,[],[f18])).
% 0.22/0.56  fof(f18,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_2)).
% 0.22/0.56  fof(f51,plain,(
% 0.22/0.56    r2_hidden(sK2,k1_funct_2(sK0,sK1))),
% 0.22/0.56    inference(cnf_transformation,[],[f38])).
% 0.22/0.56  fof(f38,plain,(
% 0.22/0.56    (~r1_tarski(k2_relat_1(sK2),sK1) | sK0 != k1_relat_1(sK2)) & r2_hidden(sK2,k1_funct_2(sK0,sK1)) & v1_relat_1(sK2)),
% 0.22/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f37])).
% 0.22/0.56  % (14938)Time elapsed: 0.131 s
% 0.22/0.56  fof(f37,plain,(
% 0.22/0.56    ? [X0,X1,X2] : ((~r1_tarski(k2_relat_1(X2),X1) | k1_relat_1(X2) != X0) & r2_hidden(X2,k1_funct_2(X0,X1)) & v1_relat_1(X2)) => ((~r1_tarski(k2_relat_1(sK2),sK1) | sK0 != k1_relat_1(sK2)) & r2_hidden(sK2,k1_funct_2(sK0,sK1)) & v1_relat_1(sK2))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  % (14938)------------------------------
% 0.22/0.56  % (14938)------------------------------
% 0.22/0.56  fof(f25,plain,(
% 0.22/0.56    ? [X0,X1,X2] : ((~r1_tarski(k2_relat_1(X2),X1) | k1_relat_1(X2) != X0) & r2_hidden(X2,k1_funct_2(X0,X1)) & v1_relat_1(X2))),
% 0.22/0.56    inference(flattening,[],[f24])).
% 0.22/0.56  fof(f24,plain,(
% 0.22/0.56    ? [X0,X1,X2] : (((~r1_tarski(k2_relat_1(X2),X1) | k1_relat_1(X2) != X0) & r2_hidden(X2,k1_funct_2(X0,X1))) & v1_relat_1(X2))),
% 0.22/0.56    inference(ennf_transformation,[],[f22])).
% 0.22/0.56  fof(f22,plain,(
% 0.22/0.56    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X2,k1_funct_2(X0,X1)) => (r1_tarski(k2_relat_1(X2),X1) & k1_relat_1(X2) = X0)))),
% 0.22/0.56    inference(pure_predicate_removal,[],[f21])).
% 0.22/0.56  fof(f21,negated_conjecture,(
% 0.22/0.56    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X2,k1_funct_2(X0,X1)) => (r1_tarski(k2_relat_1(X2),X1) & k1_relat_1(X2) = X0)))),
% 0.22/0.56    inference(negated_conjecture,[],[f20])).
% 0.22/0.56  fof(f20,conjecture,(
% 0.22/0.56    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X2,k1_funct_2(X0,X1)) => (r1_tarski(k2_relat_1(X2),X1) & k1_relat_1(X2) = X0)))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_funct_2)).
% 0.22/0.56  fof(f119,plain,(
% 0.22/0.56    sK0 = k1_relat_1(sK2) | ~v1_funct_2(sK2,sK0,sK1) | k1_xboole_0 = sK1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.56    inference(superposition,[],[f105,f75])).
% 0.22/0.56  fof(f75,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f49])).
% 0.22/0.56  fof(f49,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.56    inference(nnf_transformation,[],[f35])).
% 0.22/0.56  fof(f35,plain,(
% 0.22/0.56    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.56    inference(flattening,[],[f34])).
% 0.22/0.56  fof(f34,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.56    inference(ennf_transformation,[],[f16])).
% 0.22/0.56  fof(f16,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.56  fof(f105,plain,(
% 0.22/0.56    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)),
% 0.22/0.56    inference(resolution,[],[f96,f81])).
% 0.22/0.56  fof(f81,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f36])).
% 0.22/0.56  fof(f36,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.56    inference(ennf_transformation,[],[f15])).
% 0.22/0.56  fof(f15,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.56  fof(f160,plain,(
% 0.22/0.56    k1_xboole_0 != k1_relat_1(sK2) | k1_xboole_0 = sK1),
% 0.22/0.56    inference(subsumption_resolution,[],[f159,f50])).
% 0.22/0.56  fof(f50,plain,(
% 0.22/0.56    v1_relat_1(sK2)),
% 0.22/0.56    inference(cnf_transformation,[],[f38])).
% 0.22/0.56  fof(f159,plain,(
% 0.22/0.56    k1_xboole_0 = sK1 | k1_xboole_0 != k1_relat_1(sK2) | ~v1_relat_1(sK2)),
% 0.22/0.56    inference(subsumption_resolution,[],[f158,f53])).
% 0.22/0.56  fof(f53,plain,(
% 0.22/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f6])).
% 0.22/0.56  fof(f6,axiom,(
% 0.22/0.56    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.56  fof(f158,plain,(
% 0.22/0.56    ~r1_tarski(k1_xboole_0,sK1) | k1_xboole_0 = sK1 | k1_xboole_0 != k1_relat_1(sK2) | ~v1_relat_1(sK2)),
% 0.22/0.56    inference(superposition,[],[f153,f66])).
% 0.22/0.56  fof(f66,plain,(
% 0.22/0.56    ( ! [X0] : (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f43])).
% 0.22/0.56  fof(f43,plain,(
% 0.22/0.56    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.56    inference(nnf_transformation,[],[f32])).
% 0.22/0.56  fof(f32,plain,(
% 0.22/0.56    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f14])).
% 0.22/0.56  fof(f14,axiom,(
% 0.22/0.56    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).
% 0.22/0.56  fof(f153,plain,(
% 0.22/0.56    ~r1_tarski(k2_relat_1(sK2),sK1) | k1_xboole_0 = sK1),
% 0.22/0.56    inference(trivial_inequality_removal,[],[f151])).
% 0.22/0.56  fof(f151,plain,(
% 0.22/0.56    sK0 != sK0 | ~r1_tarski(k2_relat_1(sK2),sK1) | k1_xboole_0 = sK1),
% 0.22/0.56    inference(superposition,[],[f52,f123])).
% 0.22/0.56  fof(f52,plain,(
% 0.22/0.56    sK0 != k1_relat_1(sK2) | ~r1_tarski(k2_relat_1(sK2),sK1)),
% 0.22/0.56    inference(cnf_transformation,[],[f38])).
% 0.22/0.56  fof(f214,plain,(
% 0.22/0.56    k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.22/0.56    inference(subsumption_resolution,[],[f212,f157])).
% 0.22/0.56  fof(f157,plain,(
% 0.22/0.56    k1_xboole_0 = sK1 | ~m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))),
% 0.22/0.56    inference(resolution,[],[f153,f73])).
% 0.22/0.56  fof(f73,plain,(
% 0.22/0.56    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f48])).
% 0.22/0.56  fof(f48,plain,(
% 0.22/0.56    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.56    inference(nnf_transformation,[],[f9])).
% 0.22/0.56  fof(f9,axiom,(
% 0.22/0.56    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.56  fof(f212,plain,(
% 0.22/0.56    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.22/0.56    inference(superposition,[],[f131,f55])).
% 0.22/0.56  fof(f55,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.22/0.56    inference(cnf_transformation,[],[f26])).
% 0.22/0.56  fof(f26,plain,(
% 0.22/0.56    ! [X0,X1] : ((k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.22/0.56    inference(ennf_transformation,[],[f11])).
% 0.22/0.56  fof(f11,axiom,(
% 0.22/0.56    ! [X0,X1] : ~(~(k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).
% 0.22/0.56  fof(f131,plain,(
% 0.22/0.56    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(k2_relat_1(k2_zfmisc_1(sK0,sK1))))),
% 0.22/0.56    inference(resolution,[],[f115,f74])).
% 0.22/0.56  fof(f74,plain,(
% 0.22/0.56    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f48])).
% 0.22/0.56  fof(f115,plain,(
% 0.22/0.56    r1_tarski(k2_relat_1(sK2),k2_relat_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.56    inference(subsumption_resolution,[],[f114,f50])).
% 0.22/0.56  fof(f114,plain,(
% 0.22/0.56    r1_tarski(k2_relat_1(sK2),k2_relat_1(k2_zfmisc_1(sK0,sK1))) | ~v1_relat_1(sK2)),
% 0.22/0.56    inference(subsumption_resolution,[],[f111,f63])).
% 0.22/0.56  fof(f63,plain,(
% 0.22/0.56    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f10])).
% 0.22/0.56  fof(f10,axiom,(
% 0.22/0.56    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.56  fof(f111,plain,(
% 0.22/0.56    r1_tarski(k2_relat_1(sK2),k2_relat_1(k2_zfmisc_1(sK0,sK1))) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | ~v1_relat_1(sK2)),
% 0.22/0.56    inference(resolution,[],[f108,f65])).
% 0.22/0.56  fof(f65,plain,(
% 0.22/0.56    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f31])).
% 0.22/0.56  fof(f31,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.56    inference(flattening,[],[f30])).
% 0.22/0.56  fof(f30,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f12])).
% 0.22/0.56  fof(f12,axiom,(
% 0.22/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).
% 0.22/0.56  fof(f108,plain,(
% 0.22/0.56    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))),
% 0.22/0.56    inference(resolution,[],[f96,f73])).
% 0.22/0.56  fof(f96,plain,(
% 0.22/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.56    inference(resolution,[],[f51,f62])).
% 0.22/0.56  fof(f62,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X2,k1_funct_2(X0,X1))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f29])).
% 0.22/0.56  fof(f633,plain,(
% 0.22/0.56    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.56    inference(forward_demodulation,[],[f632,f82])).
% 0.22/0.56  fof(f632,plain,(
% 0.22/0.56    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.22/0.56    inference(subsumption_resolution,[],[f631,f577])).
% 0.22/0.56  fof(f577,plain,(
% 0.22/0.56    k1_xboole_0 != k1_relat_1(sK2)),
% 0.22/0.56    inference(subsumption_resolution,[],[f506,f262])).
% 0.22/0.56  fof(f262,plain,(
% 0.22/0.56    r1_tarski(k2_relat_1(sK2),k1_xboole_0)),
% 0.22/0.56    inference(forward_demodulation,[],[f261,f57])).
% 0.22/0.56  fof(f57,plain,(
% 0.22/0.56    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.22/0.56    inference(cnf_transformation,[],[f13])).
% 0.22/0.56  fof(f13,axiom,(
% 0.22/0.56    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.22/0.56  fof(f261,plain,(
% 0.22/0.56    r1_tarski(k2_relat_1(sK2),k2_relat_1(k1_xboole_0))),
% 0.22/0.56    inference(forward_demodulation,[],[f230,f82])).
% 0.22/0.56  fof(f230,plain,(
% 0.22/0.56    r1_tarski(k2_relat_1(sK2),k2_relat_1(k2_zfmisc_1(sK0,k1_xboole_0)))),
% 0.22/0.56    inference(backward_demodulation,[],[f115,f215])).
% 0.22/0.56  fof(f506,plain,(
% 0.22/0.56    k1_xboole_0 != k1_relat_1(sK2) | ~r1_tarski(k2_relat_1(sK2),k1_xboole_0)),
% 0.22/0.56    inference(backward_demodulation,[],[f217,f501])).
% 0.22/0.56  fof(f501,plain,(
% 0.22/0.56    k1_xboole_0 = sK0),
% 0.22/0.56    inference(resolution,[],[f499,f72])).
% 0.22/0.56  fof(f72,plain,(
% 0.22/0.56    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f33])).
% 0.22/0.56  fof(f33,plain,(
% 0.22/0.56    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f2])).
% 0.22/0.56  fof(f2,axiom,(
% 0.22/0.56    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.22/0.56  fof(f499,plain,(
% 0.22/0.56    v1_xboole_0(sK0)),
% 0.22/0.56    inference(backward_demodulation,[],[f71,f498])).
% 0.22/0.56  fof(f498,plain,(
% 0.22/0.56    sK0 = sK4),
% 0.22/0.56    inference(resolution,[],[f492,f71])).
% 0.22/0.56  fof(f492,plain,(
% 0.22/0.56    ( ! [X0] : (~v1_xboole_0(X0) | sK0 = X0) )),
% 0.22/0.56    inference(duplicate_literal_removal,[],[f486])).
% 0.22/0.56  fof(f486,plain,(
% 0.22/0.56    ( ! [X0] : (~v1_xboole_0(X0) | sK0 = X0 | ~v1_xboole_0(X0)) )),
% 0.22/0.56    inference(superposition,[],[f242,f72])).
% 0.22/0.56  fof(f242,plain,(
% 0.22/0.56    ~v1_xboole_0(k1_xboole_0) | k1_xboole_0 = sK0),
% 0.22/0.56    inference(backward_demodulation,[],[f148,f215])).
% 0.22/0.56  fof(f148,plain,(
% 0.22/0.56    ~v1_xboole_0(sK1) | k1_xboole_0 = sK0),
% 0.22/0.56    inference(resolution,[],[f116,f58])).
% 0.22/0.56  fof(f58,plain,(
% 0.22/0.56    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f42])).
% 0.22/0.56  fof(f42,plain,(
% 0.22/0.56    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f40,f41])).
% 0.22/0.56  fof(f41,plain,(
% 0.22/0.56    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f40,plain,(
% 0.22/0.56    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.56    inference(rectify,[],[f39])).
% 0.22/0.56  fof(f39,plain,(
% 0.22/0.56    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.56    inference(nnf_transformation,[],[f1])).
% 0.22/0.56  fof(f1,axiom,(
% 0.22/0.56    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.22/0.56  fof(f116,plain,(
% 0.22/0.56    r2_hidden(sK3(sK1),sK1) | k1_xboole_0 = sK0),
% 0.22/0.56    inference(resolution,[],[f104,f72])).
% 0.22/0.56  fof(f104,plain,(
% 0.22/0.56    v1_xboole_0(sK0) | r2_hidden(sK3(sK1),sK1)),
% 0.22/0.56    inference(resolution,[],[f100,f59])).
% 0.22/0.56  fof(f59,plain,(
% 0.22/0.56    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f42])).
% 0.22/0.56  fof(f100,plain,(
% 0.22/0.56    ~v1_xboole_0(sK1) | v1_xboole_0(sK0)),
% 0.22/0.56    inference(resolution,[],[f97,f60])).
% 0.22/0.56  fof(f60,plain,(
% 0.22/0.56    ( ! [X0,X1] : (v1_xboole_0(k1_funct_2(X0,X1)) | ~v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f28])).
% 0.22/0.56  fof(f28,plain,(
% 0.22/0.56    ! [X0,X1] : (v1_xboole_0(k1_funct_2(X0,X1)) | ~v1_xboole_0(X1) | v1_xboole_0(X0))),
% 0.22/0.56    inference(flattening,[],[f27])).
% 0.22/0.56  fof(f27,plain,(
% 0.22/0.56    ! [X0,X1] : (v1_xboole_0(k1_funct_2(X0,X1)) | (~v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f17])).
% 0.22/0.56  fof(f17,axiom,(
% 0.22/0.56    ! [X0,X1] : ((v1_xboole_0(X1) & ~v1_xboole_0(X0)) => v1_xboole_0(k1_funct_2(X0,X1)))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_2)).
% 0.22/0.56  fof(f97,plain,(
% 0.22/0.56    ~v1_xboole_0(k1_funct_2(sK0,sK1))),
% 0.22/0.56    inference(resolution,[],[f51,f58])).
% 0.22/0.56  fof(f71,plain,(
% 0.22/0.56    v1_xboole_0(sK4)),
% 0.22/0.56    inference(cnf_transformation,[],[f47])).
% 0.22/0.56  fof(f47,plain,(
% 0.22/0.56    v1_xboole_0(sK4)),
% 0.22/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f3,f46])).
% 0.22/0.56  fof(f46,plain,(
% 0.22/0.56    ? [X0] : v1_xboole_0(X0) => v1_xboole_0(sK4)),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f3,axiom,(
% 0.22/0.56    ? [X0] : v1_xboole_0(X0)),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).
% 0.22/0.56  fof(f217,plain,(
% 0.22/0.56    sK0 != k1_relat_1(sK2) | ~r1_tarski(k2_relat_1(sK2),k1_xboole_0)),
% 0.22/0.56    inference(backward_demodulation,[],[f52,f215])).
% 0.22/0.56  fof(f631,plain,(
% 0.22/0.56    k1_xboole_0 = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.22/0.56    inference(forward_demodulation,[],[f616,f514])).
% 0.22/0.56  fof(f514,plain,(
% 0.22/0.56    k1_relat_1(sK2) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)),
% 0.22/0.56    inference(backward_demodulation,[],[f227,f501])).
% 0.22/0.56  fof(f227,plain,(
% 0.22/0.56    k1_relat_1(sK2) = k1_relset_1(sK0,k1_xboole_0,sK2)),
% 0.22/0.56    inference(backward_demodulation,[],[f105,f215])).
% 0.22/0.56  fof(f616,plain,(
% 0.22/0.56    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.22/0.56    inference(resolution,[],[f507,f88])).
% 0.22/0.56  fof(f88,plain,(
% 0.22/0.56    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 0.22/0.56    inference(equality_resolution,[],[f76])).
% 0.22/0.56  fof(f76,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f49])).
% 0.22/0.56  fof(f507,plain,(
% 0.22/0.56    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)),
% 0.22/0.56    inference(backward_demodulation,[],[f218,f501])).
% 0.22/0.56  fof(f218,plain,(
% 0.22/0.56    v1_funct_2(sK2,sK0,k1_xboole_0)),
% 0.22/0.56    inference(backward_demodulation,[],[f95,f215])).
% 0.22/0.56  % SZS output end Proof for theBenchmark
% 0.22/0.56  % (14930)------------------------------
% 0.22/0.56  % (14930)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (14930)Termination reason: Refutation
% 0.22/0.56  
% 0.22/0.56  % (14930)Memory used [KB]: 1918
% 0.22/0.56  % (14930)Time elapsed: 0.143 s
% 0.22/0.56  % (14930)------------------------------
% 0.22/0.56  % (14930)------------------------------
% 0.22/0.56  % (14953)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.56  % (14929)Success in time 0.189 s
%------------------------------------------------------------------------------
