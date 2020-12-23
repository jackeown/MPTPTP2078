%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:04 EST 2020

% Result     : Theorem 1.39s
% Output     : Refutation 1.39s
% Verified   : 
% Statistics : Number of formulae       :   91 (1492 expanded)
%              Number of leaves         :   16 ( 342 expanded)
%              Depth                    :   31
%              Number of atoms          :  230 (4949 expanded)
%              Number of equality atoms :  101 (1592 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f547,plain,(
    $false ),
    inference(subsumption_resolution,[],[f536,f523])).

fof(f523,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(unit_resulting_resolution,[],[f436,f50])).

fof(f50,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f436,plain,(
    k1_xboole_0 != sK0 ),
    inference(subsumption_resolution,[],[f435,f42])).

fof(f42,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f435,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != sK0 ),
    inference(forward_demodulation,[],[f434,f46])).

fof(f46,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f434,plain,
    ( ~ r1_tarski(k2_relat_1(k1_xboole_0),k1_xboole_0)
    | k1_xboole_0 != sK0 ),
    inference(forward_demodulation,[],[f433,f417])).

fof(f417,plain,(
    k1_xboole_0 = sK2 ),
    inference(forward_demodulation,[],[f416,f68])).

fof(f68,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f416,plain,(
    sK2 = k2_zfmisc_1(sK0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f415,f382])).

fof(f382,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f381,f284])).

fof(f284,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f281,f245])).

fof(f245,plain,
    ( sK0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f241,f121])).

fof(f121,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f34,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
     => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_2)).

fof(f34,plain,(
    r2_hidden(sK2,k1_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_tarski(k2_relat_1(X2),X1)
        | k1_relat_1(X2) != X0 )
      & r2_hidden(X2,k1_funct_2(X0,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_tarski(k2_relat_1(X2),X1)
        | k1_relat_1(X2) != X0 )
      & r2_hidden(X2,k1_funct_2(X0,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(X2,k1_funct_2(X0,X1))
         => ( r1_tarski(k2_relat_1(X2),X1)
            & k1_relat_1(X2) = X0 ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X2,k1_funct_2(X0,X1))
       => ( r1_tarski(k2_relat_1(X2),X1)
          & k1_relat_1(X2) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_funct_2)).

fof(f241,plain,
    ( k1_xboole_0 = sK1
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | sK0 = k1_relat_1(sK2) ),
    inference(resolution,[],[f191,f115])).

fof(f115,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f34,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f191,plain,(
    ! [X4,X5,X3] :
      ( ~ v1_funct_2(X5,X3,X4)
      | k1_xboole_0 = X4
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | k1_relat_1(X5) = X3 ) ),
    inference(duplicate_literal_removal,[],[f186])).

fof(f186,plain,(
    ! [X4,X5,X3] :
      ( k1_relat_1(X5) = X3
      | k1_xboole_0 = X4
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_2(X5,X3,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(superposition,[],[f64,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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

fof(f281,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | sK0 != k1_relat_1(sK2) ),
    inference(resolution,[],[f169,f31])).

fof(f31,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK1)
    | sK0 != k1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f169,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f146,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
        & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( ~ ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
            & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).

fof(f146,plain,(
    r1_tarski(k2_relat_1(sK2),k2_relat_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f32,f125,f58,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,X1)
      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(f58,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f125,plain,(
    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f121,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f32,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f381,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 = sK1 ),
    inference(forward_demodulation,[],[f380,f45])).

fof(f45,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f380,plain,
    ( k1_relat_1(k1_xboole_0) != sK0
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f379,f42])).

fof(f379,plain,
    ( ~ r1_tarski(k1_xboole_0,sK1)
    | k1_relat_1(k1_xboole_0) != sK0
    | k1_xboole_0 = sK1 ),
    inference(forward_demodulation,[],[f356,f46])).

fof(f356,plain,
    ( ~ r1_tarski(k2_relat_1(k1_xboole_0),sK1)
    | k1_relat_1(k1_xboole_0) != sK0
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f31,f324])).

fof(f324,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(forward_demodulation,[],[f323,f69])).

fof(f69,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f323,plain,
    ( sK2 = k2_zfmisc_1(k1_xboole_0,sK1)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f322,f42])).

fof(f322,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | sK2 = k2_zfmisc_1(k1_xboole_0,sK1)
    | k1_xboole_0 = sK1 ),
    inference(forward_demodulation,[],[f306,f69])).

fof(f306,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_xboole_0,sK1),sK2)
    | sK2 = k2_zfmisc_1(k1_xboole_0,sK1)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f143,f284])).

fof(f143,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),sK2)
    | sK2 = k2_zfmisc_1(sK0,sK1) ),
    inference(resolution,[],[f125,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f415,plain,(
    sK2 = k2_zfmisc_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f414,f42])).

fof(f414,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | sK2 = k2_zfmisc_1(sK0,sK1) ),
    inference(forward_demodulation,[],[f392,f68])).

fof(f392,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,k1_xboole_0),sK2)
    | sK2 = k2_zfmisc_1(sK0,sK1) ),
    inference(backward_demodulation,[],[f143,f382])).

fof(f433,plain,
    ( k1_xboole_0 != sK0
    | ~ r1_tarski(k2_relat_1(sK2),k1_xboole_0) ),
    inference(forward_demodulation,[],[f422,f45])).

fof(f422,plain,
    ( k1_relat_1(k1_xboole_0) != sK0
    | ~ r1_tarski(k2_relat_1(sK2),k1_xboole_0) ),
    inference(backward_demodulation,[],[f383,f417])).

fof(f383,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),k1_xboole_0)
    | sK0 != k1_relat_1(sK2) ),
    inference(backward_demodulation,[],[f31,f382])).

fof(f536,plain,(
    v1_xboole_0(sK0) ),
    inference(unit_resulting_resolution,[],[f423,f198])).

fof(f198,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,k1_funct_2(X2,k1_xboole_0))
      | v1_xboole_0(X2) ) ),
    inference(resolution,[],[f96,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f96,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_funct_2(X0,k1_xboole_0))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f57,f65])).

fof(f65,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | v1_xboole_0(X0)
      | v1_xboole_0(k1_funct_2(X0,X1)) ) ),
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => v1_xboole_0(k1_funct_2(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_2)).

fof(f423,plain,(
    r2_hidden(k1_xboole_0,k1_funct_2(sK0,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f384,f417])).

fof(f384,plain,(
    r2_hidden(sK2,k1_funct_2(sK0,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f34,f382])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:58:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (31765)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.52  % (31780)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.52  % (31769)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.52  % (31773)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.24/0.53  % (31784)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.24/0.54  % (31764)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.24/0.54  % (31771)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.24/0.54  % (31762)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.24/0.54  % (31776)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.24/0.54  % (31768)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.24/0.54  % (31763)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.39/0.54  % (31780)Refutation found. Thanks to Tanya!
% 1.39/0.54  % SZS status Theorem for theBenchmark
% 1.39/0.55  % (31786)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.39/0.55  % (31778)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.39/0.55  % (31781)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.39/0.55  % (31779)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.39/0.55  % (31779)Refutation not found, incomplete strategy% (31779)------------------------------
% 1.39/0.55  % (31779)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.55  % (31779)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.55  
% 1.39/0.55  % (31779)Memory used [KB]: 1663
% 1.39/0.55  % (31779)Time elapsed: 0.135 s
% 1.39/0.55  % (31779)------------------------------
% 1.39/0.55  % (31779)------------------------------
% 1.39/0.55  % SZS output start Proof for theBenchmark
% 1.39/0.55  fof(f547,plain,(
% 1.39/0.55    $false),
% 1.39/0.55    inference(subsumption_resolution,[],[f536,f523])).
% 1.39/0.55  fof(f523,plain,(
% 1.39/0.55    ~v1_xboole_0(sK0)),
% 1.39/0.55    inference(unit_resulting_resolution,[],[f436,f50])).
% 1.39/0.55  fof(f50,plain,(
% 1.39/0.55    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.39/0.55    inference(cnf_transformation,[],[f24])).
% 1.39/0.55  fof(f24,plain,(
% 1.39/0.55    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.39/0.55    inference(ennf_transformation,[],[f3])).
% 1.39/0.55  fof(f3,axiom,(
% 1.39/0.55    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.39/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.39/0.55  fof(f436,plain,(
% 1.39/0.55    k1_xboole_0 != sK0),
% 1.39/0.55    inference(subsumption_resolution,[],[f435,f42])).
% 1.39/0.55  fof(f42,plain,(
% 1.39/0.55    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f5])).
% 1.39/0.55  fof(f5,axiom,(
% 1.39/0.55    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.39/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.39/0.55  fof(f435,plain,(
% 1.39/0.55    ~r1_tarski(k1_xboole_0,k1_xboole_0) | k1_xboole_0 != sK0),
% 1.39/0.55    inference(forward_demodulation,[],[f434,f46])).
% 1.39/0.55  fof(f46,plain,(
% 1.39/0.55    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.39/0.55    inference(cnf_transformation,[],[f11])).
% 1.39/0.55  fof(f11,axiom,(
% 1.39/0.55    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.39/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 1.39/0.55  fof(f434,plain,(
% 1.39/0.55    ~r1_tarski(k2_relat_1(k1_xboole_0),k1_xboole_0) | k1_xboole_0 != sK0),
% 1.39/0.55    inference(forward_demodulation,[],[f433,f417])).
% 1.39/0.55  fof(f417,plain,(
% 1.39/0.55    k1_xboole_0 = sK2),
% 1.39/0.55    inference(forward_demodulation,[],[f416,f68])).
% 1.39/0.55  fof(f68,plain,(
% 1.39/0.55    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.39/0.55    inference(equality_resolution,[],[f49])).
% 1.39/0.55  fof(f49,plain,(
% 1.39/0.55    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f6])).
% 1.39/0.55  fof(f6,axiom,(
% 1.39/0.55    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.39/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.39/0.55  fof(f416,plain,(
% 1.39/0.55    sK2 = k2_zfmisc_1(sK0,k1_xboole_0)),
% 1.39/0.55    inference(forward_demodulation,[],[f415,f382])).
% 1.39/0.55  fof(f382,plain,(
% 1.39/0.55    k1_xboole_0 = sK1),
% 1.39/0.55    inference(subsumption_resolution,[],[f381,f284])).
% 1.39/0.55  fof(f284,plain,(
% 1.39/0.55    k1_xboole_0 = sK0 | k1_xboole_0 = sK1),
% 1.39/0.55    inference(subsumption_resolution,[],[f281,f245])).
% 1.39/0.55  fof(f245,plain,(
% 1.39/0.55    sK0 = k1_relat_1(sK2) | k1_xboole_0 = sK1),
% 1.39/0.55    inference(subsumption_resolution,[],[f241,f121])).
% 1.39/0.55  fof(f121,plain,(
% 1.39/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.39/0.55    inference(unit_resulting_resolution,[],[f34,f54])).
% 1.39/0.55  fof(f54,plain,(
% 1.39/0.55    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X2,k1_funct_2(X0,X1))) )),
% 1.39/0.55    inference(cnf_transformation,[],[f26])).
% 1.39/0.55  fof(f26,plain,(
% 1.39/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~r2_hidden(X2,k1_funct_2(X0,X1)))),
% 1.39/0.55    inference(ennf_transformation,[],[f15])).
% 1.39/0.55  fof(f15,axiom,(
% 1.39/0.55    ! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.39/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_2)).
% 1.39/0.55  fof(f34,plain,(
% 1.39/0.55    r2_hidden(sK2,k1_funct_2(sK0,sK1))),
% 1.39/0.55    inference(cnf_transformation,[],[f20])).
% 1.39/0.55  fof(f20,plain,(
% 1.39/0.55    ? [X0,X1,X2] : ((~r1_tarski(k2_relat_1(X2),X1) | k1_relat_1(X2) != X0) & r2_hidden(X2,k1_funct_2(X0,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.39/0.55    inference(flattening,[],[f19])).
% 1.39/0.55  fof(f19,plain,(
% 1.39/0.55    ? [X0,X1,X2] : (((~r1_tarski(k2_relat_1(X2),X1) | k1_relat_1(X2) != X0) & r2_hidden(X2,k1_funct_2(X0,X1))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 1.39/0.55    inference(ennf_transformation,[],[f18])).
% 1.39/0.55  fof(f18,negated_conjecture,(
% 1.39/0.55    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X2,k1_funct_2(X0,X1)) => (r1_tarski(k2_relat_1(X2),X1) & k1_relat_1(X2) = X0)))),
% 1.39/0.55    inference(negated_conjecture,[],[f17])).
% 1.39/0.55  fof(f17,conjecture,(
% 1.39/0.55    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X2,k1_funct_2(X0,X1)) => (r1_tarski(k2_relat_1(X2),X1) & k1_relat_1(X2) = X0)))),
% 1.39/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_funct_2)).
% 1.39/0.55  fof(f241,plain,(
% 1.39/0.55    k1_xboole_0 = sK1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | sK0 = k1_relat_1(sK2)),
% 1.39/0.55    inference(resolution,[],[f191,f115])).
% 1.39/0.55  fof(f115,plain,(
% 1.39/0.55    v1_funct_2(sK2,sK0,sK1)),
% 1.39/0.55    inference(unit_resulting_resolution,[],[f34,f53])).
% 1.39/0.55  fof(f53,plain,(
% 1.39/0.55    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~r2_hidden(X2,k1_funct_2(X0,X1))) )),
% 1.39/0.55    inference(cnf_transformation,[],[f26])).
% 1.39/0.55  fof(f191,plain,(
% 1.39/0.55    ( ! [X4,X5,X3] : (~v1_funct_2(X5,X3,X4) | k1_xboole_0 = X4 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | k1_relat_1(X5) = X3) )),
% 1.39/0.55    inference(duplicate_literal_removal,[],[f186])).
% 1.39/0.55  fof(f186,plain,(
% 1.39/0.55    ( ! [X4,X5,X3] : (k1_relat_1(X5) = X3 | k1_xboole_0 = X4 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_2(X5,X3,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 1.39/0.55    inference(superposition,[],[f64,f51])).
% 1.39/0.55  fof(f51,plain,(
% 1.39/0.55    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.39/0.55    inference(cnf_transformation,[],[f25])).
% 1.39/0.55  fof(f25,plain,(
% 1.39/0.55    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.39/0.55    inference(ennf_transformation,[],[f12])).
% 1.39/0.55  fof(f12,axiom,(
% 1.39/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.39/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.39/0.55  fof(f64,plain,(
% 1.39/0.55    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f30])).
% 1.39/0.55  fof(f30,plain,(
% 1.39/0.55    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.39/0.55    inference(flattening,[],[f29])).
% 1.39/0.55  fof(f29,plain,(
% 1.39/0.55    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.39/0.55    inference(ennf_transformation,[],[f13])).
% 1.39/0.55  fof(f13,axiom,(
% 1.39/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.39/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.39/0.55  fof(f281,plain,(
% 1.39/0.55    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | sK0 != k1_relat_1(sK2)),
% 1.39/0.55    inference(resolution,[],[f169,f31])).
% 1.39/0.55  fof(f31,plain,(
% 1.39/0.55    ~r1_tarski(k2_relat_1(sK2),sK1) | sK0 != k1_relat_1(sK2)),
% 1.39/0.55    inference(cnf_transformation,[],[f20])).
% 1.39/0.55  fof(f169,plain,(
% 1.39/0.55    r1_tarski(k2_relat_1(sK2),sK1) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 1.39/0.55    inference(superposition,[],[f146,f44])).
% 1.39/0.55  fof(f44,plain,(
% 1.39/0.55    ( ! [X0,X1] : (k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.39/0.55    inference(cnf_transformation,[],[f23])).
% 1.39/0.55  fof(f23,plain,(
% 1.39/0.55    ! [X0,X1] : ((k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.39/0.55    inference(ennf_transformation,[],[f9])).
% 1.39/0.55  fof(f9,axiom,(
% 1.39/0.55    ! [X0,X1] : ~(~(k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.39/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).
% 1.39/0.55  fof(f146,plain,(
% 1.39/0.55    r1_tarski(k2_relat_1(sK2),k2_relat_1(k2_zfmisc_1(sK0,sK1)))),
% 1.39/0.55    inference(unit_resulting_resolution,[],[f32,f125,f58,f41])).
% 1.39/0.55  fof(f41,plain,(
% 1.39/0.55    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~r1_tarski(X0,X1) | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))) )),
% 1.39/0.55    inference(cnf_transformation,[],[f22])).
% 1.39/0.55  fof(f22,plain,(
% 1.39/0.55    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.39/0.55    inference(flattening,[],[f21])).
% 1.39/0.55  fof(f21,plain,(
% 1.39/0.55    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.39/0.55    inference(ennf_transformation,[],[f10])).
% 1.39/0.55  fof(f10,axiom,(
% 1.39/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 1.39/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).
% 1.39/0.55  fof(f58,plain,(
% 1.39/0.55    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.39/0.55    inference(cnf_transformation,[],[f8])).
% 1.39/0.55  fof(f8,axiom,(
% 1.39/0.55    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.39/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.39/0.55  fof(f125,plain,(
% 1.39/0.55    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))),
% 1.39/0.55    inference(unit_resulting_resolution,[],[f121,f36])).
% 1.39/0.55  fof(f36,plain,(
% 1.39/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f7])).
% 1.39/0.55  fof(f7,axiom,(
% 1.39/0.55    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.39/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.39/0.55  fof(f32,plain,(
% 1.39/0.55    v1_relat_1(sK2)),
% 1.39/0.55    inference(cnf_transformation,[],[f20])).
% 1.39/0.55  fof(f381,plain,(
% 1.39/0.55    k1_xboole_0 != sK0 | k1_xboole_0 = sK1),
% 1.39/0.55    inference(forward_demodulation,[],[f380,f45])).
% 1.39/0.55  fof(f45,plain,(
% 1.39/0.55    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.39/0.55    inference(cnf_transformation,[],[f11])).
% 1.39/0.55  fof(f380,plain,(
% 1.39/0.55    k1_relat_1(k1_xboole_0) != sK0 | k1_xboole_0 = sK1),
% 1.39/0.55    inference(subsumption_resolution,[],[f379,f42])).
% 1.39/0.55  fof(f379,plain,(
% 1.39/0.55    ~r1_tarski(k1_xboole_0,sK1) | k1_relat_1(k1_xboole_0) != sK0 | k1_xboole_0 = sK1),
% 1.39/0.55    inference(forward_demodulation,[],[f356,f46])).
% 1.39/0.55  fof(f356,plain,(
% 1.39/0.55    ~r1_tarski(k2_relat_1(k1_xboole_0),sK1) | k1_relat_1(k1_xboole_0) != sK0 | k1_xboole_0 = sK1),
% 1.39/0.55    inference(superposition,[],[f31,f324])).
% 1.39/0.55  fof(f324,plain,(
% 1.39/0.55    k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 1.39/0.55    inference(forward_demodulation,[],[f323,f69])).
% 1.39/0.55  fof(f69,plain,(
% 1.39/0.55    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.39/0.55    inference(equality_resolution,[],[f48])).
% 1.39/0.55  fof(f48,plain,(
% 1.39/0.55    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f6])).
% 1.39/0.55  fof(f323,plain,(
% 1.39/0.55    sK2 = k2_zfmisc_1(k1_xboole_0,sK1) | k1_xboole_0 = sK1),
% 1.39/0.55    inference(subsumption_resolution,[],[f322,f42])).
% 1.39/0.55  fof(f322,plain,(
% 1.39/0.55    ~r1_tarski(k1_xboole_0,sK2) | sK2 = k2_zfmisc_1(k1_xboole_0,sK1) | k1_xboole_0 = sK1),
% 1.39/0.55    inference(forward_demodulation,[],[f306,f69])).
% 1.39/0.55  fof(f306,plain,(
% 1.39/0.55    ~r1_tarski(k2_zfmisc_1(k1_xboole_0,sK1),sK2) | sK2 = k2_zfmisc_1(k1_xboole_0,sK1) | k1_xboole_0 = sK1),
% 1.39/0.55    inference(superposition,[],[f143,f284])).
% 1.39/0.55  fof(f143,plain,(
% 1.39/0.55    ~r1_tarski(k2_zfmisc_1(sK0,sK1),sK2) | sK2 = k2_zfmisc_1(sK0,sK1)),
% 1.39/0.55    inference(resolution,[],[f125,f39])).
% 1.39/0.55  fof(f39,plain,(
% 1.39/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.39/0.55    inference(cnf_transformation,[],[f4])).
% 1.39/0.55  fof(f4,axiom,(
% 1.39/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.39/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.39/0.55  fof(f415,plain,(
% 1.39/0.55    sK2 = k2_zfmisc_1(sK0,sK1)),
% 1.39/0.55    inference(subsumption_resolution,[],[f414,f42])).
% 1.39/0.55  fof(f414,plain,(
% 1.39/0.55    ~r1_tarski(k1_xboole_0,sK2) | sK2 = k2_zfmisc_1(sK0,sK1)),
% 1.39/0.55    inference(forward_demodulation,[],[f392,f68])).
% 1.39/0.55  fof(f392,plain,(
% 1.39/0.55    ~r1_tarski(k2_zfmisc_1(sK0,k1_xboole_0),sK2) | sK2 = k2_zfmisc_1(sK0,sK1)),
% 1.39/0.55    inference(backward_demodulation,[],[f143,f382])).
% 1.39/0.55  fof(f433,plain,(
% 1.39/0.55    k1_xboole_0 != sK0 | ~r1_tarski(k2_relat_1(sK2),k1_xboole_0)),
% 1.39/0.55    inference(forward_demodulation,[],[f422,f45])).
% 1.39/0.55  fof(f422,plain,(
% 1.39/0.55    k1_relat_1(k1_xboole_0) != sK0 | ~r1_tarski(k2_relat_1(sK2),k1_xboole_0)),
% 1.39/0.55    inference(backward_demodulation,[],[f383,f417])).
% 1.39/0.55  fof(f383,plain,(
% 1.39/0.55    ~r1_tarski(k2_relat_1(sK2),k1_xboole_0) | sK0 != k1_relat_1(sK2)),
% 1.39/0.55    inference(backward_demodulation,[],[f31,f382])).
% 1.39/0.55  fof(f536,plain,(
% 1.39/0.55    v1_xboole_0(sK0)),
% 1.39/0.55    inference(unit_resulting_resolution,[],[f423,f198])).
% 1.39/0.55  fof(f198,plain,(
% 1.39/0.55    ( ! [X2,X3] : (~r2_hidden(X3,k1_funct_2(X2,k1_xboole_0)) | v1_xboole_0(X2)) )),
% 1.39/0.55    inference(resolution,[],[f96,f56])).
% 1.39/0.55  fof(f56,plain,(
% 1.39/0.55    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~r2_hidden(X1,X0)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f1])).
% 1.39/0.55  fof(f1,axiom,(
% 1.39/0.55    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.39/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.39/0.55  fof(f96,plain,(
% 1.39/0.55    ( ! [X0] : (v1_xboole_0(k1_funct_2(X0,k1_xboole_0)) | v1_xboole_0(X0)) )),
% 1.39/0.55    inference(resolution,[],[f57,f65])).
% 1.39/0.55  fof(f65,plain,(
% 1.39/0.55    v1_xboole_0(k1_xboole_0)),
% 1.39/0.55    inference(cnf_transformation,[],[f2])).
% 1.39/0.55  fof(f2,axiom,(
% 1.39/0.55    v1_xboole_0(k1_xboole_0)),
% 1.39/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.39/0.55  fof(f57,plain,(
% 1.39/0.55    ( ! [X0,X1] : (~v1_xboole_0(X1) | v1_xboole_0(X0) | v1_xboole_0(k1_funct_2(X0,X1))) )),
% 1.39/0.55    inference(cnf_transformation,[],[f28])).
% 1.39/0.55  fof(f28,plain,(
% 1.39/0.55    ! [X0,X1] : (v1_xboole_0(k1_funct_2(X0,X1)) | ~v1_xboole_0(X1) | v1_xboole_0(X0))),
% 1.39/0.55    inference(flattening,[],[f27])).
% 1.39/0.55  fof(f27,plain,(
% 1.39/0.55    ! [X0,X1] : (v1_xboole_0(k1_funct_2(X0,X1)) | (~v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 1.39/0.55    inference(ennf_transformation,[],[f14])).
% 1.39/0.55  fof(f14,axiom,(
% 1.39/0.55    ! [X0,X1] : ((v1_xboole_0(X1) & ~v1_xboole_0(X0)) => v1_xboole_0(k1_funct_2(X0,X1)))),
% 1.39/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_2)).
% 1.39/0.55  fof(f423,plain,(
% 1.39/0.55    r2_hidden(k1_xboole_0,k1_funct_2(sK0,k1_xboole_0))),
% 1.39/0.55    inference(backward_demodulation,[],[f384,f417])).
% 1.39/0.55  fof(f384,plain,(
% 1.39/0.55    r2_hidden(sK2,k1_funct_2(sK0,k1_xboole_0))),
% 1.39/0.55    inference(backward_demodulation,[],[f34,f382])).
% 1.39/0.55  % SZS output end Proof for theBenchmark
% 1.39/0.55  % (31780)------------------------------
% 1.39/0.55  % (31780)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.55  % (31780)Termination reason: Refutation
% 1.39/0.55  
% 1.39/0.55  % (31780)Memory used [KB]: 1918
% 1.39/0.55  % (31780)Time elapsed: 0.134 s
% 1.39/0.55  % (31780)------------------------------
% 1.39/0.55  % (31780)------------------------------
% 1.39/0.56  % (31760)Success in time 0.189 s
%------------------------------------------------------------------------------
