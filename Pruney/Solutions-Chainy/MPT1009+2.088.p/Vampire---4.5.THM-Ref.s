%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:04:38 EST 2020

% Result     : Theorem 1.39s
% Output     : Refutation 1.39s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 298 expanded)
%              Number of leaves         :   16 (  82 expanded)
%              Depth                    :   19
%              Number of atoms          :  292 ( 989 expanded)
%              Number of equality atoms :  136 ( 363 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f152,plain,(
    $false ),
    inference(subsumption_resolution,[],[f151,f90])).

fof(f90,plain,(
    v1_relat_1(sK5) ),
    inference(resolution,[],[f52,f72])).

fof(f72,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK2,sK2,sK2),sK3))) ),
    inference(definition_unfolding,[],[f43,f70])).

fof(f70,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f46,f49])).

fof(f49,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f46,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f43,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3))) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK2),sK3,sK5,sK4),k1_tarski(k1_funct_1(sK5,sK2)))
    & k1_xboole_0 != sK3
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3)))
    & v1_funct_2(sK5,k1_tarski(sK2),sK3)
    & v1_funct_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f15,f30])).

fof(f30,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
        & k1_xboole_0 != X1
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
   => ( ~ r1_tarski(k7_relset_1(k1_tarski(sK2),sK3,sK5,sK4),k1_tarski(k1_funct_1(sK5,sK2)))
      & k1_xboole_0 != sK3
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3)))
      & v1_funct_2(sK5,k1_tarski(sK2),sK3)
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X3,k1_tarski(X0),X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X3,k1_tarski(X0),X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X3,k1_tarski(X0),X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f151,plain,(
    ~ v1_relat_1(sK5) ),
    inference(resolution,[],[f144,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

fof(f144,plain,(
    ~ r1_tarski(k9_relat_1(sK5,sK4),k2_relat_1(sK5)) ),
    inference(backward_demodulation,[],[f104,f143])).

fof(f143,plain,(
    k1_enumset1(k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2)) = k2_relat_1(sK5) ),
    inference(forward_demodulation,[],[f142,f120])).

fof(f120,plain,(
    k2_relat_1(sK5) = k11_relat_1(sK5,sK2) ),
    inference(forward_demodulation,[],[f118,f91])).

fof(f91,plain,(
    k9_relat_1(sK5,k1_relat_1(sK5)) = k2_relat_1(sK5) ),
    inference(resolution,[],[f47,f90])).

fof(f47,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(f118,plain,(
    k9_relat_1(sK5,k1_relat_1(sK5)) = k11_relat_1(sK5,sK2) ),
    inference(superposition,[],[f96,f108])).

fof(f108,plain,(
    k1_enumset1(sK2,sK2,sK2) = k1_relat_1(sK5) ),
    inference(forward_demodulation,[],[f107,f99])).

fof(f99,plain,(
    k1_relat_1(sK5) = k1_relset_1(k1_enumset1(sK2,sK2,sK2),sK3,sK5) ),
    inference(resolution,[],[f53,f72])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f107,plain,(
    k1_enumset1(sK2,sK2,sK2) = k1_relset_1(k1_enumset1(sK2,sK2,sK2),sK3,sK5) ),
    inference(subsumption_resolution,[],[f106,f44])).

fof(f44,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f31])).

fof(f106,plain,
    ( k1_xboole_0 = sK3
    | k1_enumset1(sK2,sK2,sK2) = k1_relset_1(k1_enumset1(sK2,sK2,sK2),sK3,sK5) ),
    inference(subsumption_resolution,[],[f105,f73])).

fof(f73,plain,(
    v1_funct_2(sK5,k1_enumset1(sK2,sK2,sK2),sK3) ),
    inference(definition_unfolding,[],[f42,f70])).

fof(f42,plain,(
    v1_funct_2(sK5,k1_tarski(sK2),sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f105,plain,
    ( ~ v1_funct_2(sK5,k1_enumset1(sK2,sK2,sK2),sK3)
    | k1_xboole_0 = sK3
    | k1_enumset1(sK2,sK2,sK2) = k1_relset_1(k1_enumset1(sK2,sK2,sK2),sK3,sK5) ),
    inference(resolution,[],[f54,f92])).

fof(f92,plain,(
    sP0(k1_enumset1(sK2,sK2,sK2),sK5,sK3) ),
    inference(resolution,[],[f58,f72])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP0(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f24,f26])).

fof(f26,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

% (1293)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
fof(f23,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ v1_funct_2(X1,X0,X2)
      | k1_xboole_0 = X2
      | k1_relset_1(X0,X2,X1) = X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X2 )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f96,plain,(
    ! [X0] : k11_relat_1(sK5,X0) = k9_relat_1(sK5,k1_enumset1(X0,X0,X0)) ),
    inference(resolution,[],[f74,f90])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_enumset1(X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f48,f70])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

fof(f142,plain,(
    k1_enumset1(k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2)) = k11_relat_1(sK5,sK2) ),
    inference(subsumption_resolution,[],[f141,f90])).

fof(f141,plain,
    ( k1_enumset1(k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2)) = k11_relat_1(sK5,sK2)
    | ~ v1_relat_1(sK5) ),
    inference(subsumption_resolution,[],[f139,f41])).

fof(f41,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f31])).

fof(f139,plain,
    ( k1_enumset1(k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2)) = k11_relat_1(sK5,sK2)
    | ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5) ),
    inference(resolution,[],[f75,f115])).

fof(f115,plain,(
    r2_hidden(sK2,k1_relat_1(sK5)) ),
    inference(superposition,[],[f89,f108])).

fof(f89,plain,(
    ! [X2,X3] : r2_hidden(X2,k1_enumset1(X3,X3,X2)) ),
    inference(resolution,[],[f85,f83])).

fof(f83,plain,(
    ! [X4,X2,X1] :
      ( ~ sP1(X4,X1,X2)
      | r2_hidden(X4,X2) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ( ( sK6(X0,X1,X2) != X0
              & sK6(X0,X1,X2) != X1 )
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( sK6(X0,X1,X2) = X0
            | sK6(X0,X1,X2) = X1
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X0 != X4
                & X1 != X4 ) )
            & ( X0 = X4
              | X1 = X4
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f37,f38])).

fof(f38,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X0 != X3
              & X1 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X0 = X3
            | X1 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK6(X0,X1,X2) != X0
            & sK6(X0,X1,X2) != X1 )
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( sK6(X0,X1,X2) = X0
          | sK6(X0,X1,X2) = X1
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ( X0 != X3
                & X1 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X0 = X3
              | X1 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X0 != X4
                & X1 != X4 ) )
            & ( X0 = X4
              | X1 = X4
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X1,X0,X2] :
      ( ( sP1(X1,X0,X2)
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP1(X1,X0,X2) ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X1,X0,X2] :
      ( ( sP1(X1,X0,X2)
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP1(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X1,X0,X2] :
      ( sP1(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f85,plain,(
    ! [X0,X1] : sP1(X1,X0,k1_enumset1(X0,X0,X1)) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( sP1(X1,X0,X2)
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f67,f49])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( sP1(X1,X0,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ~ sP1(X1,X0,X2) )
      & ( sP1(X1,X0,X2)
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> sP1(X1,X0,X2) ) ),
    inference(definition_folding,[],[f1,f28])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(X1))
      | k11_relat_1(X1,X0) = k1_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f51,f70])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_funct_1)).

fof(f104,plain,(
    ~ r1_tarski(k9_relat_1(sK5,sK4),k1_enumset1(k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2))) ),
    inference(backward_demodulation,[],[f71,f103])).

% (1298)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
fof(f103,plain,(
    ! [X0] : k7_relset_1(k1_enumset1(sK2,sK2,sK2),sK3,sK5,X0) = k9_relat_1(sK5,X0) ),
    inference(resolution,[],[f69,f72])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f71,plain,(
    ~ r1_tarski(k7_relset_1(k1_enumset1(sK2,sK2,sK2),sK3,sK5,sK4),k1_enumset1(k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2))) ),
    inference(definition_unfolding,[],[f45,f70,f70])).

fof(f45,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK2),sK3,sK5,sK4),k1_tarski(k1_funct_1(sK5,sK2))) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:13:09 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.25/0.53  % (1297)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.25/0.54  % (1307)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.25/0.54  % (1299)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.25/0.54  % (1305)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.39/0.54  % (1297)Refutation found. Thanks to Tanya!
% 1.39/0.54  % SZS status Theorem for theBenchmark
% 1.39/0.54  % SZS output start Proof for theBenchmark
% 1.39/0.54  fof(f152,plain,(
% 1.39/0.54    $false),
% 1.39/0.54    inference(subsumption_resolution,[],[f151,f90])).
% 1.39/0.54  fof(f90,plain,(
% 1.39/0.54    v1_relat_1(sK5)),
% 1.39/0.54    inference(resolution,[],[f52,f72])).
% 1.39/0.54  fof(f72,plain,(
% 1.39/0.54    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK2,sK2,sK2),sK3)))),
% 1.39/0.54    inference(definition_unfolding,[],[f43,f70])).
% 1.39/0.54  fof(f70,plain,(
% 1.39/0.54    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 1.39/0.54    inference(definition_unfolding,[],[f46,f49])).
% 1.39/0.54  fof(f49,plain,(
% 1.39/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f3])).
% 1.39/0.54  fof(f3,axiom,(
% 1.39/0.54    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.39/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.39/0.54  fof(f46,plain,(
% 1.39/0.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f2])).
% 1.39/0.54  fof(f2,axiom,(
% 1.39/0.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.39/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.39/0.54  fof(f43,plain,(
% 1.39/0.54    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3)))),
% 1.39/0.54    inference(cnf_transformation,[],[f31])).
% 1.39/0.54  fof(f31,plain,(
% 1.39/0.54    ~r1_tarski(k7_relset_1(k1_tarski(sK2),sK3,sK5,sK4),k1_tarski(k1_funct_1(sK5,sK2))) & k1_xboole_0 != sK3 & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3))) & v1_funct_2(sK5,k1_tarski(sK2),sK3) & v1_funct_1(sK5)),
% 1.39/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f15,f30])).
% 1.39/0.54  fof(f30,plain,(
% 1.39/0.54    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK2),sK3,sK5,sK4),k1_tarski(k1_funct_1(sK5,sK2))) & k1_xboole_0 != sK3 & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3))) & v1_funct_2(sK5,k1_tarski(sK2),sK3) & v1_funct_1(sK5))),
% 1.39/0.54    introduced(choice_axiom,[])).
% 1.39/0.54  fof(f15,plain,(
% 1.39/0.54    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3))),
% 1.39/0.54    inference(flattening,[],[f14])).
% 1.39/0.54  fof(f14,plain,(
% 1.39/0.54    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)))),
% 1.39/0.54    inference(ennf_transformation,[],[f13])).
% 1.39/0.54  fof(f13,negated_conjecture,(
% 1.39/0.54    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 1.39/0.54    inference(negated_conjecture,[],[f12])).
% 1.39/0.54  fof(f12,conjecture,(
% 1.39/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 1.39/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).
% 1.39/0.54  fof(f52,plain,(
% 1.39/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f21])).
% 1.39/0.54  fof(f21,plain,(
% 1.39/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.39/0.54    inference(ennf_transformation,[],[f8])).
% 1.39/0.54  fof(f8,axiom,(
% 1.39/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.39/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.39/0.54  fof(f151,plain,(
% 1.39/0.54    ~v1_relat_1(sK5)),
% 1.39/0.54    inference(resolution,[],[f144,f50])).
% 1.39/0.54  fof(f50,plain,(
% 1.39/0.54    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f18])).
% 1.39/0.54  fof(f18,plain,(
% 1.39/0.54    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.39/0.54    inference(ennf_transformation,[],[f5])).
% 1.39/0.54  fof(f5,axiom,(
% 1.39/0.54    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 1.39/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).
% 1.39/0.54  fof(f144,plain,(
% 1.39/0.54    ~r1_tarski(k9_relat_1(sK5,sK4),k2_relat_1(sK5))),
% 1.39/0.54    inference(backward_demodulation,[],[f104,f143])).
% 1.39/0.54  fof(f143,plain,(
% 1.39/0.54    k1_enumset1(k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2)) = k2_relat_1(sK5)),
% 1.39/0.54    inference(forward_demodulation,[],[f142,f120])).
% 1.39/0.54  fof(f120,plain,(
% 1.39/0.54    k2_relat_1(sK5) = k11_relat_1(sK5,sK2)),
% 1.39/0.54    inference(forward_demodulation,[],[f118,f91])).
% 1.39/0.54  fof(f91,plain,(
% 1.39/0.54    k9_relat_1(sK5,k1_relat_1(sK5)) = k2_relat_1(sK5)),
% 1.39/0.54    inference(resolution,[],[f47,f90])).
% 1.39/0.54  fof(f47,plain,(
% 1.39/0.54    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f16])).
% 1.39/0.54  fof(f16,plain,(
% 1.39/0.54    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 1.39/0.54    inference(ennf_transformation,[],[f6])).
% 1.39/0.54  fof(f6,axiom,(
% 1.39/0.54    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 1.39/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).
% 1.39/0.54  fof(f118,plain,(
% 1.39/0.54    k9_relat_1(sK5,k1_relat_1(sK5)) = k11_relat_1(sK5,sK2)),
% 1.39/0.54    inference(superposition,[],[f96,f108])).
% 1.39/0.54  fof(f108,plain,(
% 1.39/0.54    k1_enumset1(sK2,sK2,sK2) = k1_relat_1(sK5)),
% 1.39/0.54    inference(forward_demodulation,[],[f107,f99])).
% 1.39/0.54  fof(f99,plain,(
% 1.39/0.54    k1_relat_1(sK5) = k1_relset_1(k1_enumset1(sK2,sK2,sK2),sK3,sK5)),
% 1.39/0.54    inference(resolution,[],[f53,f72])).
% 1.39/0.54  fof(f53,plain,(
% 1.39/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f22])).
% 1.39/0.54  fof(f22,plain,(
% 1.39/0.54    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.39/0.54    inference(ennf_transformation,[],[f9])).
% 1.39/0.54  fof(f9,axiom,(
% 1.39/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.39/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.39/0.54  fof(f107,plain,(
% 1.39/0.54    k1_enumset1(sK2,sK2,sK2) = k1_relset_1(k1_enumset1(sK2,sK2,sK2),sK3,sK5)),
% 1.39/0.54    inference(subsumption_resolution,[],[f106,f44])).
% 1.39/0.54  fof(f44,plain,(
% 1.39/0.54    k1_xboole_0 != sK3),
% 1.39/0.54    inference(cnf_transformation,[],[f31])).
% 1.39/0.54  fof(f106,plain,(
% 1.39/0.54    k1_xboole_0 = sK3 | k1_enumset1(sK2,sK2,sK2) = k1_relset_1(k1_enumset1(sK2,sK2,sK2),sK3,sK5)),
% 1.39/0.54    inference(subsumption_resolution,[],[f105,f73])).
% 1.39/0.54  fof(f73,plain,(
% 1.39/0.54    v1_funct_2(sK5,k1_enumset1(sK2,sK2,sK2),sK3)),
% 1.39/0.54    inference(definition_unfolding,[],[f42,f70])).
% 1.39/0.54  fof(f42,plain,(
% 1.39/0.54    v1_funct_2(sK5,k1_tarski(sK2),sK3)),
% 1.39/0.54    inference(cnf_transformation,[],[f31])).
% 1.39/0.54  fof(f105,plain,(
% 1.39/0.54    ~v1_funct_2(sK5,k1_enumset1(sK2,sK2,sK2),sK3) | k1_xboole_0 = sK3 | k1_enumset1(sK2,sK2,sK2) = k1_relset_1(k1_enumset1(sK2,sK2,sK2),sK3,sK5)),
% 1.39/0.54    inference(resolution,[],[f54,f92])).
% 1.39/0.54  fof(f92,plain,(
% 1.39/0.54    sP0(k1_enumset1(sK2,sK2,sK2),sK5,sK3)),
% 1.39/0.54    inference(resolution,[],[f58,f72])).
% 1.39/0.54  fof(f58,plain,(
% 1.39/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP0(X0,X2,X1)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f34])).
% 1.39/0.54  fof(f34,plain,(
% 1.39/0.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.39/0.54    inference(nnf_transformation,[],[f27])).
% 1.39/0.54  fof(f27,plain,(
% 1.39/0.54    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.39/0.54    inference(definition_folding,[],[f24,f26])).
% 1.39/0.54  fof(f26,plain,(
% 1.39/0.54    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 1.39/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.39/0.54  fof(f24,plain,(
% 1.39/0.54    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.39/0.54    inference(flattening,[],[f23])).
% 1.39/0.54  % (1293)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.39/0.54  fof(f23,plain,(
% 1.39/0.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.39/0.54    inference(ennf_transformation,[],[f11])).
% 1.39/0.54  fof(f11,axiom,(
% 1.39/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.39/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.39/0.54  fof(f54,plain,(
% 1.39/0.54    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | ~v1_funct_2(X1,X0,X2) | k1_xboole_0 = X2 | k1_relset_1(X0,X2,X1) = X0) )),
% 1.39/0.54    inference(cnf_transformation,[],[f33])).
% 1.39/0.54  fof(f33,plain,(
% 1.39/0.54    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X2) | ~sP0(X0,X1,X2))),
% 1.39/0.54    inference(rectify,[],[f32])).
% 1.39/0.54  fof(f32,plain,(
% 1.39/0.54    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 1.39/0.54    inference(nnf_transformation,[],[f26])).
% 1.39/0.54  fof(f96,plain,(
% 1.39/0.54    ( ! [X0] : (k11_relat_1(sK5,X0) = k9_relat_1(sK5,k1_enumset1(X0,X0,X0))) )),
% 1.39/0.54    inference(resolution,[],[f74,f90])).
% 1.39/0.54  fof(f74,plain,(
% 1.39/0.54    ( ! [X0,X1] : (~v1_relat_1(X0) | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_enumset1(X1,X1,X1))) )),
% 1.39/0.54    inference(definition_unfolding,[],[f48,f70])).
% 1.39/0.54  fof(f48,plain,(
% 1.39/0.54    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f17])).
% 1.39/0.54  fof(f17,plain,(
% 1.39/0.54    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 1.39/0.54    inference(ennf_transformation,[],[f4])).
% 1.39/0.54  fof(f4,axiom,(
% 1.39/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 1.39/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).
% 1.39/0.54  fof(f142,plain,(
% 1.39/0.54    k1_enumset1(k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2)) = k11_relat_1(sK5,sK2)),
% 1.39/0.54    inference(subsumption_resolution,[],[f141,f90])).
% 1.39/0.54  fof(f141,plain,(
% 1.39/0.54    k1_enumset1(k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2)) = k11_relat_1(sK5,sK2) | ~v1_relat_1(sK5)),
% 1.39/0.54    inference(subsumption_resolution,[],[f139,f41])).
% 1.39/0.54  fof(f41,plain,(
% 1.39/0.54    v1_funct_1(sK5)),
% 1.39/0.54    inference(cnf_transformation,[],[f31])).
% 1.39/0.54  fof(f139,plain,(
% 1.39/0.54    k1_enumset1(k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2)) = k11_relat_1(sK5,sK2) | ~v1_funct_1(sK5) | ~v1_relat_1(sK5)),
% 1.39/0.54    inference(resolution,[],[f75,f115])).
% 1.39/0.54  fof(f115,plain,(
% 1.39/0.54    r2_hidden(sK2,k1_relat_1(sK5))),
% 1.39/0.54    inference(superposition,[],[f89,f108])).
% 1.39/0.54  fof(f89,plain,(
% 1.39/0.54    ( ! [X2,X3] : (r2_hidden(X2,k1_enumset1(X3,X3,X2))) )),
% 1.39/0.54    inference(resolution,[],[f85,f83])).
% 1.39/0.54  fof(f83,plain,(
% 1.39/0.54    ( ! [X4,X2,X1] : (~sP1(X4,X1,X2) | r2_hidden(X4,X2)) )),
% 1.39/0.54    inference(equality_resolution,[],[f63])).
% 1.39/0.54  fof(f63,plain,(
% 1.39/0.54    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | ~sP1(X0,X1,X2)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f39])).
% 1.39/0.54  fof(f39,plain,(
% 1.39/0.54    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | (((sK6(X0,X1,X2) != X0 & sK6(X0,X1,X2) != X1) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (sK6(X0,X1,X2) = X0 | sK6(X0,X1,X2) = X1 | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 1.39/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f37,f38])).
% 1.39/0.54  fof(f38,plain,(
% 1.39/0.54    ! [X2,X1,X0] : (? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2))) => (((sK6(X0,X1,X2) != X0 & sK6(X0,X1,X2) != X1) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (sK6(X0,X1,X2) = X0 | sK6(X0,X1,X2) = X1 | r2_hidden(sK6(X0,X1,X2),X2))))),
% 1.39/0.54    introduced(choice_axiom,[])).
% 1.39/0.54  fof(f37,plain,(
% 1.39/0.54    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 1.39/0.54    inference(rectify,[],[f36])).
% 1.39/0.54  fof(f36,plain,(
% 1.39/0.54    ! [X1,X0,X2] : ((sP1(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | ~sP1(X1,X0,X2)))),
% 1.39/0.54    inference(flattening,[],[f35])).
% 1.39/0.54  fof(f35,plain,(
% 1.39/0.54    ! [X1,X0,X2] : ((sP1(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | ~sP1(X1,X0,X2)))),
% 1.39/0.54    inference(nnf_transformation,[],[f28])).
% 1.39/0.54  fof(f28,plain,(
% 1.39/0.54    ! [X1,X0,X2] : (sP1(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.39/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.39/0.54  fof(f85,plain,(
% 1.39/0.54    ( ! [X0,X1] : (sP1(X1,X0,k1_enumset1(X0,X0,X1))) )),
% 1.39/0.54    inference(equality_resolution,[],[f77])).
% 1.39/0.54  fof(f77,plain,(
% 1.39/0.54    ( ! [X2,X0,X1] : (sP1(X1,X0,X2) | k1_enumset1(X0,X0,X1) != X2) )),
% 1.39/0.54    inference(definition_unfolding,[],[f67,f49])).
% 1.39/0.54  fof(f67,plain,(
% 1.39/0.54    ( ! [X2,X0,X1] : (sP1(X1,X0,X2) | k2_tarski(X0,X1) != X2) )),
% 1.39/0.54    inference(cnf_transformation,[],[f40])).
% 1.39/0.54  fof(f40,plain,(
% 1.39/0.54    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ~sP1(X1,X0,X2)) & (sP1(X1,X0,X2) | k2_tarski(X0,X1) != X2))),
% 1.39/0.54    inference(nnf_transformation,[],[f29])).
% 1.39/0.54  fof(f29,plain,(
% 1.39/0.54    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> sP1(X1,X0,X2))),
% 1.39/0.54    inference(definition_folding,[],[f1,f28])).
% 1.39/0.54  fof(f1,axiom,(
% 1.39/0.54    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.39/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 1.39/0.54  fof(f75,plain,(
% 1.39/0.54    ( ! [X0,X1] : (~r2_hidden(X0,k1_relat_1(X1)) | k11_relat_1(X1,X0) = k1_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.39/0.54    inference(definition_unfolding,[],[f51,f70])).
% 1.39/0.54  fof(f51,plain,(
% 1.39/0.54    ( ! [X0,X1] : (k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f20])).
% 1.39/0.54  fof(f20,plain,(
% 1.39/0.54    ! [X0,X1] : (k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.39/0.54    inference(flattening,[],[f19])).
% 1.39/0.54  fof(f19,plain,(
% 1.39/0.54    ! [X0,X1] : ((k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.39/0.54    inference(ennf_transformation,[],[f7])).
% 1.39/0.54  fof(f7,axiom,(
% 1.39/0.54    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))))),
% 1.39/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_funct_1)).
% 1.39/0.54  fof(f104,plain,(
% 1.39/0.54    ~r1_tarski(k9_relat_1(sK5,sK4),k1_enumset1(k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2)))),
% 1.39/0.54    inference(backward_demodulation,[],[f71,f103])).
% 1.39/0.54  % (1298)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.39/0.54  fof(f103,plain,(
% 1.39/0.54    ( ! [X0] : (k7_relset_1(k1_enumset1(sK2,sK2,sK2),sK3,sK5,X0) = k9_relat_1(sK5,X0)) )),
% 1.39/0.54    inference(resolution,[],[f69,f72])).
% 1.39/0.54  fof(f69,plain,(
% 1.39/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f25])).
% 1.39/0.54  fof(f25,plain,(
% 1.39/0.54    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.39/0.54    inference(ennf_transformation,[],[f10])).
% 1.39/0.54  fof(f10,axiom,(
% 1.39/0.54    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 1.39/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 1.39/0.54  fof(f71,plain,(
% 1.39/0.54    ~r1_tarski(k7_relset_1(k1_enumset1(sK2,sK2,sK2),sK3,sK5,sK4),k1_enumset1(k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2)))),
% 1.39/0.54    inference(definition_unfolding,[],[f45,f70,f70])).
% 1.39/0.54  fof(f45,plain,(
% 1.39/0.54    ~r1_tarski(k7_relset_1(k1_tarski(sK2),sK3,sK5,sK4),k1_tarski(k1_funct_1(sK5,sK2)))),
% 1.39/0.54    inference(cnf_transformation,[],[f31])).
% 1.39/0.54  % SZS output end Proof for theBenchmark
% 1.39/0.54  % (1297)------------------------------
% 1.39/0.54  % (1297)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.54  % (1297)Termination reason: Refutation
% 1.39/0.54  
% 1.39/0.54  % (1297)Memory used [KB]: 10746
% 1.39/0.54  % (1297)Time elapsed: 0.116 s
% 1.39/0.54  % (1297)------------------------------
% 1.39/0.54  % (1297)------------------------------
% 1.39/0.55  % (1290)Success in time 0.179 s
%------------------------------------------------------------------------------
