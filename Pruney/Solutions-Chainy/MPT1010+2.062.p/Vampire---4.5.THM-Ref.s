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
% DateTime   : Thu Dec  3 13:04:59 EST 2020

% Result     : Theorem 1.08s
% Output     : Refutation 1.08s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 413 expanded)
%              Number of leaves         :   19 (  98 expanded)
%              Depth                    :   22
%              Number of atoms          :  408 (2026 expanded)
%              Number of equality atoms :  185 ( 817 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f429,plain,(
    $false ),
    inference(subsumption_resolution,[],[f378,f306])).

fof(f306,plain,(
    ! [X4] : r2_hidden(X4,k1_xboole_0) ),
    inference(backward_demodulation,[],[f99,f300])).

fof(f300,plain,(
    ! [X1] : k1_xboole_0 = X1 ),
    inference(subsumption_resolution,[],[f296,f91])).

fof(f91,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f296,plain,(
    ! [X1] :
      ( k1_xboole_0 != k2_zfmisc_1(X1,k1_xboole_0)
      | k1_xboole_0 = X1 ) ),
    inference(superposition,[],[f65,f236])).

fof(f236,plain,(
    k1_xboole_0 = k1_tarski(sK1) ),
    inference(subsumption_resolution,[],[f233,f53])).

fof(f53,plain,(
    r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( sK1 != k1_funct_1(sK3,sK2)
    & r2_hidden(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    & v1_funct_2(sK3,sK0,k1_tarski(sK1))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f34])).

fof(f34,plain,
    ( ? [X0,X1,X2,X3] :
        ( k1_funct_1(X3,X2) != X1
        & r2_hidden(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
   => ( sK1 != k1_funct_1(sK3,sK2)
      & r2_hidden(sK2,sK0)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
      & v1_funct_2(sK3,sK0,k1_tarski(sK1))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => k1_funct_1(X3,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => k1_funct_1(X3,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

fof(f233,plain,
    ( ~ r2_hidden(sK2,sK0)
    | k1_xboole_0 = k1_tarski(sK1) ),
    inference(superposition,[],[f189,f231])).

fof(f231,plain,
    ( sK0 = k1_relat_1(sK3)
    | k1_xboole_0 = k1_tarski(sK1) ),
    inference(subsumption_resolution,[],[f229,f52])).

fof(f52,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    inference(cnf_transformation,[],[f35])).

fof(f229,plain,
    ( sK0 = k1_relat_1(sK3)
    | k1_xboole_0 = k1_tarski(sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    inference(superposition,[],[f183,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f183,plain,
    ( sK0 = k1_relset_1(sK0,k1_tarski(sK1),sK3)
    | k1_xboole_0 = k1_tarski(sK1) ),
    inference(subsumption_resolution,[],[f180,f51])).

fof(f51,plain,(
    v1_funct_2(sK3,sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f35])).

fof(f180,plain,
    ( ~ v1_funct_2(sK3,sK0,k1_tarski(sK1))
    | k1_xboole_0 = k1_tarski(sK1)
    | sK0 = k1_relset_1(sK0,k1_tarski(sK1),sK3) ),
    inference(resolution,[],[f74,f52])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f44])).

% (11344)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% (11345)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
fof(f44,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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

fof(f189,plain,(
    ~ r2_hidden(sK2,k1_relat_1(sK3)) ),
    inference(trivial_inequality_removal,[],[f185])).

fof(f185,plain,
    ( sK1 != sK1
    | ~ r2_hidden(sK2,k1_relat_1(sK3)) ),
    inference(superposition,[],[f54,f178])).

fof(f178,plain,(
    ! [X0] :
      ( sK1 = k1_funct_1(sK3,X0)
      | ~ r2_hidden(X0,k1_relat_1(sK3)) ) ),
    inference(subsumption_resolution,[],[f177,f115])).

fof(f115,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f70,f52])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f177,plain,(
    ! [X0] :
      ( sK1 = k1_funct_1(sK3,X0)
      | ~ r2_hidden(X0,k1_relat_1(sK3))
      | ~ v1_relat_1(sK3) ) ),
    inference(subsumption_resolution,[],[f176,f50])).

fof(f50,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f176,plain,(
    ! [X0] :
      ( sK1 = k1_funct_1(sK3,X0)
      | ~ r2_hidden(X0,k1_relat_1(sK3))
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f171,f88])).

fof(f88,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK4(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK4(X0,X1),X1) )
              & ( ( sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1))
                  & r2_hidden(sK5(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK4(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK6(X0,X5)) = X5
                    & r2_hidden(sK6(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f37,f40,f39,f38])).

% (11340)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k1_funct_1(X0,X3) != X2
                | ~ r2_hidden(X3,k1_relat_1(X0)) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( k1_funct_1(X0,X4) = X2
                & r2_hidden(X4,k1_relat_1(X0)) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( k1_funct_1(X0,X3) != sK4(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK4(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = sK4(X0,X1)
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1))
        & r2_hidden(sK5(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK6(X0,X5)) = X5
        & r2_hidden(sK6(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X2
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ? [X7] :
                      ( k1_funct_1(X0,X7) = X5
                      & r2_hidden(X7,k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) ) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

fof(f171,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK3))
      | sK1 = X0 ) ),
    inference(resolution,[],[f169,f129])).

fof(f129,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_tarski(X0))
      | X0 = X1 ) ),
    inference(duplicate_literal_removal,[],[f128])).

fof(f128,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_tarski(X0))
      | X0 = X1
      | X0 = X1 ) ),
    inference(superposition,[],[f102,f55])).

fof(f55,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f102,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_tarski(X0,X1))
      | X0 = X4
      | X1 = X4 ) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK7(X0,X1,X2) != X1
              & sK7(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK7(X0,X1,X2),X2) )
          & ( sK7(X0,X1,X2) = X1
            | sK7(X0,X1,X2) = X0
            | r2_hidden(sK7(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f47,f48])).

fof(f48,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK7(X0,X1,X2) != X1
            & sK7(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK7(X0,X1,X2),X2) )
        & ( sK7(X0,X1,X2) = X1
          | sK7(X0,X1,X2) = X0
          | r2_hidden(sK7(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f46])).

% (11356)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
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
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
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
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f169,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_tarski(sK1))
      | ~ r2_hidden(X0,k2_relat_1(sK3)) ) ),
    inference(subsumption_resolution,[],[f168,f111])).

fof(f111,plain,(
    ! [X1] : ~ v1_xboole_0(k1_tarski(X1)) ),
    inference(superposition,[],[f108,f55])).

fof(f108,plain,(
    ! [X0,X1] : ~ v1_xboole_0(k2_tarski(X0,X1)) ),
    inference(resolution,[],[f99,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f168,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK3))
      | v1_xboole_0(k1_tarski(sK1))
      | r2_hidden(X0,k1_tarski(sK1)) ) ),
    inference(resolution,[],[f165,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f24])).

% (11343)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f165,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_tarski(sK1))
      | ~ r2_hidden(X0,k2_relat_1(sK3)) ) ),
    inference(resolution,[],[f159,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

% (11356)Refutation not found, incomplete strategy% (11356)------------------------------
% (11356)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (11356)Termination reason: Refutation not found, incomplete strategy

% (11356)Memory used [KB]: 10746
% (11356)Time elapsed: 0.127 s
% (11356)------------------------------
% (11356)------------------------------
fof(f159,plain,(
    m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(k1_tarski(sK1))) ),
    inference(resolution,[],[f136,f52])).

fof(f136,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_relat_1(X2),k1_zfmisc_1(X1)) ) ),
    inference(duplicate_literal_removal,[],[f135])).

fof(f135,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relat_1(X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f73,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f54,plain,(
    sK1 != k1_funct_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))
        & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
     => ( k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))
        & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_zfmisc_1)).

fof(f99,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_tarski(X0,X4)) ),
    inference(equality_resolution,[],[f98])).

fof(f98,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f378,plain,(
    ~ r2_hidden(sK2,k1_xboole_0) ),
    inference(backward_demodulation,[],[f189,f300])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:08:25 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  ipcrm: permission denied for id (1217822720)
% 0.13/0.36  ipcrm: permission denied for id (1224409089)
% 0.13/0.36  ipcrm: permission denied for id (1217888258)
% 0.13/0.36  ipcrm: permission denied for id (1222082564)
% 0.13/0.37  ipcrm: permission denied for id (1222115333)
% 0.13/0.37  ipcrm: permission denied for id (1217986566)
% 0.13/0.37  ipcrm: permission denied for id (1218019335)
% 0.13/0.37  ipcrm: permission denied for id (1224507401)
% 0.13/0.37  ipcrm: permission denied for id (1224540170)
% 0.13/0.37  ipcrm: permission denied for id (1222246411)
% 0.13/0.37  ipcrm: permission denied for id (1222279180)
% 0.13/0.37  ipcrm: permission denied for id (1218150413)
% 0.13/0.38  ipcrm: permission denied for id (1218183182)
% 0.13/0.38  ipcrm: permission denied for id (1222311951)
% 0.13/0.38  ipcrm: permission denied for id (1218248720)
% 0.13/0.38  ipcrm: permission denied for id (1218281489)
% 0.13/0.38  ipcrm: permission denied for id (1222344722)
% 0.13/0.38  ipcrm: permission denied for id (1218347027)
% 0.13/0.38  ipcrm: permission denied for id (1222377492)
% 0.13/0.38  ipcrm: permission denied for id (1224572949)
% 0.13/0.39  ipcrm: permission denied for id (1218445334)
% 0.13/0.39  ipcrm: permission denied for id (1218478103)
% 0.13/0.39  ipcrm: permission denied for id (1218510872)
% 0.13/0.39  ipcrm: permission denied for id (1222443033)
% 0.13/0.39  ipcrm: permission denied for id (1218576410)
% 0.13/0.39  ipcrm: permission denied for id (1218609179)
% 0.13/0.39  ipcrm: permission denied for id (1218641948)
% 0.13/0.39  ipcrm: permission denied for id (1218674717)
% 0.13/0.40  ipcrm: permission denied for id (1225687070)
% 0.13/0.40  ipcrm: permission denied for id (1224638495)
% 0.20/0.40  ipcrm: permission denied for id (1222541344)
% 0.20/0.40  ipcrm: permission denied for id (1225719841)
% 0.20/0.40  ipcrm: permission denied for id (1222606882)
% 0.20/0.40  ipcrm: permission denied for id (1218871331)
% 0.20/0.40  ipcrm: permission denied for id (1222639652)
% 0.20/0.40  ipcrm: permission denied for id (1218969638)
% 0.20/0.41  ipcrm: permission denied for id (1222705191)
% 0.20/0.41  ipcrm: permission denied for id (1219067944)
% 0.20/0.41  ipcrm: permission denied for id (1219100713)
% 0.20/0.41  ipcrm: permission denied for id (1222737962)
% 0.20/0.41  ipcrm: permission denied for id (1225785387)
% 0.20/0.41  ipcrm: permission denied for id (1219231788)
% 0.20/0.41  ipcrm: permission denied for id (1219264557)
% 0.20/0.41  ipcrm: permission denied for id (1224769582)
% 0.20/0.42  ipcrm: permission denied for id (1224802351)
% 0.20/0.42  ipcrm: permission denied for id (1224835120)
% 0.20/0.42  ipcrm: permission denied for id (1219395633)
% 0.20/0.42  ipcrm: permission denied for id (1219428402)
% 0.20/0.42  ipcrm: permission denied for id (1222934579)
% 0.20/0.42  ipcrm: permission denied for id (1222967348)
% 0.20/0.42  ipcrm: permission denied for id (1223000117)
% 0.20/0.42  ipcrm: permission denied for id (1224867894)
% 0.20/0.43  ipcrm: permission denied for id (1223065655)
% 0.20/0.43  ipcrm: permission denied for id (1223098424)
% 0.20/0.43  ipcrm: permission denied for id (1223131193)
% 0.20/0.43  ipcrm: permission denied for id (1219690554)
% 0.20/0.43  ipcrm: permission denied for id (1219723323)
% 0.20/0.43  ipcrm: permission denied for id (1219756092)
% 0.20/0.43  ipcrm: permission denied for id (1223163965)
% 0.20/0.43  ipcrm: permission denied for id (1225850943)
% 0.20/0.44  ipcrm: permission denied for id (1219887168)
% 0.20/0.44  ipcrm: permission denied for id (1219952705)
% 0.20/0.44  ipcrm: permission denied for id (1223262274)
% 0.20/0.44  ipcrm: permission denied for id (1223295043)
% 0.20/0.44  ipcrm: permission denied for id (1220051012)
% 0.20/0.44  ipcrm: permission denied for id (1224966213)
% 0.20/0.44  ipcrm: permission denied for id (1220116550)
% 0.20/0.44  ipcrm: permission denied for id (1225883719)
% 0.20/0.45  ipcrm: permission denied for id (1220182088)
% 0.20/0.45  ipcrm: permission denied for id (1220214857)
% 0.20/0.45  ipcrm: permission denied for id (1225916490)
% 0.20/0.45  ipcrm: permission denied for id (1225064523)
% 0.20/0.45  ipcrm: permission denied for id (1220313164)
% 0.20/0.45  ipcrm: permission denied for id (1225097293)
% 0.20/0.45  ipcrm: permission denied for id (1223491662)
% 0.20/0.45  ipcrm: permission denied for id (1220411471)
% 0.20/0.46  ipcrm: permission denied for id (1223524432)
% 0.20/0.46  ipcrm: permission denied for id (1225130065)
% 0.20/0.46  ipcrm: permission denied for id (1220509778)
% 0.20/0.46  ipcrm: permission denied for id (1220542547)
% 0.20/0.46  ipcrm: permission denied for id (1223589972)
% 0.20/0.46  ipcrm: permission denied for id (1220608085)
% 0.20/0.46  ipcrm: permission denied for id (1220640854)
% 0.20/0.46  ipcrm: permission denied for id (1223622743)
% 0.20/0.47  ipcrm: permission denied for id (1225982041)
% 0.20/0.47  ipcrm: permission denied for id (1220771930)
% 0.20/0.47  ipcrm: permission denied for id (1220804699)
% 0.20/0.47  ipcrm: permission denied for id (1220837468)
% 0.20/0.47  ipcrm: permission denied for id (1225228381)
% 0.20/0.47  ipcrm: permission denied for id (1220903006)
% 0.20/0.47  ipcrm: permission denied for id (1223753823)
% 0.20/0.47  ipcrm: permission denied for id (1220968544)
% 0.20/0.48  ipcrm: permission denied for id (1221001313)
% 0.20/0.48  ipcrm: permission denied for id (1226014818)
% 0.20/0.48  ipcrm: permission denied for id (1221066851)
% 0.20/0.48  ipcrm: permission denied for id (1225326693)
% 0.20/0.48  ipcrm: permission denied for id (1221165158)
% 0.20/0.48  ipcrm: permission denied for id (1221197927)
% 0.20/0.48  ipcrm: permission denied for id (1221230696)
% 0.20/0.49  ipcrm: permission denied for id (1221263465)
% 0.20/0.49  ipcrm: permission denied for id (1223884906)
% 0.20/0.49  ipcrm: permission denied for id (1225359467)
% 0.20/0.49  ipcrm: permission denied for id (1221361772)
% 0.20/0.49  ipcrm: permission denied for id (1221394541)
% 0.20/0.49  ipcrm: permission denied for id (1223950446)
% 0.20/0.49  ipcrm: permission denied for id (1223983215)
% 0.20/0.49  ipcrm: permission denied for id (1225392240)
% 0.20/0.50  ipcrm: permission denied for id (1221492849)
% 0.20/0.50  ipcrm: permission denied for id (1221591156)
% 0.20/0.50  ipcrm: permission denied for id (1221623925)
% 0.20/0.50  ipcrm: permission denied for id (1224114294)
% 0.20/0.50  ipcrm: permission denied for id (1225490551)
% 0.20/0.50  ipcrm: permission denied for id (1221722232)
% 0.20/0.50  ipcrm: permission denied for id (1224212601)
% 0.20/0.51  ipcrm: permission denied for id (1226145914)
% 0.20/0.51  ipcrm: permission denied for id (1225588859)
% 0.20/0.51  ipcrm: permission denied for id (1224310908)
% 0.20/0.51  ipcrm: permission denied for id (1224343677)
% 0.20/0.51  ipcrm: permission denied for id (1224376446)
% 0.20/0.51  ipcrm: permission denied for id (1221984383)
% 1.08/0.64  % (11342)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.08/0.65  % (11350)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.08/0.66  % (11366)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.08/0.66  % (11358)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.08/0.67  % (11349)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.08/0.67  % (11350)Refutation not found, incomplete strategy% (11350)------------------------------
% 1.08/0.67  % (11350)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.08/0.67  % (11350)Termination reason: Refutation not found, incomplete strategy
% 1.08/0.67  
% 1.08/0.67  % (11350)Memory used [KB]: 10874
% 1.08/0.67  % (11350)Time elapsed: 0.122 s
% 1.08/0.67  % (11350)------------------------------
% 1.08/0.67  % (11350)------------------------------
% 1.08/0.68  % (11353)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.08/0.68  % (11362)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.08/0.68  % (11349)Refutation found. Thanks to Tanya!
% 1.08/0.68  % SZS status Theorem for theBenchmark
% 1.08/0.68  % (11341)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.08/0.68  % (11357)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.08/0.68  % (11359)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.08/0.68  % (11365)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.08/0.68  % (11361)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.08/0.68  % (11354)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.08/0.69  % (11355)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.08/0.69  % (11364)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.08/0.69  % SZS output start Proof for theBenchmark
% 1.08/0.69  fof(f429,plain,(
% 1.08/0.69    $false),
% 1.08/0.69    inference(subsumption_resolution,[],[f378,f306])).
% 1.08/0.69  fof(f306,plain,(
% 1.08/0.69    ( ! [X4] : (r2_hidden(X4,k1_xboole_0)) )),
% 1.08/0.69    inference(backward_demodulation,[],[f99,f300])).
% 1.08/0.69  fof(f300,plain,(
% 1.08/0.69    ( ! [X1] : (k1_xboole_0 = X1) )),
% 1.08/0.69    inference(subsumption_resolution,[],[f296,f91])).
% 1.08/0.69  fof(f91,plain,(
% 1.08/0.69    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.08/0.69    inference(equality_resolution,[],[f69])).
% 1.08/0.69  fof(f69,plain,(
% 1.08/0.69    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 1.08/0.69    inference(cnf_transformation,[],[f43])).
% 1.08/0.69  fof(f43,plain,(
% 1.08/0.69    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 1.08/0.69    inference(flattening,[],[f42])).
% 1.08/0.69  fof(f42,plain,(
% 1.08/0.69    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 1.08/0.69    inference(nnf_transformation,[],[f5])).
% 1.08/0.69  fof(f5,axiom,(
% 1.08/0.69    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.08/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.08/0.69  fof(f296,plain,(
% 1.08/0.69    ( ! [X1] : (k1_xboole_0 != k2_zfmisc_1(X1,k1_xboole_0) | k1_xboole_0 = X1) )),
% 1.08/0.69    inference(superposition,[],[f65,f236])).
% 1.08/0.69  fof(f236,plain,(
% 1.08/0.69    k1_xboole_0 = k1_tarski(sK1)),
% 1.08/0.69    inference(subsumption_resolution,[],[f233,f53])).
% 1.08/0.69  fof(f53,plain,(
% 1.08/0.69    r2_hidden(sK2,sK0)),
% 1.08/0.69    inference(cnf_transformation,[],[f35])).
% 1.08/0.69  fof(f35,plain,(
% 1.08/0.69    sK1 != k1_funct_1(sK3,sK2) & r2_hidden(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_2(sK3,sK0,k1_tarski(sK1)) & v1_funct_1(sK3)),
% 1.08/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f34])).
% 1.08/0.69  fof(f34,plain,(
% 1.08/0.69    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (sK1 != k1_funct_1(sK3,sK2) & r2_hidden(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_2(sK3,sK0,k1_tarski(sK1)) & v1_funct_1(sK3))),
% 1.08/0.69    introduced(choice_axiom,[])).
% 1.08/0.69  fof(f19,plain,(
% 1.08/0.69    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))),
% 1.08/0.69    inference(flattening,[],[f18])).
% 1.08/0.69  fof(f18,plain,(
% 1.08/0.69    ? [X0,X1,X2,X3] : ((k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)))),
% 1.08/0.69    inference(ennf_transformation,[],[f16])).
% 1.08/0.69  fof(f16,negated_conjecture,(
% 1.08/0.69    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 1.08/0.69    inference(negated_conjecture,[],[f15])).
% 1.08/0.69  fof(f15,conjecture,(
% 1.08/0.69    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 1.08/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).
% 1.08/0.69  fof(f233,plain,(
% 1.08/0.69    ~r2_hidden(sK2,sK0) | k1_xboole_0 = k1_tarski(sK1)),
% 1.08/0.69    inference(superposition,[],[f189,f231])).
% 1.08/0.69  fof(f231,plain,(
% 1.08/0.69    sK0 = k1_relat_1(sK3) | k1_xboole_0 = k1_tarski(sK1)),
% 1.08/0.69    inference(subsumption_resolution,[],[f229,f52])).
% 1.08/0.69  fof(f52,plain,(
% 1.08/0.69    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))),
% 1.08/0.69    inference(cnf_transformation,[],[f35])).
% 1.08/0.69  fof(f229,plain,(
% 1.08/0.69    sK0 = k1_relat_1(sK3) | k1_xboole_0 = k1_tarski(sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))),
% 1.08/0.69    inference(superposition,[],[f183,f72])).
% 1.08/0.69  fof(f72,plain,(
% 1.08/0.69    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.08/0.69    inference(cnf_transformation,[],[f28])).
% 1.08/0.69  fof(f28,plain,(
% 1.08/0.69    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.08/0.69    inference(ennf_transformation,[],[f12])).
% 1.08/0.69  fof(f12,axiom,(
% 1.08/0.69    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.08/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.08/0.69  fof(f183,plain,(
% 1.08/0.69    sK0 = k1_relset_1(sK0,k1_tarski(sK1),sK3) | k1_xboole_0 = k1_tarski(sK1)),
% 1.08/0.69    inference(subsumption_resolution,[],[f180,f51])).
% 1.08/0.69  fof(f51,plain,(
% 1.08/0.69    v1_funct_2(sK3,sK0,k1_tarski(sK1))),
% 1.08/0.69    inference(cnf_transformation,[],[f35])).
% 1.08/0.69  fof(f180,plain,(
% 1.08/0.69    ~v1_funct_2(sK3,sK0,k1_tarski(sK1)) | k1_xboole_0 = k1_tarski(sK1) | sK0 = k1_relset_1(sK0,k1_tarski(sK1),sK3)),
% 1.08/0.69    inference(resolution,[],[f74,f52])).
% 1.08/0.69  fof(f74,plain,(
% 1.08/0.69    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 1.08/0.69    inference(cnf_transformation,[],[f44])).
% 1.08/0.69  % (11344)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.08/0.69  % (11345)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.08/0.69  fof(f44,plain,(
% 1.08/0.69    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.08/0.69    inference(nnf_transformation,[],[f31])).
% 1.08/0.69  fof(f31,plain,(
% 1.08/0.69    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.08/0.69    inference(flattening,[],[f30])).
% 1.08/0.69  fof(f30,plain,(
% 1.08/0.69    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.08/0.69    inference(ennf_transformation,[],[f14])).
% 1.08/0.69  fof(f14,axiom,(
% 1.08/0.69    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.08/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.08/0.69  fof(f189,plain,(
% 1.08/0.69    ~r2_hidden(sK2,k1_relat_1(sK3))),
% 1.08/0.69    inference(trivial_inequality_removal,[],[f185])).
% 1.08/0.69  fof(f185,plain,(
% 1.08/0.69    sK1 != sK1 | ~r2_hidden(sK2,k1_relat_1(sK3))),
% 1.08/0.69    inference(superposition,[],[f54,f178])).
% 1.08/0.69  fof(f178,plain,(
% 1.08/0.69    ( ! [X0] : (sK1 = k1_funct_1(sK3,X0) | ~r2_hidden(X0,k1_relat_1(sK3))) )),
% 1.08/0.69    inference(subsumption_resolution,[],[f177,f115])).
% 1.08/0.69  fof(f115,plain,(
% 1.08/0.69    v1_relat_1(sK3)),
% 1.08/0.69    inference(resolution,[],[f70,f52])).
% 1.08/0.69  fof(f70,plain,(
% 1.08/0.69    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.08/0.69    inference(cnf_transformation,[],[f26])).
% 1.08/0.69  fof(f26,plain,(
% 1.08/0.69    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.08/0.69    inference(ennf_transformation,[],[f10])).
% 1.08/0.69  fof(f10,axiom,(
% 1.08/0.69    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.08/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.08/0.69  fof(f177,plain,(
% 1.08/0.69    ( ! [X0] : (sK1 = k1_funct_1(sK3,X0) | ~r2_hidden(X0,k1_relat_1(sK3)) | ~v1_relat_1(sK3)) )),
% 1.08/0.69    inference(subsumption_resolution,[],[f176,f50])).
% 1.08/0.69  fof(f50,plain,(
% 1.08/0.69    v1_funct_1(sK3)),
% 1.08/0.69    inference(cnf_transformation,[],[f35])).
% 1.08/0.69  fof(f176,plain,(
% 1.08/0.69    ( ! [X0] : (sK1 = k1_funct_1(sK3,X0) | ~r2_hidden(X0,k1_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)) )),
% 1.08/0.69    inference(resolution,[],[f171,f88])).
% 1.08/0.69  fof(f88,plain,(
% 1.08/0.69    ( ! [X6,X0] : (r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0)) | ~r2_hidden(X6,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.08/0.69    inference(equality_resolution,[],[f87])).
% 1.08/0.69  fof(f87,plain,(
% 1.08/0.69    ( ! [X6,X0,X1] : (r2_hidden(k1_funct_1(X0,X6),X1) | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.08/0.69    inference(equality_resolution,[],[f58])).
% 1.08/0.69  fof(f58,plain,(
% 1.08/0.69    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.08/0.69    inference(cnf_transformation,[],[f41])).
% 1.08/0.69  fof(f41,plain,(
% 1.08/0.69    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK4(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK4(X0,X1),X1)) & ((sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1)) & r2_hidden(sK5(X0,X1),k1_relat_1(X0))) | r2_hidden(sK4(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK6(X0,X5)) = X5 & r2_hidden(sK6(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.08/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f37,f40,f39,f38])).
% 1.08/0.69  % (11340)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.08/0.69  fof(f38,plain,(
% 1.08/0.69    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK4(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK4(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK4(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK4(X0,X1),X1))))),
% 1.08/0.69    introduced(choice_axiom,[])).
% 1.08/0.69  fof(f39,plain,(
% 1.08/0.69    ! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = sK4(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) => (sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1)) & r2_hidden(sK5(X0,X1),k1_relat_1(X0))))),
% 1.08/0.69    introduced(choice_axiom,[])).
% 1.08/0.69  fof(f40,plain,(
% 1.08/0.69    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK6(X0,X5)) = X5 & r2_hidden(sK6(X0,X5),k1_relat_1(X0))))),
% 1.08/0.69    introduced(choice_axiom,[])).
% 1.08/0.69  fof(f37,plain,(
% 1.08/0.69    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.08/0.69    inference(rectify,[],[f36])).
% 1.08/0.69  fof(f36,plain,(
% 1.08/0.69    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.08/0.69    inference(nnf_transformation,[],[f21])).
% 1.08/0.69  fof(f21,plain,(
% 1.08/0.69    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.08/0.69    inference(flattening,[],[f20])).
% 1.08/0.69  fof(f20,plain,(
% 1.08/0.69    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.08/0.69    inference(ennf_transformation,[],[f9])).
% 1.08/0.69  fof(f9,axiom,(
% 1.08/0.69    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 1.08/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).
% 1.08/0.69  fof(f171,plain,(
% 1.08/0.69    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK3)) | sK1 = X0) )),
% 1.08/0.69    inference(resolution,[],[f169,f129])).
% 1.08/0.69  fof(f129,plain,(
% 1.08/0.69    ( ! [X0,X1] : (~r2_hidden(X1,k1_tarski(X0)) | X0 = X1) )),
% 1.08/0.69    inference(duplicate_literal_removal,[],[f128])).
% 1.08/0.69  fof(f128,plain,(
% 1.08/0.69    ( ! [X0,X1] : (~r2_hidden(X1,k1_tarski(X0)) | X0 = X1 | X0 = X1) )),
% 1.08/0.69    inference(superposition,[],[f102,f55])).
% 1.08/0.69  fof(f55,plain,(
% 1.08/0.69    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.08/0.69    inference(cnf_transformation,[],[f3])).
% 1.08/0.69  fof(f3,axiom,(
% 1.08/0.69    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.08/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.08/0.69  fof(f102,plain,(
% 1.08/0.69    ( ! [X4,X0,X1] : (~r2_hidden(X4,k2_tarski(X0,X1)) | X0 = X4 | X1 = X4) )),
% 1.08/0.69    inference(equality_resolution,[],[f81])).
% 1.08/0.69  fof(f81,plain,(
% 1.08/0.69    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 1.08/0.69    inference(cnf_transformation,[],[f49])).
% 1.08/0.69  fof(f49,plain,(
% 1.08/0.69    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK7(X0,X1,X2) != X1 & sK7(X0,X1,X2) != X0) | ~r2_hidden(sK7(X0,X1,X2),X2)) & (sK7(X0,X1,X2) = X1 | sK7(X0,X1,X2) = X0 | r2_hidden(sK7(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.08/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f47,f48])).
% 1.08/0.69  fof(f48,plain,(
% 1.08/0.69    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK7(X0,X1,X2) != X1 & sK7(X0,X1,X2) != X0) | ~r2_hidden(sK7(X0,X1,X2),X2)) & (sK7(X0,X1,X2) = X1 | sK7(X0,X1,X2) = X0 | r2_hidden(sK7(X0,X1,X2),X2))))),
% 1.08/0.69    introduced(choice_axiom,[])).
% 1.08/0.69  fof(f47,plain,(
% 1.08/0.69    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.08/0.69    inference(rectify,[],[f46])).
% 1.08/0.69  % (11356)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.08/0.69  fof(f46,plain,(
% 1.08/0.69    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.08/0.69    inference(flattening,[],[f45])).
% 1.08/0.69  fof(f45,plain,(
% 1.08/0.69    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.08/0.69    inference(nnf_transformation,[],[f2])).
% 1.08/0.69  fof(f2,axiom,(
% 1.08/0.69    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.08/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 1.08/0.69  fof(f169,plain,(
% 1.08/0.69    ( ! [X0] : (r2_hidden(X0,k1_tarski(sK1)) | ~r2_hidden(X0,k2_relat_1(sK3))) )),
% 1.08/0.69    inference(subsumption_resolution,[],[f168,f111])).
% 1.08/0.69  fof(f111,plain,(
% 1.08/0.69    ( ! [X1] : (~v1_xboole_0(k1_tarski(X1))) )),
% 1.08/0.69    inference(superposition,[],[f108,f55])).
% 1.08/0.69  fof(f108,plain,(
% 1.08/0.69    ( ! [X0,X1] : (~v1_xboole_0(k2_tarski(X0,X1))) )),
% 1.08/0.69    inference(resolution,[],[f99,f62])).
% 1.08/0.69  fof(f62,plain,(
% 1.08/0.69    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 1.08/0.69    inference(cnf_transformation,[],[f22])).
% 1.08/0.69  fof(f22,plain,(
% 1.08/0.69    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 1.08/0.69    inference(ennf_transformation,[],[f17])).
% 1.08/0.69  fof(f17,plain,(
% 1.08/0.69    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 1.08/0.69    inference(unused_predicate_definition_removal,[],[f1])).
% 1.08/0.69  fof(f1,axiom,(
% 1.08/0.69    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.08/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.08/0.69  fof(f168,plain,(
% 1.08/0.69    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK3)) | v1_xboole_0(k1_tarski(sK1)) | r2_hidden(X0,k1_tarski(sK1))) )),
% 1.08/0.69    inference(resolution,[],[f165,f66])).
% 1.08/0.69  fof(f66,plain,(
% 1.08/0.69    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 1.08/0.69    inference(cnf_transformation,[],[f25])).
% 1.08/0.69  fof(f25,plain,(
% 1.08/0.69    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.08/0.69    inference(flattening,[],[f24])).
% 1.08/0.69  % (11343)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.08/0.69  fof(f24,plain,(
% 1.08/0.69    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.08/0.69    inference(ennf_transformation,[],[f7])).
% 1.08/0.69  fof(f7,axiom,(
% 1.08/0.69    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.08/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 1.08/0.69  fof(f165,plain,(
% 1.08/0.69    ( ! [X0] : (m1_subset_1(X0,k1_tarski(sK1)) | ~r2_hidden(X0,k2_relat_1(sK3))) )),
% 1.08/0.69    inference(resolution,[],[f159,f80])).
% 1.08/0.69  fof(f80,plain,(
% 1.08/0.69    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 1.08/0.69    inference(cnf_transformation,[],[f33])).
% 1.08/0.69  fof(f33,plain,(
% 1.08/0.69    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.08/0.69    inference(flattening,[],[f32])).
% 1.08/0.69  fof(f32,plain,(
% 1.08/0.69    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 1.08/0.69    inference(ennf_transformation,[],[f8])).
% 1.08/0.69  fof(f8,axiom,(
% 1.08/0.69    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 1.08/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 1.08/0.70  % (11356)Refutation not found, incomplete strategy% (11356)------------------------------
% 1.08/0.70  % (11356)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.08/0.70  % (11356)Termination reason: Refutation not found, incomplete strategy
% 1.08/0.70  
% 1.08/0.70  % (11356)Memory used [KB]: 10746
% 1.08/0.70  % (11356)Time elapsed: 0.127 s
% 1.08/0.70  % (11356)------------------------------
% 1.08/0.70  % (11356)------------------------------
% 1.08/0.70  fof(f159,plain,(
% 1.08/0.70    m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(k1_tarski(sK1)))),
% 1.08/0.70    inference(resolution,[],[f136,f52])).
% 1.08/0.70  fof(f136,plain,(
% 1.08/0.70    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_relat_1(X2),k1_zfmisc_1(X1))) )),
% 1.08/0.70    inference(duplicate_literal_removal,[],[f135])).
% 1.08/0.70  fof(f135,plain,(
% 1.08/0.70    ( ! [X2,X0,X1] : (m1_subset_1(k2_relat_1(X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.08/0.70    inference(superposition,[],[f73,f71])).
% 1.08/0.70  fof(f71,plain,(
% 1.08/0.70    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.08/0.70    inference(cnf_transformation,[],[f27])).
% 1.08/0.70  fof(f27,plain,(
% 1.08/0.70    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.08/0.70    inference(ennf_transformation,[],[f13])).
% 1.08/0.70  fof(f13,axiom,(
% 1.08/0.70    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.08/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.08/0.70  fof(f73,plain,(
% 1.08/0.70    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.08/0.70    inference(cnf_transformation,[],[f29])).
% 1.08/0.70  fof(f29,plain,(
% 1.08/0.70    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.08/0.70    inference(ennf_transformation,[],[f11])).
% 1.08/0.70  fof(f11,axiom,(
% 1.08/0.70    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 1.08/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 1.08/0.70  fof(f54,plain,(
% 1.08/0.70    sK1 != k1_funct_1(sK3,sK2)),
% 1.08/0.70    inference(cnf_transformation,[],[f35])).
% 1.08/0.70  fof(f65,plain,(
% 1.08/0.70    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1)) | k1_xboole_0 = X0) )),
% 1.08/0.70    inference(cnf_transformation,[],[f23])).
% 1.08/0.70  fof(f23,plain,(
% 1.08/0.70    ! [X0,X1] : ((k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1)) & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0)) | k1_xboole_0 = X0)),
% 1.08/0.70    inference(ennf_transformation,[],[f6])).
% 1.08/0.70  fof(f6,axiom,(
% 1.08/0.70    ! [X0,X1] : (k1_xboole_0 != X0 => (k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1)) & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0)))),
% 1.08/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_zfmisc_1)).
% 1.08/0.70  fof(f99,plain,(
% 1.08/0.70    ( ! [X4,X0] : (r2_hidden(X4,k2_tarski(X0,X4))) )),
% 1.08/0.70    inference(equality_resolution,[],[f98])).
% 1.08/0.70  fof(f98,plain,(
% 1.08/0.70    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k2_tarski(X0,X4) != X2) )),
% 1.08/0.70    inference(equality_resolution,[],[f83])).
% 1.08/0.70  fof(f83,plain,(
% 1.08/0.70    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 1.08/0.70    inference(cnf_transformation,[],[f49])).
% 1.08/0.70  fof(f378,plain,(
% 1.08/0.70    ~r2_hidden(sK2,k1_xboole_0)),
% 1.08/0.70    inference(backward_demodulation,[],[f189,f300])).
% 1.08/0.70  % SZS output end Proof for theBenchmark
% 1.08/0.70  % (11349)------------------------------
% 1.08/0.70  % (11349)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.08/0.70  % (11349)Termination reason: Refutation
% 1.08/0.70  
% 1.08/0.70  % (11349)Memory used [KB]: 1918
% 1.08/0.70  % (11349)Time elapsed: 0.109 s
% 1.08/0.70  % (11349)------------------------------
% 1.08/0.70  % (11349)------------------------------
% 1.08/0.70  % (11367)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.08/0.70  % (11206)Success in time 0.343 s
%------------------------------------------------------------------------------
