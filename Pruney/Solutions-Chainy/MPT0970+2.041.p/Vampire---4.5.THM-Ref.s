%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:54 EST 2020

% Result     : Theorem 1.19s
% Output     : Refutation 1.19s
% Verified   : 
% Statistics : Number of formulae       :  125 (1144 expanded)
%              Number of leaves         :   25 ( 364 expanded)
%              Depth                    :   22
%              Number of atoms          :  503 (6116 expanded)
%              Number of equality atoms :  140 (1824 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f389,plain,(
    $false ),
    inference(global_subsumption,[],[f329,f388])).

fof(f388,plain,(
    k1_xboole_0 = k2_relset_1(sK3,k1_xboole_0,sK5) ),
    inference(forward_demodulation,[],[f334,f379])).

fof(f379,plain,(
    k1_xboole_0 = k2_relat_1(sK5) ),
    inference(subsumption_resolution,[],[f131,f330])).

fof(f330,plain,(
    v5_relat_1(sK5,k1_xboole_0) ),
    inference(backward_demodulation,[],[f132,f324])).

fof(f324,plain,(
    k1_xboole_0 = sK4 ),
    inference(resolution,[],[f322,f139])).

fof(f139,plain,(
    ! [X0] : sP0(sK5,X0,k9_relat_1(sK5,X0)) ),
    inference(global_subsumption,[],[f116,f138])).

fof(f138,plain,(
    ! [X0] :
      ( sP0(sK5,X0,k9_relat_1(sK5,X0))
      | ~ v1_relat_1(sK5) ) ),
    inference(resolution,[],[f115,f59])).

fof(f59,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( sK4 != k2_relset_1(sK3,sK4,sK5)
    & ! [X3] :
        ( ( k1_funct_1(sK5,sK6(X3)) = X3
          & r2_hidden(sK6(X3),sK3) )
        | ~ r2_hidden(X3,sK4) )
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_2(sK5,sK3,sK4)
    & v1_funct_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f17,f35,f34])).

fof(f34,plain,
    ( ? [X0,X1,X2] :
        ( k2_relset_1(X0,X1,X2) != X1
        & ! [X3] :
            ( ? [X4] :
                ( k1_funct_1(X2,X4) = X3
                & r2_hidden(X4,X0) )
            | ~ r2_hidden(X3,X1) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( sK4 != k2_relset_1(sK3,sK4,sK5)
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(sK5,X4) = X3
              & r2_hidden(X4,sK3) )
          | ~ r2_hidden(X3,sK4) )
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
      & v1_funct_2(sK5,sK3,sK4)
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X3] :
      ( ? [X4] :
          ( k1_funct_1(sK5,X4) = X3
          & r2_hidden(X4,sK3) )
     => ( k1_funct_1(sK5,sK6(X3)) = X3
        & r2_hidden(sK6(X3),sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) != X1
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(X2,X4) = X3
              & r2_hidden(X4,X0) )
          | ~ r2_hidden(X3,X1) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) != X1
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(X2,X4) = X3
              & r2_hidden(X4,X0) )
          | ~ r2_hidden(X3,X1) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ! [X3] :
              ~ ( ! [X4] :
                    ~ ( k1_funct_1(X2,X4) = X3
                      & r2_hidden(X4,X0) )
                & r2_hidden(X3,X1) )
         => k2_relset_1(X0,X1,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ! [X3] :
            ~ ( ! [X4] :
                  ~ ( k1_funct_1(X2,X4) = X3
                    & r2_hidden(X4,X0) )
              & r2_hidden(X3,X1) )
       => k2_relset_1(X0,X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_2)).

fof(f115,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | sP0(X0,X1,k9_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f101,f77])).

fof(f77,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f20,f30,f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( sP0(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( k1_funct_1(X0,X4) = X3
              & r2_hidden(X4,X1)
              & r2_hidden(X4,k1_relat_1(X0)) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> sP0(X0,X1,X2) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_1)).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0)
      | sP0(X0,X1,k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ~ sP0(X0,X1,X2) )
          & ( sP0(X0,X1,X2)
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f116,plain,(
    v1_relat_1(sK5) ),
    inference(resolution,[],[f114,f61])).

fof(f61,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f36])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f66,f78])).

fof(f78,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f322,plain,(
    ! [X0] :
      ( ~ sP0(sK5,sK3,k9_relat_1(sK5,X0))
      | k1_xboole_0 = sK4 ) ),
    inference(global_subsumption,[],[f178,f307])).

fof(f307,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK4
      | ~ sP0(sK5,sK3,k9_relat_1(sK5,X0))
      | sP14(sK5,sK4) ) ),
    inference(resolution,[],[f306,f171])).

fof(f171,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK12(X0,sK5),k9_relat_1(sK5,X1))
      | sP14(sK5,X0) ) ),
    inference(resolution,[],[f170,f112])).

fof(f112,plain,(
    ! [X6,X2,X1] :
      ( ~ r2_hidden(k4_tarski(X6,sK12(X1,X2)),X2)
      | sP14(X2,X1) ) ),
    inference(cnf_transformation,[],[f112_D])).

fof(f112_D,plain,(
    ! [X1,X2] :
      ( ! [X6] : ~ r2_hidden(k4_tarski(X6,sK12(X1,X2)),X2)
    <=> ~ sP14(X2,X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP14])])).

fof(f170,plain,(
    ! [X4,X5] :
      ( r2_hidden(k4_tarski(sK10(X4,X5,sK5),X4),sK5)
      | ~ r2_hidden(X4,k9_relat_1(sK5,X5)) ) ),
    inference(resolution,[],[f85,f116])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(k4_tarski(sK10(X0,X1,X2),X0),X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK10(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK10(X0,X1,X2),X0),X2)
            & r2_hidden(sK10(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f48,f49])).

fof(f49,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK10(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK10(X0,X1,X2),X0),X2)
        & r2_hidden(sK10(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X4,X0),X2)
              & r2_hidden(X4,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X3,X0),X2)
              & r2_hidden(X3,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(f306,plain,(
    ! [X0] :
      ( r2_hidden(sK12(sK4,sK5),X0)
      | k1_xboole_0 = sK4
      | ~ sP0(sK5,sK3,X0) ) ),
    inference(global_subsumption,[],[f262,f305])).

fof(f305,plain,(
    ! [X0] :
      ( ~ sP0(sK5,sK3,X0)
      | k1_xboole_0 = sK4
      | r2_hidden(sK12(sK4,sK5),X0)
      | ~ r2_hidden(sK12(sK4,sK5),sK4) ) ),
    inference(resolution,[],[f270,f62])).

fof(f62,plain,(
    ! [X3] :
      ( r2_hidden(sK6(X3),sK3)
      | ~ r2_hidden(X3,sK4) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f270,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK6(sK12(sK4,sK5)),X1)
      | ~ sP0(sK5,X1,X0)
      | k1_xboole_0 = sK4
      | r2_hidden(sK12(sK4,sK5),X0) ) ),
    inference(backward_demodulation,[],[f263,f266])).

fof(f266,plain,(
    sK12(sK4,sK5) = k1_funct_1(sK5,sK6(sK12(sK4,sK5))) ),
    inference(resolution,[],[f262,f63])).

fof(f63,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK4)
      | k1_funct_1(sK5,sK6(X3)) = X3 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f263,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(sK5,sK6(sK12(sK4,sK5))),X0)
      | ~ sP0(sK5,X1,X0)
      | k1_xboole_0 = sK4
      | ~ r2_hidden(sK6(sK12(sK4,sK5)),X1) ) ),
    inference(resolution,[],[f262,f229])).

fof(f229,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,sK4)
      | r2_hidden(k1_funct_1(sK5,sK6(X0)),X2)
      | ~ sP0(sK5,X1,X2)
      | k1_xboole_0 = sK4
      | ~ r2_hidden(sK6(X0),X1) ) ),
    inference(resolution,[],[f219,f62])).

fof(f219,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(X2,sK3)
      | ~ r2_hidden(X2,X3)
      | r2_hidden(k1_funct_1(sK5,X2),X4)
      | ~ sP0(sK5,X3,X4)
      | k1_xboole_0 = sK4 ) ),
    inference(superposition,[],[f102,f217])).

fof(f217,plain,
    ( sK3 = k1_relat_1(sK5)
    | k1_xboole_0 = sK4 ),
    inference(global_subsumption,[],[f60,f216])).

fof(f216,plain,
    ( sK3 = k1_relat_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK4)
    | k1_xboole_0 = sK4 ),
    inference(forward_demodulation,[],[f215,f149])).

fof(f149,plain,(
    k1_relat_1(sK5) = k1_relset_1(sK3,sK4,sK5) ),
    inference(resolution,[],[f88,f61])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f215,plain,
    ( ~ v1_funct_2(sK5,sK3,sK4)
    | k1_xboole_0 = sK4
    | sK3 = k1_relset_1(sK3,sK4,sK5) ),
    inference(resolution,[],[f91,f137])).

fof(f137,plain,(
    sP2(sK3,sK5,sK4) ),
    inference(resolution,[],[f95,f61])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP2(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP2(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP2(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f27,f32])).

fof(f32,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP2(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | ~ v1_funct_2(X1,X0,X2)
      | k1_xboole_0 = X2
      | k1_relset_1(X0,X2,X1) = X0 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X2 )
      | ~ sP2(X0,X1,X2) ) ),
    inference(rectify,[],[f51])).

fof(f51,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP2(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f60,plain,(
    v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f36])).

fof(f102,plain,(
    ! [X2,X0,X7,X1] :
      ( ~ r2_hidden(X7,k1_relat_1(X0))
      | ~ r2_hidden(X7,X1)
      | r2_hidden(k1_funct_1(X0,X7),X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | k1_funct_1(X0,X7) != X6
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X7,k1_relat_1(X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ! [X4] :
                ( k1_funct_1(X0,X4) != sK7(X0,X1,X2)
                | ~ r2_hidden(X4,X1)
                | ~ r2_hidden(X4,k1_relat_1(X0)) )
            | ~ r2_hidden(sK7(X0,X1,X2),X2) )
          & ( ( sK7(X0,X1,X2) = k1_funct_1(X0,sK8(X0,X1,X2))
              & r2_hidden(sK8(X0,X1,X2),X1)
              & r2_hidden(sK8(X0,X1,X2),k1_relat_1(X0)) )
            | r2_hidden(sK7(X0,X1,X2),X2) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X2)
              | ! [X7] :
                  ( k1_funct_1(X0,X7) != X6
                  | ~ r2_hidden(X7,X1)
                  | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
            & ( ( k1_funct_1(X0,sK9(X0,X1,X6)) = X6
                & r2_hidden(sK9(X0,X1,X6),X1)
                & r2_hidden(sK9(X0,X1,X6),k1_relat_1(X0)) )
              | ~ r2_hidden(X6,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f39,f42,f41,f40])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( k1_funct_1(X0,X4) != X3
                | ~ r2_hidden(X4,X1)
                | ~ r2_hidden(X4,k1_relat_1(X0)) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( k1_funct_1(X0,X5) = X3
                & r2_hidden(X5,X1)
                & r2_hidden(X5,k1_relat_1(X0)) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( k1_funct_1(X0,X4) != sK7(X0,X1,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,k1_relat_1(X0)) )
          | ~ r2_hidden(sK7(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( k1_funct_1(X0,X5) = sK7(X0,X1,X2)
              & r2_hidden(X5,X1)
              & r2_hidden(X5,k1_relat_1(X0)) )
          | r2_hidden(sK7(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( k1_funct_1(X0,X5) = sK7(X0,X1,X2)
          & r2_hidden(X5,X1)
          & r2_hidden(X5,k1_relat_1(X0)) )
     => ( sK7(X0,X1,X2) = k1_funct_1(X0,sK8(X0,X1,X2))
        & r2_hidden(sK8(X0,X1,X2),X1)
        & r2_hidden(sK8(X0,X1,X2),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( k1_funct_1(X0,X8) = X6
          & r2_hidden(X8,X1)
          & r2_hidden(X8,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK9(X0,X1,X6)) = X6
        & r2_hidden(sK9(X0,X1,X6),X1)
        & r2_hidden(sK9(X0,X1,X6),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ! [X4] :
                  ( k1_funct_1(X0,X4) != X3
                  | ~ r2_hidden(X4,X1)
                  | ~ r2_hidden(X4,k1_relat_1(X0)) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X5] :
                  ( k1_funct_1(X0,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X5,k1_relat_1(X0)) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X2)
              | ! [X7] :
                  ( k1_funct_1(X0,X7) != X6
                  | ~ r2_hidden(X7,X1)
                  | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
            & ( ? [X8] :
                  ( k1_funct_1(X0,X8) = X6
                  & r2_hidden(X8,X1)
                  & r2_hidden(X8,k1_relat_1(X0)) )
              | ~ r2_hidden(X6,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ! [X4] :
                  ( k1_funct_1(X0,X4) != X3
                  | ~ r2_hidden(X4,X1)
                  | ~ r2_hidden(X4,k1_relat_1(X0)) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ! [X4] :
                  ( k1_funct_1(X0,X4) != X3
                  | ~ r2_hidden(X4,X1)
                  | ~ r2_hidden(X4,k1_relat_1(X0)) ) )
            & ( ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f262,plain,(
    r2_hidden(sK12(sK4,sK5),sK4) ),
    inference(global_subsumption,[],[f153,f261])).

fof(f261,plain,
    ( sK4 = k2_relat_1(sK5)
    | r2_hidden(sK12(sK4,sK5),sK4) ),
    inference(forward_demodulation,[],[f260,f150])).

fof(f150,plain,(
    k2_relset_1(sK3,sK4,sK5) = k2_relat_1(sK5) ),
    inference(resolution,[],[f89,f61])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

% (20716)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
fof(f260,plain,
    ( r2_hidden(sK12(sK4,sK5),sK4)
    | sK4 = k2_relset_1(sK3,sK4,sK5) ),
    inference(resolution,[],[f98,f61])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_hidden(sK12(X1,X2),X1)
      | k2_relset_1(X0,X1,X2) = X1 ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( r2_hidden(k4_tarski(sK11(X2,X3),X3),X2)
              | ~ r2_hidden(X3,X1) )
          | k2_relset_1(X0,X1,X2) != X1 )
        & ( k2_relset_1(X0,X1,X2) = X1
          | ( ! [X6] : ~ r2_hidden(k4_tarski(X6,sK12(X1,X2)),X2)
            & r2_hidden(sK12(X1,X2),X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11,sK12])],[f55,f57,f56])).

fof(f56,plain,(
    ! [X3,X2] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X3),X2)
     => r2_hidden(k4_tarski(sK11(X2,X3),X3),X2) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X2,X1] :
      ( ? [X5] :
          ( ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X2)
          & r2_hidden(X5,X1) )
     => ( ! [X6] : ~ r2_hidden(k4_tarski(X6,sK12(X1,X2)),X2)
        & r2_hidden(sK12(X1,X2),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( ? [X4] : r2_hidden(k4_tarski(X4,X3),X2)
              | ~ r2_hidden(X3,X1) )
          | k2_relset_1(X0,X1,X2) != X1 )
        & ( k2_relset_1(X0,X1,X2) = X1
          | ? [X5] :
              ( ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X2)
              & r2_hidden(X5,X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(rectify,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( ? [X4] : r2_hidden(k4_tarski(X4,X3),X2)
              | ~ r2_hidden(X3,X1) )
          | k2_relset_1(X0,X1,X2) != X1 )
        & ( k2_relset_1(X0,X1,X2) = X1
          | ? [X3] :
              ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),X2)
              & r2_hidden(X3,X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X4,X3),X2)
            | ~ r2_hidden(X3,X1) )
      <=> k2_relset_1(X0,X1,X2) = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),X2)
              & r2_hidden(X3,X1) )
      <=> k2_relset_1(X0,X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_relset_1)).

fof(f153,plain,(
    sK4 != k2_relat_1(sK5) ),
    inference(superposition,[],[f64,f150])).

fof(f64,plain,(
    sK4 != k2_relset_1(sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f36])).

fof(f178,plain,(
    ~ sP14(sK5,sK4) ),
    inference(global_subsumption,[],[f153,f177])).

fof(f177,plain,
    ( sK4 = k2_relat_1(sK5)
    | ~ sP14(sK5,sK4) ),
    inference(forward_demodulation,[],[f176,f150])).

fof(f176,plain,
    ( sK4 = k2_relset_1(sK3,sK4,sK5)
    | ~ sP14(sK5,sK4) ),
    inference(resolution,[],[f113,f61])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = X1
      | ~ sP14(X2,X1) ) ),
    inference(general_splitting,[],[f99,f112_D])).

fof(f99,plain,(
    ! [X6,X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_hidden(k4_tarski(X6,sK12(X1,X2)),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f58])).

% (20715)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
fof(f132,plain,(
    v5_relat_1(sK5,sK4) ),
    inference(resolution,[],[f90,f61])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f131,plain,
    ( ~ v5_relat_1(sK5,k1_xboole_0)
    | k1_xboole_0 = k2_relat_1(sK5) ),
    inference(resolution,[],[f126,f119])).

fof(f119,plain,(
    ! [X3] :
      ( r1_tarski(k2_relat_1(sK5),X3)
      | ~ v5_relat_1(sK5,X3) ) ),
    inference(resolution,[],[f79,f116])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f126,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f83,f65])).

fof(f65,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

% (20731)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
fof(f46,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
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

fof(f334,plain,(
    k2_relat_1(sK5) = k2_relset_1(sK3,k1_xboole_0,sK5) ),
    inference(backward_demodulation,[],[f150,f324])).

fof(f329,plain,(
    k1_xboole_0 != k2_relset_1(sK3,k1_xboole_0,sK5) ),
    inference(backward_demodulation,[],[f64,f324])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:46:16 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (20724)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.50  % (20723)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.51  % (20722)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.51  % (20720)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.52  % (20733)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.19/0.52  % (20732)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.19/0.52  % (20714)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.19/0.52  % (20726)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.19/0.52  % (20724)Refutation found. Thanks to Tanya!
% 1.19/0.52  % SZS status Theorem for theBenchmark
% 1.19/0.52  % (20725)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.19/0.52  % (20713)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.19/0.52  % SZS output start Proof for theBenchmark
% 1.19/0.52  fof(f389,plain,(
% 1.19/0.52    $false),
% 1.19/0.52    inference(global_subsumption,[],[f329,f388])).
% 1.19/0.52  fof(f388,plain,(
% 1.19/0.52    k1_xboole_0 = k2_relset_1(sK3,k1_xboole_0,sK5)),
% 1.19/0.52    inference(forward_demodulation,[],[f334,f379])).
% 1.19/0.52  fof(f379,plain,(
% 1.19/0.52    k1_xboole_0 = k2_relat_1(sK5)),
% 1.19/0.52    inference(subsumption_resolution,[],[f131,f330])).
% 1.19/0.52  fof(f330,plain,(
% 1.19/0.52    v5_relat_1(sK5,k1_xboole_0)),
% 1.19/0.52    inference(backward_demodulation,[],[f132,f324])).
% 1.19/0.52  fof(f324,plain,(
% 1.19/0.52    k1_xboole_0 = sK4),
% 1.19/0.52    inference(resolution,[],[f322,f139])).
% 1.19/0.52  fof(f139,plain,(
% 1.19/0.52    ( ! [X0] : (sP0(sK5,X0,k9_relat_1(sK5,X0))) )),
% 1.19/0.52    inference(global_subsumption,[],[f116,f138])).
% 1.19/0.52  fof(f138,plain,(
% 1.19/0.52    ( ! [X0] : (sP0(sK5,X0,k9_relat_1(sK5,X0)) | ~v1_relat_1(sK5)) )),
% 1.19/0.52    inference(resolution,[],[f115,f59])).
% 1.19/0.52  fof(f59,plain,(
% 1.19/0.52    v1_funct_1(sK5)),
% 1.19/0.52    inference(cnf_transformation,[],[f36])).
% 1.19/0.52  fof(f36,plain,(
% 1.19/0.52    sK4 != k2_relset_1(sK3,sK4,sK5) & ! [X3] : ((k1_funct_1(sK5,sK6(X3)) = X3 & r2_hidden(sK6(X3),sK3)) | ~r2_hidden(X3,sK4)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5)),
% 1.19/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f17,f35,f34])).
% 1.19/0.52  fof(f34,plain,(
% 1.19/0.52    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (sK4 != k2_relset_1(sK3,sK4,sK5) & ! [X3] : (? [X4] : (k1_funct_1(sK5,X4) = X3 & r2_hidden(X4,sK3)) | ~r2_hidden(X3,sK4)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5))),
% 1.19/0.52    introduced(choice_axiom,[])).
% 1.19/0.52  fof(f35,plain,(
% 1.19/0.52    ! [X3] : (? [X4] : (k1_funct_1(sK5,X4) = X3 & r2_hidden(X4,sK3)) => (k1_funct_1(sK5,sK6(X3)) = X3 & r2_hidden(sK6(X3),sK3)))),
% 1.19/0.52    introduced(choice_axiom,[])).
% 1.19/0.52  fof(f17,plain,(
% 1.19/0.52    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.19/0.52    inference(flattening,[],[f16])).
% 1.19/0.52  fof(f16,plain,(
% 1.19/0.52    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.19/0.52    inference(ennf_transformation,[],[f14])).
% 1.19/0.52  fof(f14,negated_conjecture,(
% 1.19/0.52    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 1.19/0.52    inference(negated_conjecture,[],[f13])).
% 1.19/0.52  fof(f13,conjecture,(
% 1.19/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 1.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_2)).
% 1.19/0.52  fof(f115,plain,(
% 1.19/0.52    ( ! [X0,X1] : (~v1_funct_1(X0) | sP0(X0,X1,k9_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.19/0.52    inference(resolution,[],[f101,f77])).
% 1.19/0.52  fof(f77,plain,(
% 1.19/0.52    ( ! [X0] : (sP1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.19/0.52    inference(cnf_transformation,[],[f31])).
% 1.19/0.52  fof(f31,plain,(
% 1.19/0.52    ! [X0] : (sP1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.19/0.52    inference(definition_folding,[],[f20,f30,f29])).
% 1.19/0.52  fof(f29,plain,(
% 1.19/0.52    ! [X0,X1,X2] : (sP0(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0)))))),
% 1.19/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.19/0.52  fof(f30,plain,(
% 1.19/0.52    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> sP0(X0,X1,X2)) | ~sP1(X0))),
% 1.19/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.19/0.52  fof(f20,plain,(
% 1.19/0.52    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.19/0.52    inference(flattening,[],[f19])).
% 1.19/0.52  fof(f19,plain,(
% 1.19/0.52    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.19/0.52    inference(ennf_transformation,[],[f7])).
% 1.19/0.52  fof(f7,axiom,(
% 1.19/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))))),
% 1.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_1)).
% 1.19/0.52  fof(f101,plain,(
% 1.19/0.52    ( ! [X0,X1] : (~sP1(X0) | sP0(X0,X1,k9_relat_1(X0,X1))) )),
% 1.19/0.52    inference(equality_resolution,[],[f67])).
% 1.19/0.52  fof(f67,plain,(
% 1.19/0.52    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | k9_relat_1(X0,X1) != X2 | ~sP1(X0)) )),
% 1.19/0.52    inference(cnf_transformation,[],[f37])).
% 1.19/0.52  fof(f37,plain,(
% 1.19/0.52    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ~sP0(X0,X1,X2)) & (sP0(X0,X1,X2) | k9_relat_1(X0,X1) != X2)) | ~sP1(X0))),
% 1.19/0.52    inference(nnf_transformation,[],[f30])).
% 1.19/0.52  fof(f116,plain,(
% 1.19/0.52    v1_relat_1(sK5)),
% 1.19/0.52    inference(resolution,[],[f114,f61])).
% 1.19/0.52  fof(f61,plain,(
% 1.19/0.52    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 1.19/0.52    inference(cnf_transformation,[],[f36])).
% 1.19/0.52  fof(f114,plain,(
% 1.19/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0)) )),
% 1.19/0.52    inference(resolution,[],[f66,f78])).
% 1.19/0.52  fof(f78,plain,(
% 1.19/0.52    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.19/0.52    inference(cnf_transformation,[],[f5])).
% 1.19/0.52  fof(f5,axiom,(
% 1.19/0.52    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.19/0.52  fof(f66,plain,(
% 1.19/0.52    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 1.19/0.52    inference(cnf_transformation,[],[f18])).
% 1.19/0.52  fof(f18,plain,(
% 1.19/0.52    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.19/0.52    inference(ennf_transformation,[],[f3])).
% 1.19/0.52  fof(f3,axiom,(
% 1.19/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.19/0.52  fof(f322,plain,(
% 1.19/0.52    ( ! [X0] : (~sP0(sK5,sK3,k9_relat_1(sK5,X0)) | k1_xboole_0 = sK4) )),
% 1.19/0.52    inference(global_subsumption,[],[f178,f307])).
% 1.19/0.52  fof(f307,plain,(
% 1.19/0.52    ( ! [X0] : (k1_xboole_0 = sK4 | ~sP0(sK5,sK3,k9_relat_1(sK5,X0)) | sP14(sK5,sK4)) )),
% 1.19/0.52    inference(resolution,[],[f306,f171])).
% 1.19/0.52  fof(f171,plain,(
% 1.19/0.52    ( ! [X0,X1] : (~r2_hidden(sK12(X0,sK5),k9_relat_1(sK5,X1)) | sP14(sK5,X0)) )),
% 1.19/0.52    inference(resolution,[],[f170,f112])).
% 1.19/0.52  fof(f112,plain,(
% 1.19/0.52    ( ! [X6,X2,X1] : (~r2_hidden(k4_tarski(X6,sK12(X1,X2)),X2) | sP14(X2,X1)) )),
% 1.19/0.52    inference(cnf_transformation,[],[f112_D])).
% 1.19/0.52  fof(f112_D,plain,(
% 1.19/0.52    ( ! [X1,X2] : (( ! [X6] : ~r2_hidden(k4_tarski(X6,sK12(X1,X2)),X2) ) <=> ~sP14(X2,X1)) )),
% 1.19/0.52    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP14])])).
% 1.19/0.52  fof(f170,plain,(
% 1.19/0.52    ( ! [X4,X5] : (r2_hidden(k4_tarski(sK10(X4,X5,sK5),X4),sK5) | ~r2_hidden(X4,k9_relat_1(sK5,X5))) )),
% 1.19/0.52    inference(resolution,[],[f85,f116])).
% 1.19/0.52  fof(f85,plain,(
% 1.19/0.52    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(k4_tarski(sK10(X0,X1,X2),X0),X2)) )),
% 1.19/0.52    inference(cnf_transformation,[],[f50])).
% 1.19/0.52  fof(f50,plain,(
% 1.19/0.52    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK10(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK10(X0,X1,X2),X0),X2) & r2_hidden(sK10(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.19/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f48,f49])).
% 1.19/0.52  fof(f49,plain,(
% 1.19/0.52    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK10(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK10(X0,X1,X2),X0),X2) & r2_hidden(sK10(X0,X1,X2),k1_relat_1(X2))))),
% 1.19/0.52    introduced(choice_axiom,[])).
% 1.19/0.52  fof(f48,plain,(
% 1.19/0.52    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.19/0.52    inference(rectify,[],[f47])).
% 1.19/0.52  fof(f47,plain,(
% 1.19/0.52    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.19/0.52    inference(nnf_transformation,[],[f22])).
% 1.19/0.52  fof(f22,plain,(
% 1.19/0.52    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 1.19/0.52    inference(ennf_transformation,[],[f6])).
% 1.19/0.52  fof(f6,axiom,(
% 1.19/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 1.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).
% 1.19/0.53  fof(f306,plain,(
% 1.19/0.53    ( ! [X0] : (r2_hidden(sK12(sK4,sK5),X0) | k1_xboole_0 = sK4 | ~sP0(sK5,sK3,X0)) )),
% 1.19/0.53    inference(global_subsumption,[],[f262,f305])).
% 1.19/0.53  fof(f305,plain,(
% 1.19/0.53    ( ! [X0] : (~sP0(sK5,sK3,X0) | k1_xboole_0 = sK4 | r2_hidden(sK12(sK4,sK5),X0) | ~r2_hidden(sK12(sK4,sK5),sK4)) )),
% 1.19/0.53    inference(resolution,[],[f270,f62])).
% 1.19/0.53  fof(f62,plain,(
% 1.19/0.53    ( ! [X3] : (r2_hidden(sK6(X3),sK3) | ~r2_hidden(X3,sK4)) )),
% 1.19/0.53    inference(cnf_transformation,[],[f36])).
% 1.19/0.53  fof(f270,plain,(
% 1.19/0.53    ( ! [X0,X1] : (~r2_hidden(sK6(sK12(sK4,sK5)),X1) | ~sP0(sK5,X1,X0) | k1_xboole_0 = sK4 | r2_hidden(sK12(sK4,sK5),X0)) )),
% 1.19/0.53    inference(backward_demodulation,[],[f263,f266])).
% 1.19/0.53  fof(f266,plain,(
% 1.19/0.53    sK12(sK4,sK5) = k1_funct_1(sK5,sK6(sK12(sK4,sK5)))),
% 1.19/0.53    inference(resolution,[],[f262,f63])).
% 1.19/0.53  fof(f63,plain,(
% 1.19/0.53    ( ! [X3] : (~r2_hidden(X3,sK4) | k1_funct_1(sK5,sK6(X3)) = X3) )),
% 1.19/0.53    inference(cnf_transformation,[],[f36])).
% 1.19/0.53  fof(f263,plain,(
% 1.19/0.53    ( ! [X0,X1] : (r2_hidden(k1_funct_1(sK5,sK6(sK12(sK4,sK5))),X0) | ~sP0(sK5,X1,X0) | k1_xboole_0 = sK4 | ~r2_hidden(sK6(sK12(sK4,sK5)),X1)) )),
% 1.19/0.53    inference(resolution,[],[f262,f229])).
% 1.19/0.53  fof(f229,plain,(
% 1.19/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X0,sK4) | r2_hidden(k1_funct_1(sK5,sK6(X0)),X2) | ~sP0(sK5,X1,X2) | k1_xboole_0 = sK4 | ~r2_hidden(sK6(X0),X1)) )),
% 1.19/0.53    inference(resolution,[],[f219,f62])).
% 1.19/0.53  fof(f219,plain,(
% 1.19/0.53    ( ! [X4,X2,X3] : (~r2_hidden(X2,sK3) | ~r2_hidden(X2,X3) | r2_hidden(k1_funct_1(sK5,X2),X4) | ~sP0(sK5,X3,X4) | k1_xboole_0 = sK4) )),
% 1.19/0.53    inference(superposition,[],[f102,f217])).
% 1.19/0.53  fof(f217,plain,(
% 1.19/0.53    sK3 = k1_relat_1(sK5) | k1_xboole_0 = sK4),
% 1.19/0.53    inference(global_subsumption,[],[f60,f216])).
% 1.19/0.53  fof(f216,plain,(
% 1.19/0.53    sK3 = k1_relat_1(sK5) | ~v1_funct_2(sK5,sK3,sK4) | k1_xboole_0 = sK4),
% 1.19/0.53    inference(forward_demodulation,[],[f215,f149])).
% 1.19/0.53  fof(f149,plain,(
% 1.19/0.53    k1_relat_1(sK5) = k1_relset_1(sK3,sK4,sK5)),
% 1.19/0.53    inference(resolution,[],[f88,f61])).
% 1.19/0.53  fof(f88,plain,(
% 1.19/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relat_1(X2) = k1_relset_1(X0,X1,X2)) )),
% 1.19/0.53    inference(cnf_transformation,[],[f23])).
% 1.19/0.53  fof(f23,plain,(
% 1.19/0.53    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.19/0.53    inference(ennf_transformation,[],[f9])).
% 1.19/0.53  fof(f9,axiom,(
% 1.19/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 1.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.19/0.53  fof(f215,plain,(
% 1.19/0.53    ~v1_funct_2(sK5,sK3,sK4) | k1_xboole_0 = sK4 | sK3 = k1_relset_1(sK3,sK4,sK5)),
% 1.19/0.53    inference(resolution,[],[f91,f137])).
% 1.19/0.53  fof(f137,plain,(
% 1.19/0.53    sP2(sK3,sK5,sK4)),
% 1.19/0.53    inference(resolution,[],[f95,f61])).
% 1.19/0.53  fof(f95,plain,(
% 1.19/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP2(X0,X2,X1)) )),
% 1.19/0.53    inference(cnf_transformation,[],[f53])).
% 1.19/0.53  fof(f53,plain,(
% 1.19/0.53    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP2(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.19/0.53    inference(nnf_transformation,[],[f33])).
% 1.19/0.53  fof(f33,plain,(
% 1.19/0.53    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP2(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.19/0.53    inference(definition_folding,[],[f27,f32])).
% 1.19/0.53  fof(f32,plain,(
% 1.19/0.53    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP2(X0,X2,X1))),
% 1.19/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 1.19/0.53  fof(f27,plain,(
% 1.19/0.53    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.19/0.53    inference(flattening,[],[f26])).
% 1.19/0.53  fof(f26,plain,(
% 1.19/0.53    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.19/0.53    inference(ennf_transformation,[],[f12])).
% 1.19/0.53  fof(f12,axiom,(
% 1.19/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.19/0.53  fof(f91,plain,(
% 1.19/0.53    ( ! [X2,X0,X1] : (~sP2(X0,X1,X2) | ~v1_funct_2(X1,X0,X2) | k1_xboole_0 = X2 | k1_relset_1(X0,X2,X1) = X0) )),
% 1.19/0.53    inference(cnf_transformation,[],[f52])).
% 1.19/0.53  fof(f52,plain,(
% 1.19/0.53    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X2) | ~sP2(X0,X1,X2))),
% 1.19/0.53    inference(rectify,[],[f51])).
% 1.19/0.53  fof(f51,plain,(
% 1.19/0.53    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP2(X0,X2,X1))),
% 1.19/0.53    inference(nnf_transformation,[],[f32])).
% 1.19/0.53  fof(f60,plain,(
% 1.19/0.53    v1_funct_2(sK5,sK3,sK4)),
% 1.19/0.53    inference(cnf_transformation,[],[f36])).
% 1.19/0.53  fof(f102,plain,(
% 1.19/0.53    ( ! [X2,X0,X7,X1] : (~r2_hidden(X7,k1_relat_1(X0)) | ~r2_hidden(X7,X1) | r2_hidden(k1_funct_1(X0,X7),X2) | ~sP0(X0,X1,X2)) )),
% 1.19/0.53    inference(equality_resolution,[],[f72])).
% 1.19/0.53  fof(f72,plain,(
% 1.19/0.53    ( ! [X6,X2,X0,X7,X1] : (r2_hidden(X6,X2) | k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)) | ~sP0(X0,X1,X2)) )),
% 1.19/0.53    inference(cnf_transformation,[],[f43])).
% 1.19/0.53  fof(f43,plain,(
% 1.19/0.53    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((! [X4] : (k1_funct_1(X0,X4) != sK7(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK7(X0,X1,X2),X2)) & ((sK7(X0,X1,X2) = k1_funct_1(X0,sK8(X0,X1,X2)) & r2_hidden(sK8(X0,X1,X2),X1) & r2_hidden(sK8(X0,X1,X2),k1_relat_1(X0))) | r2_hidden(sK7(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK9(X0,X1,X6)) = X6 & r2_hidden(sK9(X0,X1,X6),X1) & r2_hidden(sK9(X0,X1,X6),k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | ~sP0(X0,X1,X2)))),
% 1.19/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f39,f42,f41,f40])).
% 1.19/0.53  fof(f40,plain,(
% 1.19/0.53    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2))) => ((! [X4] : (k1_funct_1(X0,X4) != sK7(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK7(X0,X1,X2),X2)) & (? [X5] : (k1_funct_1(X0,X5) = sK7(X0,X1,X2) & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(sK7(X0,X1,X2),X2))))),
% 1.19/0.53    introduced(choice_axiom,[])).
% 1.19/0.53  fof(f41,plain,(
% 1.19/0.53    ! [X2,X1,X0] : (? [X5] : (k1_funct_1(X0,X5) = sK7(X0,X1,X2) & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) => (sK7(X0,X1,X2) = k1_funct_1(X0,sK8(X0,X1,X2)) & r2_hidden(sK8(X0,X1,X2),X1) & r2_hidden(sK8(X0,X1,X2),k1_relat_1(X0))))),
% 1.19/0.53    introduced(choice_axiom,[])).
% 1.19/0.53  fof(f42,plain,(
% 1.19/0.53    ! [X6,X1,X0] : (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) => (k1_funct_1(X0,sK9(X0,X1,X6)) = X6 & r2_hidden(sK9(X0,X1,X6),X1) & r2_hidden(sK9(X0,X1,X6),k1_relat_1(X0))))),
% 1.19/0.53    introduced(choice_axiom,[])).
% 1.19/0.53  fof(f39,plain,(
% 1.19/0.53    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | ~sP0(X0,X1,X2)))),
% 1.19/0.53    inference(rectify,[],[f38])).
% 1.19/0.53  fof(f38,plain,(
% 1.19/0.53    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0)))) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2))) | ~sP0(X0,X1,X2)))),
% 1.19/0.53    inference(nnf_transformation,[],[f29])).
% 1.19/0.53  fof(f262,plain,(
% 1.19/0.53    r2_hidden(sK12(sK4,sK5),sK4)),
% 1.19/0.53    inference(global_subsumption,[],[f153,f261])).
% 1.19/0.53  fof(f261,plain,(
% 1.19/0.53    sK4 = k2_relat_1(sK5) | r2_hidden(sK12(sK4,sK5),sK4)),
% 1.19/0.53    inference(forward_demodulation,[],[f260,f150])).
% 1.19/0.53  fof(f150,plain,(
% 1.19/0.53    k2_relset_1(sK3,sK4,sK5) = k2_relat_1(sK5)),
% 1.19/0.53    inference(resolution,[],[f89,f61])).
% 1.19/0.53  fof(f89,plain,(
% 1.19/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.19/0.53    inference(cnf_transformation,[],[f24])).
% 1.19/0.53  fof(f24,plain,(
% 1.19/0.53    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.19/0.53    inference(ennf_transformation,[],[f10])).
% 1.19/0.53  fof(f10,axiom,(
% 1.19/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.19/0.53  % (20716)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.19/0.53  fof(f260,plain,(
% 1.19/0.53    r2_hidden(sK12(sK4,sK5),sK4) | sK4 = k2_relset_1(sK3,sK4,sK5)),
% 1.19/0.53    inference(resolution,[],[f98,f61])).
% 1.19/0.53  fof(f98,plain,(
% 1.19/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_hidden(sK12(X1,X2),X1) | k2_relset_1(X0,X1,X2) = X1) )),
% 1.19/0.53    inference(cnf_transformation,[],[f58])).
% 1.19/0.53  fof(f58,plain,(
% 1.19/0.53    ! [X0,X1,X2] : (((! [X3] : (r2_hidden(k4_tarski(sK11(X2,X3),X3),X2) | ~r2_hidden(X3,X1)) | k2_relset_1(X0,X1,X2) != X1) & (k2_relset_1(X0,X1,X2) = X1 | (! [X6] : ~r2_hidden(k4_tarski(X6,sK12(X1,X2)),X2) & r2_hidden(sK12(X1,X2),X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.19/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11,sK12])],[f55,f57,f56])).
% 1.19/0.53  fof(f56,plain,(
% 1.19/0.53    ! [X3,X2] : (? [X4] : r2_hidden(k4_tarski(X4,X3),X2) => r2_hidden(k4_tarski(sK11(X2,X3),X3),X2))),
% 1.19/0.53    introduced(choice_axiom,[])).
% 1.19/0.53  fof(f57,plain,(
% 1.19/0.53    ! [X2,X1] : (? [X5] : (! [X6] : ~r2_hidden(k4_tarski(X6,X5),X2) & r2_hidden(X5,X1)) => (! [X6] : ~r2_hidden(k4_tarski(X6,sK12(X1,X2)),X2) & r2_hidden(sK12(X1,X2),X1)))),
% 1.19/0.53    introduced(choice_axiom,[])).
% 1.19/0.53  fof(f55,plain,(
% 1.19/0.53    ! [X0,X1,X2] : (((! [X3] : (? [X4] : r2_hidden(k4_tarski(X4,X3),X2) | ~r2_hidden(X3,X1)) | k2_relset_1(X0,X1,X2) != X1) & (k2_relset_1(X0,X1,X2) = X1 | ? [X5] : (! [X6] : ~r2_hidden(k4_tarski(X6,X5),X2) & r2_hidden(X5,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.19/0.53    inference(rectify,[],[f54])).
% 1.19/0.53  fof(f54,plain,(
% 1.19/0.53    ! [X0,X1,X2] : (((! [X3] : (? [X4] : r2_hidden(k4_tarski(X4,X3),X2) | ~r2_hidden(X3,X1)) | k2_relset_1(X0,X1,X2) != X1) & (k2_relset_1(X0,X1,X2) = X1 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X4,X3),X2) & r2_hidden(X3,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.19/0.53    inference(nnf_transformation,[],[f28])).
% 1.19/0.53  fof(f28,plain,(
% 1.19/0.53    ! [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X4,X3),X2) | ~r2_hidden(X3,X1)) <=> k2_relset_1(X0,X1,X2) = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.19/0.53    inference(ennf_transformation,[],[f11])).
% 1.19/0.53  fof(f11,axiom,(
% 1.19/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X4,X3),X2) & r2_hidden(X3,X1)) <=> k2_relset_1(X0,X1,X2) = X1))),
% 1.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_relset_1)).
% 1.19/0.53  fof(f153,plain,(
% 1.19/0.53    sK4 != k2_relat_1(sK5)),
% 1.19/0.53    inference(superposition,[],[f64,f150])).
% 1.19/0.53  fof(f64,plain,(
% 1.19/0.53    sK4 != k2_relset_1(sK3,sK4,sK5)),
% 1.19/0.53    inference(cnf_transformation,[],[f36])).
% 1.19/0.53  fof(f178,plain,(
% 1.19/0.53    ~sP14(sK5,sK4)),
% 1.19/0.53    inference(global_subsumption,[],[f153,f177])).
% 1.19/0.53  fof(f177,plain,(
% 1.19/0.53    sK4 = k2_relat_1(sK5) | ~sP14(sK5,sK4)),
% 1.19/0.53    inference(forward_demodulation,[],[f176,f150])).
% 1.19/0.53  fof(f176,plain,(
% 1.19/0.53    sK4 = k2_relset_1(sK3,sK4,sK5) | ~sP14(sK5,sK4)),
% 1.19/0.53    inference(resolution,[],[f113,f61])).
% 1.19/0.53  fof(f113,plain,(
% 1.19/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = X1 | ~sP14(X2,X1)) )),
% 1.19/0.53    inference(general_splitting,[],[f99,f112_D])).
% 1.19/0.53  fof(f99,plain,(
% 1.19/0.53    ( ! [X6,X2,X0,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_hidden(k4_tarski(X6,sK12(X1,X2)),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.19/0.53    inference(cnf_transformation,[],[f58])).
% 1.19/0.53  % (20715)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.19/0.53  fof(f132,plain,(
% 1.19/0.53    v5_relat_1(sK5,sK4)),
% 1.19/0.53    inference(resolution,[],[f90,f61])).
% 1.19/0.53  fof(f90,plain,(
% 1.19/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.19/0.53    inference(cnf_transformation,[],[f25])).
% 1.19/0.53  fof(f25,plain,(
% 1.19/0.53    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.19/0.53    inference(ennf_transformation,[],[f15])).
% 1.19/0.53  fof(f15,plain,(
% 1.19/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 1.19/0.53    inference(pure_predicate_removal,[],[f8])).
% 1.19/0.53  fof(f8,axiom,(
% 1.19/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.19/0.53  fof(f131,plain,(
% 1.19/0.53    ~v5_relat_1(sK5,k1_xboole_0) | k1_xboole_0 = k2_relat_1(sK5)),
% 1.19/0.53    inference(resolution,[],[f126,f119])).
% 1.19/0.53  fof(f119,plain,(
% 1.19/0.53    ( ! [X3] : (r1_tarski(k2_relat_1(sK5),X3) | ~v5_relat_1(sK5,X3)) )),
% 1.19/0.53    inference(resolution,[],[f79,f116])).
% 1.19/0.53  fof(f79,plain,(
% 1.19/0.53    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0)) )),
% 1.19/0.53    inference(cnf_transformation,[],[f44])).
% 1.19/0.53  fof(f44,plain,(
% 1.19/0.53    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.19/0.53    inference(nnf_transformation,[],[f21])).
% 1.19/0.53  fof(f21,plain,(
% 1.19/0.53    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.19/0.53    inference(ennf_transformation,[],[f4])).
% 1.19/0.53  fof(f4,axiom,(
% 1.19/0.53    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 1.19/0.53  fof(f126,plain,(
% 1.19/0.53    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.19/0.53    inference(resolution,[],[f83,f65])).
% 1.19/0.53  fof(f65,plain,(
% 1.19/0.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.19/0.53    inference(cnf_transformation,[],[f2])).
% 1.19/0.53  fof(f2,axiom,(
% 1.19/0.53    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.19/0.53  fof(f83,plain,(
% 1.19/0.53    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.19/0.53    inference(cnf_transformation,[],[f46])).
% 1.19/0.53  % (20731)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.19/0.53  fof(f46,plain,(
% 1.19/0.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.19/0.53    inference(flattening,[],[f45])).
% 1.19/0.53  fof(f45,plain,(
% 1.19/0.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.19/0.53    inference(nnf_transformation,[],[f1])).
% 1.19/0.53  fof(f1,axiom,(
% 1.19/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.19/0.53  fof(f334,plain,(
% 1.19/0.53    k2_relat_1(sK5) = k2_relset_1(sK3,k1_xboole_0,sK5)),
% 1.19/0.53    inference(backward_demodulation,[],[f150,f324])).
% 1.19/0.53  fof(f329,plain,(
% 1.19/0.53    k1_xboole_0 != k2_relset_1(sK3,k1_xboole_0,sK5)),
% 1.19/0.53    inference(backward_demodulation,[],[f64,f324])).
% 1.19/0.53  % SZS output end Proof for theBenchmark
% 1.19/0.53  % (20724)------------------------------
% 1.19/0.53  % (20724)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.19/0.53  % (20724)Termination reason: Refutation
% 1.19/0.53  
% 1.19/0.53  % (20724)Memory used [KB]: 6780
% 1.19/0.53  % (20724)Time elapsed: 0.084 s
% 1.19/0.53  % (20724)------------------------------
% 1.19/0.53  % (20724)------------------------------
% 1.19/0.53  % (20703)Success in time 0.165 s
%------------------------------------------------------------------------------
