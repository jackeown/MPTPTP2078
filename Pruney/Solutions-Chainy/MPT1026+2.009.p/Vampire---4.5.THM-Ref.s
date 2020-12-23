%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:31 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  149 (14155 expanded)
%              Number of leaves         :   21 (4343 expanded)
%              Depth                    :   55
%              Number of atoms          :  542 (73893 expanded)
%              Number of equality atoms :   73 (13436 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f598,plain,(
    $false ),
    inference(subsumption_resolution,[],[f597,f108])).

fof(f108,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f597,plain,(
    ~ r1_tarski(sK4,sK4) ),
    inference(forward_demodulation,[],[f596,f136])).

fof(f136,plain,(
    sK4 = k1_relat_1(sK6) ),
    inference(forward_demodulation,[],[f135,f125])).

fof(f125,plain,(
    sK6 = sK13(sK5,sK4,sK6) ),
    inference(resolution,[],[f122,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | sK13(X0,X1,X2) = X2 ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ! [X3] :
            ( ~ r1_tarski(k2_relat_1(X3),X0)
            | k1_relat_1(X3) != X1
            | X2 != X3
            | ~ v1_funct_1(X3)
            | ~ v1_relat_1(X3) ) )
      & ( ( r1_tarski(k2_relat_1(sK13(X0,X1,X2)),X0)
          & k1_relat_1(sK13(X0,X1,X2)) = X1
          & sK13(X0,X1,X2) = X2
          & v1_funct_1(sK13(X0,X1,X2))
          & v1_relat_1(sK13(X0,X1,X2)) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13])],[f60,f61])).

fof(f61,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r1_tarski(k2_relat_1(X4),X0)
          & k1_relat_1(X4) = X1
          & X2 = X4
          & v1_funct_1(X4)
          & v1_relat_1(X4) )
     => ( r1_tarski(k2_relat_1(sK13(X0,X1,X2)),X0)
        & k1_relat_1(sK13(X0,X1,X2)) = X1
        & sK13(X0,X1,X2) = X2
        & v1_funct_1(sK13(X0,X1,X2))
        & v1_relat_1(sK13(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ! [X3] :
            ( ~ r1_tarski(k2_relat_1(X3),X0)
            | k1_relat_1(X3) != X1
            | X2 != X3
            | ~ v1_funct_1(X3)
            | ~ v1_relat_1(X3) ) )
      & ( ? [X4] :
            ( r1_tarski(k2_relat_1(X4),X0)
            & k1_relat_1(X4) = X1
            & X2 = X4
            & v1_funct_1(X4)
            & v1_relat_1(X4) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(rectify,[],[f59])).

fof(f59,plain,(
    ! [X1,X0,X3] :
      ( ( sP2(X1,X0,X3)
        | ! [X4] :
            ( ~ r1_tarski(k2_relat_1(X4),X1)
            | k1_relat_1(X4) != X0
            | X3 != X4
            | ~ v1_funct_1(X4)
            | ~ v1_relat_1(X4) ) )
      & ( ? [X4] :
            ( r1_tarski(k2_relat_1(X4),X1)
            & k1_relat_1(X4) = X0
            & X3 = X4
            & v1_funct_1(X4)
            & v1_relat_1(X4) )
        | ~ sP2(X1,X0,X3) ) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X1,X0,X3] :
      ( sP2(X1,X0,X3)
    <=> ? [X4] :
          ( r1_tarski(k2_relat_1(X4),X1)
          & k1_relat_1(X4) = X0
          & X3 = X4
          & v1_funct_1(X4)
          & v1_relat_1(X4) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f122,plain,(
    sP2(sK5,sK4,sK6) ),
    inference(resolution,[],[f121,f64])).

fof(f64,plain,(
    r2_hidden(sK6,k1_funct_2(sK4,sK5)) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
      | ~ v1_funct_2(sK6,sK4,sK5)
      | ~ v1_funct_1(sK6) )
    & r2_hidden(sK6,k1_funct_2(sK4,sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f16,f37])).

fof(f37,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2) )
        & r2_hidden(X2,k1_funct_2(X0,X1)) )
   => ( ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
        | ~ v1_funct_2(sK6,sK4,sK5)
        | ~ v1_funct_1(sK6) )
      & r2_hidden(sK6,k1_funct_2(sK4,sK5)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2) )
      & r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X2,k1_funct_2(X0,X1))
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
     => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_2)).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_funct_2(X1,X2))
      | sP2(X2,X1,X0) ) ),
    inference(resolution,[],[f94,f112])).

fof(f112,plain,(
    ! [X0,X1] : sP3(X0,X1,k1_funct_2(X0,X1)) ),
    inference(equality_resolution,[],[f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( sP3(X0,X1,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( ( k1_funct_2(X0,X1) = X2
        | ~ sP3(X0,X1,X2) )
      & ( sP3(X0,X1,X2)
        | k1_funct_2(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_2(X0,X1) = X2
    <=> sP3(X0,X1,X2) ) ),
    inference(definition_folding,[],[f12,f35,f34])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( sP3(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP2(X1,X0,X3) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( k1_funct_2(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r1_tarski(k2_relat_1(X4),X1)
              & k1_relat_1(X4) = X0
              & X3 = X4
              & v1_funct_1(X4)
              & v1_relat_1(X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_funct_2)).

fof(f94,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP3(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | sP2(X1,X0,X4) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ( ( ~ sP2(X1,X0,sK12(X0,X1,X2))
            | ~ r2_hidden(sK12(X0,X1,X2),X2) )
          & ( sP2(X1,X0,sK12(X0,X1,X2))
            | r2_hidden(sK12(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP2(X1,X0,X4) )
            & ( sP2(X1,X0,X4)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f56,f57])).

fof(f57,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ sP2(X1,X0,X3)
            | ~ r2_hidden(X3,X2) )
          & ( sP2(X1,X0,X3)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ sP2(X1,X0,sK12(X0,X1,X2))
          | ~ r2_hidden(sK12(X0,X1,X2),X2) )
        & ( sP2(X1,X0,sK12(X0,X1,X2))
          | r2_hidden(sK12(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP2(X1,X0,X3)
              | ~ r2_hidden(X3,X2) )
            & ( sP2(X1,X0,X3)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP2(X1,X0,X4) )
            & ( sP2(X1,X0,X4)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(rectify,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP2(X1,X0,X3)
              | ~ r2_hidden(X3,X2) )
            & ( sP2(X1,X0,X3)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ sP2(X1,X0,X3) )
            & ( sP2(X1,X0,X3)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f135,plain,(
    sK4 = k1_relat_1(sK13(sK5,sK4,sK6)) ),
    inference(resolution,[],[f101,f122])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | k1_relat_1(sK13(X0,X1,X2)) = X1 ) ),
    inference(cnf_transformation,[],[f62])).

fof(f596,plain,(
    ~ r1_tarski(k1_relat_1(sK6),sK4) ),
    inference(subsumption_resolution,[],[f595,f418])).

fof(f418,plain,(
    r1_tarski(sK4,sK5) ),
    inference(backward_demodulation,[],[f145,f410])).

fof(f410,plain,(
    sK4 = k2_relat_1(sK6) ),
    inference(resolution,[],[f408,f148])).

fof(f148,plain,(
    ! [X0] :
      ( ~ sP0(sK6,X0)
      | k2_relat_1(sK6) = X0 ) ),
    inference(subsumption_resolution,[],[f147,f130])).

fof(f130,plain,(
    v1_funct_1(sK6) ),
    inference(subsumption_resolution,[],[f129,f122])).

fof(f129,plain,
    ( v1_funct_1(sK6)
    | ~ sP2(sK5,sK4,sK6) ),
    inference(superposition,[],[f99,f125])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(sK13(X0,X1,X2))
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f147,plain,(
    ! [X0] :
      ( k2_relat_1(sK6) = X0
      | ~ v1_funct_1(sK6)
      | ~ sP0(sK6,X0) ) ),
    inference(resolution,[],[f117,f127])).

fof(f127,plain,(
    v1_relat_1(sK6) ),
    inference(forward_demodulation,[],[f126,f125])).

fof(f126,plain,(
    v1_relat_1(sK13(sK5,sK4,sK6)) ),
    inference(resolution,[],[f122,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | v1_relat_1(sK13(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f117,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(X0) = X1
      | ~ v1_funct_1(X0)
      | ~ sP0(X0,X1) ) ),
    inference(resolution,[],[f71,f78])).

fof(f78,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f21,f32,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( k1_funct_1(X0,X3) = X2
              & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> sP0(X0,X1) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0)
      | ~ sP0(X0,X1)
      | k2_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ~ sP0(X0,X1) )
          & ( sP0(X0,X1)
            | k2_relat_1(X0) != X1 ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f408,plain,(
    sP0(sK6,sK4) ),
    inference(resolution,[],[f367,f366])).

fof(f366,plain,(
    ! [X2] : ~ r2_hidden(X2,sK4) ),
    inference(resolution,[],[f350,f79])).

fof(f79,plain,(
    ! [X2,X0] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK10(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f47,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK10(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f350,plain,(
    v1_xboole_0(sK4) ),
    inference(subsumption_resolution,[],[f349,f108])).

fof(f349,plain,
    ( ~ r1_tarski(sK4,sK4)
    | v1_xboole_0(sK4) ),
    inference(forward_demodulation,[],[f348,f136])).

fof(f348,plain,
    ( v1_xboole_0(sK4)
    | ~ r1_tarski(k1_relat_1(sK6),sK4) ),
    inference(subsumption_resolution,[],[f347,f127])).

fof(f347,plain,
    ( v1_xboole_0(sK4)
    | ~ r1_tarski(k1_relat_1(sK6),sK4)
    | ~ v1_relat_1(sK6) ),
    inference(subsumption_resolution,[],[f345,f145])).

fof(f345,plain,
    ( v1_xboole_0(sK4)
    | ~ r1_tarski(k2_relat_1(sK6),sK5)
    | ~ r1_tarski(k1_relat_1(sK6),sK4)
    | ~ v1_relat_1(sK6) ),
    inference(resolution,[],[f343,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(f343,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | v1_xboole_0(sK4) ),
    inference(resolution,[],[f342,f131])).

fof(f131,plain,
    ( ~ v1_funct_2(sK6,sK4,sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(subsumption_resolution,[],[f65,f130])).

fof(f65,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | ~ v1_funct_2(sK6,sK4,sK5)
    | ~ v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f38])).

fof(f342,plain,
    ( v1_funct_2(sK6,sK4,sK5)
    | v1_xboole_0(sK4) ),
    inference(resolution,[],[f339,f145])).

fof(f339,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK6),X0)
      | v1_xboole_0(sK4)
      | v1_funct_2(sK6,sK4,X0) ) ),
    inference(subsumption_resolution,[],[f338,f108])).

fof(f338,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK4,sK4)
      | v1_funct_2(sK6,sK4,X0)
      | v1_xboole_0(sK4)
      | ~ r1_tarski(k2_relat_1(sK6),X0) ) ),
    inference(forward_demodulation,[],[f337,f136])).

fof(f337,plain,(
    ! [X0] :
      ( v1_funct_2(sK6,sK4,X0)
      | v1_xboole_0(sK4)
      | ~ r1_tarski(k2_relat_1(sK6),X0)
      | ~ r1_tarski(k1_relat_1(sK6),sK4) ) ),
    inference(subsumption_resolution,[],[f335,f127])).

fof(f335,plain,(
    ! [X0] :
      ( v1_funct_2(sK6,sK4,X0)
      | v1_xboole_0(sK4)
      | ~ r1_tarski(k2_relat_1(sK6),X0)
      | ~ r1_tarski(k1_relat_1(sK6),sK4)
      | ~ v1_relat_1(sK6) ) ),
    inference(resolution,[],[f300,f91])).

fof(f300,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,X0)))
      | v1_funct_2(sK6,sK4,X0)
      | v1_xboole_0(sK4) ) ),
    inference(subsumption_resolution,[],[f299,f130])).

fof(f299,plain,(
    ! [X0] :
      ( v1_xboole_0(sK4)
      | v1_funct_2(sK6,sK4,X0)
      | ~ v1_funct_1(sK6)
      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,X0))) ) ),
    inference(resolution,[],[f296,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_partfun1(X2,X0)
      | v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).

fof(f296,plain,
    ( v1_partfun1(sK6,sK4)
    | v1_xboole_0(sK4) ),
    inference(resolution,[],[f289,f80])).

fof(f80,plain,(
    ! [X0] :
      ( r2_hidden(sK10(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f289,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK4)
      | v1_partfun1(sK6,sK4) ) ),
    inference(subsumption_resolution,[],[f288,f127])).

fof(f288,plain,(
    ! [X0] :
      ( v1_partfun1(sK6,sK4)
      | ~ r2_hidden(X0,sK4)
      | ~ v1_relat_1(sK6) ) ),
    inference(subsumption_resolution,[],[f287,f130])).

fof(f287,plain,(
    ! [X0] :
      ( v1_partfun1(sK6,sK4)
      | ~ r2_hidden(X0,sK4)
      | ~ v1_funct_1(sK6)
      | ~ v1_relat_1(sK6) ) ),
    inference(resolution,[],[f286,f78])).

fof(f286,plain,(
    ! [X0] :
      ( ~ sP1(sK6)
      | v1_partfun1(sK6,sK4)
      | ~ r2_hidden(X0,sK4) ) ),
    inference(forward_demodulation,[],[f285,f136])).

fof(f285,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK6))
      | v1_partfun1(sK6,sK4)
      | ~ sP1(sK6) ) ),
    inference(resolution,[],[f279,f106])).

fof(f106,plain,(
    ! [X0] :
      ( sP0(X0,k2_relat_1(X0))
      | ~ sP1(X0) ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | k2_relat_1(X0) != X1
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f279,plain,(
    ! [X0,X1] :
      ( ~ sP0(X1,k2_relat_1(sK6))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | v1_partfun1(sK6,sK4) ) ),
    inference(resolution,[],[f278,f107])).

fof(f107,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ sP0(X0,X1) ) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ( ! [X3] :
                ( k1_funct_1(X0,X3) != sK7(X0,X1)
                | ~ r2_hidden(X3,k1_relat_1(X0)) )
            | ~ r2_hidden(sK7(X0,X1),X1) )
          & ( ( sK7(X0,X1) = k1_funct_1(X0,sK8(X0,X1))
              & r2_hidden(sK8(X0,X1),k1_relat_1(X0)) )
            | r2_hidden(sK7(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( k1_funct_1(X0,X6) != X5
                  | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
            & ( ( k1_funct_1(X0,sK9(X0,X5)) = X5
                & r2_hidden(sK9(X0,X5),k1_relat_1(X0)) )
              | ~ r2_hidden(X5,X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f41,f44,f43,f42])).

fof(f42,plain,(
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
              ( k1_funct_1(X0,X3) != sK7(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK7(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK7(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK7(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = sK7(X0,X1)
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( sK7(X0,X1) = k1_funct_1(X0,sK8(X0,X1))
        & r2_hidden(sK8(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK9(X0,X5)) = X5
        & r2_hidden(sK9(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
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
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
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
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f278,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k2_relat_1(sK6))
      | v1_partfun1(sK6,sK4) ) ),
    inference(resolution,[],[f273,f79])).

fof(f273,plain,
    ( v1_xboole_0(k2_relat_1(sK6))
    | v1_partfun1(sK6,sK4) ),
    inference(subsumption_resolution,[],[f271,f152])).

fof(f152,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,k2_relat_1(sK6)))) ),
    inference(forward_demodulation,[],[f151,f136])).

fof(f151,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),k2_relat_1(sK6)))) ),
    inference(subsumption_resolution,[],[f150,f130])).

fof(f150,plain,
    ( ~ v1_funct_1(sK6)
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),k2_relat_1(sK6)))) ),
    inference(resolution,[],[f69,f127])).

fof(f69,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(f271,plain,
    ( v1_partfun1(sK6,sK4)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,k2_relat_1(sK6))))
    | v1_xboole_0(k2_relat_1(sK6)) ),
    inference(resolution,[],[f270,f142])).

fof(f142,plain,(
    v1_funct_2(sK6,sK4,k2_relat_1(sK6)) ),
    inference(subsumption_resolution,[],[f141,f127])).

fof(f141,plain,
    ( v1_funct_2(sK6,sK4,k2_relat_1(sK6))
    | ~ v1_relat_1(sK6) ),
    inference(subsumption_resolution,[],[f140,f130])).

fof(f140,plain,
    ( v1_funct_2(sK6,sK4,k2_relat_1(sK6))
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6) ),
    inference(superposition,[],[f68,f136])).

fof(f68,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f270,plain,(
    ! [X6,X5] :
      ( ~ v1_funct_2(sK6,X5,X6)
      | v1_partfun1(sK6,X5)
      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | v1_xboole_0(X6) ) ),
    inference(resolution,[],[f83,f130])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f367,plain,(
    ! [X0] :
      ( r2_hidden(sK7(sK6,X0),X0)
      | sP0(sK6,X0) ) ),
    inference(subsumption_resolution,[],[f190,f366])).

fof(f190,plain,(
    ! [X0] :
      ( r2_hidden(sK8(sK6,X0),sK4)
      | r2_hidden(sK7(sK6,X0),X0)
      | sP0(sK6,X0) ) ),
    inference(superposition,[],[f75,f136])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK8(X0,X1),k1_relat_1(X0))
      | r2_hidden(sK7(X0,X1),X1)
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f145,plain,(
    r1_tarski(k2_relat_1(sK6),sK5) ),
    inference(forward_demodulation,[],[f144,f125])).

fof(f144,plain,(
    r1_tarski(k2_relat_1(sK13(sK5,sK4,sK6)),sK5) ),
    inference(resolution,[],[f102,f122])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | r1_tarski(k2_relat_1(sK13(X0,X1,X2)),X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f595,plain,
    ( ~ r1_tarski(sK4,sK5)
    | ~ r1_tarski(k1_relat_1(sK6),sK4) ),
    inference(forward_demodulation,[],[f594,f410])).

fof(f594,plain,
    ( ~ r1_tarski(k2_relat_1(sK6),sK5)
    | ~ r1_tarski(k1_relat_1(sK6),sK4) ),
    inference(subsumption_resolution,[],[f592,f127])).

fof(f592,plain,
    ( ~ r1_tarski(k2_relat_1(sK6),sK5)
    | ~ r1_tarski(k1_relat_1(sK6),sK4)
    | ~ v1_relat_1(sK6) ),
    inference(resolution,[],[f591,f91])).

fof(f591,plain,(
    ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(subsumption_resolution,[],[f589,f418])).

fof(f589,plain,
    ( ~ r1_tarski(sK4,sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(resolution,[],[f588,f131])).

fof(f588,plain,(
    ! [X0] :
      ( v1_funct_2(sK6,sK4,X0)
      | ~ r1_tarski(sK4,X0) ) ),
    inference(subsumption_resolution,[],[f587,f108])).

fof(f587,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK4,sK4)
      | ~ r1_tarski(sK4,X0)
      | v1_funct_2(sK6,sK4,X0) ) ),
    inference(forward_demodulation,[],[f586,f136])).

fof(f586,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK4,X0)
      | v1_funct_2(sK6,sK4,X0)
      | ~ r1_tarski(k1_relat_1(sK6),sK4) ) ),
    inference(forward_demodulation,[],[f585,f410])).

fof(f585,plain,(
    ! [X0] :
      ( v1_funct_2(sK6,sK4,X0)
      | ~ r1_tarski(k2_relat_1(sK6),X0)
      | ~ r1_tarski(k1_relat_1(sK6),sK4) ) ),
    inference(subsumption_resolution,[],[f583,f127])).

fof(f583,plain,(
    ! [X0] :
      ( v1_funct_2(sK6,sK4,X0)
      | ~ r1_tarski(k2_relat_1(sK6),X0)
      | ~ r1_tarski(k1_relat_1(sK6),sK4)
      | ~ v1_relat_1(sK6) ) ),
    inference(resolution,[],[f540,f91])).

fof(f540,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,X0)))
      | v1_funct_2(sK6,sK4,X0) ) ),
    inference(subsumption_resolution,[],[f539,f130])).

fof(f539,plain,(
    ! [X0] :
      ( v1_funct_2(sK6,sK4,X0)
      | ~ v1_funct_1(sK6)
      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,X0))) ) ),
    inference(resolution,[],[f538,f93])).

fof(f538,plain,(
    v1_partfun1(sK6,sK4) ),
    inference(resolution,[],[f365,f421])).

fof(f421,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) ),
    inference(backward_demodulation,[],[f152,f410])).

fof(f365,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK4,X1)))
      | v1_partfun1(X0,sK4) ) ),
    inference(resolution,[],[f350,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_partfun1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:04:59 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (3132)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.51  % (3125)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.51  % (3145)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.51  % (3126)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (3136)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.51  % (3128)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.51  % (3129)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.52  % (3133)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.52  % (3137)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.52  % (3128)Refutation not found, incomplete strategy% (3128)------------------------------
% 0.21/0.52  % (3128)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (3128)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (3128)Memory used [KB]: 10618
% 0.21/0.52  % (3128)Time elapsed: 0.065 s
% 0.21/0.52  % (3128)------------------------------
% 0.21/0.52  % (3128)------------------------------
% 0.21/0.52  % (3134)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.52  % (3143)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.53  % (3131)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.53  % (3123)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (3139)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.53  % (3122)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.53  % (3141)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.53  % (3123)Refutation not found, incomplete strategy% (3123)------------------------------
% 0.21/0.53  % (3123)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (3123)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (3123)Memory used [KB]: 10618
% 0.21/0.53  % (3123)Time elapsed: 0.115 s
% 0.21/0.53  % (3123)------------------------------
% 0.21/0.53  % (3123)------------------------------
% 0.21/0.53  % (3127)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.53  % (3122)Refutation not found, incomplete strategy% (3122)------------------------------
% 0.21/0.53  % (3122)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (3122)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (3122)Memory used [KB]: 10746
% 0.21/0.53  % (3122)Time elapsed: 0.115 s
% 0.21/0.53  % (3122)------------------------------
% 0.21/0.53  % (3122)------------------------------
% 0.21/0.53  % (3127)Refutation not found, incomplete strategy% (3127)------------------------------
% 0.21/0.53  % (3127)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (3127)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (3127)Memory used [KB]: 6140
% 0.21/0.53  % (3127)Time elapsed: 0.118 s
% 0.21/0.53  % (3127)------------------------------
% 0.21/0.53  % (3127)------------------------------
% 0.21/0.54  % (3147)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.54  % (3130)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.54  % (3135)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (3142)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.54  % (3135)Refutation not found, incomplete strategy% (3135)------------------------------
% 0.21/0.54  % (3135)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (3135)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (3135)Memory used [KB]: 6268
% 0.21/0.54  % (3135)Time elapsed: 0.132 s
% 0.21/0.54  % (3135)------------------------------
% 0.21/0.54  % (3135)------------------------------
% 0.21/0.54  % (3146)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.54  % (3144)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.54  % (3124)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.55  % (3125)Refutation found. Thanks to Tanya!
% 0.21/0.55  % SZS status Theorem for theBenchmark
% 0.21/0.55  % SZS output start Proof for theBenchmark
% 0.21/0.55  fof(f598,plain,(
% 0.21/0.55    $false),
% 0.21/0.55    inference(subsumption_resolution,[],[f597,f108])).
% 0.21/0.55  fof(f108,plain,(
% 0.21/0.55    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.55    inference(equality_resolution,[],[f87])).
% 0.21/0.55  fof(f87,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.55    inference(cnf_transformation,[],[f53])).
% 0.21/0.55  fof(f53,plain,(
% 0.21/0.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.55    inference(flattening,[],[f52])).
% 0.21/0.55  fof(f52,plain,(
% 0.21/0.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.55    inference(nnf_transformation,[],[f2])).
% 0.21/0.55  fof(f2,axiom,(
% 0.21/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.55  fof(f597,plain,(
% 0.21/0.55    ~r1_tarski(sK4,sK4)),
% 0.21/0.55    inference(forward_demodulation,[],[f596,f136])).
% 0.21/0.55  fof(f136,plain,(
% 0.21/0.55    sK4 = k1_relat_1(sK6)),
% 0.21/0.55    inference(forward_demodulation,[],[f135,f125])).
% 0.21/0.55  fof(f125,plain,(
% 0.21/0.55    sK6 = sK13(sK5,sK4,sK6)),
% 0.21/0.55    inference(resolution,[],[f122,f100])).
% 0.21/0.55  fof(f100,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~sP2(X0,X1,X2) | sK13(X0,X1,X2) = X2) )),
% 0.21/0.55    inference(cnf_transformation,[],[f62])).
% 0.21/0.55  fof(f62,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ! [X3] : (~r1_tarski(k2_relat_1(X3),X0) | k1_relat_1(X3) != X1 | X2 != X3 | ~v1_funct_1(X3) | ~v1_relat_1(X3))) & ((r1_tarski(k2_relat_1(sK13(X0,X1,X2)),X0) & k1_relat_1(sK13(X0,X1,X2)) = X1 & sK13(X0,X1,X2) = X2 & v1_funct_1(sK13(X0,X1,X2)) & v1_relat_1(sK13(X0,X1,X2))) | ~sP2(X0,X1,X2)))),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13])],[f60,f61])).
% 0.21/0.55  fof(f61,plain,(
% 0.21/0.55    ! [X2,X1,X0] : (? [X4] : (r1_tarski(k2_relat_1(X4),X0) & k1_relat_1(X4) = X1 & X2 = X4 & v1_funct_1(X4) & v1_relat_1(X4)) => (r1_tarski(k2_relat_1(sK13(X0,X1,X2)),X0) & k1_relat_1(sK13(X0,X1,X2)) = X1 & sK13(X0,X1,X2) = X2 & v1_funct_1(sK13(X0,X1,X2)) & v1_relat_1(sK13(X0,X1,X2))))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f60,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ! [X3] : (~r1_tarski(k2_relat_1(X3),X0) | k1_relat_1(X3) != X1 | X2 != X3 | ~v1_funct_1(X3) | ~v1_relat_1(X3))) & (? [X4] : (r1_tarski(k2_relat_1(X4),X0) & k1_relat_1(X4) = X1 & X2 = X4 & v1_funct_1(X4) & v1_relat_1(X4)) | ~sP2(X0,X1,X2)))),
% 0.21/0.55    inference(rectify,[],[f59])).
% 0.21/0.55  fof(f59,plain,(
% 0.21/0.55    ! [X1,X0,X3] : ((sP2(X1,X0,X3) | ! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4))) & (? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4)) | ~sP2(X1,X0,X3)))),
% 0.21/0.55    inference(nnf_transformation,[],[f34])).
% 0.21/0.55  fof(f34,plain,(
% 0.21/0.55    ! [X1,X0,X3] : (sP2(X1,X0,X3) <=> ? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4)))),
% 0.21/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.21/0.55  fof(f122,plain,(
% 0.21/0.55    sP2(sK5,sK4,sK6)),
% 0.21/0.55    inference(resolution,[],[f121,f64])).
% 0.21/0.55  fof(f64,plain,(
% 0.21/0.55    r2_hidden(sK6,k1_funct_2(sK4,sK5))),
% 0.21/0.55    inference(cnf_transformation,[],[f38])).
% 0.21/0.55  fof(f38,plain,(
% 0.21/0.55    (~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) | ~v1_funct_2(sK6,sK4,sK5) | ~v1_funct_1(sK6)) & r2_hidden(sK6,k1_funct_2(sK4,sK5))),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f16,f37])).
% 0.21/0.55  fof(f37,plain,(
% 0.21/0.55    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & r2_hidden(X2,k1_funct_2(X0,X1))) => ((~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) | ~v1_funct_2(sK6,sK4,sK5) | ~v1_funct_1(sK6)) & r2_hidden(sK6,k1_funct_2(sK4,sK5)))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f16,plain,(
% 0.21/0.55    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & r2_hidden(X2,k1_funct_2(X0,X1)))),
% 0.21/0.55    inference(ennf_transformation,[],[f15])).
% 0.21/0.55  fof(f15,negated_conjecture,(
% 0.21/0.55    ~! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.21/0.55    inference(negated_conjecture,[],[f14])).
% 0.21/0.55  fof(f14,conjecture,(
% 0.21/0.55    ! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_2)).
% 0.21/0.55  fof(f121,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_funct_2(X1,X2)) | sP2(X2,X1,X0)) )),
% 0.21/0.55    inference(resolution,[],[f94,f112])).
% 0.21/0.55  fof(f112,plain,(
% 0.21/0.55    ( ! [X0,X1] : (sP3(X0,X1,k1_funct_2(X0,X1))) )),
% 0.21/0.55    inference(equality_resolution,[],[f104])).
% 0.21/0.55  fof(f104,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (sP3(X0,X1,X2) | k1_funct_2(X0,X1) != X2) )),
% 0.21/0.55    inference(cnf_transformation,[],[f63])).
% 0.21/0.55  fof(f63,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((k1_funct_2(X0,X1) = X2 | ~sP3(X0,X1,X2)) & (sP3(X0,X1,X2) | k1_funct_2(X0,X1) != X2))),
% 0.21/0.55    inference(nnf_transformation,[],[f36])).
% 0.21/0.55  fof(f36,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (k1_funct_2(X0,X1) = X2 <=> sP3(X0,X1,X2))),
% 0.21/0.55    inference(definition_folding,[],[f12,f35,f34])).
% 0.21/0.55  fof(f35,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (sP3(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> sP2(X1,X0,X3)))),
% 0.21/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.21/0.55  fof(f12,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : (k1_funct_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4))))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_funct_2)).
% 0.21/0.55  fof(f94,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X1] : (~sP3(X0,X1,X2) | ~r2_hidden(X4,X2) | sP2(X1,X0,X4)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f58])).
% 0.21/0.55  fof(f58,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((sP3(X0,X1,X2) | ((~sP2(X1,X0,sK12(X0,X1,X2)) | ~r2_hidden(sK12(X0,X1,X2),X2)) & (sP2(X1,X0,sK12(X0,X1,X2)) | r2_hidden(sK12(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP2(X1,X0,X4)) & (sP2(X1,X0,X4) | ~r2_hidden(X4,X2))) | ~sP3(X0,X1,X2)))),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f56,f57])).
% 0.21/0.55  fof(f57,plain,(
% 0.21/0.55    ! [X2,X1,X0] : (? [X3] : ((~sP2(X1,X0,X3) | ~r2_hidden(X3,X2)) & (sP2(X1,X0,X3) | r2_hidden(X3,X2))) => ((~sP2(X1,X0,sK12(X0,X1,X2)) | ~r2_hidden(sK12(X0,X1,X2),X2)) & (sP2(X1,X0,sK12(X0,X1,X2)) | r2_hidden(sK12(X0,X1,X2),X2))))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f56,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((sP3(X0,X1,X2) | ? [X3] : ((~sP2(X1,X0,X3) | ~r2_hidden(X3,X2)) & (sP2(X1,X0,X3) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP2(X1,X0,X4)) & (sP2(X1,X0,X4) | ~r2_hidden(X4,X2))) | ~sP3(X0,X1,X2)))),
% 0.21/0.55    inference(rectify,[],[f55])).
% 0.21/0.55  fof(f55,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((sP3(X0,X1,X2) | ? [X3] : ((~sP2(X1,X0,X3) | ~r2_hidden(X3,X2)) & (sP2(X1,X0,X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~sP2(X1,X0,X3)) & (sP2(X1,X0,X3) | ~r2_hidden(X3,X2))) | ~sP3(X0,X1,X2)))),
% 0.21/0.55    inference(nnf_transformation,[],[f35])).
% 0.21/0.55  fof(f135,plain,(
% 0.21/0.55    sK4 = k1_relat_1(sK13(sK5,sK4,sK6))),
% 0.21/0.55    inference(resolution,[],[f101,f122])).
% 0.21/0.55  fof(f101,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~sP2(X0,X1,X2) | k1_relat_1(sK13(X0,X1,X2)) = X1) )),
% 0.21/0.55    inference(cnf_transformation,[],[f62])).
% 0.21/0.55  fof(f596,plain,(
% 0.21/0.55    ~r1_tarski(k1_relat_1(sK6),sK4)),
% 0.21/0.55    inference(subsumption_resolution,[],[f595,f418])).
% 0.21/0.55  fof(f418,plain,(
% 0.21/0.55    r1_tarski(sK4,sK5)),
% 0.21/0.55    inference(backward_demodulation,[],[f145,f410])).
% 0.21/0.55  fof(f410,plain,(
% 0.21/0.55    sK4 = k2_relat_1(sK6)),
% 0.21/0.55    inference(resolution,[],[f408,f148])).
% 0.21/0.55  fof(f148,plain,(
% 0.21/0.55    ( ! [X0] : (~sP0(sK6,X0) | k2_relat_1(sK6) = X0) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f147,f130])).
% 0.21/0.55  fof(f130,plain,(
% 0.21/0.55    v1_funct_1(sK6)),
% 0.21/0.55    inference(subsumption_resolution,[],[f129,f122])).
% 0.21/0.55  fof(f129,plain,(
% 0.21/0.55    v1_funct_1(sK6) | ~sP2(sK5,sK4,sK6)),
% 0.21/0.55    inference(superposition,[],[f99,f125])).
% 0.21/0.55  fof(f99,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (v1_funct_1(sK13(X0,X1,X2)) | ~sP2(X0,X1,X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f62])).
% 0.21/0.55  fof(f147,plain,(
% 0.21/0.55    ( ! [X0] : (k2_relat_1(sK6) = X0 | ~v1_funct_1(sK6) | ~sP0(sK6,X0)) )),
% 0.21/0.55    inference(resolution,[],[f117,f127])).
% 0.21/0.55  fof(f127,plain,(
% 0.21/0.55    v1_relat_1(sK6)),
% 0.21/0.55    inference(forward_demodulation,[],[f126,f125])).
% 0.21/0.55  fof(f126,plain,(
% 0.21/0.55    v1_relat_1(sK13(sK5,sK4,sK6))),
% 0.21/0.55    inference(resolution,[],[f122,f98])).
% 0.21/0.55  fof(f98,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~sP2(X0,X1,X2) | v1_relat_1(sK13(X0,X1,X2))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f62])).
% 0.21/0.55  fof(f117,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~v1_relat_1(X0) | k2_relat_1(X0) = X1 | ~v1_funct_1(X0) | ~sP0(X0,X1)) )),
% 0.21/0.55    inference(resolution,[],[f71,f78])).
% 0.21/0.55  fof(f78,plain,(
% 0.21/0.55    ( ! [X0] : (sP1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f33])).
% 0.21/0.55  fof(f33,plain,(
% 0.21/0.55    ! [X0] : (sP1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.55    inference(definition_folding,[],[f21,f32,f31])).
% 0.21/0.55  fof(f31,plain,(
% 0.21/0.55    ! [X0,X1] : (sP0(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0)))))),
% 0.21/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.55  fof(f32,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> sP0(X0,X1)) | ~sP1(X0))),
% 0.21/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.55  fof(f21,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.55    inference(flattening,[],[f20])).
% 0.21/0.55  fof(f20,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f7])).
% 0.21/0.55  fof(f7,axiom,(
% 0.21/0.55    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).
% 0.21/0.55  fof(f71,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~sP1(X0) | ~sP0(X0,X1) | k2_relat_1(X0) = X1) )),
% 0.21/0.55    inference(cnf_transformation,[],[f39])).
% 0.21/0.55  fof(f39,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ~sP0(X0,X1)) & (sP0(X0,X1) | k2_relat_1(X0) != X1)) | ~sP1(X0))),
% 0.21/0.55    inference(nnf_transformation,[],[f32])).
% 0.21/0.55  fof(f408,plain,(
% 0.21/0.55    sP0(sK6,sK4)),
% 0.21/0.55    inference(resolution,[],[f367,f366])).
% 0.21/0.55  fof(f366,plain,(
% 0.21/0.55    ( ! [X2] : (~r2_hidden(X2,sK4)) )),
% 0.21/0.55    inference(resolution,[],[f350,f79])).
% 0.21/0.55  fof(f79,plain,(
% 0.21/0.55    ( ! [X2,X0] : (~v1_xboole_0(X0) | ~r2_hidden(X2,X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f49])).
% 0.21/0.55  fof(f49,plain,(
% 0.21/0.55    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK10(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f47,f48])).
% 0.21/0.55  fof(f48,plain,(
% 0.21/0.55    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK10(X0),X0))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f47,plain,(
% 0.21/0.55    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.55    inference(rectify,[],[f46])).
% 0.21/0.55  fof(f46,plain,(
% 0.21/0.55    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.55    inference(nnf_transformation,[],[f1])).
% 0.21/0.55  fof(f1,axiom,(
% 0.21/0.55    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.55  fof(f350,plain,(
% 0.21/0.55    v1_xboole_0(sK4)),
% 0.21/0.55    inference(subsumption_resolution,[],[f349,f108])).
% 0.21/0.55  fof(f349,plain,(
% 0.21/0.55    ~r1_tarski(sK4,sK4) | v1_xboole_0(sK4)),
% 0.21/0.55    inference(forward_demodulation,[],[f348,f136])).
% 0.21/0.55  fof(f348,plain,(
% 0.21/0.55    v1_xboole_0(sK4) | ~r1_tarski(k1_relat_1(sK6),sK4)),
% 0.21/0.55    inference(subsumption_resolution,[],[f347,f127])).
% 0.21/0.55  fof(f347,plain,(
% 0.21/0.55    v1_xboole_0(sK4) | ~r1_tarski(k1_relat_1(sK6),sK4) | ~v1_relat_1(sK6)),
% 0.21/0.55    inference(subsumption_resolution,[],[f345,f145])).
% 0.21/0.55  fof(f345,plain,(
% 0.21/0.55    v1_xboole_0(sK4) | ~r1_tarski(k2_relat_1(sK6),sK5) | ~r1_tarski(k1_relat_1(sK6),sK4) | ~v1_relat_1(sK6)),
% 0.21/0.55    inference(resolution,[],[f343,f91])).
% 0.21/0.55  fof(f91,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f28])).
% 0.21/0.55  fof(f28,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.21/0.55    inference(flattening,[],[f27])).
% 0.21/0.55  fof(f27,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 0.21/0.55    inference(ennf_transformation,[],[f8])).
% 0.21/0.55  fof(f8,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).
% 0.21/0.55  fof(f343,plain,(
% 0.21/0.55    ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) | v1_xboole_0(sK4)),
% 0.21/0.55    inference(resolution,[],[f342,f131])).
% 0.21/0.55  fof(f131,plain,(
% 0.21/0.55    ~v1_funct_2(sK6,sK4,sK5) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))),
% 0.21/0.55    inference(subsumption_resolution,[],[f65,f130])).
% 0.21/0.55  fof(f65,plain,(
% 0.21/0.55    ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) | ~v1_funct_2(sK6,sK4,sK5) | ~v1_funct_1(sK6)),
% 0.21/0.55    inference(cnf_transformation,[],[f38])).
% 0.21/0.55  fof(f342,plain,(
% 0.21/0.55    v1_funct_2(sK6,sK4,sK5) | v1_xboole_0(sK4)),
% 0.21/0.55    inference(resolution,[],[f339,f145])).
% 0.21/0.55  fof(f339,plain,(
% 0.21/0.55    ( ! [X0] : (~r1_tarski(k2_relat_1(sK6),X0) | v1_xboole_0(sK4) | v1_funct_2(sK6,sK4,X0)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f338,f108])).
% 0.21/0.55  fof(f338,plain,(
% 0.21/0.55    ( ! [X0] : (~r1_tarski(sK4,sK4) | v1_funct_2(sK6,sK4,X0) | v1_xboole_0(sK4) | ~r1_tarski(k2_relat_1(sK6),X0)) )),
% 0.21/0.55    inference(forward_demodulation,[],[f337,f136])).
% 0.21/0.55  fof(f337,plain,(
% 0.21/0.55    ( ! [X0] : (v1_funct_2(sK6,sK4,X0) | v1_xboole_0(sK4) | ~r1_tarski(k2_relat_1(sK6),X0) | ~r1_tarski(k1_relat_1(sK6),sK4)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f335,f127])).
% 0.21/0.55  fof(f335,plain,(
% 0.21/0.55    ( ! [X0] : (v1_funct_2(sK6,sK4,X0) | v1_xboole_0(sK4) | ~r1_tarski(k2_relat_1(sK6),X0) | ~r1_tarski(k1_relat_1(sK6),sK4) | ~v1_relat_1(sK6)) )),
% 0.21/0.55    inference(resolution,[],[f300,f91])).
% 0.21/0.55  fof(f300,plain,(
% 0.21/0.55    ( ! [X0] : (~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,X0))) | v1_funct_2(sK6,sK4,X0) | v1_xboole_0(sK4)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f299,f130])).
% 0.21/0.55  fof(f299,plain,(
% 0.21/0.55    ( ! [X0] : (v1_xboole_0(sK4) | v1_funct_2(sK6,sK4,X0) | ~v1_funct_1(sK6) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,X0)))) )),
% 0.21/0.55    inference(resolution,[],[f296,f93])).
% 0.21/0.55  fof(f93,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~v1_partfun1(X2,X0) | v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f30])).
% 0.21/0.55  fof(f30,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.55    inference(flattening,[],[f29])).
% 0.21/0.55  fof(f29,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.55    inference(ennf_transformation,[],[f9])).
% 0.21/0.55  fof(f9,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).
% 0.21/0.55  fof(f296,plain,(
% 0.21/0.55    v1_partfun1(sK6,sK4) | v1_xboole_0(sK4)),
% 0.21/0.55    inference(resolution,[],[f289,f80])).
% 0.21/0.55  fof(f80,plain,(
% 0.21/0.55    ( ! [X0] : (r2_hidden(sK10(X0),X0) | v1_xboole_0(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f49])).
% 0.21/0.55  fof(f289,plain,(
% 0.21/0.55    ( ! [X0] : (~r2_hidden(X0,sK4) | v1_partfun1(sK6,sK4)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f288,f127])).
% 0.21/0.55  fof(f288,plain,(
% 0.21/0.55    ( ! [X0] : (v1_partfun1(sK6,sK4) | ~r2_hidden(X0,sK4) | ~v1_relat_1(sK6)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f287,f130])).
% 0.21/0.55  fof(f287,plain,(
% 0.21/0.55    ( ! [X0] : (v1_partfun1(sK6,sK4) | ~r2_hidden(X0,sK4) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6)) )),
% 0.21/0.55    inference(resolution,[],[f286,f78])).
% 0.21/0.55  fof(f286,plain,(
% 0.21/0.55    ( ! [X0] : (~sP1(sK6) | v1_partfun1(sK6,sK4) | ~r2_hidden(X0,sK4)) )),
% 0.21/0.55    inference(forward_demodulation,[],[f285,f136])).
% 0.21/0.55  fof(f285,plain,(
% 0.21/0.55    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK6)) | v1_partfun1(sK6,sK4) | ~sP1(sK6)) )),
% 0.21/0.55    inference(resolution,[],[f279,f106])).
% 0.21/0.55  fof(f106,plain,(
% 0.21/0.55    ( ! [X0] : (sP0(X0,k2_relat_1(X0)) | ~sP1(X0)) )),
% 0.21/0.55    inference(equality_resolution,[],[f70])).
% 0.21/0.55  fof(f70,plain,(
% 0.21/0.55    ( ! [X0,X1] : (sP0(X0,X1) | k2_relat_1(X0) != X1 | ~sP1(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f39])).
% 0.21/0.55  fof(f279,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~sP0(X1,k2_relat_1(sK6)) | ~r2_hidden(X0,k1_relat_1(X1)) | v1_partfun1(sK6,sK4)) )),
% 0.21/0.55    inference(resolution,[],[f278,f107])).
% 0.21/0.55  fof(f107,plain,(
% 0.21/0.55    ( ! [X6,X0,X1] : (r2_hidden(k1_funct_1(X0,X6),X1) | ~r2_hidden(X6,k1_relat_1(X0)) | ~sP0(X0,X1)) )),
% 0.21/0.55    inference(equality_resolution,[],[f74])).
% 0.21/0.55  fof(f74,plain,(
% 0.21/0.55    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | ~sP0(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f45])).
% 0.21/0.55  fof(f45,plain,(
% 0.21/0.55    ! [X0,X1] : ((sP0(X0,X1) | ((! [X3] : (k1_funct_1(X0,X3) != sK7(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK7(X0,X1),X1)) & ((sK7(X0,X1) = k1_funct_1(X0,sK8(X0,X1)) & r2_hidden(sK8(X0,X1),k1_relat_1(X0))) | r2_hidden(sK7(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK9(X0,X5)) = X5 & r2_hidden(sK9(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | ~sP0(X0,X1)))),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f41,f44,f43,f42])).
% 0.21/0.55  fof(f42,plain,(
% 0.21/0.55    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK7(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK7(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK7(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK7(X0,X1),X1))))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f43,plain,(
% 0.21/0.55    ! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = sK7(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) => (sK7(X0,X1) = k1_funct_1(X0,sK8(X0,X1)) & r2_hidden(sK8(X0,X1),k1_relat_1(X0))))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f44,plain,(
% 0.21/0.55    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK9(X0,X5)) = X5 & r2_hidden(sK9(X0,X5),k1_relat_1(X0))))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f41,plain,(
% 0.21/0.55    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | ~sP0(X0,X1)))),
% 0.21/0.55    inference(rectify,[],[f40])).
% 0.21/0.55  fof(f40,plain,(
% 0.21/0.55    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | ~sP0(X0,X1)))),
% 0.21/0.55    inference(nnf_transformation,[],[f31])).
% 0.21/0.55  fof(f278,plain,(
% 0.21/0.55    ( ! [X2] : (~r2_hidden(X2,k2_relat_1(sK6)) | v1_partfun1(sK6,sK4)) )),
% 0.21/0.55    inference(resolution,[],[f273,f79])).
% 0.21/0.55  fof(f273,plain,(
% 0.21/0.55    v1_xboole_0(k2_relat_1(sK6)) | v1_partfun1(sK6,sK4)),
% 0.21/0.55    inference(subsumption_resolution,[],[f271,f152])).
% 0.21/0.55  fof(f152,plain,(
% 0.21/0.55    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,k2_relat_1(sK6))))),
% 0.21/0.55    inference(forward_demodulation,[],[f151,f136])).
% 0.21/0.55  fof(f151,plain,(
% 0.21/0.55    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),k2_relat_1(sK6))))),
% 0.21/0.55    inference(subsumption_resolution,[],[f150,f130])).
% 0.21/0.55  fof(f150,plain,(
% 0.21/0.55    ~v1_funct_1(sK6) | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),k2_relat_1(sK6))))),
% 0.21/0.55    inference(resolution,[],[f69,f127])).
% 0.21/0.55  fof(f69,plain,(
% 0.21/0.55    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f19])).
% 0.21/0.55  fof(f19,plain,(
% 0.21/0.55    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.55    inference(flattening,[],[f18])).
% 0.21/0.55  fof(f18,plain,(
% 0.21/0.55    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f13])).
% 0.21/0.55  fof(f13,axiom,(
% 0.21/0.55    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).
% 0.21/0.55  fof(f271,plain,(
% 0.21/0.55    v1_partfun1(sK6,sK4) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,k2_relat_1(sK6)))) | v1_xboole_0(k2_relat_1(sK6))),
% 0.21/0.55    inference(resolution,[],[f270,f142])).
% 0.21/0.55  fof(f142,plain,(
% 0.21/0.55    v1_funct_2(sK6,sK4,k2_relat_1(sK6))),
% 0.21/0.55    inference(subsumption_resolution,[],[f141,f127])).
% 0.21/0.55  fof(f141,plain,(
% 0.21/0.55    v1_funct_2(sK6,sK4,k2_relat_1(sK6)) | ~v1_relat_1(sK6)),
% 0.21/0.55    inference(subsumption_resolution,[],[f140,f130])).
% 0.21/0.55  fof(f140,plain,(
% 0.21/0.55    v1_funct_2(sK6,sK4,k2_relat_1(sK6)) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6)),
% 0.21/0.55    inference(superposition,[],[f68,f136])).
% 0.21/0.55  fof(f68,plain,(
% 0.21/0.55    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f19])).
% 0.21/0.55  fof(f270,plain,(
% 0.21/0.55    ( ! [X6,X5] : (~v1_funct_2(sK6,X5,X6) | v1_partfun1(sK6,X5) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | v1_xboole_0(X6)) )),
% 0.21/0.55    inference(resolution,[],[f83,f130])).
% 0.21/0.55  fof(f83,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f23])).
% 0.21/0.55  fof(f23,plain,(
% 0.21/0.55    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.21/0.55    inference(flattening,[],[f22])).
% 0.21/0.55  fof(f22,plain,(
% 0.21/0.55    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.21/0.55    inference(ennf_transformation,[],[f11])).
% 0.21/0.55  fof(f11,axiom,(
% 0.21/0.55    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.21/0.55  fof(f367,plain,(
% 0.21/0.55    ( ! [X0] : (r2_hidden(sK7(sK6,X0),X0) | sP0(sK6,X0)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f190,f366])).
% 0.21/0.55  fof(f190,plain,(
% 0.21/0.55    ( ! [X0] : (r2_hidden(sK8(sK6,X0),sK4) | r2_hidden(sK7(sK6,X0),X0) | sP0(sK6,X0)) )),
% 0.21/0.55    inference(superposition,[],[f75,f136])).
% 0.21/0.55  fof(f75,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r2_hidden(sK8(X0,X1),k1_relat_1(X0)) | r2_hidden(sK7(X0,X1),X1) | sP0(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f45])).
% 0.21/0.55  fof(f145,plain,(
% 0.21/0.55    r1_tarski(k2_relat_1(sK6),sK5)),
% 0.21/0.55    inference(forward_demodulation,[],[f144,f125])).
% 0.21/0.55  fof(f144,plain,(
% 0.21/0.55    r1_tarski(k2_relat_1(sK13(sK5,sK4,sK6)),sK5)),
% 0.21/0.55    inference(resolution,[],[f102,f122])).
% 0.21/0.55  fof(f102,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~sP2(X0,X1,X2) | r1_tarski(k2_relat_1(sK13(X0,X1,X2)),X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f62])).
% 0.21/0.55  fof(f595,plain,(
% 0.21/0.55    ~r1_tarski(sK4,sK5) | ~r1_tarski(k1_relat_1(sK6),sK4)),
% 0.21/0.55    inference(forward_demodulation,[],[f594,f410])).
% 0.21/0.55  fof(f594,plain,(
% 0.21/0.55    ~r1_tarski(k2_relat_1(sK6),sK5) | ~r1_tarski(k1_relat_1(sK6),sK4)),
% 0.21/0.55    inference(subsumption_resolution,[],[f592,f127])).
% 0.21/0.55  fof(f592,plain,(
% 0.21/0.55    ~r1_tarski(k2_relat_1(sK6),sK5) | ~r1_tarski(k1_relat_1(sK6),sK4) | ~v1_relat_1(sK6)),
% 0.21/0.55    inference(resolution,[],[f591,f91])).
% 0.21/0.55  fof(f591,plain,(
% 0.21/0.55    ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))),
% 0.21/0.55    inference(subsumption_resolution,[],[f589,f418])).
% 0.21/0.55  fof(f589,plain,(
% 0.21/0.55    ~r1_tarski(sK4,sK5) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))),
% 0.21/0.55    inference(resolution,[],[f588,f131])).
% 0.21/0.55  fof(f588,plain,(
% 0.21/0.55    ( ! [X0] : (v1_funct_2(sK6,sK4,X0) | ~r1_tarski(sK4,X0)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f587,f108])).
% 0.21/0.55  fof(f587,plain,(
% 0.21/0.55    ( ! [X0] : (~r1_tarski(sK4,sK4) | ~r1_tarski(sK4,X0) | v1_funct_2(sK6,sK4,X0)) )),
% 0.21/0.55    inference(forward_demodulation,[],[f586,f136])).
% 0.21/0.55  fof(f586,plain,(
% 0.21/0.55    ( ! [X0] : (~r1_tarski(sK4,X0) | v1_funct_2(sK6,sK4,X0) | ~r1_tarski(k1_relat_1(sK6),sK4)) )),
% 0.21/0.55    inference(forward_demodulation,[],[f585,f410])).
% 0.21/0.55  fof(f585,plain,(
% 0.21/0.55    ( ! [X0] : (v1_funct_2(sK6,sK4,X0) | ~r1_tarski(k2_relat_1(sK6),X0) | ~r1_tarski(k1_relat_1(sK6),sK4)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f583,f127])).
% 0.21/0.55  fof(f583,plain,(
% 0.21/0.55    ( ! [X0] : (v1_funct_2(sK6,sK4,X0) | ~r1_tarski(k2_relat_1(sK6),X0) | ~r1_tarski(k1_relat_1(sK6),sK4) | ~v1_relat_1(sK6)) )),
% 0.21/0.55    inference(resolution,[],[f540,f91])).
% 0.21/0.55  fof(f540,plain,(
% 0.21/0.55    ( ! [X0] : (~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,X0))) | v1_funct_2(sK6,sK4,X0)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f539,f130])).
% 0.21/0.55  fof(f539,plain,(
% 0.21/0.55    ( ! [X0] : (v1_funct_2(sK6,sK4,X0) | ~v1_funct_1(sK6) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,X0)))) )),
% 0.21/0.55    inference(resolution,[],[f538,f93])).
% 0.21/0.55  fof(f538,plain,(
% 0.21/0.55    v1_partfun1(sK6,sK4)),
% 0.21/0.55    inference(resolution,[],[f365,f421])).
% 0.21/0.55  fof(f421,plain,(
% 0.21/0.55    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4)))),
% 0.21/0.55    inference(backward_demodulation,[],[f152,f410])).
% 0.21/0.55  fof(f365,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK4,X1))) | v1_partfun1(X0,sK4)) )),
% 0.21/0.55    inference(resolution,[],[f350,f84])).
% 0.21/0.55  fof(f84,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_partfun1(X2,X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f24])).
% 0.21/0.55  fof(f24,plain,(
% 0.21/0.55    ! [X0,X1] : (! [X2] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f10])).
% 0.21/0.55  fof(f10,axiom,(
% 0.21/0.55    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_partfun1(X2,X0)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_partfun1)).
% 0.21/0.55  % SZS output end Proof for theBenchmark
% 0.21/0.55  % (3125)------------------------------
% 0.21/0.55  % (3125)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (3125)Termination reason: Refutation
% 0.21/0.55  
% 0.21/0.55  % (3125)Memory used [KB]: 6652
% 0.21/0.55  % (3125)Time elapsed: 0.117 s
% 0.21/0.55  % (3125)------------------------------
% 0.21/0.55  % (3125)------------------------------
% 0.21/0.55  % (3120)Success in time 0.188 s
%------------------------------------------------------------------------------
