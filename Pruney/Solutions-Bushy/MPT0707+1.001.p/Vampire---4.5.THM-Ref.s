%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0707+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:30 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  120 (2567 expanded)
%              Number of leaves         :   12 ( 737 expanded)
%              Depth                    :   38
%              Number of atoms          :  478 (12583 expanded)
%              Number of equality atoms :  148 (3956 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f677,plain,(
    $false ),
    inference(subsumption_resolution,[],[f676,f34])).

fof(f34,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f676,plain,(
    ~ v1_relat_1(k6_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f675,f35])).

fof(f35,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f675,plain,
    ( ~ v1_funct_1(k6_relat_1(sK0))
    | ~ v1_relat_1(k6_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f674,f604])).

fof(f604,plain,(
    r2_hidden(sK2(k6_relat_1(sK0),sK1,sK1),sK0) ),
    inference(backward_demodulation,[],[f521,f540])).

fof(f540,plain,(
    sK2(k6_relat_1(sK0),sK1,sK1) = sK3(k6_relat_1(sK0),sK1,sK1) ),
    inference(forward_demodulation,[],[f539,f528])).

fof(f528,plain,(
    sK2(k6_relat_1(sK0),sK1,sK1) = k1_funct_1(k6_relat_1(sK0),sK3(k6_relat_1(sK0),sK1,sK1)) ),
    inference(subsumption_resolution,[],[f527,f499])).

fof(f499,plain,
    ( sK2(k6_relat_1(sK0),sK1,sK1) = k1_funct_1(k6_relat_1(sK0),sK3(k6_relat_1(sK0),sK1,sK1))
    | r2_hidden(sK2(k6_relat_1(sK0),sK1,sK1),sK0) ),
    inference(subsumption_resolution,[],[f497,f32])).

fof(f32,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( sK1 != k9_relat_1(k6_relat_1(sK0),sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f19])).

fof(f19,plain,
    ( ? [X0,X1] :
        ( k9_relat_1(k6_relat_1(X0),X1) != X1
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( sK1 != k9_relat_1(k6_relat_1(sK0),sK1)
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),X1) != X1
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).

fof(f497,plain,
    ( sK2(k6_relat_1(sK0),sK1,sK1) = k1_funct_1(k6_relat_1(sK0),sK3(k6_relat_1(sK0),sK1,sK1))
    | r2_hidden(sK2(k6_relat_1(sK0),sK1,sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f265,f122])).

fof(f122,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(X0)) ) ),
    inference(resolution,[],[f119,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f119,plain,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(X1)) ) ),
    inference(subsumption_resolution,[],[f112,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f112,plain,(
    ! [X1] :
      ( r2_hidden(sK2(k6_relat_1(sK0),sK1,sK1),sK1)
      | ~ v1_xboole_0(X1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f87,f50])).

fof(f87,plain,
    ( r2_hidden(sK3(k6_relat_1(sK0),sK1,sK1),sK1)
    | r2_hidden(sK2(k6_relat_1(sK0),sK1,sK1),sK1) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X1] :
      ( sK1 != X1
      | r2_hidden(sK3(k6_relat_1(sK0),sK1,X1),sK1)
      | r2_hidden(sK2(k6_relat_1(sK0),sK1,X1),X1) ) ),
    inference(subsumption_resolution,[],[f70,f34])).

fof(f70,plain,(
    ! [X1] :
      ( sK1 != X1
      | r2_hidden(sK3(k6_relat_1(sK0),sK1,X1),sK1)
      | r2_hidden(sK2(k6_relat_1(sK0),sK1,X1),X1)
      | ~ v1_relat_1(k6_relat_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f65,f35])).

fof(f65,plain,(
    ! [X1] :
      ( sK1 != X1
      | r2_hidden(sK3(k6_relat_1(sK0),sK1,X1),sK1)
      | r2_hidden(sK2(k6_relat_1(sK0),sK1,X1),X1)
      | ~ v1_funct_1(k6_relat_1(sK0))
      | ~ v1_relat_1(k6_relat_1(sK0)) ) ),
    inference(superposition,[],[f33,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( k1_funct_1(X0,X4) != sK2(X0,X1,X2)
                    | ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(X4,k1_relat_1(X0)) )
                | ~ r2_hidden(sK2(X0,X1,X2),X2) )
              & ( ( sK2(X0,X1,X2) = k1_funct_1(X0,sK3(X0,X1,X2))
                  & r2_hidden(sK3(X0,X1,X2),X1)
                  & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X0)) )
                | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( k1_funct_1(X0,X7) != X6
                      | ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK4(X0,X1,X6)) = X6
                    & r2_hidden(sK4(X0,X1,X6),X1)
                    & r2_hidden(sK4(X0,X1,X6),k1_relat_1(X0)) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f22,f25,f24,f23])).

fof(f23,plain,(
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
              ( k1_funct_1(X0,X4) != sK2(X0,X1,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,k1_relat_1(X0)) )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( k1_funct_1(X0,X5) = sK2(X0,X1,X2)
              & r2_hidden(X5,X1)
              & r2_hidden(X5,k1_relat_1(X0)) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( k1_funct_1(X0,X5) = sK2(X0,X1,X2)
          & r2_hidden(X5,X1)
          & r2_hidden(X5,k1_relat_1(X0)) )
     => ( sK2(X0,X1,X2) = k1_funct_1(X0,sK3(X0,X1,X2))
        & r2_hidden(sK3(X0,X1,X2),X1)
        & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( k1_funct_1(X0,X8) = X6
          & r2_hidden(X8,X1)
          & r2_hidden(X8,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X1,X6)) = X6
        & r2_hidden(sK4(X0,X1,X6),X1)
        & r2_hidden(sK4(X0,X1,X6),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
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
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
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
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

fof(f10,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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

fof(f33,plain,(
    sK1 != k9_relat_1(k6_relat_1(sK0),sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f265,plain,
    ( m1_subset_1(sK2(k6_relat_1(sK0),sK1,sK1),sK0)
    | sK2(k6_relat_1(sK0),sK1,sK1) = k1_funct_1(k6_relat_1(sK0),sK3(k6_relat_1(sK0),sK1,sK1)) ),
    inference(resolution,[],[f141,f32])).

fof(f141,plain,(
    ! [X3] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(X3))
      | m1_subset_1(sK2(k6_relat_1(sK0),sK1,sK1),X3)
      | sK2(k6_relat_1(sK0),sK1,sK1) = k1_funct_1(k6_relat_1(sK0),sK3(k6_relat_1(sK0),sK1,sK1)) ) ),
    inference(resolution,[],[f89,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f89,plain,
    ( r2_hidden(sK2(k6_relat_1(sK0),sK1,sK1),sK1)
    | sK2(k6_relat_1(sK0),sK1,sK1) = k1_funct_1(k6_relat_1(sK0),sK3(k6_relat_1(sK0),sK1,sK1)) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X2] :
      ( sK1 != X2
      | sK2(k6_relat_1(sK0),sK1,X2) = k1_funct_1(k6_relat_1(sK0),sK3(k6_relat_1(sK0),sK1,X2))
      | r2_hidden(sK2(k6_relat_1(sK0),sK1,X2),X2) ) ),
    inference(subsumption_resolution,[],[f72,f34])).

fof(f72,plain,(
    ! [X2] :
      ( sK1 != X2
      | sK2(k6_relat_1(sK0),sK1,X2) = k1_funct_1(k6_relat_1(sK0),sK3(k6_relat_1(sK0),sK1,X2))
      | r2_hidden(sK2(k6_relat_1(sK0),sK1,X2),X2)
      | ~ v1_relat_1(k6_relat_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f66,f35])).

fof(f66,plain,(
    ! [X2] :
      ( sK1 != X2
      | sK2(k6_relat_1(sK0),sK1,X2) = k1_funct_1(k6_relat_1(sK0),sK3(k6_relat_1(sK0),sK1,X2))
      | r2_hidden(sK2(k6_relat_1(sK0),sK1,X2),X2)
      | ~ v1_funct_1(k6_relat_1(sK0))
      | ~ v1_relat_1(k6_relat_1(sK0)) ) ),
    inference(superposition,[],[f33,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X0,X1) = X2
      | sK2(X0,X1,X2) = k1_funct_1(X0,sK3(X0,X1,X2))
      | r2_hidden(sK2(X0,X1,X2),X2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f527,plain,
    ( ~ r2_hidden(sK2(k6_relat_1(sK0),sK1,sK1),sK0)
    | sK2(k6_relat_1(sK0),sK1,sK1) = k1_funct_1(k6_relat_1(sK0),sK3(k6_relat_1(sK0),sK1,sK1)) ),
    inference(subsumption_resolution,[],[f526,f34])).

fof(f526,plain,
    ( ~ r2_hidden(sK2(k6_relat_1(sK0),sK1,sK1),sK0)
    | sK2(k6_relat_1(sK0),sK1,sK1) = k1_funct_1(k6_relat_1(sK0),sK3(k6_relat_1(sK0),sK1,sK1))
    | ~ v1_relat_1(k6_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f525,f35])).

fof(f525,plain,
    ( ~ r2_hidden(sK2(k6_relat_1(sK0),sK1,sK1),sK0)
    | sK2(k6_relat_1(sK0),sK1,sK1) = k1_funct_1(k6_relat_1(sK0),sK3(k6_relat_1(sK0),sK1,sK1))
    | ~ v1_funct_1(k6_relat_1(sK0))
    | ~ v1_relat_1(k6_relat_1(sK0)) ),
    inference(superposition,[],[f323,f59])).

fof(f59,plain,(
    ! [X0] :
      ( k1_relat_1(k6_relat_1(X0)) = X0
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | k6_relat_1(X0) != X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ( sK5(X0,X1) != k1_funct_1(X1,sK5(X0,X1))
            & r2_hidden(sK5(X0,X1),X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X3] :
                ( k1_funct_1(X1,X3) = X3
                | ~ r2_hidden(X3,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f29,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X1,X2) != X2
          & r2_hidden(X2,X0) )
     => ( sK5(X0,X1) != k1_funct_1(X1,sK5(X0,X1))
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X3] :
                ( k1_funct_1(X1,X3) = X3
                | ~ r2_hidden(X3,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X2] :
                ( k1_funct_1(X1,X2) = X2
                | ~ r2_hidden(X2,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X2] :
                ( k1_funct_1(X1,X2) = X2
                | ~ r2_hidden(X2,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( r2_hidden(X2,X0)
             => k1_funct_1(X1,X2) = X2 )
          & k1_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_1)).

fof(f323,plain,
    ( ~ r2_hidden(sK2(k6_relat_1(sK0),sK1,sK1),k1_relat_1(k6_relat_1(sK0)))
    | sK2(k6_relat_1(sK0),sK1,sK1) = k1_funct_1(k6_relat_1(sK0),sK3(k6_relat_1(sK0),sK1,sK1)) ),
    inference(subsumption_resolution,[],[f321,f161])).

fof(f161,plain,
    ( sK2(k6_relat_1(sK0),sK1,sK1) = k1_funct_1(k6_relat_1(sK0),sK2(k6_relat_1(sK0),sK1,sK1))
    | sK2(k6_relat_1(sK0),sK1,sK1) = k1_funct_1(k6_relat_1(sK0),sK3(k6_relat_1(sK0),sK1,sK1)) ),
    inference(resolution,[],[f86,f89])).

fof(f86,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK1)
      | k1_funct_1(k6_relat_1(sK0),X4) = X4 ) ),
    inference(subsumption_resolution,[],[f85,f34])).

fof(f85,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK1)
      | k1_funct_1(k6_relat_1(sK0),X4) = X4
      | ~ v1_relat_1(k6_relat_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f81,f35])).

fof(f81,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK1)
      | k1_funct_1(k6_relat_1(sK0),X4) = X4
      | ~ v1_funct_1(k6_relat_1(sK0))
      | ~ v1_relat_1(k6_relat_1(sK0)) ) ),
    inference(resolution,[],[f77,f58])).

fof(f58,plain,(
    ! [X0,X3] :
      ( k1_funct_1(k6_relat_1(X0),X3) = X3
      | ~ r2_hidden(X3,X0)
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(X1,X3) = X3
      | ~ r2_hidden(X3,X0)
      | k6_relat_1(X0) != X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f77,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK0)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f76,f60])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK0)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f32,f50])).

fof(f76,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | r2_hidden(X0,sK0)
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f61,f44])).

fof(f61,plain,(
    ! [X1] :
      ( m1_subset_1(X1,sK0)
      | ~ r2_hidden(X1,sK1) ) ),
    inference(resolution,[],[f32,f49])).

fof(f321,plain,
    ( sK2(k6_relat_1(sK0),sK1,sK1) != k1_funct_1(k6_relat_1(sK0),sK2(k6_relat_1(sK0),sK1,sK1))
    | sK2(k6_relat_1(sK0),sK1,sK1) = k1_funct_1(k6_relat_1(sK0),sK3(k6_relat_1(sK0),sK1,sK1))
    | ~ r2_hidden(sK2(k6_relat_1(sK0),sK1,sK1),k1_relat_1(k6_relat_1(sK0))) ),
    inference(duplicate_literal_removal,[],[f313])).

fof(f313,plain,
    ( sK2(k6_relat_1(sK0),sK1,sK1) != k1_funct_1(k6_relat_1(sK0),sK2(k6_relat_1(sK0),sK1,sK1))
    | sK2(k6_relat_1(sK0),sK1,sK1) = k1_funct_1(k6_relat_1(sK0),sK3(k6_relat_1(sK0),sK1,sK1))
    | ~ r2_hidden(sK2(k6_relat_1(sK0),sK1,sK1),k1_relat_1(k6_relat_1(sK0)))
    | sK2(k6_relat_1(sK0),sK1,sK1) = k1_funct_1(k6_relat_1(sK0),sK3(k6_relat_1(sK0),sK1,sK1)) ),
    inference(resolution,[],[f147,f89])).

fof(f147,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | sK2(k6_relat_1(sK0),sK1,sK1) != k1_funct_1(k6_relat_1(sK0),X0)
      | sK2(k6_relat_1(sK0),sK1,sK1) = k1_funct_1(k6_relat_1(sK0),sK3(k6_relat_1(sK0),sK1,sK1))
      | ~ r2_hidden(X0,k1_relat_1(k6_relat_1(sK0))) ) ),
    inference(subsumption_resolution,[],[f146,f34])).

fof(f146,plain,(
    ! [X0] :
      ( sK2(k6_relat_1(sK0),sK1,sK1) = k1_funct_1(k6_relat_1(sK0),sK3(k6_relat_1(sK0),sK1,sK1))
      | sK2(k6_relat_1(sK0),sK1,sK1) != k1_funct_1(k6_relat_1(sK0),X0)
      | ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,k1_relat_1(k6_relat_1(sK0)))
      | ~ v1_relat_1(k6_relat_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f145,f35])).

fof(f145,plain,(
    ! [X0] :
      ( sK2(k6_relat_1(sK0),sK1,sK1) = k1_funct_1(k6_relat_1(sK0),sK3(k6_relat_1(sK0),sK1,sK1))
      | sK2(k6_relat_1(sK0),sK1,sK1) != k1_funct_1(k6_relat_1(sK0),X0)
      | ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,k1_relat_1(k6_relat_1(sK0)))
      | ~ v1_funct_1(k6_relat_1(sK0))
      | ~ v1_relat_1(k6_relat_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f137,f33])).

fof(f137,plain,(
    ! [X0] :
      ( sK2(k6_relat_1(sK0),sK1,sK1) = k1_funct_1(k6_relat_1(sK0),sK3(k6_relat_1(sK0),sK1,sK1))
      | sK1 = k9_relat_1(k6_relat_1(sK0),sK1)
      | sK2(k6_relat_1(sK0),sK1,sK1) != k1_funct_1(k6_relat_1(sK0),X0)
      | ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,k1_relat_1(k6_relat_1(sK0)))
      | ~ v1_funct_1(k6_relat_1(sK0))
      | ~ v1_relat_1(k6_relat_1(sK0)) ) ),
    inference(resolution,[],[f89,f43])).

fof(f43,plain,(
    ! [X4,X2,X0,X1] :
      ( k9_relat_1(X0,X1) = X2
      | k1_funct_1(X0,X4) != sK2(X0,X1,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(sK2(X0,X1,X2),X2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f539,plain,(
    sK3(k6_relat_1(sK0),sK1,sK1) = k1_funct_1(k6_relat_1(sK0),sK3(k6_relat_1(sK0),sK1,sK1)) ),
    inference(subsumption_resolution,[],[f538,f34])).

fof(f538,plain,
    ( sK3(k6_relat_1(sK0),sK1,sK1) = k1_funct_1(k6_relat_1(sK0),sK3(k6_relat_1(sK0),sK1,sK1))
    | ~ v1_relat_1(k6_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f535,f35])).

fof(f535,plain,
    ( sK3(k6_relat_1(sK0),sK1,sK1) = k1_funct_1(k6_relat_1(sK0),sK3(k6_relat_1(sK0),sK1,sK1))
    | ~ v1_funct_1(k6_relat_1(sK0))
    | ~ v1_relat_1(k6_relat_1(sK0)) ),
    inference(resolution,[],[f521,f58])).

fof(f521,plain,(
    r2_hidden(sK3(k6_relat_1(sK0),sK1,sK1),sK0) ),
    inference(subsumption_resolution,[],[f519,f366])).

fof(f366,plain,
    ( r2_hidden(sK3(k6_relat_1(sK0),sK1,sK1),sK0)
    | r2_hidden(sK2(k6_relat_1(sK0),sK1,sK1),sK1) ),
    inference(subsumption_resolution,[],[f364,f32])).

fof(f364,plain,
    ( r2_hidden(sK2(k6_relat_1(sK0),sK1,sK1),sK1)
    | r2_hidden(sK3(k6_relat_1(sK0),sK1,sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f207,f122])).

fof(f207,plain,
    ( m1_subset_1(sK3(k6_relat_1(sK0),sK1,sK1),sK0)
    | r2_hidden(sK2(k6_relat_1(sK0),sK1,sK1),sK1) ),
    inference(resolution,[],[f113,f32])).

fof(f113,plain,(
    ! [X2] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(X2))
      | m1_subset_1(sK3(k6_relat_1(sK0),sK1,sK1),X2)
      | r2_hidden(sK2(k6_relat_1(sK0),sK1,sK1),sK1) ) ),
    inference(resolution,[],[f87,f49])).

fof(f519,plain,
    ( r2_hidden(sK3(k6_relat_1(sK0),sK1,sK1),sK0)
    | ~ r2_hidden(sK2(k6_relat_1(sK0),sK1,sK1),sK1) ),
    inference(resolution,[],[f435,f77])).

fof(f435,plain,
    ( ~ r2_hidden(sK2(k6_relat_1(sK0),sK1,sK1),sK0)
    | r2_hidden(sK3(k6_relat_1(sK0),sK1,sK1),sK0) ),
    inference(subsumption_resolution,[],[f434,f34])).

fof(f434,plain,
    ( ~ r2_hidden(sK2(k6_relat_1(sK0),sK1,sK1),sK0)
    | r2_hidden(sK3(k6_relat_1(sK0),sK1,sK1),sK0)
    | ~ v1_relat_1(k6_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f433,f35])).

fof(f433,plain,
    ( ~ r2_hidden(sK2(k6_relat_1(sK0),sK1,sK1),sK0)
    | r2_hidden(sK3(k6_relat_1(sK0),sK1,sK1),sK0)
    | ~ v1_funct_1(k6_relat_1(sK0))
    | ~ v1_relat_1(k6_relat_1(sK0)) ),
    inference(superposition,[],[f281,f59])).

fof(f281,plain,
    ( ~ r2_hidden(sK2(k6_relat_1(sK0),sK1,sK1),k1_relat_1(k6_relat_1(sK0)))
    | r2_hidden(sK3(k6_relat_1(sK0),sK1,sK1),k1_relat_1(k6_relat_1(sK0))) ),
    inference(subsumption_resolution,[],[f278,f162])).

fof(f162,plain,
    ( sK2(k6_relat_1(sK0),sK1,sK1) = k1_funct_1(k6_relat_1(sK0),sK2(k6_relat_1(sK0),sK1,sK1))
    | r2_hidden(sK3(k6_relat_1(sK0),sK1,sK1),k1_relat_1(k6_relat_1(sK0))) ),
    inference(resolution,[],[f86,f88])).

fof(f88,plain,
    ( r2_hidden(sK2(k6_relat_1(sK0),sK1,sK1),sK1)
    | r2_hidden(sK3(k6_relat_1(sK0),sK1,sK1),k1_relat_1(k6_relat_1(sK0))) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X0] :
      ( sK1 != X0
      | r2_hidden(sK3(k6_relat_1(sK0),sK1,X0),k1_relat_1(k6_relat_1(sK0)))
      | r2_hidden(sK2(k6_relat_1(sK0),sK1,X0),X0) ) ),
    inference(subsumption_resolution,[],[f68,f34])).

fof(f68,plain,(
    ! [X0] :
      ( sK1 != X0
      | r2_hidden(sK3(k6_relat_1(sK0),sK1,X0),k1_relat_1(k6_relat_1(sK0)))
      | r2_hidden(sK2(k6_relat_1(sK0),sK1,X0),X0)
      | ~ v1_relat_1(k6_relat_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f64,f35])).

fof(f64,plain,(
    ! [X0] :
      ( sK1 != X0
      | r2_hidden(sK3(k6_relat_1(sK0),sK1,X0),k1_relat_1(k6_relat_1(sK0)))
      | r2_hidden(sK2(k6_relat_1(sK0),sK1,X0),X0)
      | ~ v1_funct_1(k6_relat_1(sK0))
      | ~ v1_relat_1(k6_relat_1(sK0)) ) ),
    inference(superposition,[],[f33,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),k1_relat_1(X0))
      | r2_hidden(sK2(X0,X1,X2),X2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f278,plain,
    ( sK2(k6_relat_1(sK0),sK1,sK1) != k1_funct_1(k6_relat_1(sK0),sK2(k6_relat_1(sK0),sK1,sK1))
    | r2_hidden(sK3(k6_relat_1(sK0),sK1,sK1),k1_relat_1(k6_relat_1(sK0)))
    | ~ r2_hidden(sK2(k6_relat_1(sK0),sK1,sK1),k1_relat_1(k6_relat_1(sK0))) ),
    inference(duplicate_literal_removal,[],[f271])).

fof(f271,plain,
    ( sK2(k6_relat_1(sK0),sK1,sK1) != k1_funct_1(k6_relat_1(sK0),sK2(k6_relat_1(sK0),sK1,sK1))
    | r2_hidden(sK3(k6_relat_1(sK0),sK1,sK1),k1_relat_1(k6_relat_1(sK0)))
    | ~ r2_hidden(sK2(k6_relat_1(sK0),sK1,sK1),k1_relat_1(k6_relat_1(sK0)))
    | r2_hidden(sK3(k6_relat_1(sK0),sK1,sK1),k1_relat_1(k6_relat_1(sK0))) ),
    inference(resolution,[],[f134,f88])).

fof(f134,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | sK2(k6_relat_1(sK0),sK1,sK1) != k1_funct_1(k6_relat_1(sK0),X0)
      | r2_hidden(sK3(k6_relat_1(sK0),sK1,sK1),k1_relat_1(k6_relat_1(sK0)))
      | ~ r2_hidden(X0,k1_relat_1(k6_relat_1(sK0))) ) ),
    inference(subsumption_resolution,[],[f133,f34])).

fof(f133,plain,(
    ! [X0] :
      ( r2_hidden(sK3(k6_relat_1(sK0),sK1,sK1),k1_relat_1(k6_relat_1(sK0)))
      | sK2(k6_relat_1(sK0),sK1,sK1) != k1_funct_1(k6_relat_1(sK0),X0)
      | ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,k1_relat_1(k6_relat_1(sK0)))
      | ~ v1_relat_1(k6_relat_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f132,f35])).

fof(f132,plain,(
    ! [X0] :
      ( r2_hidden(sK3(k6_relat_1(sK0),sK1,sK1),k1_relat_1(k6_relat_1(sK0)))
      | sK2(k6_relat_1(sK0),sK1,sK1) != k1_funct_1(k6_relat_1(sK0),X0)
      | ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,k1_relat_1(k6_relat_1(sK0)))
      | ~ v1_funct_1(k6_relat_1(sK0))
      | ~ v1_relat_1(k6_relat_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f124,f33])).

fof(f124,plain,(
    ! [X0] :
      ( r2_hidden(sK3(k6_relat_1(sK0),sK1,sK1),k1_relat_1(k6_relat_1(sK0)))
      | sK1 = k9_relat_1(k6_relat_1(sK0),sK1)
      | sK2(k6_relat_1(sK0),sK1,sK1) != k1_funct_1(k6_relat_1(sK0),X0)
      | ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,k1_relat_1(k6_relat_1(sK0)))
      | ~ v1_funct_1(k6_relat_1(sK0))
      | ~ v1_relat_1(k6_relat_1(sK0)) ) ),
    inference(resolution,[],[f88,f43])).

fof(f674,plain,
    ( ~ r2_hidden(sK2(k6_relat_1(sK0),sK1,sK1),sK0)
    | ~ v1_funct_1(k6_relat_1(sK0))
    | ~ v1_relat_1(k6_relat_1(sK0)) ),
    inference(superposition,[],[f641,f59])).

fof(f641,plain,(
    ~ r2_hidden(sK2(k6_relat_1(sK0),sK1,sK1),k1_relat_1(k6_relat_1(sK0))) ),
    inference(subsumption_resolution,[],[f635,f608])).

fof(f608,plain,(
    sK2(k6_relat_1(sK0),sK1,sK1) = k1_funct_1(k6_relat_1(sK0),sK2(k6_relat_1(sK0),sK1,sK1)) ),
    inference(duplicate_literal_removal,[],[f553])).

fof(f553,plain,
    ( sK2(k6_relat_1(sK0),sK1,sK1) = k1_funct_1(k6_relat_1(sK0),sK2(k6_relat_1(sK0),sK1,sK1))
    | sK2(k6_relat_1(sK0),sK1,sK1) = k1_funct_1(k6_relat_1(sK0),sK2(k6_relat_1(sK0),sK1,sK1)) ),
    inference(backward_demodulation,[],[f161,f540])).

fof(f635,plain,
    ( sK2(k6_relat_1(sK0),sK1,sK1) != k1_funct_1(k6_relat_1(sK0),sK2(k6_relat_1(sK0),sK1,sK1))
    | ~ r2_hidden(sK2(k6_relat_1(sK0),sK1,sK1),k1_relat_1(k6_relat_1(sK0))) ),
    inference(resolution,[],[f629,f609])).

fof(f609,plain,(
    r2_hidden(sK2(k6_relat_1(sK0),sK1,sK1),sK1) ),
    inference(duplicate_literal_removal,[],[f541])).

fof(f541,plain,
    ( r2_hidden(sK2(k6_relat_1(sK0),sK1,sK1),sK1)
    | r2_hidden(sK2(k6_relat_1(sK0),sK1,sK1),sK1) ),
    inference(backward_demodulation,[],[f87,f540])).

fof(f629,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | sK2(k6_relat_1(sK0),sK1,sK1) != k1_funct_1(k6_relat_1(sK0),X0)
      | ~ r2_hidden(X0,k1_relat_1(k6_relat_1(sK0))) ) ),
    inference(subsumption_resolution,[],[f628,f34])).

fof(f628,plain,(
    ! [X0] :
      ( sK2(k6_relat_1(sK0),sK1,sK1) != k1_funct_1(k6_relat_1(sK0),X0)
      | ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,k1_relat_1(k6_relat_1(sK0)))
      | ~ v1_relat_1(k6_relat_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f627,f35])).

fof(f627,plain,(
    ! [X0] :
      ( sK2(k6_relat_1(sK0),sK1,sK1) != k1_funct_1(k6_relat_1(sK0),X0)
      | ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,k1_relat_1(k6_relat_1(sK0)))
      | ~ v1_funct_1(k6_relat_1(sK0))
      | ~ v1_relat_1(k6_relat_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f616,f33])).

fof(f616,plain,(
    ! [X0] :
      ( sK1 = k9_relat_1(k6_relat_1(sK0),sK1)
      | sK2(k6_relat_1(sK0),sK1,sK1) != k1_funct_1(k6_relat_1(sK0),X0)
      | ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,k1_relat_1(k6_relat_1(sK0)))
      | ~ v1_funct_1(k6_relat_1(sK0))
      | ~ v1_relat_1(k6_relat_1(sK0)) ) ),
    inference(resolution,[],[f609,f43])).

%------------------------------------------------------------------------------
