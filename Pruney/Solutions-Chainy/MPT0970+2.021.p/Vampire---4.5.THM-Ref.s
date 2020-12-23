%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:51 EST 2020

% Result     : Theorem 1.41s
% Output     : Refutation 1.41s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 374 expanded)
%              Number of leaves         :   17 ( 106 expanded)
%              Depth                    :   24
%              Number of atoms          :  350 (1814 expanded)
%              Number of equality atoms :  109 ( 438 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f397,plain,(
    $false ),
    inference(subsumption_resolution,[],[f353,f70])).

fof(f70,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f353,plain,(
    ~ r1_tarski(k1_xboole_0,k2_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f132,f334])).

fof(f334,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f331,f132])).

fof(f331,plain,
    ( k1_xboole_0 = sK1
    | r1_tarski(sK1,k2_relat_1(sK2)) ),
    inference(resolution,[],[f328,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK7(X0,X1),X1)
          & r2_hidden(sK7(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f38,f39])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK7(X0,X1),X1)
        & r2_hidden(sK7(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f328,plain,
    ( ~ r2_hidden(sK7(sK1,k2_relat_1(sK2)),sK1)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f324,f76])).

fof(f76,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f324,plain,
    ( ~ r1_tarski(sK0,sK0)
    | ~ r2_hidden(sK7(sK1,k2_relat_1(sK2)),sK1)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f293,f316])).

fof(f316,plain,
    ( sK0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f315,f150])).

fof(f150,plain,(
    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(resolution,[],[f55,f43])).

fof(f43,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    & ! [X3] :
        ( ( k1_funct_1(sK2,sK3(X3)) = X3
          & r2_hidden(sK3(X3),sK0) )
        | ~ r2_hidden(X3,sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f26,f25])).

fof(f25,plain,
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
   => ( sK1 != k2_relset_1(sK0,sK1,sK2)
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(sK2,X4) = X3
              & r2_hidden(X4,sK0) )
          | ~ r2_hidden(X3,sK1) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X3] :
      ( ? [X4] :
          ( k1_funct_1(sK2,X4) = X3
          & r2_hidden(X4,sK0) )
     => ( k1_funct_1(sK2,sK3(X3)) = X3
        & r2_hidden(sK3(X3),sK0) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_2)).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f315,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f314,f42])).

fof(f42,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f314,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f49,f43])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f293,plain,
    ( ~ r1_tarski(sK0,k1_relat_1(sK2))
    | ~ r2_hidden(sK7(sK1,k2_relat_1(sK2)),sK1) ),
    inference(resolution,[],[f292,f44])).

fof(f44,plain,(
    ! [X3] :
      ( r2_hidden(sK3(X3),sK0)
      | ~ r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f292,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3(sK7(sK1,k2_relat_1(sK2))),X0)
      | ~ r1_tarski(X0,k1_relat_1(sK2)) ) ),
    inference(subsumption_resolution,[],[f288,f132])).

fof(f288,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3(sK7(sK1,k2_relat_1(sK2))),X0)
      | ~ r1_tarski(X0,k1_relat_1(sK2))
      | r1_tarski(sK1,k2_relat_1(sK2)) ) ),
    inference(resolution,[],[f168,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK7(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f168,plain,(
    ! [X0] :
      ( r2_hidden(sK7(sK1,k2_relat_1(sK2)),k2_relat_1(sK2))
      | ~ r2_hidden(sK3(sK7(sK1,k2_relat_1(sK2))),X0)
      | ~ r1_tarski(X0,k1_relat_1(sK2)) ) ),
    inference(superposition,[],[f165,f151])).

fof(f151,plain,(
    sK7(sK1,k2_relat_1(sK2)) = k1_funct_1(sK2,sK3(sK7(sK1,k2_relat_1(sK2)))) ),
    inference(resolution,[],[f85,f132])).

fof(f85,plain,(
    ! [X0] :
      ( r1_tarski(sK1,X0)
      | sK7(sK1,X0) = k1_funct_1(sK2,sK3(sK7(sK1,X0))) ) ),
    inference(resolution,[],[f45,f66])).

fof(f45,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK1)
      | k1_funct_1(sK2,sK3(X3)) = X3 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f165,plain,(
    ! [X2,X1] :
      ( r2_hidden(k1_funct_1(sK2,X1),k2_relat_1(sK2))
      | ~ r2_hidden(X1,X2)
      | ~ r1_tarski(X2,k1_relat_1(sK2)) ) ),
    inference(resolution,[],[f163,f65])).

fof(f65,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f163,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK2))
      | r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK2)) ) ),
    inference(subsumption_resolution,[],[f162,f84])).

fof(f84,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f69,f43])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f162,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK2))
      | r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK2))
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f79,f41])).

fof(f41,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f79,plain,(
    ! [X6,X0] :
      ( ~ v1_funct_1(X0)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f32,f35,f34,f33])).

fof(f33,plain,(
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

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = sK4(X0,X1)
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1))
        & r2_hidden(sK5(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK6(X0,X5)) = X5
        & r2_hidden(sK6(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
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
    inference(rectify,[],[f31])).

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

fof(f132,plain,(
    ~ r1_tarski(sK1,k2_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f122,f125])).

fof(f125,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f48,f43])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f122,plain,(
    ~ r1_tarski(sK1,k2_relset_1(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f121,f46])).

fof(f46,plain,(
    sK1 != k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f121,plain,
    ( ~ r1_tarski(sK1,k2_relset_1(sK0,sK1,sK2))
    | sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f118,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f118,plain,(
    r1_tarski(k2_relset_1(sK0,sK1,sK2),sK1) ),
    inference(duplicate_literal_removal,[],[f116])).

fof(f116,plain,
    ( r1_tarski(k2_relset_1(sK0,sK1,sK2),sK1)
    | r1_tarski(k2_relset_1(sK0,sK1,sK2),sK1) ),
    inference(resolution,[],[f114,f66])).

fof(f114,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK7(X0,sK1),k2_relset_1(sK0,sK1,sK2))
      | r1_tarski(X0,sK1) ) ),
    inference(resolution,[],[f113,f67])).

fof(f113,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,k2_relset_1(sK0,sK1,sK2)) ) ),
    inference(resolution,[],[f112,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f112,plain,(
    m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f47,f43])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:26:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (1295)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.51  % (1293)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.52  % (1301)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.52  % (1288)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (1290)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.53  % (1291)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.27/0.53  % (1289)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.27/0.53  % (1296)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.27/0.53  % (1308)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.27/0.53  % (1309)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.27/0.54  % (1307)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.27/0.54  % (1300)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.27/0.54  % (1287)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.27/0.54  % (1299)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.27/0.54  % (1297)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.27/0.54  % (1314)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.27/0.54  % (1292)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.27/0.54  % (1296)Refutation not found, incomplete strategy% (1296)------------------------------
% 1.27/0.54  % (1296)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.54  % (1296)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.54  
% 1.27/0.54  % (1296)Memory used [KB]: 10746
% 1.27/0.54  % (1296)Time elapsed: 0.127 s
% 1.27/0.54  % (1296)------------------------------
% 1.27/0.54  % (1296)------------------------------
% 1.27/0.54  % (1286)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.27/0.54  % (1315)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.41/0.55  % (1303)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.41/0.55  % (1313)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.41/0.55  % (1303)Refutation not found, incomplete strategy% (1303)------------------------------
% 1.41/0.55  % (1303)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (1303)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.55  
% 1.41/0.55  % (1303)Memory used [KB]: 10746
% 1.41/0.55  % (1303)Time elapsed: 0.127 s
% 1.41/0.55  % (1303)------------------------------
% 1.41/0.55  % (1303)------------------------------
% 1.41/0.55  % (1312)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.41/0.55  % (1304)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.41/0.56  % (1302)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.41/0.56  % (1298)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.41/0.56  % (1291)Refutation found. Thanks to Tanya!
% 1.41/0.56  % SZS status Theorem for theBenchmark
% 1.41/0.56  % (1310)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.41/0.56  % (1305)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.41/0.56  % (1294)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.41/0.56  % (1306)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.41/0.57  % (1311)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.41/0.58  % SZS output start Proof for theBenchmark
% 1.41/0.58  fof(f397,plain,(
% 1.41/0.58    $false),
% 1.41/0.58    inference(subsumption_resolution,[],[f353,f70])).
% 1.41/0.58  fof(f70,plain,(
% 1.41/0.58    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.41/0.58    inference(cnf_transformation,[],[f3])).
% 1.41/0.58  fof(f3,axiom,(
% 1.41/0.58    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.41/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.41/0.58  fof(f353,plain,(
% 1.41/0.58    ~r1_tarski(k1_xboole_0,k2_relat_1(sK2))),
% 1.41/0.58    inference(backward_demodulation,[],[f132,f334])).
% 1.41/0.58  fof(f334,plain,(
% 1.41/0.58    k1_xboole_0 = sK1),
% 1.41/0.58    inference(subsumption_resolution,[],[f331,f132])).
% 1.41/0.58  fof(f331,plain,(
% 1.41/0.58    k1_xboole_0 = sK1 | r1_tarski(sK1,k2_relat_1(sK2))),
% 1.41/0.58    inference(resolution,[],[f328,f66])).
% 1.41/0.58  fof(f66,plain,(
% 1.41/0.58    ( ! [X0,X1] : (r2_hidden(sK7(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.41/0.58    inference(cnf_transformation,[],[f40])).
% 1.41/0.58  fof(f40,plain,(
% 1.41/0.58    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.41/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f38,f39])).
% 1.41/0.58  fof(f39,plain,(
% 1.41/0.58    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0)))),
% 1.41/0.58    introduced(choice_axiom,[])).
% 1.41/0.58  fof(f38,plain,(
% 1.41/0.58    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.41/0.58    inference(rectify,[],[f37])).
% 1.41/0.58  fof(f37,plain,(
% 1.41/0.58    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.41/0.58    inference(nnf_transformation,[],[f22])).
% 1.41/0.58  fof(f22,plain,(
% 1.41/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.41/0.58    inference(ennf_transformation,[],[f1])).
% 1.41/0.58  fof(f1,axiom,(
% 1.41/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.41/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.41/0.58  fof(f328,plain,(
% 1.41/0.58    ~r2_hidden(sK7(sK1,k2_relat_1(sK2)),sK1) | k1_xboole_0 = sK1),
% 1.41/0.58    inference(subsumption_resolution,[],[f324,f76])).
% 1.41/0.58  fof(f76,plain,(
% 1.41/0.58    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.41/0.58    inference(equality_resolution,[],[f57])).
% 1.41/0.58  fof(f57,plain,(
% 1.41/0.58    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.41/0.58    inference(cnf_transformation,[],[f30])).
% 1.41/0.58  fof(f30,plain,(
% 1.41/0.58    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.41/0.58    inference(flattening,[],[f29])).
% 1.41/0.58  fof(f29,plain,(
% 1.41/0.58    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.41/0.58    inference(nnf_transformation,[],[f2])).
% 1.41/0.58  fof(f2,axiom,(
% 1.41/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.41/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.41/0.58  fof(f324,plain,(
% 1.41/0.58    ~r1_tarski(sK0,sK0) | ~r2_hidden(sK7(sK1,k2_relat_1(sK2)),sK1) | k1_xboole_0 = sK1),
% 1.41/0.58    inference(superposition,[],[f293,f316])).
% 1.41/0.58  fof(f316,plain,(
% 1.41/0.58    sK0 = k1_relat_1(sK2) | k1_xboole_0 = sK1),
% 1.41/0.58    inference(superposition,[],[f315,f150])).
% 1.41/0.58  fof(f150,plain,(
% 1.41/0.58    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)),
% 1.41/0.58    inference(resolution,[],[f55,f43])).
% 1.41/0.58  fof(f43,plain,(
% 1.41/0.58    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.41/0.58    inference(cnf_transformation,[],[f27])).
% 1.41/0.58  fof(f27,plain,(
% 1.41/0.58    sK1 != k2_relset_1(sK0,sK1,sK2) & ! [X3] : ((k1_funct_1(sK2,sK3(X3)) = X3 & r2_hidden(sK3(X3),sK0)) | ~r2_hidden(X3,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 1.41/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f26,f25])).
% 1.41/0.58  fof(f25,plain,(
% 1.41/0.58    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (sK1 != k2_relset_1(sK0,sK1,sK2) & ! [X3] : (? [X4] : (k1_funct_1(sK2,X4) = X3 & r2_hidden(X4,sK0)) | ~r2_hidden(X3,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.41/0.58    introduced(choice_axiom,[])).
% 1.41/0.58  fof(f26,plain,(
% 1.41/0.58    ! [X3] : (? [X4] : (k1_funct_1(sK2,X4) = X3 & r2_hidden(X4,sK0)) => (k1_funct_1(sK2,sK3(X3)) = X3 & r2_hidden(sK3(X3),sK0)))),
% 1.41/0.58    introduced(choice_axiom,[])).
% 1.41/0.58  fof(f14,plain,(
% 1.41/0.58    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.41/0.58    inference(flattening,[],[f13])).
% 1.41/0.58  fof(f13,plain,(
% 1.41/0.58    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.41/0.58    inference(ennf_transformation,[],[f12])).
% 1.41/0.58  fof(f12,negated_conjecture,(
% 1.41/0.58    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 1.41/0.58    inference(negated_conjecture,[],[f11])).
% 1.41/0.58  fof(f11,conjecture,(
% 1.41/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 1.41/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_2)).
% 1.41/0.58  fof(f55,plain,(
% 1.41/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.41/0.58    inference(cnf_transformation,[],[f19])).
% 1.41/0.58  fof(f19,plain,(
% 1.41/0.58    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.41/0.58    inference(ennf_transformation,[],[f8])).
% 1.41/0.58  fof(f8,axiom,(
% 1.41/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.41/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.41/0.58  fof(f315,plain,(
% 1.41/0.58    sK0 = k1_relset_1(sK0,sK1,sK2) | k1_xboole_0 = sK1),
% 1.41/0.58    inference(subsumption_resolution,[],[f314,f42])).
% 1.41/0.58  fof(f42,plain,(
% 1.41/0.58    v1_funct_2(sK2,sK0,sK1)),
% 1.41/0.58    inference(cnf_transformation,[],[f27])).
% 1.41/0.58  fof(f314,plain,(
% 1.41/0.58    ~v1_funct_2(sK2,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2)),
% 1.41/0.58    inference(resolution,[],[f49,f43])).
% 1.41/0.58  fof(f49,plain,(
% 1.41/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 1.41/0.58    inference(cnf_transformation,[],[f28])).
% 1.41/0.58  fof(f28,plain,(
% 1.41/0.58    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.41/0.58    inference(nnf_transformation,[],[f18])).
% 1.41/0.58  fof(f18,plain,(
% 1.41/0.58    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.41/0.58    inference(flattening,[],[f17])).
% 1.41/0.58  fof(f17,plain,(
% 1.41/0.58    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.41/0.58    inference(ennf_transformation,[],[f10])).
% 1.41/0.58  fof(f10,axiom,(
% 1.41/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.41/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.41/0.58  fof(f293,plain,(
% 1.41/0.58    ~r1_tarski(sK0,k1_relat_1(sK2)) | ~r2_hidden(sK7(sK1,k2_relat_1(sK2)),sK1)),
% 1.41/0.58    inference(resolution,[],[f292,f44])).
% 1.41/0.58  fof(f44,plain,(
% 1.41/0.58    ( ! [X3] : (r2_hidden(sK3(X3),sK0) | ~r2_hidden(X3,sK1)) )),
% 1.41/0.58    inference(cnf_transformation,[],[f27])).
% 1.41/0.58  fof(f292,plain,(
% 1.41/0.58    ( ! [X0] : (~r2_hidden(sK3(sK7(sK1,k2_relat_1(sK2))),X0) | ~r1_tarski(X0,k1_relat_1(sK2))) )),
% 1.41/0.58    inference(subsumption_resolution,[],[f288,f132])).
% 1.41/0.58  fof(f288,plain,(
% 1.41/0.58    ( ! [X0] : (~r2_hidden(sK3(sK7(sK1,k2_relat_1(sK2))),X0) | ~r1_tarski(X0,k1_relat_1(sK2)) | r1_tarski(sK1,k2_relat_1(sK2))) )),
% 1.41/0.58    inference(resolution,[],[f168,f67])).
% 1.41/0.58  fof(f67,plain,(
% 1.41/0.58    ( ! [X0,X1] : (~r2_hidden(sK7(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.41/0.58    inference(cnf_transformation,[],[f40])).
% 1.41/0.58  fof(f168,plain,(
% 1.41/0.58    ( ! [X0] : (r2_hidden(sK7(sK1,k2_relat_1(sK2)),k2_relat_1(sK2)) | ~r2_hidden(sK3(sK7(sK1,k2_relat_1(sK2))),X0) | ~r1_tarski(X0,k1_relat_1(sK2))) )),
% 1.41/0.58    inference(superposition,[],[f165,f151])).
% 1.41/0.58  fof(f151,plain,(
% 1.41/0.58    sK7(sK1,k2_relat_1(sK2)) = k1_funct_1(sK2,sK3(sK7(sK1,k2_relat_1(sK2))))),
% 1.41/0.58    inference(resolution,[],[f85,f132])).
% 1.41/0.58  fof(f85,plain,(
% 1.41/0.58    ( ! [X0] : (r1_tarski(sK1,X0) | sK7(sK1,X0) = k1_funct_1(sK2,sK3(sK7(sK1,X0)))) )),
% 1.41/0.58    inference(resolution,[],[f45,f66])).
% 1.41/0.58  fof(f45,plain,(
% 1.41/0.58    ( ! [X3] : (~r2_hidden(X3,sK1) | k1_funct_1(sK2,sK3(X3)) = X3) )),
% 1.41/0.58    inference(cnf_transformation,[],[f27])).
% 1.41/0.58  fof(f165,plain,(
% 1.41/0.58    ( ! [X2,X1] : (r2_hidden(k1_funct_1(sK2,X1),k2_relat_1(sK2)) | ~r2_hidden(X1,X2) | ~r1_tarski(X2,k1_relat_1(sK2))) )),
% 1.41/0.58    inference(resolution,[],[f163,f65])).
% 1.41/0.58  fof(f65,plain,(
% 1.41/0.58    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 1.41/0.58    inference(cnf_transformation,[],[f40])).
% 1.41/0.58  fof(f163,plain,(
% 1.41/0.58    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK2)) | r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK2))) )),
% 1.41/0.58    inference(subsumption_resolution,[],[f162,f84])).
% 1.41/0.58  fof(f84,plain,(
% 1.41/0.58    v1_relat_1(sK2)),
% 1.41/0.58    inference(resolution,[],[f69,f43])).
% 1.41/0.58  fof(f69,plain,(
% 1.41/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.41/0.58    inference(cnf_transformation,[],[f24])).
% 1.41/0.58  fof(f24,plain,(
% 1.41/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.41/0.58    inference(ennf_transformation,[],[f6])).
% 1.41/0.58  fof(f6,axiom,(
% 1.41/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.41/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.41/0.58  fof(f162,plain,(
% 1.41/0.58    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK2)) | r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK2)) | ~v1_relat_1(sK2)) )),
% 1.41/0.58    inference(resolution,[],[f79,f41])).
% 1.41/0.58  fof(f41,plain,(
% 1.41/0.58    v1_funct_1(sK2)),
% 1.41/0.58    inference(cnf_transformation,[],[f27])).
% 1.41/0.58  fof(f79,plain,(
% 1.41/0.58    ( ! [X6,X0] : (~v1_funct_1(X0) | ~r2_hidden(X6,k1_relat_1(X0)) | r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.41/0.58    inference(equality_resolution,[],[f78])).
% 1.41/0.58  fof(f78,plain,(
% 1.41/0.58    ( ! [X6,X0,X1] : (r2_hidden(k1_funct_1(X0,X6),X1) | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.41/0.58    inference(equality_resolution,[],[f61])).
% 1.41/0.58  fof(f61,plain,(
% 1.41/0.58    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.41/0.58    inference(cnf_transformation,[],[f36])).
% 1.41/0.58  fof(f36,plain,(
% 1.41/0.58    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK4(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK4(X0,X1),X1)) & ((sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1)) & r2_hidden(sK5(X0,X1),k1_relat_1(X0))) | r2_hidden(sK4(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK6(X0,X5)) = X5 & r2_hidden(sK6(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.41/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f32,f35,f34,f33])).
% 1.41/0.58  fof(f33,plain,(
% 1.41/0.58    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK4(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK4(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK4(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK4(X0,X1),X1))))),
% 1.41/0.58    introduced(choice_axiom,[])).
% 1.41/0.58  fof(f34,plain,(
% 1.41/0.58    ! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = sK4(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) => (sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1)) & r2_hidden(sK5(X0,X1),k1_relat_1(X0))))),
% 1.41/0.58    introduced(choice_axiom,[])).
% 1.41/0.58  fof(f35,plain,(
% 1.41/0.58    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK6(X0,X5)) = X5 & r2_hidden(sK6(X0,X5),k1_relat_1(X0))))),
% 1.41/0.58    introduced(choice_axiom,[])).
% 1.41/0.58  fof(f32,plain,(
% 1.41/0.58    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.41/0.58    inference(rectify,[],[f31])).
% 1.41/0.58  fof(f31,plain,(
% 1.41/0.58    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.41/0.58    inference(nnf_transformation,[],[f21])).
% 1.41/0.58  fof(f21,plain,(
% 1.41/0.58    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.41/0.58    inference(flattening,[],[f20])).
% 1.41/0.58  fof(f20,plain,(
% 1.41/0.58    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.41/0.58    inference(ennf_transformation,[],[f5])).
% 1.41/0.58  fof(f5,axiom,(
% 1.41/0.58    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 1.41/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).
% 1.41/0.58  fof(f132,plain,(
% 1.41/0.58    ~r1_tarski(sK1,k2_relat_1(sK2))),
% 1.41/0.58    inference(backward_demodulation,[],[f122,f125])).
% 1.41/0.58  fof(f125,plain,(
% 1.41/0.58    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 1.41/0.58    inference(resolution,[],[f48,f43])).
% 1.41/0.58  fof(f48,plain,(
% 1.41/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.41/0.58    inference(cnf_transformation,[],[f16])).
% 1.41/0.58  fof(f16,plain,(
% 1.41/0.58    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.41/0.58    inference(ennf_transformation,[],[f9])).
% 1.41/0.58  fof(f9,axiom,(
% 1.41/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.41/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.41/0.58  fof(f122,plain,(
% 1.41/0.58    ~r1_tarski(sK1,k2_relset_1(sK0,sK1,sK2))),
% 1.41/0.58    inference(subsumption_resolution,[],[f121,f46])).
% 1.41/0.58  fof(f46,plain,(
% 1.41/0.58    sK1 != k2_relset_1(sK0,sK1,sK2)),
% 1.41/0.58    inference(cnf_transformation,[],[f27])).
% 1.41/0.58  fof(f121,plain,(
% 1.41/0.58    ~r1_tarski(sK1,k2_relset_1(sK0,sK1,sK2)) | sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.41/0.58    inference(resolution,[],[f118,f58])).
% 1.41/0.58  fof(f58,plain,(
% 1.41/0.58    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.41/0.58    inference(cnf_transformation,[],[f30])).
% 1.41/0.58  fof(f118,plain,(
% 1.41/0.58    r1_tarski(k2_relset_1(sK0,sK1,sK2),sK1)),
% 1.41/0.58    inference(duplicate_literal_removal,[],[f116])).
% 1.41/0.58  fof(f116,plain,(
% 1.41/0.58    r1_tarski(k2_relset_1(sK0,sK1,sK2),sK1) | r1_tarski(k2_relset_1(sK0,sK1,sK2),sK1)),
% 1.41/0.58    inference(resolution,[],[f114,f66])).
% 1.41/0.58  fof(f114,plain,(
% 1.41/0.58    ( ! [X0] : (~r2_hidden(sK7(X0,sK1),k2_relset_1(sK0,sK1,sK2)) | r1_tarski(X0,sK1)) )),
% 1.41/0.58    inference(resolution,[],[f113,f67])).
% 1.41/0.58  fof(f113,plain,(
% 1.41/0.58    ( ! [X0] : (r2_hidden(X0,sK1) | ~r2_hidden(X0,k2_relset_1(sK0,sK1,sK2))) )),
% 1.41/0.58    inference(resolution,[],[f112,f68])).
% 1.41/0.58  fof(f68,plain,(
% 1.41/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 1.41/0.58    inference(cnf_transformation,[],[f23])).
% 1.41/0.58  fof(f23,plain,(
% 1.41/0.58    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.41/0.58    inference(ennf_transformation,[],[f4])).
% 1.41/0.58  fof(f4,axiom,(
% 1.41/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.41/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 1.41/0.58  fof(f112,plain,(
% 1.41/0.58    m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1))),
% 1.41/0.58    inference(resolution,[],[f47,f43])).
% 1.41/0.58  fof(f47,plain,(
% 1.41/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))) )),
% 1.41/0.58    inference(cnf_transformation,[],[f15])).
% 1.41/0.58  fof(f15,plain,(
% 1.41/0.58    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.41/0.58    inference(ennf_transformation,[],[f7])).
% 1.41/0.58  fof(f7,axiom,(
% 1.41/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 1.41/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 1.41/0.58  % SZS output end Proof for theBenchmark
% 1.41/0.58  % (1291)------------------------------
% 1.41/0.58  % (1291)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.58  % (1291)Termination reason: Refutation
% 1.41/0.58  
% 1.41/0.58  % (1291)Memory used [KB]: 6524
% 1.41/0.58  % (1291)Time elapsed: 0.148 s
% 1.41/0.58  % (1291)------------------------------
% 1.41/0.58  % (1291)------------------------------
% 1.41/0.58  % (1285)Success in time 0.214 s
%------------------------------------------------------------------------------
