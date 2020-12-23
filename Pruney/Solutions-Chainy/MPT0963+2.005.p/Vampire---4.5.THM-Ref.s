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
% DateTime   : Thu Dec  3 13:00:28 EST 2020

% Result     : Theorem 1.54s
% Output     : Refutation 1.54s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 327 expanded)
%              Number of leaves         :   12 (  88 expanded)
%              Depth                    :   16
%              Number of atoms          :  298 (2199 expanded)
%              Number of equality atoms :   46 ( 328 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f124,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f58,f60,f111,f123])).

fof(f123,plain,(
    spl7_3 ),
    inference(avatar_contradiction_clause,[],[f122])).

fof(f122,plain,
    ( $false
    | spl7_3 ),
    inference(subsumption_resolution,[],[f120,f118])).

fof(f118,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK1)
    | spl7_3 ),
    inference(resolution,[],[f57,f87])).

fof(f87,plain,(
    ! [X0] :
      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
      | ~ r1_tarski(k2_relat_1(sK2),X0) ) ),
    inference(forward_demodulation,[],[f86,f27])).

fof(f27,plain,(
    sK0 = k1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_2(sK2,sK0,sK1)
      | ~ v1_funct_1(sK2) )
    & ! [X3] :
        ( r2_hidden(k1_funct_1(sK2,X3),sK1)
        | ~ r2_hidden(X3,sK0) )
    & sK0 = k1_relat_1(sK2)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2) )
        & ! [X3] :
            ( r2_hidden(k1_funct_1(X2,X3),X1)
            | ~ r2_hidden(X3,X0) )
        & k1_relat_1(X2) = X0
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_2(sK2,sK0,sK1)
        | ~ v1_funct_1(sK2) )
      & ! [X3] :
          ( r2_hidden(k1_funct_1(sK2,X3),sK1)
          | ~ r2_hidden(X3,sK0) )
      & sK0 = k1_relat_1(sK2)
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2) )
      & ! [X3] :
          ( r2_hidden(k1_funct_1(X2,X3),X1)
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2) )
      & ! [X3] :
          ( r2_hidden(k1_funct_1(X2,X3),X1)
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( ! [X3] :
                ( r2_hidden(X3,X0)
               => r2_hidden(k1_funct_1(X2,X3),X1) )
            & k1_relat_1(X2) = X0 )
         => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X2,X0,X1)
            & v1_funct_1(X2) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( ! [X3] :
              ( r2_hidden(X3,X0)
             => r2_hidden(k1_funct_1(X2,X3),X1) )
          & k1_relat_1(X2) = X0 )
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_funct_2)).

fof(f86,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK2),X0)
      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X0))) ) ),
    inference(subsumption_resolution,[],[f85,f25])).

fof(f25,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f85,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK2),X0)
      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X0)))
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f38,f26])).

fof(f26,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

fof(f57,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl7_3 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl7_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f120,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | spl7_3 ),
    inference(resolution,[],[f119,f98])).

fof(f98,plain,(
    ! [X3] :
      ( r2_hidden(sK6(k2_relat_1(sK2),X3),sK1)
      | r1_tarski(k2_relat_1(sK2),X3) ) ),
    inference(resolution,[],[f95,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK6(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f22,f23])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f95,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK2))
      | r2_hidden(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f93,f84])).

fof(f84,plain,(
    ! [X0] :
      ( r2_hidden(sK5(sK2,X0),sK0)
      | ~ r2_hidden(X0,k2_relat_1(sK2)) ) ),
    inference(subsumption_resolution,[],[f83,f25])).

fof(f83,plain,(
    ! [X0] :
      ( r2_hidden(sK5(sK2,X0),sK0)
      | ~ r2_hidden(X0,k2_relat_1(sK2))
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f82,f26])).

fof(f82,plain,(
    ! [X0] :
      ( r2_hidden(sK5(sK2,X0),sK0)
      | ~ r2_hidden(X0,k2_relat_1(sK2))
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f45,f27])).

fof(f45,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK5(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK5(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK3(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK3(X0,X1),X1) )
              & ( ( sK3(X0,X1) = k1_funct_1(X0,sK4(X0,X1))
                  & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK3(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK5(X0,X5)) = X5
                    & r2_hidden(sK5(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f16,f19,f18,f17])).

fof(f17,plain,(
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
              ( k1_funct_1(X0,X3) != sK3(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK3(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = sK3(X0,X1)
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( sK3(X0,X1) = k1_funct_1(X0,sK4(X0,X1))
        & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK5(X0,X5)) = X5
        & r2_hidden(sK5(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
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
    inference(rectify,[],[f15])).

fof(f15,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
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
    inference(flattening,[],[f8])).

fof(f8,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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

fof(f93,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK1)
      | ~ r2_hidden(sK5(sK2,X0),sK0)
      | ~ r2_hidden(X0,k2_relat_1(sK2)) ) ),
    inference(superposition,[],[f28,f92])).

fof(f92,plain,(
    ! [X0] :
      ( k1_funct_1(sK2,sK5(sK2,X0)) = X0
      | ~ r2_hidden(X0,k2_relat_1(sK2)) ) ),
    inference(subsumption_resolution,[],[f91,f25])).

fof(f91,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK2))
      | k1_funct_1(sK2,sK5(sK2,X0)) = X0
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f44,f26])).

fof(f44,plain,(
    ! [X0,X5] :
      ( ~ v1_funct_1(X0)
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | k1_funct_1(X0,sK5(X0,X5)) = X5
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK5(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f28,plain,(
    ! [X3] :
      ( r2_hidden(k1_funct_1(sK2,X3),sK1)
      | ~ r2_hidden(X3,sK0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f119,plain,
    ( ~ r2_hidden(sK6(k2_relat_1(sK2),sK1),sK1)
    | spl7_3 ),
    inference(resolution,[],[f118,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK6(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f111,plain,(
    spl7_2 ),
    inference(avatar_contradiction_clause,[],[f110])).

fof(f110,plain,
    ( $false
    | spl7_2 ),
    inference(subsumption_resolution,[],[f103,f64])).

fof(f64,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK1)
    | spl7_2 ),
    inference(resolution,[],[f63,f53])).

fof(f53,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl7_2
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f63,plain,(
    ! [X0] :
      ( v1_funct_2(sK2,sK0,X0)
      | ~ r1_tarski(k2_relat_1(sK2),X0) ) ),
    inference(forward_demodulation,[],[f62,f27])).

fof(f62,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK2),X0)
      | v1_funct_2(sK2,k1_relat_1(sK2),X0) ) ),
    inference(subsumption_resolution,[],[f61,f25])).

% (27963)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
fof(f61,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK2),X0)
      | v1_funct_2(sK2,k1_relat_1(sK2),X0)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f37,f26])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f103,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | spl7_2 ),
    inference(resolution,[],[f98,f65])).

fof(f65,plain,
    ( ~ r2_hidden(sK6(k2_relat_1(sK2),sK1),sK1)
    | spl7_2 ),
    inference(resolution,[],[f64,f41])).

fof(f60,plain,(
    spl7_1 ),
    inference(avatar_contradiction_clause,[],[f59])).

fof(f59,plain,
    ( $false
    | spl7_1 ),
    inference(subsumption_resolution,[],[f49,f26])).

fof(f49,plain,
    ( ~ v1_funct_1(sK2)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl7_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f58,plain,
    ( ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f29,f55,f51,f47])).

fof(f29,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f14])).
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
% 0.14/0.35  % DateTime   : Tue Dec  1 12:10:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.54  % (27941)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.40/0.57  % (27943)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.54/0.57  % (27962)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.54/0.57  % (27949)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.54/0.57  % (27943)Refutation found. Thanks to Tanya!
% 1.54/0.57  % SZS status Theorem for theBenchmark
% 1.54/0.58  % (27953)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.54/0.58  % (27946)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.54/0.58  % (27958)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.54/0.58  % SZS output start Proof for theBenchmark
% 1.54/0.58  fof(f124,plain,(
% 1.54/0.58    $false),
% 1.54/0.58    inference(avatar_sat_refutation,[],[f58,f60,f111,f123])).
% 1.54/0.58  fof(f123,plain,(
% 1.54/0.58    spl7_3),
% 1.54/0.58    inference(avatar_contradiction_clause,[],[f122])).
% 1.54/0.58  fof(f122,plain,(
% 1.54/0.58    $false | spl7_3),
% 1.54/0.58    inference(subsumption_resolution,[],[f120,f118])).
% 1.54/0.58  fof(f118,plain,(
% 1.54/0.58    ~r1_tarski(k2_relat_1(sK2),sK1) | spl7_3),
% 1.54/0.58    inference(resolution,[],[f57,f87])).
% 1.54/0.58  fof(f87,plain,(
% 1.54/0.58    ( ! [X0] : (m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | ~r1_tarski(k2_relat_1(sK2),X0)) )),
% 1.54/0.58    inference(forward_demodulation,[],[f86,f27])).
% 1.54/0.58  fof(f27,plain,(
% 1.54/0.58    sK0 = k1_relat_1(sK2)),
% 1.54/0.58    inference(cnf_transformation,[],[f14])).
% 1.54/0.58  fof(f14,plain,(
% 1.54/0.58    (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) & ! [X3] : (r2_hidden(k1_funct_1(sK2,X3),sK1) | ~r2_hidden(X3,sK0)) & sK0 = k1_relat_1(sK2) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 1.54/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f13])).
% 1.54/0.58  fof(f13,plain,(
% 1.54/0.58    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & ! [X3] : (r2_hidden(k1_funct_1(X2,X3),X1) | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => ((~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) & ! [X3] : (r2_hidden(k1_funct_1(sK2,X3),sK1) | ~r2_hidden(X3,sK0)) & sK0 = k1_relat_1(sK2) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 1.54/0.58    introduced(choice_axiom,[])).
% 1.54/0.58  fof(f7,plain,(
% 1.54/0.58    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & ! [X3] : (r2_hidden(k1_funct_1(X2,X3),X1) | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.54/0.58    inference(flattening,[],[f6])).
% 1.54/0.58  fof(f6,plain,(
% 1.54/0.58    ? [X0,X1,X2] : (((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & (! [X3] : (r2_hidden(k1_funct_1(X2,X3),X1) | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0)) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 1.54/0.58    inference(ennf_transformation,[],[f5])).
% 1.54/0.58  fof(f5,negated_conjecture,(
% 1.54/0.58    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,X0) => r2_hidden(k1_funct_1(X2,X3),X1)) & k1_relat_1(X2) = X0) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 1.54/0.58    inference(negated_conjecture,[],[f4])).
% 1.54/0.58  fof(f4,conjecture,(
% 1.54/0.58    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,X0) => r2_hidden(k1_funct_1(X2,X3),X1)) & k1_relat_1(X2) = X0) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 1.54/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_funct_2)).
% 1.54/0.58  fof(f86,plain,(
% 1.54/0.58    ( ! [X0] : (~r1_tarski(k2_relat_1(sK2),X0) | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X0)))) )),
% 1.54/0.58    inference(subsumption_resolution,[],[f85,f25])).
% 1.54/0.58  fof(f25,plain,(
% 1.54/0.58    v1_relat_1(sK2)),
% 1.54/0.58    inference(cnf_transformation,[],[f14])).
% 1.54/0.58  fof(f85,plain,(
% 1.54/0.58    ( ! [X0] : (~r1_tarski(k2_relat_1(sK2),X0) | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X0))) | ~v1_relat_1(sK2)) )),
% 1.54/0.58    inference(resolution,[],[f38,f26])).
% 1.54/0.58  fof(f26,plain,(
% 1.54/0.58    v1_funct_1(sK2)),
% 1.54/0.58    inference(cnf_transformation,[],[f14])).
% 1.54/0.58  fof(f38,plain,(
% 1.54/0.58    ( ! [X0,X1] : (~v1_funct_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_relat_1(X1)) )),
% 1.54/0.58    inference(cnf_transformation,[],[f11])).
% 1.54/0.58  fof(f11,plain,(
% 1.54/0.58    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.54/0.58    inference(flattening,[],[f10])).
% 1.54/0.58  fof(f10,plain,(
% 1.54/0.58    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.54/0.58    inference(ennf_transformation,[],[f3])).
% 1.54/0.58  fof(f3,axiom,(
% 1.54/0.58    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 1.54/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).
% 1.54/0.58  fof(f57,plain,(
% 1.54/0.58    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl7_3),
% 1.54/0.58    inference(avatar_component_clause,[],[f55])).
% 1.54/0.58  fof(f55,plain,(
% 1.54/0.58    spl7_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.54/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 1.54/0.58  fof(f120,plain,(
% 1.54/0.58    r1_tarski(k2_relat_1(sK2),sK1) | spl7_3),
% 1.54/0.58    inference(resolution,[],[f119,f98])).
% 1.54/0.58  fof(f98,plain,(
% 1.54/0.58    ( ! [X3] : (r2_hidden(sK6(k2_relat_1(sK2),X3),sK1) | r1_tarski(k2_relat_1(sK2),X3)) )),
% 1.54/0.58    inference(resolution,[],[f95,f40])).
% 1.54/0.58  fof(f40,plain,(
% 1.54/0.58    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.54/0.58    inference(cnf_transformation,[],[f24])).
% 1.54/0.58  fof(f24,plain,(
% 1.54/0.58    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.54/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f22,f23])).
% 1.54/0.58  fof(f23,plain,(
% 1.54/0.58    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)))),
% 1.54/0.58    introduced(choice_axiom,[])).
% 1.54/0.58  fof(f22,plain,(
% 1.54/0.58    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.54/0.58    inference(rectify,[],[f21])).
% 1.54/0.58  fof(f21,plain,(
% 1.54/0.58    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.54/0.58    inference(nnf_transformation,[],[f12])).
% 1.54/0.58  fof(f12,plain,(
% 1.54/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.54/0.58    inference(ennf_transformation,[],[f1])).
% 1.54/0.58  fof(f1,axiom,(
% 1.54/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.54/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.54/0.58  fof(f95,plain,(
% 1.54/0.58    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK2)) | r2_hidden(X0,sK1)) )),
% 1.54/0.58    inference(subsumption_resolution,[],[f93,f84])).
% 1.54/0.58  fof(f84,plain,(
% 1.54/0.58    ( ! [X0] : (r2_hidden(sK5(sK2,X0),sK0) | ~r2_hidden(X0,k2_relat_1(sK2))) )),
% 1.54/0.58    inference(subsumption_resolution,[],[f83,f25])).
% 1.54/0.58  fof(f83,plain,(
% 1.54/0.58    ( ! [X0] : (r2_hidden(sK5(sK2,X0),sK0) | ~r2_hidden(X0,k2_relat_1(sK2)) | ~v1_relat_1(sK2)) )),
% 1.54/0.58    inference(subsumption_resolution,[],[f82,f26])).
% 1.54/0.58  fof(f82,plain,(
% 1.54/0.58    ( ! [X0] : (r2_hidden(sK5(sK2,X0),sK0) | ~r2_hidden(X0,k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 1.54/0.58    inference(superposition,[],[f45,f27])).
% 1.54/0.58  fof(f45,plain,(
% 1.54/0.58    ( ! [X0,X5] : (r2_hidden(sK5(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.54/0.58    inference(equality_resolution,[],[f30])).
% 1.54/0.58  fof(f30,plain,(
% 1.54/0.58    ( ! [X0,X5,X1] : (r2_hidden(sK5(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.54/0.58    inference(cnf_transformation,[],[f20])).
% 1.54/0.58  fof(f20,plain,(
% 1.54/0.58    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK3(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK3(X0,X1),X1)) & ((sK3(X0,X1) = k1_funct_1(X0,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),k1_relat_1(X0))) | r2_hidden(sK3(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK5(X0,X5)) = X5 & r2_hidden(sK5(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.54/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f16,f19,f18,f17])).
% 1.54/0.58  fof(f17,plain,(
% 1.54/0.58    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK3(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK3(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK3(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK3(X0,X1),X1))))),
% 1.54/0.58    introduced(choice_axiom,[])).
% 1.54/0.58  fof(f18,plain,(
% 1.54/0.58    ! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = sK3(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) => (sK3(X0,X1) = k1_funct_1(X0,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),k1_relat_1(X0))))),
% 1.54/0.58    introduced(choice_axiom,[])).
% 1.54/0.58  fof(f19,plain,(
% 1.54/0.58    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK5(X0,X5)) = X5 & r2_hidden(sK5(X0,X5),k1_relat_1(X0))))),
% 1.54/0.58    introduced(choice_axiom,[])).
% 1.54/0.58  fof(f16,plain,(
% 1.54/0.58    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.54/0.58    inference(rectify,[],[f15])).
% 1.54/0.59  fof(f15,plain,(
% 1.54/0.59    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.54/0.59    inference(nnf_transformation,[],[f9])).
% 1.54/0.59  fof(f9,plain,(
% 1.54/0.59    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.54/0.59    inference(flattening,[],[f8])).
% 1.54/0.59  fof(f8,plain,(
% 1.54/0.59    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.54/0.59    inference(ennf_transformation,[],[f2])).
% 1.54/0.59  fof(f2,axiom,(
% 1.54/0.59    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 1.54/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).
% 1.54/0.59  fof(f93,plain,(
% 1.54/0.59    ( ! [X0] : (r2_hidden(X0,sK1) | ~r2_hidden(sK5(sK2,X0),sK0) | ~r2_hidden(X0,k2_relat_1(sK2))) )),
% 1.54/0.59    inference(superposition,[],[f28,f92])).
% 1.54/0.59  fof(f92,plain,(
% 1.54/0.59    ( ! [X0] : (k1_funct_1(sK2,sK5(sK2,X0)) = X0 | ~r2_hidden(X0,k2_relat_1(sK2))) )),
% 1.54/0.59    inference(subsumption_resolution,[],[f91,f25])).
% 1.54/0.59  fof(f91,plain,(
% 1.54/0.59    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK2)) | k1_funct_1(sK2,sK5(sK2,X0)) = X0 | ~v1_relat_1(sK2)) )),
% 1.54/0.59    inference(resolution,[],[f44,f26])).
% 1.54/0.59  fof(f44,plain,(
% 1.54/0.59    ( ! [X0,X5] : (~v1_funct_1(X0) | ~r2_hidden(X5,k2_relat_1(X0)) | k1_funct_1(X0,sK5(X0,X5)) = X5 | ~v1_relat_1(X0)) )),
% 1.54/0.59    inference(equality_resolution,[],[f31])).
% 1.54/0.59  fof(f31,plain,(
% 1.54/0.59    ( ! [X0,X5,X1] : (k1_funct_1(X0,sK5(X0,X5)) = X5 | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.54/0.59    inference(cnf_transformation,[],[f20])).
% 1.54/0.59  fof(f28,plain,(
% 1.54/0.59    ( ! [X3] : (r2_hidden(k1_funct_1(sK2,X3),sK1) | ~r2_hidden(X3,sK0)) )),
% 1.54/0.59    inference(cnf_transformation,[],[f14])).
% 1.54/0.59  fof(f119,plain,(
% 1.54/0.59    ~r2_hidden(sK6(k2_relat_1(sK2),sK1),sK1) | spl7_3),
% 1.54/0.59    inference(resolution,[],[f118,f41])).
% 1.54/0.59  fof(f41,plain,(
% 1.54/0.59    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK6(X0,X1),X1)) )),
% 1.54/0.59    inference(cnf_transformation,[],[f24])).
% 1.54/0.59  fof(f111,plain,(
% 1.54/0.59    spl7_2),
% 1.54/0.59    inference(avatar_contradiction_clause,[],[f110])).
% 1.54/0.59  fof(f110,plain,(
% 1.54/0.59    $false | spl7_2),
% 1.54/0.59    inference(subsumption_resolution,[],[f103,f64])).
% 1.54/0.59  fof(f64,plain,(
% 1.54/0.59    ~r1_tarski(k2_relat_1(sK2),sK1) | spl7_2),
% 1.54/0.59    inference(resolution,[],[f63,f53])).
% 1.54/0.59  fof(f53,plain,(
% 1.54/0.59    ~v1_funct_2(sK2,sK0,sK1) | spl7_2),
% 1.54/0.59    inference(avatar_component_clause,[],[f51])).
% 1.54/0.59  fof(f51,plain,(
% 1.54/0.59    spl7_2 <=> v1_funct_2(sK2,sK0,sK1)),
% 1.54/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 1.54/0.59  fof(f63,plain,(
% 1.54/0.59    ( ! [X0] : (v1_funct_2(sK2,sK0,X0) | ~r1_tarski(k2_relat_1(sK2),X0)) )),
% 1.54/0.59    inference(forward_demodulation,[],[f62,f27])).
% 1.54/0.59  fof(f62,plain,(
% 1.54/0.59    ( ! [X0] : (~r1_tarski(k2_relat_1(sK2),X0) | v1_funct_2(sK2,k1_relat_1(sK2),X0)) )),
% 1.54/0.59    inference(subsumption_resolution,[],[f61,f25])).
% 1.54/0.59  % (27963)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.54/0.59  fof(f61,plain,(
% 1.54/0.59    ( ! [X0] : (~r1_tarski(k2_relat_1(sK2),X0) | v1_funct_2(sK2,k1_relat_1(sK2),X0) | ~v1_relat_1(sK2)) )),
% 1.54/0.59    inference(resolution,[],[f37,f26])).
% 1.54/0.59  fof(f37,plain,(
% 1.54/0.59    ( ! [X0,X1] : (~v1_funct_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.54/0.59    inference(cnf_transformation,[],[f11])).
% 1.54/0.59  fof(f103,plain,(
% 1.54/0.59    r1_tarski(k2_relat_1(sK2),sK1) | spl7_2),
% 1.54/0.59    inference(resolution,[],[f98,f65])).
% 1.54/0.59  fof(f65,plain,(
% 1.54/0.59    ~r2_hidden(sK6(k2_relat_1(sK2),sK1),sK1) | spl7_2),
% 1.54/0.59    inference(resolution,[],[f64,f41])).
% 1.54/0.59  fof(f60,plain,(
% 1.54/0.59    spl7_1),
% 1.54/0.59    inference(avatar_contradiction_clause,[],[f59])).
% 1.54/0.59  fof(f59,plain,(
% 1.54/0.59    $false | spl7_1),
% 1.54/0.59    inference(subsumption_resolution,[],[f49,f26])).
% 1.54/0.59  fof(f49,plain,(
% 1.54/0.59    ~v1_funct_1(sK2) | spl7_1),
% 1.54/0.59    inference(avatar_component_clause,[],[f47])).
% 1.54/0.59  fof(f47,plain,(
% 1.54/0.59    spl7_1 <=> v1_funct_1(sK2)),
% 1.54/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.54/0.59  fof(f58,plain,(
% 1.54/0.59    ~spl7_1 | ~spl7_2 | ~spl7_3),
% 1.54/0.59    inference(avatar_split_clause,[],[f29,f55,f51,f47])).
% 1.54/0.59  fof(f29,plain,(
% 1.54/0.59    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 1.54/0.59    inference(cnf_transformation,[],[f14])).
% 1.54/0.59  % SZS output end Proof for theBenchmark
% 1.54/0.59  % (27943)------------------------------
% 1.54/0.59  % (27943)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.59  % (27943)Termination reason: Refutation
% 1.54/0.59  
% 1.54/0.59  % (27943)Memory used [KB]: 10746
% 1.54/0.59  % (27943)Time elapsed: 0.138 s
% 1.54/0.59  % (27943)------------------------------
% 1.54/0.59  % (27943)------------------------------
% 1.54/0.59  % (27939)Success in time 0.226 s
%------------------------------------------------------------------------------
