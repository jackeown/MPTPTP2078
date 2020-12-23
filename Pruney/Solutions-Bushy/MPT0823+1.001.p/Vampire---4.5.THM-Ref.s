%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0823+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:42 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 330 expanded)
%              Number of leaves         :   23 ( 101 expanded)
%              Depth                    :   19
%              Number of atoms          :  412 (1428 expanded)
%              Number of equality atoms :   86 ( 340 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f512,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f67,f80,f90,f451,f466,f469,f511])).

fof(f511,plain,(
    spl11_7 ),
    inference(avatar_contradiction_clause,[],[f510])).

fof(f510,plain,
    ( $false
    | spl11_7 ),
    inference(subsumption_resolution,[],[f509,f137])).

fof(f137,plain,(
    v1_relat_1(k4_relat_1(sK2)) ),
    inference(resolution,[],[f127,f36])).

fof(f36,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ( k1_relset_1(sK0,sK1,sK2) != k2_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2))
      | k2_relset_1(sK0,sK1,sK2) != k1_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2)) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_relset_1(X0,X1,X2) != k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2))
          | k2_relset_1(X0,X1,X2) != k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ( k1_relset_1(sK0,sK1,sK2) != k2_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2))
        | k2_relset_1(sK0,sK1,sK2) != k1_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2)) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) != k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2))
        | k2_relset_1(X0,X1,X2) != k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( k1_relset_1(X0,X1,X2) = k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2))
          & k2_relset_1(X0,X1,X2) = k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2))
        & k2_relset_1(X0,X1,X2) = k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_relset_1)).

fof(f127,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | v1_relat_1(k4_relat_1(X3)) ) ),
    inference(resolution,[],[f88,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_relat_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(duplicate_literal_removal,[],[f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_relat_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f54,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k3_relset_1(X0,X1,X2) = k4_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k3_relset_1(X0,X1,X2) = k4_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k3_relset_1(X0,X1,X2) = k4_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_relset_1)).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_relset_1)).

fof(f509,plain,
    ( ~ v1_relat_1(k4_relat_1(sK2))
    | spl11_7 ),
    inference(subsumption_resolution,[],[f502,f68])).

fof(f68,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f50,f36])).

fof(f502,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_relat_1(k4_relat_1(sK2))
    | spl11_7 ),
    inference(trivial_inequality_removal,[],[f489])).

fof(f489,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(k4_relat_1(sK2))
    | spl11_7 ),
    inference(superposition,[],[f472,f448])).

fof(f448,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k4_relat_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f427])).

fof(f427,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k4_relat_1(X0)) ) ),
    inference(superposition,[],[f426,f237])).

fof(f237,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k4_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f233,f122])).

fof(f122,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(k4_tarski(sK3(k4_relat_1(X2),X3),sK4(k4_relat_1(X2),X3)),X3)
      | k4_relat_1(k4_relat_1(X2)) = X3
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(k4_relat_1(X2))
      | ~ r2_hidden(k4_tarski(sK3(k4_relat_1(X2),X3),sK4(k4_relat_1(X2),X3)),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(duplicate_literal_removal,[],[f121])).

fof(f121,plain,(
    ! [X2,X3] :
      ( k4_relat_1(k4_relat_1(X2)) = X3
      | ~ r2_hidden(k4_tarski(sK3(k4_relat_1(X2),X3),sK4(k4_relat_1(X2),X3)),X3)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(k4_relat_1(X2))
      | ~ r2_hidden(k4_tarski(sK3(k4_relat_1(X2),X3),sK4(k4_relat_1(X2),X3)),X2)
      | ~ v1_relat_1(k4_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f41,f55])).

fof(f55,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(k4_tarski(X4,X5),k4_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X4),X0)
      | ~ v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r2_hidden(k4_tarski(X5,X4),X0)
      | k4_relat_1(X0) != X1
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k4_relat_1(X0) = X1
              | ( ( ~ r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0)
                  | ~ r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) )
                & ( r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0)
                  | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X5,X4),X0) )
                  & ( r2_hidden(k4_tarski(X5,X4),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
              | k4_relat_1(X0) != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f21,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( r2_hidden(k4_tarski(X3,X2),X0)
            | r2_hidden(k4_tarski(X2,X3),X1) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0)
          | ~ r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) )
        & ( r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0)
          | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k4_relat_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) )
                  & ( r2_hidden(k4_tarski(X3,X2),X0)
                    | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X5,X4),X0) )
                  & ( r2_hidden(k4_tarski(X5,X4),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
              | k4_relat_1(X0) != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k4_relat_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) )
                  & ( r2_hidden(k4_tarski(X3,X2),X0)
                    | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
            & ( ! [X2,X3] :
                  ( ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r2_hidden(k4_tarski(X3,X2),X0) )
                  & ( r2_hidden(k4_tarski(X3,X2),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
              | k4_relat_1(X0) != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k4_relat_1(X0) = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r2_hidden(k4_tarski(X3,X2),X0) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( k4_relat_1(X0) = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r2_hidden(k4_tarski(X3,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_relat_1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0)
      | k4_relat_1(X0) = X1
      | ~ r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f233,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(sK3(k4_relat_1(X0),X0),sK4(k4_relat_1(X0),X0)),X0)
      | k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k4_relat_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f232])).

fof(f232,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(sK3(k4_relat_1(X0),X0),sK4(k4_relat_1(X0),X0)),X0)
      | k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(factoring,[],[f118])).

fof(f118,plain,(
    ! [X4,X5] :
      ( r2_hidden(k4_tarski(sK3(k4_relat_1(X4),X5),sK4(k4_relat_1(X4),X5)),X5)
      | k4_relat_1(k4_relat_1(X4)) = X5
      | ~ v1_relat_1(X5)
      | ~ v1_relat_1(k4_relat_1(X4))
      | r2_hidden(k4_tarski(sK3(k4_relat_1(X4),X5),sK4(k4_relat_1(X4),X5)),X4)
      | ~ v1_relat_1(X4) ) ),
    inference(duplicate_literal_removal,[],[f117])).

fof(f117,plain,(
    ! [X4,X5] :
      ( k4_relat_1(k4_relat_1(X4)) = X5
      | r2_hidden(k4_tarski(sK3(k4_relat_1(X4),X5),sK4(k4_relat_1(X4),X5)),X5)
      | ~ v1_relat_1(X5)
      | ~ v1_relat_1(k4_relat_1(X4))
      | r2_hidden(k4_tarski(sK3(k4_relat_1(X4),X5),sK4(k4_relat_1(X4),X5)),X4)
      | ~ v1_relat_1(k4_relat_1(X4))
      | ~ v1_relat_1(X4) ) ),
    inference(resolution,[],[f40,f56])).

fof(f56,plain,(
    ! [X4,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X4,X5),k4_relat_1(X0))
      | r2_hidden(k4_tarski(X5,X4),X0)
      | ~ v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X4),X0)
      | ~ r2_hidden(k4_tarski(X4,X5),X1)
      | k4_relat_1(X0) != X1
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0)
      | k4_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f426,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f422,f170])).

fof(f170,plain,(
    ! [X8,X9] :
      ( ~ v1_relat_1(k4_relat_1(X8))
      | ~ v1_relat_1(X8)
      | ~ r2_hidden(sK5(X8,X9),k1_relat_1(k4_relat_1(X8)))
      | k2_relat_1(X8) = X9
      | ~ r2_hidden(sK5(X8,X9),X9) ) ),
    inference(resolution,[],[f103,f45])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0)
      | k2_relat_1(X0) = X1
      | ~ r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0)
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0)
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK7(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f25,f28,f27,f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0)
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK5(X0,X1)),X0)
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK5(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK7(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f103,plain,(
    ! [X6,X5] :
      ( r2_hidden(k4_tarski(sK10(k4_relat_1(X5),X6),X6),X5)
      | ~ v1_relat_1(k4_relat_1(X5))
      | ~ v1_relat_1(X5)
      | ~ r2_hidden(X6,k1_relat_1(k4_relat_1(X5))) ) ),
    inference(resolution,[],[f56,f60])).

fof(f60,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK10(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK10(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK8(X0,X1),X3),X0)
            | ~ r2_hidden(sK8(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X0)
            | r2_hidden(sK8(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK10(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f31,f34,f33,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK8(X0,X1),X3),X0)
          | ~ r2_hidden(sK8(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK8(X0,X1),X4),X0)
          | r2_hidden(sK8(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK8(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK10(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f422,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0,k1_relat_1(k4_relat_1(X0))),k1_relat_1(k4_relat_1(X0)))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k4_relat_1(X0))
      | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ),
    inference(factoring,[],[f130])).

fof(f130,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK5(X2,X3),k1_relat_1(k4_relat_1(X2)))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(k4_relat_1(X2))
      | k2_relat_1(X2) = X3
      | r2_hidden(sK5(X2,X3),X3) ) ),
    inference(resolution,[],[f95,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0)
      | k2_relat_1(X0) = X1
      | r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(k4_relat_1(X2))
      | ~ v1_relat_1(X2)
      | r2_hidden(X1,k1_relat_1(k4_relat_1(X2))) ) ),
    inference(resolution,[],[f55,f59])).

fof(f59,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X5,X6),X0)
      | r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f472,plain,
    ( k2_relat_1(k4_relat_1(sK2)) != k1_relat_1(sK2)
    | spl11_7 ),
    inference(subsumption_resolution,[],[f471,f36])).

fof(f471,plain,
    ( k2_relat_1(k4_relat_1(sK2)) != k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl11_7 ),
    inference(superposition,[],[f465,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f465,plain,
    ( k1_relset_1(sK0,sK1,sK2) != k2_relat_1(k4_relat_1(sK2))
    | spl11_7 ),
    inference(avatar_component_clause,[],[f464])).

fof(f464,plain,
    ( spl11_7
  <=> k1_relset_1(sK0,sK1,sK2) = k2_relat_1(k4_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).

fof(f469,plain,(
    spl11_6 ),
    inference(avatar_contradiction_clause,[],[f468])).

fof(f468,plain,
    ( $false
    | spl11_6 ),
    inference(subsumption_resolution,[],[f467,f36])).

fof(f467,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl11_6 ),
    inference(resolution,[],[f462,f88])).

fof(f462,plain,
    ( ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl11_6 ),
    inference(avatar_component_clause,[],[f461])).

fof(f461,plain,
    ( spl11_6
  <=> m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).

fof(f466,plain,
    ( ~ spl11_6
    | ~ spl11_7
    | spl11_2 ),
    inference(avatar_split_clause,[],[f459,f65,f464,f461])).

fof(f65,plain,
    ( spl11_2
  <=> k1_relset_1(sK0,sK1,sK2) = k2_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f459,plain,
    ( k1_relset_1(sK0,sK1,sK2) != k2_relat_1(k4_relat_1(sK2))
    | ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl11_2 ),
    inference(superposition,[],[f454,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f454,plain,
    ( k1_relset_1(sK0,sK1,sK2) != k2_relset_1(sK1,sK0,k4_relat_1(sK2))
    | spl11_2 ),
    inference(subsumption_resolution,[],[f452,f36])).

fof(f452,plain,
    ( k1_relset_1(sK0,sK1,sK2) != k2_relset_1(sK1,sK0,k4_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl11_2 ),
    inference(superposition,[],[f66,f53])).

fof(f66,plain,
    ( k1_relset_1(sK0,sK1,sK2) != k2_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2))
    | spl11_2 ),
    inference(avatar_component_clause,[],[f65])).

fof(f451,plain,(
    spl11_4 ),
    inference(avatar_contradiction_clause,[],[f450])).

fof(f450,plain,
    ( $false
    | spl11_4 ),
    inference(subsumption_resolution,[],[f449,f68])).

fof(f449,plain,
    ( ~ v1_relat_1(sK2)
    | spl11_4 ),
    inference(subsumption_resolution,[],[f447,f137])).

fof(f447,plain,
    ( ~ v1_relat_1(k4_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | spl11_4 ),
    inference(trivial_inequality_removal,[],[f428])).

fof(f428,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | ~ v1_relat_1(k4_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | spl11_4 ),
    inference(superposition,[],[f100,f426])).

fof(f100,plain,
    ( k1_relat_1(k4_relat_1(sK2)) != k2_relat_1(sK2)
    | spl11_4 ),
    inference(subsumption_resolution,[],[f99,f36])).

fof(f99,plain,
    ( k1_relat_1(k4_relat_1(sK2)) != k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl11_4 ),
    inference(superposition,[],[f93,f52])).

fof(f93,plain,
    ( k2_relset_1(sK0,sK1,sK2) != k1_relat_1(k4_relat_1(sK2))
    | spl11_4 ),
    inference(subsumption_resolution,[],[f92,f36])).

fof(f92,plain,
    ( k2_relset_1(sK0,sK1,sK2) != k1_relat_1(k4_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl11_4 ),
    inference(superposition,[],[f79,f53])).

fof(f79,plain,
    ( k2_relset_1(sK0,sK1,sK2) != k1_relat_1(k3_relset_1(sK0,sK1,sK2))
    | spl11_4 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl11_4
  <=> k2_relset_1(sK0,sK1,sK2) = k1_relat_1(k3_relset_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f90,plain,(
    spl11_3 ),
    inference(avatar_contradiction_clause,[],[f89])).

fof(f89,plain,
    ( $false
    | spl11_3 ),
    inference(subsumption_resolution,[],[f85,f36])).

fof(f85,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl11_3 ),
    inference(resolution,[],[f54,f76])).

fof(f76,plain,
    ( ~ m1_subset_1(k3_relset_1(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl11_3 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl11_3
  <=> m1_subset_1(k3_relset_1(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f80,plain,
    ( ~ spl11_3
    | ~ spl11_4
    | spl11_1 ),
    inference(avatar_split_clause,[],[f73,f62,f78,f75])).

fof(f62,plain,
    ( spl11_1
  <=> k2_relset_1(sK0,sK1,sK2) = k1_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f73,plain,
    ( k2_relset_1(sK0,sK1,sK2) != k1_relat_1(k3_relset_1(sK0,sK1,sK2))
    | ~ m1_subset_1(k3_relset_1(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl11_1 ),
    inference(superposition,[],[f63,f51])).

fof(f63,plain,
    ( k2_relset_1(sK0,sK1,sK2) != k1_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2))
    | spl11_1 ),
    inference(avatar_component_clause,[],[f62])).

fof(f67,plain,
    ( ~ spl11_1
    | ~ spl11_2 ),
    inference(avatar_split_clause,[],[f37,f65,f62])).

fof(f37,plain,
    ( k1_relset_1(sK0,sK1,sK2) != k2_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2))
    | k2_relset_1(sK0,sK1,sK2) != k1_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f19])).

%------------------------------------------------------------------------------
