%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_1__t162_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:18 EDT 2019

% Result     : Theorem 1.78s
% Output     : Refutation 1.78s
% Verified   : 
% Statistics : Number of formulae       :  100 (1313 expanded)
%              Number of leaves         :   12 ( 374 expanded)
%              Depth                    :   40
%              Number of atoms          :  416 (6575 expanded)
%              Number of equality atoms :  122 (2126 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4247,plain,(
    $false ),
    inference(subsumption_resolution,[],[f4246,f59])).

fof(f59,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t162_funct_1.p',fc3_funct_1)).

fof(f4246,plain,(
    ~ v1_relat_1(k6_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f4245,f60])).

fof(f60,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f4245,plain,
    ( ~ v1_funct_1(k6_relat_1(sK0))
    | ~ v1_relat_1(k6_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f4243,f3151])).

fof(f3151,plain,(
    r2_hidden(sK2(k6_relat_1(sK0),sK1,sK1),sK0) ),
    inference(resolution,[],[f3146,f112])).

fof(f112,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | r2_hidden(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f111,f93])).

fof(f93,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK0)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f55,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t162_funct_1.p',t5_subset)).

fof(f55,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( k9_relat_1(k6_relat_1(sK0),sK1) != sK1
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f39])).

fof(f39,plain,
    ( ? [X0,X1] :
        ( k9_relat_1(k6_relat_1(X0),X1) != X1
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( k9_relat_1(k6_relat_1(sK0),sK1) != sK1
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),X1) != X1
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t162_funct_1.p',t162_funct_1)).

fof(f111,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | r2_hidden(X0,sK0)
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f94,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t162_funct_1.p',t2_subset)).

fof(f94,plain,(
    ! [X1] :
      ( m1_subset_1(X1,sK0)
      | ~ r2_hidden(X1,sK1) ) ),
    inference(resolution,[],[f55,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t162_funct_1.p',t4_subset)).

fof(f3146,plain,(
    r2_hidden(sK2(k6_relat_1(sK0),sK1,sK1),sK1) ),
    inference(duplicate_literal_removal,[],[f3127])).

fof(f3127,plain,
    ( r2_hidden(sK2(k6_relat_1(sK0),sK1,sK1),sK1)
    | r2_hidden(sK2(k6_relat_1(sK0),sK1,sK1),sK1)
    | r2_hidden(sK2(k6_relat_1(sK0),sK1,sK1),sK1) ),
    inference(superposition,[],[f124,f3083])).

fof(f3083,plain,
    ( sK2(k6_relat_1(sK0),sK1,sK1) = sK3(k6_relat_1(sK0),sK1,sK1)
    | r2_hidden(sK2(k6_relat_1(sK0),sK1,sK1),sK1) ),
    inference(backward_demodulation,[],[f3082,f132])).

fof(f132,plain,
    ( r2_hidden(sK2(k6_relat_1(sK0),sK1,sK1),sK1)
    | k1_funct_1(k6_relat_1(sK0),sK3(k6_relat_1(sK0),sK1,sK1)) = sK2(k6_relat_1(sK0),sK1,sK1) ),
    inference(equality_resolution,[],[f107])).

fof(f107,plain,(
    ! [X2] :
      ( sK1 != X2
      | k1_funct_1(k6_relat_1(sK0),sK3(k6_relat_1(sK0),sK1,X2)) = sK2(k6_relat_1(sK0),sK1,X2)
      | r2_hidden(sK2(k6_relat_1(sK0),sK1,X2),X2) ) ),
    inference(subsumption_resolution,[],[f106,f59])).

fof(f106,plain,(
    ! [X2] :
      ( sK1 != X2
      | k1_funct_1(k6_relat_1(sK0),sK3(k6_relat_1(sK0),sK1,X2)) = sK2(k6_relat_1(sK0),sK1,X2)
      | r2_hidden(sK2(k6_relat_1(sK0),sK1,X2),X2)
      | ~ v1_relat_1(k6_relat_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f100,f60])).

fof(f100,plain,(
    ! [X2] :
      ( sK1 != X2
      | k1_funct_1(k6_relat_1(sK0),sK3(k6_relat_1(sK0),sK1,X2)) = sK2(k6_relat_1(sK0),sK1,X2)
      | r2_hidden(sK2(k6_relat_1(sK0),sK1,X2),X2)
      | ~ v1_funct_1(k6_relat_1(sK0))
      | ~ v1_relat_1(k6_relat_1(sK0)) ) ),
    inference(superposition,[],[f56,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X0,X1) = X2
      | k1_funct_1(X0,sK3(X0,X1,X2)) = sK2(X0,X1,X2)
      | r2_hidden(sK2(X0,X1,X2),X2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( k1_funct_1(X0,X4) != sK2(X0,X1,X2)
                    | ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(X4,k1_relat_1(X0)) )
                | ~ r2_hidden(sK2(X0,X1,X2),X2) )
              & ( ( k1_funct_1(X0,sK3(X0,X1,X2)) = sK2(X0,X1,X2)
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f42,f45,f44,f43])).

fof(f43,plain,(
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

fof(f44,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( k1_funct_1(X0,X5) = X3
          & r2_hidden(X5,X1)
          & r2_hidden(X5,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X1,X2)) = X3
        & r2_hidden(sK3(X0,X1,X2),X1)
        & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( k1_funct_1(X0,X8) = X6
          & r2_hidden(X8,X1)
          & r2_hidden(X8,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X1,X6)) = X6
        & r2_hidden(sK4(X0,X1,X6),X1)
        & r2_hidden(sK4(X0,X1,X6),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
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
    inference(rectify,[],[f41])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox/benchmark/funct_1__t162_funct_1.p',d12_funct_1)).

fof(f56,plain,(
    k9_relat_1(k6_relat_1(sK0),sK1) != sK1 ),
    inference(cnf_transformation,[],[f40])).

fof(f3082,plain,(
    k1_funct_1(k6_relat_1(sK0),sK3(k6_relat_1(sK0),sK1,sK1)) = sK3(k6_relat_1(sK0),sK1,sK1) ),
    inference(subsumption_resolution,[],[f3081,f59])).

fof(f3081,plain,
    ( k1_funct_1(k6_relat_1(sK0),sK3(k6_relat_1(sK0),sK1,sK1)) = sK3(k6_relat_1(sK0),sK1,sK1)
    | ~ v1_relat_1(k6_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f3071,f60])).

fof(f3071,plain,
    ( k1_funct_1(k6_relat_1(sK0),sK3(k6_relat_1(sK0),sK1,sK1)) = sK3(k6_relat_1(sK0),sK1,sK1)
    | ~ v1_funct_1(k6_relat_1(sK0))
    | ~ v1_relat_1(k6_relat_1(sK0)) ),
    inference(resolution,[],[f2995,f91])).

fof(f91,plain,(
    ! [X0,X3] :
      ( k1_funct_1(k6_relat_1(X0),X3) = X3
      | ~ r2_hidden(X3,X0)
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(X1,X3) = X3
      | ~ r2_hidden(X3,X0)
      | k6_relat_1(X0) != X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ( k1_funct_1(X1,sK6(X0,X1)) != sK6(X0,X1)
            & r2_hidden(sK6(X0,X1),X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X3] :
                ( k1_funct_1(X1,X3) = X3
                | ~ r2_hidden(X3,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f51,f52])).

fof(f52,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X1,X2) != X2
          & r2_hidden(X2,X0) )
     => ( k1_funct_1(X1,sK6(X0,X1)) != sK6(X0,X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
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
    inference(rectify,[],[f50])).

fof(f50,plain,(
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
    inference(flattening,[],[f49])).

fof(f49,plain,(
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
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( r2_hidden(X2,X0)
             => k1_funct_1(X1,X2) = X2 )
          & k1_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t162_funct_1.p',t34_funct_1)).

fof(f2995,plain,(
    r2_hidden(sK3(k6_relat_1(sK0),sK1,sK1),sK0) ),
    inference(subsumption_resolution,[],[f2994,f59])).

fof(f2994,plain,
    ( r2_hidden(sK3(k6_relat_1(sK0),sK1,sK1),sK0)
    | ~ v1_relat_1(k6_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f2979,f60])).

fof(f2979,plain,
    ( r2_hidden(sK3(k6_relat_1(sK0),sK1,sK1),sK0)
    | ~ v1_funct_1(k6_relat_1(sK0))
    | ~ v1_relat_1(k6_relat_1(sK0)) ),
    inference(superposition,[],[f2951,f92])).

fof(f92,plain,(
    ! [X0] :
      ( k1_relat_1(k6_relat_1(X0)) = X0
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | k6_relat_1(X0) != X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f2951,plain,(
    r2_hidden(sK3(k6_relat_1(sK0),sK1,sK1),k1_relat_1(k6_relat_1(sK0))) ),
    inference(subsumption_resolution,[],[f2950,f197])).

fof(f197,plain,
    ( r2_hidden(sK2(k6_relat_1(sK0),sK1,sK1),sK0)
    | r2_hidden(sK3(k6_relat_1(sK0),sK1,sK1),k1_relat_1(k6_relat_1(sK0))) ),
    inference(resolution,[],[f125,f112])).

fof(f125,plain,
    ( r2_hidden(sK2(k6_relat_1(sK0),sK1,sK1),sK1)
    | r2_hidden(sK3(k6_relat_1(sK0),sK1,sK1),k1_relat_1(k6_relat_1(sK0))) ),
    inference(equality_resolution,[],[f103])).

fof(f103,plain,(
    ! [X0] :
      ( sK1 != X0
      | r2_hidden(sK3(k6_relat_1(sK0),sK1,X0),k1_relat_1(k6_relat_1(sK0)))
      | r2_hidden(sK2(k6_relat_1(sK0),sK1,X0),X0) ) ),
    inference(subsumption_resolution,[],[f102,f59])).

fof(f102,plain,(
    ! [X0] :
      ( sK1 != X0
      | r2_hidden(sK3(k6_relat_1(sK0),sK1,X0),k1_relat_1(k6_relat_1(sK0)))
      | r2_hidden(sK2(k6_relat_1(sK0),sK1,X0),X0)
      | ~ v1_relat_1(k6_relat_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f98,f60])).

fof(f98,plain,(
    ! [X0] :
      ( sK1 != X0
      | r2_hidden(sK3(k6_relat_1(sK0),sK1,X0),k1_relat_1(k6_relat_1(sK0)))
      | r2_hidden(sK2(k6_relat_1(sK0),sK1,X0),X0)
      | ~ v1_funct_1(k6_relat_1(sK0))
      | ~ v1_relat_1(k6_relat_1(sK0)) ) ),
    inference(superposition,[],[f56,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),k1_relat_1(X0))
      | r2_hidden(sK2(X0,X1,X2),X2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f2950,plain,
    ( ~ r2_hidden(sK2(k6_relat_1(sK0),sK1,sK1),sK0)
    | r2_hidden(sK3(k6_relat_1(sK0),sK1,sK1),k1_relat_1(k6_relat_1(sK0))) ),
    inference(subsumption_resolution,[],[f2949,f59])).

fof(f2949,plain,
    ( ~ r2_hidden(sK2(k6_relat_1(sK0),sK1,sK1),sK0)
    | r2_hidden(sK3(k6_relat_1(sK0),sK1,sK1),k1_relat_1(k6_relat_1(sK0)))
    | ~ v1_relat_1(k6_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f2948,f60])).

fof(f2948,plain,
    ( ~ r2_hidden(sK2(k6_relat_1(sK0),sK1,sK1),sK0)
    | r2_hidden(sK3(k6_relat_1(sK0),sK1,sK1),k1_relat_1(k6_relat_1(sK0)))
    | ~ v1_funct_1(k6_relat_1(sK0))
    | ~ v1_relat_1(k6_relat_1(sK0)) ),
    inference(superposition,[],[f1049,f92])).

fof(f1049,plain,
    ( ~ r2_hidden(sK2(k6_relat_1(sK0),sK1,sK1),k1_relat_1(k6_relat_1(sK0)))
    | r2_hidden(sK3(k6_relat_1(sK0),sK1,sK1),k1_relat_1(k6_relat_1(sK0))) ),
    inference(subsumption_resolution,[],[f1045,f698])).

fof(f698,plain,
    ( r2_hidden(sK3(k6_relat_1(sK0),sK1,sK1),k1_relat_1(k6_relat_1(sK0)))
    | k1_funct_1(k6_relat_1(sK0),sK2(k6_relat_1(sK0),sK1,sK1)) = sK2(k6_relat_1(sK0),sK1,sK1) ),
    inference(subsumption_resolution,[],[f697,f59])).

fof(f697,plain,
    ( r2_hidden(sK3(k6_relat_1(sK0),sK1,sK1),k1_relat_1(k6_relat_1(sK0)))
    | k1_funct_1(k6_relat_1(sK0),sK2(k6_relat_1(sK0),sK1,sK1)) = sK2(k6_relat_1(sK0),sK1,sK1)
    | ~ v1_relat_1(k6_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f693,f60])).

fof(f693,plain,
    ( r2_hidden(sK3(k6_relat_1(sK0),sK1,sK1),k1_relat_1(k6_relat_1(sK0)))
    | k1_funct_1(k6_relat_1(sK0),sK2(k6_relat_1(sK0),sK1,sK1)) = sK2(k6_relat_1(sK0),sK1,sK1)
    | ~ v1_funct_1(k6_relat_1(sK0))
    | ~ v1_relat_1(k6_relat_1(sK0)) ),
    inference(resolution,[],[f197,f91])).

fof(f1045,plain,
    ( k1_funct_1(k6_relat_1(sK0),sK2(k6_relat_1(sK0),sK1,sK1)) != sK2(k6_relat_1(sK0),sK1,sK1)
    | r2_hidden(sK3(k6_relat_1(sK0),sK1,sK1),k1_relat_1(k6_relat_1(sK0)))
    | ~ r2_hidden(sK2(k6_relat_1(sK0),sK1,sK1),k1_relat_1(k6_relat_1(sK0))) ),
    inference(duplicate_literal_removal,[],[f1037])).

fof(f1037,plain,
    ( k1_funct_1(k6_relat_1(sK0),sK2(k6_relat_1(sK0),sK1,sK1)) != sK2(k6_relat_1(sK0),sK1,sK1)
    | r2_hidden(sK3(k6_relat_1(sK0),sK1,sK1),k1_relat_1(k6_relat_1(sK0)))
    | ~ r2_hidden(sK2(k6_relat_1(sK0),sK1,sK1),k1_relat_1(k6_relat_1(sK0)))
    | r2_hidden(sK3(k6_relat_1(sK0),sK1,sK1),k1_relat_1(k6_relat_1(sK0))) ),
    inference(resolution,[],[f210,f125])).

fof(f210,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | k1_funct_1(k6_relat_1(sK0),X0) != sK2(k6_relat_1(sK0),sK1,sK1)
      | r2_hidden(sK3(k6_relat_1(sK0),sK1,sK1),k1_relat_1(k6_relat_1(sK0)))
      | ~ r2_hidden(X0,k1_relat_1(k6_relat_1(sK0))) ) ),
    inference(subsumption_resolution,[],[f209,f59])).

fof(f209,plain,(
    ! [X0] :
      ( r2_hidden(sK3(k6_relat_1(sK0),sK1,sK1),k1_relat_1(k6_relat_1(sK0)))
      | k1_funct_1(k6_relat_1(sK0),X0) != sK2(k6_relat_1(sK0),sK1,sK1)
      | ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,k1_relat_1(k6_relat_1(sK0)))
      | ~ v1_relat_1(k6_relat_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f208,f60])).

fof(f208,plain,(
    ! [X0] :
      ( r2_hidden(sK3(k6_relat_1(sK0),sK1,sK1),k1_relat_1(k6_relat_1(sK0)))
      | k1_funct_1(k6_relat_1(sK0),X0) != sK2(k6_relat_1(sK0),sK1,sK1)
      | ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,k1_relat_1(k6_relat_1(sK0)))
      | ~ v1_funct_1(k6_relat_1(sK0))
      | ~ v1_relat_1(k6_relat_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f195,f56])).

fof(f195,plain,(
    ! [X0] :
      ( r2_hidden(sK3(k6_relat_1(sK0),sK1,sK1),k1_relat_1(k6_relat_1(sK0)))
      | k9_relat_1(k6_relat_1(sK0),sK1) = sK1
      | k1_funct_1(k6_relat_1(sK0),X0) != sK2(k6_relat_1(sK0),sK1,sK1)
      | ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,k1_relat_1(k6_relat_1(sK0)))
      | ~ v1_funct_1(k6_relat_1(sK0))
      | ~ v1_relat_1(k6_relat_1(sK0)) ) ),
    inference(resolution,[],[f125,f69])).

fof(f69,plain,(
    ! [X4,X2,X0,X1] :
      ( k9_relat_1(X0,X1) = X2
      | k1_funct_1(X0,X4) != sK2(X0,X1,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(sK2(X0,X1,X2),X2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f124,plain,
    ( r2_hidden(sK3(k6_relat_1(sK0),sK1,sK1),sK1)
    | r2_hidden(sK2(k6_relat_1(sK0),sK1,sK1),sK1) ),
    inference(equality_resolution,[],[f105])).

fof(f105,plain,(
    ! [X1] :
      ( sK1 != X1
      | r2_hidden(sK3(k6_relat_1(sK0),sK1,X1),sK1)
      | r2_hidden(sK2(k6_relat_1(sK0),sK1,X1),X1) ) ),
    inference(subsumption_resolution,[],[f104,f59])).

fof(f104,plain,(
    ! [X1] :
      ( sK1 != X1
      | r2_hidden(sK3(k6_relat_1(sK0),sK1,X1),sK1)
      | r2_hidden(sK2(k6_relat_1(sK0),sK1,X1),X1)
      | ~ v1_relat_1(k6_relat_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f99,f60])).

fof(f99,plain,(
    ! [X1] :
      ( sK1 != X1
      | r2_hidden(sK3(k6_relat_1(sK0),sK1,X1),sK1)
      | r2_hidden(sK2(k6_relat_1(sK0),sK1,X1),X1)
      | ~ v1_funct_1(k6_relat_1(sK0))
      | ~ v1_relat_1(k6_relat_1(sK0)) ) ),
    inference(superposition,[],[f56,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f4243,plain,
    ( ~ r2_hidden(sK2(k6_relat_1(sK0),sK1,sK1),sK0)
    | ~ v1_funct_1(k6_relat_1(sK0))
    | ~ v1_relat_1(k6_relat_1(sK0)) ),
    inference(superposition,[],[f4197,f92])).

fof(f4197,plain,(
    ~ r2_hidden(sK2(k6_relat_1(sK0),sK1,sK1),k1_relat_1(k6_relat_1(sK0))) ),
    inference(subsumption_resolution,[],[f4186,f3211])).

fof(f3211,plain,(
    k1_funct_1(k6_relat_1(sK0),sK2(k6_relat_1(sK0),sK1,sK1)) = sK2(k6_relat_1(sK0),sK1,sK1) ),
    inference(subsumption_resolution,[],[f3210,f59])).

fof(f3210,plain,
    ( k1_funct_1(k6_relat_1(sK0),sK2(k6_relat_1(sK0),sK1,sK1)) = sK2(k6_relat_1(sK0),sK1,sK1)
    | ~ v1_relat_1(k6_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f3200,f60])).

fof(f3200,plain,
    ( k1_funct_1(k6_relat_1(sK0),sK2(k6_relat_1(sK0),sK1,sK1)) = sK2(k6_relat_1(sK0),sK1,sK1)
    | ~ v1_funct_1(k6_relat_1(sK0))
    | ~ v1_relat_1(k6_relat_1(sK0)) ),
    inference(resolution,[],[f3151,f91])).

fof(f4186,plain,
    ( k1_funct_1(k6_relat_1(sK0),sK2(k6_relat_1(sK0),sK1,sK1)) != sK2(k6_relat_1(sK0),sK1,sK1)
    | ~ r2_hidden(sK2(k6_relat_1(sK0),sK1,sK1),k1_relat_1(k6_relat_1(sK0))) ),
    inference(resolution,[],[f3183,f3146])).

fof(f3183,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | k1_funct_1(k6_relat_1(sK0),X0) != sK2(k6_relat_1(sK0),sK1,sK1)
      | ~ r2_hidden(X0,k1_relat_1(k6_relat_1(sK0))) ) ),
    inference(subsumption_resolution,[],[f3182,f59])).

fof(f3182,plain,(
    ! [X0] :
      ( k1_funct_1(k6_relat_1(sK0),X0) != sK2(k6_relat_1(sK0),sK1,sK1)
      | ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,k1_relat_1(k6_relat_1(sK0)))
      | ~ v1_relat_1(k6_relat_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f3181,f60])).

fof(f3181,plain,(
    ! [X0] :
      ( k1_funct_1(k6_relat_1(sK0),X0) != sK2(k6_relat_1(sK0),sK1,sK1)
      | ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,k1_relat_1(k6_relat_1(sK0)))
      | ~ v1_funct_1(k6_relat_1(sK0))
      | ~ v1_relat_1(k6_relat_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f3147,f56])).

fof(f3147,plain,(
    ! [X0] :
      ( k9_relat_1(k6_relat_1(sK0),sK1) = sK1
      | k1_funct_1(k6_relat_1(sK0),X0) != sK2(k6_relat_1(sK0),sK1,sK1)
      | ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,k1_relat_1(k6_relat_1(sK0)))
      | ~ v1_funct_1(k6_relat_1(sK0))
      | ~ v1_relat_1(k6_relat_1(sK0)) ) ),
    inference(resolution,[],[f3146,f69])).
%------------------------------------------------------------------------------
