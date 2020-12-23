%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1042+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:04 EST 2020

% Result     : Theorem 1.72s
% Output     : Refutation 1.72s
% Verified   : 
% Statistics : Number of formulae       :   42 ( 380 expanded)
%              Number of leaves         :    8 ( 134 expanded)
%              Depth                    :   12
%              Number of atoms          :  279 (3263 expanded)
%              Number of equality atoms :   39 ( 345 expanded)
%              Maximal formula depth    :   17 (   8 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2352,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2351,f2267])).

fof(f2267,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(forward_demodulation,[],[f2242,f2243])).

fof(f2243,plain,(
    sK3 = sK8(sK0,sK1,sK2,sK3) ),
    inference(unit_resulting_resolution,[],[f1868,f1869,f1870,f2122])).

fof(f2122,plain,(
    ! [X2,X0,X7,X1] :
      ( sK8(X0,X1,X2,X7) = X7
      | ~ r2_hidden(X7,k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f1895])).

fof(f1895,plain,(
    ! [X2,X0,X7,X3,X1] :
      ( sK8(X0,X1,X2,X7) = X7
      | ~ r2_hidden(X7,X3)
      | k5_partfun1(X0,X1,X2) != X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f1787])).

fof(f1787,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k5_partfun1(X0,X1,X2) = X3
            | ( ( ! [X5] :
                    ( ~ r1_partfun1(X2,X5)
                    | ~ v1_partfun1(X5,X0)
                    | sK6(X0,X1,X2,X3) != X5
                    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                    | ~ v1_funct_1(X5) )
                | ~ r2_hidden(sK6(X0,X1,X2,X3),X3) )
              & ( ( r1_partfun1(X2,sK7(X0,X1,X2,X3))
                  & v1_partfun1(sK7(X0,X1,X2,X3),X0)
                  & sK6(X0,X1,X2,X3) = sK7(X0,X1,X2,X3)
                  & m1_subset_1(sK7(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(sK7(X0,X1,X2,X3)) )
                | r2_hidden(sK6(X0,X1,X2,X3),X3) ) ) )
          & ( ! [X7] :
                ( ( r2_hidden(X7,X3)
                  | ! [X8] :
                      ( ~ r1_partfun1(X2,X8)
                      | ~ v1_partfun1(X8,X0)
                      | X7 != X8
                      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      | ~ v1_funct_1(X8) ) )
                & ( ( r1_partfun1(X2,sK8(X0,X1,X2,X7))
                    & v1_partfun1(sK8(X0,X1,X2,X7),X0)
                    & sK8(X0,X1,X2,X7) = X7
                    & m1_subset_1(sK8(X0,X1,X2,X7),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                    & v1_funct_1(sK8(X0,X1,X2,X7)) )
                  | ~ r2_hidden(X7,X3) ) )
            | k5_partfun1(X0,X1,X2) != X3 ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f1783,f1786,f1785,f1784])).

fof(f1784,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ! [X5] :
                ( ~ r1_partfun1(X2,X5)
                | ~ v1_partfun1(X5,X0)
                | X4 != X5
                | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                | ~ v1_funct_1(X5) )
            | ~ r2_hidden(X4,X3) )
          & ( ? [X6] :
                ( r1_partfun1(X2,X6)
                & v1_partfun1(X6,X0)
                & X4 = X6
                & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_1(X6) )
            | r2_hidden(X4,X3) ) )
     => ( ( ! [X5] :
              ( ~ r1_partfun1(X2,X5)
              | ~ v1_partfun1(X5,X0)
              | sK6(X0,X1,X2,X3) != X5
              | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_1(X5) )
          | ~ r2_hidden(sK6(X0,X1,X2,X3),X3) )
        & ( ? [X6] :
              ( r1_partfun1(X2,X6)
              & v1_partfun1(X6,X0)
              & sK6(X0,X1,X2,X3) = X6
              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_1(X6) )
          | r2_hidden(sK6(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1785,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X6] :
          ( r1_partfun1(X2,X6)
          & v1_partfun1(X6,X0)
          & sK6(X0,X1,X2,X3) = X6
          & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X6) )
     => ( r1_partfun1(X2,sK7(X0,X1,X2,X3))
        & v1_partfun1(sK7(X0,X1,X2,X3),X0)
        & sK6(X0,X1,X2,X3) = sK7(X0,X1,X2,X3)
        & m1_subset_1(sK7(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(sK7(X0,X1,X2,X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f1786,plain,(
    ! [X7,X2,X1,X0] :
      ( ? [X9] :
          ( r1_partfun1(X2,X9)
          & v1_partfun1(X9,X0)
          & X7 = X9
          & m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X9) )
     => ( r1_partfun1(X2,sK8(X0,X1,X2,X7))
        & v1_partfun1(sK8(X0,X1,X2,X7),X0)
        & sK8(X0,X1,X2,X7) = X7
        & m1_subset_1(sK8(X0,X1,X2,X7),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(sK8(X0,X1,X2,X7)) ) ) ),
    introduced(choice_axiom,[])).

fof(f1783,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k5_partfun1(X0,X1,X2) = X3
            | ? [X4] :
                ( ( ! [X5] :
                      ( ~ r1_partfun1(X2,X5)
                      | ~ v1_partfun1(X5,X0)
                      | X4 != X5
                      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      | ~ v1_funct_1(X5) )
                  | ~ r2_hidden(X4,X3) )
                & ( ? [X6] :
                      ( r1_partfun1(X2,X6)
                      & v1_partfun1(X6,X0)
                      & X4 = X6
                      & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      & v1_funct_1(X6) )
                  | r2_hidden(X4,X3) ) ) )
          & ( ! [X7] :
                ( ( r2_hidden(X7,X3)
                  | ! [X8] :
                      ( ~ r1_partfun1(X2,X8)
                      | ~ v1_partfun1(X8,X0)
                      | X7 != X8
                      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      | ~ v1_funct_1(X8) ) )
                & ( ? [X9] :
                      ( r1_partfun1(X2,X9)
                      & v1_partfun1(X9,X0)
                      & X7 = X9
                      & m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      & v1_funct_1(X9) )
                  | ~ r2_hidden(X7,X3) ) )
            | k5_partfun1(X0,X1,X2) != X3 ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(rectify,[],[f1782])).

fof(f1782,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k5_partfun1(X0,X1,X2) = X3
            | ? [X4] :
                ( ( ! [X5] :
                      ( ~ r1_partfun1(X2,X5)
                      | ~ v1_partfun1(X5,X0)
                      | X4 != X5
                      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      | ~ v1_funct_1(X5) )
                  | ~ r2_hidden(X4,X3) )
                & ( ? [X5] :
                      ( r1_partfun1(X2,X5)
                      & v1_partfun1(X5,X0)
                      & X4 = X5
                      & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      & v1_funct_1(X5) )
                  | r2_hidden(X4,X3) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X3)
                  | ! [X5] :
                      ( ~ r1_partfun1(X2,X5)
                      | ~ v1_partfun1(X5,X0)
                      | X4 != X5
                      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      | ~ v1_funct_1(X5) ) )
                & ( ? [X5] :
                      ( r1_partfun1(X2,X5)
                      & v1_partfun1(X5,X0)
                      & X4 = X5
                      & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      & v1_funct_1(X5) )
                  | ~ r2_hidden(X4,X3) ) )
            | k5_partfun1(X0,X1,X2) != X3 ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f1630])).

fof(f1630,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f1629])).

fof(f1629,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1481])).

fof(f1481,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_partfun1)).

fof(f1870,plain,(
    r2_hidden(sK3,k5_partfun1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f1776])).

fof(f1776,plain,
    ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_2(sK3,sK0,sK1)
      | ~ v1_funct_1(sK3) )
    & r2_hidden(sK3,k5_partfun1(sK0,sK1,sK2))
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f1615,f1775,f1774])).

fof(f1774,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X3,X0,X1)
              | ~ v1_funct_1(X3) )
            & r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
            | ~ v1_funct_2(X3,sK0,sK1)
            | ~ v1_funct_1(X3) )
          & r2_hidden(X3,k5_partfun1(sK0,sK1,sK2)) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f1775,plain,
    ( ? [X3] :
        ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
          | ~ v1_funct_2(X3,sK0,sK1)
          | ~ v1_funct_1(X3) )
        & r2_hidden(X3,k5_partfun1(sK0,sK1,sK2)) )
   => ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_2(sK3,sK0,sK1)
        | ~ v1_funct_1(sK3) )
      & r2_hidden(sK3,k5_partfun1(sK0,sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f1615,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            | ~ v1_funct_2(X3,X0,X1)
            | ~ v1_funct_1(X3) )
          & r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f1614])).

fof(f1614,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            | ~ v1_funct_2(X3,X0,X1)
            | ~ v1_funct_1(X3) )
          & r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1547])).

fof(f1547,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ! [X3] :
            ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
           => ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) ) ) ) ),
    inference(negated_conjecture,[],[f1546])).

fof(f1546,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
         => ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_2)).

fof(f1869,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f1776])).

fof(f1868,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f1776])).

fof(f2242,plain,(
    m1_subset_1(sK8(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f1868,f1869,f1870,f2123])).

fof(f2123,plain,(
    ! [X2,X0,X7,X1] :
      ( m1_subset_1(sK8(X0,X1,X2,X7),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X7,k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f1894])).

fof(f1894,plain,(
    ! [X2,X0,X7,X3,X1] :
      ( m1_subset_1(sK8(X0,X1,X2,X7),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X7,X3)
      | k5_partfun1(X0,X1,X2) != X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f1787])).

fof(f2351,plain,(
    ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f2268,f2265,f2281,f2067])).

fof(f2067,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_partfun1(X2,X0)
      | v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f1739])).

fof(f1739,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f1738])).

fof(f1738,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1530])).

fof(f1530,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( v1_partfun1(X2,X0)
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t131_funct_2)).

fof(f2281,plain,(
    ~ v1_funct_2(sK3,sK0,sK1) ),
    inference(global_subsumption,[],[f1871,f2267,f2268])).

fof(f1871,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f1776])).

fof(f2265,plain,(
    v1_partfun1(sK3,sK0) ),
    inference(backward_demodulation,[],[f2244,f2243])).

fof(f2244,plain,(
    v1_partfun1(sK8(sK0,sK1,sK2,sK3),sK0) ),
    inference(unit_resulting_resolution,[],[f1868,f1869,f1870,f2121])).

fof(f2121,plain,(
    ! [X2,X0,X7,X1] :
      ( v1_partfun1(sK8(X0,X1,X2,X7),X0)
      | ~ r2_hidden(X7,k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f1896])).

fof(f1896,plain,(
    ! [X2,X0,X7,X3,X1] :
      ( v1_partfun1(sK8(X0,X1,X2,X7),X0)
      | ~ r2_hidden(X7,X3)
      | k5_partfun1(X0,X1,X2) != X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f1787])).

fof(f2268,plain,(
    v1_funct_1(sK3) ),
    inference(forward_demodulation,[],[f2241,f2243])).

fof(f2241,plain,(
    v1_funct_1(sK8(sK0,sK1,sK2,sK3)) ),
    inference(unit_resulting_resolution,[],[f1868,f1869,f1870,f2124])).

fof(f2124,plain,(
    ! [X2,X0,X7,X1] :
      ( v1_funct_1(sK8(X0,X1,X2,X7))
      | ~ r2_hidden(X7,k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f1893])).

fof(f1893,plain,(
    ! [X2,X0,X7,X3,X1] :
      ( v1_funct_1(sK8(X0,X1,X2,X7))
      | ~ r2_hidden(X7,X3)
      | k5_partfun1(X0,X1,X2) != X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f1787])).
%------------------------------------------------------------------------------
