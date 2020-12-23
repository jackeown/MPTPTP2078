%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0998+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:01 EST 2020

% Result     : Theorem 3.12s
% Output     : Refutation 3.12s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 652 expanded)
%              Number of leaves         :    9 ( 166 expanded)
%              Depth                    :   20
%              Number of atoms          :  342 (5100 expanded)
%              Number of equality atoms :   66 ( 687 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7349,plain,(
    $false ),
    inference(subsumption_resolution,[],[f7348,f5748])).

fof(f5748,plain,(
    v1_relat_1(sK39) ),
    inference(resolution,[],[f3557,f4211])).

fof(f4211,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1873])).

fof(f1873,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1210])).

fof(f1210,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f3557,plain,(
    m1_subset_1(sK39,k1_zfmisc_1(k2_zfmisc_1(sK36,sK37))) ),
    inference(cnf_transformation,[],[f2725])).

fof(f2725,plain,
    ( ( ~ r2_hidden(k1_funct_1(sK39,sK40),sK38)
      | ~ r2_hidden(sK40,sK36)
      | ~ r2_hidden(sK40,k8_relset_1(sK36,sK37,sK39,sK38)) )
    & ( ( r2_hidden(k1_funct_1(sK39,sK40),sK38)
        & r2_hidden(sK40,sK36) )
      | r2_hidden(sK40,k8_relset_1(sK36,sK37,sK39,sK38)) )
    & k1_xboole_0 != sK37
    & m1_subset_1(sK39,k1_zfmisc_1(k2_zfmisc_1(sK36,sK37)))
    & v1_funct_2(sK39,sK36,sK37)
    & v1_funct_1(sK39) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK36,sK37,sK38,sK39,sK40])],[f2722,f2724,f2723])).

fof(f2723,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ( ~ r2_hidden(k1_funct_1(X3,X4),X2)
              | ~ r2_hidden(X4,X0)
              | ~ r2_hidden(X4,k8_relset_1(X0,X1,X3,X2)) )
            & ( ( r2_hidden(k1_funct_1(X3,X4),X2)
                & r2_hidden(X4,X0) )
              | r2_hidden(X4,k8_relset_1(X0,X1,X3,X2)) ) )
        & k1_xboole_0 != X1
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ( ~ r2_hidden(k1_funct_1(sK39,X4),sK38)
            | ~ r2_hidden(X4,sK36)
            | ~ r2_hidden(X4,k8_relset_1(sK36,sK37,sK39,sK38)) )
          & ( ( r2_hidden(k1_funct_1(sK39,X4),sK38)
              & r2_hidden(X4,sK36) )
            | r2_hidden(X4,k8_relset_1(sK36,sK37,sK39,sK38)) ) )
      & k1_xboole_0 != sK37
      & m1_subset_1(sK39,k1_zfmisc_1(k2_zfmisc_1(sK36,sK37)))
      & v1_funct_2(sK39,sK36,sK37)
      & v1_funct_1(sK39) ) ),
    introduced(choice_axiom,[])).

fof(f2724,plain,
    ( ? [X4] :
        ( ( ~ r2_hidden(k1_funct_1(sK39,X4),sK38)
          | ~ r2_hidden(X4,sK36)
          | ~ r2_hidden(X4,k8_relset_1(sK36,sK37,sK39,sK38)) )
        & ( ( r2_hidden(k1_funct_1(sK39,X4),sK38)
            & r2_hidden(X4,sK36) )
          | r2_hidden(X4,k8_relset_1(sK36,sK37,sK39,sK38)) ) )
   => ( ( ~ r2_hidden(k1_funct_1(sK39,sK40),sK38)
        | ~ r2_hidden(sK40,sK36)
        | ~ r2_hidden(sK40,k8_relset_1(sK36,sK37,sK39,sK38)) )
      & ( ( r2_hidden(k1_funct_1(sK39,sK40),sK38)
          & r2_hidden(sK40,sK36) )
        | r2_hidden(sK40,k8_relset_1(sK36,sK37,sK39,sK38)) ) ) ),
    introduced(choice_axiom,[])).

fof(f2722,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( ~ r2_hidden(k1_funct_1(X3,X4),X2)
            | ~ r2_hidden(X4,X0)
            | ~ r2_hidden(X4,k8_relset_1(X0,X1,X3,X2)) )
          & ( ( r2_hidden(k1_funct_1(X3,X4),X2)
              & r2_hidden(X4,X0) )
            | r2_hidden(X4,k8_relset_1(X0,X1,X3,X2)) ) )
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f2721])).

fof(f2721,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( ~ r2_hidden(k1_funct_1(X3,X4),X2)
            | ~ r2_hidden(X4,X0)
            | ~ r2_hidden(X4,k8_relset_1(X0,X1,X3,X2)) )
          & ( ( r2_hidden(k1_funct_1(X3,X4),X2)
              & r2_hidden(X4,X0) )
            | r2_hidden(X4,k8_relset_1(X0,X1,X3,X2)) ) )
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(nnf_transformation,[],[f1560])).

fof(f1560,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( r2_hidden(X4,k8_relset_1(X0,X1,X3,X2))
        <~> ( r2_hidden(k1_funct_1(X3,X4),X2)
            & r2_hidden(X4,X0) ) )
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f1559])).

fof(f1559,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( r2_hidden(X4,k8_relset_1(X0,X1,X3,X2))
        <~> ( r2_hidden(k1_funct_1(X3,X4),X2)
            & r2_hidden(X4,X0) ) )
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f1524])).

fof(f1524,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => ! [X4] :
              ( r2_hidden(X4,k8_relset_1(X0,X1,X3,X2))
            <=> ( r2_hidden(k1_funct_1(X3,X4),X2)
                & r2_hidden(X4,X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f1523])).

fof(f1523,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => ! [X4] :
            ( r2_hidden(X4,k8_relset_1(X0,X1,X3,X2))
          <=> ( r2_hidden(k1_funct_1(X3,X4),X2)
              & r2_hidden(X4,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_funct_2)).

fof(f7348,plain,(
    ~ v1_relat_1(sK39) ),
    inference(subsumption_resolution,[],[f7347,f3555])).

fof(f3555,plain,(
    v1_funct_1(sK39) ),
    inference(cnf_transformation,[],[f2725])).

fof(f7347,plain,
    ( ~ v1_funct_1(sK39)
    | ~ v1_relat_1(sK39) ),
    inference(subsumption_resolution,[],[f7297,f7343])).

fof(f7343,plain,(
    ~ r2_hidden(k1_funct_1(sK39,sK40),sK38) ),
    inference(subsumption_resolution,[],[f7293,f6228])).

fof(f6228,plain,(
    r2_hidden(sK40,sK36) ),
    inference(duplicate_literal_removal,[],[f6227])).

fof(f6227,plain,
    ( r2_hidden(sK40,sK36)
    | r2_hidden(sK40,sK36) ),
    inference(forward_demodulation,[],[f6226,f5912])).

fof(f5912,plain,(
    sK36 = k1_relat_1(sK39) ),
    inference(forward_demodulation,[],[f5792,f5878])).

fof(f5878,plain,(
    sK36 = k1_relset_1(sK36,sK37,sK39) ),
    inference(subsumption_resolution,[],[f5877,f3558])).

fof(f3558,plain,(
    k1_xboole_0 != sK37 ),
    inference(cnf_transformation,[],[f2725])).

fof(f5877,plain,
    ( k1_xboole_0 = sK37
    | sK36 = k1_relset_1(sK36,sK37,sK39) ),
    inference(subsumption_resolution,[],[f5760,f3556])).

fof(f3556,plain,(
    v1_funct_2(sK39,sK36,sK37) ),
    inference(cnf_transformation,[],[f2725])).

fof(f5760,plain,
    ( ~ v1_funct_2(sK39,sK36,sK37)
    | k1_xboole_0 = sK37
    | sK36 = k1_relset_1(sK36,sK37,sK39) ),
    inference(resolution,[],[f3557,f4339])).

fof(f4339,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f3141])).

fof(f3141,plain,(
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
    inference(nnf_transformation,[],[f1945])).

fof(f1945,plain,(
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
    inference(flattening,[],[f1944])).

fof(f1944,plain,(
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
    inference(ennf_transformation,[],[f1472])).

fof(f1472,axiom,(
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

fof(f5792,plain,(
    k1_relat_1(sK39) = k1_relset_1(sK36,sK37,sK39) ),
    inference(resolution,[],[f3557,f5312])).

fof(f5312,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f2602])).

fof(f2602,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1227])).

fof(f1227,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f6226,plain,
    ( r2_hidden(sK40,sK36)
    | r2_hidden(sK40,k1_relat_1(sK39)) ),
    inference(subsumption_resolution,[],[f6225,f5748])).

fof(f6225,plain,
    ( r2_hidden(sK40,sK36)
    | r2_hidden(sK40,k1_relat_1(sK39))
    | ~ v1_relat_1(sK39) ),
    inference(subsumption_resolution,[],[f6175,f3555])).

fof(f6175,plain,
    ( r2_hidden(sK40,sK36)
    | r2_hidden(sK40,k1_relat_1(sK39))
    | ~ v1_funct_1(sK39)
    | ~ v1_relat_1(sK39) ),
    inference(resolution,[],[f5848,f5502])).

fof(f5502,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k10_relat_1(X0,X1))
      | r2_hidden(X4,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f3710])).

fof(f3710,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X4,X2)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f2816])).

fof(f2816,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ( ( ~ r2_hidden(k1_funct_1(X0,sK76(X0,X1,X2)),X1)
                | ~ r2_hidden(sK76(X0,X1,X2),k1_relat_1(X0))
                | ~ r2_hidden(sK76(X0,X1,X2),X2) )
              & ( ( r2_hidden(k1_funct_1(X0,sK76(X0,X1,X2)),X1)
                  & r2_hidden(sK76(X0,X1,X2),k1_relat_1(X0)) )
                | r2_hidden(sK76(X0,X1,X2),X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k1_funct_1(X0,X4),X1)
                  | ~ r2_hidden(X4,k1_relat_1(X0)) )
                & ( ( r2_hidden(k1_funct_1(X0,X4),X1)
                    & r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X4,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK76])],[f2814,f2815])).

fof(f2815,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
            | ~ r2_hidden(X3,k1_relat_1(X0))
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
              & r2_hidden(X3,k1_relat_1(X0)) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(k1_funct_1(X0,sK76(X0,X1,X2)),X1)
          | ~ r2_hidden(sK76(X0,X1,X2),k1_relat_1(X0))
          | ~ r2_hidden(sK76(X0,X1,X2),X2) )
        & ( ( r2_hidden(k1_funct_1(X0,sK76(X0,X1,X2)),X1)
            & r2_hidden(sK76(X0,X1,X2),k1_relat_1(X0)) )
          | r2_hidden(sK76(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f2814,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0))
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k1_funct_1(X0,X4),X1)
                  | ~ r2_hidden(X4,k1_relat_1(X0)) )
                & ( ( r2_hidden(k1_funct_1(X0,X4),X1)
                    & r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X4,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f2813])).

fof(f2813,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0))
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0)) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f2812])).

fof(f2812,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0))
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0)) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f1647])).

fof(f1647,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1646])).

fof(f1646,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f900])).

fof(f900,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_funct_1)).

fof(f5848,plain,
    ( r2_hidden(sK40,k10_relat_1(sK39,sK38))
    | r2_hidden(sK40,sK36) ),
    inference(backward_demodulation,[],[f3559,f5738])).

fof(f5738,plain,(
    ! [X11] : k8_relset_1(sK36,sK37,sK39,X11) = k10_relat_1(sK39,X11) ),
    inference(resolution,[],[f3557,f4057])).

fof(f4057,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f1793])).

fof(f1793,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1234])).

fof(f1234,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f3559,plain,
    ( r2_hidden(sK40,sK36)
    | r2_hidden(sK40,k8_relset_1(sK36,sK37,sK39,sK38)) ),
    inference(cnf_transformation,[],[f2725])).

fof(f7293,plain,
    ( ~ r2_hidden(k1_funct_1(sK39,sK40),sK38)
    | ~ r2_hidden(sK40,sK36) ),
    inference(resolution,[],[f6295,f5850])).

fof(f5850,plain,
    ( ~ r2_hidden(sK40,k10_relat_1(sK39,sK38))
    | ~ r2_hidden(k1_funct_1(sK39,sK40),sK38)
    | ~ r2_hidden(sK40,sK36) ),
    inference(backward_demodulation,[],[f3561,f5738])).

fof(f3561,plain,
    ( ~ r2_hidden(k1_funct_1(sK39,sK40),sK38)
    | ~ r2_hidden(sK40,sK36)
    | ~ r2_hidden(sK40,k8_relset_1(sK36,sK37,sK39,sK38)) ),
    inference(cnf_transformation,[],[f2725])).

fof(f6295,plain,(
    r2_hidden(sK40,k10_relat_1(sK39,sK38)) ),
    inference(subsumption_resolution,[],[f6294,f6228])).

fof(f6294,plain,
    ( ~ r2_hidden(sK40,sK36)
    | r2_hidden(sK40,k10_relat_1(sK39,sK38)) ),
    inference(forward_demodulation,[],[f6293,f5912])).

fof(f6293,plain,
    ( r2_hidden(sK40,k10_relat_1(sK39,sK38))
    | ~ r2_hidden(sK40,k1_relat_1(sK39)) ),
    inference(subsumption_resolution,[],[f6292,f5748])).

fof(f6292,plain,
    ( r2_hidden(sK40,k10_relat_1(sK39,sK38))
    | ~ r2_hidden(sK40,k1_relat_1(sK39))
    | ~ v1_relat_1(sK39) ),
    inference(subsumption_resolution,[],[f6291,f3555])).

fof(f6291,plain,
    ( r2_hidden(sK40,k10_relat_1(sK39,sK38))
    | ~ r2_hidden(sK40,k1_relat_1(sK39))
    | ~ v1_funct_1(sK39)
    | ~ v1_relat_1(sK39) ),
    inference(duplicate_literal_removal,[],[f6245])).

fof(f6245,plain,
    ( r2_hidden(sK40,k10_relat_1(sK39,sK38))
    | r2_hidden(sK40,k10_relat_1(sK39,sK38))
    | ~ r2_hidden(sK40,k1_relat_1(sK39))
    | ~ v1_funct_1(sK39)
    | ~ v1_relat_1(sK39) ),
    inference(resolution,[],[f5849,f5500])).

fof(f5500,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(k1_funct_1(X0,X4),X1)
      | r2_hidden(X4,k10_relat_1(X0,X1))
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f3712])).

fof(f3712,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(k1_funct_1(X0,X4),X1)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | k10_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f2816])).

fof(f5849,plain,
    ( r2_hidden(k1_funct_1(sK39,sK40),sK38)
    | r2_hidden(sK40,k10_relat_1(sK39,sK38)) ),
    inference(backward_demodulation,[],[f3560,f5738])).

fof(f3560,plain,
    ( r2_hidden(k1_funct_1(sK39,sK40),sK38)
    | r2_hidden(sK40,k8_relset_1(sK36,sK37,sK39,sK38)) ),
    inference(cnf_transformation,[],[f2725])).

fof(f7297,plain,
    ( r2_hidden(k1_funct_1(sK39,sK40),sK38)
    | ~ v1_funct_1(sK39)
    | ~ v1_relat_1(sK39) ),
    inference(resolution,[],[f6295,f5501])).

fof(f5501,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k10_relat_1(X0,X1))
      | r2_hidden(k1_funct_1(X0,X4),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f3711])).

fof(f3711,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X4),X1)
      | ~ r2_hidden(X4,X2)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f2816])).
%------------------------------------------------------------------------------
