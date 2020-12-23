%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0963+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:59 EST 2020

% Result     : Timeout 59.37s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :   83 ( 240 expanded)
%              Number of leaves         :   17 (  60 expanded)
%              Depth                    :   14
%              Number of atoms          :  387 (1576 expanded)
%              Number of equality atoms :   53 ( 196 expanded)
%              Maximal formula depth    :   10 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f73933,plain,(
    $false ),
    inference(subsumption_resolution,[],[f73864,f6709])).

fof(f6709,plain,(
    ~ r2_hidden(sK74(k2_relat_1(sK29),sK28),sK28) ),
    inference(resolution,[],[f4345,f2584])).

fof(f2584,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK74(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f2136])).

fof(f2136,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK74(X0,X1),X1)
          & r2_hidden(sK74(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK74])],[f2134,f2135])).

fof(f2135,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK74(X0,X1),X1)
        & r2_hidden(sK74(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f2134,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f2133])).

fof(f2133,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1609])).

fof(f1609,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f4345,plain,(
    ~ r1_tarski(k2_relat_1(sK29),sK28) ),
    inference(subsumption_resolution,[],[f4344,f3160])).

fof(f3160,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f2585])).

fof(f2585,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2138])).

fof(f2138,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f2137])).

fof(f2137,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f4344,plain,
    ( ~ r1_tarski(sK27,sK27)
    | ~ r1_tarski(k2_relat_1(sK29),sK28) ),
    inference(forward_demodulation,[],[f4343,f2371])).

fof(f2371,plain,(
    sK27 = k1_relat_1(sK29) ),
    inference(cnf_transformation,[],[f2014])).

fof(f2014,plain,
    ( ( ~ m1_subset_1(sK29,k1_zfmisc_1(k2_zfmisc_1(sK27,sK28)))
      | ~ v1_funct_2(sK29,sK27,sK28)
      | ~ v1_funct_1(sK29) )
    & ! [X3] :
        ( r2_hidden(k1_funct_1(sK29,X3),sK28)
        | ~ r2_hidden(X3,sK27) )
    & sK27 = k1_relat_1(sK29)
    & v1_funct_1(sK29)
    & v1_relat_1(sK29) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK27,sK28,sK29])],[f1492,f2013])).

fof(f2013,plain,
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
   => ( ( ~ m1_subset_1(sK29,k1_zfmisc_1(k2_zfmisc_1(sK27,sK28)))
        | ~ v1_funct_2(sK29,sK27,sK28)
        | ~ v1_funct_1(sK29) )
      & ! [X3] :
          ( r2_hidden(k1_funct_1(sK29,X3),sK28)
          | ~ r2_hidden(X3,sK27) )
      & sK27 = k1_relat_1(sK29)
      & v1_funct_1(sK29)
      & v1_relat_1(sK29) ) ),
    introduced(choice_axiom,[])).

fof(f1492,plain,(
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
    inference(flattening,[],[f1491])).

fof(f1491,plain,(
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
    inference(ennf_transformation,[],[f1480])).

fof(f1480,negated_conjecture,(
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
    inference(negated_conjecture,[],[f1479])).

fof(f1479,conjecture,(
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

fof(f4343,plain,
    ( ~ r1_tarski(k2_relat_1(sK29),sK28)
    | ~ r1_tarski(k1_relat_1(sK29),sK27) ),
    inference(subsumption_resolution,[],[f4342,f3599])).

fof(f3599,plain,(
    ! [X1] :
      ( v1_funct_2(sK29,sK27,X1)
      | ~ r1_tarski(k2_relat_1(sK29),X1) ) ),
    inference(forward_demodulation,[],[f3598,f2371])).

fof(f3598,plain,(
    ! [X1] :
      ( v1_funct_2(sK29,k1_relat_1(sK29),X1)
      | ~ r1_tarski(k2_relat_1(sK29),X1) ) ),
    inference(subsumption_resolution,[],[f3301,f2370])).

fof(f2370,plain,(
    v1_funct_1(sK29) ),
    inference(cnf_transformation,[],[f2014])).

fof(f3301,plain,(
    ! [X1] :
      ( v1_funct_2(sK29,k1_relat_1(sK29),X1)
      | ~ r1_tarski(k2_relat_1(sK29),X1)
      | ~ v1_funct_1(sK29) ) ),
    inference(resolution,[],[f2369,f2449])).

fof(f2449,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1538])).

fof(f1538,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1537])).

fof(f1537,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1478])).

fof(f1478,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

fof(f2369,plain,(
    v1_relat_1(sK29) ),
    inference(cnf_transformation,[],[f2014])).

fof(f4342,plain,
    ( ~ v1_funct_2(sK29,sK27,sK28)
    | ~ r1_tarski(k2_relat_1(sK29),sK28)
    | ~ r1_tarski(k1_relat_1(sK29),sK27) ),
    inference(subsumption_resolution,[],[f4341,f2369])).

fof(f4341,plain,
    ( ~ v1_funct_2(sK29,sK27,sK28)
    | ~ r1_tarski(k2_relat_1(sK29),sK28)
    | ~ r1_tarski(k1_relat_1(sK29),sK27)
    | ~ v1_relat_1(sK29) ),
    inference(subsumption_resolution,[],[f4322,f2370])).

fof(f4322,plain,
    ( ~ v1_funct_2(sK29,sK27,sK28)
    | ~ v1_funct_1(sK29)
    | ~ r1_tarski(k2_relat_1(sK29),sK28)
    | ~ r1_tarski(k1_relat_1(sK29),sK27)
    | ~ v1_relat_1(sK29) ),
    inference(resolution,[],[f2373,f2725])).

fof(f2725,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1683])).

fof(f1683,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f1682])).

fof(f1682,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f1240])).

fof(f1240,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(f2373,plain,
    ( ~ m1_subset_1(sK29,k1_zfmisc_1(k2_zfmisc_1(sK27,sK28)))
    | ~ v1_funct_2(sK29,sK27,sK28)
    | ~ v1_funct_1(sK29) ),
    inference(cnf_transformation,[],[f2014])).

fof(f73864,plain,(
    r2_hidden(sK74(k2_relat_1(sK29),sK28),sK28) ),
    inference(resolution,[],[f19854,f6708])).

fof(f6708,plain,(
    r2_hidden(sK74(k2_relat_1(sK29),sK28),k2_relat_1(sK29)) ),
    inference(resolution,[],[f4345,f2583])).

fof(f2583,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK74(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f2136])).

fof(f19854,plain,(
    ! [X11] :
      ( ~ r2_hidden(X11,k2_relat_1(sK29))
      | r2_hidden(X11,sK28) ) ),
    inference(resolution,[],[f4313,f3181])).

fof(f3181,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK118(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f2811])).

fof(f2811,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK118(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2245])).

fof(f2245,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK116(X0,X1)),X0)
            | ~ r2_hidden(sK116(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK117(X0,X1),sK116(X0,X1)),X0)
            | r2_hidden(sK116(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK118(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK116,sK117,sK118])],[f2241,f2244,f2243,f2242])).

fof(f2242,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK116(X0,X1)),X0)
          | ~ r2_hidden(sK116(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK116(X0,X1)),X0)
          | r2_hidden(sK116(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f2243,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK116(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK117(X0,X1),sK116(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f2244,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK118(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f2241,plain,(
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
    inference(rectify,[],[f2240])).

fof(f2240,plain,(
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
    inference(nnf_transformation,[],[f657])).

fof(f657,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f4313,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(k4_tarski(X6,X7),sK29)
      | r2_hidden(X7,sK28) ) ),
    inference(subsumption_resolution,[],[f4312,f3178])).

fof(f3178,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f2808])).

fof(f2808,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2239])).

fof(f2239,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK113(X0,X1),X3),X0)
            | ~ r2_hidden(sK113(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK113(X0,X1),sK114(X0,X1)),X0)
            | r2_hidden(sK113(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK115(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK113,sK114,sK115])],[f2235,f2238,f2237,f2236])).

fof(f2236,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK113(X0,X1),X3),X0)
          | ~ r2_hidden(sK113(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK113(X0,X1),X4),X0)
          | r2_hidden(sK113(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f2237,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK113(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK113(X0,X1),sK114(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f2238,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK115(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f2235,plain,(
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
    inference(rectify,[],[f2234])).

fof(f2234,plain,(
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
    inference(nnf_transformation,[],[f656])).

fof(f656,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f4312,plain,(
    ! [X6,X7] :
      ( r2_hidden(X7,sK28)
      | ~ r2_hidden(k4_tarski(X6,X7),sK29)
      | ~ r2_hidden(X6,k1_relat_1(sK29)) ) ),
    inference(subsumption_resolution,[],[f4311,f4158])).

fof(f4158,plain,(
    ! [X6,X5] :
      ( ~ r2_hidden(k4_tarski(X5,X6),sK29)
      | r2_hidden(X5,sK27) ) ),
    inference(subsumption_resolution,[],[f4157,f2369])).

fof(f4157,plain,(
    ! [X6,X5] :
      ( r2_hidden(X5,sK27)
      | ~ r2_hidden(k4_tarski(X5,X6),sK29)
      | ~ v1_relat_1(sK29) ) ),
    inference(subsumption_resolution,[],[f4033,f2370])).

fof(f4033,plain,(
    ! [X6,X5] :
      ( r2_hidden(X5,sK27)
      | ~ r2_hidden(k4_tarski(X5,X6),sK29)
      | ~ v1_funct_1(sK29)
      | ~ v1_relat_1(sK29) ) ),
    inference(superposition,[],[f2454,f2371])).

fof(f2454,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f2046])).

fof(f2046,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f2045])).

fof(f2045,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f1542])).

fof(f1542,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f1541])).

fof(f1541,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f1050])).

fof(f1050,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(f4311,plain,(
    ! [X6,X7] :
      ( r2_hidden(X7,sK28)
      | ~ r2_hidden(X6,sK27)
      | ~ r2_hidden(k4_tarski(X6,X7),sK29)
      | ~ r2_hidden(X6,k1_relat_1(sK29)) ) ),
    inference(subsumption_resolution,[],[f4310,f2369])).

fof(f4310,plain,(
    ! [X6,X7] :
      ( r2_hidden(X7,sK28)
      | ~ r2_hidden(X6,sK27)
      | ~ r2_hidden(k4_tarski(X6,X7),sK29)
      | ~ r2_hidden(X6,k1_relat_1(sK29))
      | ~ v1_relat_1(sK29) ) ),
    inference(subsumption_resolution,[],[f4287,f2370])).

fof(f4287,plain,(
    ! [X6,X7] :
      ( r2_hidden(X7,sK28)
      | ~ r2_hidden(X6,sK27)
      | ~ r2_hidden(k4_tarski(X6,X7),sK29)
      | ~ r2_hidden(X6,k1_relat_1(sK29))
      | ~ v1_funct_1(sK29)
      | ~ v1_relat_1(sK29) ) ),
    inference(superposition,[],[f2372,f2529])).

fof(f2529,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X0,X1) = X2
      | ~ r2_hidden(k4_tarski(X1,X2),X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f2091])).

fof(f2091,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( ( k1_funct_1(X0,X1) = X2
                | k1_xboole_0 != X2 )
              & ( k1_xboole_0 = X2
                | k1_funct_1(X0,X1) != X2 ) )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( ( k1_funct_1(X0,X1) = X2
                | ~ r2_hidden(k4_tarski(X1,X2),X0) )
              & ( r2_hidden(k4_tarski(X1,X2),X0)
                | k1_funct_1(X0,X1) != X2 ) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f1580])).

fof(f1580,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1579])).

fof(f1579,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f903])).

fof(f903,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( ( ~ r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 ) )
          & ( r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).

fof(f2372,plain,(
    ! [X3] :
      ( r2_hidden(k1_funct_1(sK29,X3),sK28)
      | ~ r2_hidden(X3,sK27) ) ),
    inference(cnf_transformation,[],[f2014])).
%------------------------------------------------------------------------------
