%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1417+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:20 EST 2020

% Result     : Theorem 31.43s
% Output     : Refutation 31.43s
% Verified   : 
% Statistics : Number of formulae       :  182 ( 966 expanded)
%              Number of leaves         :   28 ( 429 expanded)
%              Depth                    :   15
%              Number of atoms          :  862 (7513 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21314,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f3590,f3595,f3738,f3761,f3764,f3767,f3791,f3794,f3797,f7113,f15176,f15430,f15802,f20100,f21119,f21120,f21270,f21273])).

fof(f21273,plain,
    ( spl92_27
    | ~ spl92_9
    | ~ spl92_10
    | ~ spl92_11 ),
    inference(avatar_split_clause,[],[f21272,f3583,f3579,f3575,f3915])).

fof(f3915,plain,
    ( spl92_27
  <=> v1_funct_2(k3_filter_1(sK2,sK3,sK5),k2_zfmisc_1(k8_eqrel_1(sK2,sK3),k8_eqrel_1(sK2,sK3)),k8_eqrel_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl92_27])])).

fof(f3575,plain,
    ( spl92_9
  <=> v1_funct_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl92_9])])).

fof(f3579,plain,
    ( spl92_10
  <=> v1_funct_2(sK5,k2_zfmisc_1(sK2,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl92_10])])).

fof(f3583,plain,
    ( spl92_11
  <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK2),sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl92_11])])).

fof(f21272,plain,
    ( v1_funct_2(k3_filter_1(sK2,sK3,sK5),k2_zfmisc_1(k8_eqrel_1(sK2,sK3),k8_eqrel_1(sK2,sK3)),k8_eqrel_1(sK2,sK3))
    | ~ spl92_9
    | ~ spl92_10
    | ~ spl92_11 ),
    inference(subsumption_resolution,[],[f21271,f3580])).

fof(f3580,plain,
    ( v1_funct_2(sK5,k2_zfmisc_1(sK2,sK2),sK2)
    | ~ spl92_10 ),
    inference(avatar_component_clause,[],[f3579])).

fof(f21271,plain,
    ( ~ v1_funct_2(sK5,k2_zfmisc_1(sK2,sK2),sK2)
    | v1_funct_2(k3_filter_1(sK2,sK3,sK5),k2_zfmisc_1(k8_eqrel_1(sK2,sK3),k8_eqrel_1(sK2,sK3)),k8_eqrel_1(sK2,sK3))
    | ~ spl92_9
    | ~ spl92_11 ),
    inference(subsumption_resolution,[],[f20086,f3584])).

fof(f3584,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK2),sK2)))
    | ~ spl92_11 ),
    inference(avatar_component_clause,[],[f3583])).

fof(f20086,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK2),sK2)))
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK2,sK2),sK2)
    | v1_funct_2(k3_filter_1(sK2,sK3,sK5),k2_zfmisc_1(k8_eqrel_1(sK2,sK3),k8_eqrel_1(sK2,sK3)),k8_eqrel_1(sK2,sK3))
    | ~ spl92_9 ),
    inference(resolution,[],[f3443,f3576])).

fof(f3576,plain,
    ( v1_funct_1(sK5)
    | ~ spl92_9 ),
    inference(avatar_component_clause,[],[f3575])).

fof(f3443,plain,(
    ! [X1] :
      ( ~ v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK2),sK2)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(sK2,sK2),sK2)
      | v1_funct_2(k3_filter_1(sK2,sK3,X1),k2_zfmisc_1(k8_eqrel_1(sK2,sK3),k8_eqrel_1(sK2,sK3)),k8_eqrel_1(sK2,sK3)) ) ),
    inference(subsumption_resolution,[],[f3442,f2978])).

fof(f2978,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f2804])).

fof(f2804,plain,
    ( ~ r6_binop_1(k8_eqrel_1(sK2,sK3),k3_filter_1(sK2,sK3,sK4),k3_filter_1(sK2,sK3,sK5))
    & r6_binop_1(sK2,sK4,sK5)
    & m2_filter_1(sK5,sK2,sK3)
    & m2_filter_1(sK4,sK2,sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    & v8_relat_2(sK3)
    & v3_relat_2(sK3)
    & v1_partfun1(sK3,sK2)
    & ~ v1_xboole_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f2640,f2803,f2802,f2801,f2800])).

fof(f2800,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ r6_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
                    & r6_binop_1(X0,X2,X3)
                    & m2_filter_1(X3,X0,X1) )
                & m2_filter_1(X2,X0,X1) )
            & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v8_relat_2(X1)
            & v3_relat_2(X1)
            & v1_partfun1(X1,X0) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r6_binop_1(k8_eqrel_1(sK2,X1),k3_filter_1(sK2,X1,X2),k3_filter_1(sK2,X1,X3))
                  & r6_binop_1(sK2,X2,X3)
                  & m2_filter_1(X3,sK2,X1) )
              & m2_filter_1(X2,sK2,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
          & v8_relat_2(X1)
          & v3_relat_2(X1)
          & v1_partfun1(X1,sK2) )
      & ~ v1_xboole_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f2801,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ r6_binop_1(k8_eqrel_1(sK2,X1),k3_filter_1(sK2,X1,X2),k3_filter_1(sK2,X1,X3))
                & r6_binop_1(sK2,X2,X3)
                & m2_filter_1(X3,sK2,X1) )
            & m2_filter_1(X2,sK2,X1) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
        & v8_relat_2(X1)
        & v3_relat_2(X1)
        & v1_partfun1(X1,sK2) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ r6_binop_1(k8_eqrel_1(sK2,sK3),k3_filter_1(sK2,sK3,X2),k3_filter_1(sK2,sK3,X3))
              & r6_binop_1(sK2,X2,X3)
              & m2_filter_1(X3,sK2,sK3) )
          & m2_filter_1(X2,sK2,sK3) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      & v8_relat_2(sK3)
      & v3_relat_2(sK3)
      & v1_partfun1(sK3,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f2802,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ r6_binop_1(k8_eqrel_1(sK2,sK3),k3_filter_1(sK2,sK3,X2),k3_filter_1(sK2,sK3,X3))
            & r6_binop_1(sK2,X2,X3)
            & m2_filter_1(X3,sK2,sK3) )
        & m2_filter_1(X2,sK2,sK3) )
   => ( ? [X3] :
          ( ~ r6_binop_1(k8_eqrel_1(sK2,sK3),k3_filter_1(sK2,sK3,sK4),k3_filter_1(sK2,sK3,X3))
          & r6_binop_1(sK2,sK4,X3)
          & m2_filter_1(X3,sK2,sK3) )
      & m2_filter_1(sK4,sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f2803,plain,
    ( ? [X3] :
        ( ~ r6_binop_1(k8_eqrel_1(sK2,sK3),k3_filter_1(sK2,sK3,sK4),k3_filter_1(sK2,sK3,X3))
        & r6_binop_1(sK2,sK4,X3)
        & m2_filter_1(X3,sK2,sK3) )
   => ( ~ r6_binop_1(k8_eqrel_1(sK2,sK3),k3_filter_1(sK2,sK3,sK4),k3_filter_1(sK2,sK3,sK5))
      & r6_binop_1(sK2,sK4,sK5)
      & m2_filter_1(sK5,sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f2640,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r6_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
                  & r6_binop_1(X0,X2,X3)
                  & m2_filter_1(X3,X0,X1) )
              & m2_filter_1(X2,X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v8_relat_2(X1)
          & v3_relat_2(X1)
          & v1_partfun1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f2639])).

fof(f2639,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r6_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
                  & r6_binop_1(X0,X2,X3)
                  & m2_filter_1(X3,X0,X1) )
              & m2_filter_1(X2,X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v8_relat_2(X1)
          & v3_relat_2(X1)
          & v1_partfun1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2623])).

fof(f2623,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v8_relat_2(X1)
              & v3_relat_2(X1)
              & v1_partfun1(X1,X0) )
           => ! [X2] :
                ( m2_filter_1(X2,X0,X1)
               => ! [X3] :
                    ( m2_filter_1(X3,X0,X1)
                   => ( r6_binop_1(X0,X2,X3)
                     => r6_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f2622])).

fof(f2622,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v8_relat_2(X1)
            & v3_relat_2(X1)
            & v1_partfun1(X1,X0) )
         => ! [X2] :
              ( m2_filter_1(X2,X0,X1)
             => ! [X3] :
                  ( m2_filter_1(X3,X0,X1)
                 => ( r6_binop_1(X0,X2,X3)
                   => r6_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_filter_1)).

fof(f3442,plain,(
    ! [X1] :
      ( v1_funct_2(k3_filter_1(sK2,sK3,X1),k2_zfmisc_1(k8_eqrel_1(sK2,sK3),k8_eqrel_1(sK2,sK3)),k8_eqrel_1(sK2,sK3))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK2),sK2)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(sK2,sK2),sK2)
      | ~ v1_funct_1(X1)
      | v1_xboole_0(sK2) ) ),
    inference(subsumption_resolution,[],[f3441,f2980])).

fof(f2980,plain,(
    v3_relat_2(sK3) ),
    inference(cnf_transformation,[],[f2804])).

fof(f3441,plain,(
    ! [X1] :
      ( v1_funct_2(k3_filter_1(sK2,sK3,X1),k2_zfmisc_1(k8_eqrel_1(sK2,sK3),k8_eqrel_1(sK2,sK3)),k8_eqrel_1(sK2,sK3))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK2),sK2)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(sK2,sK2),sK2)
      | ~ v1_funct_1(X1)
      | ~ v3_relat_2(sK3)
      | v1_xboole_0(sK2) ) ),
    inference(subsumption_resolution,[],[f3440,f2981])).

fof(f2981,plain,(
    v8_relat_2(sK3) ),
    inference(cnf_transformation,[],[f2804])).

fof(f3440,plain,(
    ! [X1] :
      ( v1_funct_2(k3_filter_1(sK2,sK3,X1),k2_zfmisc_1(k8_eqrel_1(sK2,sK3),k8_eqrel_1(sK2,sK3)),k8_eqrel_1(sK2,sK3))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK2),sK2)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(sK2,sK2),sK2)
      | ~ v1_funct_1(X1)
      | ~ v8_relat_2(sK3)
      | ~ v3_relat_2(sK3)
      | v1_xboole_0(sK2) ) ),
    inference(subsumption_resolution,[],[f3429,f2982])).

fof(f2982,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f2804])).

fof(f3429,plain,(
    ! [X1] :
      ( v1_funct_2(k3_filter_1(sK2,sK3,X1),k2_zfmisc_1(k8_eqrel_1(sK2,sK3),k8_eqrel_1(sK2,sK3)),k8_eqrel_1(sK2,sK3))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK2),sK2)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(sK2,sK2),sK2)
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      | ~ v8_relat_2(sK3)
      | ~ v3_relat_2(sK3)
      | v1_xboole_0(sK2) ) ),
    inference(resolution,[],[f2979,f2988])).

fof(f2988,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k3_filter_1(X0,X1,X2),k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | ~ v1_partfun1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f2642])).

fof(f2642,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k3_filter_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))))
        & v1_funct_2(k3_filter_1(X0,X1,X2),k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))
        & v1_funct_1(k3_filter_1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | ~ v1_partfun1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f2641])).

fof(f2641,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k3_filter_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))))
        & v1_funct_2(k3_filter_1(X0,X1,X2),k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))
        & v1_funct_1(k3_filter_1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | ~ v1_partfun1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2588])).

fof(f2588,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
        & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
        & v1_funct_1(X2)
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v8_relat_2(X1)
        & v3_relat_2(X1)
        & v1_partfun1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => ( m1_subset_1(k3_filter_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))))
        & v1_funct_2(k3_filter_1(X0,X1,X2),k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))
        & v1_funct_1(k3_filter_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_filter_1)).

fof(f2979,plain,(
    v1_partfun1(sK3,sK2) ),
    inference(cnf_transformation,[],[f2804])).

fof(f21270,plain,
    ( ~ spl92_25
    | ~ spl92_27
    | ~ spl92_28
    | ~ spl92_23
    | ~ spl92_24
    | ~ spl92_26
    | ~ spl92_29
    | ~ spl92_30 ),
    inference(avatar_split_clause,[],[f21269,f3927,f3923,f3911,f3903,f3899,f3919,f3915,f3907])).

fof(f3907,plain,
    ( spl92_25
  <=> m1_subset_1(k3_filter_1(sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK2,sK3),k8_eqrel_1(sK2,sK3)),k8_eqrel_1(sK2,sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl92_25])])).

fof(f3919,plain,
    ( spl92_28
  <=> m1_subset_1(k3_filter_1(sK2,sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK2,sK3),k8_eqrel_1(sK2,sK3)),k8_eqrel_1(sK2,sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl92_28])])).

fof(f3899,plain,
    ( spl92_23
  <=> v1_funct_1(k3_filter_1(sK2,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl92_23])])).

fof(f3903,plain,
    ( spl92_24
  <=> v1_funct_2(k3_filter_1(sK2,sK3,sK4),k2_zfmisc_1(k8_eqrel_1(sK2,sK3),k8_eqrel_1(sK2,sK3)),k8_eqrel_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl92_24])])).

fof(f3911,plain,
    ( spl92_26
  <=> v1_funct_1(k3_filter_1(sK2,sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl92_26])])).

fof(f3923,plain,
    ( spl92_29
  <=> r4_binop_1(k8_eqrel_1(sK2,sK3),k3_filter_1(sK2,sK3,sK4),k3_filter_1(sK2,sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl92_29])])).

fof(f3927,plain,
    ( spl92_30
  <=> r5_binop_1(k8_eqrel_1(sK2,sK3),k3_filter_1(sK2,sK3,sK4),k3_filter_1(sK2,sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl92_30])])).

fof(f21269,plain,
    ( ~ m1_subset_1(k3_filter_1(sK2,sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK2,sK3),k8_eqrel_1(sK2,sK3)),k8_eqrel_1(sK2,sK3))))
    | ~ v1_funct_2(k3_filter_1(sK2,sK3,sK5),k2_zfmisc_1(k8_eqrel_1(sK2,sK3),k8_eqrel_1(sK2,sK3)),k8_eqrel_1(sK2,sK3))
    | ~ m1_subset_1(k3_filter_1(sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK2,sK3),k8_eqrel_1(sK2,sK3)),k8_eqrel_1(sK2,sK3))))
    | ~ spl92_23
    | ~ spl92_24
    | ~ spl92_26
    | ~ spl92_29
    | ~ spl92_30 ),
    inference(subsumption_resolution,[],[f21268,f3900])).

fof(f3900,plain,
    ( v1_funct_1(k3_filter_1(sK2,sK3,sK4))
    | ~ spl92_23 ),
    inference(avatar_component_clause,[],[f3899])).

fof(f21268,plain,
    ( ~ m1_subset_1(k3_filter_1(sK2,sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK2,sK3),k8_eqrel_1(sK2,sK3)),k8_eqrel_1(sK2,sK3))))
    | ~ v1_funct_2(k3_filter_1(sK2,sK3,sK5),k2_zfmisc_1(k8_eqrel_1(sK2,sK3),k8_eqrel_1(sK2,sK3)),k8_eqrel_1(sK2,sK3))
    | ~ m1_subset_1(k3_filter_1(sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK2,sK3),k8_eqrel_1(sK2,sK3)),k8_eqrel_1(sK2,sK3))))
    | ~ v1_funct_1(k3_filter_1(sK2,sK3,sK4))
    | ~ spl92_24
    | ~ spl92_26
    | ~ spl92_29
    | ~ spl92_30 ),
    inference(subsumption_resolution,[],[f21267,f3904])).

fof(f3904,plain,
    ( v1_funct_2(k3_filter_1(sK2,sK3,sK4),k2_zfmisc_1(k8_eqrel_1(sK2,sK3),k8_eqrel_1(sK2,sK3)),k8_eqrel_1(sK2,sK3))
    | ~ spl92_24 ),
    inference(avatar_component_clause,[],[f3903])).

fof(f21267,plain,
    ( ~ m1_subset_1(k3_filter_1(sK2,sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK2,sK3),k8_eqrel_1(sK2,sK3)),k8_eqrel_1(sK2,sK3))))
    | ~ v1_funct_2(k3_filter_1(sK2,sK3,sK5),k2_zfmisc_1(k8_eqrel_1(sK2,sK3),k8_eqrel_1(sK2,sK3)),k8_eqrel_1(sK2,sK3))
    | ~ m1_subset_1(k3_filter_1(sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK2,sK3),k8_eqrel_1(sK2,sK3)),k8_eqrel_1(sK2,sK3))))
    | ~ v1_funct_2(k3_filter_1(sK2,sK3,sK4),k2_zfmisc_1(k8_eqrel_1(sK2,sK3),k8_eqrel_1(sK2,sK3)),k8_eqrel_1(sK2,sK3))
    | ~ v1_funct_1(k3_filter_1(sK2,sK3,sK4))
    | ~ spl92_26
    | ~ spl92_29
    | ~ spl92_30 ),
    inference(subsumption_resolution,[],[f15804,f3912])).

fof(f3912,plain,
    ( v1_funct_1(k3_filter_1(sK2,sK3,sK5))
    | ~ spl92_26 ),
    inference(avatar_component_clause,[],[f3911])).

fof(f15804,plain,
    ( ~ m1_subset_1(k3_filter_1(sK2,sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK2,sK3),k8_eqrel_1(sK2,sK3)),k8_eqrel_1(sK2,sK3))))
    | ~ v1_funct_2(k3_filter_1(sK2,sK3,sK5),k2_zfmisc_1(k8_eqrel_1(sK2,sK3),k8_eqrel_1(sK2,sK3)),k8_eqrel_1(sK2,sK3))
    | ~ v1_funct_1(k3_filter_1(sK2,sK3,sK5))
    | ~ m1_subset_1(k3_filter_1(sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK2,sK3),k8_eqrel_1(sK2,sK3)),k8_eqrel_1(sK2,sK3))))
    | ~ v1_funct_2(k3_filter_1(sK2,sK3,sK4),k2_zfmisc_1(k8_eqrel_1(sK2,sK3),k8_eqrel_1(sK2,sK3)),k8_eqrel_1(sK2,sK3))
    | ~ v1_funct_1(k3_filter_1(sK2,sK3,sK4))
    | ~ spl92_29
    | ~ spl92_30 ),
    inference(subsumption_resolution,[],[f15803,f3924])).

fof(f3924,plain,
    ( r4_binop_1(k8_eqrel_1(sK2,sK3),k3_filter_1(sK2,sK3,sK4),k3_filter_1(sK2,sK3,sK5))
    | ~ spl92_29 ),
    inference(avatar_component_clause,[],[f3923])).

fof(f15803,plain,
    ( ~ r4_binop_1(k8_eqrel_1(sK2,sK3),k3_filter_1(sK2,sK3,sK4),k3_filter_1(sK2,sK3,sK5))
    | ~ m1_subset_1(k3_filter_1(sK2,sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK2,sK3),k8_eqrel_1(sK2,sK3)),k8_eqrel_1(sK2,sK3))))
    | ~ v1_funct_2(k3_filter_1(sK2,sK3,sK5),k2_zfmisc_1(k8_eqrel_1(sK2,sK3),k8_eqrel_1(sK2,sK3)),k8_eqrel_1(sK2,sK3))
    | ~ v1_funct_1(k3_filter_1(sK2,sK3,sK5))
    | ~ m1_subset_1(k3_filter_1(sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK2,sK3),k8_eqrel_1(sK2,sK3)),k8_eqrel_1(sK2,sK3))))
    | ~ v1_funct_2(k3_filter_1(sK2,sK3,sK4),k2_zfmisc_1(k8_eqrel_1(sK2,sK3),k8_eqrel_1(sK2,sK3)),k8_eqrel_1(sK2,sK3))
    | ~ v1_funct_1(k3_filter_1(sK2,sK3,sK4))
    | ~ spl92_30 ),
    inference(subsumption_resolution,[],[f15490,f2986])).

fof(f2986,plain,(
    ~ r6_binop_1(k8_eqrel_1(sK2,sK3),k3_filter_1(sK2,sK3,sK4),k3_filter_1(sK2,sK3,sK5)) ),
    inference(cnf_transformation,[],[f2804])).

fof(f15490,plain,
    ( r6_binop_1(k8_eqrel_1(sK2,sK3),k3_filter_1(sK2,sK3,sK4),k3_filter_1(sK2,sK3,sK5))
    | ~ r4_binop_1(k8_eqrel_1(sK2,sK3),k3_filter_1(sK2,sK3,sK4),k3_filter_1(sK2,sK3,sK5))
    | ~ m1_subset_1(k3_filter_1(sK2,sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK2,sK3),k8_eqrel_1(sK2,sK3)),k8_eqrel_1(sK2,sK3))))
    | ~ v1_funct_2(k3_filter_1(sK2,sK3,sK5),k2_zfmisc_1(k8_eqrel_1(sK2,sK3),k8_eqrel_1(sK2,sK3)),k8_eqrel_1(sK2,sK3))
    | ~ v1_funct_1(k3_filter_1(sK2,sK3,sK5))
    | ~ m1_subset_1(k3_filter_1(sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK2,sK3),k8_eqrel_1(sK2,sK3)),k8_eqrel_1(sK2,sK3))))
    | ~ v1_funct_2(k3_filter_1(sK2,sK3,sK4),k2_zfmisc_1(k8_eqrel_1(sK2,sK3),k8_eqrel_1(sK2,sK3)),k8_eqrel_1(sK2,sK3))
    | ~ v1_funct_1(k3_filter_1(sK2,sK3,sK4))
    | ~ spl92_30 ),
    inference(resolution,[],[f3928,f2992])).

fof(f2992,plain,(
    ! [X2,X0,X1] :
      ( r6_binop_1(X0,X1,X2)
      | ~ r5_binop_1(X0,X1,X2)
      | ~ r4_binop_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f2806])).

fof(f2806,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r6_binop_1(X0,X1,X2)
              | ~ r5_binop_1(X0,X1,X2)
              | ~ r4_binop_1(X0,X1,X2) )
            & ( ( r5_binop_1(X0,X1,X2)
                & r4_binop_1(X0,X1,X2) )
              | ~ r6_binop_1(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
          | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
          | ~ v1_funct_1(X2) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f2805])).

fof(f2805,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r6_binop_1(X0,X1,X2)
              | ~ r5_binop_1(X0,X1,X2)
              | ~ r4_binop_1(X0,X1,X2) )
            & ( ( r5_binop_1(X0,X1,X2)
                & r4_binop_1(X0,X1,X2) )
              | ~ r6_binop_1(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
          | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
          | ~ v1_funct_1(X2) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1) ) ),
    inference(nnf_transformation,[],[f2644])).

fof(f2644,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r6_binop_1(X0,X1,X2)
          <=> ( r5_binop_1(X0,X1,X2)
              & r4_binop_1(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
          | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
          | ~ v1_funct_1(X2) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f2643])).

fof(f2643,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r6_binop_1(X0,X1,X2)
          <=> ( r5_binop_1(X0,X1,X2)
              & r4_binop_1(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
          | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
          | ~ v1_funct_1(X2) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f2575])).

fof(f2575,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
        & v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
            & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
            & v1_funct_1(X2) )
         => ( r6_binop_1(X0,X1,X2)
          <=> ( r5_binop_1(X0,X1,X2)
              & r4_binop_1(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_binop_1)).

fof(f3928,plain,
    ( r5_binop_1(k8_eqrel_1(sK2,sK3),k3_filter_1(sK2,sK3,sK4),k3_filter_1(sK2,sK3,sK5))
    | ~ spl92_30 ),
    inference(avatar_component_clause,[],[f3927])).

fof(f21120,plain,
    ( spl92_25
    | ~ spl92_6
    | ~ spl92_7
    | ~ spl92_8 ),
    inference(avatar_split_clause,[],[f21104,f3571,f3567,f3563,f3907])).

fof(f3563,plain,
    ( spl92_6
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl92_6])])).

fof(f3567,plain,
    ( spl92_7
  <=> v1_funct_2(sK4,k2_zfmisc_1(sK2,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl92_7])])).

fof(f3571,plain,
    ( spl92_8
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK2),sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl92_8])])).

fof(f21104,plain,
    ( m1_subset_1(k3_filter_1(sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK2,sK3),k8_eqrel_1(sK2,sK3)),k8_eqrel_1(sK2,sK3))))
    | ~ spl92_6
    | ~ spl92_7
    | ~ spl92_8 ),
    inference(subsumption_resolution,[],[f21103,f3568])).

fof(f3568,plain,
    ( v1_funct_2(sK4,k2_zfmisc_1(sK2,sK2),sK2)
    | ~ spl92_7 ),
    inference(avatar_component_clause,[],[f3567])).

fof(f21103,plain,
    ( ~ v1_funct_2(sK4,k2_zfmisc_1(sK2,sK2),sK2)
    | m1_subset_1(k3_filter_1(sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK2,sK3),k8_eqrel_1(sK2,sK3)),k8_eqrel_1(sK2,sK3))))
    | ~ spl92_6
    | ~ spl92_8 ),
    inference(subsumption_resolution,[],[f21085,f3572])).

fof(f3572,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK2),sK2)))
    | ~ spl92_8 ),
    inference(avatar_component_clause,[],[f3571])).

fof(f21085,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK2),sK2)))
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK2,sK2),sK2)
    | m1_subset_1(k3_filter_1(sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK2,sK3),k8_eqrel_1(sK2,sK3)),k8_eqrel_1(sK2,sK3))))
    | ~ spl92_6 ),
    inference(resolution,[],[f3447,f3564])).

fof(f3564,plain,
    ( v1_funct_1(sK4)
    | ~ spl92_6 ),
    inference(avatar_component_clause,[],[f3563])).

fof(f3447,plain,(
    ! [X2] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK2),sK2)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(sK2,sK2),sK2)
      | m1_subset_1(k3_filter_1(sK2,sK3,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK2,sK3),k8_eqrel_1(sK2,sK3)),k8_eqrel_1(sK2,sK3)))) ) ),
    inference(subsumption_resolution,[],[f3446,f2978])).

fof(f3446,plain,(
    ! [X2] :
      ( m1_subset_1(k3_filter_1(sK2,sK3,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK2,sK3),k8_eqrel_1(sK2,sK3)),k8_eqrel_1(sK2,sK3))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK2),sK2)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(sK2,sK2),sK2)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(sK2) ) ),
    inference(subsumption_resolution,[],[f3445,f2980])).

fof(f3445,plain,(
    ! [X2] :
      ( m1_subset_1(k3_filter_1(sK2,sK3,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK2,sK3),k8_eqrel_1(sK2,sK3)),k8_eqrel_1(sK2,sK3))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK2),sK2)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(sK2,sK2),sK2)
      | ~ v1_funct_1(X2)
      | ~ v3_relat_2(sK3)
      | v1_xboole_0(sK2) ) ),
    inference(subsumption_resolution,[],[f3444,f2981])).

fof(f3444,plain,(
    ! [X2] :
      ( m1_subset_1(k3_filter_1(sK2,sK3,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK2,sK3),k8_eqrel_1(sK2,sK3)),k8_eqrel_1(sK2,sK3))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK2),sK2)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(sK2,sK2),sK2)
      | ~ v1_funct_1(X2)
      | ~ v8_relat_2(sK3)
      | ~ v3_relat_2(sK3)
      | v1_xboole_0(sK2) ) ),
    inference(subsumption_resolution,[],[f3430,f2982])).

fof(f3430,plain,(
    ! [X2] :
      ( m1_subset_1(k3_filter_1(sK2,sK3,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK2,sK3),k8_eqrel_1(sK2,sK3)),k8_eqrel_1(sK2,sK3))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK2),sK2)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(sK2,sK2),sK2)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      | ~ v8_relat_2(sK3)
      | ~ v3_relat_2(sK3)
      | v1_xboole_0(sK2) ) ),
    inference(resolution,[],[f2979,f2989])).

fof(f2989,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_filter_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | ~ v1_partfun1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f2642])).

fof(f21119,plain,
    ( spl92_28
    | ~ spl92_9
    | ~ spl92_10
    | ~ spl92_11 ),
    inference(avatar_split_clause,[],[f21109,f3583,f3579,f3575,f3919])).

fof(f21109,plain,
    ( m1_subset_1(k3_filter_1(sK2,sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK2,sK3),k8_eqrel_1(sK2,sK3)),k8_eqrel_1(sK2,sK3))))
    | ~ spl92_9
    | ~ spl92_10
    | ~ spl92_11 ),
    inference(subsumption_resolution,[],[f21108,f3580])).

fof(f21108,plain,
    ( ~ v1_funct_2(sK5,k2_zfmisc_1(sK2,sK2),sK2)
    | m1_subset_1(k3_filter_1(sK2,sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK2,sK3),k8_eqrel_1(sK2,sK3)),k8_eqrel_1(sK2,sK3))))
    | ~ spl92_9
    | ~ spl92_11 ),
    inference(subsumption_resolution,[],[f21086,f3584])).

fof(f21086,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK2),sK2)))
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK2,sK2),sK2)
    | m1_subset_1(k3_filter_1(sK2,sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK2,sK3),k8_eqrel_1(sK2,sK3)),k8_eqrel_1(sK2,sK3))))
    | ~ spl92_9 ),
    inference(resolution,[],[f3447,f3576])).

fof(f20100,plain,
    ( spl92_24
    | ~ spl92_6
    | ~ spl92_7
    | ~ spl92_8 ),
    inference(avatar_split_clause,[],[f20097,f3571,f3567,f3563,f3903])).

fof(f20097,plain,
    ( v1_funct_2(k3_filter_1(sK2,sK3,sK4),k2_zfmisc_1(k8_eqrel_1(sK2,sK3),k8_eqrel_1(sK2,sK3)),k8_eqrel_1(sK2,sK3))
    | ~ spl92_6
    | ~ spl92_7
    | ~ spl92_8 ),
    inference(subsumption_resolution,[],[f20096,f3568])).

fof(f20096,plain,
    ( ~ v1_funct_2(sK4,k2_zfmisc_1(sK2,sK2),sK2)
    | v1_funct_2(k3_filter_1(sK2,sK3,sK4),k2_zfmisc_1(k8_eqrel_1(sK2,sK3),k8_eqrel_1(sK2,sK3)),k8_eqrel_1(sK2,sK3))
    | ~ spl92_6
    | ~ spl92_8 ),
    inference(subsumption_resolution,[],[f20085,f3572])).

fof(f20085,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK2),sK2)))
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK2,sK2),sK2)
    | v1_funct_2(k3_filter_1(sK2,sK3,sK4),k2_zfmisc_1(k8_eqrel_1(sK2,sK3),k8_eqrel_1(sK2,sK3)),k8_eqrel_1(sK2,sK3))
    | ~ spl92_6 ),
    inference(resolution,[],[f3443,f3564])).

fof(f15802,plain,
    ( spl92_26
    | ~ spl92_9
    | ~ spl92_10
    | ~ spl92_11 ),
    inference(avatar_split_clause,[],[f15786,f3583,f3579,f3575,f3911])).

fof(f15786,plain,
    ( v1_funct_1(k3_filter_1(sK2,sK3,sK5))
    | ~ spl92_9
    | ~ spl92_10
    | ~ spl92_11 ),
    inference(subsumption_resolution,[],[f15785,f3580])).

fof(f15785,plain,
    ( ~ v1_funct_2(sK5,k2_zfmisc_1(sK2,sK2),sK2)
    | v1_funct_1(k3_filter_1(sK2,sK3,sK5))
    | ~ spl92_9
    | ~ spl92_11 ),
    inference(subsumption_resolution,[],[f15749,f3584])).

fof(f15749,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK2),sK2)))
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK2,sK2),sK2)
    | v1_funct_1(k3_filter_1(sK2,sK3,sK5))
    | ~ spl92_9 ),
    inference(resolution,[],[f3439,f3576])).

fof(f3439,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK2),sK2)))
      | ~ v1_funct_2(X0,k2_zfmisc_1(sK2,sK2),sK2)
      | v1_funct_1(k3_filter_1(sK2,sK3,X0)) ) ),
    inference(subsumption_resolution,[],[f3438,f2978])).

fof(f3438,plain,(
    ! [X0] :
      ( v1_funct_1(k3_filter_1(sK2,sK3,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK2),sK2)))
      | ~ v1_funct_2(X0,k2_zfmisc_1(sK2,sK2),sK2)
      | ~ v1_funct_1(X0)
      | v1_xboole_0(sK2) ) ),
    inference(subsumption_resolution,[],[f3437,f2980])).

fof(f3437,plain,(
    ! [X0] :
      ( v1_funct_1(k3_filter_1(sK2,sK3,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK2),sK2)))
      | ~ v1_funct_2(X0,k2_zfmisc_1(sK2,sK2),sK2)
      | ~ v1_funct_1(X0)
      | ~ v3_relat_2(sK3)
      | v1_xboole_0(sK2) ) ),
    inference(subsumption_resolution,[],[f3436,f2981])).

fof(f3436,plain,(
    ! [X0] :
      ( v1_funct_1(k3_filter_1(sK2,sK3,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK2),sK2)))
      | ~ v1_funct_2(X0,k2_zfmisc_1(sK2,sK2),sK2)
      | ~ v1_funct_1(X0)
      | ~ v8_relat_2(sK3)
      | ~ v3_relat_2(sK3)
      | v1_xboole_0(sK2) ) ),
    inference(subsumption_resolution,[],[f3428,f2982])).

fof(f3428,plain,(
    ! [X0] :
      ( v1_funct_1(k3_filter_1(sK2,sK3,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK2),sK2)))
      | ~ v1_funct_2(X0,k2_zfmisc_1(sK2,sK2),sK2)
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      | ~ v8_relat_2(sK3)
      | ~ v3_relat_2(sK3)
      | v1_xboole_0(sK2) ) ),
    inference(resolution,[],[f2979,f2987])).

fof(f2987,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k3_filter_1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | ~ v1_partfun1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f2642])).

fof(f15430,plain,
    ( spl92_30
    | ~ spl92_13 ),
    inference(avatar_split_clause,[],[f15429,f3592,f3927])).

fof(f3592,plain,
    ( spl92_13
  <=> r5_binop_1(sK2,sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl92_13])])).

fof(f15429,plain,
    ( r5_binop_1(k8_eqrel_1(sK2,sK3),k3_filter_1(sK2,sK3,sK4),k3_filter_1(sK2,sK3,sK5))
    | ~ spl92_13 ),
    inference(subsumption_resolution,[],[f15416,f3594])).

fof(f3594,plain,
    ( r5_binop_1(sK2,sK4,sK5)
    | ~ spl92_13 ),
    inference(avatar_component_clause,[],[f3592])).

fof(f15416,plain,
    ( ~ r5_binop_1(sK2,sK4,sK5)
    | r5_binop_1(k8_eqrel_1(sK2,sK3),k3_filter_1(sK2,sK3,sK4),k3_filter_1(sK2,sK3,sK5)) ),
    inference(resolution,[],[f3753,f2983])).

fof(f2983,plain,(
    m2_filter_1(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f2804])).

fof(f3753,plain,(
    ! [X1] :
      ( ~ m2_filter_1(X1,sK2,sK3)
      | ~ r5_binop_1(sK2,X1,sK5)
      | r5_binop_1(k8_eqrel_1(sK2,sK3),k3_filter_1(sK2,sK3,X1),k3_filter_1(sK2,sK3,sK5)) ) ),
    inference(subsumption_resolution,[],[f3752,f2978])).

fof(f3752,plain,(
    ! [X1] :
      ( r5_binop_1(k8_eqrel_1(sK2,sK3),k3_filter_1(sK2,sK3,X1),k3_filter_1(sK2,sK3,sK5))
      | ~ r5_binop_1(sK2,X1,sK5)
      | ~ m2_filter_1(X1,sK2,sK3)
      | v1_xboole_0(sK2) ) ),
    inference(subsumption_resolution,[],[f3751,f2979])).

fof(f3751,plain,(
    ! [X1] :
      ( r5_binop_1(k8_eqrel_1(sK2,sK3),k3_filter_1(sK2,sK3,X1),k3_filter_1(sK2,sK3,sK5))
      | ~ r5_binop_1(sK2,X1,sK5)
      | ~ m2_filter_1(X1,sK2,sK3)
      | ~ v1_partfun1(sK3,sK2)
      | v1_xboole_0(sK2) ) ),
    inference(subsumption_resolution,[],[f3750,f2980])).

fof(f3750,plain,(
    ! [X1] :
      ( r5_binop_1(k8_eqrel_1(sK2,sK3),k3_filter_1(sK2,sK3,X1),k3_filter_1(sK2,sK3,sK5))
      | ~ r5_binop_1(sK2,X1,sK5)
      | ~ m2_filter_1(X1,sK2,sK3)
      | ~ v3_relat_2(sK3)
      | ~ v1_partfun1(sK3,sK2)
      | v1_xboole_0(sK2) ) ),
    inference(subsumption_resolution,[],[f3749,f2981])).

fof(f3749,plain,(
    ! [X1] :
      ( r5_binop_1(k8_eqrel_1(sK2,sK3),k3_filter_1(sK2,sK3,X1),k3_filter_1(sK2,sK3,sK5))
      | ~ r5_binop_1(sK2,X1,sK5)
      | ~ m2_filter_1(X1,sK2,sK3)
      | ~ v8_relat_2(sK3)
      | ~ v3_relat_2(sK3)
      | ~ v1_partfun1(sK3,sK2)
      | v1_xboole_0(sK2) ) ),
    inference(subsumption_resolution,[],[f3488,f2982])).

fof(f3488,plain,(
    ! [X1] :
      ( r5_binop_1(k8_eqrel_1(sK2,sK3),k3_filter_1(sK2,sK3,X1),k3_filter_1(sK2,sK3,sK5))
      | ~ r5_binop_1(sK2,X1,sK5)
      | ~ m2_filter_1(X1,sK2,sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      | ~ v8_relat_2(sK3)
      | ~ v3_relat_2(sK3)
      | ~ v1_partfun1(sK3,sK2)
      | v1_xboole_0(sK2) ) ),
    inference(resolution,[],[f2984,f3069])).

fof(f3069,plain,(
    ! [X2,X0,X3,X1] :
      ( r5_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
      | ~ r5_binop_1(X0,X2,X3)
      | ~ m2_filter_1(X3,X0,X1)
      | ~ m2_filter_1(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | ~ v1_partfun1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f2700])).

fof(f2700,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r5_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
                  | ~ r5_binop_1(X0,X2,X3)
                  | ~ m2_filter_1(X3,X0,X1) )
              | ~ m2_filter_1(X2,X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          | ~ v8_relat_2(X1)
          | ~ v3_relat_2(X1)
          | ~ v1_partfun1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f2699])).

fof(f2699,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r5_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
                  | ~ r5_binop_1(X0,X2,X3)
                  | ~ m2_filter_1(X3,X0,X1) )
              | ~ m2_filter_1(X2,X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          | ~ v8_relat_2(X1)
          | ~ v3_relat_2(X1)
          | ~ v1_partfun1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2621])).

fof(f2621,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v8_relat_2(X1)
            & v3_relat_2(X1)
            & v1_partfun1(X1,X0) )
         => ! [X2] :
              ( m2_filter_1(X2,X0,X1)
             => ! [X3] :
                  ( m2_filter_1(X3,X0,X1)
                 => ( r5_binop_1(X0,X2,X3)
                   => r5_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_filter_1)).

fof(f2984,plain,(
    m2_filter_1(sK5,sK2,sK3) ),
    inference(cnf_transformation,[],[f2804])).

fof(f15176,plain,
    ( spl92_29
    | ~ spl92_12 ),
    inference(avatar_split_clause,[],[f15175,f3587,f3923])).

fof(f3587,plain,
    ( spl92_12
  <=> r4_binop_1(sK2,sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl92_12])])).

fof(f15175,plain,
    ( r4_binop_1(k8_eqrel_1(sK2,sK3),k3_filter_1(sK2,sK3,sK4),k3_filter_1(sK2,sK3,sK5))
    | ~ spl92_12 ),
    inference(subsumption_resolution,[],[f15162,f3589])).

fof(f3589,plain,
    ( r4_binop_1(sK2,sK4,sK5)
    | ~ spl92_12 ),
    inference(avatar_component_clause,[],[f3587])).

fof(f15162,plain,
    ( ~ r4_binop_1(sK2,sK4,sK5)
    | r4_binop_1(k8_eqrel_1(sK2,sK3),k3_filter_1(sK2,sK3,sK4),k3_filter_1(sK2,sK3,sK5)) ),
    inference(resolution,[],[f3743,f2983])).

fof(f3743,plain,(
    ! [X3] :
      ( ~ m2_filter_1(X3,sK2,sK3)
      | ~ r4_binop_1(sK2,X3,sK5)
      | r4_binop_1(k8_eqrel_1(sK2,sK3),k3_filter_1(sK2,sK3,X3),k3_filter_1(sK2,sK3,sK5)) ) ),
    inference(subsumption_resolution,[],[f3742,f2978])).

fof(f3742,plain,(
    ! [X3] :
      ( r4_binop_1(k8_eqrel_1(sK2,sK3),k3_filter_1(sK2,sK3,X3),k3_filter_1(sK2,sK3,sK5))
      | ~ r4_binop_1(sK2,X3,sK5)
      | ~ m2_filter_1(X3,sK2,sK3)
      | v1_xboole_0(sK2) ) ),
    inference(subsumption_resolution,[],[f3741,f2979])).

fof(f3741,plain,(
    ! [X3] :
      ( r4_binop_1(k8_eqrel_1(sK2,sK3),k3_filter_1(sK2,sK3,X3),k3_filter_1(sK2,sK3,sK5))
      | ~ r4_binop_1(sK2,X3,sK5)
      | ~ m2_filter_1(X3,sK2,sK3)
      | ~ v1_partfun1(sK3,sK2)
      | v1_xboole_0(sK2) ) ),
    inference(subsumption_resolution,[],[f3740,f2980])).

fof(f3740,plain,(
    ! [X3] :
      ( r4_binop_1(k8_eqrel_1(sK2,sK3),k3_filter_1(sK2,sK3,X3),k3_filter_1(sK2,sK3,sK5))
      | ~ r4_binop_1(sK2,X3,sK5)
      | ~ m2_filter_1(X3,sK2,sK3)
      | ~ v3_relat_2(sK3)
      | ~ v1_partfun1(sK3,sK2)
      | v1_xboole_0(sK2) ) ),
    inference(subsumption_resolution,[],[f3739,f2981])).

fof(f3739,plain,(
    ! [X3] :
      ( r4_binop_1(k8_eqrel_1(sK2,sK3),k3_filter_1(sK2,sK3,X3),k3_filter_1(sK2,sK3,sK5))
      | ~ r4_binop_1(sK2,X3,sK5)
      | ~ m2_filter_1(X3,sK2,sK3)
      | ~ v8_relat_2(sK3)
      | ~ v3_relat_2(sK3)
      | ~ v1_partfun1(sK3,sK2)
      | v1_xboole_0(sK2) ) ),
    inference(subsumption_resolution,[],[f3490,f2982])).

fof(f3490,plain,(
    ! [X3] :
      ( r4_binop_1(k8_eqrel_1(sK2,sK3),k3_filter_1(sK2,sK3,X3),k3_filter_1(sK2,sK3,sK5))
      | ~ r4_binop_1(sK2,X3,sK5)
      | ~ m2_filter_1(X3,sK2,sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      | ~ v8_relat_2(sK3)
      | ~ v3_relat_2(sK3)
      | ~ v1_partfun1(sK3,sK2)
      | v1_xboole_0(sK2) ) ),
    inference(resolution,[],[f2984,f3075])).

fof(f3075,plain,(
    ! [X2,X0,X3,X1] :
      ( r4_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
      | ~ r4_binop_1(X0,X2,X3)
      | ~ m2_filter_1(X3,X0,X1)
      | ~ m2_filter_1(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | ~ v1_partfun1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f2704])).

fof(f2704,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r4_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
                  | ~ r4_binop_1(X0,X2,X3)
                  | ~ m2_filter_1(X3,X0,X1) )
              | ~ m2_filter_1(X2,X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          | ~ v8_relat_2(X1)
          | ~ v3_relat_2(X1)
          | ~ v1_partfun1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f2703])).

fof(f2703,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r4_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
                  | ~ r4_binop_1(X0,X2,X3)
                  | ~ m2_filter_1(X3,X0,X1) )
              | ~ m2_filter_1(X2,X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          | ~ v8_relat_2(X1)
          | ~ v3_relat_2(X1)
          | ~ v1_partfun1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2635])).

fof(f2635,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v8_relat_2(X1)
            & v3_relat_2(X1)
            & v1_partfun1(X1,X0) )
         => ! [X2] :
              ( m2_filter_1(X2,X0,X1)
             => ! [X3] :
                  ( m2_filter_1(X3,X0,X1)
                 => ( r4_binop_1(X0,X2,X3)
                   => r4_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_filter_1)).

fof(f7113,plain,
    ( ~ spl92_6
    | ~ spl92_7
    | ~ spl92_8
    | spl92_23 ),
    inference(avatar_contradiction_clause,[],[f7112])).

fof(f7112,plain,
    ( $false
    | ~ spl92_6
    | ~ spl92_7
    | ~ spl92_8
    | spl92_23 ),
    inference(subsumption_resolution,[],[f7111,f2978])).

fof(f7111,plain,
    ( v1_xboole_0(sK2)
    | ~ spl92_6
    | ~ spl92_7
    | ~ spl92_8
    | spl92_23 ),
    inference(subsumption_resolution,[],[f7110,f2979])).

fof(f7110,plain,
    ( ~ v1_partfun1(sK3,sK2)
    | v1_xboole_0(sK2)
    | ~ spl92_6
    | ~ spl92_7
    | ~ spl92_8
    | spl92_23 ),
    inference(subsumption_resolution,[],[f7109,f2980])).

fof(f7109,plain,
    ( ~ v3_relat_2(sK3)
    | ~ v1_partfun1(sK3,sK2)
    | v1_xboole_0(sK2)
    | ~ spl92_6
    | ~ spl92_7
    | ~ spl92_8
    | spl92_23 ),
    inference(subsumption_resolution,[],[f7108,f2981])).

fof(f7108,plain,
    ( ~ v8_relat_2(sK3)
    | ~ v3_relat_2(sK3)
    | ~ v1_partfun1(sK3,sK2)
    | v1_xboole_0(sK2)
    | ~ spl92_6
    | ~ spl92_7
    | ~ spl92_8
    | spl92_23 ),
    inference(subsumption_resolution,[],[f7107,f2982])).

fof(f7107,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v8_relat_2(sK3)
    | ~ v3_relat_2(sK3)
    | ~ v1_partfun1(sK3,sK2)
    | v1_xboole_0(sK2)
    | ~ spl92_6
    | ~ spl92_7
    | ~ spl92_8
    | spl92_23 ),
    inference(subsumption_resolution,[],[f7106,f3564])).

fof(f7106,plain,
    ( ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v8_relat_2(sK3)
    | ~ v3_relat_2(sK3)
    | ~ v1_partfun1(sK3,sK2)
    | v1_xboole_0(sK2)
    | ~ spl92_7
    | ~ spl92_8
    | spl92_23 ),
    inference(subsumption_resolution,[],[f7105,f3568])).

fof(f7105,plain,
    ( ~ v1_funct_2(sK4,k2_zfmisc_1(sK2,sK2),sK2)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v8_relat_2(sK3)
    | ~ v3_relat_2(sK3)
    | ~ v1_partfun1(sK3,sK2)
    | v1_xboole_0(sK2)
    | ~ spl92_8
    | spl92_23 ),
    inference(subsumption_resolution,[],[f5107,f3572])).

fof(f5107,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK2),sK2)))
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK2,sK2),sK2)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v8_relat_2(sK3)
    | ~ v3_relat_2(sK3)
    | ~ v1_partfun1(sK3,sK2)
    | v1_xboole_0(sK2)
    | spl92_23 ),
    inference(resolution,[],[f3901,f2987])).

fof(f3901,plain,
    ( ~ v1_funct_1(k3_filter_1(sK2,sK3,sK4))
    | spl92_23 ),
    inference(avatar_component_clause,[],[f3899])).

fof(f3797,plain,
    ( ~ spl92_1
    | spl92_6 ),
    inference(avatar_split_clause,[],[f3796,f3563,f3417])).

fof(f3417,plain,
    ( spl92_1
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl92_1])])).

fof(f3796,plain,
    ( ~ v1_relat_1(sK3)
    | spl92_6 ),
    inference(subsumption_resolution,[],[f3795,f2978])).

fof(f3795,plain,
    ( ~ v1_relat_1(sK3)
    | v1_xboole_0(sK2)
    | spl92_6 ),
    inference(subsumption_resolution,[],[f3471,f3565])).

fof(f3565,plain,
    ( ~ v1_funct_1(sK4)
    | spl92_6 ),
    inference(avatar_component_clause,[],[f3563])).

fof(f3471,plain,
    ( v1_funct_1(sK4)
    | ~ v1_relat_1(sK3)
    | v1_xboole_0(sK2) ),
    inference(resolution,[],[f2983,f2994])).

fof(f2994,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(X2)
      | ~ m2_filter_1(X2,X0,X1)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f2648])).

fof(f2648,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
            & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
            & v1_funct_1(X2) )
          | ~ m2_filter_1(X2,X0,X1) )
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f2647])).

fof(f2647,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
            & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
            & v1_funct_1(X2) )
          | ~ m2_filter_1(X2,X0,X1) )
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2594])).

fof(f2594,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m2_filter_1(X2,X0,X1)
         => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
            & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
            & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_filter_1)).

fof(f3794,plain,(
    spl92_7 ),
    inference(avatar_split_clause,[],[f3793,f3567])).

fof(f3793,plain,(
    v1_funct_2(sK4,k2_zfmisc_1(sK2,sK2),sK2) ),
    inference(global_subsumption,[],[f3609,f3792])).

fof(f3792,plain,
    ( v1_funct_2(sK4,k2_zfmisc_1(sK2,sK2),sK2)
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f3472,f2978])).

fof(f3472,plain,
    ( v1_funct_2(sK4,k2_zfmisc_1(sK2,sK2),sK2)
    | ~ v1_relat_1(sK3)
    | v1_xboole_0(sK2) ),
    inference(resolution,[],[f2983,f2995])).

fof(f2995,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ m2_filter_1(X2,X0,X1)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f2648])).

fof(f3609,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f2982,f3001])).

fof(f3001,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f2655])).

fof(f2655,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1210])).

fof(f1210,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f3791,plain,(
    spl92_8 ),
    inference(avatar_split_clause,[],[f3790,f3571])).

fof(f3790,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK2),sK2))) ),
    inference(global_subsumption,[],[f3609,f3789])).

fof(f3789,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK2),sK2)))
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f3473,f2978])).

fof(f3473,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK2),sK2)))
    | ~ v1_relat_1(sK3)
    | v1_xboole_0(sK2) ),
    inference(resolution,[],[f2983,f2996])).

fof(f2996,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ m2_filter_1(X2,X0,X1)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f2648])).

fof(f3767,plain,(
    spl92_9 ),
    inference(avatar_split_clause,[],[f3766,f3575])).

fof(f3766,plain,(
    v1_funct_1(sK5) ),
    inference(global_subsumption,[],[f3609,f3765])).

fof(f3765,plain,
    ( v1_funct_1(sK5)
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f3484,f2978])).

fof(f3484,plain,
    ( v1_funct_1(sK5)
    | ~ v1_relat_1(sK3)
    | v1_xboole_0(sK2) ),
    inference(resolution,[],[f2984,f2994])).

fof(f3764,plain,(
    spl92_10 ),
    inference(avatar_split_clause,[],[f3763,f3579])).

fof(f3763,plain,(
    v1_funct_2(sK5,k2_zfmisc_1(sK2,sK2),sK2) ),
    inference(global_subsumption,[],[f3609,f3762])).

fof(f3762,plain,
    ( v1_funct_2(sK5,k2_zfmisc_1(sK2,sK2),sK2)
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f3485,f2978])).

fof(f3485,plain,
    ( v1_funct_2(sK5,k2_zfmisc_1(sK2,sK2),sK2)
    | ~ v1_relat_1(sK3)
    | v1_xboole_0(sK2) ),
    inference(resolution,[],[f2984,f2995])).

fof(f3761,plain,(
    spl92_11 ),
    inference(avatar_split_clause,[],[f3760,f3583])).

fof(f3760,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK2),sK2))) ),
    inference(global_subsumption,[],[f3609,f3759])).

fof(f3759,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK2),sK2)))
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f3486,f2978])).

fof(f3486,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK2),sK2)))
    | ~ v1_relat_1(sK3)
    | v1_xboole_0(sK2) ),
    inference(resolution,[],[f2984,f2996])).

fof(f3738,plain,(
    spl92_1 ),
    inference(avatar_split_clause,[],[f3609,f3417])).

fof(f3595,plain,
    ( ~ spl92_6
    | ~ spl92_7
    | ~ spl92_8
    | ~ spl92_9
    | ~ spl92_10
    | ~ spl92_11
    | spl92_13 ),
    inference(avatar_split_clause,[],[f3561,f3592,f3583,f3579,f3575,f3571,f3567,f3563])).

fof(f3561,plain,
    ( r5_binop_1(sK2,sK4,sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK2),sK2)))
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK2,sK2),sK2)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK2),sK2)))
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK2,sK2),sK2)
    | ~ v1_funct_1(sK4) ),
    inference(resolution,[],[f2985,f2991])).

fof(f2991,plain,(
    ! [X2,X0,X1] :
      ( r5_binop_1(X0,X1,X2)
      | ~ r6_binop_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f2806])).

fof(f2985,plain,(
    r6_binop_1(sK2,sK4,sK5) ),
    inference(cnf_transformation,[],[f2804])).

fof(f3590,plain,
    ( ~ spl92_6
    | ~ spl92_7
    | ~ spl92_8
    | ~ spl92_9
    | ~ spl92_10
    | ~ spl92_11
    | spl92_12 ),
    inference(avatar_split_clause,[],[f3560,f3587,f3583,f3579,f3575,f3571,f3567,f3563])).

fof(f3560,plain,
    ( r4_binop_1(sK2,sK4,sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK2),sK2)))
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK2,sK2),sK2)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK2),sK2)))
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK2,sK2),sK2)
    | ~ v1_funct_1(sK4) ),
    inference(resolution,[],[f2985,f2990])).

fof(f2990,plain,(
    ! [X2,X0,X1] :
      ( r4_binop_1(X0,X1,X2)
      | ~ r6_binop_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f2806])).
%------------------------------------------------------------------------------
