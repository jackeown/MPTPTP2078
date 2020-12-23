%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1409+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:53 EST 2020

% Result     : Theorem 1.41s
% Output     : Refutation 1.41s
% Verified   : 
% Statistics : Number of formulae       :  200 (1418 expanded)
%              Number of leaves         :   26 ( 625 expanded)
%              Depth                    :   72
%              Number of atoms          : 1292 (11214 expanded)
%              Number of equality atoms :   79 (1505 expanded)
%              Maximal formula depth    :   32 (   9 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f411,plain,(
    $false ),
    inference(subsumption_resolution,[],[f410,f105])).

fof(f105,plain,(
    v1_relat_1(sK1) ),
    inference(resolution,[],[f95,f70])).

fof(f70,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,
    ( k1_binop_1(k3_filter_1(sK0,sK1,sK4),k6_eqrel_1(sK0,sK0,sK1,sK2),k6_eqrel_1(sK0,sK0,sK1,sK3)) != k6_eqrel_1(sK0,sK0,sK1,k4_binop_1(sK0,sK4,sK2,sK3))
    & m2_filter_1(sK4,sK0,sK1)
    & m1_subset_1(sK3,sK0)
    & m1_subset_1(sK2,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v8_relat_2(sK1)
    & v3_relat_2(sK1)
    & v1_partfun1(sK1,sK0)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f22,f57,f56,f55,f54,f53])).

fof(f53,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( k1_binop_1(k3_filter_1(X0,X1,X4),k6_eqrel_1(X0,X0,X1,X2),k6_eqrel_1(X0,X0,X1,X3)) != k6_eqrel_1(X0,X0,X1,k4_binop_1(X0,X4,X2,X3))
                        & m2_filter_1(X4,X0,X1) )
                    & m1_subset_1(X3,X0) )
                & m1_subset_1(X2,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v8_relat_2(X1)
            & v3_relat_2(X1)
            & v1_partfun1(X1,X0) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( k1_binop_1(k3_filter_1(sK0,X1,X4),k6_eqrel_1(sK0,sK0,X1,X2),k6_eqrel_1(sK0,sK0,X1,X3)) != k6_eqrel_1(sK0,sK0,X1,k4_binop_1(sK0,X4,X2,X3))
                      & m2_filter_1(X4,sK0,X1) )
                  & m1_subset_1(X3,sK0) )
              & m1_subset_1(X2,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
          & v8_relat_2(X1)
          & v3_relat_2(X1)
          & v1_partfun1(X1,sK0) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( k1_binop_1(k3_filter_1(sK0,X1,X4),k6_eqrel_1(sK0,sK0,X1,X2),k6_eqrel_1(sK0,sK0,X1,X3)) != k6_eqrel_1(sK0,sK0,X1,k4_binop_1(sK0,X4,X2,X3))
                    & m2_filter_1(X4,sK0,X1) )
                & m1_subset_1(X3,sK0) )
            & m1_subset_1(X2,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        & v8_relat_2(X1)
        & v3_relat_2(X1)
        & v1_partfun1(X1,sK0) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( k1_binop_1(k3_filter_1(sK0,sK1,X4),k6_eqrel_1(sK0,sK0,sK1,X2),k6_eqrel_1(sK0,sK0,sK1,X3)) != k6_eqrel_1(sK0,sK0,sK1,k4_binop_1(sK0,X4,X2,X3))
                  & m2_filter_1(X4,sK0,sK1) )
              & m1_subset_1(X3,sK0) )
          & m1_subset_1(X2,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v8_relat_2(sK1)
      & v3_relat_2(sK1)
      & v1_partfun1(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( k1_binop_1(k3_filter_1(sK0,sK1,X4),k6_eqrel_1(sK0,sK0,sK1,X2),k6_eqrel_1(sK0,sK0,sK1,X3)) != k6_eqrel_1(sK0,sK0,sK1,k4_binop_1(sK0,X4,X2,X3))
                & m2_filter_1(X4,sK0,sK1) )
            & m1_subset_1(X3,sK0) )
        & m1_subset_1(X2,sK0) )
   => ( ? [X3] :
          ( ? [X4] :
              ( k1_binop_1(k3_filter_1(sK0,sK1,X4),k6_eqrel_1(sK0,sK0,sK1,sK2),k6_eqrel_1(sK0,sK0,sK1,X3)) != k6_eqrel_1(sK0,sK0,sK1,k4_binop_1(sK0,X4,sK2,X3))
              & m2_filter_1(X4,sK0,sK1) )
          & m1_subset_1(X3,sK0) )
      & m1_subset_1(sK2,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( k1_binop_1(k3_filter_1(sK0,sK1,X4),k6_eqrel_1(sK0,sK0,sK1,sK2),k6_eqrel_1(sK0,sK0,sK1,X3)) != k6_eqrel_1(sK0,sK0,sK1,k4_binop_1(sK0,X4,sK2,X3))
            & m2_filter_1(X4,sK0,sK1) )
        & m1_subset_1(X3,sK0) )
   => ( ? [X4] :
          ( k1_binop_1(k3_filter_1(sK0,sK1,X4),k6_eqrel_1(sK0,sK0,sK1,sK2),k6_eqrel_1(sK0,sK0,sK1,sK3)) != k6_eqrel_1(sK0,sK0,sK1,k4_binop_1(sK0,X4,sK2,sK3))
          & m2_filter_1(X4,sK0,sK1) )
      & m1_subset_1(sK3,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,
    ( ? [X4] :
        ( k1_binop_1(k3_filter_1(sK0,sK1,X4),k6_eqrel_1(sK0,sK0,sK1,sK2),k6_eqrel_1(sK0,sK0,sK1,sK3)) != k6_eqrel_1(sK0,sK0,sK1,k4_binop_1(sK0,X4,sK2,sK3))
        & m2_filter_1(X4,sK0,sK1) )
   => ( k1_binop_1(k3_filter_1(sK0,sK1,sK4),k6_eqrel_1(sK0,sK0,sK1,sK2),k6_eqrel_1(sK0,sK0,sK1,sK3)) != k6_eqrel_1(sK0,sK0,sK1,k4_binop_1(sK0,sK4,sK2,sK3))
      & m2_filter_1(sK4,sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( k1_binop_1(k3_filter_1(X0,X1,X4),k6_eqrel_1(X0,X0,X1,X2),k6_eqrel_1(X0,X0,X1,X3)) != k6_eqrel_1(X0,X0,X1,k4_binop_1(X0,X4,X2,X3))
                      & m2_filter_1(X4,X0,X1) )
                  & m1_subset_1(X3,X0) )
              & m1_subset_1(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v8_relat_2(X1)
          & v3_relat_2(X1)
          & v1_partfun1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( k1_binop_1(k3_filter_1(X0,X1,X4),k6_eqrel_1(X0,X0,X1,X2),k6_eqrel_1(X0,X0,X1,X3)) != k6_eqrel_1(X0,X0,X1,k4_binop_1(X0,X4,X2,X3))
                      & m2_filter_1(X4,X0,X1) )
                  & m1_subset_1(X3,X0) )
              & m1_subset_1(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v8_relat_2(X1)
          & v3_relat_2(X1)
          & v1_partfun1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v8_relat_2(X1)
              & v3_relat_2(X1)
              & v1_partfun1(X1,X0) )
           => ! [X2] :
                ( m1_subset_1(X2,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,X0)
                   => ! [X4] :
                        ( m2_filter_1(X4,X0,X1)
                       => k1_binop_1(k3_filter_1(X0,X1,X4),k6_eqrel_1(X0,X0,X1,X2),k6_eqrel_1(X0,X0,X1,X3)) = k6_eqrel_1(X0,X0,X1,k4_binop_1(X0,X4,X2,X3)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v8_relat_2(X1)
            & v3_relat_2(X1)
            & v1_partfun1(X1,X0) )
         => ! [X2] :
              ( m1_subset_1(X2,X0)
             => ! [X3] :
                  ( m1_subset_1(X3,X0)
                 => ! [X4] :
                      ( m2_filter_1(X4,X0,X1)
                     => k1_binop_1(k3_filter_1(X0,X1,X4),k6_eqrel_1(X0,X0,X1,X2),k6_eqrel_1(X0,X0,X1,X3)) = k6_eqrel_1(X0,X0,X1,k4_binop_1(X0,X4,X2,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_filter_1)).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f410,plain,(
    ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f409,f68])).

fof(f68,plain,(
    v3_relat_2(sK1) ),
    inference(cnf_transformation,[],[f58])).

fof(f409,plain,
    ( ~ v3_relat_2(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f408,f69])).

fof(f69,plain,(
    v8_relat_2(sK1) ),
    inference(cnf_transformation,[],[f58])).

fof(f408,plain,
    ( ~ v8_relat_2(sK1)
    | ~ v3_relat_2(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f407,f83])).

fof(f83,plain,(
    ! [X0] :
      ( v1_relat_2(X0)
      | ~ v8_relat_2(X0)
      | ~ v3_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_relat_2(X0)
        & v1_relat_1(X0) )
      | ~ v8_relat_2(X0)
      | ~ v3_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_relat_2(X0)
        & v1_relat_1(X0) )
      | ~ v8_relat_2(X0)
      | ~ v3_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v8_relat_2(X0)
        & v3_relat_2(X0)
        & v1_relat_1(X0) )
     => ( v1_relat_2(X0)
        & v1_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_partfun1)).

fof(f407,plain,(
    ~ v1_relat_2(sK1) ),
    inference(subsumption_resolution,[],[f406,f71])).

fof(f71,plain,(
    m1_subset_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f406,plain,
    ( ~ v1_relat_2(sK1)
    | ~ m1_subset_1(sK2,sK0) ),
    inference(subsumption_resolution,[],[f405,f66])).

fof(f66,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f405,plain,
    ( ~ v1_relat_2(sK1)
    | v1_xboole_0(sK0)
    | ~ m1_subset_1(sK2,sK0) ),
    inference(resolution,[],[f404,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f404,plain,
    ( ~ r2_hidden(sK2,sK0)
    | ~ v1_relat_2(sK1) ),
    inference(subsumption_resolution,[],[f403,f72])).

fof(f72,plain,(
    m1_subset_1(sK3,sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f403,plain,
    ( ~ v1_relat_2(sK1)
    | ~ r2_hidden(sK2,sK0)
    | ~ m1_subset_1(sK3,sK0) ),
    inference(subsumption_resolution,[],[f402,f66])).

fof(f402,plain,
    ( ~ v1_relat_2(sK1)
    | ~ r2_hidden(sK2,sK0)
    | v1_xboole_0(sK0)
    | ~ m1_subset_1(sK3,sK0) ),
    inference(resolution,[],[f401,f85])).

fof(f401,plain,
    ( ~ r2_hidden(sK3,sK0)
    | ~ v1_relat_2(sK1)
    | ~ r2_hidden(sK2,sK0) ),
    inference(subsumption_resolution,[],[f400,f105])).

fof(f400,plain,
    ( ~ v1_relat_1(sK1)
    | ~ r2_hidden(sK3,sK0)
    | ~ v1_relat_2(sK1)
    | ~ r2_hidden(sK2,sK0) ),
    inference(resolution,[],[f399,f73])).

fof(f73,plain,(
    m2_filter_1(sK4,sK0,sK1) ),
    inference(cnf_transformation,[],[f58])).

fof(f399,plain,(
    ! [X0] :
      ( ~ m2_filter_1(sK4,sK0,X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(sK3,sK0)
      | ~ v1_relat_2(sK1)
      | ~ r2_hidden(sK2,sK0) ) ),
    inference(duplicate_literal_removal,[],[f397])).

fof(f397,plain,(
    ! [X0] :
      ( ~ m2_filter_1(sK4,sK0,X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(sK3,sK0)
      | ~ v1_relat_2(sK1)
      | ~ r2_hidden(sK2,sK0)
      | ~ v1_relat_2(sK1) ) ),
    inference(resolution,[],[f395,f167])).

fof(f167,plain,(
    ! [X0] :
      ( r2_hidden(X0,k11_relat_1(sK1,X0))
      | ~ r2_hidden(X0,sK0)
      | ~ v1_relat_2(sK1) ) ),
    inference(subsumption_resolution,[],[f166,f68])).

fof(f166,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | r2_hidden(X0,k11_relat_1(sK1,X0))
      | ~ v3_relat_2(sK1)
      | ~ v1_relat_2(sK1) ) ),
    inference(subsumption_resolution,[],[f164,f67])).

fof(f67,plain,(
    v1_partfun1(sK1,sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f164,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | r2_hidden(X0,k11_relat_1(sK1,X0))
      | ~ v1_partfun1(sK1,sK0)
      | ~ v3_relat_2(sK1)
      | ~ v1_relat_2(sK1) ) ),
    inference(resolution,[],[f163,f70])).

fof(f163,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ r2_hidden(X2,X0)
      | r2_hidden(X2,k11_relat_1(X1,X2))
      | ~ v1_partfun1(X1,X0)
      | ~ v3_relat_2(X1)
      | ~ v1_relat_2(X1) ) ),
    inference(duplicate_literal_removal,[],[f162])).

fof(f162,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k11_relat_1(X1,X2))
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v3_relat_2(X1)
      | ~ v1_relat_2(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(superposition,[],[f91,f102])).

fof(f102,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_eqrel_1(X0,X1,X2,X3) = k11_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2,X3] :
      ( k6_eqrel_1(X0,X1,X2,X3) = k11_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k6_eqrel_1(X0,X1,X2,X3) = k11_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_eqrel_1)).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k6_eqrel_1(X0,X0,X1,X2))
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v3_relat_2(X1)
      | ~ v1_relat_2(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,k6_eqrel_1(X0,X0,X1,X2))
          | ~ r2_hidden(X2,X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v3_relat_2(X1)
      | ~ v1_relat_2(X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,k6_eqrel_1(X0,X0,X1,X2))
          | ~ r2_hidden(X2,X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v3_relat_2(X1)
      | ~ v1_relat_2(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_partfun1(X1,X0)
        & v3_relat_2(X1)
        & v1_relat_2(X1) )
     => ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,k6_eqrel_1(X0,X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_eqrel_1)).

fof(f395,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2,k11_relat_1(sK1,sK2))
      | ~ m2_filter_1(sK4,sK0,X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(sK3,sK0)
      | ~ v1_relat_2(sK1) ) ),
    inference(resolution,[],[f394,f167])).

fof(f394,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3,k11_relat_1(sK1,sK3))
      | ~ v1_relat_1(X0)
      | ~ m2_filter_1(sK4,sK0,X0)
      | ~ r2_hidden(sK2,k11_relat_1(sK1,sK2)) ) ),
    inference(subsumption_resolution,[],[f393,f66])).

fof(f393,plain,(
    ! [X0] :
      ( ~ m2_filter_1(sK4,sK0,X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(sK3,k11_relat_1(sK1,sK3))
      | ~ r2_hidden(sK2,k11_relat_1(sK1,sK2))
      | v1_xboole_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f392])).

fof(f392,plain,(
    ! [X0] :
      ( ~ m2_filter_1(sK4,sK0,X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(sK3,k11_relat_1(sK1,sK3))
      | ~ r2_hidden(sK2,k11_relat_1(sK1,sK2))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(sK0) ) ),
    inference(condensation,[],[f391])).

fof(f391,plain,(
    ! [X0,X1] :
      ( ~ m2_filter_1(sK4,sK0,X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(sK3,k11_relat_1(sK1,sK3))
      | ~ r2_hidden(sK2,k11_relat_1(sK1,sK2))
      | ~ m2_filter_1(sK4,sK0,X1)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f390,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ m2_filter_1(X2,X0,X1)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
            & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
            & v1_funct_1(X2) )
          | ~ m2_filter_1(X2,X0,X1) )
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
            & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
            & v1_funct_1(X2) )
          | ~ m2_filter_1(X2,X0,X1) )
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m2_filter_1(X2,X0,X1)
         => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
            & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
            & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_filter_1)).

fof(f390,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ m2_filter_1(sK4,sK0,X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(sK3,k11_relat_1(sK1,sK3))
      | ~ r2_hidden(sK2,k11_relat_1(sK1,sK2)) ) ),
    inference(subsumption_resolution,[],[f389,f158])).

fof(f158,plain,(
    ~ v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f157,f68])).

fof(f157,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ v3_relat_2(sK1) ),
    inference(subsumption_resolution,[],[f156,f69])).

fof(f156,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ v8_relat_2(sK1)
    | ~ v3_relat_2(sK1) ),
    inference(subsumption_resolution,[],[f155,f67])).

fof(f155,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ v1_partfun1(sK1,sK0)
    | ~ v8_relat_2(sK1)
    | ~ v3_relat_2(sK1) ),
    inference(subsumption_resolution,[],[f154,f70])).

fof(f154,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_partfun1(sK1,sK0)
    | ~ v8_relat_2(sK1)
    | ~ v3_relat_2(sK1) ),
    inference(subsumption_resolution,[],[f153,f134])).

fof(f134,plain,(
    ~ v1_xboole_0(k8_eqrel_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f133,f66])).

fof(f133,plain,
    ( ~ v1_xboole_0(k8_eqrel_1(sK0,sK1))
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f132,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ m1_eqrel_1(X1,X0)
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_xboole_0(X1)
          | ~ m1_eqrel_1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_eqrel_1(X1,X0)
         => ~ v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_eqrel_1)).

fof(f132,plain,(
    m1_eqrel_1(k8_eqrel_1(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f131,f68])).

fof(f131,plain,
    ( m1_eqrel_1(k8_eqrel_1(sK0,sK1),sK0)
    | ~ v3_relat_2(sK1) ),
    inference(subsumption_resolution,[],[f130,f69])).

fof(f130,plain,
    ( m1_eqrel_1(k8_eqrel_1(sK0,sK1),sK0)
    | ~ v8_relat_2(sK1)
    | ~ v3_relat_2(sK1) ),
    inference(subsumption_resolution,[],[f128,f67])).

fof(f128,plain,
    ( m1_eqrel_1(k8_eqrel_1(sK0,sK1),sK0)
    | ~ v1_partfun1(sK1,sK0)
    | ~ v8_relat_2(sK1)
    | ~ v3_relat_2(sK1) ),
    inference(resolution,[],[f92,f70])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | m1_eqrel_1(k8_eqrel_1(X0,X1),X0)
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_eqrel_1(k8_eqrel_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_eqrel_1(k8_eqrel_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_partfun1(X1,X0)
        & v8_relat_2(X1)
        & v3_relat_2(X1) )
     => m1_eqrel_1(k8_eqrel_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_eqrel_1)).

fof(f153,plain,
    ( v1_xboole_0(k8_eqrel_1(sK0,sK1))
    | ~ v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_partfun1(sK1,sK0)
    | ~ v8_relat_2(sK1)
    | ~ v3_relat_2(sK1) ),
    inference(superposition,[],[f146,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( k8_eqrel_1(X0,X1) = k7_eqrel_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k8_eqrel_1(X0,X1) = k7_eqrel_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k8_eqrel_1(X0,X1) = k7_eqrel_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_partfun1(X1,X0)
        & v8_relat_2(X1)
        & v3_relat_2(X1) )
     => k8_eqrel_1(X0,X1) = k7_eqrel_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_eqrel_1)).

fof(f146,plain,
    ( v1_xboole_0(k7_eqrel_1(sK0,sK1))
    | ~ v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f144,f84])).

fof(f84,plain,(
    ! [X0] : m1_subset_1(sK9(X0),X0) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0] : m1_subset_1(sK9(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f10,f63])).

fof(f63,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK9(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f10,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f144,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k7_eqrel_1(sK0,sK1))
      | v1_xboole_0(k7_eqrel_1(sK0,sK1))
      | ~ v1_xboole_0(k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f143,f85])).

fof(f143,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k7_eqrel_1(sK0,sK1))
      | ~ v1_xboole_0(k1_zfmisc_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f142,f68])).

fof(f142,plain,(
    ! [X0] :
      ( ~ v3_relat_2(sK1)
      | ~ v1_xboole_0(k1_zfmisc_1(sK0))
      | ~ r2_hidden(X0,k7_eqrel_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f141,f69])).

fof(f141,plain,(
    ! [X0] :
      ( ~ v8_relat_2(sK1)
      | ~ v3_relat_2(sK1)
      | ~ v1_xboole_0(k1_zfmisc_1(sK0))
      | ~ r2_hidden(X0,k7_eqrel_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f139,f67])).

fof(f139,plain,(
    ! [X0] :
      ( ~ v1_partfun1(sK1,sK0)
      | ~ v8_relat_2(sK1)
      | ~ v3_relat_2(sK1)
      | ~ v1_xboole_0(k1_zfmisc_1(sK0))
      | ~ r2_hidden(X0,k7_eqrel_1(sK0,sK1)) ) ),
    inference(resolution,[],[f135,f70])).

fof(f135,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
      | ~ v1_partfun1(X0,X1)
      | ~ v8_relat_2(X0)
      | ~ v3_relat_2(X0)
      | ~ v1_xboole_0(k1_zfmisc_1(X1))
      | ~ r2_hidden(X2,k7_eqrel_1(X1,X0)) ) ),
    inference(resolution,[],[f94,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f94,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_eqrel_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_eqrel_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_eqrel_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_partfun1(X1,X0)
        & v8_relat_2(X1)
        & v3_relat_2(X1) )
     => m1_subset_1(k7_eqrel_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_eqrel_1)).

fof(f389,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ m2_filter_1(sK4,sK0,X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(sK3,k11_relat_1(sK1,sK3))
      | ~ r2_hidden(sK2,k11_relat_1(sK1,sK2))
      | v1_xboole_0(k1_zfmisc_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f388,f134])).

fof(f388,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ m2_filter_1(sK4,sK0,X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(sK3,k11_relat_1(sK1,sK3))
      | ~ r2_hidden(sK2,k11_relat_1(sK1,sK2))
      | v1_xboole_0(k8_eqrel_1(sK0,sK1))
      | v1_xboole_0(k1_zfmisc_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f387,f71])).

fof(f387,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ m2_filter_1(sK4,sK0,X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(sK3,k11_relat_1(sK1,sK3))
      | ~ r2_hidden(sK2,k11_relat_1(sK1,sK2))
      | ~ m1_subset_1(sK2,sK0)
      | v1_xboole_0(k8_eqrel_1(sK0,sK1))
      | v1_xboole_0(k1_zfmisc_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f386,f66])).

fof(f386,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ m2_filter_1(sK4,sK0,X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(sK3,k11_relat_1(sK1,sK3))
      | ~ r2_hidden(sK2,k11_relat_1(sK1,sK2))
      | v1_xboole_0(sK0)
      | ~ m1_subset_1(sK2,sK0)
      | v1_xboole_0(k8_eqrel_1(sK0,sK1))
      | v1_xboole_0(k1_zfmisc_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f385,f68])).

fof(f385,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ m2_filter_1(sK4,sK0,X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(sK3,k11_relat_1(sK1,sK3))
      | ~ r2_hidden(sK2,k11_relat_1(sK1,sK2))
      | ~ v3_relat_2(sK1)
      | v1_xboole_0(sK0)
      | ~ m1_subset_1(sK2,sK0)
      | v1_xboole_0(k8_eqrel_1(sK0,sK1))
      | v1_xboole_0(k1_zfmisc_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f384,f69])).

fof(f384,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ m2_filter_1(sK4,sK0,X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(sK3,k11_relat_1(sK1,sK3))
      | ~ r2_hidden(sK2,k11_relat_1(sK1,sK2))
      | ~ v8_relat_2(sK1)
      | ~ v3_relat_2(sK1)
      | v1_xboole_0(sK0)
      | ~ m1_subset_1(sK2,sK0)
      | v1_xboole_0(k8_eqrel_1(sK0,sK1))
      | v1_xboole_0(k1_zfmisc_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f383,f67])).

fof(f383,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ m2_filter_1(sK4,sK0,X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(sK3,k11_relat_1(sK1,sK3))
      | ~ r2_hidden(sK2,k11_relat_1(sK1,sK2))
      | ~ v1_partfun1(sK1,sK0)
      | ~ v8_relat_2(sK1)
      | ~ v3_relat_2(sK1)
      | v1_xboole_0(sK0)
      | ~ m1_subset_1(sK2,sK0)
      | v1_xboole_0(k8_eqrel_1(sK0,sK1))
      | v1_xboole_0(k1_zfmisc_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f382,f70])).

fof(f382,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ m2_filter_1(sK4,sK0,X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(sK3,k11_relat_1(sK1,sK3))
      | ~ r2_hidden(sK2,k11_relat_1(sK1,sK2))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ v1_partfun1(sK1,sK0)
      | ~ v8_relat_2(sK1)
      | ~ v3_relat_2(sK1)
      | v1_xboole_0(sK0)
      | ~ m1_subset_1(sK2,sK0)
      | v1_xboole_0(k8_eqrel_1(sK0,sK1))
      | v1_xboole_0(k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f381,f173])).

fof(f173,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k11_relat_1(X2,X0),k8_eqrel_1(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
      | ~ v1_partfun1(X2,X1)
      | ~ v8_relat_2(X2)
      | ~ v3_relat_2(X2)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1)
      | v1_xboole_0(k8_eqrel_1(X1,X2))
      | v1_xboole_0(k1_zfmisc_1(X1)) ) ),
    inference(subsumption_resolution,[],[f172,f137])).

fof(f137,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_eqrel_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1) ) ),
    inference(duplicate_literal_removal,[],[f136])).

fof(f136,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_eqrel_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1) ) ),
    inference(superposition,[],[f94,f93])).

fof(f172,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
      | ~ v1_partfun1(X2,X1)
      | ~ v8_relat_2(X2)
      | ~ v3_relat_2(X2)
      | v1_xboole_0(X1)
      | m1_subset_1(k11_relat_1(X2,X0),k8_eqrel_1(X1,X2))
      | ~ m1_subset_1(k8_eqrel_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1)))
      | v1_xboole_0(k8_eqrel_1(X1,X2))
      | v1_xboole_0(k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f170,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ m2_subset_1(X2,X0,X1)
      | m1_subset_1(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m2_subset_1(X2,X0,X1)
            | ~ m1_subset_1(X2,X1) )
          & ( m1_subset_1(X2,X1)
            | ~ m2_subset_1(X2,X0,X1) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m2_subset_1(X2,X0,X1)
        <=> m1_subset_1(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m2_subset_1(X2,X0,X1)
        <=> m1_subset_1(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X0))
        & ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m2_subset_1(X2,X0,X1)
        <=> m1_subset_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_m2_subset_1)).

fof(f170,plain,(
    ! [X2,X0,X1] :
      ( m2_subset_1(k11_relat_1(X1,X2),k1_zfmisc_1(X0),k8_eqrel_1(X0,X1))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | v1_xboole_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f169])).

fof(f169,plain,(
    ! [X2,X0,X1] :
      ( m2_subset_1(k11_relat_1(X1,X2),k1_zfmisc_1(X0),k8_eqrel_1(X0,X1))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | v1_xboole_0(X0) ) ),
    inference(superposition,[],[f97,f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( k9_eqrel_1(X0,X1,X2) = k11_relat_1(X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( k9_eqrel_1(X0,X1,X2) = k11_relat_1(X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( k9_eqrel_1(X0,X1,X2) = k11_relat_1(X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,X0)
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_partfun1(X1,X0)
        & v8_relat_2(X1)
        & v3_relat_2(X1)
        & ~ v1_xboole_0(X0) )
     => k9_eqrel_1(X0,X1,X2) = k11_relat_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_eqrel_1)).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( m2_subset_1(k9_eqrel_1(X0,X1,X2),k1_zfmisc_1(X0),k8_eqrel_1(X0,X1))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( m2_subset_1(k9_eqrel_1(X0,X1,X2),k1_zfmisc_1(X0),k8_eqrel_1(X0,X1))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( m2_subset_1(k9_eqrel_1(X0,X1,X2),k1_zfmisc_1(X0),k8_eqrel_1(X0,X1))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,X0)
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_partfun1(X1,X0)
        & v8_relat_2(X1)
        & v3_relat_2(X1)
        & ~ v1_xboole_0(X0) )
     => m2_subset_1(k9_eqrel_1(X0,X1,X2),k1_zfmisc_1(X0),k8_eqrel_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_eqrel_1)).

fof(f381,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k11_relat_1(sK1,sK2),k8_eqrel_1(sK0,sK1))
      | ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ m2_filter_1(sK4,sK0,X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(sK3,k11_relat_1(sK1,sK3))
      | ~ r2_hidden(sK2,k11_relat_1(sK1,sK2)) ) ),
    inference(subsumption_resolution,[],[f380,f158])).

fof(f380,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2,k11_relat_1(sK1,sK2))
      | ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ m2_filter_1(sK4,sK0,X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(sK3,k11_relat_1(sK1,sK3))
      | ~ m1_subset_1(k11_relat_1(sK1,sK2),k8_eqrel_1(sK0,sK1))
      | v1_xboole_0(k1_zfmisc_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f379,f134])).

fof(f379,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2,k11_relat_1(sK1,sK2))
      | ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ m2_filter_1(sK4,sK0,X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(sK3,k11_relat_1(sK1,sK3))
      | ~ m1_subset_1(k11_relat_1(sK1,sK2),k8_eqrel_1(sK0,sK1))
      | v1_xboole_0(k8_eqrel_1(sK0,sK1))
      | v1_xboole_0(k1_zfmisc_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f378,f72])).

fof(f378,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2,k11_relat_1(sK1,sK2))
      | ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ m2_filter_1(sK4,sK0,X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(sK3,k11_relat_1(sK1,sK3))
      | ~ m1_subset_1(k11_relat_1(sK1,sK2),k8_eqrel_1(sK0,sK1))
      | ~ m1_subset_1(sK3,sK0)
      | v1_xboole_0(k8_eqrel_1(sK0,sK1))
      | v1_xboole_0(k1_zfmisc_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f377,f66])).

fof(f377,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2,k11_relat_1(sK1,sK2))
      | ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ m2_filter_1(sK4,sK0,X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(sK3,k11_relat_1(sK1,sK3))
      | ~ m1_subset_1(k11_relat_1(sK1,sK2),k8_eqrel_1(sK0,sK1))
      | v1_xboole_0(sK0)
      | ~ m1_subset_1(sK3,sK0)
      | v1_xboole_0(k8_eqrel_1(sK0,sK1))
      | v1_xboole_0(k1_zfmisc_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f376,f68])).

fof(f376,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2,k11_relat_1(sK1,sK2))
      | ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ m2_filter_1(sK4,sK0,X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(sK3,k11_relat_1(sK1,sK3))
      | ~ m1_subset_1(k11_relat_1(sK1,sK2),k8_eqrel_1(sK0,sK1))
      | ~ v3_relat_2(sK1)
      | v1_xboole_0(sK0)
      | ~ m1_subset_1(sK3,sK0)
      | v1_xboole_0(k8_eqrel_1(sK0,sK1))
      | v1_xboole_0(k1_zfmisc_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f375,f69])).

fof(f375,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2,k11_relat_1(sK1,sK2))
      | ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ m2_filter_1(sK4,sK0,X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(sK3,k11_relat_1(sK1,sK3))
      | ~ m1_subset_1(k11_relat_1(sK1,sK2),k8_eqrel_1(sK0,sK1))
      | ~ v8_relat_2(sK1)
      | ~ v3_relat_2(sK1)
      | v1_xboole_0(sK0)
      | ~ m1_subset_1(sK3,sK0)
      | v1_xboole_0(k8_eqrel_1(sK0,sK1))
      | v1_xboole_0(k1_zfmisc_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f374,f67])).

fof(f374,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2,k11_relat_1(sK1,sK2))
      | ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ m2_filter_1(sK4,sK0,X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(sK3,k11_relat_1(sK1,sK3))
      | ~ m1_subset_1(k11_relat_1(sK1,sK2),k8_eqrel_1(sK0,sK1))
      | ~ v1_partfun1(sK1,sK0)
      | ~ v8_relat_2(sK1)
      | ~ v3_relat_2(sK1)
      | v1_xboole_0(sK0)
      | ~ m1_subset_1(sK3,sK0)
      | v1_xboole_0(k8_eqrel_1(sK0,sK1))
      | v1_xboole_0(k1_zfmisc_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f373,f70])).

fof(f373,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2,k11_relat_1(sK1,sK2))
      | ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ m2_filter_1(sK4,sK0,X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(sK3,k11_relat_1(sK1,sK3))
      | ~ m1_subset_1(k11_relat_1(sK1,sK2),k8_eqrel_1(sK0,sK1))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ v1_partfun1(sK1,sK0)
      | ~ v8_relat_2(sK1)
      | ~ v3_relat_2(sK1)
      | v1_xboole_0(sK0)
      | ~ m1_subset_1(sK3,sK0)
      | v1_xboole_0(k8_eqrel_1(sK0,sK1))
      | v1_xboole_0(k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f372,f173])).

fof(f372,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k11_relat_1(sK1,sK3),k8_eqrel_1(sK0,sK1))
      | ~ r2_hidden(sK2,k11_relat_1(sK1,sK2))
      | ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ m2_filter_1(sK4,sK0,X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(sK3,k11_relat_1(sK1,sK3))
      | ~ m1_subset_1(k11_relat_1(sK1,sK2),k8_eqrel_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f371,f134])).

fof(f371,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3,k11_relat_1(sK1,sK3))
      | ~ r2_hidden(sK2,k11_relat_1(sK1,sK2))
      | ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ m2_filter_1(sK4,sK0,X0)
      | ~ v1_relat_1(X0)
      | ~ m1_subset_1(k11_relat_1(sK1,sK3),k8_eqrel_1(sK0,sK1))
      | v1_xboole_0(k8_eqrel_1(sK0,sK1))
      | ~ m1_subset_1(k11_relat_1(sK1,sK2),k8_eqrel_1(sK0,sK1)) ) ),
    inference(resolution,[],[f369,f85])).

fof(f369,plain,(
    ! [X0] :
      ( ~ r2_hidden(k11_relat_1(sK1,sK2),k8_eqrel_1(sK0,sK1))
      | ~ r2_hidden(sK3,k11_relat_1(sK1,sK3))
      | ~ r2_hidden(sK2,k11_relat_1(sK1,sK2))
      | ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ m2_filter_1(sK4,sK0,X0)
      | ~ v1_relat_1(X0)
      | ~ m1_subset_1(k11_relat_1(sK1,sK3),k8_eqrel_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f368,f134])).

fof(f368,plain,(
    ! [X0] :
      ( ~ r2_hidden(k11_relat_1(sK1,sK2),k8_eqrel_1(sK0,sK1))
      | ~ r2_hidden(sK3,k11_relat_1(sK1,sK3))
      | ~ r2_hidden(sK2,k11_relat_1(sK1,sK2))
      | ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ m2_filter_1(sK4,sK0,X0)
      | ~ v1_relat_1(X0)
      | v1_xboole_0(k8_eqrel_1(sK0,sK1))
      | ~ m1_subset_1(k11_relat_1(sK1,sK3),k8_eqrel_1(sK0,sK1)) ) ),
    inference(resolution,[],[f367,f85])).

fof(f367,plain,(
    ! [X0] :
      ( ~ r2_hidden(k11_relat_1(sK1,sK3),k8_eqrel_1(sK0,sK1))
      | ~ r2_hidden(k11_relat_1(sK1,sK2),k8_eqrel_1(sK0,sK1))
      | ~ r2_hidden(sK3,k11_relat_1(sK1,sK3))
      | ~ r2_hidden(sK2,k11_relat_1(sK1,sK2))
      | ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ m2_filter_1(sK4,sK0,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f366,f66])).

fof(f366,plain,(
    ! [X0] :
      ( ~ r2_hidden(k11_relat_1(sK1,sK3),k8_eqrel_1(sK0,sK1))
      | ~ r2_hidden(k11_relat_1(sK1,sK2),k8_eqrel_1(sK0,sK1))
      | ~ r2_hidden(sK3,k11_relat_1(sK1,sK3))
      | ~ r2_hidden(sK2,k11_relat_1(sK1,sK2))
      | ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ m2_filter_1(sK4,sK0,X0)
      | ~ v1_relat_1(X0)
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f365,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ m2_filter_1(X2,X0,X1)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f365,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ r2_hidden(k11_relat_1(sK1,sK3),k8_eqrel_1(sK0,sK1))
    | ~ r2_hidden(k11_relat_1(sK1,sK2),k8_eqrel_1(sK0,sK1))
    | ~ r2_hidden(sK3,k11_relat_1(sK1,sK3))
    | ~ r2_hidden(sK2,k11_relat_1(sK1,sK2))
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0) ),
    inference(equality_resolution,[],[f364])).

fof(f364,plain,(
    ! [X0,X1] :
      ( k11_relat_1(sK1,k1_binop_1(sK4,X0,X1)) != k11_relat_1(sK1,k1_binop_1(sK4,sK2,sK3))
      | ~ r2_hidden(X0,k11_relat_1(sK1,sK2))
      | ~ r2_hidden(k11_relat_1(sK1,sK3),k8_eqrel_1(sK0,sK1))
      | ~ r2_hidden(k11_relat_1(sK1,sK2),k8_eqrel_1(sK0,sK1))
      | ~ r2_hidden(X1,k11_relat_1(sK1,sK3))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
      | ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0) ) ),
    inference(subsumption_resolution,[],[f363,f111])).

fof(f111,plain,(
    v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f110,f66])).

fof(f110,plain,
    ( v1_funct_1(sK4)
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f109,f105])).

fof(f109,plain,
    ( v1_funct_1(sK4)
    | ~ v1_relat_1(sK1)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f88,f73])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ m2_filter_1(X2,X0,X1)
      | v1_funct_1(X2)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f363,plain,(
    ! [X0,X1] :
      ( k11_relat_1(sK1,k1_binop_1(sK4,X0,X1)) != k11_relat_1(sK1,k1_binop_1(sK4,sK2,sK3))
      | ~ r2_hidden(X0,k11_relat_1(sK1,sK2))
      | ~ r2_hidden(k11_relat_1(sK1,sK3),k8_eqrel_1(sK0,sK1))
      | ~ r2_hidden(k11_relat_1(sK1,sK2),k8_eqrel_1(sK0,sK1))
      | ~ r2_hidden(X1,k11_relat_1(sK1,sK3))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
      | ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ v1_funct_1(sK4) ) ),
    inference(subsumption_resolution,[],[f362,f71])).

fof(f362,plain,(
    ! [X0,X1] :
      ( k11_relat_1(sK1,k1_binop_1(sK4,X0,X1)) != k11_relat_1(sK1,k1_binop_1(sK4,sK2,sK3))
      | ~ r2_hidden(X0,k11_relat_1(sK1,sK2))
      | ~ r2_hidden(k11_relat_1(sK1,sK3),k8_eqrel_1(sK0,sK1))
      | ~ r2_hidden(k11_relat_1(sK1,sK2),k8_eqrel_1(sK0,sK1))
      | ~ r2_hidden(X1,k11_relat_1(sK1,sK3))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
      | ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ m1_subset_1(sK2,sK0)
      | ~ v1_funct_1(sK4) ) ),
    inference(subsumption_resolution,[],[f361,f72])).

fof(f361,plain,(
    ! [X0,X1] :
      ( k11_relat_1(sK1,k1_binop_1(sK4,X0,X1)) != k11_relat_1(sK1,k1_binop_1(sK4,sK2,sK3))
      | ~ r2_hidden(X0,k11_relat_1(sK1,sK2))
      | ~ r2_hidden(k11_relat_1(sK1,sK3),k8_eqrel_1(sK0,sK1))
      | ~ r2_hidden(k11_relat_1(sK1,sK2),k8_eqrel_1(sK0,sK1))
      | ~ r2_hidden(X1,k11_relat_1(sK1,sK3))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
      | ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ m1_subset_1(sK3,sK0)
      | ~ m1_subset_1(sK2,sK0)
      | ~ v1_funct_1(sK4) ) ),
    inference(duplicate_literal_removal,[],[f360])).

fof(f360,plain,(
    ! [X0,X1] :
      ( k11_relat_1(sK1,k1_binop_1(sK4,X0,X1)) != k11_relat_1(sK1,k1_binop_1(sK4,sK2,sK3))
      | ~ r2_hidden(X0,k11_relat_1(sK1,sK2))
      | ~ r2_hidden(k11_relat_1(sK1,sK3),k8_eqrel_1(sK0,sK1))
      | ~ r2_hidden(k11_relat_1(sK1,sK2),k8_eqrel_1(sK0,sK1))
      | ~ r2_hidden(X1,k11_relat_1(sK1,sK3))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
      | ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ m1_subset_1(sK3,sK0)
      | ~ m1_subset_1(sK2,sK0)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
      | ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ v1_funct_1(sK4) ) ),
    inference(superposition,[],[f352,f103])).

fof(f103,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_binop_1(X0,X1,X2,X3) = k1_binop_1(X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2,X3] :
      ( k4_binop_1(X0,X1,X2,X3) = k1_binop_1(X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2,X3] :
      ( k4_binop_1(X0,X1,X2,X3) = k1_binop_1(X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,X0)
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
        & v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
        & v1_funct_1(X1) )
     => k4_binop_1(X0,X1,X2,X3) = k1_binop_1(X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_binop_1)).

fof(f352,plain,(
    ! [X0,X1] :
      ( k11_relat_1(sK1,k4_binop_1(sK0,sK4,sK2,sK3)) != k11_relat_1(sK1,k1_binop_1(sK4,X0,X1))
      | ~ r2_hidden(X0,k11_relat_1(sK1,sK2))
      | ~ r2_hidden(k11_relat_1(sK1,sK3),k8_eqrel_1(sK0,sK1))
      | ~ r2_hidden(k11_relat_1(sK1,sK2),k8_eqrel_1(sK0,sK1))
      | ~ r2_hidden(X1,k11_relat_1(sK1,sK3))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
      | ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0) ) ),
    inference(subsumption_resolution,[],[f349,f70])).

fof(f349,plain,(
    ! [X0,X1] :
      ( k11_relat_1(sK1,k4_binop_1(sK0,sK4,sK2,sK3)) != k11_relat_1(sK1,k1_binop_1(sK4,X0,X1))
      | ~ r2_hidden(X0,k11_relat_1(sK1,sK2))
      | ~ r2_hidden(k11_relat_1(sK1,sK3),k8_eqrel_1(sK0,sK1))
      | ~ r2_hidden(k11_relat_1(sK1,sK2),k8_eqrel_1(sK0,sK1))
      | ~ r2_hidden(X1,k11_relat_1(sK1,sK3))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
      | ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ) ),
    inference(superposition,[],[f340,f102])).

fof(f340,plain,(
    ! [X0,X1] :
      ( k6_eqrel_1(sK0,sK0,sK1,k1_binop_1(sK4,X0,X1)) != k11_relat_1(sK1,k4_binop_1(sK0,sK4,sK2,sK3))
      | ~ r2_hidden(X0,k11_relat_1(sK1,sK2))
      | ~ r2_hidden(k11_relat_1(sK1,sK3),k8_eqrel_1(sK0,sK1))
      | ~ r2_hidden(k11_relat_1(sK1,sK2),k8_eqrel_1(sK0,sK1))
      | ~ r2_hidden(X1,k11_relat_1(sK1,sK3))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
      | ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0) ) ),
    inference(subsumption_resolution,[],[f332,f70])).

fof(f332,plain,(
    ! [X0,X1] :
      ( k6_eqrel_1(sK0,sK0,sK1,k1_binop_1(sK4,X0,X1)) != k11_relat_1(sK1,k4_binop_1(sK0,sK4,sK2,sK3))
      | ~ r2_hidden(X0,k11_relat_1(sK1,sK2))
      | ~ r2_hidden(k11_relat_1(sK1,sK3),k8_eqrel_1(sK0,sK1))
      | ~ r2_hidden(k11_relat_1(sK1,sK2),k8_eqrel_1(sK0,sK1))
      | ~ r2_hidden(X1,k11_relat_1(sK1,sK3))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
      | ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ) ),
    inference(superposition,[],[f319,f102])).

fof(f319,plain,(
    ! [X4,X5] :
      ( k6_eqrel_1(sK0,sK0,sK1,k4_binop_1(sK0,sK4,sK2,sK3)) != k6_eqrel_1(sK0,sK0,sK1,k1_binop_1(sK4,X4,X5))
      | ~ r2_hidden(X4,k11_relat_1(sK1,sK2))
      | ~ r2_hidden(k11_relat_1(sK1,sK3),k8_eqrel_1(sK0,sK1))
      | ~ r2_hidden(k11_relat_1(sK1,sK2),k8_eqrel_1(sK0,sK1))
      | ~ r2_hidden(X5,k11_relat_1(sK1,sK3))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
      | ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0) ) ),
    inference(subsumption_resolution,[],[f318,f66])).

fof(f318,plain,(
    ! [X4,X5] :
      ( k6_eqrel_1(sK0,sK0,sK1,k4_binop_1(sK0,sK4,sK2,sK3)) != k6_eqrel_1(sK0,sK0,sK1,k1_binop_1(sK4,X4,X5))
      | ~ r2_hidden(X4,k11_relat_1(sK1,sK2))
      | ~ r2_hidden(k11_relat_1(sK1,sK3),k8_eqrel_1(sK0,sK1))
      | ~ r2_hidden(k11_relat_1(sK1,sK2),k8_eqrel_1(sK0,sK1))
      | ~ r2_hidden(X5,k11_relat_1(sK1,sK3))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
      | ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
      | v1_xboole_0(sK0) ) ),
    inference(subsumption_resolution,[],[f317,f67])).

fof(f317,plain,(
    ! [X4,X5] :
      ( k6_eqrel_1(sK0,sK0,sK1,k4_binop_1(sK0,sK4,sK2,sK3)) != k6_eqrel_1(sK0,sK0,sK1,k1_binop_1(sK4,X4,X5))
      | ~ r2_hidden(X4,k11_relat_1(sK1,sK2))
      | ~ r2_hidden(k11_relat_1(sK1,sK3),k8_eqrel_1(sK0,sK1))
      | ~ r2_hidden(k11_relat_1(sK1,sK2),k8_eqrel_1(sK0,sK1))
      | ~ r2_hidden(X5,k11_relat_1(sK1,sK3))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
      | ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ v1_partfun1(sK1,sK0)
      | v1_xboole_0(sK0) ) ),
    inference(subsumption_resolution,[],[f316,f68])).

fof(f316,plain,(
    ! [X4,X5] :
      ( k6_eqrel_1(sK0,sK0,sK1,k4_binop_1(sK0,sK4,sK2,sK3)) != k6_eqrel_1(sK0,sK0,sK1,k1_binop_1(sK4,X4,X5))
      | ~ r2_hidden(X4,k11_relat_1(sK1,sK2))
      | ~ r2_hidden(k11_relat_1(sK1,sK3),k8_eqrel_1(sK0,sK1))
      | ~ r2_hidden(k11_relat_1(sK1,sK2),k8_eqrel_1(sK0,sK1))
      | ~ r2_hidden(X5,k11_relat_1(sK1,sK3))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
      | ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ v3_relat_2(sK1)
      | ~ v1_partfun1(sK1,sK0)
      | v1_xboole_0(sK0) ) ),
    inference(subsumption_resolution,[],[f315,f69])).

fof(f315,plain,(
    ! [X4,X5] :
      ( k6_eqrel_1(sK0,sK0,sK1,k4_binop_1(sK0,sK4,sK2,sK3)) != k6_eqrel_1(sK0,sK0,sK1,k1_binop_1(sK4,X4,X5))
      | ~ r2_hidden(X4,k11_relat_1(sK1,sK2))
      | ~ r2_hidden(k11_relat_1(sK1,sK3),k8_eqrel_1(sK0,sK1))
      | ~ r2_hidden(k11_relat_1(sK1,sK2),k8_eqrel_1(sK0,sK1))
      | ~ r2_hidden(X5,k11_relat_1(sK1,sK3))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
      | ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ v8_relat_2(sK1)
      | ~ v3_relat_2(sK1)
      | ~ v1_partfun1(sK1,sK0)
      | v1_xboole_0(sK0) ) ),
    inference(subsumption_resolution,[],[f314,f70])).

fof(f314,plain,(
    ! [X4,X5] :
      ( k6_eqrel_1(sK0,sK0,sK1,k4_binop_1(sK0,sK4,sK2,sK3)) != k6_eqrel_1(sK0,sK0,sK1,k1_binop_1(sK4,X4,X5))
      | ~ r2_hidden(X4,k11_relat_1(sK1,sK2))
      | ~ r2_hidden(k11_relat_1(sK1,sK3),k8_eqrel_1(sK0,sK1))
      | ~ r2_hidden(k11_relat_1(sK1,sK2),k8_eqrel_1(sK0,sK1))
      | ~ r2_hidden(X5,k11_relat_1(sK1,sK3))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
      | ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ v8_relat_2(sK1)
      | ~ v3_relat_2(sK1)
      | ~ v1_partfun1(sK1,sK0)
      | v1_xboole_0(sK0) ) ),
    inference(subsumption_resolution,[],[f313,f111])).

fof(f313,plain,(
    ! [X4,X5] :
      ( k6_eqrel_1(sK0,sK0,sK1,k4_binop_1(sK0,sK4,sK2,sK3)) != k6_eqrel_1(sK0,sK0,sK1,k1_binop_1(sK4,X4,X5))
      | ~ r2_hidden(X4,k11_relat_1(sK1,sK2))
      | ~ r2_hidden(k11_relat_1(sK1,sK3),k8_eqrel_1(sK0,sK1))
      | ~ r2_hidden(k11_relat_1(sK1,sK2),k8_eqrel_1(sK0,sK1))
      | ~ r2_hidden(X5,k11_relat_1(sK1,sK3))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
      | ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ v8_relat_2(sK1)
      | ~ v3_relat_2(sK1)
      | ~ v1_partfun1(sK1,sK0)
      | v1_xboole_0(sK0) ) ),
    inference(subsumption_resolution,[],[f286,f73])).

fof(f286,plain,(
    ! [X4,X5] :
      ( k6_eqrel_1(sK0,sK0,sK1,k4_binop_1(sK0,sK4,sK2,sK3)) != k6_eqrel_1(sK0,sK0,sK1,k1_binop_1(sK4,X4,X5))
      | ~ r2_hidden(X4,k11_relat_1(sK1,sK2))
      | ~ r2_hidden(k11_relat_1(sK1,sK3),k8_eqrel_1(sK0,sK1))
      | ~ r2_hidden(k11_relat_1(sK1,sK2),k8_eqrel_1(sK0,sK1))
      | ~ r2_hidden(X5,k11_relat_1(sK1,sK3))
      | ~ m2_filter_1(sK4,sK0,sK1)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
      | ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ v8_relat_2(sK1)
      | ~ v3_relat_2(sK1)
      | ~ v1_partfun1(sK1,sK0)
      | v1_xboole_0(sK0) ) ),
    inference(superposition,[],[f121,f276])).

fof(f276,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( k6_eqrel_1(X4,X4,X5,k1_binop_1(X6,X2,X0)) = k1_binop_1(k3_filter_1(X4,X5,X6),X3,X1)
      | ~ r2_hidden(X2,X3)
      | ~ r2_hidden(X1,k8_eqrel_1(X4,X5))
      | ~ r2_hidden(X3,k8_eqrel_1(X4,X5))
      | ~ r2_hidden(X0,X1)
      | ~ m2_filter_1(X6,X4,X5)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X4),X4)))
      | ~ v1_funct_2(X6,k2_zfmisc_1(X4,X4),X4)
      | ~ v1_funct_1(X6)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X4)))
      | ~ v8_relat_2(X5)
      | ~ v3_relat_2(X5)
      | ~ v1_partfun1(X5,X4)
      | v1_xboole_0(X4) ) ),
    inference(subsumption_resolution,[],[f275,f99])).

fof(f99,plain,(
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
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
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
    inference(flattening,[],[f47])).

fof(f47,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_filter_1)).

fof(f275,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X2,X3)
      | ~ r2_hidden(X1,k8_eqrel_1(X4,X5))
      | ~ r2_hidden(X3,k8_eqrel_1(X4,X5))
      | k6_eqrel_1(X4,X4,X5,k1_binop_1(X6,X2,X0)) = k1_binop_1(k3_filter_1(X4,X5,X6),X3,X1)
      | ~ v1_funct_2(k3_filter_1(X4,X5,X6),k2_zfmisc_1(k8_eqrel_1(X4,X5),k8_eqrel_1(X4,X5)),k8_eqrel_1(X4,X5))
      | ~ m2_filter_1(X6,X4,X5)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X4),X4)))
      | ~ v1_funct_2(X6,k2_zfmisc_1(X4,X4),X4)
      | ~ v1_funct_1(X6)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X4)))
      | ~ v8_relat_2(X5)
      | ~ v3_relat_2(X5)
      | ~ v1_partfun1(X5,X4)
      | v1_xboole_0(X4) ) ),
    inference(subsumption_resolution,[],[f274,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | v1_funct_1(k3_filter_1(X0,X1,X2))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | ~ v1_partfun1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f274,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X2,X3)
      | ~ r2_hidden(X1,k8_eqrel_1(X4,X5))
      | ~ r2_hidden(X3,k8_eqrel_1(X4,X5))
      | k6_eqrel_1(X4,X4,X5,k1_binop_1(X6,X2,X0)) = k1_binop_1(k3_filter_1(X4,X5,X6),X3,X1)
      | ~ v1_funct_2(k3_filter_1(X4,X5,X6),k2_zfmisc_1(k8_eqrel_1(X4,X5),k8_eqrel_1(X4,X5)),k8_eqrel_1(X4,X5))
      | ~ v1_funct_1(k3_filter_1(X4,X5,X6))
      | ~ m2_filter_1(X6,X4,X5)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X4),X4)))
      | ~ v1_funct_2(X6,k2_zfmisc_1(X4,X4),X4)
      | ~ v1_funct_1(X6)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X4)))
      | ~ v8_relat_2(X5)
      | ~ v3_relat_2(X5)
      | ~ v1_partfun1(X5,X4)
      | v1_xboole_0(X4) ) ),
    inference(duplicate_literal_removal,[],[f272])).

fof(f272,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X2,X3)
      | ~ r2_hidden(X1,k8_eqrel_1(X4,X5))
      | ~ r2_hidden(X3,k8_eqrel_1(X4,X5))
      | k6_eqrel_1(X4,X4,X5,k1_binop_1(X6,X2,X0)) = k1_binop_1(k3_filter_1(X4,X5,X6),X3,X1)
      | ~ v1_funct_2(k3_filter_1(X4,X5,X6),k2_zfmisc_1(k8_eqrel_1(X4,X5),k8_eqrel_1(X4,X5)),k8_eqrel_1(X4,X5))
      | ~ v1_funct_1(k3_filter_1(X4,X5,X6))
      | ~ m2_filter_1(X6,X4,X5)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X4),X4)))
      | ~ v1_funct_2(X6,k2_zfmisc_1(X4,X4),X4)
      | ~ v1_funct_1(X6)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X4)))
      | ~ v8_relat_2(X5)
      | ~ v3_relat_2(X5)
      | ~ v1_partfun1(X5,X4)
      | v1_xboole_0(X4)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X4),X4)))
      | ~ v1_funct_2(X6,k2_zfmisc_1(X4,X4),X4)
      | ~ v1_funct_1(X6)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X4)))
      | ~ v8_relat_2(X5)
      | ~ v3_relat_2(X5)
      | ~ v1_partfun1(X5,X4)
      | v1_xboole_0(X4) ) ),
    inference(resolution,[],[f104,f100])).

fof(f100,plain,(
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
    inference(cnf_transformation,[],[f48])).

fof(f104,plain,(
    ! [X2,X0,X10,X8,X1,X11,X9] :
      ( ~ m1_subset_1(k3_filter_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))))
      | ~ r2_hidden(X11,X9)
      | ~ r2_hidden(X10,X8)
      | ~ r2_hidden(X9,k8_eqrel_1(X0,X1))
      | ~ r2_hidden(X8,k8_eqrel_1(X0,X1))
      | k6_eqrel_1(X0,X0,X1,k1_binop_1(X2,X10,X11)) = k1_binop_1(k3_filter_1(X0,X1,X2),X8,X9)
      | ~ v1_funct_2(k3_filter_1(X0,X1,X2),k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))
      | ~ v1_funct_1(k3_filter_1(X0,X1,X2))
      | ~ m2_filter_1(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | ~ v1_partfun1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X2,X0,X10,X8,X3,X1,X11,X9] :
      ( k1_binop_1(X3,X8,X9) = k6_eqrel_1(X0,X0,X1,k1_binop_1(X2,X10,X11))
      | ~ r2_hidden(X11,X9)
      | ~ r2_hidden(X10,X8)
      | ~ r2_hidden(X9,k8_eqrel_1(X0,X1))
      | ~ r2_hidden(X8,k8_eqrel_1(X0,X1))
      | k3_filter_1(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))))
      | ~ v1_funct_2(X3,k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))
      | ~ v1_funct_1(X3)
      | ~ m2_filter_1(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | ~ v1_partfun1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k3_filter_1(X0,X1,X2) = X3
                      | ( k1_binop_1(X3,sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3)) != k6_eqrel_1(X0,X0,X1,k1_binop_1(X2,sK7(X0,X1,X2,X3),sK8(X0,X1,X2,X3)))
                        & r2_hidden(sK8(X0,X1,X2,X3),sK6(X0,X1,X2,X3))
                        & r2_hidden(sK7(X0,X1,X2,X3),sK5(X0,X1,X2,X3))
                        & r2_hidden(sK6(X0,X1,X2,X3),k8_eqrel_1(X0,X1))
                        & r2_hidden(sK5(X0,X1,X2,X3),k8_eqrel_1(X0,X1)) ) )
                    & ( ! [X8,X9,X10,X11] :
                          ( k1_binop_1(X3,X8,X9) = k6_eqrel_1(X0,X0,X1,k1_binop_1(X2,X10,X11))
                          | ~ r2_hidden(X11,X9)
                          | ~ r2_hidden(X10,X8)
                          | ~ r2_hidden(X9,k8_eqrel_1(X0,X1))
                          | ~ r2_hidden(X8,k8_eqrel_1(X0,X1)) )
                      | k3_filter_1(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))))
                  | ~ v1_funct_2(X3,k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))
                  | ~ v1_funct_1(X3) )
              | ~ m2_filter_1(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
              | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
              | ~ v1_funct_1(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          | ~ v8_relat_2(X1)
          | ~ v3_relat_2(X1)
          | ~ v1_partfun1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f60,f61])).

fof(f61,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4,X5,X6,X7] :
          ( k1_binop_1(X3,X4,X5) != k6_eqrel_1(X0,X0,X1,k1_binop_1(X2,X6,X7))
          & r2_hidden(X7,X5)
          & r2_hidden(X6,X4)
          & r2_hidden(X5,k8_eqrel_1(X0,X1))
          & r2_hidden(X4,k8_eqrel_1(X0,X1)) )
     => ( k1_binop_1(X3,sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3)) != k6_eqrel_1(X0,X0,X1,k1_binop_1(X2,sK7(X0,X1,X2,X3),sK8(X0,X1,X2,X3)))
        & r2_hidden(sK8(X0,X1,X2,X3),sK6(X0,X1,X2,X3))
        & r2_hidden(sK7(X0,X1,X2,X3),sK5(X0,X1,X2,X3))
        & r2_hidden(sK6(X0,X1,X2,X3),k8_eqrel_1(X0,X1))
        & r2_hidden(sK5(X0,X1,X2,X3),k8_eqrel_1(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k3_filter_1(X0,X1,X2) = X3
                      | ? [X4,X5,X6,X7] :
                          ( k1_binop_1(X3,X4,X5) != k6_eqrel_1(X0,X0,X1,k1_binop_1(X2,X6,X7))
                          & r2_hidden(X7,X5)
                          & r2_hidden(X6,X4)
                          & r2_hidden(X5,k8_eqrel_1(X0,X1))
                          & r2_hidden(X4,k8_eqrel_1(X0,X1)) ) )
                    & ( ! [X8,X9,X10,X11] :
                          ( k1_binop_1(X3,X8,X9) = k6_eqrel_1(X0,X0,X1,k1_binop_1(X2,X10,X11))
                          | ~ r2_hidden(X11,X9)
                          | ~ r2_hidden(X10,X8)
                          | ~ r2_hidden(X9,k8_eqrel_1(X0,X1))
                          | ~ r2_hidden(X8,k8_eqrel_1(X0,X1)) )
                      | k3_filter_1(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))))
                  | ~ v1_funct_2(X3,k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))
                  | ~ v1_funct_1(X3) )
              | ~ m2_filter_1(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
              | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
              | ~ v1_funct_1(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          | ~ v8_relat_2(X1)
          | ~ v3_relat_2(X1)
          | ~ v1_partfun1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(rectify,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k3_filter_1(X0,X1,X2) = X3
                      | ? [X4,X5,X6,X7] :
                          ( k1_binop_1(X3,X4,X5) != k6_eqrel_1(X0,X0,X1,k1_binop_1(X2,X6,X7))
                          & r2_hidden(X7,X5)
                          & r2_hidden(X6,X4)
                          & r2_hidden(X5,k8_eqrel_1(X0,X1))
                          & r2_hidden(X4,k8_eqrel_1(X0,X1)) ) )
                    & ( ! [X4,X5,X6,X7] :
                          ( k1_binop_1(X3,X4,X5) = k6_eqrel_1(X0,X0,X1,k1_binop_1(X2,X6,X7))
                          | ~ r2_hidden(X7,X5)
                          | ~ r2_hidden(X6,X4)
                          | ~ r2_hidden(X5,k8_eqrel_1(X0,X1))
                          | ~ r2_hidden(X4,k8_eqrel_1(X0,X1)) )
                      | k3_filter_1(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))))
                  | ~ v1_funct_2(X3,k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))
                  | ~ v1_funct_1(X3) )
              | ~ m2_filter_1(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
              | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
              | ~ v1_funct_1(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          | ~ v8_relat_2(X1)
          | ~ v3_relat_2(X1)
          | ~ v1_partfun1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k3_filter_1(X0,X1,X2) = X3
                  <=> ! [X4,X5,X6,X7] :
                        ( k1_binop_1(X3,X4,X5) = k6_eqrel_1(X0,X0,X1,k1_binop_1(X2,X6,X7))
                        | ~ r2_hidden(X7,X5)
                        | ~ r2_hidden(X6,X4)
                        | ~ r2_hidden(X5,k8_eqrel_1(X0,X1))
                        | ~ r2_hidden(X4,k8_eqrel_1(X0,X1)) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))))
                  | ~ v1_funct_2(X3,k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))
                  | ~ v1_funct_1(X3) )
              | ~ m2_filter_1(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
              | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
              | ~ v1_funct_1(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          | ~ v8_relat_2(X1)
          | ~ v3_relat_2(X1)
          | ~ v1_partfun1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k3_filter_1(X0,X1,X2) = X3
                  <=> ! [X4,X5,X6,X7] :
                        ( k1_binop_1(X3,X4,X5) = k6_eqrel_1(X0,X0,X1,k1_binop_1(X2,X6,X7))
                        | ~ r2_hidden(X7,X5)
                        | ~ r2_hidden(X6,X4)
                        | ~ r2_hidden(X5,k8_eqrel_1(X0,X1))
                        | ~ r2_hidden(X4,k8_eqrel_1(X0,X1)) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))))
                  | ~ v1_funct_2(X3,k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))
                  | ~ v1_funct_1(X3) )
              | ~ m2_filter_1(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
              | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
              | ~ v1_funct_1(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          | ~ v8_relat_2(X1)
          | ~ v3_relat_2(X1)
          | ~ v1_partfun1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v8_relat_2(X1)
            & v3_relat_2(X1)
            & v1_partfun1(X1,X0) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
                & v1_funct_1(X2) )
             => ( m2_filter_1(X2,X0,X1)
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))))
                      & v1_funct_2(X3,k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))
                      & v1_funct_1(X3) )
                   => ( k3_filter_1(X0,X1,X2) = X3
                    <=> ! [X4,X5,X6,X7] :
                          ( ( r2_hidden(X7,X5)
                            & r2_hidden(X6,X4)
                            & r2_hidden(X5,k8_eqrel_1(X0,X1))
                            & r2_hidden(X4,k8_eqrel_1(X0,X1)) )
                         => k1_binop_1(X3,X4,X5) = k6_eqrel_1(X0,X0,X1,k1_binop_1(X2,X6,X7)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_filter_1)).

fof(f121,plain,(
    k6_eqrel_1(sK0,sK0,sK1,k4_binop_1(sK0,sK4,sK2,sK3)) != k1_binop_1(k3_filter_1(sK0,sK1,sK4),k11_relat_1(sK1,sK2),k11_relat_1(sK1,sK3)) ),
    inference(subsumption_resolution,[],[f120,f70])).

fof(f120,plain,
    ( k6_eqrel_1(sK0,sK0,sK1,k4_binop_1(sK0,sK4,sK2,sK3)) != k1_binop_1(k3_filter_1(sK0,sK1,sK4),k11_relat_1(sK1,sK2),k11_relat_1(sK1,sK3))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(superposition,[],[f118,f102])).

fof(f118,plain,(
    k6_eqrel_1(sK0,sK0,sK1,k4_binop_1(sK0,sK4,sK2,sK3)) != k1_binop_1(k3_filter_1(sK0,sK1,sK4),k11_relat_1(sK1,sK2),k6_eqrel_1(sK0,sK0,sK1,sK3)) ),
    inference(subsumption_resolution,[],[f116,f70])).

fof(f116,plain,
    ( k6_eqrel_1(sK0,sK0,sK1,k4_binop_1(sK0,sK4,sK2,sK3)) != k1_binop_1(k3_filter_1(sK0,sK1,sK4),k11_relat_1(sK1,sK2),k6_eqrel_1(sK0,sK0,sK1,sK3))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(superposition,[],[f74,f102])).

fof(f74,plain,(
    k1_binop_1(k3_filter_1(sK0,sK1,sK4),k6_eqrel_1(sK0,sK0,sK1,sK2),k6_eqrel_1(sK0,sK0,sK1,sK3)) != k6_eqrel_1(sK0,sK0,sK1,k4_binop_1(sK0,sK4,sK2,sK3)) ),
    inference(cnf_transformation,[],[f58])).

%------------------------------------------------------------------------------
