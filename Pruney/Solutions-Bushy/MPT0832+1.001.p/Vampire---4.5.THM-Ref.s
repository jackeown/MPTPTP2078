%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0832+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:43 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 192 expanded)
%              Number of leaves         :   25 (  79 expanded)
%              Depth                    :   11
%              Number of atoms          :  357 ( 662 expanded)
%              Number of equality atoms :   16 (  34 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f197,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f58,f62,f68,f77,f92,f98,f101,f109,f114,f135,f145,f157,f169,f182,f196])).

fof(f196,plain,
    ( ~ spl8_6
    | spl8_9
    | ~ spl8_18
    | ~ spl8_21 ),
    inference(avatar_split_clause,[],[f191,f180,f167,f107,f90])).

fof(f90,plain,
    ( spl8_6
  <=> v1_relat_1(k8_relat_1(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

% (1933)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
fof(f107,plain,
    ( spl8_9
  <=> r1_tarski(k8_relat_1(sK1,sK3),k2_zfmisc_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f167,plain,
    ( spl8_18
  <=> r2_hidden(sK4(k8_relat_1(sK1,sK3),k2_zfmisc_1(sK2,sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f180,plain,
    ( spl8_21
  <=> r2_hidden(sK5(k8_relat_1(sK1,sK3),k2_zfmisc_1(sK2,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f191,plain,
    ( ~ r2_hidden(sK4(k8_relat_1(sK1,sK3),k2_zfmisc_1(sK2,sK1)),sK2)
    | r1_tarski(k8_relat_1(sK1,sK3),k2_zfmisc_1(sK2,sK1))
    | ~ v1_relat_1(k8_relat_1(sK1,sK3))
    | ~ spl8_21 ),
    inference(resolution,[],[f186,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)
      | r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)
              & r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f21,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(k4_tarski(X2,X3),X1)
          & r2_hidden(k4_tarski(X2,X3),X0) )
     => ( ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)
        & r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                & r2_hidden(k4_tarski(X2,X3),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                & r2_hidden(k4_tarski(X2,X3),X0) ) )
          & ( ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
                | ~ r2_hidden(k4_tarski(X2,X3),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X1)
              | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
             => r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).

fof(f186,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(X0,sK5(k8_relat_1(sK1,sK3),k2_zfmisc_1(sK2,sK1))),k2_zfmisc_1(X1,sK1))
        | ~ r2_hidden(X0,X1) )
    | ~ spl8_21 ),
    inference(resolution,[],[f181,f51])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X1,X3)
      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_zfmisc_1)).

fof(f181,plain,
    ( r2_hidden(sK5(k8_relat_1(sK1,sK3),k2_zfmisc_1(sK2,sK1)),sK1)
    | ~ spl8_21 ),
    inference(avatar_component_clause,[],[f180])).

fof(f182,plain,
    ( ~ spl8_7
    | ~ spl8_6
    | spl8_21
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f178,f112,f180,f90,f96])).

fof(f96,plain,
    ( spl8_7
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f112,plain,
    ( spl8_10
  <=> r2_hidden(k4_tarski(sK4(k8_relat_1(sK1,sK3),k2_zfmisc_1(sK2,sK1)),sK5(k8_relat_1(sK1,sK3),k2_zfmisc_1(sK2,sK1))),k8_relat_1(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f178,plain,
    ( r2_hidden(sK5(k8_relat_1(sK1,sK3),k2_zfmisc_1(sK2,sK1)),sK1)
    | ~ v1_relat_1(k8_relat_1(sK1,sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl8_10 ),
    inference(resolution,[],[f54,f113])).

fof(f113,plain,
    ( r2_hidden(k4_tarski(sK4(k8_relat_1(sK1,sK3),k2_zfmisc_1(sK2,sK1)),sK5(k8_relat_1(sK1,sK3),k2_zfmisc_1(sK2,sK1))),k8_relat_1(sK1,sK3))
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f112])).

fof(f54,plain,(
    ! [X6,X0,X5,X1] :
      ( ~ r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1))
      | r2_hidden(X6,X0)
      | ~ v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(X6,X0)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k8_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X1)
                  | ~ r2_hidden(sK7(X0,X1,X2),X0)
                  | ~ r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2) )
                & ( ( r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X1)
                    & r2_hidden(sK7(X0,X1,X2),X0) )
                  | r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X1)
                    | ~ r2_hidden(X6,X0) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X1)
                      & r2_hidden(X6,X0) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k8_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f26,f27])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
            | ~ r2_hidden(X4,X0)
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ( r2_hidden(k4_tarski(X3,X4),X1)
              & r2_hidden(X4,X0) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X1)
          | ~ r2_hidden(sK7(X0,X1,X2),X0)
          | ~ r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2) )
        & ( ( r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X1)
            & r2_hidden(sK7(X0,X1,X2),X0) )
          | r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X1)
                    | ~ r2_hidden(X6,X0) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X1)
                      & r2_hidden(X6,X0) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k8_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k8_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k8_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k8_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X1)
                  & r2_hidden(X4,X0) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( k8_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X1)
                  & r2_hidden(X4,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_relat_1)).

fof(f169,plain,
    ( spl8_18
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f159,f155,f167])).

fof(f155,plain,
    ( spl8_16
  <=> r2_hidden(k4_tarski(sK4(k8_relat_1(sK1,sK3),k2_zfmisc_1(sK2,sK1)),sK5(k8_relat_1(sK1,sK3),k2_zfmisc_1(sK2,sK1))),k2_zfmisc_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f159,plain,
    ( r2_hidden(sK4(k8_relat_1(sK1,sK3),k2_zfmisc_1(sK2,sK1)),sK2)
    | ~ spl8_16 ),
    inference(resolution,[],[f156,f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f156,plain,
    ( r2_hidden(k4_tarski(sK4(k8_relat_1(sK1,sK3),k2_zfmisc_1(sK2,sK1)),sK5(k8_relat_1(sK1,sK3),k2_zfmisc_1(sK2,sK1))),k2_zfmisc_1(sK2,sK0))
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f155])).

fof(f157,plain,
    ( spl8_16
    | ~ spl8_2
    | ~ spl8_14 ),
    inference(avatar_split_clause,[],[f152,f143,f60,f155])).

fof(f60,plain,
    ( spl8_2
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f143,plain,
    ( spl8_14
  <=> ! [X0] :
        ( r2_hidden(k4_tarski(sK4(k8_relat_1(sK1,sK3),k2_zfmisc_1(sK2,sK1)),sK5(k8_relat_1(sK1,sK3),k2_zfmisc_1(sK2,sK1))),X0)
        | ~ r1_tarski(sK3,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f152,plain,
    ( r2_hidden(k4_tarski(sK4(k8_relat_1(sK1,sK3),k2_zfmisc_1(sK2,sK1)),sK5(k8_relat_1(sK1,sK3),k2_zfmisc_1(sK2,sK1))),k2_zfmisc_1(sK2,sK0))
    | ~ spl8_2
    | ~ spl8_14 ),
    inference(resolution,[],[f147,f61])).

fof(f61,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f60])).

fof(f147,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(X1))
        | r2_hidden(k4_tarski(sK4(k8_relat_1(sK1,sK3),k2_zfmisc_1(sK2,sK1)),sK5(k8_relat_1(sK1,sK3),k2_zfmisc_1(sK2,sK1))),X1) )
    | ~ spl8_14 ),
    inference(resolution,[],[f144,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f144,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK3,X0)
        | r2_hidden(k4_tarski(sK4(k8_relat_1(sK1,sK3),k2_zfmisc_1(sK2,sK1)),sK5(k8_relat_1(sK1,sK3),k2_zfmisc_1(sK2,sK1))),X0) )
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f143])).

fof(f145,plain,
    ( ~ spl8_7
    | spl8_14
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f140,f133,f143,f96])).

fof(f133,plain,
    ( spl8_12
  <=> r2_hidden(k4_tarski(sK4(k8_relat_1(sK1,sK3),k2_zfmisc_1(sK2,sK1)),sK5(k8_relat_1(sK1,sK3),k2_zfmisc_1(sK2,sK1))),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f140,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(sK4(k8_relat_1(sK1,sK3),k2_zfmisc_1(sK2,sK1)),sK5(k8_relat_1(sK1,sK3),k2_zfmisc_1(sK2,sK1))),X0)
        | ~ r1_tarski(sK3,X0)
        | ~ v1_relat_1(sK3) )
    | ~ spl8_12 ),
    inference(resolution,[],[f134,f34])).

fof(f34,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ r2_hidden(k4_tarski(X4,X5),X0)
      | r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f134,plain,
    ( r2_hidden(k4_tarski(sK4(k8_relat_1(sK1,sK3),k2_zfmisc_1(sK2,sK1)),sK5(k8_relat_1(sK1,sK3),k2_zfmisc_1(sK2,sK1))),sK3)
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f133])).

fof(f135,plain,
    ( ~ spl8_7
    | spl8_12
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f129,f112,f133,f96])).

fof(f129,plain,
    ( r2_hidden(k4_tarski(sK4(k8_relat_1(sK1,sK3),k2_zfmisc_1(sK2,sK1)),sK5(k8_relat_1(sK1,sK3),k2_zfmisc_1(sK2,sK1))),sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl8_10 ),
    inference(resolution,[],[f113,f63])).

fof(f63,plain,(
    ! [X6,X0,X5,X1] :
      ( ~ r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1))
      | r2_hidden(k4_tarski(X5,X6),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(global_subsumption,[],[f37,f53])).

fof(f53,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1))
      | ~ v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k8_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(f114,plain,
    ( spl8_10
    | ~ spl8_2
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f110,f75,f60,f112])).

fof(f75,plain,
    ( spl8_5
  <=> r2_hidden(k4_tarski(sK4(k6_relset_1(sK2,sK0,sK1,sK3),k2_zfmisc_1(sK2,sK1)),sK5(k6_relset_1(sK2,sK0,sK1,sK3),k2_zfmisc_1(sK2,sK1))),k6_relset_1(sK2,sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f110,plain,
    ( r2_hidden(k4_tarski(sK4(k8_relat_1(sK1,sK3),k2_zfmisc_1(sK2,sK1)),sK5(k8_relat_1(sK1,sK3),k2_zfmisc_1(sK2,sK1))),k8_relat_1(sK1,sK3))
    | ~ spl8_2
    | ~ spl8_5 ),
    inference(forward_demodulation,[],[f76,f82])).

fof(f82,plain,
    ( ! [X0] : k6_relset_1(sK2,sK0,X0,sK3) = k8_relat_1(X0,sK3)
    | ~ spl8_2 ),
    inference(resolution,[],[f47,f61])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_relset_1)).

fof(f76,plain,
    ( r2_hidden(k4_tarski(sK4(k6_relset_1(sK2,sK0,sK1,sK3),k2_zfmisc_1(sK2,sK1)),sK5(k6_relset_1(sK2,sK0,sK1,sK3),k2_zfmisc_1(sK2,sK1))),k6_relset_1(sK2,sK0,sK1,sK3))
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f75])).

fof(f109,plain,
    ( ~ spl8_9
    | ~ spl8_2
    | spl8_3 ),
    inference(avatar_split_clause,[],[f87,f66,f60,f107])).

fof(f66,plain,
    ( spl8_3
  <=> r1_tarski(k6_relset_1(sK2,sK0,sK1,sK3),k2_zfmisc_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f87,plain,
    ( ~ r1_tarski(k8_relat_1(sK1,sK3),k2_zfmisc_1(sK2,sK1))
    | ~ spl8_2
    | spl8_3 ),
    inference(superposition,[],[f67,f82])).

fof(f67,plain,
    ( ~ r1_tarski(k6_relset_1(sK2,sK0,sK1,sK3),k2_zfmisc_1(sK2,sK1))
    | spl8_3 ),
    inference(avatar_component_clause,[],[f66])).

fof(f101,plain,
    ( ~ spl8_2
    | spl8_7 ),
    inference(avatar_contradiction_clause,[],[f100])).

fof(f100,plain,
    ( $false
    | ~ spl8_2
    | spl8_7 ),
    inference(subsumption_resolution,[],[f61,f99])).

fof(f99,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl8_7 ),
    inference(resolution,[],[f97,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f97,plain,
    ( ~ v1_relat_1(sK3)
    | spl8_7 ),
    inference(avatar_component_clause,[],[f96])).

fof(f98,plain,
    ( ~ spl8_7
    | spl8_6 ),
    inference(avatar_split_clause,[],[f93,f90,f96])).

fof(f93,plain,
    ( ~ v1_relat_1(sK3)
    | spl8_6 ),
    inference(resolution,[],[f91,f37])).

fof(f91,plain,
    ( ~ v1_relat_1(k8_relat_1(sK1,sK3))
    | spl8_6 ),
    inference(avatar_component_clause,[],[f90])).

fof(f92,plain,
    ( ~ spl8_6
    | ~ spl8_2
    | spl8_4 ),
    inference(avatar_split_clause,[],[f86,f72,f60,f90])).

fof(f72,plain,
    ( spl8_4
  <=> v1_relat_1(k6_relset_1(sK2,sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f86,plain,
    ( ~ v1_relat_1(k8_relat_1(sK1,sK3))
    | ~ spl8_2
    | spl8_4 ),
    inference(superposition,[],[f73,f82])).

fof(f73,plain,
    ( ~ v1_relat_1(k6_relset_1(sK2,sK0,sK1,sK3))
    | spl8_4 ),
    inference(avatar_component_clause,[],[f72])).

fof(f77,plain,
    ( ~ spl8_4
    | spl8_5
    | spl8_3 ),
    inference(avatar_split_clause,[],[f70,f66,f75,f72])).

fof(f70,plain,
    ( r2_hidden(k4_tarski(sK4(k6_relset_1(sK2,sK0,sK1,sK3),k2_zfmisc_1(sK2,sK1)),sK5(k6_relset_1(sK2,sK0,sK1,sK3),k2_zfmisc_1(sK2,sK1))),k6_relset_1(sK2,sK0,sK1,sK3))
    | ~ v1_relat_1(k6_relset_1(sK2,sK0,sK1,sK3))
    | spl8_3 ),
    inference(resolution,[],[f35,f67])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f68,plain,
    ( ~ spl8_3
    | spl8_1 ),
    inference(avatar_split_clause,[],[f64,f56,f66])).

fof(f56,plain,
    ( spl8_1
  <=> m1_subset_1(k6_relset_1(sK2,sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f64,plain,
    ( ~ r1_tarski(k6_relset_1(sK2,sK0,sK1,sK3),k2_zfmisc_1(sK2,sK1))
    | spl8_1 ),
    inference(resolution,[],[f45,f57])).

fof(f57,plain,
    ( ~ m1_subset_1(k6_relset_1(sK2,sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl8_1 ),
    inference(avatar_component_clause,[],[f56])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f62,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f32,f60])).

fof(f32,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ~ m1_subset_1(k6_relset_1(sK2,sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
   => ( ~ m1_subset_1(k6_relset_1(sK2,sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
       => m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
     => m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_relset_1)).

fof(f58,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f33,f56])).

fof(f33,plain,(
    ~ m1_subset_1(k6_relset_1(sK2,sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f19])).

%------------------------------------------------------------------------------
