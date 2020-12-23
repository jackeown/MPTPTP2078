%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_2__t16_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:36 EDT 2019

% Result     : Theorem 1.30s
% Output     : Refutation 1.30s
% Verified   : 
% Statistics : Number of formulae       :  259 ( 878 expanded)
%              Number of leaves         :   58 ( 333 expanded)
%              Depth                    :   13
%              Number of atoms          :  831 (3784 expanded)
%              Number of equality atoms :  163 (1064 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4834,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f217,f331,f354,f355,f371,f440,f487,f540,f547,f564,f567,f613,f643,f668,f677,f679,f1914,f2573,f2604,f2715,f2719,f2805,f2877,f2882,f2968,f2995,f2999,f3018,f3032,f3519,f4643,f4738,f4748,f4828,f4829,f4831,f4833])).

fof(f4833,plain,
    ( ~ spl9_313
    | ~ spl9_315
    | spl9_380
    | ~ spl9_395
    | ~ spl9_0
    | ~ spl9_356 ),
    inference(avatar_split_clause,[],[f4832,f2803,f123,f3004,f2880,f2561,f2558])).

fof(f2558,plain,
    ( spl9_313
  <=> ~ v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_313])])).

fof(f2561,plain,
    ( spl9_315
  <=> ~ v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_315])])).

fof(f2880,plain,
    ( spl9_380
  <=> ! [X0] :
        ( sK4(sK2,sK1) != sK4(sK2,X0)
        | ~ r2_hidden(sK4(sK2,X0),X0)
        | k2_relat_1(sK2) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_380])])).

fof(f3004,plain,
    ( spl9_395
  <=> ~ r2_hidden(sK5(sK2,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_395])])).

fof(f123,plain,
    ( spl9_0
  <=> k1_relset_1(sK0,sK1,sK2) = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_0])])).

fof(f2803,plain,
    ( spl9_356
  <=> k1_funct_1(sK2,sK5(sK2,sK1)) = sK4(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_356])])).

fof(f4832,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5(sK2,sK1),sK0)
        | sK4(sK2,sK1) != sK4(sK2,X0)
        | k2_relat_1(sK2) = X0
        | ~ r2_hidden(sK4(sK2,X0),X0)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl9_0
    | ~ spl9_356 ),
    inference(forward_demodulation,[],[f4750,f2554])).

fof(f2554,plain,
    ( k1_relat_1(sK2) = sK0
    | ~ spl9_0 ),
    inference(forward_demodulation,[],[f116,f124])).

fof(f124,plain,
    ( k1_relset_1(sK0,sK1,sK2) = sK0
    | ~ spl9_0 ),
    inference(avatar_component_clause,[],[f123])).

fof(f116,plain,(
    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(resolution,[],[f70,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t16_funct_2.p',redefinition_k1_relset_1)).

fof(f70,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,
    ( k2_relset_1(sK0,sK1,sK2) != sK1
    & ! [X3] :
        ( ( k1_funct_1(sK2,sK3(X3)) = X3
          & r2_hidden(sK3(X3),sK0) )
        | ~ r2_hidden(X3,sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f31,f54,f53])).

fof(f53,plain,
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
   => ( k2_relset_1(sK0,sK1,sK2) != sK1
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(sK2,X4) = X3
              & r2_hidden(X4,sK0) )
          | ~ r2_hidden(X3,sK1) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X2,X0,X3] :
      ( ? [X4] :
          ( k1_funct_1(X2,X4) = X3
          & r2_hidden(X4,X0) )
     => ( k1_funct_1(X2,sK3(X3)) = X3
        & r2_hidden(sK3(X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
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
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/funct_2__t16_funct_2.p',t16_funct_2)).

fof(f4750,plain,
    ( ! [X0] :
        ( sK4(sK2,sK1) != sK4(sK2,X0)
        | k2_relat_1(sK2) = X0
        | ~ r2_hidden(sK5(sK2,sK1),k1_relat_1(sK2))
        | ~ r2_hidden(sK4(sK2,X0),X0)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl9_356 ),
    inference(superposition,[],[f81,f2804])).

fof(f2804,plain,
    ( k1_funct_1(sK2,sK5(sK2,sK1)) = sK4(sK2,sK1)
    | ~ spl9_356 ),
    inference(avatar_component_clause,[],[f2803])).

fof(f81,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(X0,X3) != sK4(X0,X1)
      | k2_relat_1(X0) = X1
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ r2_hidden(sK4(X0,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK4(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK4(X0,X1),X1) )
              & ( ( k1_funct_1(X0,sK5(X0,X1)) = sK4(X0,X1)
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f57,f60,f59,f58])).

fof(f58,plain,(
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

fof(f59,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK5(X0,X1)) = X2
        & r2_hidden(sK5(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK6(X0,X5)) = X5
        & r2_hidden(sK6(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
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
    inference(rectify,[],[f56])).

fof(f56,plain,(
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
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f33,plain,(
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
    file('/export/starexec/sandbox/benchmark/funct_2__t16_funct_2.p',d5_funct_1)).

fof(f4831,plain,
    ( ~ spl9_313
    | ~ spl9_315
    | spl9_376
    | ~ spl9_395
    | ~ spl9_0
    | ~ spl9_356 ),
    inference(avatar_split_clause,[],[f4830,f2803,f123,f3004,f2872,f2561,f2558])).

fof(f2872,plain,
    ( spl9_376
  <=> r2_hidden(sK4(sK2,sK1),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_376])])).

fof(f4830,plain,
    ( ~ r2_hidden(sK5(sK2,sK1),sK0)
    | r2_hidden(sK4(sK2,sK1),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl9_0
    | ~ spl9_356 ),
    inference(forward_demodulation,[],[f4749,f2554])).

fof(f4749,plain,
    ( r2_hidden(sK4(sK2,sK1),k2_relat_1(sK2))
    | ~ r2_hidden(sK5(sK2,sK1),k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl9_356 ),
    inference(superposition,[],[f105,f2804])).

fof(f105,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f104])).

fof(f104,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f4829,plain,
    ( spl9_354
    | spl9_398
    | spl9_390
    | ~ spl9_318 ),
    inference(avatar_split_clause,[],[f4640,f2568,f2993,f4144,f2800])).

fof(f2800,plain,
    ( spl9_354
  <=> k1_funct_1(sK2,sK3(sK4(sK2,sK1))) = sK4(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_354])])).

fof(f4144,plain,
    ( spl9_398
  <=> m1_subset_1(sK5(sK2,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_398])])).

fof(f2993,plain,
    ( spl9_390
  <=> k2_relat_1(sK2) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_390])])).

fof(f2568,plain,
    ( spl9_318
  <=> ! [X1] :
        ( r2_hidden(sK5(sK2,X1),sK0)
        | k2_relat_1(sK2) = X1
        | r2_hidden(sK4(sK2,X1),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_318])])).

fof(f4640,plain,
    ( k2_relat_1(sK2) = sK1
    | m1_subset_1(sK5(sK2,sK1),sK0)
    | k1_funct_1(sK2,sK3(sK4(sK2,sK1))) = sK4(sK2,sK1)
    | ~ spl9_318 ),
    inference(resolution,[],[f2884,f72])).

fof(f72,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK1)
      | k1_funct_1(sK2,sK3(X3)) = X3 ) ),
    inference(cnf_transformation,[],[f55])).

fof(f2884,plain,
    ( ! [X1] :
        ( r2_hidden(sK4(sK2,X1),X1)
        | k2_relat_1(sK2) = X1
        | m1_subset_1(sK5(sK2,X1),sK0) )
    | ~ spl9_318 ),
    inference(resolution,[],[f2569,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t16_funct_2.p',t1_subset)).

fof(f2569,plain,
    ( ! [X1] :
        ( r2_hidden(sK5(sK2,X1),sK0)
        | r2_hidden(sK4(sK2,X1),X1)
        | k2_relat_1(sK2) = X1 )
    | ~ spl9_318 ),
    inference(avatar_component_clause,[],[f2568])).

fof(f4828,plain,
    ( ~ spl9_376
    | spl9_393 ),
    inference(avatar_contradiction_clause,[],[f4827])).

fof(f4827,plain,
    ( $false
    | ~ spl9_376
    | ~ spl9_393 ),
    inference(subsumption_resolution,[],[f3577,f2998])).

fof(f2998,plain,
    ( ~ m1_subset_1(sK4(sK2,sK1),sK1)
    | ~ spl9_393 ),
    inference(avatar_component_clause,[],[f2997])).

fof(f2997,plain,
    ( spl9_393
  <=> ~ m1_subset_1(sK4(sK2,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_393])])).

fof(f3577,plain,
    ( m1_subset_1(sK4(sK2,sK1),sK1)
    | ~ spl9_376 ),
    inference(resolution,[],[f2612,f2873])).

fof(f2873,plain,
    ( r2_hidden(sK4(sK2,sK1),k2_relat_1(sK2))
    | ~ spl9_376 ),
    inference(avatar_component_clause,[],[f2872])).

fof(f2612,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k2_relat_1(sK2))
      | m1_subset_1(X1,sK1) ) ),
    inference(resolution,[],[f2553,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t16_funct_2.p',t4_subset)).

fof(f2553,plain,(
    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) ),
    inference(global_subsumption,[],[f70,f2552])).

fof(f2552,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f95,f115])).

fof(f115,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f70,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t16_funct_2.p',redefinition_k2_relset_1)).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t16_funct_2.p',dt_k2_relset_1)).

fof(f4748,plain,
    ( ~ spl9_393
    | spl9_4
    | spl9_397 ),
    inference(avatar_split_clause,[],[f4744,f4736,f159,f2997])).

fof(f159,plain,
    ( spl9_4
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f4736,plain,
    ( spl9_397
  <=> ~ r2_hidden(sK4(sK2,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_397])])).

fof(f4744,plain,
    ( v1_xboole_0(sK1)
    | ~ m1_subset_1(sK4(sK2,sK1),sK1)
    | ~ spl9_397 ),
    inference(resolution,[],[f4737,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t16_funct_2.p',t2_subset)).

fof(f4737,plain,
    ( ~ r2_hidden(sK4(sK2,sK1),sK1)
    | ~ spl9_397 ),
    inference(avatar_component_clause,[],[f4736])).

fof(f4738,plain,
    ( spl9_390
    | ~ spl9_397
    | ~ spl9_380 ),
    inference(avatar_split_clause,[],[f4734,f2880,f4736,f2993])).

fof(f4734,plain,
    ( ~ r2_hidden(sK4(sK2,sK1),sK1)
    | k2_relat_1(sK2) = sK1
    | ~ spl9_380 ),
    inference(equality_resolution,[],[f2881])).

fof(f2881,plain,
    ( ! [X0] :
        ( sK4(sK2,sK1) != sK4(sK2,X0)
        | ~ r2_hidden(sK4(sK2,X0),X0)
        | k2_relat_1(sK2) = X0 )
    | ~ spl9_380 ),
    inference(avatar_component_clause,[],[f2880])).

fof(f4643,plain,
    ( spl9_388
    | spl9_398
    | spl9_390
    | ~ spl9_318 ),
    inference(avatar_split_clause,[],[f4641,f2568,f2993,f4144,f4141])).

fof(f4141,plain,
    ( spl9_388
  <=> m1_subset_1(sK3(sK4(sK2,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_388])])).

fof(f4641,plain,
    ( k2_relat_1(sK2) = sK1
    | m1_subset_1(sK5(sK2,sK1),sK0)
    | m1_subset_1(sK3(sK4(sK2,sK1)),sK0)
    | ~ spl9_318 ),
    inference(resolution,[],[f2884,f144])).

fof(f144,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK1)
      | m1_subset_1(sK3(X1),sK0) ) ),
    inference(resolution,[],[f71,f85])).

fof(f71,plain,(
    ! [X3] :
      ( r2_hidden(sK3(X3),sK0)
      | ~ r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f3519,plain,(
    spl9_27 ),
    inference(avatar_contradiction_clause,[],[f3518])).

fof(f3518,plain,
    ( $false
    | ~ spl9_27 ),
    inference(subsumption_resolution,[],[f2188,f216])).

fof(f216,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl9_27 ),
    inference(avatar_component_clause,[],[f215])).

fof(f215,plain,
    ( spl9_27
  <=> ~ v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_27])])).

fof(f2188,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(backward_demodulation,[],[f2185,f74])).

fof(f74,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t16_funct_2.p',dt_o_0_0_xboole_0)).

fof(f2185,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(resolution,[],[f74,f75])).

fof(f75,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t16_funct_2.p',t6_boole)).

fof(f3032,plain,(
    ~ spl9_390 ),
    inference(avatar_contradiction_clause,[],[f3019])).

fof(f3019,plain,
    ( $false
    | ~ spl9_390 ),
    inference(subsumption_resolution,[],[f2551,f2994])).

fof(f2994,plain,
    ( k2_relat_1(sK2) = sK1
    | ~ spl9_390 ),
    inference(avatar_component_clause,[],[f2993])).

fof(f2551,plain,(
    k2_relat_1(sK2) != sK1 ),
    inference(superposition,[],[f73,f115])).

fof(f73,plain,(
    k2_relset_1(sK0,sK1,sK2) != sK1 ),
    inference(cnf_transformation,[],[f55])).

fof(f3018,plain,
    ( ~ spl9_399
    | spl9_12
    | spl9_395 ),
    inference(avatar_split_clause,[],[f3010,f3004,f866,f3016])).

fof(f3016,plain,
    ( spl9_399
  <=> ~ m1_subset_1(sK5(sK2,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_399])])).

fof(f866,plain,
    ( spl9_12
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f3010,plain,
    ( v1_xboole_0(sK0)
    | ~ m1_subset_1(sK5(sK2,sK1),sK0)
    | ~ spl9_395 ),
    inference(resolution,[],[f3005,f86])).

fof(f3005,plain,
    ( ~ r2_hidden(sK5(sK2,sK1),sK0)
    | ~ spl9_395 ),
    inference(avatar_component_clause,[],[f3004])).

fof(f2999,plain,
    ( ~ spl9_393
    | spl9_4
    | spl9_379 ),
    inference(avatar_split_clause,[],[f2991,f2875,f159,f2997])).

fof(f2875,plain,
    ( spl9_379
  <=> ~ r2_hidden(sK3(sK4(sK2,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_379])])).

fof(f2991,plain,
    ( v1_xboole_0(sK1)
    | ~ m1_subset_1(sK4(sK2,sK1),sK1)
    | ~ spl9_379 ),
    inference(resolution,[],[f2963,f86])).

fof(f2963,plain,
    ( ~ r2_hidden(sK4(sK2,sK1),sK1)
    | ~ spl9_379 ),
    inference(resolution,[],[f2876,f71])).

fof(f2876,plain,
    ( ~ r2_hidden(sK3(sK4(sK2,sK1)),sK0)
    | ~ spl9_379 ),
    inference(avatar_component_clause,[],[f2875])).

fof(f2995,plain,
    ( ~ spl9_313
    | ~ spl9_315
    | spl9_390
    | spl9_356
    | spl9_379 ),
    inference(avatar_split_clause,[],[f2990,f2875,f2803,f2993,f2561,f2558])).

fof(f2990,plain,
    ( k1_funct_1(sK2,sK5(sK2,sK1)) = sK4(sK2,sK1)
    | k2_relat_1(sK2) = sK1
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl9_379 ),
    inference(resolution,[],[f2963,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | k1_funct_1(X0,sK5(X0,X1)) = sK4(X0,X1)
      | k2_relat_1(X0) = X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f2968,plain,
    ( ~ spl9_389
    | spl9_12
    | spl9_379 ),
    inference(avatar_split_clause,[],[f2964,f2875,f866,f2966])).

fof(f2966,plain,
    ( spl9_389
  <=> ~ m1_subset_1(sK3(sK4(sK2,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_389])])).

fof(f2964,plain,
    ( v1_xboole_0(sK0)
    | ~ m1_subset_1(sK3(sK4(sK2,sK1)),sK0)
    | ~ spl9_379 ),
    inference(resolution,[],[f2876,f86])).

fof(f2882,plain,
    ( ~ spl9_313
    | ~ spl9_315
    | spl9_380
    | ~ spl9_379
    | ~ spl9_0
    | ~ spl9_354 ),
    inference(avatar_split_clause,[],[f2878,f2800,f123,f2875,f2880,f2561,f2558])).

fof(f2878,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(sK4(sK2,sK1)),sK0)
        | sK4(sK2,sK1) != sK4(sK2,X0)
        | k2_relat_1(sK2) = X0
        | ~ r2_hidden(sK4(sK2,X0),X0)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl9_0
    | ~ spl9_354 ),
    inference(forward_demodulation,[],[f2869,f2554])).

fof(f2869,plain,
    ( ! [X0] :
        ( sK4(sK2,sK1) != sK4(sK2,X0)
        | k2_relat_1(sK2) = X0
        | ~ r2_hidden(sK3(sK4(sK2,sK1)),k1_relat_1(sK2))
        | ~ r2_hidden(sK4(sK2,X0),X0)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl9_354 ),
    inference(superposition,[],[f81,f2801])).

fof(f2801,plain,
    ( k1_funct_1(sK2,sK3(sK4(sK2,sK1))) = sK4(sK2,sK1)
    | ~ spl9_354 ),
    inference(avatar_component_clause,[],[f2800])).

fof(f2877,plain,
    ( ~ spl9_313
    | ~ spl9_315
    | spl9_376
    | ~ spl9_379
    | ~ spl9_0
    | ~ spl9_354 ),
    inference(avatar_split_clause,[],[f2870,f2800,f123,f2875,f2872,f2561,f2558])).

fof(f2870,plain,
    ( ~ r2_hidden(sK3(sK4(sK2,sK1)),sK0)
    | r2_hidden(sK4(sK2,sK1),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl9_0
    | ~ spl9_354 ),
    inference(forward_demodulation,[],[f2868,f2554])).

fof(f2868,plain,
    ( r2_hidden(sK4(sK2,sK1),k2_relat_1(sK2))
    | ~ r2_hidden(sK3(sK4(sK2,sK1)),k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl9_354 ),
    inference(superposition,[],[f105,f2801])).

fof(f2805,plain,
    ( spl9_354
    | spl9_356 ),
    inference(avatar_split_clause,[],[f2798,f2803,f2800])).

fof(f2798,plain,
    ( k1_funct_1(sK2,sK5(sK2,sK1)) = sK4(sK2,sK1)
    | k1_funct_1(sK2,sK3(sK4(sK2,sK1))) = sK4(sK2,sK1) ),
    inference(global_subsumption,[],[f68,f2551,f2797])).

fof(f2797,plain,
    ( k1_funct_1(sK2,sK5(sK2,sK1)) = sK4(sK2,sK1)
    | k2_relat_1(sK2) = sK1
    | ~ v1_funct_1(sK2)
    | k1_funct_1(sK2,sK3(sK4(sK2,sK1))) = sK4(sK2,sK1) ),
    inference(resolution,[],[f155,f117])).

fof(f117,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f70,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t16_funct_2.p',cc1_relset_1)).

fof(f155,plain,(
    ! [X2] :
      ( ~ v1_relat_1(X2)
      | k1_funct_1(X2,sK5(X2,sK1)) = sK4(X2,sK1)
      | k2_relat_1(X2) = sK1
      | ~ v1_funct_1(X2)
      | k1_funct_1(sK2,sK3(sK4(X2,sK1))) = sK4(X2,sK1) ) ),
    inference(resolution,[],[f72,f80])).

fof(f68,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f2719,plain,
    ( ~ spl9_313
    | ~ spl9_315
    | spl9_318
    | ~ spl9_0 ),
    inference(avatar_split_clause,[],[f2717,f123,f2568,f2561,f2558])).

fof(f2717,plain,
    ( ! [X1] :
        ( r2_hidden(sK5(sK2,X1),sK0)
        | r2_hidden(sK4(sK2,X1),X1)
        | k2_relat_1(sK2) = X1
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl9_0 ),
    inference(superposition,[],[f79,f2554])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),k1_relat_1(X0))
      | r2_hidden(sK4(X0,X1),X1)
      | k2_relat_1(X0) = X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f2715,plain,
    ( spl9_0
    | spl9_2 ),
    inference(avatar_split_clause,[],[f2714,f126,f123])).

fof(f126,plain,
    ( spl9_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f2714,plain,
    ( k1_xboole_0 = sK1
    | k1_relset_1(sK0,sK1,sK2) = sK0 ),
    inference(global_subsumption,[],[f69,f2706])).

fof(f2706,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | k1_xboole_0 = sK1
    | k1_relset_1(sK0,sK1,sK2) = sK0 ),
    inference(resolution,[],[f70,f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
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
    inference(nnf_transformation,[],[f49])).

fof(f49,plain,(
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
    inference(flattening,[],[f48])).

fof(f48,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox/benchmark/funct_2__t16_funct_2.p',d1_funct_2)).

fof(f69,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f55])).

fof(f2604,plain,(
    spl9_315 ),
    inference(avatar_contradiction_clause,[],[f2603])).

fof(f2603,plain,
    ( $false
    | ~ spl9_315 ),
    inference(subsumption_resolution,[],[f68,f2562])).

fof(f2562,plain,
    ( ~ v1_funct_1(sK2)
    | ~ spl9_315 ),
    inference(avatar_component_clause,[],[f2561])).

fof(f2573,plain,(
    spl9_313 ),
    inference(avatar_contradiction_clause,[],[f2572])).

fof(f2572,plain,
    ( $false
    | ~ spl9_313 ),
    inference(subsumption_resolution,[],[f117,f2559])).

fof(f2559,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl9_313 ),
    inference(avatar_component_clause,[],[f2558])).

fof(f1914,plain,
    ( ~ spl9_2
    | spl9_5
    | ~ spl9_6 ),
    inference(avatar_contradiction_clause,[],[f1913])).

fof(f1913,plain,
    ( $false
    | ~ spl9_2
    | ~ spl9_5
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f415,f1769])).

fof(f1769,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl9_2
    | ~ spl9_5 ),
    inference(backward_demodulation,[],[f127,f131])).

fof(f131,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl9_5
  <=> ~ v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f127,plain,
    ( k1_xboole_0 = sK1
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f126])).

fof(f415,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl9_6 ),
    inference(backward_demodulation,[],[f219,f134])).

fof(f134,plain,
    ( v1_xboole_0(sK2)
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl9_6
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f219,plain,
    ( k1_xboole_0 = sK2
    | ~ spl9_6 ),
    inference(resolution,[],[f134,f75])).

fof(f679,plain,(
    ~ spl9_84 ),
    inference(avatar_contradiction_clause,[],[f678])).

fof(f678,plain,
    ( $false
    | ~ spl9_84 ),
    inference(resolution,[],[f676,f82])).

fof(f82,plain,(
    ! [X0] : m1_subset_1(sK7(X0),X0) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0] : m1_subset_1(sK7(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f16,f62])).

fof(f62,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK7(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f16,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t16_funct_2.p',existence_m1_subset_1)).

fof(f676,plain,
    ( ! [X0] : ~ m1_subset_1(X0,sK1)
    | ~ spl9_84 ),
    inference(avatar_component_clause,[],[f675])).

fof(f675,plain,
    ( spl9_84
  <=> ! [X0] : ~ m1_subset_1(X0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_84])])).

fof(f677,plain,
    ( spl9_84
    | spl9_4
    | ~ spl9_14 ),
    inference(avatar_split_clause,[],[f669,f150,f159,f675])).

fof(f150,plain,
    ( spl9_14
  <=> ! [X0] : ~ r2_hidden(X0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f669,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK1)
        | ~ m1_subset_1(X0,sK1) )
    | ~ spl9_14 ),
    inference(resolution,[],[f151,f86])).

fof(f151,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK1)
    | ~ spl9_14 ),
    inference(avatar_component_clause,[],[f150])).

fof(f668,plain,
    ( ~ spl9_13
    | spl9_14 ),
    inference(avatar_split_clause,[],[f665,f150,f147])).

fof(f147,plain,
    ( spl9_13
  <=> ~ v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).

fof(f665,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | ~ v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f71,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t16_funct_2.p',t7_boole)).

fof(f643,plain,
    ( ~ spl9_31
    | spl9_32
    | ~ spl9_4
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f642,f133,f159,f265,f262])).

fof(f262,plain,
    ( spl9_31
  <=> ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_31])])).

fof(f265,plain,
    ( spl9_32
  <=> m1_subset_1(k2_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_32])])).

fof(f642,plain,
    ( m1_subset_1(k2_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl9_4
    | ~ spl9_6 ),
    inference(superposition,[],[f95,f430])).

fof(f430,plain,
    ( k2_relset_1(sK0,k1_xboole_0,k1_xboole_0) = k2_relat_1(k1_xboole_0)
    | ~ spl9_4
    | ~ spl9_6 ),
    inference(resolution,[],[f423,f93])).

fof(f423,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl9_4
    | ~ spl9_6 ),
    inference(forward_demodulation,[],[f341,f219])).

fof(f341,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl9_4 ),
    inference(forward_demodulation,[],[f70,f312])).

fof(f312,plain,
    ( k1_xboole_0 = sK1
    | ~ spl9_4 ),
    inference(resolution,[],[f160,f75])).

fof(f160,plain,
    ( v1_xboole_0(sK1)
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f159])).

fof(f613,plain,
    ( ~ spl9_4
    | ~ spl9_6
    | ~ spl9_70 ),
    inference(avatar_contradiction_clause,[],[f611])).

fof(f611,plain,
    ( $false
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_70 ),
    inference(subsumption_resolution,[],[f424,f596])).

fof(f596,plain,
    ( k2_relset_1(sK0,k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_70 ),
    inference(forward_demodulation,[],[f430,f572])).

fof(f572,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl9_70 ),
    inference(resolution,[],[f563,f75])).

fof(f563,plain,
    ( v1_xboole_0(k2_relat_1(k1_xboole_0))
    | ~ spl9_70 ),
    inference(avatar_component_clause,[],[f562])).

fof(f562,plain,
    ( spl9_70
  <=> v1_xboole_0(k2_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_70])])).

fof(f424,plain,
    ( k2_relset_1(sK0,k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | ~ spl9_4
    | ~ spl9_6 ),
    inference(forward_demodulation,[],[f340,f219])).

fof(f340,plain,
    ( k2_relset_1(sK0,k1_xboole_0,sK2) != k1_xboole_0
    | ~ spl9_4 ),
    inference(forward_demodulation,[],[f73,f312])).

fof(f567,plain,(
    ~ spl9_68 ),
    inference(avatar_contradiction_clause,[],[f566])).

fof(f566,plain,
    ( $false
    | ~ spl9_68 ),
    inference(resolution,[],[f560,f82])).

fof(f560,plain,
    ( ! [X0] : ~ m1_subset_1(X0,k2_relat_1(k1_xboole_0))
    | ~ spl9_68 ),
    inference(avatar_component_clause,[],[f559])).

fof(f559,plain,
    ( spl9_68
  <=> ! [X0] : ~ m1_subset_1(X0,k2_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_68])])).

fof(f564,plain,
    ( spl9_68
    | spl9_70
    | ~ spl9_66 ),
    inference(avatar_split_clause,[],[f552,f545,f562,f559])).

fof(f545,plain,
    ( spl9_66
  <=> ! [X0] : ~ r2_hidden(X0,k2_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_66])])).

fof(f552,plain,
    ( ! [X0] :
        ( v1_xboole_0(k2_relat_1(k1_xboole_0))
        | ~ m1_subset_1(X0,k2_relat_1(k1_xboole_0)) )
    | ~ spl9_66 ),
    inference(resolution,[],[f546,f86])).

fof(f546,plain,
    ( ! [X0] : ~ r2_hidden(X0,k2_relat_1(k1_xboole_0))
    | ~ spl9_66 ),
    inference(avatar_component_clause,[],[f545])).

fof(f547,plain,
    ( spl9_66
    | ~ spl9_27
    | ~ spl9_32 ),
    inference(avatar_split_clause,[],[f542,f265,f215,f545])).

fof(f542,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(k1_xboole_0)
        | ~ r2_hidden(X0,k2_relat_1(k1_xboole_0)) )
    | ~ spl9_32 ),
    inference(resolution,[],[f266,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t16_funct_2.p',t5_subset)).

fof(f266,plain,
    ( m1_subset_1(k2_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl9_32 ),
    inference(avatar_component_clause,[],[f265])).

fof(f540,plain,
    ( ~ spl9_55
    | spl9_32
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_20 ),
    inference(avatar_split_clause,[],[f539,f185,f133,f159,f265,f475])).

fof(f475,plain,
    ( spl9_55
  <=> ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_55])])).

fof(f185,plain,
    ( spl9_20
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).

fof(f539,plain,
    ( m1_subset_1(k2_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_20 ),
    inference(superposition,[],[f95,f454])).

fof(f454,plain,
    ( k2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k2_relat_1(k1_xboole_0)
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_20 ),
    inference(resolution,[],[f444,f93])).

fof(f444,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_20 ),
    inference(backward_demodulation,[],[f186,f423])).

fof(f186,plain,
    ( k1_xboole_0 = sK0
    | ~ spl9_20 ),
    inference(avatar_component_clause,[],[f185])).

fof(f487,plain,
    ( ~ spl9_4
    | ~ spl9_6
    | ~ spl9_20
    | spl9_55 ),
    inference(avatar_contradiction_clause,[],[f486])).

fof(f486,plain,
    ( $false
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_20
    | ~ spl9_55 ),
    inference(subsumption_resolution,[],[f444,f476])).

fof(f476,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl9_55 ),
    inference(avatar_component_clause,[],[f475])).

fof(f440,plain,
    ( ~ spl9_4
    | ~ spl9_6
    | spl9_23 ),
    inference(avatar_contradiction_clause,[],[f439])).

fof(f439,plain,
    ( $false
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_23 ),
    inference(subsumption_resolution,[],[f422,f425])).

fof(f425,plain,
    ( ~ v1_funct_2(k1_xboole_0,sK0,k1_xboole_0)
    | ~ spl9_6
    | ~ spl9_23 ),
    inference(forward_demodulation,[],[f189,f219])).

fof(f189,plain,
    ( ~ v1_funct_2(sK2,sK0,k1_xboole_0)
    | ~ spl9_23 ),
    inference(avatar_component_clause,[],[f188])).

fof(f188,plain,
    ( spl9_23
  <=> ~ v1_funct_2(sK2,sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).

fof(f422,plain,
    ( v1_funct_2(k1_xboole_0,sK0,k1_xboole_0)
    | ~ spl9_4
    | ~ spl9_6 ),
    inference(forward_demodulation,[],[f342,f219])).

fof(f342,plain,
    ( v1_funct_2(sK2,sK0,k1_xboole_0)
    | ~ spl9_4 ),
    inference(forward_demodulation,[],[f69,f312])).

fof(f371,plain,
    ( spl9_13
    | ~ spl9_20
    | ~ spl9_26 ),
    inference(avatar_contradiction_clause,[],[f370])).

fof(f370,plain,
    ( $false
    | ~ spl9_13
    | ~ spl9_20
    | ~ spl9_26 ),
    inference(subsumption_resolution,[],[f205,f363])).

fof(f363,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl9_13
    | ~ spl9_20 ),
    inference(backward_demodulation,[],[f186,f148])).

fof(f148,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl9_13 ),
    inference(avatar_component_clause,[],[f147])).

fof(f205,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl9_26 ),
    inference(avatar_component_clause,[],[f204])).

fof(f204,plain,
    ( spl9_26
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).

fof(f355,plain,
    ( ~ spl9_27
    | spl9_6
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f351,f159,f133,f215])).

fof(f351,plain,
    ( v1_xboole_0(sK2)
    | ~ v1_xboole_0(k1_xboole_0)
    | ~ spl9_4 ),
    inference(resolution,[],[f341,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | v1_xboole_0(X2)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t16_funct_2.p',cc4_relset_1)).

fof(f354,plain,
    ( spl9_18
    | spl9_20
    | ~ spl9_23
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f345,f159,f188,f185,f182])).

fof(f182,plain,
    ( spl9_18
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).

fof(f345,plain,
    ( ~ v1_funct_2(sK2,sK0,k1_xboole_0)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK2
    | ~ spl9_4 ),
    inference(resolution,[],[f341,f110])).

fof(f110,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2 ) ),
    inference(equality_resolution,[],[f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f331,plain,
    ( ~ spl9_4
    | ~ spl9_18
    | spl9_31 ),
    inference(avatar_contradiction_clause,[],[f320])).

fof(f320,plain,
    ( $false
    | ~ spl9_4
    | ~ spl9_18
    | ~ spl9_31 ),
    inference(subsumption_resolution,[],[f263,f317])).

fof(f317,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl9_4
    | ~ spl9_18 ),
    inference(backward_demodulation,[],[f312,f276])).

fof(f276,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl9_18 ),
    inference(forward_demodulation,[],[f70,f183])).

fof(f183,plain,
    ( k1_xboole_0 = sK2
    | ~ spl9_18 ),
    inference(avatar_component_clause,[],[f182])).

fof(f263,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl9_31 ),
    inference(avatar_component_clause,[],[f262])).

fof(f217,plain,
    ( ~ spl9_27
    | spl9_6
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f178,f126,f133,f215])).

fof(f178,plain,
    ( v1_xboole_0(sK2)
    | ~ v1_xboole_0(k1_xboole_0)
    | ~ spl9_2 ),
    inference(resolution,[],[f169,f83])).

fof(f169,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl9_2 ),
    inference(backward_demodulation,[],[f127,f70])).
%------------------------------------------------------------------------------
