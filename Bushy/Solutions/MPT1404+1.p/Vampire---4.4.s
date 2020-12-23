%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : connsp_2__t34_connsp_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:35:53 EDT 2019

% Result     : Theorem 0.91s
% Output     : Refutation 0.91s
% Verified   : 
% Statistics : Number of formulae       :  175 ( 610 expanded)
%              Number of leaves         :   30 ( 203 expanded)
%              Depth                    :   34
%              Number of atoms          : 1014 (5452 expanded)
%              Number of equality atoms :   16 (  60 expanded)
%              Maximal formula depth    :   18 (   8 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2817,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f157,f161,f168,f192,f1534,f1540,f2813])).

fof(f2813,plain,
    ( ~ spl11_0
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_12 ),
    inference(avatar_contradiction_clause,[],[f2812])).

fof(f2812,plain,
    ( $false
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_12 ),
    inference(subsumption_resolution,[],[f2811,f156])).

fof(f156,plain,
    ( r1_xboole_0(sK3,sK1)
    | ~ spl11_2 ),
    inference(avatar_component_clause,[],[f155])).

fof(f155,plain,
    ( spl11_2
  <=> r1_xboole_0(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f2811,plain,
    ( ~ r1_xboole_0(sK3,sK1)
    | ~ spl11_0
    | ~ spl11_4
    | ~ spl11_12 ),
    inference(subsumption_resolution,[],[f2805,f160])).

fof(f160,plain,
    ( m1_connsp_2(sK3,sK0,sK2)
    | ~ spl11_4 ),
    inference(avatar_component_clause,[],[f159])).

fof(f159,plain,
    ( spl11_4
  <=> m1_connsp_2(sK3,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f2805,plain,
    ( ~ m1_connsp_2(sK3,sK0,sK2)
    | ~ r1_xboole_0(sK3,sK1)
    | ~ spl11_0
    | ~ spl11_4
    | ~ spl11_12 ),
    inference(resolution,[],[f2680,f1560])).

fof(f1560,plain,
    ( r1_tarski(sK3,u1_struct_0(sK0))
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f1559,f99])).

fof(f99,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,plain,
    ( ( ( r1_xboole_0(sK3,sK1)
        & m1_connsp_2(sK3,sK0,sK2) )
      | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1)) )
    & ( ! [X4] :
          ( ~ r1_xboole_0(X4,sK1)
          | ~ m1_connsp_2(X4,sK0,sK2) )
      | r2_hidden(sK2,k2_pre_topc(sK0,sK1)) )
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f76,f80,f79,f78,f77])).

fof(f77,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ? [X3] :
                      ( r1_xboole_0(X3,X1)
                      & m1_connsp_2(X3,X0,X2) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) )
                & ( ! [X4] :
                      ( ~ r1_xboole_0(X4,X1)
                      | ~ m1_connsp_2(X4,X0,X2) )
                  | r2_hidden(X2,k2_pre_topc(X0,X1)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( r1_xboole_0(X3,X1)
                    & m1_connsp_2(X3,sK0,X2) )
                | ~ r2_hidden(X2,k2_pre_topc(sK0,X1)) )
              & ( ! [X4] :
                    ( ~ r1_xboole_0(X4,X1)
                    | ~ m1_connsp_2(X4,sK0,X2) )
                | r2_hidden(X2,k2_pre_topc(sK0,X1)) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f78,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( r1_xboole_0(X3,X1)
                    & m1_connsp_2(X3,X0,X2) )
                | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & ( ! [X4] :
                    ( ~ r1_xboole_0(X4,X1)
                    | ~ m1_connsp_2(X4,X0,X2) )
                | r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ( ? [X3] :
                  ( r1_xboole_0(X3,sK1)
                  & m1_connsp_2(X3,X0,X2) )
              | ~ r2_hidden(X2,k2_pre_topc(X0,sK1)) )
            & ( ! [X4] :
                  ( ~ r1_xboole_0(X4,sK1)
                  | ~ m1_connsp_2(X4,X0,X2) )
              | r2_hidden(X2,k2_pre_topc(X0,sK1)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( r1_xboole_0(X3,X1)
                & m1_connsp_2(X3,X0,X2) )
            | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) )
          & ( ! [X4] :
                ( ~ r1_xboole_0(X4,X1)
                | ~ m1_connsp_2(X4,X0,X2) )
            | r2_hidden(X2,k2_pre_topc(X0,X1)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( ? [X3] :
              ( r1_xboole_0(X3,X1)
              & m1_connsp_2(X3,X0,sK2) )
          | ~ r2_hidden(sK2,k2_pre_topc(X0,X1)) )
        & ( ! [X4] :
              ( ~ r1_xboole_0(X4,X1)
              | ~ m1_connsp_2(X4,X0,sK2) )
          | r2_hidden(sK2,k2_pre_topc(X0,X1)) )
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( r1_xboole_0(X3,X1)
          & m1_connsp_2(X3,X0,X2) )
     => ( r1_xboole_0(sK3,X1)
        & m1_connsp_2(sK3,X0,X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f76,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( r1_xboole_0(X3,X1)
                    & m1_connsp_2(X3,X0,X2) )
                | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & ( ! [X4] :
                    ( ~ r1_xboole_0(X4,X1)
                    | ~ m1_connsp_2(X4,X0,X2) )
                | r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f75])).

fof(f75,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( r1_xboole_0(X3,X1)
                    & m1_connsp_2(X3,X0,X2) )
                | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & ( ! [X3] :
                    ( ~ r1_xboole_0(X3,X1)
                    | ~ m1_connsp_2(X3,X0,X2) )
                | r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f74])).

fof(f74,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( r1_xboole_0(X3,X1)
                    & m1_connsp_2(X3,X0,X2) )
                | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & ( ! [X3] :
                    ( ~ r1_xboole_0(X3,X1)
                    | ~ m1_connsp_2(X3,X0,X2) )
                | r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <~> ! [X3] :
                    ( ~ r1_xboole_0(X3,X1)
                    | ~ m1_connsp_2(X3,X0,X2) ) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <~> ! [X3] :
                    ( ~ r1_xboole_0(X3,X1)
                    | ~ m1_connsp_2(X3,X0,X2) ) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r2_hidden(X2,k2_pre_topc(X0,X1))
                <=> ! [X3] :
                      ( m1_connsp_2(X3,X0,X2)
                     => ~ r1_xboole_0(X3,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ! [X3] :
                    ( m1_connsp_2(X3,X0,X2)
                   => ~ r1_xboole_0(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t34_connsp_2.p',t34_connsp_2)).

fof(f1559,plain,
    ( v2_struct_0(sK0)
    | r1_tarski(sK3,u1_struct_0(sK0))
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f1558,f100])).

fof(f100,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f81])).

fof(f1558,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | r1_tarski(sK3,u1_struct_0(sK0))
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f1557,f101])).

fof(f101,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f81])).

fof(f1557,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | r1_tarski(sK3,u1_struct_0(sK0))
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f1546,f103])).

fof(f103,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f81])).

fof(f1546,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | r1_tarski(sK3,u1_struct_0(sK0))
    | ~ spl11_4 ),
    inference(resolution,[],[f160,f248])).

fof(f248,plain,(
    ! [X14,X15,X16] :
      ( ~ m1_connsp_2(X14,X15,X16)
      | ~ m1_subset_1(X16,u1_struct_0(X15))
      | ~ l1_pre_topc(X15)
      | ~ v2_pre_topc(X15)
      | v2_struct_0(X15)
      | r1_tarski(X14,u1_struct_0(X15)) ) ),
    inference(resolution,[],[f130,f137])).

fof(f137,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t34_connsp_2.p',t3_subset)).

fof(f130,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t34_connsp_2.p',dt_m1_connsp_2)).

fof(f2680,plain,
    ( ! [X2] :
        ( ~ r1_tarski(X2,u1_struct_0(sK0))
        | ~ m1_connsp_2(X2,sK0,sK2)
        | ~ r1_xboole_0(X2,sK1) )
    | ~ spl11_0
    | ~ spl11_12 ),
    inference(resolution,[],[f2649,f138])).

fof(f138,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f94])).

fof(f2649,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_xboole_0(X2,sK1)
        | ~ m1_connsp_2(X2,sK0,sK2) )
    | ~ spl11_0
    | ~ spl11_12 ),
    inference(subsumption_resolution,[],[f2648,f99])).

fof(f2648,plain,
    ( ! [X2] :
        ( ~ r1_xboole_0(X2,sK1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_connsp_2(X2,sK0,sK2)
        | v2_struct_0(sK0) )
    | ~ spl11_0
    | ~ spl11_12 ),
    inference(subsumption_resolution,[],[f2647,f100])).

fof(f2647,plain,
    ( ! [X2] :
        ( ~ r1_xboole_0(X2,sK1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_connsp_2(X2,sK0,sK2)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl11_0
    | ~ spl11_12 ),
    inference(subsumption_resolution,[],[f2646,f101])).

fof(f2646,plain,
    ( ! [X2] :
        ( ~ r1_xboole_0(X2,sK1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_connsp_2(X2,sK0,sK2)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl11_0
    | ~ spl11_12 ),
    inference(subsumption_resolution,[],[f2638,f103])).

fof(f2638,plain,
    ( ! [X2] :
        ( ~ r1_xboole_0(X2,sK1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_connsp_2(X2,sK0,sK2)
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl11_0
    | ~ spl11_12 ),
    inference(resolution,[],[f2587,f266])).

fof(f266,plain,(
    ! [X6,X4,X5] :
      ( r2_hidden(X6,k1_tops_1(X5,X4))
      | ~ m1_connsp_2(X4,X5,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X5))
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5) ) ),
    inference(subsumption_resolution,[],[f258,f248])).

fof(f258,plain,(
    ! [X6,X4,X5] :
      ( ~ m1_connsp_2(X4,X5,X6)
      | r2_hidden(X6,k1_tops_1(X5,X4))
      | ~ m1_subset_1(X6,u1_struct_0(X5))
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5)
      | ~ r1_tarski(X4,u1_struct_0(X5)) ) ),
    inference(resolution,[],[f121,f138])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f89])).

fof(f89,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ~ r2_hidden(X1,k1_tops_1(X0,X2)) )
                & ( r2_hidden(X1,k1_tops_1(X0,X2))
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t34_connsp_2.p',d1_connsp_2)).

fof(f2587,plain,
    ( ! [X14] :
        ( ~ r2_hidden(sK2,k1_tops_1(sK0,X14))
        | ~ r1_xboole_0(X14,sK1)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl11_0
    | ~ spl11_12 ),
    inference(subsumption_resolution,[],[f2586,f137])).

fof(f2586,plain,
    ( ! [X14] :
        ( ~ r1_xboole_0(X14,sK1)
        | ~ r1_tarski(X14,u1_struct_0(sK0))
        | ~ r2_hidden(sK2,k1_tops_1(sK0,X14))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl11_0
    | ~ spl11_12 ),
    inference(subsumption_resolution,[],[f2579,f101])).

fof(f2579,plain,
    ( ! [X14] :
        ( ~ r1_xboole_0(X14,sK1)
        | ~ l1_pre_topc(sK0)
        | ~ r1_tarski(X14,u1_struct_0(sK0))
        | ~ r2_hidden(sK2,k1_tops_1(sK0,X14))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl11_0
    | ~ spl11_12 ),
    inference(resolution,[],[f785,f2265])).

fof(f2265,plain,
    ( ! [X2] :
        ( ~ r1_xboole_0(sK1,k1_tops_1(sK0,X2))
        | ~ r2_hidden(sK2,k1_tops_1(sK0,X2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl11_0
    | ~ spl11_12 ),
    inference(subsumption_resolution,[],[f2264,f137])).

fof(f2264,plain,
    ( ! [X2] :
        ( ~ r2_hidden(sK2,k1_tops_1(sK0,X2))
        | ~ r1_xboole_0(sK1,k1_tops_1(sK0,X2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X2,u1_struct_0(sK0)) )
    | ~ spl11_0
    | ~ spl11_12 ),
    inference(subsumption_resolution,[],[f2263,f100])).

fof(f2263,plain,
    ( ! [X2] :
        ( ~ r2_hidden(sK2,k1_tops_1(sK0,X2))
        | ~ r1_xboole_0(sK1,k1_tops_1(sK0,X2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_pre_topc(sK0)
        | ~ r1_tarski(X2,u1_struct_0(sK0)) )
    | ~ spl11_0
    | ~ spl11_12 ),
    inference(subsumption_resolution,[],[f2251,f101])).

fof(f2251,plain,
    ( ! [X2] :
        ( ~ r2_hidden(sK2,k1_tops_1(sK0,X2))
        | ~ r1_xboole_0(sK1,k1_tops_1(sK0,X2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r1_tarski(X2,u1_struct_0(sK0)) )
    | ~ spl11_0
    | ~ spl11_12 ),
    inference(resolution,[],[f1663,f207])).

fof(f207,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ r1_tarski(X1,u1_struct_0(X0)) ) ),
    inference(resolution,[],[f132,f138])).

fof(f132,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t34_connsp_2.p',fc9_tops_1)).

fof(f1663,plain,
    ( ! [X4] :
        ( ~ v3_pre_topc(k1_tops_1(sK0,X4),sK0)
        | ~ r2_hidden(sK2,k1_tops_1(sK0,X4))
        | ~ r1_xboole_0(sK1,k1_tops_1(sK0,X4))
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl11_0
    | ~ spl11_12 ),
    inference(subsumption_resolution,[],[f1652,f101])).

fof(f1652,plain,
    ( ! [X4] :
        ( ~ v3_pre_topc(k1_tops_1(sK0,X4),sK0)
        | ~ r2_hidden(sK2,k1_tops_1(sK0,X4))
        | ~ r1_xboole_0(sK1,k1_tops_1(sK0,X4))
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl11_0
    | ~ spl11_12 ),
    inference(resolution,[],[f1578,f134])).

fof(f134,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t34_connsp_2.p',dt_k1_tops_1)).

fof(f1578,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | ~ r2_hidden(sK2,X0)
        | ~ r1_xboole_0(sK1,X0) )
    | ~ spl11_0
    | ~ spl11_12 ),
    inference(subsumption_resolution,[],[f1577,f101])).

fof(f1577,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK2,X0)
        | ~ r1_xboole_0(sK1,X0)
        | ~ l1_pre_topc(sK0) )
    | ~ spl11_0
    | ~ spl11_12 ),
    inference(subsumption_resolution,[],[f1576,f102])).

fof(f102,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f81])).

fof(f1576,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK2,X0)
        | ~ r1_xboole_0(sK1,X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl11_0
    | ~ spl11_12 ),
    inference(subsumption_resolution,[],[f1568,f188])).

fof(f188,plain,
    ( r2_hidden(sK2,u1_struct_0(sK0))
    | ~ spl11_12 ),
    inference(avatar_component_clause,[],[f187])).

fof(f187,plain,
    ( spl11_12
  <=> r2_hidden(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).

fof(f1568,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK2,X0)
        | ~ r2_hidden(sK2,u1_struct_0(sK0))
        | ~ r1_xboole_0(sK1,X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl11_0 ),
    inference(resolution,[],[f164,f363])).

fof(f363,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,k2_pre_topc(X2,X3))
      | ~ v3_pre_topc(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,u1_struct_0(X2))
      | ~ r1_xboole_0(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(duplicate_literal_removal,[],[f357])).

fof(f357,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v3_pre_topc(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ r2_hidden(X0,k2_pre_topc(X2,X3))
      | ~ r2_hidden(X0,u1_struct_0(X2))
      | ~ r1_xboole_0(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(resolution,[],[f150,f133])).

fof(f133,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t34_connsp_2.p',dt_k2_pre_topc)).

fof(f150,plain,(
    ! [X6,X0,X8,X1] :
      ( ~ m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X6,X8)
      | ~ v3_pre_topc(X8,X0)
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X6,k2_pre_topc(X0,X1))
      | ~ r2_hidden(X6,u1_struct_0(X0))
      | ~ r1_xboole_0(X1,X8)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f110])).

fof(f110,plain,(
    ! [X6,X2,X0,X8,X1] :
      ( ~ r1_xboole_0(X1,X8)
      | ~ r2_hidden(X6,X8)
      | ~ v3_pre_topc(X8,X0)
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X6,X2)
      | ~ r2_hidden(X6,u1_struct_0(X0))
      | k2_pre_topc(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f88])).

fof(f88,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k2_pre_topc(X0,X1) = X2
                  | ( ( ( r1_xboole_0(X1,sK5(X0,X1,X2))
                        & r2_hidden(sK4(X0,X1,X2),sK5(X0,X1,X2))
                        & v3_pre_topc(sK5(X0,X1,X2),X0)
                        & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
                      | ~ r2_hidden(sK4(X0,X1,X2),X2) )
                    & ( ! [X5] :
                          ( ~ r1_xboole_0(X1,X5)
                          | ~ r2_hidden(sK4(X0,X1,X2),X5)
                          | ~ v3_pre_topc(X5,X0)
                          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                      | r2_hidden(sK4(X0,X1,X2),X2) )
                    & r2_hidden(sK4(X0,X1,X2),u1_struct_0(X0)) ) )
                & ( ! [X6] :
                      ( ( ( r2_hidden(X6,X2)
                          | ( r1_xboole_0(X1,sK6(X0,X1,X6))
                            & r2_hidden(X6,sK6(X0,X1,X6))
                            & v3_pre_topc(sK6(X0,X1,X6),X0)
                            & m1_subset_1(sK6(X0,X1,X6),k1_zfmisc_1(u1_struct_0(X0))) ) )
                        & ( ! [X8] :
                              ( ~ r1_xboole_0(X1,X8)
                              | ~ r2_hidden(X6,X8)
                              | ~ v3_pre_topc(X8,X0)
                              | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X0))) )
                          | ~ r2_hidden(X6,X2) ) )
                      | ~ r2_hidden(X6,u1_struct_0(X0)) )
                  | k2_pre_topc(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f84,f87,f86,f85])).

fof(f85,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ? [X4] :
                ( r1_xboole_0(X1,X4)
                & r2_hidden(X3,X4)
                & v3_pre_topc(X4,X0)
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ r2_hidden(X3,X2) )
          & ( ! [X5] :
                ( ~ r1_xboole_0(X1,X5)
                | ~ r2_hidden(X3,X5)
                | ~ v3_pre_topc(X5,X0)
                | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
            | r2_hidden(X3,X2) )
          & r2_hidden(X3,u1_struct_0(X0)) )
     => ( ( ? [X4] :
              ( r1_xboole_0(X1,X4)
              & r2_hidden(sK4(X0,X1,X2),X4)
              & v3_pre_topc(X4,X0)
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ! [X5] :
              ( ~ r1_xboole_0(X1,X5)
              | ~ r2_hidden(sK4(X0,X1,X2),X5)
              | ~ v3_pre_topc(X5,X0)
              | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
          | r2_hidden(sK4(X0,X1,X2),X2) )
        & r2_hidden(sK4(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f86,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( r1_xboole_0(X1,X4)
          & r2_hidden(X3,X4)
          & v3_pre_topc(X4,X0)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r1_xboole_0(X1,sK5(X0,X1,X2))
        & r2_hidden(X3,sK5(X0,X1,X2))
        & v3_pre_topc(sK5(X0,X1,X2),X0)
        & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f87,plain,(
    ! [X6,X1,X0] :
      ( ? [X7] :
          ( r1_xboole_0(X1,X7)
          & r2_hidden(X6,X7)
          & v3_pre_topc(X7,X0)
          & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r1_xboole_0(X1,sK6(X0,X1,X6))
        & r2_hidden(X6,sK6(X0,X1,X6))
        & v3_pre_topc(sK6(X0,X1,X6),X0)
        & m1_subset_1(sK6(X0,X1,X6),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f84,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k2_pre_topc(X0,X1) = X2
                  | ? [X3] :
                      ( ( ? [X4] :
                            ( r1_xboole_0(X1,X4)
                            & r2_hidden(X3,X4)
                            & v3_pre_topc(X4,X0)
                            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                        | ~ r2_hidden(X3,X2) )
                      & ( ! [X5] :
                            ( ~ r1_xboole_0(X1,X5)
                            | ~ r2_hidden(X3,X5)
                            | ~ v3_pre_topc(X5,X0)
                            | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                        | r2_hidden(X3,X2) )
                      & r2_hidden(X3,u1_struct_0(X0)) ) )
                & ( ! [X6] :
                      ( ( ( r2_hidden(X6,X2)
                          | ? [X7] :
                              ( r1_xboole_0(X1,X7)
                              & r2_hidden(X6,X7)
                              & v3_pre_topc(X7,X0)
                              & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X0))) ) )
                        & ( ! [X8] :
                              ( ~ r1_xboole_0(X1,X8)
                              | ~ r2_hidden(X6,X8)
                              | ~ v3_pre_topc(X8,X0)
                              | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X0))) )
                          | ~ r2_hidden(X6,X2) ) )
                      | ~ r2_hidden(X6,u1_struct_0(X0)) )
                  | k2_pre_topc(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f83])).

fof(f83,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k2_pre_topc(X0,X1) = X2
                  | ? [X3] :
                      ( ( ? [X4] :
                            ( r1_xboole_0(X1,X4)
                            & r2_hidden(X3,X4)
                            & v3_pre_topc(X4,X0)
                            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                        | ~ r2_hidden(X3,X2) )
                      & ( ! [X4] :
                            ( ~ r1_xboole_0(X1,X4)
                            | ~ r2_hidden(X3,X4)
                            | ~ v3_pre_topc(X4,X0)
                            | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                        | r2_hidden(X3,X2) )
                      & r2_hidden(X3,u1_struct_0(X0)) ) )
                & ( ! [X3] :
                      ( ( ( r2_hidden(X3,X2)
                          | ? [X4] :
                              ( r1_xboole_0(X1,X4)
                              & r2_hidden(X3,X4)
                              & v3_pre_topc(X4,X0)
                              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) ) )
                        & ( ! [X4] :
                              ( ~ r1_xboole_0(X1,X4)
                              | ~ r2_hidden(X3,X4)
                              | ~ v3_pre_topc(X4,X0)
                              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                          | ~ r2_hidden(X3,X2) ) )
                      | ~ r2_hidden(X3,u1_struct_0(X0)) )
                  | k2_pre_topc(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f82])).

fof(f82,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k2_pre_topc(X0,X1) = X2
                  | ? [X3] :
                      ( ( ? [X4] :
                            ( r1_xboole_0(X1,X4)
                            & r2_hidden(X3,X4)
                            & v3_pre_topc(X4,X0)
                            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                        | ~ r2_hidden(X3,X2) )
                      & ( ! [X4] :
                            ( ~ r1_xboole_0(X1,X4)
                            | ~ r2_hidden(X3,X4)
                            | ~ v3_pre_topc(X4,X0)
                            | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                        | r2_hidden(X3,X2) )
                      & r2_hidden(X3,u1_struct_0(X0)) ) )
                & ( ! [X3] :
                      ( ( ( r2_hidden(X3,X2)
                          | ? [X4] :
                              ( r1_xboole_0(X1,X4)
                              & r2_hidden(X3,X4)
                              & v3_pre_topc(X4,X0)
                              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) ) )
                        & ( ! [X4] :
                              ( ~ r1_xboole_0(X1,X4)
                              | ~ r2_hidden(X3,X4)
                              | ~ v3_pre_topc(X4,X0)
                              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                          | ~ r2_hidden(X3,X2) ) )
                      | ~ r2_hidden(X3,u1_struct_0(X0)) )
                  | k2_pre_topc(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k2_pre_topc(X0,X1) = X2
              <=> ! [X3] :
                    ( ( r2_hidden(X3,X2)
                    <=> ! [X4] :
                          ( ~ r1_xboole_0(X1,X4)
                          | ~ r2_hidden(X3,X4)
                          | ~ v3_pre_topc(X4,X0)
                          | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) ) )
                    | ~ r2_hidden(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k2_pre_topc(X0,X1) = X2
              <=> ! [X3] :
                    ( ( r2_hidden(X3,X2)
                    <=> ! [X4] :
                          ( ~ r1_xboole_0(X1,X4)
                          | ~ r2_hidden(X3,X4)
                          | ~ v3_pre_topc(X4,X0)
                          | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) ) )
                    | ~ r2_hidden(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( k2_pre_topc(X0,X1) = X2
              <=> ! [X3] :
                    ( r2_hidden(X3,u1_struct_0(X0))
                   => ( r2_hidden(X3,X2)
                    <=> ! [X4] :
                          ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                         => ~ ( r1_xboole_0(X1,X4)
                              & r2_hidden(X3,X4)
                              & v3_pre_topc(X4,X0) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t34_connsp_2.p',d13_pre_topc)).

fof(f164,plain,
    ( r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | ~ spl11_0 ),
    inference(avatar_component_clause,[],[f163])).

fof(f163,plain,
    ( spl11_0
  <=> r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_0])])).

fof(f785,plain,(
    ! [X2,X3,X1] :
      ( r1_xboole_0(X3,k1_tops_1(X2,X1))
      | ~ r1_xboole_0(X1,X3)
      | ~ l1_pre_topc(X2)
      | ~ r1_tarski(X1,u1_struct_0(X2)) ) ),
    inference(resolution,[],[f406,f128])).

fof(f128,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t34_connsp_2.p',symmetry_r1_xboole_0)).

fof(f406,plain,(
    ! [X6,X8,X7] :
      ( r1_xboole_0(k1_tops_1(X6,X7),X8)
      | ~ r1_tarski(X7,u1_struct_0(X6))
      | ~ r1_xboole_0(X7,X8)
      | ~ l1_pre_topc(X6) ) ),
    inference(resolution,[],[f203,f141])).

fof(f141,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X1,X2)
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f69])).

fof(f69,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t34_connsp_2.p',t63_xboole_1)).

fof(f203,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ l1_pre_topc(X0)
      | ~ r1_tarski(X1,u1_struct_0(X0)) ) ),
    inference(resolution,[],[f109,f138])).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t34_connsp_2.p',t44_tops_1)).

fof(f1540,plain,
    ( spl11_0
    | ~ spl11_13
    | ~ spl11_6 ),
    inference(avatar_split_clause,[],[f1536,f166,f1538,f163])).

fof(f1538,plain,
    ( spl11_13
  <=> ~ r2_hidden(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_13])])).

fof(f166,plain,
    ( spl11_6
  <=> ! [X4] :
        ( ~ r1_xboole_0(X4,sK1)
        | ~ m1_connsp_2(X4,sK0,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).

fof(f1536,plain,
    ( ~ r2_hidden(sK2,u1_struct_0(sK0))
    | r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f1535,f101])).

fof(f1535,plain,
    ( ~ r2_hidden(sK2,u1_struct_0(sK0))
    | r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f1443,f102])).

fof(f1443,plain,
    ( ~ r2_hidden(sK2,u1_struct_0(sK0))
    | r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl11_6 ),
    inference(duplicate_literal_removal,[],[f1442])).

fof(f1442,plain,
    ( ~ r2_hidden(sK2,u1_struct_0(sK0))
    | r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | ~ r2_hidden(sK2,u1_struct_0(sK0))
    | r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl11_6 ),
    inference(resolution,[],[f1441,f312])).

fof(f312,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,sK6(X1,X2,X0))
      | ~ r2_hidden(X0,u1_struct_0(X1))
      | r2_hidden(X0,k2_pre_topc(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1) ) ),
    inference(duplicate_literal_removal,[],[f306])).

fof(f306,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,sK6(X1,X2,X0))
      | ~ r2_hidden(X0,u1_struct_0(X1))
      | r2_hidden(X0,k2_pre_topc(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f147,f133])).

fof(f147,plain,(
    ! [X6,X0,X1] :
      ( ~ m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X6,sK6(X0,X1,X6))
      | ~ r2_hidden(X6,u1_struct_0(X0))
      | r2_hidden(X6,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f113])).

fof(f113,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,X2)
      | r2_hidden(X6,sK6(X0,X1,X6))
      | ~ r2_hidden(X6,u1_struct_0(X0))
      | k2_pre_topc(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f88])).

fof(f1441,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK2,sK6(sK0,sK1,X0))
        | ~ r2_hidden(X0,u1_struct_0(sK0))
        | r2_hidden(X0,k2_pre_topc(sK0,sK1)) )
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f1440,f101])).

fof(f1440,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_pre_topc(sK0,sK1))
        | ~ l1_pre_topc(sK0)
        | ~ r2_hidden(X0,u1_struct_0(sK0))
        | ~ r2_hidden(sK2,sK6(sK0,sK1,X0)) )
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f1439,f102])).

fof(f1439,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_pre_topc(sK0,sK1))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ r2_hidden(X0,u1_struct_0(sK0))
        | ~ r2_hidden(sK2,sK6(sK0,sK1,X0)) )
    | ~ spl11_6 ),
    inference(duplicate_literal_removal,[],[f1437])).

fof(f1437,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_pre_topc(sK0,sK1))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ r2_hidden(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK2,sK6(sK0,sK1,X0))
        | r2_hidden(X0,k2_pre_topc(sK0,sK1))
        | ~ r2_hidden(X0,u1_struct_0(sK0)) )
    | ~ spl11_6 ),
    inference(resolution,[],[f549,f714])).

fof(f714,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(sK6(sK0,X1,X0),sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK2,sK6(sK0,X1,X0))
        | r2_hidden(X0,k2_pre_topc(sK0,X1))
        | ~ r2_hidden(X0,u1_struct_0(sK0)) )
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f713,f99])).

fof(f713,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK2,sK6(sK0,X1,X0))
        | r2_hidden(X0,k2_pre_topc(sK0,X1))
        | v2_struct_0(sK0)
        | ~ r1_xboole_0(sK6(sK0,X1,X0),sK1) )
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f712,f100])).

fof(f712,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK2,sK6(sK0,X1,X0))
        | r2_hidden(X0,k2_pre_topc(sK0,X1))
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ r1_xboole_0(sK6(sK0,X1,X0),sK1) )
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f711,f103])).

fof(f711,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK2,sK6(sK0,X1,X0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | r2_hidden(X0,k2_pre_topc(sK0,X1))
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ r1_xboole_0(sK6(sK0,X1,X0),sK1) )
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f702,f101])).

fof(f702,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ r2_hidden(sK2,sK6(sK0,X1,X0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | r2_hidden(X0,k2_pre_topc(sK0,X1))
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ r1_xboole_0(sK6(sK0,X1,X0),sK1) )
    | ~ spl11_6 ),
    inference(resolution,[],[f348,f167])).

fof(f167,plain,
    ( ! [X4] :
        ( ~ m1_connsp_2(X4,sK0,sK2)
        | ~ r1_xboole_0(X4,sK1) )
    | ~ spl11_6 ),
    inference(avatar_component_clause,[],[f166])).

fof(f348,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_connsp_2(sK6(X1,X2,X0),X1,X3)
      | ~ r2_hidden(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ r2_hidden(X3,sK6(X1,X2,X0))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | r2_hidden(X0,k2_pre_topc(X1,X2))
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f347,f133])).

fof(f347,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,k2_pre_topc(X1,X2))
      | ~ r2_hidden(X0,u1_struct_0(X1))
      | ~ m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ r2_hidden(X3,sK6(X1,X2,X0))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | m1_connsp_2(sK6(X1,X2,X0),X1,X3)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f346,f148])).

fof(f148,plain,(
    ! [X6,X0,X1] :
      ( ~ m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(sK6(X0,X1,X6),X0)
      | ~ r2_hidden(X6,u1_struct_0(X0))
      | r2_hidden(X6,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f112])).

fof(f112,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,X2)
      | v3_pre_topc(sK6(X0,X1,X6),X0)
      | ~ r2_hidden(X6,u1_struct_0(X0))
      | k2_pre_topc(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f88])).

fof(f346,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,k2_pre_topc(X1,X2))
      | ~ r2_hidden(X0,u1_struct_0(X1))
      | ~ m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ r2_hidden(X3,sK6(X1,X2,X0))
      | ~ v3_pre_topc(sK6(X1,X2,X0),X1)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | m1_connsp_2(sK6(X1,X2,X0),X1,X3)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(duplicate_literal_removal,[],[f335])).

fof(f335,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,k2_pre_topc(X1,X2))
      | ~ r2_hidden(X0,u1_struct_0(X1))
      | ~ m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ r2_hidden(X3,sK6(X1,X2,X0))
      | ~ v3_pre_topc(sK6(X1,X2,X0),X1)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | m1_connsp_2(sK6(X1,X2,X0),X1,X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f149,f123])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X2,X1)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | m1_connsp_2(X1,X0,X2)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r2_hidden(X2,X1)
                  & v3_pre_topc(X1,X0) )
               => m1_connsp_2(X1,X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t34_connsp_2.p',t5_connsp_2)).

fof(f149,plain,(
    ! [X6,X0,X1] :
      ( m1_subset_1(sK6(X0,X1,X6),k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X6,k2_pre_topc(X0,X1))
      | ~ r2_hidden(X6,u1_struct_0(X0))
      | ~ m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f111])).

fof(f111,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,X2)
      | m1_subset_1(sK6(X0,X1,X6),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X6,u1_struct_0(X0))
      | k2_pre_topc(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f88])).

fof(f549,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(sK6(X1,X2,X0),X2)
      | r2_hidden(X0,k2_pre_topc(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ r2_hidden(X0,u1_struct_0(X1)) ) ),
    inference(resolution,[],[f305,f128])).

fof(f305,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,sK6(X1,X0,X2))
      | ~ r2_hidden(X2,u1_struct_0(X1))
      | r2_hidden(X2,k2_pre_topc(X1,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1) ) ),
    inference(duplicate_literal_removal,[],[f299])).

fof(f299,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,sK6(X1,X0,X2))
      | ~ r2_hidden(X2,u1_struct_0(X1))
      | r2_hidden(X2,k2_pre_topc(X1,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f146,f133])).

fof(f146,plain,(
    ! [X6,X0,X1] :
      ( ~ m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | r1_xboole_0(X1,sK6(X0,X1,X6))
      | ~ r2_hidden(X6,u1_struct_0(X0))
      | r2_hidden(X6,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f114])).

fof(f114,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,X2)
      | r1_xboole_0(X1,sK6(X0,X1,X6))
      | ~ r2_hidden(X6,u1_struct_0(X0))
      | k2_pre_topc(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f88])).

fof(f1534,plain,(
    ~ spl11_14 ),
    inference(avatar_contradiction_clause,[],[f1533])).

fof(f1533,plain,
    ( $false
    | ~ spl11_14 ),
    inference(subsumption_resolution,[],[f1532,f99])).

fof(f1532,plain,
    ( v2_struct_0(sK0)
    | ~ spl11_14 ),
    inference(subsumption_resolution,[],[f1528,f169])).

fof(f169,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f108,f101])).

fof(f108,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t34_connsp_2.p',dt_l1_pre_topc)).

fof(f1528,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_14 ),
    inference(resolution,[],[f191,f124])).

fof(f124,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t34_connsp_2.p',fc2_struct_0)).

fof(f191,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl11_14 ),
    inference(avatar_component_clause,[],[f190])).

fof(f190,plain,
    ( spl11_14
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_14])])).

fof(f192,plain,
    ( spl11_12
    | spl11_14 ),
    inference(avatar_split_clause,[],[f177,f190,f187])).

fof(f177,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | r2_hidden(sK2,u1_struct_0(sK0)) ),
    inference(resolution,[],[f129,f103])).

fof(f129,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t34_connsp_2.p',t2_subset)).

fof(f168,plain,
    ( spl11_0
    | spl11_6 ),
    inference(avatar_split_clause,[],[f104,f166,f163])).

fof(f104,plain,(
    ! [X4] :
      ( ~ r1_xboole_0(X4,sK1)
      | ~ m1_connsp_2(X4,sK0,sK2)
      | r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f161,plain,
    ( ~ spl11_1
    | spl11_4 ),
    inference(avatar_split_clause,[],[f105,f159,f152])).

fof(f152,plain,
    ( spl11_1
  <=> ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f105,plain,
    ( m1_connsp_2(sK3,sK0,sK2)
    | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ),
    inference(cnf_transformation,[],[f81])).

fof(f157,plain,
    ( ~ spl11_1
    | spl11_2 ),
    inference(avatar_split_clause,[],[f106,f155,f152])).

fof(f106,plain,
    ( r1_xboole_0(sK3,sK1)
    | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ),
    inference(cnf_transformation,[],[f81])).
%------------------------------------------------------------------------------
