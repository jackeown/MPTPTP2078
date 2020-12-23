%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1189+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:27 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  189 (1296 expanded)
%              Number of leaves         :   32 ( 387 expanded)
%              Depth                    :   26
%              Number of atoms          :  770 (12222 expanded)
%              Number of equality atoms :   69 (1708 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f449,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f101,f106,f111,f115,f125,f149,f189,f194,f199,f225,f233,f325,f448])).

fof(f448,plain,
    ( ~ spl4_1
    | spl4_2
    | spl4_3
    | ~ spl4_4
    | spl4_7
    | ~ spl4_8 ),
    inference(avatar_contradiction_clause,[],[f447])).

fof(f447,plain,
    ( $false
    | ~ spl4_1
    | spl4_2
    | spl4_3
    | ~ spl4_4
    | spl4_7
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f446,f416])).

fof(f416,plain,
    ( r2_hidden(sK2,u1_struct_0(sK0))
    | ~ spl4_4
    | spl4_7 ),
    inference(subsumption_resolution,[],[f406,f124])).

fof(f124,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl4_7 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl4_7
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f406,plain,
    ( r2_hidden(sK2,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl4_4 ),
    inference(resolution,[],[f110,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f110,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl4_4
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f446,plain,
    ( ~ r2_hidden(sK2,u1_struct_0(sK0))
    | ~ spl4_1
    | spl4_2
    | spl4_3
    | ~ spl4_4
    | ~ spl4_8 ),
    inference(forward_demodulation,[],[f445,f229])).

fof(f229,plain,(
    u1_struct_0(sK0) = k3_relat_1(u1_orders_2(sK0)) ),
    inference(subsumption_resolution,[],[f228,f128])).

fof(f128,plain,(
    v1_relat_2(u1_orders_2(sK0)) ),
    inference(subsumption_resolution,[],[f126,f63])).

fof(f63,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,
    ( ( ( ~ r2_orders_2(sK0,sK1,sK2)
        & sK1 != sK2
        & m1_subset_1(sK2,u1_struct_0(sK0)) )
      | ~ r9_orders_1(u1_orders_2(sK0),sK1) )
    & ( ! [X3] :
          ( r2_orders_2(sK0,sK1,X3)
          | sK1 = X3
          | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
      | r9_orders_1(u1_orders_2(sK0),sK1) )
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f46,f49,f48,f47])).

fof(f47,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ? [X2] :
                  ( ~ r2_orders_2(X0,X1,X2)
                  & X1 != X2
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ r9_orders_1(u1_orders_2(X0),X1) )
            & ( ! [X3] :
                  ( r2_orders_2(X0,X1,X3)
                  | X1 = X3
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | r9_orders_1(u1_orders_2(X0),X1) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ? [X2] :
                ( ~ r2_orders_2(sK0,X1,X2)
                & X1 != X2
                & m1_subset_1(X2,u1_struct_0(sK0)) )
            | ~ r9_orders_1(u1_orders_2(sK0),X1) )
          & ( ! [X3] :
                ( r2_orders_2(sK0,X1,X3)
                | X1 = X3
                | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
            | r9_orders_1(u1_orders_2(sK0),X1) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ? [X1] :
        ( ( ? [X2] :
              ( ~ r2_orders_2(sK0,X1,X2)
              & X1 != X2
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          | ~ r9_orders_1(u1_orders_2(sK0),X1) )
        & ( ! [X3] :
              ( r2_orders_2(sK0,X1,X3)
              | X1 = X3
              | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
          | r9_orders_1(u1_orders_2(sK0),X1) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ( ? [X2] :
            ( ~ r2_orders_2(sK0,sK1,X2)
            & sK1 != X2
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        | ~ r9_orders_1(u1_orders_2(sK0),sK1) )
      & ( ! [X3] :
            ( r2_orders_2(sK0,sK1,X3)
            | sK1 = X3
            | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
        | r9_orders_1(u1_orders_2(sK0),sK1) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ? [X2] :
        ( ~ r2_orders_2(sK0,sK1,X2)
        & sK1 != X2
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ~ r2_orders_2(sK0,sK1,sK2)
      & sK1 != sK2
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ~ r2_orders_2(X0,X1,X2)
                & X1 != X2
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r9_orders_1(u1_orders_2(X0),X1) )
          & ( ! [X3] :
                ( r2_orders_2(X0,X1,X3)
                | X1 = X3
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            | r9_orders_1(u1_orders_2(X0),X1) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ~ r2_orders_2(X0,X1,X2)
                & X1 != X2
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r9_orders_1(u1_orders_2(X0),X1) )
          & ( ! [X2] :
                ( r2_orders_2(X0,X1,X2)
                | X1 = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | r9_orders_1(u1_orders_2(X0),X1) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ~ r2_orders_2(X0,X1,X2)
                & X1 != X2
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r9_orders_1(u1_orders_2(X0),X1) )
          & ( ! [X2] :
                ( r2_orders_2(X0,X1,X2)
                | X1 = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | r9_orders_1(u1_orders_2(X0),X1) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r9_orders_1(u1_orders_2(X0),X1)
          <~> ! [X2] :
                ( r2_orders_2(X0,X1,X2)
                | X1 = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r9_orders_1(u1_orders_2(X0),X1)
          <~> ! [X2] :
                ( r2_orders_2(X0,X1,X2)
                | X1 = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( r9_orders_1(u1_orders_2(X0),X1)
            <=> ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ( X1 != X2
                   => r2_orders_2(X0,X1,X2) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( r9_orders_1(u1_orders_2(X0),X1)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( X1 != X2
                 => r2_orders_2(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t161_orders_2)).

fof(f126,plain,
    ( v1_relat_2(u1_orders_2(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f60,f90])).

fof(f90,plain,(
    ! [X0] :
      ( v1_relat_2(u1_orders_2(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( v1_relat_2(u1_orders_2(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( v1_relat_2(u1_orders_2(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0) )
     => v1_relat_2(u1_orders_2(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_orders_2)).

fof(f60,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f228,plain,
    ( u1_struct_0(sK0) = k3_relat_1(u1_orders_2(sK0))
    | ~ v1_relat_2(u1_orders_2(sK0)) ),
    inference(subsumption_resolution,[],[f227,f135])).

fof(f135,plain,(
    v4_relat_2(u1_orders_2(sK0)) ),
    inference(subsumption_resolution,[],[f134,f129])).

fof(f129,plain,(
    v2_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f127,f63])).

fof(f127,plain,
    ( v2_orders_2(sK0)
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f60,f79])).

fof(f79,plain,(
    ! [X0] :
      ( v2_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( v2_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( v2_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v3_orders_2(X0)
       => v2_orders_2(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_orders_2)).

fof(f134,plain,
    ( v4_relat_2(u1_orders_2(sK0))
    | ~ v2_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f133,f63])).

fof(f133,plain,
    ( v4_relat_2(u1_orders_2(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v2_orders_2(sK0) ),
    inference(resolution,[],[f62,f77])).

fof(f77,plain,(
    ! [X0] :
      ( v4_relat_2(u1_orders_2(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v2_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( v4_relat_2(u1_orders_2(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v2_orders_2(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( v4_relat_2(u1_orders_2(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v2_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v2_orders_2(X0) )
     => v4_relat_2(u1_orders_2(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_orders_2)).

fof(f62,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f227,plain,
    ( u1_struct_0(sK0) = k3_relat_1(u1_orders_2(sK0))
    | ~ v4_relat_2(u1_orders_2(sK0))
    | ~ v1_relat_2(u1_orders_2(sK0)) ),
    inference(subsumption_resolution,[],[f226,f132])).

fof(f132,plain,(
    v8_relat_2(u1_orders_2(sK0)) ),
    inference(subsumption_resolution,[],[f131,f129])).

fof(f131,plain,
    ( v8_relat_2(u1_orders_2(sK0))
    | ~ v2_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f130,f63])).

fof(f130,plain,
    ( v8_relat_2(u1_orders_2(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v2_orders_2(sK0) ),
    inference(resolution,[],[f61,f78])).

fof(f78,plain,(
    ! [X0] :
      ( v8_relat_2(u1_orders_2(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v2_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( v8_relat_2(u1_orders_2(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v2_orders_2(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( v8_relat_2(u1_orders_2(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v2_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & v2_orders_2(X0) )
     => v8_relat_2(u1_orders_2(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_orders_2)).

fof(f61,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f226,plain,
    ( u1_struct_0(sK0) = k3_relat_1(u1_orders_2(sK0))
    | ~ v8_relat_2(u1_orders_2(sK0))
    | ~ v4_relat_2(u1_orders_2(sK0))
    | ~ v1_relat_2(u1_orders_2(sK0)) ),
    inference(subsumption_resolution,[],[f217,f144])).

fof(f144,plain,(
    m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    inference(resolution,[],[f63,f88])).

fof(f88,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(f217,plain,
    ( u1_struct_0(sK0) = k3_relat_1(u1_orders_2(sK0))
    | ~ m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v8_relat_2(u1_orders_2(sK0))
    | ~ v4_relat_2(u1_orders_2(sK0))
    | ~ v1_relat_2(u1_orders_2(sK0)) ),
    inference(resolution,[],[f150,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v4_relat_2(X1)
      | ~ v1_relat_2(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v4_relat_2(X1)
      | ~ v1_relat_2(X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v4_relat_2(X1)
      | ~ v1_relat_2(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_partfun1(X1,X0)
        & v8_relat_2(X1)
        & v4_relat_2(X1)
        & v1_relat_2(X1) )
     => k3_relat_1(X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_orders_1)).

fof(f150,plain,(
    v1_partfun1(u1_orders_2(sK0),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f145,f129])).

fof(f145,plain,
    ( v1_partfun1(u1_orders_2(sK0),u1_struct_0(sK0))
    | ~ v2_orders_2(sK0) ),
    inference(resolution,[],[f63,f89])).

fof(f89,plain,(
    ! [X0] :
      ( v1_partfun1(u1_orders_2(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( v1_partfun1(u1_orders_2(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_orders_2(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( v1_partfun1(u1_orders_2(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_orders_2(X0) )
     => v1_partfun1(u1_orders_2(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_orders_2)).

fof(f445,plain,
    ( ~ r2_hidden(sK2,k3_relat_1(u1_orders_2(sK0)))
    | ~ spl4_1
    | spl4_2
    | spl4_3
    | ~ spl4_4
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f444,f179])).

fof(f179,plain,
    ( v1_relat_1(u1_orders_2(sK0))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f178])).

fof(f178,plain,
    ( spl4_8
  <=> v1_relat_1(u1_orders_2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f444,plain,
    ( ~ r2_hidden(sK2,k3_relat_1(u1_orders_2(sK0)))
    | ~ v1_relat_1(u1_orders_2(sK0))
    | ~ spl4_1
    | spl4_2
    | spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f443,f95])).

fof(f95,plain,
    ( r9_orders_1(u1_orders_2(sK0),sK1)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl4_1
  <=> r9_orders_1(u1_orders_2(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f443,plain,
    ( ~ r2_hidden(sK2,k3_relat_1(u1_orders_2(sK0)))
    | ~ r9_orders_1(u1_orders_2(sK0),sK1)
    | ~ v1_relat_1(u1_orders_2(sK0))
    | spl4_2
    | spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f441,f105])).

fof(f105,plain,
    ( sK1 != sK2
    | spl4_3 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl4_3
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f441,plain,
    ( sK1 = sK2
    | ~ r2_hidden(sK2,k3_relat_1(u1_orders_2(sK0)))
    | ~ r9_orders_1(u1_orders_2(sK0),sK1)
    | ~ v1_relat_1(u1_orders_2(sK0))
    | spl4_2
    | spl4_3
    | ~ spl4_4 ),
    inference(resolution,[],[f421,f73])).

fof(f73,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(k4_tarski(X1,X3),X0)
      | X1 = X3
      | ~ r2_hidden(X3,k3_relat_1(X0))
      | ~ r9_orders_1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r9_orders_1(X0,X1)
            | ( ~ r2_hidden(k4_tarski(X1,sK3(X0,X1)),X0)
              & sK3(X0,X1) != X1
              & r2_hidden(sK3(X0,X1),k3_relat_1(X0)) )
            | ~ r2_hidden(X1,k3_relat_1(X0)) )
          & ( ( ! [X3] :
                  ( r2_hidden(k4_tarski(X1,X3),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,k3_relat_1(X0)) )
              & r2_hidden(X1,k3_relat_1(X0)) )
            | ~ r9_orders_1(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f55,f56])).

fof(f56,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(k4_tarski(X1,X2),X0)
          & X1 != X2
          & r2_hidden(X2,k3_relat_1(X0)) )
     => ( ~ r2_hidden(k4_tarski(X1,sK3(X0,X1)),X0)
        & sK3(X0,X1) != X1
        & r2_hidden(sK3(X0,X1),k3_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r9_orders_1(X0,X1)
            | ? [X2] :
                ( ~ r2_hidden(k4_tarski(X1,X2),X0)
                & X1 != X2
                & r2_hidden(X2,k3_relat_1(X0)) )
            | ~ r2_hidden(X1,k3_relat_1(X0)) )
          & ( ( ! [X3] :
                  ( r2_hidden(k4_tarski(X1,X3),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,k3_relat_1(X0)) )
              & r2_hidden(X1,k3_relat_1(X0)) )
            | ~ r9_orders_1(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r9_orders_1(X0,X1)
            | ? [X2] :
                ( ~ r2_hidden(k4_tarski(X1,X2),X0)
                & X1 != X2
                & r2_hidden(X2,k3_relat_1(X0)) )
            | ~ r2_hidden(X1,k3_relat_1(X0)) )
          & ( ( ! [X2] :
                  ( r2_hidden(k4_tarski(X1,X2),X0)
                  | X1 = X2
                  | ~ r2_hidden(X2,k3_relat_1(X0)) )
              & r2_hidden(X1,k3_relat_1(X0)) )
            | ~ r9_orders_1(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r9_orders_1(X0,X1)
            | ? [X2] :
                ( ~ r2_hidden(k4_tarski(X1,X2),X0)
                & X1 != X2
                & r2_hidden(X2,k3_relat_1(X0)) )
            | ~ r2_hidden(X1,k3_relat_1(X0)) )
          & ( ( ! [X2] :
                  ( r2_hidden(k4_tarski(X1,X2),X0)
                  | X1 = X2
                  | ~ r2_hidden(X2,k3_relat_1(X0)) )
              & r2_hidden(X1,k3_relat_1(X0)) )
            | ~ r9_orders_1(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r9_orders_1(X0,X1)
        <=> ( ! [X2] :
                ( r2_hidden(k4_tarski(X1,X2),X0)
                | X1 = X2
                | ~ r2_hidden(X2,k3_relat_1(X0)) )
            & r2_hidden(X1,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r9_orders_1(X0,X1)
        <=> ( ! [X2] :
                ( r2_hidden(k4_tarski(X1,X2),X0)
                | X1 = X2
                | ~ r2_hidden(X2,k3_relat_1(X0)) )
            & r2_hidden(X1,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r9_orders_1(X0,X1)
        <=> ( ! [X2] :
                ( r2_hidden(X2,k3_relat_1(X0))
               => ( r2_hidden(k4_tarski(X1,X2),X0)
                  | X1 = X2 ) )
            & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_orders_1)).

fof(f421,plain,
    ( ~ r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0))
    | spl4_2
    | spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f420,f63])).

fof(f420,plain,
    ( ~ r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0))
    | ~ l1_orders_2(sK0)
    | spl4_2
    | spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f419,f64])).

fof(f64,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f50])).

fof(f419,plain,
    ( ~ r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | spl4_2
    | spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f417,f110])).

fof(f417,plain,
    ( ~ r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | spl4_2
    | spl4_3
    | ~ spl4_4 ),
    inference(resolution,[],[f371,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_orders_2(X0,X1,X2)
                  | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
                & ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
                  | ~ r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_orders_2)).

fof(f371,plain,
    ( ~ r1_orders_2(sK0,sK1,sK2)
    | spl4_2
    | spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f370,f63])).

fof(f370,plain,
    ( ~ r1_orders_2(sK0,sK1,sK2)
    | ~ l1_orders_2(sK0)
    | spl4_2
    | spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f369,f64])).

fof(f369,plain,
    ( ~ r1_orders_2(sK0,sK1,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | spl4_2
    | spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f368,f110])).

fof(f368,plain,
    ( ~ r1_orders_2(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | spl4_2
    | spl4_3 ),
    inference(subsumption_resolution,[],[f364,f105])).

fof(f364,plain,
    ( sK1 = sK2
    | ~ r1_orders_2(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | spl4_2 ),
    inference(resolution,[],[f100,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r2_orders_2(X0,X1,X2)
      | X1 = X2
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_orders_2(X0,X1,X2)
                  | X1 = X2
                  | ~ r1_orders_2(X0,X1,X2) )
                & ( ( X1 != X2
                    & r1_orders_2(X0,X1,X2) )
                  | ~ r2_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_orders_2(X0,X1,X2)
                  | X1 = X2
                  | ~ r1_orders_2(X0,X1,X2) )
                & ( ( X1 != X2
                    & r1_orders_2(X0,X1,X2) )
                  | ~ r2_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_orders_2)).

fof(f100,plain,
    ( ~ r2_orders_2(sK0,sK1,sK2)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl4_2
  <=> r2_orders_2(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f325,plain,
    ( ~ spl4_5
    | ~ spl4_10
    | spl4_11
    | spl4_12 ),
    inference(avatar_contradiction_clause,[],[f324])).

fof(f324,plain,
    ( $false
    | ~ spl4_5
    | ~ spl4_10
    | spl4_11
    | spl4_12 ),
    inference(subsumption_resolution,[],[f323,f255])).

fof(f255,plain,
    ( m1_subset_1(sK3(u1_orders_2(sK0),sK1),u1_struct_0(sK0))
    | ~ spl4_10 ),
    inference(resolution,[],[f234,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f234,plain,
    ( r2_hidden(sK3(u1_orders_2(sK0),sK1),u1_struct_0(sK0))
    | ~ spl4_10 ),
    inference(forward_demodulation,[],[f188,f229])).

fof(f188,plain,
    ( r2_hidden(sK3(u1_orders_2(sK0),sK1),k3_relat_1(u1_orders_2(sK0)))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f186])).

fof(f186,plain,
    ( spl4_10
  <=> r2_hidden(sK3(u1_orders_2(sK0),sK1),k3_relat_1(u1_orders_2(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f323,plain,
    ( ~ m1_subset_1(sK3(u1_orders_2(sK0),sK1),u1_struct_0(sK0))
    | ~ spl4_5
    | ~ spl4_10
    | spl4_11
    | spl4_12 ),
    inference(subsumption_resolution,[],[f318,f193])).

fof(f193,plain,
    ( sK1 != sK3(u1_orders_2(sK0),sK1)
    | spl4_11 ),
    inference(avatar_component_clause,[],[f191])).

fof(f191,plain,
    ( spl4_11
  <=> sK1 = sK3(u1_orders_2(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f318,plain,
    ( sK1 = sK3(u1_orders_2(sK0),sK1)
    | ~ m1_subset_1(sK3(u1_orders_2(sK0),sK1),u1_struct_0(sK0))
    | ~ spl4_5
    | ~ spl4_10
    | spl4_12 ),
    inference(resolution,[],[f209,f303])).

fof(f303,plain,
    ( ~ r1_orders_2(sK0,sK1,sK3(u1_orders_2(sK0),sK1))
    | ~ spl4_10
    | spl4_12 ),
    inference(subsumption_resolution,[],[f302,f63])).

fof(f302,plain,
    ( ~ r1_orders_2(sK0,sK1,sK3(u1_orders_2(sK0),sK1))
    | ~ l1_orders_2(sK0)
    | ~ spl4_10
    | spl4_12 ),
    inference(subsumption_resolution,[],[f301,f64])).

fof(f301,plain,
    ( ~ r1_orders_2(sK0,sK1,sK3(u1_orders_2(sK0),sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl4_10
    | spl4_12 ),
    inference(subsumption_resolution,[],[f298,f255])).

fof(f298,plain,
    ( ~ r1_orders_2(sK0,sK1,sK3(u1_orders_2(sK0),sK1))
    | ~ m1_subset_1(sK3(u1_orders_2(sK0),sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | spl4_12 ),
    inference(resolution,[],[f198,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f198,plain,
    ( ~ r2_hidden(k4_tarski(sK1,sK3(u1_orders_2(sK0),sK1)),u1_orders_2(sK0))
    | spl4_12 ),
    inference(avatar_component_clause,[],[f196])).

fof(f196,plain,
    ( spl4_12
  <=> r2_hidden(k4_tarski(sK1,sK3(u1_orders_2(sK0),sK1)),u1_orders_2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f209,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,sK1,X0)
        | sK1 = X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f208,f63])).

fof(f208,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK1 = X0
        | r1_orders_2(sK0,sK1,X0)
        | ~ l1_orders_2(sK0) )
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f206,f64])).

fof(f206,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK1 = X0
        | r1_orders_2(sK0,sK1,X0)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl4_5 ),
    inference(duplicate_literal_removal,[],[f205])).

fof(f205,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK1 = X0
        | r1_orders_2(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl4_5 ),
    inference(resolution,[],[f114,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f114,plain,
    ( ! [X3] :
        ( r2_orders_2(sK0,sK1,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | sK1 = X3 )
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl4_5
  <=> ! [X3] :
        ( r2_orders_2(sK0,sK1,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | sK1 = X3 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f233,plain,
    ( spl4_7
    | spl4_9 ),
    inference(avatar_contradiction_clause,[],[f232])).

fof(f232,plain,
    ( $false
    | spl4_7
    | spl4_9 ),
    inference(subsumption_resolution,[],[f231,f172])).

fof(f172,plain,
    ( r2_hidden(sK1,u1_struct_0(sK0))
    | spl4_7 ),
    inference(subsumption_resolution,[],[f163,f124])).

fof(f163,plain,
    ( r2_hidden(sK1,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f64,f86])).

fof(f231,plain,
    ( ~ r2_hidden(sK1,u1_struct_0(sK0))
    | spl4_9 ),
    inference(forward_demodulation,[],[f184,f229])).

fof(f184,plain,
    ( ~ r2_hidden(sK1,k3_relat_1(u1_orders_2(sK0)))
    | spl4_9 ),
    inference(avatar_component_clause,[],[f182])).

fof(f182,plain,
    ( spl4_9
  <=> r2_hidden(sK1,k3_relat_1(u1_orders_2(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f225,plain,(
    spl4_8 ),
    inference(avatar_contradiction_clause,[],[f224])).

fof(f224,plain,
    ( $false
    | spl4_8 ),
    inference(subsumption_resolution,[],[f222,f63])).

fof(f222,plain,
    ( ~ l1_orders_2(sK0)
    | spl4_8 ),
    inference(resolution,[],[f212,f88])).

fof(f212,plain,
    ( ! [X0,X1] : ~ m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl4_8 ),
    inference(resolution,[],[f180,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f180,plain,
    ( ~ v1_relat_1(u1_orders_2(sK0))
    | spl4_8 ),
    inference(avatar_component_clause,[],[f178])).

fof(f199,plain,
    ( ~ spl4_8
    | ~ spl4_9
    | ~ spl4_12
    | spl4_1 ),
    inference(avatar_split_clause,[],[f176,f94,f196,f182,f178])).

fof(f176,plain,
    ( ~ r2_hidden(k4_tarski(sK1,sK3(u1_orders_2(sK0),sK1)),u1_orders_2(sK0))
    | ~ r2_hidden(sK1,k3_relat_1(u1_orders_2(sK0)))
    | ~ v1_relat_1(u1_orders_2(sK0))
    | spl4_1 ),
    inference(resolution,[],[f96,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r9_orders_1(X0,X1)
      | ~ r2_hidden(k4_tarski(X1,sK3(X0,X1)),X0)
      | ~ r2_hidden(X1,k3_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f96,plain,
    ( ~ r9_orders_1(u1_orders_2(sK0),sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f94])).

fof(f194,plain,
    ( ~ spl4_8
    | ~ spl4_9
    | ~ spl4_11
    | spl4_1 ),
    inference(avatar_split_clause,[],[f175,f94,f191,f182,f178])).

fof(f175,plain,
    ( sK1 != sK3(u1_orders_2(sK0),sK1)
    | ~ r2_hidden(sK1,k3_relat_1(u1_orders_2(sK0)))
    | ~ v1_relat_1(u1_orders_2(sK0))
    | spl4_1 ),
    inference(resolution,[],[f96,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r9_orders_1(X0,X1)
      | sK3(X0,X1) != X1
      | ~ r2_hidden(X1,k3_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f189,plain,
    ( ~ spl4_8
    | ~ spl4_9
    | spl4_10
    | spl4_1 ),
    inference(avatar_split_clause,[],[f174,f94,f186,f182,f178])).

fof(f174,plain,
    ( r2_hidden(sK3(u1_orders_2(sK0),sK1),k3_relat_1(u1_orders_2(sK0)))
    | ~ r2_hidden(sK1,k3_relat_1(u1_orders_2(sK0)))
    | ~ v1_relat_1(u1_orders_2(sK0))
    | spl4_1 ),
    inference(resolution,[],[f96,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r9_orders_1(X0,X1)
      | r2_hidden(sK3(X0,X1),k3_relat_1(X0))
      | ~ r2_hidden(X1,k3_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f149,plain,(
    spl4_6 ),
    inference(avatar_contradiction_clause,[],[f148])).

fof(f148,plain,
    ( $false
    | spl4_6 ),
    inference(subsumption_resolution,[],[f143,f120])).

fof(f120,plain,
    ( ~ l1_struct_0(sK0)
    | spl4_6 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl4_6
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f143,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f63,f87])).

fof(f87,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f125,plain,
    ( ~ spl4_6
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f116,f122,f118])).

fof(f116,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ l1_struct_0(sK0) ),
    inference(resolution,[],[f59,f80])).

fof(f80,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f59,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f115,plain,
    ( spl4_1
    | spl4_5 ),
    inference(avatar_split_clause,[],[f65,f113,f94])).

fof(f65,plain,(
    ! [X3] :
      ( r2_orders_2(sK0,sK1,X3)
      | sK1 = X3
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | r9_orders_1(u1_orders_2(sK0),sK1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f111,plain,
    ( ~ spl4_1
    | spl4_4 ),
    inference(avatar_split_clause,[],[f66,f108,f94])).

fof(f66,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r9_orders_1(u1_orders_2(sK0),sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f106,plain,
    ( ~ spl4_1
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f67,f103,f94])).

fof(f67,plain,
    ( sK1 != sK2
    | ~ r9_orders_1(u1_orders_2(sK0),sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f101,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f68,f98,f94])).

fof(f68,plain,
    ( ~ r2_orders_2(sK0,sK1,sK2)
    | ~ r9_orders_1(u1_orders_2(sK0),sK1) ),
    inference(cnf_transformation,[],[f50])).

%------------------------------------------------------------------------------
