%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : orders_2__t36_orders_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n030.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:19 EDT 2019

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :  315 (1539 expanded)
%              Number of leaves         :   45 ( 501 expanded)
%              Depth                    :   25
%              Number of atoms          : 1308 (14914 expanded)
%              Number of equality atoms :   89 ( 293 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14347,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f174,f181,f183,f212,f241,f254,f5420,f5733,f8193,f8207,f8540,f8555,f8576,f13281,f13489,f13498,f13966,f14006,f14089,f14106,f14179,f14346])).

fof(f14346,plain,
    ( ~ spl11_44
    | spl11_1255
    | ~ spl11_1258
    | ~ spl11_1262 ),
    inference(avatar_contradiction_clause,[],[f14345])).

fof(f14345,plain,
    ( $false
    | ~ spl11_44
    | ~ spl11_1255
    | ~ spl11_1258
    | ~ spl11_1262 ),
    inference(subsumption_resolution,[],[f13821,f291])).

fof(f291,plain,(
    r2_hidden(k4_tarski(sK1,sK1),u1_orders_2(sK0)) ),
    inference(subsumption_resolution,[],[f290,f100])).

fof(f100,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,
    ( ( ( ~ r3_orders_2(sK0,sK2,sK1)
        & ~ r3_orders_2(sK0,sK1,sK2) )
      | ~ m1_subset_1(k7_domain_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v6_orders_2(k7_domain_1(u1_struct_0(sK0),sK1,sK2),sK0) )
    & ( r3_orders_2(sK0,sK2,sK1)
      | r3_orders_2(sK0,sK1,sK2)
      | ( m1_subset_1(k7_domain_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
        & v6_orders_2(k7_domain_1(u1_struct_0(sK0),sK1,sK2),sK0) ) )
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f75,f78,f77,f76])).

fof(f76,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ( ~ r3_orders_2(X0,X2,X1)
                    & ~ r3_orders_2(X0,X1,X2) )
                  | ~ m1_subset_1(k7_domain_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
                  | ~ v6_orders_2(k7_domain_1(u1_struct_0(X0),X1,X2),X0) )
                & ( r3_orders_2(X0,X2,X1)
                  | r3_orders_2(X0,X1,X2)
                  | ( m1_subset_1(k7_domain_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
                    & v6_orders_2(k7_domain_1(u1_struct_0(X0),X1,X2),X0) ) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ( ~ r3_orders_2(sK0,X2,X1)
                  & ~ r3_orders_2(sK0,X1,X2) )
                | ~ m1_subset_1(k7_domain_1(u1_struct_0(sK0),X1,X2),k1_zfmisc_1(u1_struct_0(sK0)))
                | ~ v6_orders_2(k7_domain_1(u1_struct_0(sK0),X1,X2),sK0) )
              & ( r3_orders_2(sK0,X2,X1)
                | r3_orders_2(sK0,X1,X2)
                | ( m1_subset_1(k7_domain_1(u1_struct_0(sK0),X1,X2),k1_zfmisc_1(u1_struct_0(sK0)))
                  & v6_orders_2(k7_domain_1(u1_struct_0(sK0),X1,X2),sK0) ) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f77,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( ~ r3_orders_2(X0,X2,X1)
                  & ~ r3_orders_2(X0,X1,X2) )
                | ~ m1_subset_1(k7_domain_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
                | ~ v6_orders_2(k7_domain_1(u1_struct_0(X0),X1,X2),X0) )
              & ( r3_orders_2(X0,X2,X1)
                | r3_orders_2(X0,X1,X2)
                | ( m1_subset_1(k7_domain_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
                  & v6_orders_2(k7_domain_1(u1_struct_0(X0),X1,X2),X0) ) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ( ( ~ r3_orders_2(X0,X2,sK1)
                & ~ r3_orders_2(X0,sK1,X2) )
              | ~ m1_subset_1(k7_domain_1(u1_struct_0(X0),sK1,X2),k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v6_orders_2(k7_domain_1(u1_struct_0(X0),sK1,X2),X0) )
            & ( r3_orders_2(X0,X2,sK1)
              | r3_orders_2(X0,sK1,X2)
              | ( m1_subset_1(k7_domain_1(u1_struct_0(X0),sK1,X2),k1_zfmisc_1(u1_struct_0(X0)))
                & v6_orders_2(k7_domain_1(u1_struct_0(X0),sK1,X2),X0) ) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK1,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ( ~ r3_orders_2(X0,X2,X1)
              & ~ r3_orders_2(X0,X1,X2) )
            | ~ m1_subset_1(k7_domain_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v6_orders_2(k7_domain_1(u1_struct_0(X0),X1,X2),X0) )
          & ( r3_orders_2(X0,X2,X1)
            | r3_orders_2(X0,X1,X2)
            | ( m1_subset_1(k7_domain_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
              & v6_orders_2(k7_domain_1(u1_struct_0(X0),X1,X2),X0) ) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( ( ~ r3_orders_2(X0,sK2,X1)
            & ~ r3_orders_2(X0,X1,sK2) )
          | ~ m1_subset_1(k7_domain_1(u1_struct_0(X0),X1,sK2),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v6_orders_2(k7_domain_1(u1_struct_0(X0),X1,sK2),X0) )
        & ( r3_orders_2(X0,sK2,X1)
          | r3_orders_2(X0,X1,sK2)
          | ( m1_subset_1(k7_domain_1(u1_struct_0(X0),X1,sK2),k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(k7_domain_1(u1_struct_0(X0),X1,sK2),X0) ) )
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f75,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( ~ r3_orders_2(X0,X2,X1)
                  & ~ r3_orders_2(X0,X1,X2) )
                | ~ m1_subset_1(k7_domain_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
                | ~ v6_orders_2(k7_domain_1(u1_struct_0(X0),X1,X2),X0) )
              & ( r3_orders_2(X0,X2,X1)
                | r3_orders_2(X0,X1,X2)
                | ( m1_subset_1(k7_domain_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
                  & v6_orders_2(k7_domain_1(u1_struct_0(X0),X1,X2),X0) ) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f74])).

fof(f74,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( ~ r3_orders_2(X0,X2,X1)
                  & ~ r3_orders_2(X0,X1,X2) )
                | ~ m1_subset_1(k7_domain_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
                | ~ v6_orders_2(k7_domain_1(u1_struct_0(X0),X1,X2),X0) )
              & ( r3_orders_2(X0,X2,X1)
                | r3_orders_2(X0,X1,X2)
                | ( m1_subset_1(k7_domain_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
                  & v6_orders_2(k7_domain_1(u1_struct_0(X0),X1,X2),X0) ) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( m1_subset_1(k7_domain_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
                  & v6_orders_2(k7_domain_1(u1_struct_0(X0),X1,X2),X0) )
              <~> ( r3_orders_2(X0,X2,X1)
                  | r3_orders_2(X0,X1,X2) ) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( m1_subset_1(k7_domain_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
                  & v6_orders_2(k7_domain_1(u1_struct_0(X0),X1,X2),X0) )
              <~> ( r3_orders_2(X0,X2,X1)
                  | r3_orders_2(X0,X1,X2) ) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( ( m1_subset_1(k7_domain_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
                    & v6_orders_2(k7_domain_1(u1_struct_0(X0),X1,X2),X0) )
                <=> ( r3_orders_2(X0,X2,X1)
                    | r3_orders_2(X0,X1,X2) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( m1_subset_1(k7_domain_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
                  & v6_orders_2(k7_domain_1(u1_struct_0(X0),X1,X2),X0) )
              <=> ( r3_orders_2(X0,X2,X1)
                  | r3_orders_2(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t36_orders_2.p',t36_orders_2)).

fof(f290,plain,
    ( r2_hidden(k4_tarski(sK1,sK1),u1_orders_2(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f288,f101])).

fof(f101,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f79])).

fof(f288,plain,
    ( r2_hidden(k4_tarski(sK1,sK1),u1_orders_2(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(duplicate_literal_removal,[],[f287])).

fof(f287,plain,
    ( r2_hidden(k4_tarski(sK1,sK1),u1_orders_2(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f266,f115])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X1,X2)
      | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f84,plain,(
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
    inference(nnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t36_orders_2.p',d9_orders_2)).

fof(f266,plain,(
    r1_orders_2(sK0,sK1,sK1) ),
    inference(subsumption_resolution,[],[f265,f98])).

fof(f98,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f79])).

fof(f265,plain,
    ( r1_orders_2(sK0,sK1,sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f264,f99])).

fof(f99,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f79])).

fof(f264,plain,
    ( r1_orders_2(sK0,sK1,sK1)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f263,f100])).

fof(f263,plain,
    ( r1_orders_2(sK0,sK1,sK1)
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f262,f101])).

fof(f262,plain,
    ( r1_orders_2(sK0,sK1,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f261])).

fof(f261,plain,
    ( r1_orders_2(sK0,sK1,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f194,f130])).

fof(f130,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_orders_2(X0,X1,X2)
      | r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f88])).

fof(f88,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_orders_2(X0,X1,X2)
          | ~ r1_orders_2(X0,X1,X2) )
        & ( r1_orders_2(X0,X1,X2)
          | ~ r3_orders_2(X0,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t36_orders_2.p',redefinition_r3_orders_2)).

fof(f194,plain,(
    r3_orders_2(sK0,sK1,sK1) ),
    inference(global_subsumption,[],[f185,f193])).

fof(f193,plain,
    ( r3_orders_2(sK0,sK1,sK1)
    | ~ sP9(sK0) ),
    inference(subsumption_resolution,[],[f192,f98])).

fof(f192,plain,
    ( r3_orders_2(sK0,sK1,sK1)
    | v2_struct_0(sK0)
    | ~ sP9(sK0) ),
    inference(subsumption_resolution,[],[f191,f99])).

fof(f191,plain,
    ( r3_orders_2(sK0,sK1,sK1)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ sP9(sK0) ),
    inference(subsumption_resolution,[],[f186,f100])).

fof(f186,plain,
    ( r3_orders_2(sK0,sK1,sK1)
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ sP9(sK0) ),
    inference(resolution,[],[f101,f153])).

fof(f153,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | r3_orders_2(X0,X1,X1)
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ sP9(X0) ) ),
    inference(general_splitting,[],[f129,f152_D])).

fof(f152,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | sP9(X0) ) ),
    inference(cnf_transformation,[],[f152_D])).

fof(f152_D,plain,(
    ! [X0] :
      ( ! [X2] : ~ m1_subset_1(X2,u1_struct_0(X0))
    <=> ~ sP9(X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP9])])).

fof(f129,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r3_orders_2(X0,X1,X1) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t36_orders_2.p',reflexivity_r3_orders_2)).

fof(f185,plain,(
    sP9(sK0) ),
    inference(resolution,[],[f101,f152])).

fof(f13821,plain,
    ( ~ r2_hidden(k4_tarski(sK1,sK1),u1_orders_2(sK0))
    | ~ spl11_44
    | ~ spl11_1255
    | ~ spl11_1258
    | ~ spl11_1262 ),
    inference(forward_demodulation,[],[f13820,f8367])).

fof(f8367,plain,
    ( sK1 = sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | ~ spl11_1258 ),
    inference(avatar_component_clause,[],[f8366])).

fof(f8366,plain,
    ( spl11_1258
  <=> sK1 = sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1258])])).

fof(f13820,plain,
    ( ~ r2_hidden(k4_tarski(sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2)),sK1),u1_orders_2(sK0))
    | ~ spl11_44
    | ~ spl11_1255
    | ~ spl11_1262 ),
    inference(subsumption_resolution,[],[f13819,f483])).

fof(f483,plain,
    ( v1_relat_1(u1_orders_2(sK0))
    | ~ spl11_44 ),
    inference(avatar_component_clause,[],[f482])).

fof(f482,plain,
    ( spl11_44
  <=> v1_relat_1(u1_orders_2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_44])])).

fof(f13819,plain,
    ( ~ r2_hidden(k4_tarski(sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2)),sK1),u1_orders_2(sK0))
    | ~ v1_relat_1(u1_orders_2(sK0))
    | ~ spl11_1255
    | ~ spl11_1262 ),
    inference(subsumption_resolution,[],[f13817,f8206])).

fof(f8206,plain,
    ( ~ r7_relat_2(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | ~ spl11_1255 ),
    inference(avatar_component_clause,[],[f8205])).

fof(f8205,plain,
    ( spl11_1255
  <=> ~ r7_relat_2(u1_orders_2(sK0),k2_tarski(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1255])])).

fof(f13817,plain,
    ( ~ r2_hidden(k4_tarski(sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2)),sK1),u1_orders_2(sK0))
    | r7_relat_2(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | ~ v1_relat_1(u1_orders_2(sK0))
    | ~ spl11_1262 ),
    inference(superposition,[],[f111,f8392])).

fof(f8392,plain,
    ( sK1 = sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | ~ spl11_1262 ),
    inference(avatar_component_clause,[],[f8391])).

fof(f8391,plain,
    ( spl11_1262
  <=> sK1 = sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1262])])).

fof(f111,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0)
      | r7_relat_2(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f83,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r7_relat_2(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0)
              & ~ r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0)
              & r2_hidden(sK4(X0,X1),X1)
              & r2_hidden(sK3(X0,X1),X1) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X5,X4),X0)
                | r2_hidden(k4_tarski(X4,X5),X0)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X1) )
            | ~ r7_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f81,f82])).

fof(f82,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(k4_tarski(X3,X2),X0)
          & ~ r2_hidden(k4_tarski(X2,X3),X0)
          & r2_hidden(X3,X1)
          & r2_hidden(X2,X1) )
     => ( ~ r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0)
        & ~ r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0)
        & r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f81,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r7_relat_2(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                & ~ r2_hidden(k4_tarski(X2,X3),X0)
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X5,X4),X0)
                | r2_hidden(k4_tarski(X4,X5),X0)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X1) )
            | ~ r7_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f80])).

fof(f80,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r7_relat_2(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                & ~ r2_hidden(k4_tarski(X2,X3),X0)
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) ) )
          & ( ! [X2,X3] :
                ( r2_hidden(k4_tarski(X3,X2),X0)
                | r2_hidden(k4_tarski(X2,X3),X0)
                | ~ r2_hidden(X3,X1)
                | ~ r2_hidden(X2,X1) )
            | ~ r7_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r7_relat_2(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r7_relat_2(X0,X1)
        <=> ! [X2,X3] :
              ~ ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                & ~ r2_hidden(k4_tarski(X2,X3),X0)
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t36_orders_2.p',d7_relat_2)).

fof(f14179,plain,
    ( spl11_1256
    | spl11_1258
    | ~ spl11_44
    | spl11_1255 ),
    inference(avatar_split_clause,[],[f14172,f8205,f482,f8366,f8360])).

fof(f8360,plain,
    ( spl11_1256
  <=> sK2 = sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1256])])).

fof(f14172,plain,
    ( sK1 = sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | sK2 = sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | ~ spl11_44
    | ~ spl11_1255 ),
    inference(resolution,[],[f13687,f151])).

fof(f151,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_tarski(X0,X1))
      | X0 = X4
      | X1 = X4 ) ),
    inference(equality_resolution,[],[f136])).

fof(f136,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f93])).

fof(f93,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK6(X0,X1,X2) != X1
              & sK6(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( sK6(X0,X1,X2) = X1
            | sK6(X0,X1,X2) = X0
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f91,f92])).

fof(f92,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK6(X0,X1,X2) != X1
            & sK6(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( sK6(X0,X1,X2) = X1
          | sK6(X0,X1,X2) = X0
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f91,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f90])).

fof(f90,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f89])).

fof(f89,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t36_orders_2.p',d2_tarski)).

fof(f13687,plain,
    ( r2_hidden(sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2)),k2_tarski(sK1,sK2))
    | ~ spl11_44
    | ~ spl11_1255 ),
    inference(subsumption_resolution,[],[f13685,f483])).

fof(f13685,plain,
    ( r2_hidden(sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2)),k2_tarski(sK1,sK2))
    | ~ v1_relat_1(u1_orders_2(sK0))
    | ~ spl11_1255 ),
    inference(resolution,[],[f8206,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( r7_relat_2(X0,X1)
      | r2_hidden(sK3(X0,X1),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f14106,plain,
    ( ~ spl11_4
    | ~ spl11_44
    | spl11_1255
    | ~ spl11_1256
    | ~ spl11_1262 ),
    inference(avatar_contradiction_clause,[],[f14105])).

fof(f14105,plain,
    ( $false
    | ~ spl11_4
    | ~ spl11_44
    | ~ spl11_1255
    | ~ spl11_1256
    | ~ spl11_1262 ),
    inference(subsumption_resolution,[],[f14104,f100])).

fof(f14104,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl11_4
    | ~ spl11_44
    | ~ spl11_1255
    | ~ spl11_1256
    | ~ spl11_1262 ),
    inference(subsumption_resolution,[],[f14103,f102])).

fof(f102,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f79])).

fof(f14103,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl11_4
    | ~ spl11_44
    | ~ spl11_1255
    | ~ spl11_1256
    | ~ spl11_1262 ),
    inference(subsumption_resolution,[],[f14102,f101])).

fof(f14102,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl11_4
    | ~ spl11_44
    | ~ spl11_1255
    | ~ spl11_1256
    | ~ spl11_1262 ),
    inference(subsumption_resolution,[],[f14101,f13859])).

fof(f13859,plain,
    ( ~ r2_hidden(k4_tarski(sK2,sK1),u1_orders_2(sK0))
    | ~ spl11_44
    | ~ spl11_1255
    | ~ spl11_1256
    | ~ spl11_1262 ),
    inference(forward_demodulation,[],[f13858,f8392])).

fof(f13858,plain,
    ( ~ r2_hidden(k4_tarski(sK2,sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2))),u1_orders_2(sK0))
    | ~ spl11_44
    | ~ spl11_1255
    | ~ spl11_1256 ),
    inference(subsumption_resolution,[],[f13857,f483])).

fof(f13857,plain,
    ( ~ r2_hidden(k4_tarski(sK2,sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2))),u1_orders_2(sK0))
    | ~ v1_relat_1(u1_orders_2(sK0))
    | ~ spl11_1255
    | ~ spl11_1256 ),
    inference(subsumption_resolution,[],[f13855,f8206])).

fof(f13855,plain,
    ( ~ r2_hidden(k4_tarski(sK2,sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2))),u1_orders_2(sK0))
    | r7_relat_2(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | ~ v1_relat_1(u1_orders_2(sK0))
    | ~ spl11_1256 ),
    inference(superposition,[],[f111,f8361])).

fof(f8361,plain,
    ( sK2 = sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | ~ spl11_1256 ),
    inference(avatar_component_clause,[],[f8360])).

fof(f14101,plain,
    ( r2_hidden(k4_tarski(sK2,sK1),u1_orders_2(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl11_4 ),
    inference(resolution,[],[f260,f115])).

fof(f260,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f259,f98])).

fof(f259,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | v2_struct_0(sK0)
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f258,f99])).

fof(f258,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f257,f100])).

fof(f257,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f256,f102])).

fof(f256,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f255,f101])).

fof(f255,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_4 ),
    inference(resolution,[],[f170,f130])).

fof(f170,plain,
    ( r3_orders_2(sK0,sK2,sK1)
    | ~ spl11_4 ),
    inference(avatar_component_clause,[],[f169])).

fof(f169,plain,
    ( spl11_4
  <=> r3_orders_2(sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f14089,plain,
    ( ~ spl11_6
    | ~ spl11_44
    | spl11_1255
    | ~ spl11_1256
    | ~ spl11_1262 ),
    inference(avatar_contradiction_clause,[],[f14088])).

fof(f14088,plain,
    ( $false
    | ~ spl11_6
    | ~ spl11_44
    | ~ spl11_1255
    | ~ spl11_1256
    | ~ spl11_1262 ),
    inference(subsumption_resolution,[],[f13864,f13989])).

fof(f13989,plain,
    ( r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0))
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f13988,f100])).

fof(f13988,plain,
    ( r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f13987,f101])).

fof(f13987,plain,
    ( r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f13986,f102])).

fof(f13986,plain,
    ( r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl11_6 ),
    inference(resolution,[],[f1180,f115])).

fof(f1180,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f1179,f98])).

fof(f1179,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | v2_struct_0(sK0)
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f1178,f99])).

fof(f1178,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f1177,f100])).

fof(f1177,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f1176,f101])).

fof(f1176,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f1175,f102])).

fof(f1175,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_6 ),
    inference(resolution,[],[f177,f130])).

fof(f177,plain,
    ( r3_orders_2(sK0,sK1,sK2)
    | ~ spl11_6 ),
    inference(avatar_component_clause,[],[f176])).

fof(f176,plain,
    ( spl11_6
  <=> r3_orders_2(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).

fof(f13864,plain,
    ( ~ r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0))
    | ~ spl11_44
    | ~ spl11_1255
    | ~ spl11_1256
    | ~ spl11_1262 ),
    inference(forward_demodulation,[],[f13863,f8392])).

fof(f13863,plain,
    ( ~ r2_hidden(k4_tarski(sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2)),sK2),u1_orders_2(sK0))
    | ~ spl11_44
    | ~ spl11_1255
    | ~ spl11_1256 ),
    inference(subsumption_resolution,[],[f13862,f483])).

fof(f13862,plain,
    ( ~ r2_hidden(k4_tarski(sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2)),sK2),u1_orders_2(sK0))
    | ~ v1_relat_1(u1_orders_2(sK0))
    | ~ spl11_1255
    | ~ spl11_1256 ),
    inference(subsumption_resolution,[],[f13856,f8206])).

fof(f13856,plain,
    ( ~ r2_hidden(k4_tarski(sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2)),sK2),u1_orders_2(sK0))
    | r7_relat_2(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | ~ v1_relat_1(u1_orders_2(sK0))
    | ~ spl11_1256 ),
    inference(superposition,[],[f112,f8361])).

fof(f112,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0)
      | r7_relat_2(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f14006,plain,
    ( spl11_1260
    | spl11_1262
    | ~ spl11_44
    | spl11_1255 ),
    inference(avatar_split_clause,[],[f13999,f8205,f482,f8391,f8385])).

fof(f8385,plain,
    ( spl11_1260
  <=> sK2 = sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1260])])).

fof(f13999,plain,
    ( sK1 = sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | sK2 = sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | ~ spl11_44
    | ~ spl11_1255 ),
    inference(resolution,[],[f13688,f151])).

fof(f13688,plain,
    ( r2_hidden(sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2)),k2_tarski(sK1,sK2))
    | ~ spl11_44
    | ~ spl11_1255 ),
    inference(subsumption_resolution,[],[f13686,f483])).

fof(f13686,plain,
    ( r2_hidden(sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2)),k2_tarski(sK1,sK2))
    | ~ v1_relat_1(u1_orders_2(sK0))
    | ~ spl11_1255 ),
    inference(resolution,[],[f8206,f110])).

fof(f110,plain,(
    ! [X0,X1] :
      ( r7_relat_2(X0,X1)
      | r2_hidden(sK4(X0,X1),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f13966,plain,
    ( ~ spl11_4
    | ~ spl11_44
    | spl11_1255
    | ~ spl11_1258
    | ~ spl11_1260 ),
    inference(avatar_contradiction_clause,[],[f13965])).

fof(f13965,plain,
    ( $false
    | ~ spl11_4
    | ~ spl11_44
    | ~ spl11_1255
    | ~ spl11_1258
    | ~ spl11_1260 ),
    inference(subsumption_resolution,[],[f8558,f13874])).

fof(f13874,plain,
    ( r2_hidden(k4_tarski(sK2,sK1),u1_orders_2(sK0))
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f13873,f100])).

fof(f13873,plain,
    ( r2_hidden(k4_tarski(sK2,sK1),u1_orders_2(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f13872,f102])).

fof(f13872,plain,
    ( r2_hidden(k4_tarski(sK2,sK1),u1_orders_2(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f13871,f101])).

fof(f13871,plain,
    ( r2_hidden(k4_tarski(sK2,sK1),u1_orders_2(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl11_4 ),
    inference(resolution,[],[f260,f115])).

fof(f8558,plain,
    ( ~ r2_hidden(k4_tarski(sK2,sK1),u1_orders_2(sK0))
    | ~ spl11_44
    | ~ spl11_1255
    | ~ spl11_1258
    | ~ spl11_1260 ),
    inference(forward_demodulation,[],[f8557,f8386])).

fof(f8386,plain,
    ( sK2 = sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | ~ spl11_1260 ),
    inference(avatar_component_clause,[],[f8385])).

fof(f8557,plain,
    ( ~ r2_hidden(k4_tarski(sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2)),sK1),u1_orders_2(sK0))
    | ~ spl11_44
    | ~ spl11_1255
    | ~ spl11_1258 ),
    inference(subsumption_resolution,[],[f8556,f483])).

fof(f8556,plain,
    ( ~ r2_hidden(k4_tarski(sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2)),sK1),u1_orders_2(sK0))
    | ~ v1_relat_1(u1_orders_2(sK0))
    | ~ spl11_1255
    | ~ spl11_1258 ),
    inference(subsumption_resolution,[],[f8550,f8206])).

fof(f8550,plain,
    ( ~ r2_hidden(k4_tarski(sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2)),sK1),u1_orders_2(sK0))
    | r7_relat_2(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | ~ v1_relat_1(u1_orders_2(sK0))
    | ~ spl11_1258 ),
    inference(superposition,[],[f112,f8367])).

fof(f13498,plain,
    ( spl11_5
    | ~ spl11_1678 ),
    inference(avatar_contradiction_clause,[],[f13497])).

fof(f13497,plain,
    ( $false
    | ~ spl11_5
    | ~ spl11_1678 ),
    inference(subsumption_resolution,[],[f13496,f98])).

fof(f13496,plain,
    ( v2_struct_0(sK0)
    | ~ spl11_5
    | ~ spl11_1678 ),
    inference(subsumption_resolution,[],[f13495,f99])).

fof(f13495,plain,
    ( ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_5
    | ~ spl11_1678 ),
    inference(subsumption_resolution,[],[f13494,f100])).

fof(f13494,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_5
    | ~ spl11_1678 ),
    inference(subsumption_resolution,[],[f13493,f102])).

fof(f13493,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_5
    | ~ spl11_1678 ),
    inference(subsumption_resolution,[],[f13492,f101])).

fof(f13492,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_5
    | ~ spl11_1678 ),
    inference(subsumption_resolution,[],[f13490,f173])).

fof(f173,plain,
    ( ~ r3_orders_2(sK0,sK2,sK1)
    | ~ spl11_5 ),
    inference(avatar_component_clause,[],[f172])).

fof(f172,plain,
    ( spl11_5
  <=> ~ r3_orders_2(sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).

fof(f13490,plain,
    ( r3_orders_2(sK0,sK2,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_1678 ),
    inference(resolution,[],[f13274,f131])).

fof(f131,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X1,X2)
      | r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f88])).

fof(f13274,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | ~ spl11_1678 ),
    inference(avatar_component_clause,[],[f13273])).

fof(f13273,plain,
    ( spl11_1678
  <=> r1_orders_2(sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1678])])).

fof(f13489,plain,
    ( spl11_7
    | ~ spl11_1680 ),
    inference(avatar_contradiction_clause,[],[f13488])).

fof(f13488,plain,
    ( $false
    | ~ spl11_7
    | ~ spl11_1680 ),
    inference(subsumption_resolution,[],[f13487,f98])).

fof(f13487,plain,
    ( v2_struct_0(sK0)
    | ~ spl11_7
    | ~ spl11_1680 ),
    inference(subsumption_resolution,[],[f13486,f99])).

fof(f13486,plain,
    ( ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_7
    | ~ spl11_1680 ),
    inference(subsumption_resolution,[],[f13485,f100])).

fof(f13485,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_7
    | ~ spl11_1680 ),
    inference(subsumption_resolution,[],[f13484,f101])).

fof(f13484,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_7
    | ~ spl11_1680 ),
    inference(subsumption_resolution,[],[f13483,f102])).

fof(f13483,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_7
    | ~ spl11_1680 ),
    inference(subsumption_resolution,[],[f13481,f180])).

fof(f180,plain,
    ( ~ r3_orders_2(sK0,sK1,sK2)
    | ~ spl11_7 ),
    inference(avatar_component_clause,[],[f179])).

fof(f179,plain,
    ( spl11_7
  <=> ~ r3_orders_2(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).

fof(f13481,plain,
    ( r3_orders_2(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_1680 ),
    inference(resolution,[],[f13480,f131])).

fof(f13480,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | ~ spl11_1680 ),
    inference(subsumption_resolution,[],[f13479,f100])).

fof(f13479,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | ~ l1_orders_2(sK0)
    | ~ spl11_1680 ),
    inference(subsumption_resolution,[],[f13478,f101])).

fof(f13478,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl11_1680 ),
    inference(subsumption_resolution,[],[f13470,f102])).

fof(f13470,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl11_1680 ),
    inference(resolution,[],[f13280,f116])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f13280,plain,
    ( r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0))
    | ~ spl11_1680 ),
    inference(avatar_component_clause,[],[f13279])).

fof(f13279,plain,
    ( spl11_1680
  <=> r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1680])])).

fof(f13281,plain,
    ( spl11_1678
    | spl11_1680
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_22
    | ~ spl11_44 ),
    inference(avatar_split_clause,[],[f13265,f482,f239,f163,f157,f13279,f13273])).

fof(f157,plain,
    ( spl11_0
  <=> v6_orders_2(k7_domain_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_0])])).

fof(f163,plain,
    ( spl11_2
  <=> m1_subset_1(k7_domain_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f239,plain,
    ( spl11_22
  <=> ! [X3] :
        ( k7_domain_1(u1_struct_0(sK0),X3,sK2) = k2_tarski(X3,sK2)
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_22])])).

fof(f13265,plain,
    ( r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0))
    | r1_orders_2(sK0,sK2,sK1)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_22
    | ~ spl11_44 ),
    inference(resolution,[],[f8686,f150])).

fof(f150,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_tarski(X4,X1)) ),
    inference(equality_resolution,[],[f149])).

fof(f149,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f137])).

fof(f137,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f93])).

fof(f8686,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_tarski(sK1,sK2))
        | r2_hidden(k4_tarski(X0,sK2),u1_orders_2(sK0))
        | r1_orders_2(sK0,sK2,X0) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_22
    | ~ spl11_44 ),
    inference(resolution,[],[f8598,f148])).

fof(f148,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_tarski(X0,X4)) ),
    inference(equality_resolution,[],[f147])).

fof(f147,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f138])).

fof(f138,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f93])).

fof(f8598,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k2_tarski(sK1,sK2))
        | ~ r2_hidden(X0,k2_tarski(sK1,sK2))
        | r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0))
        | r1_orders_2(sK0,X1,X0) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_22
    | ~ spl11_44 ),
    inference(subsumption_resolution,[],[f8597,f7407])).

fof(f7407,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,k2_tarski(sK1,sK2))
        | m1_subset_1(X4,u1_struct_0(sK0)) )
    | ~ spl11_2
    | ~ spl11_22 ),
    inference(resolution,[],[f7322,f135])).

fof(f135,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f67])).

fof(f67,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t36_orders_2.p',t4_subset)).

fof(f7322,plain,
    ( m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl11_2
    | ~ spl11_22 ),
    inference(forward_demodulation,[],[f164,f308])).

fof(f308,plain,
    ( k7_domain_1(u1_struct_0(sK0),sK1,sK2) = k2_tarski(sK1,sK2)
    | ~ spl11_22 ),
    inference(resolution,[],[f240,f101])).

fof(f240,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | k7_domain_1(u1_struct_0(sK0),X3,sK2) = k2_tarski(X3,sK2) )
    | ~ spl11_22 ),
    inference(avatar_component_clause,[],[f239])).

fof(f164,plain,
    ( m1_subset_1(k7_domain_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl11_2 ),
    inference(avatar_component_clause,[],[f163])).

fof(f8597,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0))
        | ~ r2_hidden(X0,k2_tarski(sK1,sK2))
        | ~ r2_hidden(X1,k2_tarski(sK1,sK2))
        | r1_orders_2(sK0,X1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_22
    | ~ spl11_44 ),
    inference(subsumption_resolution,[],[f8596,f7407])).

fof(f8596,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0))
        | ~ r2_hidden(X0,k2_tarski(sK1,sK2))
        | ~ r2_hidden(X1,k2_tarski(sK1,sK2))
        | r1_orders_2(sK0,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_22
    | ~ spl11_44 ),
    inference(subsumption_resolution,[],[f8580,f100])).

fof(f8580,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0))
        | ~ r2_hidden(X0,k2_tarski(sK1,sK2))
        | ~ r2_hidden(X1,k2_tarski(sK1,sK2))
        | r1_orders_2(sK0,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_22
    | ~ spl11_44 ),
    inference(resolution,[],[f8579,f116])).

fof(f8579,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(X1,X0),u1_orders_2(sK0))
        | r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0))
        | ~ r2_hidden(X0,k2_tarski(sK1,sK2))
        | ~ r2_hidden(X1,k2_tarski(sK1,sK2)) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_22
    | ~ spl11_44 ),
    inference(subsumption_resolution,[],[f8578,f483])).

fof(f8578,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0))
        | ~ r2_hidden(X1,k2_tarski(sK1,sK2))
        | ~ r2_hidden(X0,k2_tarski(sK1,sK2))
        | r2_hidden(k4_tarski(X1,X0),u1_orders_2(sK0))
        | ~ v1_relat_1(u1_orders_2(sK0)) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_22 ),
    inference(resolution,[],[f7434,f108])).

fof(f108,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ r7_relat_2(X0,X1)
      | r2_hidden(k4_tarski(X4,X5),X0)
      | ~ r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(k4_tarski(X5,X4),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f7434,plain,
    ( r7_relat_2(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_22 ),
    inference(subsumption_resolution,[],[f7433,f100])).

fof(f7433,plain,
    ( r7_relat_2(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | ~ l1_orders_2(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_22 ),
    inference(subsumption_resolution,[],[f7403,f7323])).

fof(f7323,plain,
    ( v6_orders_2(k2_tarski(sK1,sK2),sK0)
    | ~ spl11_0
    | ~ spl11_22 ),
    inference(forward_demodulation,[],[f158,f308])).

fof(f158,plain,
    ( v6_orders_2(k7_domain_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | ~ spl11_0 ),
    inference(avatar_component_clause,[],[f157])).

fof(f7403,plain,
    ( ~ v6_orders_2(k2_tarski(sK1,sK2),sK0)
    | r7_relat_2(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | ~ l1_orders_2(sK0)
    | ~ spl11_2
    | ~ spl11_22 ),
    inference(resolution,[],[f7322,f117])).

fof(f117,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v6_orders_2(X1,X0)
      | r7_relat_2(u1_orders_2(X0),X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f85])).

fof(f85,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v6_orders_2(X1,X0)
              | ~ r7_relat_2(u1_orders_2(X0),X1) )
            & ( r7_relat_2(u1_orders_2(X0),X1)
              | ~ v6_orders_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v6_orders_2(X1,X0)
          <=> r7_relat_2(u1_orders_2(X0),X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v6_orders_2(X1,X0)
          <=> r7_relat_2(u1_orders_2(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t36_orders_2.p',d11_orders_2)).

fof(f8576,plain,
    ( spl11_1
    | ~ spl11_22
    | ~ spl11_1252 ),
    inference(avatar_contradiction_clause,[],[f8575])).

fof(f8575,plain,
    ( $false
    | ~ spl11_1
    | ~ spl11_22
    | ~ spl11_1252 ),
    inference(subsumption_resolution,[],[f8200,f501])).

fof(f501,plain,
    ( ~ v6_orders_2(k2_tarski(sK1,sK2),sK0)
    | ~ spl11_1
    | ~ spl11_22 ),
    inference(backward_demodulation,[],[f308,f161])).

fof(f161,plain,
    ( ~ v6_orders_2(k7_domain_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | ~ spl11_1 ),
    inference(avatar_component_clause,[],[f160])).

fof(f160,plain,
    ( spl11_1
  <=> ~ v6_orders_2(k7_domain_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f8200,plain,
    ( v6_orders_2(k2_tarski(sK1,sK2),sK0)
    | ~ spl11_1252 ),
    inference(avatar_component_clause,[],[f8199])).

fof(f8199,plain,
    ( spl11_1252
  <=> v6_orders_2(k2_tarski(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1252])])).

fof(f8555,plain,
    ( ~ spl11_6
    | ~ spl11_44
    | spl11_1255
    | ~ spl11_1258
    | ~ spl11_1260 ),
    inference(avatar_contradiction_clause,[],[f8554])).

fof(f8554,plain,
    ( $false
    | ~ spl11_6
    | ~ spl11_44
    | ~ spl11_1255
    | ~ spl11_1258
    | ~ spl11_1260 ),
    inference(subsumption_resolution,[],[f8553,f7704])).

fof(f7704,plain,
    ( r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0))
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f7703,f100])).

fof(f7703,plain,
    ( r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f7702,f101])).

fof(f7702,plain,
    ( r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f7701,f102])).

fof(f7701,plain,
    ( r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl11_6 ),
    inference(resolution,[],[f1180,f115])).

fof(f8553,plain,
    ( ~ r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0))
    | ~ spl11_44
    | ~ spl11_1255
    | ~ spl11_1258
    | ~ spl11_1260 ),
    inference(forward_demodulation,[],[f8552,f8386])).

fof(f8552,plain,
    ( ~ r2_hidden(k4_tarski(sK1,sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2))),u1_orders_2(sK0))
    | ~ spl11_44
    | ~ spl11_1255
    | ~ spl11_1258 ),
    inference(subsumption_resolution,[],[f8551,f483])).

fof(f8551,plain,
    ( ~ r2_hidden(k4_tarski(sK1,sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2))),u1_orders_2(sK0))
    | ~ v1_relat_1(u1_orders_2(sK0))
    | ~ spl11_1255
    | ~ spl11_1258 ),
    inference(subsumption_resolution,[],[f8549,f8206])).

fof(f8549,plain,
    ( ~ r2_hidden(k4_tarski(sK1,sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2))),u1_orders_2(sK0))
    | r7_relat_2(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | ~ v1_relat_1(u1_orders_2(sK0))
    | ~ spl11_1258 ),
    inference(superposition,[],[f111,f8367])).

fof(f8540,plain,
    ( ~ spl11_44
    | spl11_1255
    | ~ spl11_1256
    | ~ spl11_1260 ),
    inference(avatar_contradiction_clause,[],[f8539])).

fof(f8539,plain,
    ( $false
    | ~ spl11_44
    | ~ spl11_1255
    | ~ spl11_1256
    | ~ spl11_1260 ),
    inference(subsumption_resolution,[],[f8538,f297])).

fof(f297,plain,(
    r2_hidden(k4_tarski(sK2,sK2),u1_orders_2(sK0)) ),
    inference(subsumption_resolution,[],[f296,f100])).

fof(f296,plain,
    ( r2_hidden(k4_tarski(sK2,sK2),u1_orders_2(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f294,f102])).

fof(f294,plain,
    ( r2_hidden(k4_tarski(sK2,sK2),u1_orders_2(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(duplicate_literal_removal,[],[f293])).

fof(f293,plain,
    ( r2_hidden(k4_tarski(sK2,sK2),u1_orders_2(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f276,f115])).

fof(f276,plain,(
    r1_orders_2(sK0,sK2,sK2) ),
    inference(subsumption_resolution,[],[f275,f98])).

fof(f275,plain,
    ( r1_orders_2(sK0,sK2,sK2)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f274,f99])).

fof(f274,plain,
    ( r1_orders_2(sK0,sK2,sK2)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f273,f100])).

fof(f273,plain,
    ( r1_orders_2(sK0,sK2,sK2)
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f272,f102])).

fof(f272,plain,
    ( r1_orders_2(sK0,sK2,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f271])).

fof(f271,plain,
    ( r1_orders_2(sK0,sK2,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f229,f130])).

fof(f229,plain,(
    r3_orders_2(sK0,sK2,sK2) ),
    inference(global_subsumption,[],[f220,f228])).

fof(f228,plain,
    ( r3_orders_2(sK0,sK2,sK2)
    | ~ sP9(sK0) ),
    inference(subsumption_resolution,[],[f227,f98])).

fof(f227,plain,
    ( r3_orders_2(sK0,sK2,sK2)
    | v2_struct_0(sK0)
    | ~ sP9(sK0) ),
    inference(subsumption_resolution,[],[f226,f99])).

fof(f226,plain,
    ( r3_orders_2(sK0,sK2,sK2)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ sP9(sK0) ),
    inference(subsumption_resolution,[],[f221,f100])).

fof(f221,plain,
    ( r3_orders_2(sK0,sK2,sK2)
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ sP9(sK0) ),
    inference(resolution,[],[f102,f153])).

fof(f220,plain,(
    sP9(sK0) ),
    inference(resolution,[],[f102,f152])).

fof(f8538,plain,
    ( ~ r2_hidden(k4_tarski(sK2,sK2),u1_orders_2(sK0))
    | ~ spl11_44
    | ~ spl11_1255
    | ~ spl11_1256
    | ~ spl11_1260 ),
    inference(forward_demodulation,[],[f8537,f8361])).

fof(f8537,plain,
    ( ~ r2_hidden(k4_tarski(sK2,sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2))),u1_orders_2(sK0))
    | ~ spl11_44
    | ~ spl11_1255
    | ~ spl11_1260 ),
    inference(subsumption_resolution,[],[f8536,f483])).

fof(f8536,plain,
    ( ~ r2_hidden(k4_tarski(sK2,sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2))),u1_orders_2(sK0))
    | ~ v1_relat_1(u1_orders_2(sK0))
    | ~ spl11_1255
    | ~ spl11_1260 ),
    inference(subsumption_resolution,[],[f8530,f8206])).

fof(f8530,plain,
    ( ~ r2_hidden(k4_tarski(sK2,sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2))),u1_orders_2(sK0))
    | r7_relat_2(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | ~ v1_relat_1(u1_orders_2(sK0))
    | ~ spl11_1260 ),
    inference(superposition,[],[f112,f8386])).

fof(f8207,plain,
    ( spl11_1252
    | ~ spl11_1255
    | ~ spl11_2
    | ~ spl11_22 ),
    inference(avatar_split_clause,[],[f8194,f239,f163,f8205,f8199])).

fof(f8194,plain,
    ( ~ r7_relat_2(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | v6_orders_2(k2_tarski(sK1,sK2),sK0)
    | ~ spl11_2
    | ~ spl11_22 ),
    inference(subsumption_resolution,[],[f7404,f100])).

fof(f7404,plain,
    ( ~ r7_relat_2(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | v6_orders_2(k2_tarski(sK1,sK2),sK0)
    | ~ l1_orders_2(sK0)
    | ~ spl11_2
    | ~ spl11_22 ),
    inference(resolution,[],[f7322,f118])).

fof(f118,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r7_relat_2(u1_orders_2(X0),X1)
      | v6_orders_2(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f85])).

fof(f8193,plain,
    ( spl11_3
    | spl11_9
    | ~ spl11_14
    | ~ spl11_22 ),
    inference(avatar_contradiction_clause,[],[f8192])).

fof(f8192,plain,
    ( $false
    | ~ spl11_3
    | ~ spl11_9
    | ~ spl11_14
    | ~ spl11_22 ),
    inference(subsumption_resolution,[],[f465,f7574])).

fof(f7574,plain,
    ( ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl11_3
    | ~ spl11_22 ),
    inference(forward_demodulation,[],[f167,f308])).

fof(f167,plain,
    ( ~ m1_subset_1(k7_domain_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl11_3 ),
    inference(avatar_component_clause,[],[f166])).

fof(f166,plain,
    ( spl11_3
  <=> ~ m1_subset_1(k7_domain_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f465,plain,
    ( m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl11_9
    | ~ spl11_14 ),
    inference(subsumption_resolution,[],[f464,f197])).

fof(f197,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl11_9 ),
    inference(avatar_component_clause,[],[f196])).

fof(f196,plain,
    ( spl11_9
  <=> ~ v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_9])])).

fof(f464,plain,
    ( m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl11_14 ),
    inference(subsumption_resolution,[],[f463,f102])).

fof(f463,plain,
    ( m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl11_14 ),
    inference(subsumption_resolution,[],[f462,f101])).

fof(f462,plain,
    ( m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl11_14 ),
    inference(superposition,[],[f132,f301])).

fof(f301,plain,
    ( k7_domain_1(u1_struct_0(sK0),sK2,sK1) = k2_tarski(sK1,sK2)
    | ~ spl11_14 ),
    inference(forward_demodulation,[],[f299,f122])).

fof(f122,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t36_orders_2.p',commutativity_k2_tarski)).

fof(f299,plain,
    ( k7_domain_1(u1_struct_0(sK0),sK2,sK1) = k2_tarski(sK2,sK1)
    | ~ spl11_14 ),
    inference(resolution,[],[f211,f102])).

fof(f211,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | k7_domain_1(u1_struct_0(sK0),X3,sK1) = k2_tarski(X3,sK1) )
    | ~ spl11_14 ),
    inference(avatar_component_clause,[],[f210])).

fof(f210,plain,
    ( spl11_14
  <=> ! [X3] :
        ( k7_domain_1(u1_struct_0(sK0),X3,sK1) = k2_tarski(X3,sK1)
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_14])])).

fof(f132,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,X0)
        & m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t36_orders_2.p',dt_k7_domain_1)).

fof(f5733,plain,
    ( spl11_45
    | ~ spl11_514 ),
    inference(avatar_contradiction_clause,[],[f5732])).

fof(f5732,plain,
    ( $false
    | ~ spl11_45
    | ~ spl11_514 ),
    inference(subsumption_resolution,[],[f5433,f486])).

fof(f486,plain,
    ( ~ v1_relat_1(u1_orders_2(sK0))
    | ~ spl11_45 ),
    inference(avatar_component_clause,[],[f485])).

fof(f485,plain,
    ( spl11_45
  <=> ~ v1_relat_1(u1_orders_2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_45])])).

fof(f5433,plain,
    ( v1_relat_1(u1_orders_2(sK0))
    | ~ spl11_514 ),
    inference(resolution,[],[f5382,f128])).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f38])).

fof(f38,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t36_orders_2.p',cc1_relset_1)).

fof(f5382,plain,
    ( m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl11_514 ),
    inference(avatar_component_clause,[],[f5381])).

fof(f5381,plain,
    ( spl11_514
  <=> m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_514])])).

fof(f5420,plain,(
    spl11_515 ),
    inference(avatar_contradiction_clause,[],[f5419])).

fof(f5419,plain,
    ( $false
    | ~ spl11_515 ),
    inference(subsumption_resolution,[],[f5418,f100])).

fof(f5418,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl11_515 ),
    inference(resolution,[],[f5385,f114])).

fof(f114,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t36_orders_2.p',dt_u1_orders_2)).

fof(f5385,plain,
    ( ~ m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl11_515 ),
    inference(avatar_component_clause,[],[f5384])).

fof(f5384,plain,
    ( spl11_515
  <=> ~ m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_515])])).

fof(f254,plain,(
    ~ spl11_8 ),
    inference(avatar_contradiction_clause,[],[f253])).

fof(f253,plain,
    ( $false
    | ~ spl11_8 ),
    inference(subsumption_resolution,[],[f252,f98])).

fof(f252,plain,
    ( v2_struct_0(sK0)
    | ~ spl11_8 ),
    inference(subsumption_resolution,[],[f249,f184])).

fof(f184,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f100,f113])).

fof(f113,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t36_orders_2.p',dt_l1_orders_2)).

fof(f249,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_8 ),
    inference(resolution,[],[f200,f120])).

fof(f120,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f39])).

fof(f39,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t36_orders_2.p',fc2_struct_0)).

fof(f200,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl11_8 ),
    inference(avatar_component_clause,[],[f199])).

fof(f199,plain,
    ( spl11_8
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).

fof(f241,plain,
    ( spl11_8
    | spl11_22 ),
    inference(avatar_split_clause,[],[f224,f239,f199])).

fof(f224,plain,(
    ! [X3] :
      ( k7_domain_1(u1_struct_0(sK0),X3,sK2) = k2_tarski(X3,sK2)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | v1_xboole_0(u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f102,f133])).

fof(f133,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,X0)
      | k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2] :
      ( k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,X0)
        & m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t36_orders_2.p',redefinition_k7_domain_1)).

fof(f212,plain,
    ( spl11_8
    | spl11_14 ),
    inference(avatar_split_clause,[],[f189,f210,f199])).

fof(f189,plain,(
    ! [X3] :
      ( k7_domain_1(u1_struct_0(sK0),X3,sK1) = k2_tarski(X3,sK1)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | v1_xboole_0(u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f101,f133])).

fof(f183,plain,
    ( spl11_0
    | spl11_6
    | spl11_4 ),
    inference(avatar_split_clause,[],[f103,f169,f176,f157])).

fof(f103,plain,
    ( r3_orders_2(sK0,sK2,sK1)
    | r3_orders_2(sK0,sK1,sK2)
    | v6_orders_2(k7_domain_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f79])).

fof(f181,plain,
    ( ~ spl11_1
    | ~ spl11_3
    | ~ spl11_7 ),
    inference(avatar_split_clause,[],[f105,f179,f166,f160])).

fof(f105,plain,
    ( ~ r3_orders_2(sK0,sK1,sK2)
    | ~ m1_subset_1(k7_domain_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v6_orders_2(k7_domain_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f79])).

fof(f174,plain,
    ( ~ spl11_1
    | ~ spl11_3
    | ~ spl11_5 ),
    inference(avatar_split_clause,[],[f106,f172,f166,f160])).

fof(f106,plain,
    ( ~ r3_orders_2(sK0,sK2,sK1)
    | ~ m1_subset_1(k7_domain_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v6_orders_2(k7_domain_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f79])).
%------------------------------------------------------------------------------
