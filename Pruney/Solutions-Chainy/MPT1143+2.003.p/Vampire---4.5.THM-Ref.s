%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:41 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 380 expanded)
%              Number of leaves         :   28 ( 123 expanded)
%              Depth                    :   20
%              Number of atoms          :  516 (1730 expanded)
%              Number of equality atoms :   48 (  99 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f292,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f95,f118,f122,f184,f187,f206,f258,f286,f291])).

fof(f291,plain,
    ( spl7_1
    | spl7_3
    | ~ spl7_4
    | ~ spl7_10
    | ~ spl7_12 ),
    inference(avatar_contradiction_clause,[],[f290])).

fof(f290,plain,
    ( $false
    | spl7_1
    | spl7_3
    | ~ spl7_4
    | ~ spl7_10
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f289,f178])).

fof(f178,plain,
    ( sP1(u1_orders_2(sK2))
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f177])).

fof(f177,plain,
    ( spl7_10
  <=> sP1(u1_orders_2(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f289,plain,
    ( ~ sP1(u1_orders_2(sK2))
    | spl7_1
    | spl7_3
    | ~ spl7_4
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f288,f166])).

fof(f166,plain,
    ( ~ r7_relat_2(u1_orders_2(sK2),k2_tarski(sK3,sK3))
    | spl7_1
    | spl7_3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f165,f51])).

fof(f51,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v6_orders_2(k6_domain_1(u1_struct_0(sK2),sK3),sK2) )
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & l1_orders_2(sK2)
    & v3_orders_2(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f17,f36,f35])).

fof(f35,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK2),X1),k1_zfmisc_1(u1_struct_0(sK2)))
            | ~ v6_orders_2(k6_domain_1(u1_struct_0(sK2),X1),sK2) )
          & m1_subset_1(X1,u1_struct_0(sK2)) )
      & l1_orders_2(sK2)
      & v3_orders_2(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X1] :
        ( ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK2),X1),k1_zfmisc_1(u1_struct_0(sK2)))
          | ~ v6_orders_2(k6_domain_1(u1_struct_0(sK2),X1),sK2) )
        & m1_subset_1(X1,u1_struct_0(sK2)) )
   => ( ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ v6_orders_2(k6_domain_1(u1_struct_0(sK2),sK3),sK2) )
      & m1_subset_1(sK3,u1_struct_0(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
              & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_orders_2)).

fof(f165,plain,
    ( ~ r7_relat_2(u1_orders_2(sK2),k2_tarski(sK3,sK3))
    | ~ l1_orders_2(sK2)
    | spl7_1
    | spl7_3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f163,f125])).

fof(f125,plain,
    ( ~ v6_orders_2(k2_tarski(sK3,sK3),sK2)
    | spl7_1
    | ~ spl7_4 ),
    inference(backward_demodulation,[],[f90,f117])).

fof(f117,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK3) = k2_tarski(sK3,sK3)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl7_4
  <=> k6_domain_1(u1_struct_0(sK2),sK3) = k2_tarski(sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f90,plain,
    ( ~ v6_orders_2(k6_domain_1(u1_struct_0(sK2),sK3),sK2)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl7_1
  <=> v6_orders_2(k6_domain_1(u1_struct_0(sK2),sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f163,plain,
    ( ~ r7_relat_2(u1_orders_2(sK2),k2_tarski(sK3,sK3))
    | v6_orders_2(k2_tarski(sK3,sK3),sK2)
    | ~ l1_orders_2(sK2)
    | spl7_3
    | ~ spl7_4 ),
    inference(resolution,[],[f60,f148])).

fof(f148,plain,
    ( m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | spl7_3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f147,f112])).

fof(f112,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK2))
    | spl7_3 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl7_3
  <=> v1_xboole_0(u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f147,plain,
    ( m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(u1_struct_0(sK2))
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f128,f52])).

fof(f52,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f37])).

fof(f128,plain,
    ( m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2))
    | ~ spl7_4 ),
    inference(superposition,[],[f74,f117])).

fof(f74,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r7_relat_2(u1_orders_2(X0),X1)
      | v6_orders_2(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v6_orders_2(X1,X0)
              | ~ r7_relat_2(u1_orders_2(X0),X1) )
            & ( r7_relat_2(u1_orders_2(X0),X1)
              | ~ v6_orders_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_orders_2)).

fof(f288,plain,
    ( r7_relat_2(u1_orders_2(sK2),k2_tarski(sK3,sK3))
    | ~ sP1(u1_orders_2(sK2))
    | ~ spl7_12 ),
    inference(resolution,[],[f196,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | r7_relat_2(X0,X1)
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r7_relat_2(X0,X1)
            | ~ sP0(X0,X1) )
          & ( sP0(X0,X1)
            | ~ r7_relat_2(X0,X1) ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r7_relat_2(X0,X1)
        <=> sP0(X0,X1) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f196,plain,
    ( sP0(u1_orders_2(sK2),k2_tarski(sK3,sK3))
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f194])).

fof(f194,plain,
    ( spl7_12
  <=> sP0(u1_orders_2(sK2),k2_tarski(sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f286,plain,
    ( spl7_1
    | spl7_3
    | ~ spl7_4
    | ~ spl7_10
    | spl7_14 ),
    inference(avatar_contradiction_clause,[],[f285])).

fof(f285,plain,
    ( $false
    | spl7_1
    | spl7_3
    | ~ spl7_4
    | ~ spl7_10
    | spl7_14 ),
    inference(subsumption_resolution,[],[f284,f51])).

fof(f284,plain,
    ( ~ l1_orders_2(sK2)
    | spl7_1
    | spl7_3
    | ~ spl7_4
    | ~ spl7_10
    | spl7_14 ),
    inference(subsumption_resolution,[],[f283,f52])).

fof(f283,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ l1_orders_2(sK2)
    | spl7_1
    | spl7_3
    | ~ spl7_4
    | ~ spl7_10
    | spl7_14 ),
    inference(subsumption_resolution,[],[f282,f171])).

fof(f171,plain,(
    r1_orders_2(sK2,sK3,sK3) ),
    inference(subsumption_resolution,[],[f170,f49])).

fof(f49,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f170,plain,
    ( r1_orders_2(sK2,sK3,sK3)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f169,f50])).

fof(f50,plain,(
    v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f169,plain,
    ( r1_orders_2(sK2,sK3,sK3)
    | ~ v3_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f168,f51])).

fof(f168,plain,
    ( r1_orders_2(sK2,sK3,sK3)
    | ~ l1_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f70,f52])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_orders_2(X0,X1,X1)
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_orders_2(X0,X1,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_orders_2)).

fof(f282,plain,
    ( ~ r1_orders_2(sK2,sK3,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ l1_orders_2(sK2)
    | spl7_1
    | spl7_3
    | ~ spl7_4
    | ~ spl7_10
    | spl7_14 ),
    inference(duplicate_literal_removal,[],[f281])).

fof(f281,plain,
    ( ~ r1_orders_2(sK2,sK3,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ l1_orders_2(sK2)
    | spl7_1
    | spl7_3
    | ~ spl7_4
    | ~ spl7_10
    | spl7_14 ),
    inference(resolution,[],[f228,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_orders_2)).

fof(f228,plain,
    ( ~ r2_hidden(k4_tarski(sK3,sK3),u1_orders_2(sK2))
    | spl7_1
    | spl7_3
    | ~ spl7_4
    | ~ spl7_10
    | spl7_14 ),
    inference(backward_demodulation,[],[f205,f225])).

fof(f225,plain,
    ( sK3 = sK5(u1_orders_2(sK2),k2_tarski(sK3,sK3))
    | spl7_1
    | spl7_3
    | ~ spl7_4
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f223,f178])).

fof(f223,plain,
    ( sK3 = sK5(u1_orders_2(sK2),k2_tarski(sK3,sK3))
    | ~ sP1(u1_orders_2(sK2))
    | spl7_1
    | spl7_3
    | ~ spl7_4 ),
    inference(resolution,[],[f167,f166])).

fof(f167,plain,(
    ! [X0,X1] :
      ( r7_relat_2(X0,k2_tarski(X1,X1))
      | sK5(X0,k2_tarski(X1,X1)) = X1
      | ~ sP1(X0) ) ),
    inference(resolution,[],[f101,f63])).

fof(f101,plain,(
    ! [X4,X3] :
      ( sP0(X4,k2_tarski(X3,X3))
      | sK5(X4,k2_tarski(X3,X3)) = X3 ) ),
    inference(resolution,[],[f86,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X1)
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ~ r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0)
          & ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)
          & r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X1) ) )
      & ( ! [X4,X5] :
            ( r2_hidden(k4_tarski(X5,X4),X0)
            | r2_hidden(k4_tarski(X4,X5),X0)
            | ~ r2_hidden(X5,X1)
            | ~ r2_hidden(X4,X1) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f42,f43])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(k4_tarski(X3,X2),X0)
          & ~ r2_hidden(k4_tarski(X2,X3),X0)
          & r2_hidden(X3,X1)
          & r2_hidden(X2,X1) )
     => ( ~ r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0)
        & ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)
        & r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
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
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
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
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ! [X2,X3] :
          ( r2_hidden(k4_tarski(X3,X2),X0)
          | r2_hidden(k4_tarski(X2,X3),X0)
          | ~ r2_hidden(X3,X1)
          | ~ r2_hidden(X2,X1) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f86,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k2_tarski(X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f75,f54])).

fof(f54,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f75,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK6(X0,X1) != X0
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( sK6(X0,X1) = X0
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f46,f47])).

fof(f47,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK6(X0,X1) != X0
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( sK6(X0,X1) = X0
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f205,plain,
    ( ~ r2_hidden(k4_tarski(sK3,sK5(u1_orders_2(sK2),k2_tarski(sK3,sK3))),u1_orders_2(sK2))
    | spl7_14 ),
    inference(avatar_component_clause,[],[f203])).

fof(f203,plain,
    ( spl7_14
  <=> r2_hidden(k4_tarski(sK3,sK5(u1_orders_2(sK2),k2_tarski(sK3,sK3))),u1_orders_2(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f258,plain,
    ( spl7_2
    | spl7_3
    | ~ spl7_4 ),
    inference(avatar_contradiction_clause,[],[f257])).

fof(f257,plain,
    ( $false
    | spl7_2
    | spl7_3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f256,f148])).

fof(f256,plain,
    ( ~ m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | spl7_2
    | ~ spl7_4 ),
    inference(forward_demodulation,[],[f94,f117])).

fof(f94,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | spl7_2 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl7_2
  <=> m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f206,plain,
    ( spl7_12
    | ~ spl7_14
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f191,f181,f203,f194])).

fof(f181,plain,
    ( spl7_11
  <=> sK3 = sK4(u1_orders_2(sK2),k2_tarski(sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f191,plain,
    ( ~ r2_hidden(k4_tarski(sK3,sK5(u1_orders_2(sK2),k2_tarski(sK3,sK3))),u1_orders_2(sK2))
    | sP0(u1_orders_2(sK2),k2_tarski(sK3,sK3))
    | ~ spl7_11 ),
    inference(superposition,[],[f67,f183])).

fof(f183,plain,
    ( sK3 = sK4(u1_orders_2(sK2),k2_tarski(sK3,sK3))
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f181])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f187,plain,(
    spl7_10 ),
    inference(avatar_contradiction_clause,[],[f186])).

fof(f186,plain,
    ( $false
    | spl7_10 ),
    inference(subsumption_resolution,[],[f185,f51])).

fof(f185,plain,
    ( ~ l1_orders_2(sK2)
    | spl7_10 ),
    inference(resolution,[],[f179,f104])).

fof(f104,plain,(
    ! [X0] :
      ( sP1(u1_orders_2(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f103,f69])).

fof(f69,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | sP1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f23,f33,f32])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r7_relat_2(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r7_relat_2(X0,X1)
        <=> ! [X2,X3] :
              ~ ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                & ~ r2_hidden(k4_tarski(X2,X3),X0)
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_relat_2)).

fof(f103,plain,(
    ! [X0] :
      ( v1_relat_1(u1_orders_2(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f102,f72])).

fof(f72,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f102,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | v1_relat_1(u1_orders_2(X0))
      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))) ) ),
    inference(resolution,[],[f56,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f56,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(f179,plain,
    ( ~ sP1(u1_orders_2(sK2))
    | spl7_10 ),
    inference(avatar_component_clause,[],[f177])).

fof(f184,plain,
    ( ~ spl7_10
    | spl7_11
    | spl7_1
    | spl7_3
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f174,f115,f111,f88,f181,f177])).

fof(f174,plain,
    ( sK3 = sK4(u1_orders_2(sK2),k2_tarski(sK3,sK3))
    | ~ sP1(u1_orders_2(sK2))
    | spl7_1
    | spl7_3
    | ~ spl7_4 ),
    inference(resolution,[],[f162,f166])).

fof(f162,plain,(
    ! [X0,X1] :
      ( r7_relat_2(X0,k2_tarski(X1,X1))
      | sK4(X0,k2_tarski(X1,X1)) = X1
      | ~ sP1(X0) ) ),
    inference(resolution,[],[f100,f63])).

fof(f100,plain,(
    ! [X2,X1] :
      ( sP0(X2,k2_tarski(X1,X1))
      | sK4(X2,k2_tarski(X1,X1)) = X1 ) ),
    inference(resolution,[],[f86,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f122,plain,(
    ~ spl7_3 ),
    inference(avatar_contradiction_clause,[],[f121])).

fof(f121,plain,
    ( $false
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f120,f49])).

fof(f120,plain,
    ( v2_struct_0(sK2)
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f119,f97])).

fof(f97,plain,(
    l1_struct_0(sK2) ),
    inference(resolution,[],[f55,f51])).

fof(f55,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f119,plain,
    ( ~ l1_struct_0(sK2)
    | v2_struct_0(sK2)
    | ~ spl7_3 ),
    inference(resolution,[],[f113,f71])).

fof(f71,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f113,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f111])).

fof(f118,plain,
    ( spl7_3
    | spl7_4 ),
    inference(avatar_split_clause,[],[f107,f115,f111])).

fof(f107,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK3) = k2_tarski(sK3,sK3)
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(resolution,[],[f79,f52])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k2_tarski(X1,X1)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f73,f54])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f95,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f53,f92,f88])).

fof(f53,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v6_orders_2(k6_domain_1(u1_struct_0(sK2),sK3),sK2) ),
    inference(cnf_transformation,[],[f37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:20:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (29651)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.49  % (29650)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (29649)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.50  % (29659)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.51  % (29658)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.51  % (29668)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.51  % (29668)Refutation not found, incomplete strategy% (29668)------------------------------
% 0.21/0.51  % (29668)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (29665)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.52  % (29668)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (29668)Memory used [KB]: 10746
% 0.21/0.52  % (29668)Time elapsed: 0.091 s
% 0.21/0.52  % (29668)------------------------------
% 0.21/0.52  % (29668)------------------------------
% 0.21/0.52  % (29650)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f292,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f95,f118,f122,f184,f187,f206,f258,f286,f291])).
% 0.21/0.52  fof(f291,plain,(
% 0.21/0.52    spl7_1 | spl7_3 | ~spl7_4 | ~spl7_10 | ~spl7_12),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f290])).
% 0.21/0.52  fof(f290,plain,(
% 0.21/0.52    $false | (spl7_1 | spl7_3 | ~spl7_4 | ~spl7_10 | ~spl7_12)),
% 0.21/0.52    inference(subsumption_resolution,[],[f289,f178])).
% 0.21/0.52  fof(f178,plain,(
% 0.21/0.52    sP1(u1_orders_2(sK2)) | ~spl7_10),
% 0.21/0.52    inference(avatar_component_clause,[],[f177])).
% 0.21/0.52  fof(f177,plain,(
% 0.21/0.52    spl7_10 <=> sP1(u1_orders_2(sK2))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.21/0.52  fof(f289,plain,(
% 0.21/0.52    ~sP1(u1_orders_2(sK2)) | (spl7_1 | spl7_3 | ~spl7_4 | ~spl7_12)),
% 0.21/0.52    inference(subsumption_resolution,[],[f288,f166])).
% 0.21/0.52  fof(f166,plain,(
% 0.21/0.52    ~r7_relat_2(u1_orders_2(sK2),k2_tarski(sK3,sK3)) | (spl7_1 | spl7_3 | ~spl7_4)),
% 0.21/0.52    inference(subsumption_resolution,[],[f165,f51])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    l1_orders_2(sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ((~m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2))) | ~v6_orders_2(k6_domain_1(u1_struct_0(sK2),sK3),sK2)) & m1_subset_1(sK3,u1_struct_0(sK2))) & l1_orders_2(sK2) & v3_orders_2(sK2) & ~v2_struct_0(sK2)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f17,f36,f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : ((~m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~m1_subset_1(k6_domain_1(u1_struct_0(sK2),X1),k1_zfmisc_1(u1_struct_0(sK2))) | ~v6_orders_2(k6_domain_1(u1_struct_0(sK2),X1),sK2)) & m1_subset_1(X1,u1_struct_0(sK2))) & l1_orders_2(sK2) & v3_orders_2(sK2) & ~v2_struct_0(sK2))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ? [X1] : ((~m1_subset_1(k6_domain_1(u1_struct_0(sK2),X1),k1_zfmisc_1(u1_struct_0(sK2))) | ~v6_orders_2(k6_domain_1(u1_struct_0(sK2),X1),sK2)) & m1_subset_1(X1,u1_struct_0(sK2))) => ((~m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2))) | ~v6_orders_2(k6_domain_1(u1_struct_0(sK2),sK3),sK2)) & m1_subset_1(sK3,u1_struct_0(sK2)))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : ((~m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : ((~m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,negated_conjecture,(
% 0.21/0.52    ~! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0))))),
% 0.21/0.52    inference(negated_conjecture,[],[f14])).
% 0.21/0.52  fof(f14,conjecture,(
% 0.21/0.52    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_orders_2)).
% 0.21/0.52  fof(f165,plain,(
% 0.21/0.52    ~r7_relat_2(u1_orders_2(sK2),k2_tarski(sK3,sK3)) | ~l1_orders_2(sK2) | (spl7_1 | spl7_3 | ~spl7_4)),
% 0.21/0.52    inference(subsumption_resolution,[],[f163,f125])).
% 0.21/0.52  fof(f125,plain,(
% 0.21/0.52    ~v6_orders_2(k2_tarski(sK3,sK3),sK2) | (spl7_1 | ~spl7_4)),
% 0.21/0.52    inference(backward_demodulation,[],[f90,f117])).
% 0.21/0.52  fof(f117,plain,(
% 0.21/0.52    k6_domain_1(u1_struct_0(sK2),sK3) = k2_tarski(sK3,sK3) | ~spl7_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f115])).
% 0.21/0.52  fof(f115,plain,(
% 0.21/0.52    spl7_4 <=> k6_domain_1(u1_struct_0(sK2),sK3) = k2_tarski(sK3,sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.21/0.52  fof(f90,plain,(
% 0.21/0.52    ~v6_orders_2(k6_domain_1(u1_struct_0(sK2),sK3),sK2) | spl7_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f88])).
% 0.21/0.52  fof(f88,plain,(
% 0.21/0.52    spl7_1 <=> v6_orders_2(k6_domain_1(u1_struct_0(sK2),sK3),sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.52  fof(f163,plain,(
% 0.21/0.52    ~r7_relat_2(u1_orders_2(sK2),k2_tarski(sK3,sK3)) | v6_orders_2(k2_tarski(sK3,sK3),sK2) | ~l1_orders_2(sK2) | (spl7_3 | ~spl7_4)),
% 0.21/0.52    inference(resolution,[],[f60,f148])).
% 0.21/0.52  fof(f148,plain,(
% 0.21/0.52    m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(u1_struct_0(sK2))) | (spl7_3 | ~spl7_4)),
% 0.21/0.52    inference(subsumption_resolution,[],[f147,f112])).
% 0.21/0.52  fof(f112,plain,(
% 0.21/0.52    ~v1_xboole_0(u1_struct_0(sK2)) | spl7_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f111])).
% 0.21/0.52  fof(f111,plain,(
% 0.21/0.52    spl7_3 <=> v1_xboole_0(u1_struct_0(sK2))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.21/0.52  fof(f147,plain,(
% 0.21/0.52    m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(u1_struct_0(sK2))) | v1_xboole_0(u1_struct_0(sK2)) | ~spl7_4),
% 0.21/0.52    inference(subsumption_resolution,[],[f128,f52])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    m1_subset_1(sK3,u1_struct_0(sK2))),
% 0.21/0.52    inference(cnf_transformation,[],[f37])).
% 0.21/0.52  fof(f128,plain,(
% 0.21/0.52    m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_subset_1(sK3,u1_struct_0(sK2)) | v1_xboole_0(u1_struct_0(sK2)) | ~spl7_4),
% 0.21/0.52    inference(superposition,[],[f74,f117])).
% 0.21/0.52  fof(f74,plain,(
% 0.21/0.52    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.52    inference(flattening,[],[f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~r7_relat_2(u1_orders_2(X0),X1) | v6_orders_2(X1,X0) | ~l1_orders_2(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f39])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (((v6_orders_2(X1,X0) | ~r7_relat_2(u1_orders_2(X0),X1)) & (r7_relat_2(u1_orders_2(X0),X1) | ~v6_orders_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.21/0.52    inference(nnf_transformation,[],[f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ((v6_orders_2(X1,X0) <=> r7_relat_2(u1_orders_2(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v6_orders_2(X1,X0) <=> r7_relat_2(u1_orders_2(X0),X1))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_orders_2)).
% 0.21/0.52  fof(f288,plain,(
% 0.21/0.52    r7_relat_2(u1_orders_2(sK2),k2_tarski(sK3,sK3)) | ~sP1(u1_orders_2(sK2)) | ~spl7_12),
% 0.21/0.52    inference(resolution,[],[f196,f63])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~sP0(X0,X1) | r7_relat_2(X0,X1) | ~sP1(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f40])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ((r7_relat_2(X0,X1) | ~sP0(X0,X1)) & (sP0(X0,X1) | ~r7_relat_2(X0,X1))) | ~sP1(X0))),
% 0.21/0.52    inference(nnf_transformation,[],[f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (r7_relat_2(X0,X1) <=> sP0(X0,X1)) | ~sP1(X0))),
% 0.21/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.52  fof(f196,plain,(
% 0.21/0.52    sP0(u1_orders_2(sK2),k2_tarski(sK3,sK3)) | ~spl7_12),
% 0.21/0.52    inference(avatar_component_clause,[],[f194])).
% 0.21/0.52  fof(f194,plain,(
% 0.21/0.52    spl7_12 <=> sP0(u1_orders_2(sK2),k2_tarski(sK3,sK3))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.21/0.52  fof(f286,plain,(
% 0.21/0.52    spl7_1 | spl7_3 | ~spl7_4 | ~spl7_10 | spl7_14),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f285])).
% 0.21/0.52  fof(f285,plain,(
% 0.21/0.52    $false | (spl7_1 | spl7_3 | ~spl7_4 | ~spl7_10 | spl7_14)),
% 0.21/0.52    inference(subsumption_resolution,[],[f284,f51])).
% 0.21/0.52  fof(f284,plain,(
% 0.21/0.52    ~l1_orders_2(sK2) | (spl7_1 | spl7_3 | ~spl7_4 | ~spl7_10 | spl7_14)),
% 0.21/0.52    inference(subsumption_resolution,[],[f283,f52])).
% 0.21/0.52  fof(f283,plain,(
% 0.21/0.52    ~m1_subset_1(sK3,u1_struct_0(sK2)) | ~l1_orders_2(sK2) | (spl7_1 | spl7_3 | ~spl7_4 | ~spl7_10 | spl7_14)),
% 0.21/0.52    inference(subsumption_resolution,[],[f282,f171])).
% 0.21/0.52  fof(f171,plain,(
% 0.21/0.52    r1_orders_2(sK2,sK3,sK3)),
% 0.21/0.52    inference(subsumption_resolution,[],[f170,f49])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    ~v2_struct_0(sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f37])).
% 0.21/0.52  fof(f170,plain,(
% 0.21/0.52    r1_orders_2(sK2,sK3,sK3) | v2_struct_0(sK2)),
% 0.21/0.52    inference(subsumption_resolution,[],[f169,f50])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    v3_orders_2(sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f37])).
% 0.21/0.52  fof(f169,plain,(
% 0.21/0.52    r1_orders_2(sK2,sK3,sK3) | ~v3_orders_2(sK2) | v2_struct_0(sK2)),
% 0.21/0.52    inference(subsumption_resolution,[],[f168,f51])).
% 0.21/0.52  fof(f168,plain,(
% 0.21/0.52    r1_orders_2(sK2,sK3,sK3) | ~l1_orders_2(sK2) | ~v3_orders_2(sK2) | v2_struct_0(sK2)),
% 0.21/0.52    inference(resolution,[],[f70,f52])).
% 0.21/0.52  fof(f70,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | r1_orders_2(X0,X1,X1) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,axiom,(
% 0.21/0.52    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r1_orders_2(X0,X1,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_orders_2)).
% 0.21/0.52  fof(f282,plain,(
% 0.21/0.52    ~r1_orders_2(sK2,sK3,sK3) | ~m1_subset_1(sK3,u1_struct_0(sK2)) | ~l1_orders_2(sK2) | (spl7_1 | spl7_3 | ~spl7_4 | ~spl7_10 | spl7_14)),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f281])).
% 0.21/0.52  fof(f281,plain,(
% 0.21/0.52    ~r1_orders_2(sK2,sK3,sK3) | ~m1_subset_1(sK3,u1_struct_0(sK2)) | ~m1_subset_1(sK3,u1_struct_0(sK2)) | ~l1_orders_2(sK2) | (spl7_1 | spl7_3 | ~spl7_4 | ~spl7_10 | spl7_14)),
% 0.21/0.52    inference(resolution,[],[f228,f57])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : (((r1_orders_2(X0,X1,X2) | ~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))) & (r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.52    inference(nnf_transformation,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : ((r1_orders_2(X0,X1,X2) <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_orders_2(X0,X1,X2) <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_orders_2)).
% 0.21/0.52  fof(f228,plain,(
% 0.21/0.52    ~r2_hidden(k4_tarski(sK3,sK3),u1_orders_2(sK2)) | (spl7_1 | spl7_3 | ~spl7_4 | ~spl7_10 | spl7_14)),
% 0.21/0.52    inference(backward_demodulation,[],[f205,f225])).
% 0.21/0.52  fof(f225,plain,(
% 0.21/0.52    sK3 = sK5(u1_orders_2(sK2),k2_tarski(sK3,sK3)) | (spl7_1 | spl7_3 | ~spl7_4 | ~spl7_10)),
% 0.21/0.52    inference(subsumption_resolution,[],[f223,f178])).
% 0.21/0.52  fof(f223,plain,(
% 0.21/0.52    sK3 = sK5(u1_orders_2(sK2),k2_tarski(sK3,sK3)) | ~sP1(u1_orders_2(sK2)) | (spl7_1 | spl7_3 | ~spl7_4)),
% 0.21/0.52    inference(resolution,[],[f167,f166])).
% 0.21/0.52  fof(f167,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r7_relat_2(X0,k2_tarski(X1,X1)) | sK5(X0,k2_tarski(X1,X1)) = X1 | ~sP1(X0)) )),
% 0.21/0.52    inference(resolution,[],[f101,f63])).
% 0.21/0.52  fof(f101,plain,(
% 0.21/0.52    ( ! [X4,X3] : (sP0(X4,k2_tarski(X3,X3)) | sK5(X4,k2_tarski(X3,X3)) = X3) )),
% 0.21/0.52    inference(resolution,[],[f86,f66])).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X1) | sP0(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f44])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    ! [X0,X1] : ((sP0(X0,X1) | (~r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0) & ~r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) & r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK4(X0,X1),X1))) & (! [X4,X5] : (r2_hidden(k4_tarski(X5,X4),X0) | r2_hidden(k4_tarski(X4,X5),X0) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X1)) | ~sP0(X0,X1)))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f42,f43])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ! [X1,X0] : (? [X2,X3] : (~r2_hidden(k4_tarski(X3,X2),X0) & ~r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(X3,X1) & r2_hidden(X2,X1)) => (~r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0) & ~r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) & r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK4(X0,X1),X1)))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ! [X0,X1] : ((sP0(X0,X1) | ? [X2,X3] : (~r2_hidden(k4_tarski(X3,X2),X0) & ~r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(X3,X1) & r2_hidden(X2,X1))) & (! [X4,X5] : (r2_hidden(k4_tarski(X5,X4),X0) | r2_hidden(k4_tarski(X4,X5),X0) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X1)) | ~sP0(X0,X1)))),
% 0.21/0.52    inference(rectify,[],[f41])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ! [X0,X1] : ((sP0(X0,X1) | ? [X2,X3] : (~r2_hidden(k4_tarski(X3,X2),X0) & ~r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(X3,X1) & r2_hidden(X2,X1))) & (! [X2,X3] : (r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X2,X1)) | ~sP0(X0,X1)))),
% 0.21/0.52    inference(nnf_transformation,[],[f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ! [X0,X1] : (sP0(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X2,X1)))),
% 0.21/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.52  fof(f86,plain,(
% 0.21/0.52    ( ! [X0,X3] : (~r2_hidden(X3,k2_tarski(X0,X0)) | X0 = X3) )),
% 0.21/0.52    inference(equality_resolution,[],[f83])).
% 0.21/0.52  fof(f83,plain,(
% 0.21/0.52    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_tarski(X0,X0) != X1) )),
% 0.21/0.52    inference(definition_unfolding,[],[f75,f54])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f48])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK6(X0,X1) != X0 | ~r2_hidden(sK6(X0,X1),X1)) & (sK6(X0,X1) = X0 | r2_hidden(sK6(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f46,f47])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK6(X0,X1) != X0 | ~r2_hidden(sK6(X0,X1),X1)) & (sK6(X0,X1) = X0 | r2_hidden(sK6(X0,X1),X1))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.52    inference(rectify,[],[f45])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 0.21/0.52  fof(f205,plain,(
% 0.21/0.52    ~r2_hidden(k4_tarski(sK3,sK5(u1_orders_2(sK2),k2_tarski(sK3,sK3))),u1_orders_2(sK2)) | spl7_14),
% 0.21/0.52    inference(avatar_component_clause,[],[f203])).
% 0.21/0.52  fof(f203,plain,(
% 0.21/0.52    spl7_14 <=> r2_hidden(k4_tarski(sK3,sK5(u1_orders_2(sK2),k2_tarski(sK3,sK3))),u1_orders_2(sK2))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 0.21/0.52  fof(f258,plain,(
% 0.21/0.52    spl7_2 | spl7_3 | ~spl7_4),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f257])).
% 0.21/0.52  fof(f257,plain,(
% 0.21/0.52    $false | (spl7_2 | spl7_3 | ~spl7_4)),
% 0.21/0.52    inference(subsumption_resolution,[],[f256,f148])).
% 0.21/0.52  fof(f256,plain,(
% 0.21/0.52    ~m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(u1_struct_0(sK2))) | (spl7_2 | ~spl7_4)),
% 0.21/0.52    inference(forward_demodulation,[],[f94,f117])).
% 0.21/0.52  fof(f94,plain,(
% 0.21/0.52    ~m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2))) | spl7_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f92])).
% 0.21/0.52  fof(f92,plain,(
% 0.21/0.52    spl7_2 <=> m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.21/0.52  fof(f206,plain,(
% 0.21/0.52    spl7_12 | ~spl7_14 | ~spl7_11),
% 0.21/0.52    inference(avatar_split_clause,[],[f191,f181,f203,f194])).
% 0.21/0.52  fof(f181,plain,(
% 0.21/0.52    spl7_11 <=> sK3 = sK4(u1_orders_2(sK2),k2_tarski(sK3,sK3))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.21/0.52  fof(f191,plain,(
% 0.21/0.52    ~r2_hidden(k4_tarski(sK3,sK5(u1_orders_2(sK2),k2_tarski(sK3,sK3))),u1_orders_2(sK2)) | sP0(u1_orders_2(sK2),k2_tarski(sK3,sK3)) | ~spl7_11),
% 0.21/0.52    inference(superposition,[],[f67,f183])).
% 0.21/0.52  fof(f183,plain,(
% 0.21/0.52    sK3 = sK4(u1_orders_2(sK2),k2_tarski(sK3,sK3)) | ~spl7_11),
% 0.21/0.52    inference(avatar_component_clause,[],[f181])).
% 0.21/0.52  fof(f67,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) | sP0(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f44])).
% 0.21/0.52  fof(f187,plain,(
% 0.21/0.52    spl7_10),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f186])).
% 0.21/0.52  fof(f186,plain,(
% 0.21/0.52    $false | spl7_10),
% 0.21/0.52    inference(subsumption_resolution,[],[f185,f51])).
% 0.21/0.52  fof(f185,plain,(
% 0.21/0.52    ~l1_orders_2(sK2) | spl7_10),
% 0.21/0.52    inference(resolution,[],[f179,f104])).
% 0.21/0.52  fof(f104,plain,(
% 0.21/0.52    ( ! [X0] : (sP1(u1_orders_2(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.52    inference(resolution,[],[f103,f69])).
% 0.21/0.52  fof(f69,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_relat_1(X0) | sP1(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f34])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ! [X0] : (sP1(X0) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(definition_folding,[],[f23,f33,f32])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (r7_relat_2(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X2,X1))) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r7_relat_2(X0,X1) <=> ! [X2,X3] : ~(~r2_hidden(k4_tarski(X3,X2),X0) & ~r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(X3,X1) & r2_hidden(X2,X1))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_relat_2)).
% 0.21/0.52  fof(f103,plain,(
% 0.21/0.52    ( ! [X0] : (v1_relat_1(u1_orders_2(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f102,f72])).
% 0.21/0.52  fof(f72,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.52  fof(f102,plain,(
% 0.21/0.52    ( ! [X0] : (~l1_orders_2(X0) | v1_relat_1(u1_orders_2(X0)) | ~v1_relat_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) )),
% 0.21/0.52    inference(resolution,[],[f56,f61])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    ( ! [X0] : (m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X0] : (m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,axiom,(
% 0.21/0.52    ! [X0] : (l1_orders_2(X0) => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).
% 0.21/0.52  fof(f179,plain,(
% 0.21/0.52    ~sP1(u1_orders_2(sK2)) | spl7_10),
% 0.21/0.52    inference(avatar_component_clause,[],[f177])).
% 0.21/0.52  fof(f184,plain,(
% 0.21/0.52    ~spl7_10 | spl7_11 | spl7_1 | spl7_3 | ~spl7_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f174,f115,f111,f88,f181,f177])).
% 0.21/0.52  fof(f174,plain,(
% 0.21/0.52    sK3 = sK4(u1_orders_2(sK2),k2_tarski(sK3,sK3)) | ~sP1(u1_orders_2(sK2)) | (spl7_1 | spl7_3 | ~spl7_4)),
% 0.21/0.52    inference(resolution,[],[f162,f166])).
% 0.21/0.52  fof(f162,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r7_relat_2(X0,k2_tarski(X1,X1)) | sK4(X0,k2_tarski(X1,X1)) = X1 | ~sP1(X0)) )),
% 0.21/0.52    inference(resolution,[],[f100,f63])).
% 0.21/0.52  fof(f100,plain,(
% 0.21/0.52    ( ! [X2,X1] : (sP0(X2,k2_tarski(X1,X1)) | sK4(X2,k2_tarski(X1,X1)) = X1) )),
% 0.21/0.52    inference(resolution,[],[f86,f65])).
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | sP0(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f44])).
% 0.21/0.52  fof(f122,plain,(
% 0.21/0.52    ~spl7_3),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f121])).
% 0.21/0.52  fof(f121,plain,(
% 0.21/0.52    $false | ~spl7_3),
% 0.21/0.52    inference(subsumption_resolution,[],[f120,f49])).
% 0.21/0.52  fof(f120,plain,(
% 0.21/0.52    v2_struct_0(sK2) | ~spl7_3),
% 0.21/0.52    inference(subsumption_resolution,[],[f119,f97])).
% 0.21/0.52  fof(f97,plain,(
% 0.21/0.52    l1_struct_0(sK2)),
% 0.21/0.52    inference(resolution,[],[f55,f51])).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    ( ! [X0] : (~l1_orders_2(X0) | l1_struct_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,axiom,(
% 0.21/0.52    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 0.21/0.52  fof(f119,plain,(
% 0.21/0.52    ~l1_struct_0(sK2) | v2_struct_0(sK2) | ~spl7_3),
% 0.21/0.52    inference(resolution,[],[f113,f71])).
% 0.21/0.52  fof(f71,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.21/0.52  fof(f113,plain,(
% 0.21/0.52    v1_xboole_0(u1_struct_0(sK2)) | ~spl7_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f111])).
% 0.21/0.52  fof(f118,plain,(
% 0.21/0.52    spl7_3 | spl7_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f107,f115,f111])).
% 0.21/0.52  fof(f107,plain,(
% 0.21/0.52    k6_domain_1(u1_struct_0(sK2),sK3) = k2_tarski(sK3,sK3) | v1_xboole_0(u1_struct_0(sK2))),
% 0.21/0.52    inference(resolution,[],[f79,f52])).
% 0.21/0.52  fof(f79,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k2_tarski(X1,X1) | v1_xboole_0(X0)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f73,f54])).
% 0.21/0.52  fof(f73,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.52    inference(flattening,[],[f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,axiom,(
% 0.21/0.52    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.21/0.52  fof(f95,plain,(
% 0.21/0.52    ~spl7_1 | ~spl7_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f53,f92,f88])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    ~m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2))) | ~v6_orders_2(k6_domain_1(u1_struct_0(sK2),sK3),sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f37])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (29650)------------------------------
% 0.21/0.52  % (29650)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (29650)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (29650)Memory used [KB]: 10874
% 0.21/0.52  % (29650)Time elapsed: 0.091 s
% 0.21/0.52  % (29650)------------------------------
% 0.21/0.52  % (29650)------------------------------
% 0.21/0.52  % (29643)Success in time 0.147 s
%------------------------------------------------------------------------------
