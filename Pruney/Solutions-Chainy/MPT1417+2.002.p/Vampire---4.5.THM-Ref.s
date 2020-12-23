%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:31 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 710 expanded)
%              Number of leaves         :   18 ( 263 expanded)
%              Depth                    :   24
%              Number of atoms          :  651 (4977 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   22 (   7 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f171,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f164,f167,f170])).

% (1289)lrs+1010_4:1_aac=none:add=off:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=on:gs=on:gsem=on:irw=on:nm=0:nwc=2.5:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_2 on theBenchmark
% (1284)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
fof(f170,plain,(
    spl8_2 ),
    inference(avatar_contradiction_clause,[],[f169])).

fof(f169,plain,
    ( $false
    | spl8_2 ),
    inference(subsumption_resolution,[],[f168,f77])).

fof(f77,plain,(
    sP0(sK4,sK6) ),
    inference(subsumption_resolution,[],[f76,f43])).

fof(f43,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( ~ r6_binop_1(k8_eqrel_1(sK4,sK5),k3_filter_1(sK4,sK5,sK6),k3_filter_1(sK4,sK5,sK7))
    & r6_binop_1(sK4,sK6,sK7)
    & m2_filter_1(sK7,sK4,sK5)
    & m2_filter_1(sK6,sK4,sK5)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4)))
    & v8_relat_2(sK5)
    & v3_relat_2(sK5)
    & v1_partfun1(sK5,sK4)
    & ~ v1_xboole_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f11,f33,f32,f31,f30])).

fof(f30,plain,
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
                  ( ~ r6_binop_1(k8_eqrel_1(sK4,X1),k3_filter_1(sK4,X1,X2),k3_filter_1(sK4,X1,X3))
                  & r6_binop_1(sK4,X2,X3)
                  & m2_filter_1(X3,sK4,X1) )
              & m2_filter_1(X2,sK4,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4)))
          & v8_relat_2(X1)
          & v3_relat_2(X1)
          & v1_partfun1(X1,sK4) )
      & ~ v1_xboole_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ r6_binop_1(k8_eqrel_1(sK4,X1),k3_filter_1(sK4,X1,X2),k3_filter_1(sK4,X1,X3))
                & r6_binop_1(sK4,X2,X3)
                & m2_filter_1(X3,sK4,X1) )
            & m2_filter_1(X2,sK4,X1) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4)))
        & v8_relat_2(X1)
        & v3_relat_2(X1)
        & v1_partfun1(X1,sK4) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ r6_binop_1(k8_eqrel_1(sK4,sK5),k3_filter_1(sK4,sK5,X2),k3_filter_1(sK4,sK5,X3))
              & r6_binop_1(sK4,X2,X3)
              & m2_filter_1(X3,sK4,sK5) )
          & m2_filter_1(X2,sK4,sK5) )
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4)))
      & v8_relat_2(sK5)
      & v3_relat_2(sK5)
      & v1_partfun1(sK5,sK4) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ r6_binop_1(k8_eqrel_1(sK4,sK5),k3_filter_1(sK4,sK5,X2),k3_filter_1(sK4,sK5,X3))
            & r6_binop_1(sK4,X2,X3)
            & m2_filter_1(X3,sK4,sK5) )
        & m2_filter_1(X2,sK4,sK5) )
   => ( ? [X3] :
          ( ~ r6_binop_1(k8_eqrel_1(sK4,sK5),k3_filter_1(sK4,sK5,sK6),k3_filter_1(sK4,sK5,X3))
          & r6_binop_1(sK4,sK6,X3)
          & m2_filter_1(X3,sK4,sK5) )
      & m2_filter_1(sK6,sK4,sK5) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X3] :
        ( ~ r6_binop_1(k8_eqrel_1(sK4,sK5),k3_filter_1(sK4,sK5,sK6),k3_filter_1(sK4,sK5,X3))
        & r6_binop_1(sK4,sK6,X3)
        & m2_filter_1(X3,sK4,sK5) )
   => ( ~ r6_binop_1(k8_eqrel_1(sK4,sK5),k3_filter_1(sK4,sK5,sK6),k3_filter_1(sK4,sK5,sK7))
      & r6_binop_1(sK4,sK6,sK7)
      & m2_filter_1(sK7,sK4,sK5) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

fof(f10,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
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
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_filter_1)).

fof(f76,plain,
    ( sP0(sK4,sK6)
    | v1_xboole_0(sK4) ),
    inference(subsumption_resolution,[],[f74,f71])).

fof(f71,plain,(
    v1_relat_1(sK5) ),
    inference(subsumption_resolution,[],[f70,f55])).

fof(f55,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f70,plain,
    ( v1_relat_1(sK5)
    | ~ v1_relat_1(k2_zfmisc_1(sK4,sK4)) ),
    inference(resolution,[],[f54,f47])).

fof(f47,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) ),
    inference(cnf_transformation,[],[f34])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f74,plain,
    ( sP0(sK4,sK6)
    | ~ v1_relat_1(sK5)
    | v1_xboole_0(sK4) ),
    inference(resolution,[],[f59,f48])).

fof(f48,plain,(
    m2_filter_1(sK6,sK4,sK5) ),
    inference(cnf_transformation,[],[f34])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m2_filter_1(X2,X0,X1)
      | sP0(X0,X2)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( sP0(X0,X2)
          | ~ m2_filter_1(X2,X0,X1) )
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(definition_folding,[],[f18,f23])).

fof(f23,plain,(
    ! [X0,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
        & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
        & v1_funct_1(X2) )
      | ~ sP0(X0,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
            & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
            & v1_funct_1(X2) )
          | ~ m2_filter_1(X2,X0,X1) )
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
            & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
            & v1_funct_1(X2) )
          | ~ m2_filter_1(X2,X0,X1) )
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m2_filter_1(X2,X0,X1)
         => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
            & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
            & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_filter_1)).

fof(f168,plain,
    ( ~ sP0(sK4,sK6)
    | spl8_2 ),
    inference(resolution,[],[f163,f96])).

fof(f96,plain,(
    ! [X0] :
      ( sP3(sK5,sK4,X0)
      | ~ sP0(sK4,X0) ) ),
    inference(subsumption_resolution,[],[f95,f43])).

fof(f95,plain,(
    ! [X0] :
      ( sP3(sK5,sK4,X0)
      | v1_xboole_0(sK4)
      | ~ sP0(sK4,X0) ) ),
    inference(subsumption_resolution,[],[f94,f44])).

fof(f44,plain,(
    v1_partfun1(sK5,sK4) ),
    inference(cnf_transformation,[],[f34])).

fof(f94,plain,(
    ! [X0] :
      ( sP3(sK5,sK4,X0)
      | ~ v1_partfun1(sK5,sK4)
      | v1_xboole_0(sK4)
      | ~ sP0(sK4,X0) ) ),
    inference(subsumption_resolution,[],[f93,f45])).

fof(f45,plain,(
    v3_relat_2(sK5) ),
    inference(cnf_transformation,[],[f34])).

fof(f93,plain,(
    ! [X0] :
      ( sP3(sK5,sK4,X0)
      | ~ v3_relat_2(sK5)
      | ~ v1_partfun1(sK5,sK4)
      | v1_xboole_0(sK4)
      | ~ sP0(sK4,X0) ) ),
    inference(subsumption_resolution,[],[f92,f46])).

fof(f46,plain,(
    v8_relat_2(sK5) ),
    inference(cnf_transformation,[],[f34])).

fof(f92,plain,(
    ! [X0] :
      ( sP3(sK5,sK4,X0)
      | ~ v8_relat_2(sK5)
      | ~ v3_relat_2(sK5)
      | ~ v1_partfun1(sK5,sK4)
      | v1_xboole_0(sK4)
      | ~ sP0(sK4,X0) ) ),
    inference(resolution,[],[f89,f47])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
      | sP3(X0,X1,X2)
      | ~ v8_relat_2(X0)
      | ~ v3_relat_2(X0)
      | ~ v1_partfun1(X0,X1)
      | v1_xboole_0(X1)
      | ~ sP0(X1,X2) ) ),
    inference(subsumption_resolution,[],[f88,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
        & v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
        & v1_funct_1(X1) )
      | ~ sP0(X0,X1) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
        & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
        & v1_funct_1(X2) )
      | ~ sP0(X0,X2) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( sP3(X0,X1,X2)
      | ~ v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
      | ~ v8_relat_2(X0)
      | ~ v3_relat_2(X0)
      | ~ v1_partfun1(X0,X1)
      | v1_xboole_0(X1)
      | ~ sP0(X1,X2) ) ),
    inference(subsumption_resolution,[],[f86,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( sP3(X0,X1,X2)
      | ~ v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
      | ~ v8_relat_2(X0)
      | ~ v3_relat_2(X0)
      | ~ v1_partfun1(X0,X1)
      | v1_xboole_0(X1)
      | ~ sP0(X1,X2) ) ),
    inference(resolution,[],[f69,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | sP3(X1,X0,X2)
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | ~ v1_partfun1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( sP3(X1,X0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | ~ v1_partfun1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_folding,[],[f22,f28])).

fof(f28,plain,(
    ! [X1,X0,X2] :
      ( ( m1_subset_1(k3_filter_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))))
        & v1_funct_2(k3_filter_1(X0,X1,X2),k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))
        & v1_funct_1(k3_filter_1(X0,X1,X2)) )
      | ~ sP3(X1,X0,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f163,plain,
    ( ~ sP3(sK5,sK4,sK6)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f161])).

fof(f161,plain,
    ( spl8_2
  <=> sP3(sK5,sK4,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f167,plain,(
    spl8_1 ),
    inference(avatar_contradiction_clause,[],[f166])).

fof(f166,plain,
    ( $false
    | spl8_1 ),
    inference(subsumption_resolution,[],[f165,f79])).

fof(f79,plain,(
    sP0(sK4,sK7) ),
    inference(subsumption_resolution,[],[f78,f43])).

fof(f78,plain,
    ( sP0(sK4,sK7)
    | v1_xboole_0(sK4) ),
    inference(subsumption_resolution,[],[f75,f71])).

fof(f75,plain,
    ( sP0(sK4,sK7)
    | ~ v1_relat_1(sK5)
    | v1_xboole_0(sK4) ),
    inference(resolution,[],[f59,f49])).

fof(f49,plain,(
    m2_filter_1(sK7,sK4,sK5) ),
    inference(cnf_transformation,[],[f34])).

fof(f165,plain,
    ( ~ sP0(sK4,sK7)
    | spl8_1 ),
    inference(resolution,[],[f159,f96])).

fof(f159,plain,
    ( ~ sP3(sK5,sK4,sK7)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f157])).

fof(f157,plain,
    ( spl8_1
  <=> sP3(sK5,sK4,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f164,plain,
    ( ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f155,f161,f157])).

fof(f155,plain,
    ( ~ sP3(sK5,sK4,sK6)
    | ~ sP3(sK5,sK4,sK7) ),
    inference(subsumption_resolution,[],[f154,f48])).

fof(f154,plain,
    ( ~ sP3(sK5,sK4,sK6)
    | ~ sP3(sK5,sK4,sK7)
    | ~ m2_filter_1(sK6,sK4,sK5) ),
    inference(subsumption_resolution,[],[f153,f116])).

fof(f116,plain,(
    r4_binop_1(sK4,sK6,sK7) ),
    inference(resolution,[],[f113,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | r4_binop_1(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ~ r5_binop_1(X2,X1,X0)
        | ~ r4_binop_1(X2,X1,X0) )
      & ( ( r5_binop_1(X2,X1,X0)
          & r4_binop_1(X2,X1,X0) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( ( sP1(X2,X1,X0)
        | ~ r5_binop_1(X0,X1,X2)
        | ~ r4_binop_1(X0,X1,X2) )
      & ( ( r5_binop_1(X0,X1,X2)
          & r4_binop_1(X0,X1,X2) )
        | ~ sP1(X2,X1,X0) ) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X2,X1,X0] :
      ( ( sP1(X2,X1,X0)
        | ~ r5_binop_1(X0,X1,X2)
        | ~ r4_binop_1(X0,X1,X2) )
      & ( ( r5_binop_1(X0,X1,X2)
          & r4_binop_1(X0,X1,X2) )
        | ~ sP1(X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( sP1(X2,X1,X0)
    <=> ( r5_binop_1(X0,X1,X2)
        & r4_binop_1(X0,X1,X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f113,plain,(
    sP1(sK7,sK6,sK4) ),
    inference(subsumption_resolution,[],[f112,f79])).

fof(f112,plain,
    ( ~ sP0(sK4,sK7)
    | sP1(sK7,sK6,sK4) ),
    inference(subsumption_resolution,[],[f111,f77])).

fof(f111,plain,
    ( ~ sP0(sK4,sK6)
    | ~ sP0(sK4,sK7)
    | sP1(sK7,sK6,sK4) ),
    inference(resolution,[],[f110,f50])).

fof(f50,plain,(
    r6_binop_1(sK4,sK6,sK7) ),
    inference(cnf_transformation,[],[f34])).

fof(f110,plain,(
    ! [X4,X5,X3] :
      ( ~ r6_binop_1(X3,X5,X4)
      | ~ sP0(X3,X5)
      | ~ sP0(X3,X4)
      | sP1(X4,X5,X3) ) ),
    inference(resolution,[],[f106,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | ~ r6_binop_1(X0,X1,X2)
      | sP1(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( ( r6_binop_1(X0,X1,X2)
          | ~ sP1(X2,X1,X0) )
        & ( sP1(X2,X1,X0)
          | ~ r6_binop_1(X0,X1,X2) ) )
      | ~ sP2(X0,X1,X2) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r6_binop_1(X0,X1,X2)
      <=> sP1(X2,X1,X0) )
      | ~ sP2(X0,X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( sP2(X0,X1,X2)
      | ~ sP0(X0,X2)
      | ~ sP0(X0,X1) ) ),
    inference(subsumption_resolution,[],[f105,f57])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( sP2(X0,X1,X2)
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ sP0(X0,X2)
      | ~ sP0(X0,X1) ) ),
    inference(subsumption_resolution,[],[f103,f56])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( sP2(X0,X1,X2)
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1)
      | ~ sP0(X0,X2)
      | ~ sP0(X0,X1) ) ),
    inference(resolution,[],[f100,f58])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | sP2(X0,X1,X2)
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1)
      | ~ sP0(X0,X2) ) ),
    inference(subsumption_resolution,[],[f99,f57])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( sP2(X0,X1,X2)
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1)
      | ~ sP0(X0,X2) ) ),
    inference(subsumption_resolution,[],[f97,f56])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( sP2(X0,X1,X2)
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1)
      | ~ sP0(X0,X2) ) ),
    inference(resolution,[],[f65,f58])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | sP2(X0,X1,X2)
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( sP2(X0,X1,X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
          | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
          | ~ v1_funct_1(X2) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1) ) ),
    inference(definition_folding,[],[f20,f26,f25])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_binop_1)).

fof(f153,plain,
    ( ~ r4_binop_1(sK4,sK6,sK7)
    | ~ sP3(sK5,sK4,sK6)
    | ~ sP3(sK5,sK4,sK7)
    | ~ m2_filter_1(sK6,sK4,sK5) ),
    inference(subsumption_resolution,[],[f152,f115])).

fof(f115,plain,(
    r5_binop_1(sK4,sK6,sK7) ),
    inference(resolution,[],[f113,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | r5_binop_1(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f152,plain,
    ( ~ r5_binop_1(sK4,sK6,sK7)
    | ~ r4_binop_1(sK4,sK6,sK7)
    | ~ sP3(sK5,sK4,sK6)
    | ~ sP3(sK5,sK4,sK7)
    | ~ m2_filter_1(sK6,sK4,sK5) ),
    inference(subsumption_resolution,[],[f151,f49])).

fof(f151,plain,
    ( ~ m2_filter_1(sK7,sK4,sK5)
    | ~ r5_binop_1(sK4,sK6,sK7)
    | ~ r4_binop_1(sK4,sK6,sK7)
    | ~ sP3(sK5,sK4,sK6)
    | ~ sP3(sK5,sK4,sK7)
    | ~ m2_filter_1(sK6,sK4,sK5) ),
    inference(subsumption_resolution,[],[f150,f43])).

fof(f150,plain,
    ( v1_xboole_0(sK4)
    | ~ m2_filter_1(sK7,sK4,sK5)
    | ~ r5_binop_1(sK4,sK6,sK7)
    | ~ r4_binop_1(sK4,sK6,sK7)
    | ~ sP3(sK5,sK4,sK6)
    | ~ sP3(sK5,sK4,sK7)
    | ~ m2_filter_1(sK6,sK4,sK5) ),
    inference(subsumption_resolution,[],[f149,f44])).

fof(f149,plain,
    ( ~ v1_partfun1(sK5,sK4)
    | v1_xboole_0(sK4)
    | ~ m2_filter_1(sK7,sK4,sK5)
    | ~ r5_binop_1(sK4,sK6,sK7)
    | ~ r4_binop_1(sK4,sK6,sK7)
    | ~ sP3(sK5,sK4,sK6)
    | ~ sP3(sK5,sK4,sK7)
    | ~ m2_filter_1(sK6,sK4,sK5) ),
    inference(subsumption_resolution,[],[f148,f45])).

fof(f148,plain,
    ( ~ v3_relat_2(sK5)
    | ~ v1_partfun1(sK5,sK4)
    | v1_xboole_0(sK4)
    | ~ m2_filter_1(sK7,sK4,sK5)
    | ~ r5_binop_1(sK4,sK6,sK7)
    | ~ r4_binop_1(sK4,sK6,sK7)
    | ~ sP3(sK5,sK4,sK6)
    | ~ sP3(sK5,sK4,sK7)
    | ~ m2_filter_1(sK6,sK4,sK5) ),
    inference(subsumption_resolution,[],[f147,f46])).

fof(f147,plain,
    ( ~ v8_relat_2(sK5)
    | ~ v3_relat_2(sK5)
    | ~ v1_partfun1(sK5,sK4)
    | v1_xboole_0(sK4)
    | ~ m2_filter_1(sK7,sK4,sK5)
    | ~ r5_binop_1(sK4,sK6,sK7)
    | ~ r4_binop_1(sK4,sK6,sK7)
    | ~ sP3(sK5,sK4,sK6)
    | ~ sP3(sK5,sK4,sK7)
    | ~ m2_filter_1(sK6,sK4,sK5) ),
    inference(subsumption_resolution,[],[f139,f47])).

fof(f139,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4)))
    | ~ v8_relat_2(sK5)
    | ~ v3_relat_2(sK5)
    | ~ v1_partfun1(sK5,sK4)
    | v1_xboole_0(sK4)
    | ~ m2_filter_1(sK7,sK4,sK5)
    | ~ r5_binop_1(sK4,sK6,sK7)
    | ~ r4_binop_1(sK4,sK6,sK7)
    | ~ sP3(sK5,sK4,sK6)
    | ~ sP3(sK5,sK4,sK7)
    | ~ m2_filter_1(sK6,sK4,sK5) ),
    inference(resolution,[],[f133,f51])).

fof(f51,plain,(
    ~ r6_binop_1(k8_eqrel_1(sK4,sK5),k3_filter_1(sK4,sK5,sK6),k3_filter_1(sK4,sK5,sK7)) ),
    inference(cnf_transformation,[],[f34])).

fof(f133,plain,(
    ! [X2,X0,X3,X1] :
      ( r6_binop_1(k8_eqrel_1(X1,X2),k3_filter_1(X1,X2,X0),k3_filter_1(X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
      | ~ v8_relat_2(X2)
      | ~ v3_relat_2(X2)
      | ~ v1_partfun1(X2,X1)
      | v1_xboole_0(X1)
      | ~ m2_filter_1(X3,X1,X2)
      | ~ r5_binop_1(X1,X0,X3)
      | ~ r4_binop_1(X1,X0,X3)
      | ~ sP3(X2,X1,X0)
      | ~ sP3(X2,X1,X3)
      | ~ m2_filter_1(X0,X1,X2) ) ),
    inference(resolution,[],[f132,f129])).

fof(f129,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP1(k3_filter_1(X1,X0,X2),k3_filter_1(X1,X0,X3),k8_eqrel_1(X1,X0))
      | ~ sP3(X0,X1,X3)
      | ~ sP3(X0,X1,X2)
      | r6_binop_1(k8_eqrel_1(X1,X0),k3_filter_1(X1,X0,X3),k3_filter_1(X1,X0,X2)) ) ),
    inference(resolution,[],[f126,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | ~ sP1(X2,X1,X0)
      | r6_binop_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f126,plain,(
    ! [X6,X4,X7,X5] :
      ( sP2(k8_eqrel_1(X4,X5),k3_filter_1(X4,X5,X6),k3_filter_1(X4,X5,X7))
      | ~ sP3(X5,X4,X7)
      | ~ sP3(X5,X4,X6) ) ),
    inference(subsumption_resolution,[],[f125,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k3_filter_1(X1,X0,X2))
      | ~ sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k3_filter_1(X1,X0,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X1,X0),k8_eqrel_1(X1,X0)),k8_eqrel_1(X1,X0))))
        & v1_funct_2(k3_filter_1(X1,X0,X2),k2_zfmisc_1(k8_eqrel_1(X1,X0),k8_eqrel_1(X1,X0)),k8_eqrel_1(X1,X0))
        & v1_funct_1(k3_filter_1(X1,X0,X2)) )
      | ~ sP3(X0,X1,X2) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X1,X0,X2] :
      ( ( m1_subset_1(k3_filter_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))))
        & v1_funct_2(k3_filter_1(X0,X1,X2),k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))
        & v1_funct_1(k3_filter_1(X0,X1,X2)) )
      | ~ sP3(X1,X0,X2) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f125,plain,(
    ! [X6,X4,X7,X5] :
      ( sP2(k8_eqrel_1(X4,X5),k3_filter_1(X4,X5,X6),k3_filter_1(X4,X5,X7))
      | ~ v1_funct_1(k3_filter_1(X4,X5,X6))
      | ~ sP3(X5,X4,X7)
      | ~ sP3(X5,X4,X6) ) ),
    inference(subsumption_resolution,[],[f122,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k3_filter_1(X1,X0,X2),k2_zfmisc_1(k8_eqrel_1(X1,X0),k8_eqrel_1(X1,X0)),k8_eqrel_1(X1,X0))
      | ~ sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f122,plain,(
    ! [X6,X4,X7,X5] :
      ( sP2(k8_eqrel_1(X4,X5),k3_filter_1(X4,X5,X6),k3_filter_1(X4,X5,X7))
      | ~ v1_funct_2(k3_filter_1(X4,X5,X6),k2_zfmisc_1(k8_eqrel_1(X4,X5),k8_eqrel_1(X4,X5)),k8_eqrel_1(X4,X5))
      | ~ v1_funct_1(k3_filter_1(X4,X5,X6))
      | ~ sP3(X5,X4,X7)
      | ~ sP3(X5,X4,X6) ) ),
    inference(resolution,[],[f102,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_filter_1(X1,X0,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X1,X0),k8_eqrel_1(X1,X0)),k8_eqrel_1(X1,X0))))
      | ~ sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f102,plain,(
    ! [X6,X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X3,X4),k8_eqrel_1(X3,X4)),k8_eqrel_1(X3,X4))))
      | sP2(k8_eqrel_1(X3,X4),X5,k3_filter_1(X3,X4,X6))
      | ~ v1_funct_2(X5,k2_zfmisc_1(k8_eqrel_1(X3,X4),k8_eqrel_1(X3,X4)),k8_eqrel_1(X3,X4))
      | ~ v1_funct_1(X5)
      | ~ sP3(X4,X3,X6) ) ),
    inference(subsumption_resolution,[],[f101,f66])).

fof(f101,plain,(
    ! [X6,X4,X5,X3] :
      ( sP2(k8_eqrel_1(X3,X4),X5,k3_filter_1(X3,X4,X6))
      | ~ v1_funct_1(k3_filter_1(X3,X4,X6))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X3,X4),k8_eqrel_1(X3,X4)),k8_eqrel_1(X3,X4))))
      | ~ v1_funct_2(X5,k2_zfmisc_1(k8_eqrel_1(X3,X4),k8_eqrel_1(X3,X4)),k8_eqrel_1(X3,X4))
      | ~ v1_funct_1(X5)
      | ~ sP3(X4,X3,X6) ) ),
    inference(subsumption_resolution,[],[f98,f67])).

fof(f98,plain,(
    ! [X6,X4,X5,X3] :
      ( sP2(k8_eqrel_1(X3,X4),X5,k3_filter_1(X3,X4,X6))
      | ~ v1_funct_2(k3_filter_1(X3,X4,X6),k2_zfmisc_1(k8_eqrel_1(X3,X4),k8_eqrel_1(X3,X4)),k8_eqrel_1(X3,X4))
      | ~ v1_funct_1(k3_filter_1(X3,X4,X6))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X3,X4),k8_eqrel_1(X3,X4)),k8_eqrel_1(X3,X4))))
      | ~ v1_funct_2(X5,k2_zfmisc_1(k8_eqrel_1(X3,X4),k8_eqrel_1(X3,X4)),k8_eqrel_1(X3,X4))
      | ~ v1_funct_1(X5)
      | ~ sP3(X4,X3,X6) ) ),
    inference(resolution,[],[f65,f68])).

fof(f132,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(k3_filter_1(X1,X2,X0),k3_filter_1(X1,X2,X3),k8_eqrel_1(X1,X2))
      | ~ m2_filter_1(X3,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
      | ~ v8_relat_2(X2)
      | ~ v3_relat_2(X2)
      | ~ v1_partfun1(X2,X1)
      | v1_xboole_0(X1)
      | ~ m2_filter_1(X0,X1,X2)
      | ~ r5_binop_1(X1,X3,X0)
      | ~ r4_binop_1(X1,X3,X0) ) ),
    inference(duplicate_literal_removal,[],[f131])).

fof(f131,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m2_filter_1(X0,X1,X2)
      | ~ m2_filter_1(X3,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
      | ~ v8_relat_2(X2)
      | ~ v3_relat_2(X2)
      | ~ v1_partfun1(X2,X1)
      | v1_xboole_0(X1)
      | sP1(k3_filter_1(X1,X2,X0),k3_filter_1(X1,X2,X3),k8_eqrel_1(X1,X2))
      | ~ r5_binop_1(X1,X3,X0)
      | ~ r4_binop_1(X1,X3,X0)
      | ~ m2_filter_1(X0,X1,X2)
      | ~ m2_filter_1(X3,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
      | ~ v8_relat_2(X2)
      | ~ v3_relat_2(X2)
      | ~ v1_partfun1(X2,X1)
      | v1_xboole_0(X1) ) ),
    inference(resolution,[],[f120,f53])).

fof(f53,plain,(
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
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_filter_1)).

fof(f120,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r4_binop_1(k8_eqrel_1(X0,X3),k3_filter_1(X0,X3,X1),k3_filter_1(X0,X3,X2))
      | ~ m2_filter_1(X2,X0,X3)
      | ~ m2_filter_1(X1,X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v8_relat_2(X3)
      | ~ v3_relat_2(X3)
      | ~ v1_partfun1(X3,X0)
      | v1_xboole_0(X0)
      | sP1(k3_filter_1(X0,X3,X2),k3_filter_1(X0,X3,X1),k8_eqrel_1(X0,X3))
      | ~ r5_binop_1(X0,X1,X2) ) ),
    inference(resolution,[],[f52,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ r5_binop_1(X2,X1,X0)
      | sP1(X0,X1,X2)
      | ~ r4_binop_1(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f52,plain,(
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
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_filter_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:57:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.45  % (1286)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.19/0.45  % (1279)lrs+1003_2:3_afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=on:fde=unused:gs=on:inw=on:nm=0:newcnf=on:nwc=1:sas=z3:stl=30:sac=on:sp=occurrence:tha=off:updr=off:uhcvi=on_2 on theBenchmark
% 0.19/0.45  % (1276)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.19/0.45  % (1273)lrs+1_3_awrs=decay:awrsf=4:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fsr=off:fde=unused:gs=on:lwlo=on:nm=16:nwc=1:sas=z3:stl=30:ss=axioms:s2a=on:st=1.2:sos=theory:sp=frequency_3 on theBenchmark
% 0.19/0.46  % (1281)WARNING: option uwaf not known.
% 0.19/0.46  % (1278)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.19/0.46  % (1278)Refutation found. Thanks to Tanya!
% 0.19/0.46  % SZS status Theorem for theBenchmark
% 0.19/0.46  % (1274)lrs-11_4:1_afp=4000:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_3 on theBenchmark
% 0.19/0.46  % SZS output start Proof for theBenchmark
% 0.19/0.46  fof(f171,plain,(
% 0.19/0.46    $false),
% 0.19/0.46    inference(avatar_sat_refutation,[],[f164,f167,f170])).
% 0.19/0.46  % (1289)lrs+1010_4:1_aac=none:add=off:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=on:gs=on:gsem=on:irw=on:nm=0:nwc=2.5:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.46  % (1284)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.19/0.46  fof(f170,plain,(
% 0.19/0.46    spl8_2),
% 0.19/0.46    inference(avatar_contradiction_clause,[],[f169])).
% 0.19/0.46  fof(f169,plain,(
% 0.19/0.46    $false | spl8_2),
% 0.19/0.46    inference(subsumption_resolution,[],[f168,f77])).
% 0.19/0.46  fof(f77,plain,(
% 0.19/0.46    sP0(sK4,sK6)),
% 0.19/0.46    inference(subsumption_resolution,[],[f76,f43])).
% 0.19/0.46  fof(f43,plain,(
% 0.19/0.46    ~v1_xboole_0(sK4)),
% 0.19/0.46    inference(cnf_transformation,[],[f34])).
% 0.19/0.46  fof(f34,plain,(
% 0.19/0.46    (((~r6_binop_1(k8_eqrel_1(sK4,sK5),k3_filter_1(sK4,sK5,sK6),k3_filter_1(sK4,sK5,sK7)) & r6_binop_1(sK4,sK6,sK7) & m2_filter_1(sK7,sK4,sK5)) & m2_filter_1(sK6,sK4,sK5)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) & v8_relat_2(sK5) & v3_relat_2(sK5) & v1_partfun1(sK5,sK4)) & ~v1_xboole_0(sK4)),
% 0.19/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f11,f33,f32,f31,f30])).
% 0.19/0.46  fof(f30,plain,(
% 0.19/0.46    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r6_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) & r6_binop_1(X0,X2,X3) & m2_filter_1(X3,X0,X1)) & m2_filter_1(X2,X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v8_relat_2(X1) & v3_relat_2(X1) & v1_partfun1(X1,X0)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~r6_binop_1(k8_eqrel_1(sK4,X1),k3_filter_1(sK4,X1,X2),k3_filter_1(sK4,X1,X3)) & r6_binop_1(sK4,X2,X3) & m2_filter_1(X3,sK4,X1)) & m2_filter_1(X2,sK4,X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) & v8_relat_2(X1) & v3_relat_2(X1) & v1_partfun1(X1,sK4)) & ~v1_xboole_0(sK4))),
% 0.19/0.46    introduced(choice_axiom,[])).
% 0.19/0.46  fof(f31,plain,(
% 0.19/0.46    ? [X1] : (? [X2] : (? [X3] : (~r6_binop_1(k8_eqrel_1(sK4,X1),k3_filter_1(sK4,X1,X2),k3_filter_1(sK4,X1,X3)) & r6_binop_1(sK4,X2,X3) & m2_filter_1(X3,sK4,X1)) & m2_filter_1(X2,sK4,X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) & v8_relat_2(X1) & v3_relat_2(X1) & v1_partfun1(X1,sK4)) => (? [X2] : (? [X3] : (~r6_binop_1(k8_eqrel_1(sK4,sK5),k3_filter_1(sK4,sK5,X2),k3_filter_1(sK4,sK5,X3)) & r6_binop_1(sK4,X2,X3) & m2_filter_1(X3,sK4,sK5)) & m2_filter_1(X2,sK4,sK5)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) & v8_relat_2(sK5) & v3_relat_2(sK5) & v1_partfun1(sK5,sK4))),
% 0.19/0.46    introduced(choice_axiom,[])).
% 0.19/0.46  fof(f32,plain,(
% 0.19/0.46    ? [X2] : (? [X3] : (~r6_binop_1(k8_eqrel_1(sK4,sK5),k3_filter_1(sK4,sK5,X2),k3_filter_1(sK4,sK5,X3)) & r6_binop_1(sK4,X2,X3) & m2_filter_1(X3,sK4,sK5)) & m2_filter_1(X2,sK4,sK5)) => (? [X3] : (~r6_binop_1(k8_eqrel_1(sK4,sK5),k3_filter_1(sK4,sK5,sK6),k3_filter_1(sK4,sK5,X3)) & r6_binop_1(sK4,sK6,X3) & m2_filter_1(X3,sK4,sK5)) & m2_filter_1(sK6,sK4,sK5))),
% 0.19/0.46    introduced(choice_axiom,[])).
% 0.19/0.46  fof(f33,plain,(
% 0.19/0.46    ? [X3] : (~r6_binop_1(k8_eqrel_1(sK4,sK5),k3_filter_1(sK4,sK5,sK6),k3_filter_1(sK4,sK5,X3)) & r6_binop_1(sK4,sK6,X3) & m2_filter_1(X3,sK4,sK5)) => (~r6_binop_1(k8_eqrel_1(sK4,sK5),k3_filter_1(sK4,sK5,sK6),k3_filter_1(sK4,sK5,sK7)) & r6_binop_1(sK4,sK6,sK7) & m2_filter_1(sK7,sK4,sK5))),
% 0.19/0.46    introduced(choice_axiom,[])).
% 0.19/0.46  fof(f11,plain,(
% 0.19/0.46    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r6_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) & r6_binop_1(X0,X2,X3) & m2_filter_1(X3,X0,X1)) & m2_filter_1(X2,X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v8_relat_2(X1) & v3_relat_2(X1) & v1_partfun1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.19/0.46    inference(flattening,[],[f10])).
% 0.19/0.46  fof(f10,plain,(
% 0.19/0.46    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r6_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) & r6_binop_1(X0,X2,X3)) & m2_filter_1(X3,X0,X1)) & m2_filter_1(X2,X0,X1)) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v8_relat_2(X1) & v3_relat_2(X1) & v1_partfun1(X1,X0))) & ~v1_xboole_0(X0))),
% 0.19/0.46    inference(ennf_transformation,[],[f9])).
% 0.19/0.46  fof(f9,negated_conjecture,(
% 0.19/0.46    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v8_relat_2(X1) & v3_relat_2(X1) & v1_partfun1(X1,X0)) => ! [X2] : (m2_filter_1(X2,X0,X1) => ! [X3] : (m2_filter_1(X3,X0,X1) => (r6_binop_1(X0,X2,X3) => r6_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3)))))))),
% 0.19/0.46    inference(negated_conjecture,[],[f8])).
% 0.19/0.46  fof(f8,conjecture,(
% 0.19/0.46    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v8_relat_2(X1) & v3_relat_2(X1) & v1_partfun1(X1,X0)) => ! [X2] : (m2_filter_1(X2,X0,X1) => ! [X3] : (m2_filter_1(X3,X0,X1) => (r6_binop_1(X0,X2,X3) => r6_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3)))))))),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_filter_1)).
% 0.19/0.46  fof(f76,plain,(
% 0.19/0.46    sP0(sK4,sK6) | v1_xboole_0(sK4)),
% 0.19/0.46    inference(subsumption_resolution,[],[f74,f71])).
% 0.19/0.46  fof(f71,plain,(
% 0.19/0.46    v1_relat_1(sK5)),
% 0.19/0.46    inference(subsumption_resolution,[],[f70,f55])).
% 0.19/0.46  fof(f55,plain,(
% 0.19/0.46    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.19/0.46    inference(cnf_transformation,[],[f2])).
% 0.19/0.46  fof(f2,axiom,(
% 0.19/0.46    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.19/0.46  fof(f70,plain,(
% 0.19/0.46    v1_relat_1(sK5) | ~v1_relat_1(k2_zfmisc_1(sK4,sK4))),
% 0.19/0.46    inference(resolution,[],[f54,f47])).
% 0.19/0.46  fof(f47,plain,(
% 0.19/0.46    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4)))),
% 0.19/0.46    inference(cnf_transformation,[],[f34])).
% 0.19/0.46  fof(f54,plain,(
% 0.19/0.46    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f16])).
% 0.19/0.46  fof(f16,plain,(
% 0.19/0.46    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.19/0.46    inference(ennf_transformation,[],[f1])).
% 0.19/0.46  fof(f1,axiom,(
% 0.19/0.46    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.19/0.46  fof(f74,plain,(
% 0.19/0.46    sP0(sK4,sK6) | ~v1_relat_1(sK5) | v1_xboole_0(sK4)),
% 0.19/0.46    inference(resolution,[],[f59,f48])).
% 0.19/0.46  fof(f48,plain,(
% 0.19/0.46    m2_filter_1(sK6,sK4,sK5)),
% 0.19/0.46    inference(cnf_transformation,[],[f34])).
% 0.19/0.46  fof(f59,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (~m2_filter_1(X2,X0,X1) | sP0(X0,X2) | ~v1_relat_1(X1) | v1_xboole_0(X0)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f24])).
% 0.19/0.46  fof(f24,plain,(
% 0.19/0.46    ! [X0,X1] : (! [X2] : (sP0(X0,X2) | ~m2_filter_1(X2,X0,X1)) | ~v1_relat_1(X1) | v1_xboole_0(X0))),
% 0.19/0.46    inference(definition_folding,[],[f18,f23])).
% 0.19/0.46  fof(f23,plain,(
% 0.19/0.46    ! [X0,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) & v1_funct_1(X2)) | ~sP0(X0,X2))),
% 0.19/0.46    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.19/0.46  fof(f18,plain,(
% 0.19/0.46    ! [X0,X1] : (! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) & v1_funct_1(X2)) | ~m2_filter_1(X2,X0,X1)) | ~v1_relat_1(X1) | v1_xboole_0(X0))),
% 0.19/0.46    inference(flattening,[],[f17])).
% 0.19/0.46  fof(f17,plain,(
% 0.19/0.46    ! [X0,X1] : (! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) & v1_funct_1(X2)) | ~m2_filter_1(X2,X0,X1)) | (~v1_relat_1(X1) | v1_xboole_0(X0)))),
% 0.19/0.46    inference(ennf_transformation,[],[f5])).
% 0.19/0.46  fof(f5,axiom,(
% 0.19/0.46    ! [X0,X1] : ((v1_relat_1(X1) & ~v1_xboole_0(X0)) => ! [X2] : (m2_filter_1(X2,X0,X1) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) & v1_funct_1(X2))))),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_filter_1)).
% 0.19/0.46  fof(f168,plain,(
% 0.19/0.46    ~sP0(sK4,sK6) | spl8_2),
% 0.19/0.46    inference(resolution,[],[f163,f96])).
% 0.19/0.46  fof(f96,plain,(
% 0.19/0.46    ( ! [X0] : (sP3(sK5,sK4,X0) | ~sP0(sK4,X0)) )),
% 0.19/0.46    inference(subsumption_resolution,[],[f95,f43])).
% 0.19/0.46  fof(f95,plain,(
% 0.19/0.46    ( ! [X0] : (sP3(sK5,sK4,X0) | v1_xboole_0(sK4) | ~sP0(sK4,X0)) )),
% 0.19/0.46    inference(subsumption_resolution,[],[f94,f44])).
% 0.19/0.46  fof(f44,plain,(
% 0.19/0.46    v1_partfun1(sK5,sK4)),
% 0.19/0.46    inference(cnf_transformation,[],[f34])).
% 0.19/0.46  fof(f94,plain,(
% 0.19/0.46    ( ! [X0] : (sP3(sK5,sK4,X0) | ~v1_partfun1(sK5,sK4) | v1_xboole_0(sK4) | ~sP0(sK4,X0)) )),
% 0.19/0.46    inference(subsumption_resolution,[],[f93,f45])).
% 0.19/0.46  fof(f45,plain,(
% 0.19/0.46    v3_relat_2(sK5)),
% 0.19/0.46    inference(cnf_transformation,[],[f34])).
% 0.19/0.46  fof(f93,plain,(
% 0.19/0.46    ( ! [X0] : (sP3(sK5,sK4,X0) | ~v3_relat_2(sK5) | ~v1_partfun1(sK5,sK4) | v1_xboole_0(sK4) | ~sP0(sK4,X0)) )),
% 0.19/0.46    inference(subsumption_resolution,[],[f92,f46])).
% 0.19/0.46  fof(f46,plain,(
% 0.19/0.46    v8_relat_2(sK5)),
% 0.19/0.46    inference(cnf_transformation,[],[f34])).
% 0.19/0.46  fof(f92,plain,(
% 0.19/0.46    ( ! [X0] : (sP3(sK5,sK4,X0) | ~v8_relat_2(sK5) | ~v3_relat_2(sK5) | ~v1_partfun1(sK5,sK4) | v1_xboole_0(sK4) | ~sP0(sK4,X0)) )),
% 0.19/0.46    inference(resolution,[],[f89,f47])).
% 0.19/0.46  fof(f89,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) | sP3(X0,X1,X2) | ~v8_relat_2(X0) | ~v3_relat_2(X0) | ~v1_partfun1(X0,X1) | v1_xboole_0(X1) | ~sP0(X1,X2)) )),
% 0.19/0.46    inference(subsumption_resolution,[],[f88,f57])).
% 0.19/0.46  fof(f57,plain,(
% 0.19/0.46    ( ! [X0,X1] : (v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0) | ~sP0(X0,X1)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f36])).
% 0.19/0.46  fof(f36,plain,(
% 0.19/0.46    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) & v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0) & v1_funct_1(X1)) | ~sP0(X0,X1))),
% 0.19/0.46    inference(rectify,[],[f35])).
% 0.19/0.46  fof(f35,plain,(
% 0.19/0.46    ! [X0,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) & v1_funct_1(X2)) | ~sP0(X0,X2))),
% 0.19/0.46    inference(nnf_transformation,[],[f23])).
% 0.19/0.46  fof(f88,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (sP3(X0,X1,X2) | ~v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) | ~v8_relat_2(X0) | ~v3_relat_2(X0) | ~v1_partfun1(X0,X1) | v1_xboole_0(X1) | ~sP0(X1,X2)) )),
% 0.19/0.46    inference(subsumption_resolution,[],[f86,f56])).
% 0.19/0.46  fof(f56,plain,(
% 0.19/0.46    ( ! [X0,X1] : (~sP0(X0,X1) | v1_funct_1(X1)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f36])).
% 0.19/0.46  fof(f86,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (sP3(X0,X1,X2) | ~v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1) | ~v1_funct_1(X2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) | ~v8_relat_2(X0) | ~v3_relat_2(X0) | ~v1_partfun1(X0,X1) | v1_xboole_0(X1) | ~sP0(X1,X2)) )),
% 0.19/0.46    inference(resolution,[],[f69,f58])).
% 0.19/0.46  fof(f58,plain,(
% 0.19/0.46    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~sP0(X0,X1)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f36])).
% 0.19/0.46  fof(f69,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | sP3(X1,X0,X2) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0) | v1_xboole_0(X0)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f29])).
% 0.19/0.46  fof(f29,plain,(
% 0.19/0.46    ! [X0,X1,X2] : (sP3(X1,X0,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0) | v1_xboole_0(X0))),
% 0.19/0.46    inference(definition_folding,[],[f22,f28])).
% 0.19/0.46  fof(f28,plain,(
% 0.19/0.46    ! [X1,X0,X2] : ((m1_subset_1(k3_filter_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1)))) & v1_funct_2(k3_filter_1(X0,X1,X2),k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1)) & v1_funct_1(k3_filter_1(X0,X1,X2))) | ~sP3(X1,X0,X2))),
% 0.19/0.46    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.19/0.46  fof(f22,plain,(
% 0.19/0.46    ! [X0,X1,X2] : ((m1_subset_1(k3_filter_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1)))) & v1_funct_2(k3_filter_1(X0,X1,X2),k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1)) & v1_funct_1(k3_filter_1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0) | v1_xboole_0(X0))),
% 0.19/0.46    inference(flattening,[],[f21])).
% 0.19/0.46  fof(f21,plain,(
% 0.19/0.46    ! [X0,X1,X2] : ((m1_subset_1(k3_filter_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1)))) & v1_funct_2(k3_filter_1(X0,X1,X2),k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1)) & v1_funct_1(k3_filter_1(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0) | v1_xboole_0(X0)))),
% 0.19/0.46    inference(ennf_transformation,[],[f4])).
% 0.19/0.46  fof(f4,axiom,(
% 0.19/0.46    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) & v1_funct_1(X2) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v8_relat_2(X1) & v3_relat_2(X1) & v1_partfun1(X1,X0) & ~v1_xboole_0(X0)) => (m1_subset_1(k3_filter_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1)))) & v1_funct_2(k3_filter_1(X0,X1,X2),k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1)) & v1_funct_1(k3_filter_1(X0,X1,X2))))),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_filter_1)).
% 0.19/0.46  fof(f163,plain,(
% 0.19/0.46    ~sP3(sK5,sK4,sK6) | spl8_2),
% 0.19/0.46    inference(avatar_component_clause,[],[f161])).
% 0.19/0.46  fof(f161,plain,(
% 0.19/0.46    spl8_2 <=> sP3(sK5,sK4,sK6)),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.19/0.46  fof(f167,plain,(
% 0.19/0.46    spl8_1),
% 0.19/0.46    inference(avatar_contradiction_clause,[],[f166])).
% 0.19/0.46  fof(f166,plain,(
% 0.19/0.46    $false | spl8_1),
% 0.19/0.46    inference(subsumption_resolution,[],[f165,f79])).
% 0.19/0.46  fof(f79,plain,(
% 0.19/0.46    sP0(sK4,sK7)),
% 0.19/0.46    inference(subsumption_resolution,[],[f78,f43])).
% 0.19/0.46  fof(f78,plain,(
% 0.19/0.46    sP0(sK4,sK7) | v1_xboole_0(sK4)),
% 0.19/0.46    inference(subsumption_resolution,[],[f75,f71])).
% 0.19/0.46  fof(f75,plain,(
% 0.19/0.46    sP0(sK4,sK7) | ~v1_relat_1(sK5) | v1_xboole_0(sK4)),
% 0.19/0.46    inference(resolution,[],[f59,f49])).
% 0.19/0.46  fof(f49,plain,(
% 0.19/0.46    m2_filter_1(sK7,sK4,sK5)),
% 0.19/0.46    inference(cnf_transformation,[],[f34])).
% 0.19/0.46  fof(f165,plain,(
% 0.19/0.46    ~sP0(sK4,sK7) | spl8_1),
% 0.19/0.46    inference(resolution,[],[f159,f96])).
% 0.19/0.46  fof(f159,plain,(
% 0.19/0.46    ~sP3(sK5,sK4,sK7) | spl8_1),
% 0.19/0.46    inference(avatar_component_clause,[],[f157])).
% 0.19/0.46  fof(f157,plain,(
% 0.19/0.46    spl8_1 <=> sP3(sK5,sK4,sK7)),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.19/0.46  fof(f164,plain,(
% 0.19/0.46    ~spl8_1 | ~spl8_2),
% 0.19/0.46    inference(avatar_split_clause,[],[f155,f161,f157])).
% 0.19/0.46  fof(f155,plain,(
% 0.19/0.46    ~sP3(sK5,sK4,sK6) | ~sP3(sK5,sK4,sK7)),
% 0.19/0.46    inference(subsumption_resolution,[],[f154,f48])).
% 0.19/0.46  fof(f154,plain,(
% 0.19/0.46    ~sP3(sK5,sK4,sK6) | ~sP3(sK5,sK4,sK7) | ~m2_filter_1(sK6,sK4,sK5)),
% 0.19/0.46    inference(subsumption_resolution,[],[f153,f116])).
% 0.19/0.46  fof(f116,plain,(
% 0.19/0.46    r4_binop_1(sK4,sK6,sK7)),
% 0.19/0.46    inference(resolution,[],[f113,f62])).
% 0.19/0.46  fof(f62,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | r4_binop_1(X2,X1,X0)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f40])).
% 0.19/0.46  fof(f40,plain,(
% 0.19/0.46    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ~r5_binop_1(X2,X1,X0) | ~r4_binop_1(X2,X1,X0)) & ((r5_binop_1(X2,X1,X0) & r4_binop_1(X2,X1,X0)) | ~sP1(X0,X1,X2)))),
% 0.19/0.46    inference(rectify,[],[f39])).
% 0.19/0.46  fof(f39,plain,(
% 0.19/0.46    ! [X2,X1,X0] : ((sP1(X2,X1,X0) | ~r5_binop_1(X0,X1,X2) | ~r4_binop_1(X0,X1,X2)) & ((r5_binop_1(X0,X1,X2) & r4_binop_1(X0,X1,X2)) | ~sP1(X2,X1,X0)))),
% 0.19/0.46    inference(flattening,[],[f38])).
% 0.19/0.46  fof(f38,plain,(
% 0.19/0.46    ! [X2,X1,X0] : ((sP1(X2,X1,X0) | (~r5_binop_1(X0,X1,X2) | ~r4_binop_1(X0,X1,X2))) & ((r5_binop_1(X0,X1,X2) & r4_binop_1(X0,X1,X2)) | ~sP1(X2,X1,X0)))),
% 0.19/0.46    inference(nnf_transformation,[],[f25])).
% 0.19/0.46  fof(f25,plain,(
% 0.19/0.46    ! [X2,X1,X0] : (sP1(X2,X1,X0) <=> (r5_binop_1(X0,X1,X2) & r4_binop_1(X0,X1,X2)))),
% 0.19/0.46    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.19/0.46  fof(f113,plain,(
% 0.19/0.46    sP1(sK7,sK6,sK4)),
% 0.19/0.46    inference(subsumption_resolution,[],[f112,f79])).
% 0.19/0.46  fof(f112,plain,(
% 0.19/0.46    ~sP0(sK4,sK7) | sP1(sK7,sK6,sK4)),
% 0.19/0.46    inference(subsumption_resolution,[],[f111,f77])).
% 0.19/0.46  fof(f111,plain,(
% 0.19/0.46    ~sP0(sK4,sK6) | ~sP0(sK4,sK7) | sP1(sK7,sK6,sK4)),
% 0.19/0.46    inference(resolution,[],[f110,f50])).
% 0.19/0.46  fof(f50,plain,(
% 0.19/0.46    r6_binop_1(sK4,sK6,sK7)),
% 0.19/0.46    inference(cnf_transformation,[],[f34])).
% 0.19/0.46  fof(f110,plain,(
% 0.19/0.46    ( ! [X4,X5,X3] : (~r6_binop_1(X3,X5,X4) | ~sP0(X3,X5) | ~sP0(X3,X4) | sP1(X4,X5,X3)) )),
% 0.19/0.46    inference(resolution,[],[f106,f60])).
% 0.19/0.46  fof(f60,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (~sP2(X0,X1,X2) | ~r6_binop_1(X0,X1,X2) | sP1(X2,X1,X0)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f37])).
% 0.19/0.46  fof(f37,plain,(
% 0.19/0.46    ! [X0,X1,X2] : (((r6_binop_1(X0,X1,X2) | ~sP1(X2,X1,X0)) & (sP1(X2,X1,X0) | ~r6_binop_1(X0,X1,X2))) | ~sP2(X0,X1,X2))),
% 0.19/0.46    inference(nnf_transformation,[],[f26])).
% 0.19/0.46  fof(f26,plain,(
% 0.19/0.46    ! [X0,X1,X2] : ((r6_binop_1(X0,X1,X2) <=> sP1(X2,X1,X0)) | ~sP2(X0,X1,X2))),
% 0.19/0.46    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.19/0.46  fof(f106,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (sP2(X0,X1,X2) | ~sP0(X0,X2) | ~sP0(X0,X1)) )),
% 0.19/0.46    inference(subsumption_resolution,[],[f105,f57])).
% 0.19/0.46  fof(f105,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (sP2(X0,X1,X2) | ~v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0) | ~sP0(X0,X2) | ~sP0(X0,X1)) )),
% 0.19/0.46    inference(subsumption_resolution,[],[f103,f56])).
% 0.19/0.46  fof(f103,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (sP2(X0,X1,X2) | ~v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X1) | ~sP0(X0,X2) | ~sP0(X0,X1)) )),
% 0.19/0.46    inference(resolution,[],[f100,f58])).
% 0.19/0.46  fof(f100,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | sP2(X0,X1,X2) | ~v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X1) | ~sP0(X0,X2)) )),
% 0.19/0.46    inference(subsumption_resolution,[],[f99,f57])).
% 0.19/0.46  fof(f99,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (sP2(X0,X1,X2) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X1) | ~sP0(X0,X2)) )),
% 0.19/0.46    inference(subsumption_resolution,[],[f97,f56])).
% 0.19/0.46  fof(f97,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (sP2(X0,X1,X2) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X1) | ~sP0(X0,X2)) )),
% 0.19/0.46    inference(resolution,[],[f65,f58])).
% 0.19/0.46  fof(f65,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | sP2(X0,X1,X2) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X1)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f27])).
% 0.19/0.46  fof(f27,plain,(
% 0.19/0.46    ! [X0,X1] : (! [X2] : (sP2(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X1))),
% 0.19/0.46    inference(definition_folding,[],[f20,f26,f25])).
% 0.19/0.46  fof(f20,plain,(
% 0.19/0.46    ! [X0,X1] : (! [X2] : ((r6_binop_1(X0,X1,X2) <=> (r5_binop_1(X0,X1,X2) & r4_binop_1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X1))),
% 0.19/0.46    inference(flattening,[],[f19])).
% 0.19/0.46  fof(f19,plain,(
% 0.19/0.46    ! [X0,X1] : (! [X2] : ((r6_binop_1(X0,X1,X2) <=> (r5_binop_1(X0,X1,X2) & r4_binop_1(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X1)))),
% 0.19/0.46    inference(ennf_transformation,[],[f3])).
% 0.19/0.46  fof(f3,axiom,(
% 0.19/0.46    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) & v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) & v1_funct_1(X2)) => (r6_binop_1(X0,X1,X2) <=> (r5_binop_1(X0,X1,X2) & r4_binop_1(X0,X1,X2)))))),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_binop_1)).
% 0.19/0.46  fof(f153,plain,(
% 0.19/0.46    ~r4_binop_1(sK4,sK6,sK7) | ~sP3(sK5,sK4,sK6) | ~sP3(sK5,sK4,sK7) | ~m2_filter_1(sK6,sK4,sK5)),
% 0.19/0.46    inference(subsumption_resolution,[],[f152,f115])).
% 0.19/0.46  fof(f115,plain,(
% 0.19/0.46    r5_binop_1(sK4,sK6,sK7)),
% 0.19/0.46    inference(resolution,[],[f113,f63])).
% 0.19/0.46  fof(f63,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | r5_binop_1(X2,X1,X0)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f40])).
% 0.19/0.46  fof(f152,plain,(
% 0.19/0.46    ~r5_binop_1(sK4,sK6,sK7) | ~r4_binop_1(sK4,sK6,sK7) | ~sP3(sK5,sK4,sK6) | ~sP3(sK5,sK4,sK7) | ~m2_filter_1(sK6,sK4,sK5)),
% 0.19/0.46    inference(subsumption_resolution,[],[f151,f49])).
% 0.19/0.46  fof(f151,plain,(
% 0.19/0.46    ~m2_filter_1(sK7,sK4,sK5) | ~r5_binop_1(sK4,sK6,sK7) | ~r4_binop_1(sK4,sK6,sK7) | ~sP3(sK5,sK4,sK6) | ~sP3(sK5,sK4,sK7) | ~m2_filter_1(sK6,sK4,sK5)),
% 0.19/0.46    inference(subsumption_resolution,[],[f150,f43])).
% 0.19/0.46  fof(f150,plain,(
% 0.19/0.46    v1_xboole_0(sK4) | ~m2_filter_1(sK7,sK4,sK5) | ~r5_binop_1(sK4,sK6,sK7) | ~r4_binop_1(sK4,sK6,sK7) | ~sP3(sK5,sK4,sK6) | ~sP3(sK5,sK4,sK7) | ~m2_filter_1(sK6,sK4,sK5)),
% 0.19/0.46    inference(subsumption_resolution,[],[f149,f44])).
% 0.19/0.46  fof(f149,plain,(
% 0.19/0.46    ~v1_partfun1(sK5,sK4) | v1_xboole_0(sK4) | ~m2_filter_1(sK7,sK4,sK5) | ~r5_binop_1(sK4,sK6,sK7) | ~r4_binop_1(sK4,sK6,sK7) | ~sP3(sK5,sK4,sK6) | ~sP3(sK5,sK4,sK7) | ~m2_filter_1(sK6,sK4,sK5)),
% 0.19/0.46    inference(subsumption_resolution,[],[f148,f45])).
% 0.19/0.46  fof(f148,plain,(
% 0.19/0.46    ~v3_relat_2(sK5) | ~v1_partfun1(sK5,sK4) | v1_xboole_0(sK4) | ~m2_filter_1(sK7,sK4,sK5) | ~r5_binop_1(sK4,sK6,sK7) | ~r4_binop_1(sK4,sK6,sK7) | ~sP3(sK5,sK4,sK6) | ~sP3(sK5,sK4,sK7) | ~m2_filter_1(sK6,sK4,sK5)),
% 0.19/0.46    inference(subsumption_resolution,[],[f147,f46])).
% 0.19/0.46  fof(f147,plain,(
% 0.19/0.46    ~v8_relat_2(sK5) | ~v3_relat_2(sK5) | ~v1_partfun1(sK5,sK4) | v1_xboole_0(sK4) | ~m2_filter_1(sK7,sK4,sK5) | ~r5_binop_1(sK4,sK6,sK7) | ~r4_binop_1(sK4,sK6,sK7) | ~sP3(sK5,sK4,sK6) | ~sP3(sK5,sK4,sK7) | ~m2_filter_1(sK6,sK4,sK5)),
% 0.19/0.46    inference(subsumption_resolution,[],[f139,f47])).
% 0.19/0.46  fof(f139,plain,(
% 0.19/0.46    ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) | ~v8_relat_2(sK5) | ~v3_relat_2(sK5) | ~v1_partfun1(sK5,sK4) | v1_xboole_0(sK4) | ~m2_filter_1(sK7,sK4,sK5) | ~r5_binop_1(sK4,sK6,sK7) | ~r4_binop_1(sK4,sK6,sK7) | ~sP3(sK5,sK4,sK6) | ~sP3(sK5,sK4,sK7) | ~m2_filter_1(sK6,sK4,sK5)),
% 0.19/0.46    inference(resolution,[],[f133,f51])).
% 0.19/0.46  fof(f51,plain,(
% 0.19/0.46    ~r6_binop_1(k8_eqrel_1(sK4,sK5),k3_filter_1(sK4,sK5,sK6),k3_filter_1(sK4,sK5,sK7))),
% 0.19/0.46    inference(cnf_transformation,[],[f34])).
% 0.19/0.46  fof(f133,plain,(
% 0.19/0.46    ( ! [X2,X0,X3,X1] : (r6_binop_1(k8_eqrel_1(X1,X2),k3_filter_1(X1,X2,X0),k3_filter_1(X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) | ~v8_relat_2(X2) | ~v3_relat_2(X2) | ~v1_partfun1(X2,X1) | v1_xboole_0(X1) | ~m2_filter_1(X3,X1,X2) | ~r5_binop_1(X1,X0,X3) | ~r4_binop_1(X1,X0,X3) | ~sP3(X2,X1,X0) | ~sP3(X2,X1,X3) | ~m2_filter_1(X0,X1,X2)) )),
% 0.19/0.46    inference(resolution,[],[f132,f129])).
% 0.19/0.46  fof(f129,plain,(
% 0.19/0.46    ( ! [X2,X0,X3,X1] : (~sP1(k3_filter_1(X1,X0,X2),k3_filter_1(X1,X0,X3),k8_eqrel_1(X1,X0)) | ~sP3(X0,X1,X3) | ~sP3(X0,X1,X2) | r6_binop_1(k8_eqrel_1(X1,X0),k3_filter_1(X1,X0,X3),k3_filter_1(X1,X0,X2))) )),
% 0.19/0.46    inference(resolution,[],[f126,f61])).
% 0.19/0.46  fof(f61,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (~sP2(X0,X1,X2) | ~sP1(X2,X1,X0) | r6_binop_1(X0,X1,X2)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f37])).
% 0.19/0.46  fof(f126,plain,(
% 0.19/0.46    ( ! [X6,X4,X7,X5] : (sP2(k8_eqrel_1(X4,X5),k3_filter_1(X4,X5,X6),k3_filter_1(X4,X5,X7)) | ~sP3(X5,X4,X7) | ~sP3(X5,X4,X6)) )),
% 0.19/0.46    inference(subsumption_resolution,[],[f125,f66])).
% 0.19/0.46  fof(f66,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (v1_funct_1(k3_filter_1(X1,X0,X2)) | ~sP3(X0,X1,X2)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f42])).
% 0.19/0.46  fof(f42,plain,(
% 0.19/0.46    ! [X0,X1,X2] : ((m1_subset_1(k3_filter_1(X1,X0,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X1,X0),k8_eqrel_1(X1,X0)),k8_eqrel_1(X1,X0)))) & v1_funct_2(k3_filter_1(X1,X0,X2),k2_zfmisc_1(k8_eqrel_1(X1,X0),k8_eqrel_1(X1,X0)),k8_eqrel_1(X1,X0)) & v1_funct_1(k3_filter_1(X1,X0,X2))) | ~sP3(X0,X1,X2))),
% 0.19/0.46    inference(rectify,[],[f41])).
% 0.19/0.46  fof(f41,plain,(
% 0.19/0.46    ! [X1,X0,X2] : ((m1_subset_1(k3_filter_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1)))) & v1_funct_2(k3_filter_1(X0,X1,X2),k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1)) & v1_funct_1(k3_filter_1(X0,X1,X2))) | ~sP3(X1,X0,X2))),
% 0.19/0.46    inference(nnf_transformation,[],[f28])).
% 0.19/0.46  fof(f125,plain,(
% 0.19/0.46    ( ! [X6,X4,X7,X5] : (sP2(k8_eqrel_1(X4,X5),k3_filter_1(X4,X5,X6),k3_filter_1(X4,X5,X7)) | ~v1_funct_1(k3_filter_1(X4,X5,X6)) | ~sP3(X5,X4,X7) | ~sP3(X5,X4,X6)) )),
% 0.19/0.46    inference(subsumption_resolution,[],[f122,f67])).
% 0.19/0.46  fof(f67,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (v1_funct_2(k3_filter_1(X1,X0,X2),k2_zfmisc_1(k8_eqrel_1(X1,X0),k8_eqrel_1(X1,X0)),k8_eqrel_1(X1,X0)) | ~sP3(X0,X1,X2)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f42])).
% 0.19/0.46  fof(f122,plain,(
% 0.19/0.46    ( ! [X6,X4,X7,X5] : (sP2(k8_eqrel_1(X4,X5),k3_filter_1(X4,X5,X6),k3_filter_1(X4,X5,X7)) | ~v1_funct_2(k3_filter_1(X4,X5,X6),k2_zfmisc_1(k8_eqrel_1(X4,X5),k8_eqrel_1(X4,X5)),k8_eqrel_1(X4,X5)) | ~v1_funct_1(k3_filter_1(X4,X5,X6)) | ~sP3(X5,X4,X7) | ~sP3(X5,X4,X6)) )),
% 0.19/0.46    inference(resolution,[],[f102,f68])).
% 0.19/0.46  fof(f68,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (m1_subset_1(k3_filter_1(X1,X0,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X1,X0),k8_eqrel_1(X1,X0)),k8_eqrel_1(X1,X0)))) | ~sP3(X0,X1,X2)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f42])).
% 0.19/0.46  fof(f102,plain,(
% 0.19/0.46    ( ! [X6,X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X3,X4),k8_eqrel_1(X3,X4)),k8_eqrel_1(X3,X4)))) | sP2(k8_eqrel_1(X3,X4),X5,k3_filter_1(X3,X4,X6)) | ~v1_funct_2(X5,k2_zfmisc_1(k8_eqrel_1(X3,X4),k8_eqrel_1(X3,X4)),k8_eqrel_1(X3,X4)) | ~v1_funct_1(X5) | ~sP3(X4,X3,X6)) )),
% 0.19/0.46    inference(subsumption_resolution,[],[f101,f66])).
% 0.19/0.46  fof(f101,plain,(
% 0.19/0.46    ( ! [X6,X4,X5,X3] : (sP2(k8_eqrel_1(X3,X4),X5,k3_filter_1(X3,X4,X6)) | ~v1_funct_1(k3_filter_1(X3,X4,X6)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X3,X4),k8_eqrel_1(X3,X4)),k8_eqrel_1(X3,X4)))) | ~v1_funct_2(X5,k2_zfmisc_1(k8_eqrel_1(X3,X4),k8_eqrel_1(X3,X4)),k8_eqrel_1(X3,X4)) | ~v1_funct_1(X5) | ~sP3(X4,X3,X6)) )),
% 0.19/0.46    inference(subsumption_resolution,[],[f98,f67])).
% 0.19/0.46  fof(f98,plain,(
% 0.19/0.46    ( ! [X6,X4,X5,X3] : (sP2(k8_eqrel_1(X3,X4),X5,k3_filter_1(X3,X4,X6)) | ~v1_funct_2(k3_filter_1(X3,X4,X6),k2_zfmisc_1(k8_eqrel_1(X3,X4),k8_eqrel_1(X3,X4)),k8_eqrel_1(X3,X4)) | ~v1_funct_1(k3_filter_1(X3,X4,X6)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X3,X4),k8_eqrel_1(X3,X4)),k8_eqrel_1(X3,X4)))) | ~v1_funct_2(X5,k2_zfmisc_1(k8_eqrel_1(X3,X4),k8_eqrel_1(X3,X4)),k8_eqrel_1(X3,X4)) | ~v1_funct_1(X5) | ~sP3(X4,X3,X6)) )),
% 0.19/0.46    inference(resolution,[],[f65,f68])).
% 0.19/0.46  fof(f132,plain,(
% 0.19/0.46    ( ! [X2,X0,X3,X1] : (sP1(k3_filter_1(X1,X2,X0),k3_filter_1(X1,X2,X3),k8_eqrel_1(X1,X2)) | ~m2_filter_1(X3,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) | ~v8_relat_2(X2) | ~v3_relat_2(X2) | ~v1_partfun1(X2,X1) | v1_xboole_0(X1) | ~m2_filter_1(X0,X1,X2) | ~r5_binop_1(X1,X3,X0) | ~r4_binop_1(X1,X3,X0)) )),
% 0.19/0.46    inference(duplicate_literal_removal,[],[f131])).
% 0.19/0.46  fof(f131,plain,(
% 0.19/0.46    ( ! [X2,X0,X3,X1] : (~m2_filter_1(X0,X1,X2) | ~m2_filter_1(X3,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) | ~v8_relat_2(X2) | ~v3_relat_2(X2) | ~v1_partfun1(X2,X1) | v1_xboole_0(X1) | sP1(k3_filter_1(X1,X2,X0),k3_filter_1(X1,X2,X3),k8_eqrel_1(X1,X2)) | ~r5_binop_1(X1,X3,X0) | ~r4_binop_1(X1,X3,X0) | ~m2_filter_1(X0,X1,X2) | ~m2_filter_1(X3,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) | ~v8_relat_2(X2) | ~v3_relat_2(X2) | ~v1_partfun1(X2,X1) | v1_xboole_0(X1)) )),
% 0.19/0.46    inference(resolution,[],[f120,f53])).
% 0.19/0.46  fof(f53,plain,(
% 0.19/0.46    ( ! [X2,X0,X3,X1] : (r4_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) | ~r4_binop_1(X0,X2,X3) | ~m2_filter_1(X3,X0,X1) | ~m2_filter_1(X2,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0) | v1_xboole_0(X0)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f15])).
% 0.19/0.46  fof(f15,plain,(
% 0.19/0.46    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r4_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) | ~r4_binop_1(X0,X2,X3) | ~m2_filter_1(X3,X0,X1)) | ~m2_filter_1(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0)) | v1_xboole_0(X0))),
% 0.19/0.46    inference(flattening,[],[f14])).
% 0.19/0.46  fof(f14,plain,(
% 0.19/0.46    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r4_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) | ~r4_binop_1(X0,X2,X3)) | ~m2_filter_1(X3,X0,X1)) | ~m2_filter_1(X2,X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0))) | v1_xboole_0(X0))),
% 0.19/0.46    inference(ennf_transformation,[],[f7])).
% 0.19/0.46  fof(f7,axiom,(
% 0.19/0.46    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v8_relat_2(X1) & v3_relat_2(X1) & v1_partfun1(X1,X0)) => ! [X2] : (m2_filter_1(X2,X0,X1) => ! [X3] : (m2_filter_1(X3,X0,X1) => (r4_binop_1(X0,X2,X3) => r4_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3)))))))),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_filter_1)).
% 0.19/0.46  fof(f120,plain,(
% 0.19/0.46    ( ! [X2,X0,X3,X1] : (~r4_binop_1(k8_eqrel_1(X0,X3),k3_filter_1(X0,X3,X1),k3_filter_1(X0,X3,X2)) | ~m2_filter_1(X2,X0,X3) | ~m2_filter_1(X1,X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X3) | ~v3_relat_2(X3) | ~v1_partfun1(X3,X0) | v1_xboole_0(X0) | sP1(k3_filter_1(X0,X3,X2),k3_filter_1(X0,X3,X1),k8_eqrel_1(X0,X3)) | ~r5_binop_1(X0,X1,X2)) )),
% 0.19/0.46    inference(resolution,[],[f52,f64])).
% 0.19/0.46  fof(f64,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (~r5_binop_1(X2,X1,X0) | sP1(X0,X1,X2) | ~r4_binop_1(X2,X1,X0)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f40])).
% 0.19/0.46  fof(f52,plain,(
% 0.19/0.46    ( ! [X2,X0,X3,X1] : (r5_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) | ~r5_binop_1(X0,X2,X3) | ~m2_filter_1(X3,X0,X1) | ~m2_filter_1(X2,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0) | v1_xboole_0(X0)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f13])).
% 0.19/0.46  fof(f13,plain,(
% 0.19/0.46    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r5_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) | ~r5_binop_1(X0,X2,X3) | ~m2_filter_1(X3,X0,X1)) | ~m2_filter_1(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0)) | v1_xboole_0(X0))),
% 0.19/0.46    inference(flattening,[],[f12])).
% 0.19/0.46  fof(f12,plain,(
% 0.19/0.46    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r5_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) | ~r5_binop_1(X0,X2,X3)) | ~m2_filter_1(X3,X0,X1)) | ~m2_filter_1(X2,X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0))) | v1_xboole_0(X0))),
% 0.19/0.46    inference(ennf_transformation,[],[f6])).
% 0.19/0.46  fof(f6,axiom,(
% 0.19/0.46    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v8_relat_2(X1) & v3_relat_2(X1) & v1_partfun1(X1,X0)) => ! [X2] : (m2_filter_1(X2,X0,X1) => ! [X3] : (m2_filter_1(X3,X0,X1) => (r5_binop_1(X0,X2,X3) => r5_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3)))))))),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_filter_1)).
% 0.19/0.46  % SZS output end Proof for theBenchmark
% 0.19/0.46  % (1278)------------------------------
% 0.19/0.46  % (1278)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.46  % (1278)Termination reason: Refutation
% 0.19/0.46  
% 0.19/0.46  % (1278)Memory used [KB]: 5500
% 0.19/0.46  % (1278)Time elapsed: 0.062 s
% 0.19/0.46  % (1278)------------------------------
% 0.19/0.46  % (1278)------------------------------
% 0.19/0.47  % (1270)Success in time 0.113 s
%------------------------------------------------------------------------------
