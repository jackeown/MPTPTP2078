%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:32 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  158 (2708 expanded)
%              Number of leaves         :   23 ( 978 expanded)
%              Depth                    :   32
%              Number of atoms          :  546 (20244 expanded)
%              Number of equality atoms :  119 (2971 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f535,plain,(
    $false ),
    inference(subsumption_resolution,[],[f520,f68])).

fof(f68,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f520,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(backward_demodulation,[],[f333,f513])).

fof(f513,plain,(
    k1_xboole_0 = k2_relat_1(sK7) ),
    inference(resolution,[],[f512,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f512,plain,(
    sP1(k2_struct_0(sK5),k2_relat_1(sK7)) ),
    inference(subsumption_resolution,[],[f464,f511])).

fof(f511,plain,(
    k2_struct_0(sK5) != k1_relat_1(sK7) ),
    inference(forward_demodulation,[],[f510,f223])).

fof(f223,plain,(
    k1_relat_1(sK7) = k2_relat_1(k2_funct_1(sK7)) ),
    inference(subsumption_resolution,[],[f222,f62])).

fof(f62,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,
    ( ~ r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK6),k2_tops_2(u1_struct_0(sK6),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),u1_struct_0(sK6),sK7)),sK7)
    & v2_funct_1(sK7)
    & k2_struct_0(sK6) = k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),sK7)
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
    & v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6))
    & v1_funct_1(sK7)
    & l1_struct_0(sK6)
    & ~ v2_struct_0(sK6)
    & l1_struct_0(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f18,f49,f48,f47])).

fof(f47,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
                & v2_funct_1(X2)
                & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_struct_0(X1)
            & ~ v2_struct_0(X1) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(sK5),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),u1_struct_0(X1),X2)),X2)
              & v2_funct_1(X2)
              & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK5),u1_struct_0(X1),X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK5),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r2_funct_2(u1_struct_0(sK5),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),u1_struct_0(X1),X2)),X2)
            & v2_funct_1(X2)
            & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK5),u1_struct_0(X1),X2)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK5),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_struct_0(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ~ r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK6),k2_tops_2(u1_struct_0(sK6),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),u1_struct_0(sK6),X2)),X2)
          & v2_funct_1(X2)
          & k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),X2) = k2_struct_0(sK6)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
          & v1_funct_2(X2,u1_struct_0(sK5),u1_struct_0(sK6))
          & v1_funct_1(X2) )
      & l1_struct_0(sK6)
      & ~ v2_struct_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ? [X2] :
        ( ~ r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK6),k2_tops_2(u1_struct_0(sK6),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),u1_struct_0(sK6),X2)),X2)
        & v2_funct_1(X2)
        & k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),X2) = k2_struct_0(sK6)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
        & v1_funct_2(X2,u1_struct_0(sK5),u1_struct_0(sK6))
        & v1_funct_1(X2) )
   => ( ~ r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK6),k2_tops_2(u1_struct_0(sK6),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),u1_struct_0(sK6),sK7)),sK7)
      & v2_funct_1(sK7)
      & k2_struct_0(sK6) = k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),sK7)
      & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
      & v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6))
      & v1_funct_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( ( l1_struct_0(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( ( v2_funct_1(X2)
                    & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
                 => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( ( l1_struct_0(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
               => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tops_2)).

fof(f222,plain,
    ( k1_relat_1(sK7) = k2_relat_1(k2_funct_1(sK7))
    | ~ v1_funct_1(sK7) ),
    inference(subsumption_resolution,[],[f216,f66])).

fof(f66,plain,(
    v2_funct_1(sK7) ),
    inference(cnf_transformation,[],[f50])).

fof(f216,plain,
    ( k1_relat_1(sK7) = k2_relat_1(k2_funct_1(sK7))
    | ~ v2_funct_1(sK7)
    | ~ v1_funct_1(sK7) ),
    inference(resolution,[],[f212,f78])).

fof(f78,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f212,plain,(
    v1_relat_1(sK7) ),
    inference(subsumption_resolution,[],[f199,f79])).

fof(f79,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f199,plain,
    ( v1_relat_1(sK7)
    | ~ v1_relat_1(k2_zfmisc_1(k2_struct_0(sK5),k2_struct_0(sK6))) ),
    inference(resolution,[],[f188,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f188,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),k2_struct_0(sK6)))) ),
    inference(forward_demodulation,[],[f187,f104])).

fof(f104,plain,(
    u1_struct_0(sK5) = k2_struct_0(sK5) ),
    inference(resolution,[],[f59,f69])).

fof(f69,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f59,plain,(
    l1_struct_0(sK5) ),
    inference(cnf_transformation,[],[f50])).

fof(f187,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),k2_struct_0(sK6)))) ),
    inference(forward_demodulation,[],[f64,f107])).

fof(f107,plain,(
    u1_struct_0(sK6) = k2_struct_0(sK6) ),
    inference(resolution,[],[f61,f69])).

fof(f61,plain,(
    l1_struct_0(sK6) ),
    inference(cnf_transformation,[],[f50])).

fof(f64,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) ),
    inference(cnf_transformation,[],[f50])).

fof(f510,plain,(
    k2_struct_0(sK5) != k2_relat_1(k2_funct_1(sK7)) ),
    inference(subsumption_resolution,[],[f509,f416])).

fof(f416,plain,(
    m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK7),k2_struct_0(sK5)))) ),
    inference(resolution,[],[f408,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | ~ sP4(X0,X1,X2) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | ~ sP4(X0,X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f408,plain,(
    sP4(k2_struct_0(sK5),k2_relat_1(sK7),sK7) ),
    inference(subsumption_resolution,[],[f407,f62])).

fof(f407,plain,
    ( sP4(k2_struct_0(sK5),k2_relat_1(sK7),sK7)
    | ~ v1_funct_1(sK7) ),
    inference(subsumption_resolution,[],[f406,f331])).

% (8431)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
fof(f331,plain,(
    v1_funct_2(sK7,k2_struct_0(sK5),k2_relat_1(sK7)) ),
    inference(backward_demodulation,[],[f169,f273])).

fof(f273,plain,(
    k2_struct_0(sK6) = k2_relat_1(sK7) ),
    inference(subsumption_resolution,[],[f267,f188])).

fof(f267,plain,
    ( k2_struct_0(sK6) = k2_relat_1(sK7)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),k2_struct_0(sK6)))) ),
    inference(superposition,[],[f232,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f232,plain,(
    k2_struct_0(sK6) = k2_relset_1(k2_struct_0(sK5),k2_struct_0(sK6),sK7) ),
    inference(forward_demodulation,[],[f231,f104])).

fof(f231,plain,(
    k2_struct_0(sK6) = k2_relset_1(u1_struct_0(sK5),k2_struct_0(sK6),sK7) ),
    inference(forward_demodulation,[],[f65,f107])).

fof(f65,plain,(
    k2_struct_0(sK6) = k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),sK7) ),
    inference(cnf_transformation,[],[f50])).

fof(f169,plain,(
    v1_funct_2(sK7,k2_struct_0(sK5),k2_struct_0(sK6)) ),
    inference(backward_demodulation,[],[f151,f107])).

fof(f151,plain,(
    v1_funct_2(sK7,k2_struct_0(sK5),u1_struct_0(sK6)) ),
    inference(backward_demodulation,[],[f63,f104])).

fof(f63,plain,(
    v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f50])).

fof(f406,plain,
    ( sP4(k2_struct_0(sK5),k2_relat_1(sK7),sK7)
    | ~ v1_funct_2(sK7,k2_struct_0(sK5),k2_relat_1(sK7))
    | ~ v1_funct_1(sK7) ),
    inference(subsumption_resolution,[],[f405,f330])).

fof(f330,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),k2_relat_1(sK7)))) ),
    inference(backward_demodulation,[],[f188,f273])).

fof(f405,plain,
    ( sP4(k2_struct_0(sK5),k2_relat_1(sK7),sK7)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),k2_relat_1(sK7))))
    | ~ v1_funct_2(sK7,k2_struct_0(sK5),k2_relat_1(sK7))
    | ~ v1_funct_1(sK7) ),
    inference(subsumption_resolution,[],[f399,f66])).

fof(f399,plain,
    ( sP4(k2_struct_0(sK5),k2_relat_1(sK7),sK7)
    | ~ v2_funct_1(sK7)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),k2_relat_1(sK7))))
    | ~ v1_funct_2(sK7,k2_struct_0(sK5),k2_relat_1(sK7))
    | ~ v1_funct_1(sK7) ),
    inference(trivial_inequality_removal,[],[f398])).

fof(f398,plain,
    ( k2_relat_1(sK7) != k2_relat_1(sK7)
    | sP4(k2_struct_0(sK5),k2_relat_1(sK7),sK7)
    | ~ v2_funct_1(sK7)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),k2_relat_1(sK7))))
    | ~ v1_funct_2(sK7,k2_struct_0(sK5),k2_relat_1(sK7))
    | ~ v1_funct_1(sK7) ),
    inference(superposition,[],[f93,f329])).

fof(f329,plain,(
    k2_relat_1(sK7) = k2_relset_1(k2_struct_0(sK5),k2_relat_1(sK7),sK7) ),
    inference(backward_demodulation,[],[f232,f273])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( sP4(X0,X1,X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( sP4(X0,X1,X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(definition_folding,[],[f34,f45])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

fof(f509,plain,
    ( k2_struct_0(sK5) != k2_relat_1(k2_funct_1(sK7))
    | ~ m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK7),k2_struct_0(sK5)))) ),
    inference(superposition,[],[f502,f81])).

fof(f502,plain,(
    k2_struct_0(sK5) != k2_relset_1(k2_relat_1(sK7),k2_struct_0(sK5),k2_funct_1(sK7)) ),
    inference(subsumption_resolution,[],[f501,f392])).

fof(f392,plain,(
    r2_funct_2(k2_struct_0(sK5),k2_relat_1(sK7),sK7,sK7) ),
    inference(subsumption_resolution,[],[f391,f62])).

fof(f391,plain,
    ( r2_funct_2(k2_struct_0(sK5),k2_relat_1(sK7),sK7,sK7)
    | ~ v1_funct_1(sK7) ),
    inference(subsumption_resolution,[],[f379,f331])).

fof(f379,plain,
    ( r2_funct_2(k2_struct_0(sK5),k2_relat_1(sK7),sK7,sK7)
    | ~ v1_funct_2(sK7,k2_struct_0(sK5),k2_relat_1(sK7))
    | ~ v1_funct_1(sK7) ),
    inference(resolution,[],[f330,f102])).

fof(f102,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(duplicate_literal_removal,[],[f101])).

fof(f101,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f96])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_funct_2(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_funct_2(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

% (8442)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
fof(f501,plain,
    ( ~ r2_funct_2(k2_struct_0(sK5),k2_relat_1(sK7),sK7,sK7)
    | k2_struct_0(sK5) != k2_relset_1(k2_relat_1(sK7),k2_struct_0(sK5),k2_funct_1(sK7)) ),
    inference(forward_demodulation,[],[f500,f213])).

fof(f213,plain,(
    sK7 = k2_funct_1(k2_funct_1(sK7)) ),
    inference(resolution,[],[f212,f128])).

fof(f128,plain,
    ( ~ v1_relat_1(sK7)
    | sK7 = k2_funct_1(k2_funct_1(sK7)) ),
    inference(subsumption_resolution,[],[f122,f62])).

fof(f122,plain,
    ( sK7 = k2_funct_1(k2_funct_1(sK7))
    | ~ v1_funct_1(sK7)
    | ~ v1_relat_1(sK7) ),
    inference(resolution,[],[f66,f76])).

fof(f76,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

fof(f500,plain,
    ( ~ r2_funct_2(k2_struct_0(sK5),k2_relat_1(sK7),k2_funct_1(k2_funct_1(sK7)),sK7)
    | k2_struct_0(sK5) != k2_relset_1(k2_relat_1(sK7),k2_struct_0(sK5),k2_funct_1(sK7)) ),
    inference(subsumption_resolution,[],[f499,f229])).

fof(f229,plain,(
    v1_funct_1(k2_funct_1(sK7)) ),
    inference(resolution,[],[f214,f73])).

fof(f73,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ sP0(X0) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ sP0(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f214,plain,(
    sP0(sK7) ),
    inference(resolution,[],[f212,f129])).

fof(f129,plain,
    ( ~ v1_relat_1(sK7)
    | sP0(sK7) ),
    inference(subsumption_resolution,[],[f123,f62])).

fof(f123,plain,
    ( sP0(sK7)
    | ~ v1_funct_1(sK7)
    | ~ v1_relat_1(sK7) ),
    inference(resolution,[],[f66,f75])).

fof(f75,plain,(
    ! [X0] :
      ( sP0(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( sP0(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f24,f39])).

fof(f24,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).

fof(f499,plain,
    ( ~ r2_funct_2(k2_struct_0(sK5),k2_relat_1(sK7),k2_funct_1(k2_funct_1(sK7)),sK7)
    | k2_struct_0(sK5) != k2_relset_1(k2_relat_1(sK7),k2_struct_0(sK5),k2_funct_1(sK7))
    | ~ v1_funct_1(k2_funct_1(sK7)) ),
    inference(subsumption_resolution,[],[f498,f415])).

fof(f415,plain,(
    v1_funct_2(k2_funct_1(sK7),k2_relat_1(sK7),k2_struct_0(sK5)) ),
    inference(resolution,[],[f408,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_funct_1(X2),X1,X0)
      | ~ sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f498,plain,
    ( ~ r2_funct_2(k2_struct_0(sK5),k2_relat_1(sK7),k2_funct_1(k2_funct_1(sK7)),sK7)
    | k2_struct_0(sK5) != k2_relset_1(k2_relat_1(sK7),k2_struct_0(sK5),k2_funct_1(sK7))
    | ~ v1_funct_2(k2_funct_1(sK7),k2_relat_1(sK7),k2_struct_0(sK5))
    | ~ v1_funct_1(k2_funct_1(sK7)) ),
    inference(subsumption_resolution,[],[f497,f416])).

fof(f497,plain,
    ( ~ r2_funct_2(k2_struct_0(sK5),k2_relat_1(sK7),k2_funct_1(k2_funct_1(sK7)),sK7)
    | k2_struct_0(sK5) != k2_relset_1(k2_relat_1(sK7),k2_struct_0(sK5),k2_funct_1(sK7))
    | ~ m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK7),k2_struct_0(sK5))))
    | ~ v1_funct_2(k2_funct_1(sK7),k2_relat_1(sK7),k2_struct_0(sK5))
    | ~ v1_funct_1(k2_funct_1(sK7)) ),
    inference(subsumption_resolution,[],[f496,f230])).

fof(f230,plain,(
    v2_funct_1(k2_funct_1(sK7)) ),
    inference(resolution,[],[f214,f74])).

fof(f74,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f496,plain,
    ( ~ r2_funct_2(k2_struct_0(sK5),k2_relat_1(sK7),k2_funct_1(k2_funct_1(sK7)),sK7)
    | ~ v2_funct_1(k2_funct_1(sK7))
    | k2_struct_0(sK5) != k2_relset_1(k2_relat_1(sK7),k2_struct_0(sK5),k2_funct_1(sK7))
    | ~ m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK7),k2_struct_0(sK5))))
    | ~ v1_funct_2(k2_funct_1(sK7),k2_relat_1(sK7),k2_struct_0(sK5))
    | ~ v1_funct_1(k2_funct_1(sK7)) ),
    inference(superposition,[],[f467,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

fof(f467,plain,(
    ~ r2_funct_2(k2_struct_0(sK5),k2_relat_1(sK7),k2_tops_2(k2_relat_1(sK7),k2_struct_0(sK5),k2_funct_1(sK7)),sK7) ),
    inference(backward_demodulation,[],[f413,f404])).

fof(f404,plain,(
    k2_funct_1(sK7) = k2_tops_2(k2_struct_0(sK5),k2_relat_1(sK7),sK7) ),
    inference(subsumption_resolution,[],[f403,f62])).

fof(f403,plain,
    ( k2_funct_1(sK7) = k2_tops_2(k2_struct_0(sK5),k2_relat_1(sK7),sK7)
    | ~ v1_funct_1(sK7) ),
    inference(subsumption_resolution,[],[f402,f331])).

fof(f402,plain,
    ( k2_funct_1(sK7) = k2_tops_2(k2_struct_0(sK5),k2_relat_1(sK7),sK7)
    | ~ v1_funct_2(sK7,k2_struct_0(sK5),k2_relat_1(sK7))
    | ~ v1_funct_1(sK7) ),
    inference(subsumption_resolution,[],[f401,f330])).

fof(f401,plain,
    ( k2_funct_1(sK7) = k2_tops_2(k2_struct_0(sK5),k2_relat_1(sK7),sK7)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),k2_relat_1(sK7))))
    | ~ v1_funct_2(sK7,k2_struct_0(sK5),k2_relat_1(sK7))
    | ~ v1_funct_1(sK7) ),
    inference(subsumption_resolution,[],[f400,f66])).

fof(f400,plain,
    ( k2_funct_1(sK7) = k2_tops_2(k2_struct_0(sK5),k2_relat_1(sK7),sK7)
    | ~ v2_funct_1(sK7)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),k2_relat_1(sK7))))
    | ~ v1_funct_2(sK7,k2_struct_0(sK5),k2_relat_1(sK7))
    | ~ v1_funct_1(sK7) ),
    inference(trivial_inequality_removal,[],[f397])).

fof(f397,plain,
    ( k2_relat_1(sK7) != k2_relat_1(sK7)
    | k2_funct_1(sK7) = k2_tops_2(k2_struct_0(sK5),k2_relat_1(sK7),sK7)
    | ~ v2_funct_1(sK7)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),k2_relat_1(sK7))))
    | ~ v1_funct_2(sK7,k2_struct_0(sK5),k2_relat_1(sK7))
    | ~ v1_funct_1(sK7) ),
    inference(superposition,[],[f94,f329])).

fof(f413,plain,(
    ~ r2_funct_2(k2_struct_0(sK5),k2_relat_1(sK7),k2_tops_2(k2_relat_1(sK7),k2_struct_0(sK5),k2_tops_2(k2_struct_0(sK5),k2_relat_1(sK7),sK7)),sK7) ),
    inference(forward_demodulation,[],[f324,f273])).

fof(f324,plain,(
    ~ r2_funct_2(k2_struct_0(sK5),k2_struct_0(sK6),k2_tops_2(k2_struct_0(sK6),k2_struct_0(sK5),k2_tops_2(k2_struct_0(sK5),k2_struct_0(sK6),sK7)),sK7) ),
    inference(forward_demodulation,[],[f323,f104])).

fof(f323,plain,(
    ~ r2_funct_2(u1_struct_0(sK5),k2_struct_0(sK6),k2_tops_2(k2_struct_0(sK6),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),k2_struct_0(sK6),sK7)),sK7) ),
    inference(forward_demodulation,[],[f67,f107])).

fof(f67,plain,(
    ~ r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK6),k2_tops_2(u1_struct_0(sK6),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),u1_struct_0(sK6),sK7)),sK7) ),
    inference(cnf_transformation,[],[f50])).

fof(f464,plain,
    ( k2_struct_0(sK5) = k1_relat_1(sK7)
    | sP1(k2_struct_0(sK5),k2_relat_1(sK7)) ),
    inference(subsumption_resolution,[],[f463,f373])).

fof(f373,plain,(
    sP2(k2_struct_0(sK5),sK7,k2_relat_1(sK7)) ),
    inference(resolution,[],[f330,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( sP2(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X2,X1,X0)
        & sP2(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f32,f43,f42,f41])).

fof(f42,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | sP1(X0,X1)
      | ~ sP2(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f43,plain,(
    ! [X2,X1,X0] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_xboole_0 = X2 )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP3(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f463,plain,
    ( k2_struct_0(sK5) = k1_relat_1(sK7)
    | sP1(k2_struct_0(sK5),k2_relat_1(sK7))
    | ~ sP2(k2_struct_0(sK5),sK7,k2_relat_1(sK7)) ),
    inference(subsumption_resolution,[],[f460,f331])).

fof(f460,plain,
    ( k2_struct_0(sK5) = k1_relat_1(sK7)
    | ~ v1_funct_2(sK7,k2_struct_0(sK5),k2_relat_1(sK7))
    | sP1(k2_struct_0(sK5),k2_relat_1(sK7))
    | ~ sP2(k2_struct_0(sK5),sK7,k2_relat_1(sK7)) ),
    inference(superposition,[],[f371,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X2,X1) = X0
      | ~ v1_funct_2(X1,X0,X2)
      | sP1(X0,X2)
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | sP1(X0,X2)
      | ~ sP2(X0,X1,X2) ) ),
    inference(rectify,[],[f54])).

fof(f54,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | sP1(X0,X1)
      | ~ sP2(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f371,plain,(
    k1_relat_1(sK7) = k1_relset_1(k2_struct_0(sK5),k2_relat_1(sK7),sK7) ),
    inference(resolution,[],[f330,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f333,plain,(
    ~ v1_xboole_0(k2_relat_1(sK7)) ),
    inference(backward_demodulation,[],[f131,f273])).

fof(f131,plain,(
    ~ v1_xboole_0(k2_struct_0(sK6)) ),
    inference(subsumption_resolution,[],[f130,f61])).

fof(f130,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK6))
    | ~ l1_struct_0(sK6) ),
    inference(superposition,[],[f108,f69])).

fof(f108,plain,(
    ~ v1_xboole_0(u1_struct_0(sK6)) ),
    inference(subsumption_resolution,[],[f106,f60])).

fof(f60,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f50])).

fof(f106,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK6))
    | v2_struct_0(sK6) ),
    inference(resolution,[],[f61,f71])).

fof(f71,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:02:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.49  % (8433)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.49  % (8437)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.50  % (8428)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.50  % (8446)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.50  % (8425)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.50  % (8433)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f535,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(subsumption_resolution,[],[f520,f68])).
% 0.21/0.50  fof(f68,plain,(
% 0.21/0.50    v1_xboole_0(k1_xboole_0)),
% 0.21/0.50    inference(cnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    v1_xboole_0(k1_xboole_0)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.50  fof(f520,plain,(
% 0.21/0.50    ~v1_xboole_0(k1_xboole_0)),
% 0.21/0.50    inference(backward_demodulation,[],[f333,f513])).
% 0.21/0.50  fof(f513,plain,(
% 0.21/0.50    k1_xboole_0 = k2_relat_1(sK7)),
% 0.21/0.50    inference(resolution,[],[f512,f86])).
% 0.21/0.50  fof(f86,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k1_xboole_0 = X1 | ~sP1(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f56])).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP1(X0,X1))),
% 0.21/0.50    inference(nnf_transformation,[],[f41])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP1(X0,X1))),
% 0.21/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.50  fof(f512,plain,(
% 0.21/0.50    sP1(k2_struct_0(sK5),k2_relat_1(sK7))),
% 0.21/0.50    inference(subsumption_resolution,[],[f464,f511])).
% 0.21/0.50  fof(f511,plain,(
% 0.21/0.50    k2_struct_0(sK5) != k1_relat_1(sK7)),
% 0.21/0.50    inference(forward_demodulation,[],[f510,f223])).
% 0.21/0.50  fof(f223,plain,(
% 0.21/0.50    k1_relat_1(sK7) = k2_relat_1(k2_funct_1(sK7))),
% 0.21/0.50    inference(subsumption_resolution,[],[f222,f62])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    v1_funct_1(sK7)),
% 0.21/0.50    inference(cnf_transformation,[],[f50])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    ((~r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK6),k2_tops_2(u1_struct_0(sK6),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),u1_struct_0(sK6),sK7)),sK7) & v2_funct_1(sK7) & k2_struct_0(sK6) = k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),sK7) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) & v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6)) & v1_funct_1(sK7)) & l1_struct_0(sK6) & ~v2_struct_0(sK6)) & l1_struct_0(sK5)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f18,f49,f48,f47])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK5),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK5),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK5),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK5))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    ? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK5),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK5),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK5),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK6),k2_tops_2(u1_struct_0(sK6),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),u1_struct_0(sK6),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),X2) = k2_struct_0(sK6) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) & v1_funct_2(X2,u1_struct_0(sK5),u1_struct_0(sK6)) & v1_funct_1(X2)) & l1_struct_0(sK6) & ~v2_struct_0(sK6))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    ? [X2] : (~r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK6),k2_tops_2(u1_struct_0(sK6),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),u1_struct_0(sK6),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),X2) = k2_struct_0(sK6) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) & v1_funct_2(X2,u1_struct_0(sK5),u1_struct_0(sK6)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK6),k2_tops_2(u1_struct_0(sK6),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),u1_struct_0(sK6),sK7)),sK7) & v2_funct_1(sK7) & k2_struct_0(sK6) = k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),sK7) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) & v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6)) & v1_funct_1(sK7))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,negated_conjecture,(
% 0.21/0.51    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 0.21/0.51    inference(negated_conjecture,[],[f15])).
% 0.21/0.51  fof(f15,conjecture,(
% 0.21/0.51    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tops_2)).
% 0.21/0.51  fof(f222,plain,(
% 0.21/0.51    k1_relat_1(sK7) = k2_relat_1(k2_funct_1(sK7)) | ~v1_funct_1(sK7)),
% 0.21/0.51    inference(subsumption_resolution,[],[f216,f66])).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    v2_funct_1(sK7)),
% 0.21/0.51    inference(cnf_transformation,[],[f50])).
% 0.21/0.51  fof(f216,plain,(
% 0.21/0.51    k1_relat_1(sK7) = k2_relat_1(k2_funct_1(sK7)) | ~v2_funct_1(sK7) | ~v1_funct_1(sK7)),
% 0.21/0.51    inference(resolution,[],[f212,f78])).
% 0.21/0.51  fof(f78,plain,(
% 0.21/0.51    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 0.21/0.51  fof(f212,plain,(
% 0.21/0.51    v1_relat_1(sK7)),
% 0.21/0.51    inference(subsumption_resolution,[],[f199,f79])).
% 0.21/0.51  fof(f79,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.51  fof(f199,plain,(
% 0.21/0.51    v1_relat_1(sK7) | ~v1_relat_1(k2_zfmisc_1(k2_struct_0(sK5),k2_struct_0(sK6)))),
% 0.21/0.51    inference(resolution,[],[f188,f70])).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.51  fof(f188,plain,(
% 0.21/0.51    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),k2_struct_0(sK6))))),
% 0.21/0.51    inference(forward_demodulation,[],[f187,f104])).
% 0.21/0.51  fof(f104,plain,(
% 0.21/0.51    u1_struct_0(sK5) = k2_struct_0(sK5)),
% 0.21/0.51    inference(resolution,[],[f59,f69])).
% 0.21/0.51  fof(f69,plain,(
% 0.21/0.51    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,axiom,(
% 0.21/0.51    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    l1_struct_0(sK5)),
% 0.21/0.51    inference(cnf_transformation,[],[f50])).
% 0.21/0.51  fof(f187,plain,(
% 0.21/0.51    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),k2_struct_0(sK6))))),
% 0.21/0.51    inference(forward_demodulation,[],[f64,f107])).
% 0.21/0.51  fof(f107,plain,(
% 0.21/0.51    u1_struct_0(sK6) = k2_struct_0(sK6)),
% 0.21/0.51    inference(resolution,[],[f61,f69])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    l1_struct_0(sK6)),
% 0.21/0.51    inference(cnf_transformation,[],[f50])).
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))),
% 0.21/0.51    inference(cnf_transformation,[],[f50])).
% 0.21/0.51  fof(f510,plain,(
% 0.21/0.51    k2_struct_0(sK5) != k2_relat_1(k2_funct_1(sK7))),
% 0.21/0.51    inference(subsumption_resolution,[],[f509,f416])).
% 0.21/0.51  fof(f416,plain,(
% 0.21/0.51    m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK7),k2_struct_0(sK5))))),
% 0.21/0.51    inference(resolution,[],[f408,f92])).
% 0.21/0.51  fof(f92,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~sP4(X0,X1,X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f57])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | ~sP4(X0,X1,X2))),
% 0.21/0.51    inference(nnf_transformation,[],[f45])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | ~sP4(X0,X1,X2))),
% 0.21/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 0.21/0.51  fof(f408,plain,(
% 0.21/0.51    sP4(k2_struct_0(sK5),k2_relat_1(sK7),sK7)),
% 0.21/0.51    inference(subsumption_resolution,[],[f407,f62])).
% 0.21/0.51  fof(f407,plain,(
% 0.21/0.51    sP4(k2_struct_0(sK5),k2_relat_1(sK7),sK7) | ~v1_funct_1(sK7)),
% 0.21/0.51    inference(subsumption_resolution,[],[f406,f331])).
% 0.21/0.51  % (8431)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.51  fof(f331,plain,(
% 0.21/0.51    v1_funct_2(sK7,k2_struct_0(sK5),k2_relat_1(sK7))),
% 0.21/0.51    inference(backward_demodulation,[],[f169,f273])).
% 0.21/0.51  fof(f273,plain,(
% 0.21/0.51    k2_struct_0(sK6) = k2_relat_1(sK7)),
% 0.21/0.51    inference(subsumption_resolution,[],[f267,f188])).
% 0.21/0.51  fof(f267,plain,(
% 0.21/0.51    k2_struct_0(sK6) = k2_relat_1(sK7) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),k2_struct_0(sK6))))),
% 0.21/0.51    inference(superposition,[],[f232,f81])).
% 0.21/0.51  fof(f81,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.51  fof(f232,plain,(
% 0.21/0.51    k2_struct_0(sK6) = k2_relset_1(k2_struct_0(sK5),k2_struct_0(sK6),sK7)),
% 0.21/0.51    inference(forward_demodulation,[],[f231,f104])).
% 0.21/0.51  fof(f231,plain,(
% 0.21/0.51    k2_struct_0(sK6) = k2_relset_1(u1_struct_0(sK5),k2_struct_0(sK6),sK7)),
% 0.21/0.51    inference(forward_demodulation,[],[f65,f107])).
% 0.21/0.51  fof(f65,plain,(
% 0.21/0.51    k2_struct_0(sK6) = k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),sK7)),
% 0.21/0.51    inference(cnf_transformation,[],[f50])).
% 0.21/0.51  fof(f169,plain,(
% 0.21/0.51    v1_funct_2(sK7,k2_struct_0(sK5),k2_struct_0(sK6))),
% 0.21/0.51    inference(backward_demodulation,[],[f151,f107])).
% 0.21/0.51  fof(f151,plain,(
% 0.21/0.51    v1_funct_2(sK7,k2_struct_0(sK5),u1_struct_0(sK6))),
% 0.21/0.51    inference(backward_demodulation,[],[f63,f104])).
% 0.21/0.51  fof(f63,plain,(
% 0.21/0.51    v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6))),
% 0.21/0.51    inference(cnf_transformation,[],[f50])).
% 0.21/0.51  fof(f406,plain,(
% 0.21/0.51    sP4(k2_struct_0(sK5),k2_relat_1(sK7),sK7) | ~v1_funct_2(sK7,k2_struct_0(sK5),k2_relat_1(sK7)) | ~v1_funct_1(sK7)),
% 0.21/0.51    inference(subsumption_resolution,[],[f405,f330])).
% 0.21/0.51  fof(f330,plain,(
% 0.21/0.51    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),k2_relat_1(sK7))))),
% 0.21/0.51    inference(backward_demodulation,[],[f188,f273])).
% 0.21/0.51  fof(f405,plain,(
% 0.21/0.51    sP4(k2_struct_0(sK5),k2_relat_1(sK7),sK7) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),k2_relat_1(sK7)))) | ~v1_funct_2(sK7,k2_struct_0(sK5),k2_relat_1(sK7)) | ~v1_funct_1(sK7)),
% 0.21/0.51    inference(subsumption_resolution,[],[f399,f66])).
% 0.21/0.51  fof(f399,plain,(
% 0.21/0.51    sP4(k2_struct_0(sK5),k2_relat_1(sK7),sK7) | ~v2_funct_1(sK7) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),k2_relat_1(sK7)))) | ~v1_funct_2(sK7,k2_struct_0(sK5),k2_relat_1(sK7)) | ~v1_funct_1(sK7)),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f398])).
% 0.21/0.51  fof(f398,plain,(
% 0.21/0.51    k2_relat_1(sK7) != k2_relat_1(sK7) | sP4(k2_struct_0(sK5),k2_relat_1(sK7),sK7) | ~v2_funct_1(sK7) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),k2_relat_1(sK7)))) | ~v1_funct_2(sK7,k2_struct_0(sK5),k2_relat_1(sK7)) | ~v1_funct_1(sK7)),
% 0.21/0.51    inference(superposition,[],[f93,f329])).
% 0.21/0.51  fof(f329,plain,(
% 0.21/0.51    k2_relat_1(sK7) = k2_relset_1(k2_struct_0(sK5),k2_relat_1(sK7),sK7)),
% 0.21/0.51    inference(backward_demodulation,[],[f232,f273])).
% 0.21/0.51  fof(f93,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (sP4(X0,X1,X2) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f46])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (sP4(X0,X1,X2) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.51    inference(definition_folding,[],[f34,f45])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.51    inference(flattening,[],[f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.21/0.51    inference(ennf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 0.21/0.51  fof(f509,plain,(
% 0.21/0.51    k2_struct_0(sK5) != k2_relat_1(k2_funct_1(sK7)) | ~m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK7),k2_struct_0(sK5))))),
% 0.21/0.51    inference(superposition,[],[f502,f81])).
% 0.21/0.51  fof(f502,plain,(
% 0.21/0.51    k2_struct_0(sK5) != k2_relset_1(k2_relat_1(sK7),k2_struct_0(sK5),k2_funct_1(sK7))),
% 0.21/0.51    inference(subsumption_resolution,[],[f501,f392])).
% 0.21/0.51  fof(f392,plain,(
% 0.21/0.51    r2_funct_2(k2_struct_0(sK5),k2_relat_1(sK7),sK7,sK7)),
% 0.21/0.51    inference(subsumption_resolution,[],[f391,f62])).
% 0.21/0.51  fof(f391,plain,(
% 0.21/0.51    r2_funct_2(k2_struct_0(sK5),k2_relat_1(sK7),sK7,sK7) | ~v1_funct_1(sK7)),
% 0.21/0.51    inference(subsumption_resolution,[],[f379,f331])).
% 0.21/0.51  fof(f379,plain,(
% 0.21/0.51    r2_funct_2(k2_struct_0(sK5),k2_relat_1(sK7),sK7,sK7) | ~v1_funct_2(sK7,k2_struct_0(sK5),k2_relat_1(sK7)) | ~v1_funct_1(sK7)),
% 0.21/0.51    inference(resolution,[],[f330,f102])).
% 0.21/0.51  fof(f102,plain,(
% 0.21/0.51    ( ! [X0,X3,X1] : (r2_funct_2(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f101])).
% 0.21/0.51  fof(f101,plain,(
% 0.21/0.51    ( ! [X0,X3,X1] : (r2_funct_2(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.21/0.51    inference(equality_resolution,[],[f96])).
% 0.21/0.51  fof(f96,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f58])).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.51    inference(nnf_transformation,[],[f38])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.51    inference(flattening,[],[f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.21/0.51    inference(ennf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).
% 0.21/0.51  % (8442)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.51  fof(f501,plain,(
% 0.21/0.51    ~r2_funct_2(k2_struct_0(sK5),k2_relat_1(sK7),sK7,sK7) | k2_struct_0(sK5) != k2_relset_1(k2_relat_1(sK7),k2_struct_0(sK5),k2_funct_1(sK7))),
% 0.21/0.51    inference(forward_demodulation,[],[f500,f213])).
% 0.21/0.51  fof(f213,plain,(
% 0.21/0.51    sK7 = k2_funct_1(k2_funct_1(sK7))),
% 0.21/0.51    inference(resolution,[],[f212,f128])).
% 0.21/0.51  fof(f128,plain,(
% 0.21/0.51    ~v1_relat_1(sK7) | sK7 = k2_funct_1(k2_funct_1(sK7))),
% 0.21/0.51    inference(subsumption_resolution,[],[f122,f62])).
% 0.21/0.51  fof(f122,plain,(
% 0.21/0.51    sK7 = k2_funct_1(k2_funct_1(sK7)) | ~v1_funct_1(sK7) | ~v1_relat_1(sK7)),
% 0.21/0.51    inference(resolution,[],[f66,f76])).
% 0.21/0.51  fof(f76,plain,(
% 0.21/0.51    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).
% 0.21/0.51  fof(f500,plain,(
% 0.21/0.51    ~r2_funct_2(k2_struct_0(sK5),k2_relat_1(sK7),k2_funct_1(k2_funct_1(sK7)),sK7) | k2_struct_0(sK5) != k2_relset_1(k2_relat_1(sK7),k2_struct_0(sK5),k2_funct_1(sK7))),
% 0.21/0.51    inference(subsumption_resolution,[],[f499,f229])).
% 0.21/0.51  fof(f229,plain,(
% 0.21/0.51    v1_funct_1(k2_funct_1(sK7))),
% 0.21/0.51    inference(resolution,[],[f214,f73])).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~sP0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f51])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~sP0(X0))),
% 0.21/0.51    inference(nnf_transformation,[],[f39])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~sP0(X0))),
% 0.21/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.51  fof(f214,plain,(
% 0.21/0.51    sP0(sK7)),
% 0.21/0.51    inference(resolution,[],[f212,f129])).
% 0.21/0.51  fof(f129,plain,(
% 0.21/0.51    ~v1_relat_1(sK7) | sP0(sK7)),
% 0.21/0.51    inference(subsumption_resolution,[],[f123,f62])).
% 0.21/0.51  fof(f123,plain,(
% 0.21/0.51    sP0(sK7) | ~v1_funct_1(sK7) | ~v1_relat_1(sK7)),
% 0.21/0.51    inference(resolution,[],[f66,f75])).
% 0.21/0.51  fof(f75,plain,(
% 0.21/0.51    ( ! [X0] : (sP0(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f40])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ! [X0] : (sP0(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(definition_folding,[],[f24,f39])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).
% 0.21/0.51  fof(f499,plain,(
% 0.21/0.51    ~r2_funct_2(k2_struct_0(sK5),k2_relat_1(sK7),k2_funct_1(k2_funct_1(sK7)),sK7) | k2_struct_0(sK5) != k2_relset_1(k2_relat_1(sK7),k2_struct_0(sK5),k2_funct_1(sK7)) | ~v1_funct_1(k2_funct_1(sK7))),
% 0.21/0.51    inference(subsumption_resolution,[],[f498,f415])).
% 0.21/0.51  fof(f415,plain,(
% 0.21/0.51    v1_funct_2(k2_funct_1(sK7),k2_relat_1(sK7),k2_struct_0(sK5))),
% 0.21/0.51    inference(resolution,[],[f408,f91])).
% 0.21/0.51  fof(f91,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (v1_funct_2(k2_funct_1(X2),X1,X0) | ~sP4(X0,X1,X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f57])).
% 0.21/0.51  fof(f498,plain,(
% 0.21/0.51    ~r2_funct_2(k2_struct_0(sK5),k2_relat_1(sK7),k2_funct_1(k2_funct_1(sK7)),sK7) | k2_struct_0(sK5) != k2_relset_1(k2_relat_1(sK7),k2_struct_0(sK5),k2_funct_1(sK7)) | ~v1_funct_2(k2_funct_1(sK7),k2_relat_1(sK7),k2_struct_0(sK5)) | ~v1_funct_1(k2_funct_1(sK7))),
% 0.21/0.51    inference(subsumption_resolution,[],[f497,f416])).
% 0.21/0.51  fof(f497,plain,(
% 0.21/0.51    ~r2_funct_2(k2_struct_0(sK5),k2_relat_1(sK7),k2_funct_1(k2_funct_1(sK7)),sK7) | k2_struct_0(sK5) != k2_relset_1(k2_relat_1(sK7),k2_struct_0(sK5),k2_funct_1(sK7)) | ~m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK7),k2_struct_0(sK5)))) | ~v1_funct_2(k2_funct_1(sK7),k2_relat_1(sK7),k2_struct_0(sK5)) | ~v1_funct_1(k2_funct_1(sK7))),
% 0.21/0.51    inference(subsumption_resolution,[],[f496,f230])).
% 0.21/0.51  fof(f230,plain,(
% 0.21/0.51    v2_funct_1(k2_funct_1(sK7))),
% 0.21/0.51    inference(resolution,[],[f214,f74])).
% 0.21/0.51  fof(f74,plain,(
% 0.21/0.51    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~sP0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f51])).
% 0.21/0.51  fof(f496,plain,(
% 0.21/0.51    ~r2_funct_2(k2_struct_0(sK5),k2_relat_1(sK7),k2_funct_1(k2_funct_1(sK7)),sK7) | ~v2_funct_1(k2_funct_1(sK7)) | k2_struct_0(sK5) != k2_relset_1(k2_relat_1(sK7),k2_struct_0(sK5),k2_funct_1(sK7)) | ~m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK7),k2_struct_0(sK5)))) | ~v1_funct_2(k2_funct_1(sK7),k2_relat_1(sK7),k2_struct_0(sK5)) | ~v1_funct_1(k2_funct_1(sK7))),
% 0.21/0.51    inference(superposition,[],[f467,f94])).
% 0.21/0.51  fof(f94,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f36])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.51    inference(flattening,[],[f35])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.21/0.51    inference(ennf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).
% 0.21/0.51  fof(f467,plain,(
% 0.21/0.51    ~r2_funct_2(k2_struct_0(sK5),k2_relat_1(sK7),k2_tops_2(k2_relat_1(sK7),k2_struct_0(sK5),k2_funct_1(sK7)),sK7)),
% 0.21/0.51    inference(backward_demodulation,[],[f413,f404])).
% 0.21/0.51  fof(f404,plain,(
% 0.21/0.51    k2_funct_1(sK7) = k2_tops_2(k2_struct_0(sK5),k2_relat_1(sK7),sK7)),
% 0.21/0.51    inference(subsumption_resolution,[],[f403,f62])).
% 0.21/0.51  fof(f403,plain,(
% 0.21/0.51    k2_funct_1(sK7) = k2_tops_2(k2_struct_0(sK5),k2_relat_1(sK7),sK7) | ~v1_funct_1(sK7)),
% 0.21/0.51    inference(subsumption_resolution,[],[f402,f331])).
% 0.21/0.51  fof(f402,plain,(
% 0.21/0.51    k2_funct_1(sK7) = k2_tops_2(k2_struct_0(sK5),k2_relat_1(sK7),sK7) | ~v1_funct_2(sK7,k2_struct_0(sK5),k2_relat_1(sK7)) | ~v1_funct_1(sK7)),
% 0.21/0.51    inference(subsumption_resolution,[],[f401,f330])).
% 0.21/0.51  fof(f401,plain,(
% 0.21/0.51    k2_funct_1(sK7) = k2_tops_2(k2_struct_0(sK5),k2_relat_1(sK7),sK7) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),k2_relat_1(sK7)))) | ~v1_funct_2(sK7,k2_struct_0(sK5),k2_relat_1(sK7)) | ~v1_funct_1(sK7)),
% 0.21/0.51    inference(subsumption_resolution,[],[f400,f66])).
% 0.21/0.51  fof(f400,plain,(
% 0.21/0.51    k2_funct_1(sK7) = k2_tops_2(k2_struct_0(sK5),k2_relat_1(sK7),sK7) | ~v2_funct_1(sK7) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),k2_relat_1(sK7)))) | ~v1_funct_2(sK7,k2_struct_0(sK5),k2_relat_1(sK7)) | ~v1_funct_1(sK7)),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f397])).
% 0.21/0.51  fof(f397,plain,(
% 0.21/0.51    k2_relat_1(sK7) != k2_relat_1(sK7) | k2_funct_1(sK7) = k2_tops_2(k2_struct_0(sK5),k2_relat_1(sK7),sK7) | ~v2_funct_1(sK7) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),k2_relat_1(sK7)))) | ~v1_funct_2(sK7,k2_struct_0(sK5),k2_relat_1(sK7)) | ~v1_funct_1(sK7)),
% 0.21/0.51    inference(superposition,[],[f94,f329])).
% 0.21/0.51  fof(f413,plain,(
% 0.21/0.51    ~r2_funct_2(k2_struct_0(sK5),k2_relat_1(sK7),k2_tops_2(k2_relat_1(sK7),k2_struct_0(sK5),k2_tops_2(k2_struct_0(sK5),k2_relat_1(sK7),sK7)),sK7)),
% 0.21/0.51    inference(forward_demodulation,[],[f324,f273])).
% 0.21/0.51  fof(f324,plain,(
% 0.21/0.51    ~r2_funct_2(k2_struct_0(sK5),k2_struct_0(sK6),k2_tops_2(k2_struct_0(sK6),k2_struct_0(sK5),k2_tops_2(k2_struct_0(sK5),k2_struct_0(sK6),sK7)),sK7)),
% 0.21/0.51    inference(forward_demodulation,[],[f323,f104])).
% 0.21/0.51  fof(f323,plain,(
% 0.21/0.51    ~r2_funct_2(u1_struct_0(sK5),k2_struct_0(sK6),k2_tops_2(k2_struct_0(sK6),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),k2_struct_0(sK6),sK7)),sK7)),
% 0.21/0.51    inference(forward_demodulation,[],[f67,f107])).
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    ~r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK6),k2_tops_2(u1_struct_0(sK6),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),u1_struct_0(sK6),sK7)),sK7)),
% 0.21/0.51    inference(cnf_transformation,[],[f50])).
% 0.21/0.51  fof(f464,plain,(
% 0.21/0.51    k2_struct_0(sK5) = k1_relat_1(sK7) | sP1(k2_struct_0(sK5),k2_relat_1(sK7))),
% 0.21/0.51    inference(subsumption_resolution,[],[f463,f373])).
% 0.21/0.51  fof(f373,plain,(
% 0.21/0.51    sP2(k2_struct_0(sK5),sK7,k2_relat_1(sK7))),
% 0.21/0.51    inference(resolution,[],[f330,f88])).
% 0.21/0.51  fof(f88,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (sP2(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f44])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((sP3(X2,X1,X0) & sP2(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(definition_folding,[],[f32,f43,f42,f41])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | sP1(X0,X1) | ~sP2(X0,X2,X1))),
% 0.21/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    ! [X2,X1,X0] : ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~sP3(X2,X1,X0))),
% 0.21/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(flattening,[],[f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.51  fof(f463,plain,(
% 0.21/0.51    k2_struct_0(sK5) = k1_relat_1(sK7) | sP1(k2_struct_0(sK5),k2_relat_1(sK7)) | ~sP2(k2_struct_0(sK5),sK7,k2_relat_1(sK7))),
% 0.21/0.51    inference(subsumption_resolution,[],[f460,f331])).
% 0.21/0.51  fof(f460,plain,(
% 0.21/0.51    k2_struct_0(sK5) = k1_relat_1(sK7) | ~v1_funct_2(sK7,k2_struct_0(sK5),k2_relat_1(sK7)) | sP1(k2_struct_0(sK5),k2_relat_1(sK7)) | ~sP2(k2_struct_0(sK5),sK7,k2_relat_1(sK7))),
% 0.21/0.51    inference(superposition,[],[f371,f84])).
% 0.21/0.51  fof(f84,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2) | sP1(X0,X2) | ~sP2(X0,X1,X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f55])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | sP1(X0,X2) | ~sP2(X0,X1,X2))),
% 0.21/0.51    inference(rectify,[],[f54])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | sP1(X0,X1) | ~sP2(X0,X2,X1))),
% 0.21/0.51    inference(nnf_transformation,[],[f42])).
% 0.21/0.51  fof(f371,plain,(
% 0.21/0.51    k1_relat_1(sK7) = k1_relset_1(k2_struct_0(sK5),k2_relat_1(sK7),sK7)),
% 0.21/0.51    inference(resolution,[],[f330,f80])).
% 0.21/0.51  fof(f80,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.51  fof(f333,plain,(
% 0.21/0.51    ~v1_xboole_0(k2_relat_1(sK7))),
% 0.21/0.51    inference(backward_demodulation,[],[f131,f273])).
% 0.21/0.51  fof(f131,plain,(
% 0.21/0.51    ~v1_xboole_0(k2_struct_0(sK6))),
% 0.21/0.51    inference(subsumption_resolution,[],[f130,f61])).
% 0.21/0.51  fof(f130,plain,(
% 0.21/0.51    ~v1_xboole_0(k2_struct_0(sK6)) | ~l1_struct_0(sK6)),
% 0.21/0.51    inference(superposition,[],[f108,f69])).
% 0.21/0.51  fof(f108,plain,(
% 0.21/0.51    ~v1_xboole_0(u1_struct_0(sK6))),
% 0.21/0.51    inference(subsumption_resolution,[],[f106,f60])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    ~v2_struct_0(sK6)),
% 0.21/0.51    inference(cnf_transformation,[],[f50])).
% 0.21/0.51  fof(f106,plain,(
% 0.21/0.51    ~v1_xboole_0(u1_struct_0(sK6)) | v2_struct_0(sK6)),
% 0.21/0.51    inference(resolution,[],[f61,f71])).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,axiom,(
% 0.21/0.51    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (8433)------------------------------
% 0.21/0.51  % (8433)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (8433)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (8433)Memory used [KB]: 1791
% 0.21/0.51  % (8433)Time elapsed: 0.077 s
% 0.21/0.51  % (8433)------------------------------
% 0.21/0.51  % (8433)------------------------------
% 0.21/0.51  % (8436)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.51  % (8424)Success in time 0.156 s
%------------------------------------------------------------------------------
