%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:32 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  125 (1815 expanded)
%              Number of leaves         :   16 ( 552 expanded)
%              Depth                    :   45
%              Number of atoms          :  431 (9481 expanded)
%              Number of equality atoms :   39 (1708 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f207,plain,(
    $false ),
    inference(subsumption_resolution,[],[f206,f73])).

fof(f73,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f206,plain,(
    ~ r1_tarski(sK2,sK2) ),
    inference(forward_demodulation,[],[f205,f92])).

fof(f92,plain,(
    sK2 = k1_relat_1(sK4) ),
    inference(forward_demodulation,[],[f91,f83])).

fof(f83,plain,(
    sK4 = sK7(sK3,sK2,sK4) ),
    inference(resolution,[],[f81,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | sK7(X0,X1,X2) = X2 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( ~ r1_tarski(k2_relat_1(X3),X0)
            | k1_relat_1(X3) != X1
            | X2 != X3
            | ~ v1_funct_1(X3)
            | ~ v1_relat_1(X3) ) )
      & ( ( r1_tarski(k2_relat_1(sK7(X0,X1,X2)),X0)
          & k1_relat_1(sK7(X0,X1,X2)) = X1
          & sK7(X0,X1,X2) = X2
          & v1_funct_1(sK7(X0,X1,X2))
          & v1_relat_1(sK7(X0,X1,X2)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f40,f41])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r1_tarski(k2_relat_1(X4),X0)
          & k1_relat_1(X4) = X1
          & X2 = X4
          & v1_funct_1(X4)
          & v1_relat_1(X4) )
     => ( r1_tarski(k2_relat_1(sK7(X0,X1,X2)),X0)
        & k1_relat_1(sK7(X0,X1,X2)) = X1
        & sK7(X0,X1,X2) = X2
        & v1_funct_1(sK7(X0,X1,X2))
        & v1_relat_1(sK7(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( ~ r1_tarski(k2_relat_1(X3),X0)
            | k1_relat_1(X3) != X1
            | X2 != X3
            | ~ v1_funct_1(X3)
            | ~ v1_relat_1(X3) ) )
      & ( ? [X4] :
            ( r1_tarski(k2_relat_1(X4),X0)
            & k1_relat_1(X4) = X1
            & X2 = X4
            & v1_funct_1(X4)
            & v1_relat_1(X4) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X1,X0,X3] :
      ( ( sP0(X1,X0,X3)
        | ! [X4] :
            ( ~ r1_tarski(k2_relat_1(X4),X1)
            | k1_relat_1(X4) != X0
            | X3 != X4
            | ~ v1_funct_1(X4)
            | ~ v1_relat_1(X4) ) )
      & ( ? [X4] :
            ( r1_tarski(k2_relat_1(X4),X1)
            & k1_relat_1(X4) = X0
            & X3 = X4
            & v1_funct_1(X4)
            & v1_relat_1(X4) )
        | ~ sP0(X1,X0,X3) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X1,X0,X3] :
      ( sP0(X1,X0,X3)
    <=> ? [X4] :
          ( r1_tarski(k2_relat_1(X4),X1)
          & k1_relat_1(X4) = X0
          & X3 = X4
          & v1_funct_1(X4)
          & v1_relat_1(X4) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f81,plain,(
    sP0(sK3,sK2,sK4) ),
    inference(resolution,[],[f80,f44])).

fof(f44,plain,(
    r2_hidden(sK4,k1_funct_2(sK2,sK3)) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      | ~ v1_funct_2(sK4,sK2,sK3)
      | ~ v1_funct_1(sK4) )
    & r2_hidden(sK4,k1_funct_2(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f12,f27])).

fof(f27,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2) )
        & r2_hidden(X2,k1_funct_2(X0,X1)) )
   => ( ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
        | ~ v1_funct_2(sK4,sK2,sK3)
        | ~ v1_funct_1(sK4) )
      & r2_hidden(sK4,k1_funct_2(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2) )
      & r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X2,k1_funct_2(X0,X1))
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
     => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_2)).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_funct_2(X1,X2))
      | sP0(X2,X1,X0) ) ),
    inference(resolution,[],[f61,f77])).

fof(f77,plain,(
    ! [X0,X1] : sP1(X0,X1,k1_funct_2(X0,X1)) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( k1_funct_2(X0,X1) = X2
        | ~ sP1(X0,X1,X2) )
      & ( sP1(X0,X1,X2)
        | k1_funct_2(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_2(X0,X1) = X2
    <=> sP1(X0,X1,X2) ) ),
    inference(definition_folding,[],[f7,f25,f24])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP0(X1,X0,X3) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k1_funct_2(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r1_tarski(k2_relat_1(X4),X1)
              & k1_relat_1(X4) = X0
              & X3 = X4
              & v1_funct_1(X4)
              & v1_relat_1(X4) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_funct_2)).

fof(f61,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | sP0(X1,X0,X4) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ( ~ sP0(X1,X0,sK6(X0,X1,X2))
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( sP0(X1,X0,sK6(X0,X1,X2))
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X1,X0,X4) )
            & ( sP0(X1,X0,X4)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f36,f37])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ sP0(X1,X0,X3)
            | ~ r2_hidden(X3,X2) )
          & ( sP0(X1,X0,X3)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ sP0(X1,X0,sK6(X0,X1,X2))
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( sP0(X1,X0,sK6(X0,X1,X2))
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP0(X1,X0,X3)
              | ~ r2_hidden(X3,X2) )
            & ( sP0(X1,X0,X3)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X1,X0,X4) )
            & ( sP0(X1,X0,X4)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP0(X1,X0,X3)
              | ~ r2_hidden(X3,X2) )
            & ( sP0(X1,X0,X3)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ sP0(X1,X0,X3) )
            & ( sP0(X1,X0,X3)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f91,plain,(
    sK2 = k1_relat_1(sK7(sK3,sK2,sK4)) ),
    inference(resolution,[],[f68,f81])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | k1_relat_1(sK7(X0,X1,X2)) = X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f205,plain,(
    ~ r1_tarski(k1_relat_1(sK4),sK2) ),
    inference(subsumption_resolution,[],[f204,f88])).

fof(f88,plain,(
    v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f85,f81])).

fof(f85,plain,
    ( v1_relat_1(sK4)
    | ~ sP0(sK3,sK2,sK4) ),
    inference(superposition,[],[f65,f83])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(sK7(X0,X1,X2))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f204,plain,
    ( ~ r1_tarski(k1_relat_1(sK4),sK2)
    | ~ v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f203,f97])).

fof(f97,plain,(
    r1_tarski(k2_relat_1(sK4),sK3) ),
    inference(forward_demodulation,[],[f96,f83])).

fof(f96,plain,(
    r1_tarski(k2_relat_1(sK7(sK3,sK2,sK4)),sK3) ),
    inference(resolution,[],[f69,f81])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | r1_tarski(k2_relat_1(sK7(X0,X1,X2)),X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f203,plain,
    ( ~ r1_tarski(k2_relat_1(sK4),sK3)
    | ~ r1_tarski(k1_relat_1(sK4),sK2)
    | ~ v1_relat_1(sK4) ),
    inference(resolution,[],[f201,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

fof(f201,plain,(
    ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(subsumption_resolution,[],[f87,f199])).

fof(f199,plain,(
    v1_funct_2(sK4,sK2,sK3) ),
    inference(resolution,[],[f189,f97])).

fof(f189,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK4),X0)
      | v1_funct_2(sK4,sK2,X0) ) ),
    inference(subsumption_resolution,[],[f188,f73])).

fof(f188,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK2,sK2)
      | v1_funct_2(sK4,sK2,X0)
      | ~ r1_tarski(k2_relat_1(sK4),X0) ) ),
    inference(forward_demodulation,[],[f187,f92])).

fof(f187,plain,(
    ! [X0] :
      ( v1_funct_2(sK4,sK2,X0)
      | ~ r1_tarski(k2_relat_1(sK4),X0)
      | ~ r1_tarski(k1_relat_1(sK4),sK2) ) ),
    inference(subsumption_resolution,[],[f186,f88])).

fof(f186,plain,(
    ! [X0] :
      ( v1_funct_2(sK4,sK2,X0)
      | ~ r1_tarski(k2_relat_1(sK4),X0)
      | ~ r1_tarski(k1_relat_1(sK4),sK2)
      | ~ v1_relat_1(sK4) ) ),
    inference(resolution,[],[f181,f58])).

fof(f181,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
      | v1_funct_2(sK4,sK2,X0) ) ),
    inference(subsumption_resolution,[],[f180,f86])).

fof(f86,plain,(
    v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f84,f81])).

fof(f84,plain,
    ( v1_funct_1(sK4)
    | ~ sP0(sK3,sK2,sK4) ),
    inference(superposition,[],[f66,f83])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(sK7(X0,X1,X2))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f180,plain,(
    ! [X0] :
      ( v1_funct_2(sK4,sK2,X0)
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) ) ),
    inference(resolution,[],[f178,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_partfun1(X2,X0)
      | v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).

fof(f178,plain,(
    v1_partfun1(sK4,sK2) ),
    inference(resolution,[],[f168,f104])).

fof(f104,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(sK4)))) ),
    inference(subsumption_resolution,[],[f103,f88])).

fof(f103,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(sK4))))
    | ~ v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f102,f86])).

fof(f102,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(sK4))))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(superposition,[],[f48,f92])).

fof(f48,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(f168,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
      | v1_partfun1(X0,sK2) ) ),
    inference(resolution,[],[f167,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_partfun1)).

fof(f167,plain,(
    v1_xboole_0(sK2) ),
    inference(subsumption_resolution,[],[f166,f73])).

fof(f166,plain,
    ( ~ r1_tarski(sK2,sK2)
    | v1_xboole_0(sK2) ),
    inference(forward_demodulation,[],[f165,f92])).

fof(f165,plain,
    ( v1_xboole_0(sK2)
    | ~ r1_tarski(k1_relat_1(sK4),sK2) ),
    inference(subsumption_resolution,[],[f164,f88])).

fof(f164,plain,
    ( v1_xboole_0(sK2)
    | ~ r1_tarski(k1_relat_1(sK4),sK2)
    | ~ v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f163,f97])).

fof(f163,plain,
    ( v1_xboole_0(sK2)
    | ~ r1_tarski(k2_relat_1(sK4),sK3)
    | ~ r1_tarski(k1_relat_1(sK4),sK2)
    | ~ v1_relat_1(sK4) ),
    inference(resolution,[],[f161,f58])).

fof(f161,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | v1_xboole_0(sK2) ),
    inference(resolution,[],[f159,f87])).

fof(f159,plain,
    ( v1_funct_2(sK4,sK2,sK3)
    | v1_xboole_0(sK2) ),
    inference(resolution,[],[f158,f97])).

fof(f158,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK4),X0)
      | v1_xboole_0(sK2)
      | v1_funct_2(sK4,sK2,X0) ) ),
    inference(subsumption_resolution,[],[f157,f73])).

fof(f157,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK2,sK2)
      | v1_funct_2(sK4,sK2,X0)
      | v1_xboole_0(sK2)
      | ~ r1_tarski(k2_relat_1(sK4),X0) ) ),
    inference(forward_demodulation,[],[f156,f92])).

fof(f156,plain,(
    ! [X0] :
      ( v1_funct_2(sK4,sK2,X0)
      | v1_xboole_0(sK2)
      | ~ r1_tarski(k2_relat_1(sK4),X0)
      | ~ r1_tarski(k1_relat_1(sK4),sK2) ) ),
    inference(subsumption_resolution,[],[f155,f88])).

fof(f155,plain,(
    ! [X0] :
      ( v1_funct_2(sK4,sK2,X0)
      | v1_xboole_0(sK2)
      | ~ r1_tarski(k2_relat_1(sK4),X0)
      | ~ r1_tarski(k1_relat_1(sK4),sK2)
      | ~ v1_relat_1(sK4) ) ),
    inference(resolution,[],[f153,f58])).

fof(f153,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
      | v1_funct_2(sK4,sK2,X0)
      | v1_xboole_0(sK2) ) ),
    inference(subsumption_resolution,[],[f152,f86])).

fof(f152,plain,(
    ! [X0] :
      ( v1_xboole_0(sK2)
      | v1_funct_2(sK4,sK2,X0)
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) ) ),
    inference(resolution,[],[f150,f60])).

fof(f150,plain,
    ( v1_partfun1(sK4,sK2)
    | v1_xboole_0(sK2) ),
    inference(resolution,[],[f149,f111])).

fof(f111,plain,(
    sP0(k2_relat_1(sK4),sK2,sK4) ),
    inference(resolution,[],[f109,f73])).

fof(f109,plain,(
    ! [X4] :
      ( ~ r1_tarski(k2_relat_1(sK4),X4)
      | sP0(X4,sK2,sK4) ) ),
    inference(forward_demodulation,[],[f108,f92])).

fof(f108,plain,(
    ! [X4] :
      ( ~ r1_tarski(k2_relat_1(sK4),X4)
      | sP0(X4,k1_relat_1(sK4),sK4) ) ),
    inference(subsumption_resolution,[],[f106,f88])).

fof(f106,plain,(
    ! [X4] :
      ( ~ r1_tarski(k2_relat_1(sK4),X4)
      | sP0(X4,k1_relat_1(sK4),sK4)
      | ~ v1_relat_1(sK4) ) ),
    inference(resolution,[],[f76,f86])).

fof(f76,plain,(
    ! [X0,X3] :
      ( ~ v1_funct_1(X3)
      | ~ r1_tarski(k2_relat_1(X3),X0)
      | sP0(X0,k1_relat_1(X3),X3)
      | ~ v1_relat_1(X3) ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X2,X0,X3] :
      ( sP0(X0,k1_relat_1(X3),X2)
      | ~ r1_tarski(k2_relat_1(X3),X0)
      | X2 != X3
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3) ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2)
      | ~ r1_tarski(k2_relat_1(X3),X0)
      | k1_relat_1(X3) != X1
      | X2 != X3
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f149,plain,(
    ! [X2,X1] :
      ( ~ sP0(k2_relat_1(sK4),X1,X2)
      | v1_partfun1(sK4,sK2)
      | v1_xboole_0(X1) ) ),
    inference(resolution,[],[f147,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k1_funct_2(X1,X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(resolution,[],[f62,f77])).

fof(f62,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ sP0(X1,X0,X4)
      | r2_hidden(X4,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f147,plain,(
    ! [X6,X5] :
      ( ~ r2_hidden(X6,k1_funct_2(X5,k2_relat_1(sK4)))
      | v1_xboole_0(X5)
      | v1_partfun1(sK4,sK2) ) ),
    inference(resolution,[],[f142,f49])).

fof(f49,plain,(
    ! [X2,X0] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK5(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f30,f31])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK5(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f142,plain,(
    ! [X2] :
      ( v1_xboole_0(k1_funct_2(X2,k2_relat_1(sK4)))
      | v1_partfun1(sK4,sK2)
      | v1_xboole_0(X2) ) ),
    inference(resolution,[],[f137,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | v1_xboole_0(k1_funct_2(X0,X1))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k1_funct_2(X0,X1))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k1_funct_2(X0,X1))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => v1_xboole_0(k1_funct_2(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_2)).

fof(f137,plain,
    ( v1_xboole_0(k2_relat_1(sK4))
    | v1_partfun1(sK4,sK2) ),
    inference(subsumption_resolution,[],[f135,f104])).

fof(f135,plain,
    ( v1_partfun1(sK4,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(sK4))))
    | v1_xboole_0(k2_relat_1(sK4)) ),
    inference(resolution,[],[f134,f95])).

fof(f95,plain,(
    v1_funct_2(sK4,sK2,k2_relat_1(sK4)) ),
    inference(subsumption_resolution,[],[f94,f88])).

fof(f94,plain,
    ( v1_funct_2(sK4,sK2,k2_relat_1(sK4))
    | ~ v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f93,f86])).

fof(f93,plain,
    ( v1_funct_2(sK4,sK2,k2_relat_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(superposition,[],[f47,f92])).

fof(f47,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f134,plain,(
    ! [X6,X5] :
      ( ~ v1_funct_2(sK4,X5,X6)
      | v1_partfun1(sK4,X5)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | v1_xboole_0(X6) ) ),
    inference(resolution,[],[f52,f86])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f87,plain,
    ( ~ v1_funct_2(sK4,sK2,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(subsumption_resolution,[],[f45,f86])).

fof(f45,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_2(sK4,sK2,sK3)
    | ~ v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_vampire %s %d
% 0.11/0.32  % Computer   : n006.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 13:26:07 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.19/0.47  % (15798)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.19/0.47  % (15807)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.19/0.47  % (15790)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.19/0.47  % (15809)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.19/0.47  % (15804)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.19/0.48  % (15797)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.19/0.48  % (15800)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.19/0.48  % (15787)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.19/0.48  % (15791)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.19/0.48  % (15788)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.19/0.48  % (15791)Refutation not found, incomplete strategy% (15791)------------------------------
% 0.19/0.48  % (15791)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.48  % (15791)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.48  
% 0.19/0.48  % (15791)Memory used [KB]: 10618
% 0.19/0.48  % (15791)Time elapsed: 0.088 s
% 0.19/0.48  % (15791)------------------------------
% 0.19/0.48  % (15791)------------------------------
% 0.19/0.48  % (15792)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.19/0.48  % (15799)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.19/0.48  % (15789)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.19/0.48  % (15788)Refutation found. Thanks to Tanya!
% 0.19/0.48  % SZS status Theorem for theBenchmark
% 0.19/0.48  % SZS output start Proof for theBenchmark
% 0.19/0.48  fof(f207,plain,(
% 0.19/0.48    $false),
% 0.19/0.48    inference(subsumption_resolution,[],[f206,f73])).
% 0.19/0.48  fof(f73,plain,(
% 0.19/0.48    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.19/0.48    inference(equality_resolution,[],[f56])).
% 0.19/0.48  fof(f56,plain,(
% 0.19/0.48    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.19/0.48    inference(cnf_transformation,[],[f34])).
% 0.19/0.48  fof(f34,plain,(
% 0.19/0.48    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.19/0.48    inference(flattening,[],[f33])).
% 0.19/0.48  fof(f33,plain,(
% 0.19/0.48    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.19/0.48    inference(nnf_transformation,[],[f2])).
% 0.19/0.48  fof(f2,axiom,(
% 0.19/0.48    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.19/0.48  fof(f206,plain,(
% 0.19/0.48    ~r1_tarski(sK2,sK2)),
% 0.19/0.48    inference(forward_demodulation,[],[f205,f92])).
% 0.19/0.48  fof(f92,plain,(
% 0.19/0.48    sK2 = k1_relat_1(sK4)),
% 0.19/0.48    inference(forward_demodulation,[],[f91,f83])).
% 0.19/0.48  fof(f83,plain,(
% 0.19/0.48    sK4 = sK7(sK3,sK2,sK4)),
% 0.19/0.48    inference(resolution,[],[f81,f67])).
% 0.19/0.48  fof(f67,plain,(
% 0.19/0.48    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | sK7(X0,X1,X2) = X2) )),
% 0.19/0.48    inference(cnf_transformation,[],[f42])).
% 0.19/0.48  fof(f42,plain,(
% 0.19/0.48    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3] : (~r1_tarski(k2_relat_1(X3),X0) | k1_relat_1(X3) != X1 | X2 != X3 | ~v1_funct_1(X3) | ~v1_relat_1(X3))) & ((r1_tarski(k2_relat_1(sK7(X0,X1,X2)),X0) & k1_relat_1(sK7(X0,X1,X2)) = X1 & sK7(X0,X1,X2) = X2 & v1_funct_1(sK7(X0,X1,X2)) & v1_relat_1(sK7(X0,X1,X2))) | ~sP0(X0,X1,X2)))),
% 0.19/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f40,f41])).
% 0.19/0.48  fof(f41,plain,(
% 0.19/0.48    ! [X2,X1,X0] : (? [X4] : (r1_tarski(k2_relat_1(X4),X0) & k1_relat_1(X4) = X1 & X2 = X4 & v1_funct_1(X4) & v1_relat_1(X4)) => (r1_tarski(k2_relat_1(sK7(X0,X1,X2)),X0) & k1_relat_1(sK7(X0,X1,X2)) = X1 & sK7(X0,X1,X2) = X2 & v1_funct_1(sK7(X0,X1,X2)) & v1_relat_1(sK7(X0,X1,X2))))),
% 0.19/0.48    introduced(choice_axiom,[])).
% 0.19/0.48  fof(f40,plain,(
% 0.19/0.48    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3] : (~r1_tarski(k2_relat_1(X3),X0) | k1_relat_1(X3) != X1 | X2 != X3 | ~v1_funct_1(X3) | ~v1_relat_1(X3))) & (? [X4] : (r1_tarski(k2_relat_1(X4),X0) & k1_relat_1(X4) = X1 & X2 = X4 & v1_funct_1(X4) & v1_relat_1(X4)) | ~sP0(X0,X1,X2)))),
% 0.19/0.48    inference(rectify,[],[f39])).
% 0.19/0.48  fof(f39,plain,(
% 0.19/0.48    ! [X1,X0,X3] : ((sP0(X1,X0,X3) | ! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4))) & (? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4)) | ~sP0(X1,X0,X3)))),
% 0.19/0.48    inference(nnf_transformation,[],[f24])).
% 0.19/0.48  fof(f24,plain,(
% 0.19/0.48    ! [X1,X0,X3] : (sP0(X1,X0,X3) <=> ? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4)))),
% 0.19/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.19/0.48  fof(f81,plain,(
% 0.19/0.48    sP0(sK3,sK2,sK4)),
% 0.19/0.48    inference(resolution,[],[f80,f44])).
% 0.19/0.48  fof(f44,plain,(
% 0.19/0.48    r2_hidden(sK4,k1_funct_2(sK2,sK3))),
% 0.19/0.48    inference(cnf_transformation,[],[f28])).
% 0.19/0.48  fof(f28,plain,(
% 0.19/0.48    (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | ~v1_funct_2(sK4,sK2,sK3) | ~v1_funct_1(sK4)) & r2_hidden(sK4,k1_funct_2(sK2,sK3))),
% 0.19/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f12,f27])).
% 0.19/0.48  fof(f27,plain,(
% 0.19/0.48    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & r2_hidden(X2,k1_funct_2(X0,X1))) => ((~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | ~v1_funct_2(sK4,sK2,sK3) | ~v1_funct_1(sK4)) & r2_hidden(sK4,k1_funct_2(sK2,sK3)))),
% 0.19/0.48    introduced(choice_axiom,[])).
% 0.19/0.48  fof(f12,plain,(
% 0.19/0.48    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & r2_hidden(X2,k1_funct_2(X0,X1)))),
% 0.19/0.48    inference(ennf_transformation,[],[f11])).
% 0.19/0.48  fof(f11,negated_conjecture,(
% 0.19/0.48    ~! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.19/0.48    inference(negated_conjecture,[],[f10])).
% 0.19/0.48  fof(f10,conjecture,(
% 0.19/0.48    ! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_2)).
% 0.19/0.48  fof(f80,plain,(
% 0.19/0.48    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_funct_2(X1,X2)) | sP0(X2,X1,X0)) )),
% 0.19/0.48    inference(resolution,[],[f61,f77])).
% 0.19/0.48  fof(f77,plain,(
% 0.19/0.48    ( ! [X0,X1] : (sP1(X0,X1,k1_funct_2(X0,X1))) )),
% 0.19/0.48    inference(equality_resolution,[],[f71])).
% 0.19/0.48  fof(f71,plain,(
% 0.19/0.48    ( ! [X2,X0,X1] : (sP1(X0,X1,X2) | k1_funct_2(X0,X1) != X2) )),
% 0.19/0.48    inference(cnf_transformation,[],[f43])).
% 0.19/0.48  fof(f43,plain,(
% 0.19/0.48    ! [X0,X1,X2] : ((k1_funct_2(X0,X1) = X2 | ~sP1(X0,X1,X2)) & (sP1(X0,X1,X2) | k1_funct_2(X0,X1) != X2))),
% 0.19/0.48    inference(nnf_transformation,[],[f26])).
% 0.19/0.48  fof(f26,plain,(
% 0.19/0.48    ! [X0,X1,X2] : (k1_funct_2(X0,X1) = X2 <=> sP1(X0,X1,X2))),
% 0.19/0.48    inference(definition_folding,[],[f7,f25,f24])).
% 0.19/0.48  fof(f25,plain,(
% 0.19/0.48    ! [X0,X1,X2] : (sP1(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> sP0(X1,X0,X3)))),
% 0.19/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.19/0.48  fof(f7,axiom,(
% 0.19/0.48    ! [X0,X1,X2] : (k1_funct_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4))))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_funct_2)).
% 0.19/0.48  fof(f61,plain,(
% 0.19/0.48    ( ! [X4,X2,X0,X1] : (~sP1(X0,X1,X2) | ~r2_hidden(X4,X2) | sP0(X1,X0,X4)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f38])).
% 0.19/0.48  fof(f38,plain,(
% 0.19/0.48    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ((~sP0(X1,X0,sK6(X0,X1,X2)) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (sP0(X1,X0,sK6(X0,X1,X2)) | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X1,X0,X4)) & (sP0(X1,X0,X4) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 0.19/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f36,f37])).
% 0.19/0.48  fof(f37,plain,(
% 0.19/0.48    ! [X2,X1,X0] : (? [X3] : ((~sP0(X1,X0,X3) | ~r2_hidden(X3,X2)) & (sP0(X1,X0,X3) | r2_hidden(X3,X2))) => ((~sP0(X1,X0,sK6(X0,X1,X2)) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (sP0(X1,X0,sK6(X0,X1,X2)) | r2_hidden(sK6(X0,X1,X2),X2))))),
% 0.19/0.48    introduced(choice_axiom,[])).
% 0.19/0.48  fof(f36,plain,(
% 0.19/0.48    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X1,X0,X3) | ~r2_hidden(X3,X2)) & (sP0(X1,X0,X3) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X1,X0,X4)) & (sP0(X1,X0,X4) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 0.19/0.48    inference(rectify,[],[f35])).
% 0.19/0.48  fof(f35,plain,(
% 0.19/0.48    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X1,X0,X3) | ~r2_hidden(X3,X2)) & (sP0(X1,X0,X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~sP0(X1,X0,X3)) & (sP0(X1,X0,X3) | ~r2_hidden(X3,X2))) | ~sP1(X0,X1,X2)))),
% 0.19/0.48    inference(nnf_transformation,[],[f25])).
% 0.19/0.48  fof(f91,plain,(
% 0.19/0.48    sK2 = k1_relat_1(sK7(sK3,sK2,sK4))),
% 0.19/0.48    inference(resolution,[],[f68,f81])).
% 0.19/0.48  fof(f68,plain,(
% 0.19/0.48    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | k1_relat_1(sK7(X0,X1,X2)) = X1) )),
% 0.19/0.48    inference(cnf_transformation,[],[f42])).
% 0.19/0.48  fof(f205,plain,(
% 0.19/0.48    ~r1_tarski(k1_relat_1(sK4),sK2)),
% 0.19/0.48    inference(subsumption_resolution,[],[f204,f88])).
% 0.19/0.48  fof(f88,plain,(
% 0.19/0.48    v1_relat_1(sK4)),
% 0.19/0.48    inference(subsumption_resolution,[],[f85,f81])).
% 0.19/0.48  fof(f85,plain,(
% 0.19/0.48    v1_relat_1(sK4) | ~sP0(sK3,sK2,sK4)),
% 0.19/0.48    inference(superposition,[],[f65,f83])).
% 0.19/0.48  fof(f65,plain,(
% 0.19/0.48    ( ! [X2,X0,X1] : (v1_relat_1(sK7(X0,X1,X2)) | ~sP0(X0,X1,X2)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f42])).
% 0.19/0.48  fof(f204,plain,(
% 0.19/0.48    ~r1_tarski(k1_relat_1(sK4),sK2) | ~v1_relat_1(sK4)),
% 0.19/0.48    inference(subsumption_resolution,[],[f203,f97])).
% 0.19/0.48  fof(f97,plain,(
% 0.19/0.48    r1_tarski(k2_relat_1(sK4),sK3)),
% 0.19/0.48    inference(forward_demodulation,[],[f96,f83])).
% 0.19/0.48  fof(f96,plain,(
% 0.19/0.48    r1_tarski(k2_relat_1(sK7(sK3,sK2,sK4)),sK3)),
% 0.19/0.48    inference(resolution,[],[f69,f81])).
% 0.19/0.48  fof(f69,plain,(
% 0.19/0.48    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | r1_tarski(k2_relat_1(sK7(X0,X1,X2)),X0)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f42])).
% 0.19/0.48  fof(f203,plain,(
% 0.19/0.48    ~r1_tarski(k2_relat_1(sK4),sK3) | ~r1_tarski(k1_relat_1(sK4),sK2) | ~v1_relat_1(sK4)),
% 0.19/0.48    inference(resolution,[],[f201,f58])).
% 0.19/0.48  fof(f58,plain,(
% 0.19/0.48    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f21])).
% 0.19/0.48  fof(f21,plain,(
% 0.19/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.19/0.48    inference(flattening,[],[f20])).
% 0.19/0.48  fof(f20,plain,(
% 0.19/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 0.19/0.48    inference(ennf_transformation,[],[f3])).
% 0.19/0.48  fof(f3,axiom,(
% 0.19/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).
% 0.19/0.48  fof(f201,plain,(
% 0.19/0.48    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 0.19/0.48    inference(subsumption_resolution,[],[f87,f199])).
% 0.19/0.48  fof(f199,plain,(
% 0.19/0.48    v1_funct_2(sK4,sK2,sK3)),
% 0.19/0.48    inference(resolution,[],[f189,f97])).
% 0.19/0.48  fof(f189,plain,(
% 0.19/0.48    ( ! [X0] : (~r1_tarski(k2_relat_1(sK4),X0) | v1_funct_2(sK4,sK2,X0)) )),
% 0.19/0.48    inference(subsumption_resolution,[],[f188,f73])).
% 0.19/0.48  fof(f188,plain,(
% 0.19/0.48    ( ! [X0] : (~r1_tarski(sK2,sK2) | v1_funct_2(sK4,sK2,X0) | ~r1_tarski(k2_relat_1(sK4),X0)) )),
% 0.19/0.48    inference(forward_demodulation,[],[f187,f92])).
% 0.19/0.48  fof(f187,plain,(
% 0.19/0.48    ( ! [X0] : (v1_funct_2(sK4,sK2,X0) | ~r1_tarski(k2_relat_1(sK4),X0) | ~r1_tarski(k1_relat_1(sK4),sK2)) )),
% 0.19/0.48    inference(subsumption_resolution,[],[f186,f88])).
% 0.19/0.48  fof(f186,plain,(
% 0.19/0.48    ( ! [X0] : (v1_funct_2(sK4,sK2,X0) | ~r1_tarski(k2_relat_1(sK4),X0) | ~r1_tarski(k1_relat_1(sK4),sK2) | ~v1_relat_1(sK4)) )),
% 0.19/0.48    inference(resolution,[],[f181,f58])).
% 0.19/0.48  fof(f181,plain,(
% 0.19/0.48    ( ! [X0] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | v1_funct_2(sK4,sK2,X0)) )),
% 0.19/0.48    inference(subsumption_resolution,[],[f180,f86])).
% 0.19/0.48  fof(f86,plain,(
% 0.19/0.48    v1_funct_1(sK4)),
% 0.19/0.48    inference(subsumption_resolution,[],[f84,f81])).
% 0.19/0.48  fof(f84,plain,(
% 0.19/0.48    v1_funct_1(sK4) | ~sP0(sK3,sK2,sK4)),
% 0.19/0.48    inference(superposition,[],[f66,f83])).
% 0.19/0.48  fof(f66,plain,(
% 0.19/0.48    ( ! [X2,X0,X1] : (v1_funct_1(sK7(X0,X1,X2)) | ~sP0(X0,X1,X2)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f42])).
% 0.19/0.48  fof(f180,plain,(
% 0.19/0.48    ( ! [X0] : (v1_funct_2(sK4,sK2,X0) | ~v1_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))) )),
% 0.19/0.48    inference(resolution,[],[f178,f60])).
% 0.19/0.48  fof(f60,plain,(
% 0.19/0.48    ( ! [X2,X0,X1] : (~v1_partfun1(X2,X0) | v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.19/0.48    inference(cnf_transformation,[],[f23])).
% 0.19/0.48  fof(f23,plain,(
% 0.19/0.48    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.48    inference(flattening,[],[f22])).
% 0.19/0.48  fof(f22,plain,(
% 0.19/0.48    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.48    inference(ennf_transformation,[],[f4])).
% 0.19/0.48  fof(f4,axiom,(
% 0.19/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).
% 0.19/0.48  fof(f178,plain,(
% 0.19/0.48    v1_partfun1(sK4,sK2)),
% 0.19/0.48    inference(resolution,[],[f168,f104])).
% 0.19/0.48  fof(f104,plain,(
% 0.19/0.48    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(sK4))))),
% 0.19/0.48    inference(subsumption_resolution,[],[f103,f88])).
% 0.19/0.48  fof(f103,plain,(
% 0.19/0.48    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(sK4)))) | ~v1_relat_1(sK4)),
% 0.19/0.48    inference(subsumption_resolution,[],[f102,f86])).
% 0.19/0.48  fof(f102,plain,(
% 0.19/0.48    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(sK4)))) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4)),
% 0.19/0.48    inference(superposition,[],[f48,f92])).
% 0.19/0.48  fof(f48,plain,(
% 0.19/0.48    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f14])).
% 0.19/0.48  fof(f14,plain,(
% 0.19/0.48    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.19/0.48    inference(flattening,[],[f13])).
% 0.19/0.48  fof(f13,plain,(
% 0.19/0.48    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.19/0.48    inference(ennf_transformation,[],[f9])).
% 0.19/0.48  fof(f9,axiom,(
% 0.19/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).
% 0.19/0.48  fof(f168,plain,(
% 0.19/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) | v1_partfun1(X0,sK2)) )),
% 0.19/0.48    inference(resolution,[],[f167,f53])).
% 0.19/0.48  fof(f53,plain,(
% 0.19/0.48    ( ! [X2,X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_partfun1(X2,X0)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f17])).
% 0.19/0.48  fof(f17,plain,(
% 0.19/0.48    ! [X0,X1] : (! [X2] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 0.19/0.48    inference(ennf_transformation,[],[f5])).
% 0.19/0.48  fof(f5,axiom,(
% 0.19/0.48    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_partfun1(X2,X0)))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_partfun1)).
% 0.19/0.48  fof(f167,plain,(
% 0.19/0.48    v1_xboole_0(sK2)),
% 0.19/0.48    inference(subsumption_resolution,[],[f166,f73])).
% 0.19/0.48  fof(f166,plain,(
% 0.19/0.48    ~r1_tarski(sK2,sK2) | v1_xboole_0(sK2)),
% 0.19/0.48    inference(forward_demodulation,[],[f165,f92])).
% 0.19/0.48  fof(f165,plain,(
% 0.19/0.48    v1_xboole_0(sK2) | ~r1_tarski(k1_relat_1(sK4),sK2)),
% 0.19/0.48    inference(subsumption_resolution,[],[f164,f88])).
% 0.19/0.48  fof(f164,plain,(
% 0.19/0.48    v1_xboole_0(sK2) | ~r1_tarski(k1_relat_1(sK4),sK2) | ~v1_relat_1(sK4)),
% 0.19/0.48    inference(subsumption_resolution,[],[f163,f97])).
% 0.19/0.48  fof(f163,plain,(
% 0.19/0.48    v1_xboole_0(sK2) | ~r1_tarski(k2_relat_1(sK4),sK3) | ~r1_tarski(k1_relat_1(sK4),sK2) | ~v1_relat_1(sK4)),
% 0.19/0.48    inference(resolution,[],[f161,f58])).
% 0.19/0.48  fof(f161,plain,(
% 0.19/0.48    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | v1_xboole_0(sK2)),
% 0.19/0.48    inference(resolution,[],[f159,f87])).
% 0.19/0.48  fof(f159,plain,(
% 0.19/0.48    v1_funct_2(sK4,sK2,sK3) | v1_xboole_0(sK2)),
% 0.19/0.48    inference(resolution,[],[f158,f97])).
% 0.19/0.48  fof(f158,plain,(
% 0.19/0.48    ( ! [X0] : (~r1_tarski(k2_relat_1(sK4),X0) | v1_xboole_0(sK2) | v1_funct_2(sK4,sK2,X0)) )),
% 0.19/0.48    inference(subsumption_resolution,[],[f157,f73])).
% 0.19/0.48  fof(f157,plain,(
% 0.19/0.48    ( ! [X0] : (~r1_tarski(sK2,sK2) | v1_funct_2(sK4,sK2,X0) | v1_xboole_0(sK2) | ~r1_tarski(k2_relat_1(sK4),X0)) )),
% 0.19/0.48    inference(forward_demodulation,[],[f156,f92])).
% 0.19/0.48  fof(f156,plain,(
% 0.19/0.48    ( ! [X0] : (v1_funct_2(sK4,sK2,X0) | v1_xboole_0(sK2) | ~r1_tarski(k2_relat_1(sK4),X0) | ~r1_tarski(k1_relat_1(sK4),sK2)) )),
% 0.19/0.48    inference(subsumption_resolution,[],[f155,f88])).
% 0.19/0.48  fof(f155,plain,(
% 0.19/0.48    ( ! [X0] : (v1_funct_2(sK4,sK2,X0) | v1_xboole_0(sK2) | ~r1_tarski(k2_relat_1(sK4),X0) | ~r1_tarski(k1_relat_1(sK4),sK2) | ~v1_relat_1(sK4)) )),
% 0.19/0.48    inference(resolution,[],[f153,f58])).
% 0.19/0.48  fof(f153,plain,(
% 0.19/0.48    ( ! [X0] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | v1_funct_2(sK4,sK2,X0) | v1_xboole_0(sK2)) )),
% 0.19/0.48    inference(subsumption_resolution,[],[f152,f86])).
% 0.19/0.48  fof(f152,plain,(
% 0.19/0.48    ( ! [X0] : (v1_xboole_0(sK2) | v1_funct_2(sK4,sK2,X0) | ~v1_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))) )),
% 0.19/0.48    inference(resolution,[],[f150,f60])).
% 0.19/0.48  fof(f150,plain,(
% 0.19/0.48    v1_partfun1(sK4,sK2) | v1_xboole_0(sK2)),
% 0.19/0.48    inference(resolution,[],[f149,f111])).
% 0.19/0.48  fof(f111,plain,(
% 0.19/0.48    sP0(k2_relat_1(sK4),sK2,sK4)),
% 0.19/0.48    inference(resolution,[],[f109,f73])).
% 0.19/0.48  fof(f109,plain,(
% 0.19/0.48    ( ! [X4] : (~r1_tarski(k2_relat_1(sK4),X4) | sP0(X4,sK2,sK4)) )),
% 0.19/0.48    inference(forward_demodulation,[],[f108,f92])).
% 0.19/0.48  fof(f108,plain,(
% 0.19/0.48    ( ! [X4] : (~r1_tarski(k2_relat_1(sK4),X4) | sP0(X4,k1_relat_1(sK4),sK4)) )),
% 0.19/0.48    inference(subsumption_resolution,[],[f106,f88])).
% 0.19/0.48  fof(f106,plain,(
% 0.19/0.48    ( ! [X4] : (~r1_tarski(k2_relat_1(sK4),X4) | sP0(X4,k1_relat_1(sK4),sK4) | ~v1_relat_1(sK4)) )),
% 0.19/0.48    inference(resolution,[],[f76,f86])).
% 0.19/0.48  fof(f76,plain,(
% 0.19/0.48    ( ! [X0,X3] : (~v1_funct_1(X3) | ~r1_tarski(k2_relat_1(X3),X0) | sP0(X0,k1_relat_1(X3),X3) | ~v1_relat_1(X3)) )),
% 0.19/0.48    inference(equality_resolution,[],[f75])).
% 0.19/0.48  fof(f75,plain,(
% 0.19/0.48    ( ! [X2,X0,X3] : (sP0(X0,k1_relat_1(X3),X2) | ~r1_tarski(k2_relat_1(X3),X0) | X2 != X3 | ~v1_funct_1(X3) | ~v1_relat_1(X3)) )),
% 0.19/0.48    inference(equality_resolution,[],[f70])).
% 0.19/0.48  fof(f70,plain,(
% 0.19/0.48    ( ! [X2,X0,X3,X1] : (sP0(X0,X1,X2) | ~r1_tarski(k2_relat_1(X3),X0) | k1_relat_1(X3) != X1 | X2 != X3 | ~v1_funct_1(X3) | ~v1_relat_1(X3)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f42])).
% 0.19/0.48  fof(f149,plain,(
% 0.19/0.48    ( ! [X2,X1] : (~sP0(k2_relat_1(sK4),X1,X2) | v1_partfun1(sK4,sK2) | v1_xboole_0(X1)) )),
% 0.19/0.48    inference(resolution,[],[f147,f89])).
% 0.19/0.48  fof(f89,plain,(
% 0.19/0.48    ( ! [X2,X0,X1] : (r2_hidden(X2,k1_funct_2(X1,X0)) | ~sP0(X0,X1,X2)) )),
% 0.19/0.48    inference(resolution,[],[f62,f77])).
% 0.19/0.48  fof(f62,plain,(
% 0.19/0.48    ( ! [X4,X2,X0,X1] : (~sP1(X0,X1,X2) | ~sP0(X1,X0,X4) | r2_hidden(X4,X2)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f38])).
% 0.19/0.48  fof(f147,plain,(
% 0.19/0.48    ( ! [X6,X5] : (~r2_hidden(X6,k1_funct_2(X5,k2_relat_1(sK4))) | v1_xboole_0(X5) | v1_partfun1(sK4,sK2)) )),
% 0.19/0.48    inference(resolution,[],[f142,f49])).
% 0.19/0.48  fof(f49,plain,(
% 0.19/0.48    ( ! [X2,X0] : (~v1_xboole_0(X0) | ~r2_hidden(X2,X0)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f32])).
% 0.19/0.48  fof(f32,plain,(
% 0.19/0.48    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK5(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.19/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f30,f31])).
% 0.19/0.48  fof(f31,plain,(
% 0.19/0.48    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK5(X0),X0))),
% 0.19/0.48    introduced(choice_axiom,[])).
% 0.19/0.48  fof(f30,plain,(
% 0.19/0.48    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.19/0.48    inference(rectify,[],[f29])).
% 0.19/0.48  fof(f29,plain,(
% 0.19/0.48    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.19/0.48    inference(nnf_transformation,[],[f1])).
% 0.19/0.48  fof(f1,axiom,(
% 0.19/0.48    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.19/0.48  fof(f142,plain,(
% 0.19/0.48    ( ! [X2] : (v1_xboole_0(k1_funct_2(X2,k2_relat_1(sK4))) | v1_partfun1(sK4,sK2) | v1_xboole_0(X2)) )),
% 0.19/0.48    inference(resolution,[],[f137,f54])).
% 0.19/0.48  fof(f54,plain,(
% 0.19/0.48    ( ! [X0,X1] : (~v1_xboole_0(X1) | v1_xboole_0(k1_funct_2(X0,X1)) | v1_xboole_0(X0)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f19])).
% 0.19/0.48  fof(f19,plain,(
% 0.19/0.48    ! [X0,X1] : (v1_xboole_0(k1_funct_2(X0,X1)) | ~v1_xboole_0(X1) | v1_xboole_0(X0))),
% 0.19/0.48    inference(flattening,[],[f18])).
% 0.19/0.48  fof(f18,plain,(
% 0.19/0.48    ! [X0,X1] : (v1_xboole_0(k1_funct_2(X0,X1)) | (~v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 0.19/0.48    inference(ennf_transformation,[],[f8])).
% 0.19/0.48  fof(f8,axiom,(
% 0.19/0.48    ! [X0,X1] : ((v1_xboole_0(X1) & ~v1_xboole_0(X0)) => v1_xboole_0(k1_funct_2(X0,X1)))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_2)).
% 0.19/0.48  fof(f137,plain,(
% 0.19/0.48    v1_xboole_0(k2_relat_1(sK4)) | v1_partfun1(sK4,sK2)),
% 0.19/0.48    inference(subsumption_resolution,[],[f135,f104])).
% 0.19/0.48  fof(f135,plain,(
% 0.19/0.48    v1_partfun1(sK4,sK2) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(sK4)))) | v1_xboole_0(k2_relat_1(sK4))),
% 0.19/0.48    inference(resolution,[],[f134,f95])).
% 0.19/0.48  fof(f95,plain,(
% 0.19/0.48    v1_funct_2(sK4,sK2,k2_relat_1(sK4))),
% 0.19/0.48    inference(subsumption_resolution,[],[f94,f88])).
% 0.19/0.48  fof(f94,plain,(
% 0.19/0.48    v1_funct_2(sK4,sK2,k2_relat_1(sK4)) | ~v1_relat_1(sK4)),
% 0.19/0.48    inference(subsumption_resolution,[],[f93,f86])).
% 0.19/0.48  fof(f93,plain,(
% 0.19/0.48    v1_funct_2(sK4,sK2,k2_relat_1(sK4)) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4)),
% 0.19/0.48    inference(superposition,[],[f47,f92])).
% 0.19/0.48  fof(f47,plain,(
% 0.19/0.48    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f14])).
% 0.19/0.48  fof(f134,plain,(
% 0.19/0.48    ( ! [X6,X5] : (~v1_funct_2(sK4,X5,X6) | v1_partfun1(sK4,X5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | v1_xboole_0(X6)) )),
% 0.19/0.48    inference(resolution,[],[f52,f86])).
% 0.19/0.48  fof(f52,plain,(
% 0.19/0.48    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f16])).
% 0.19/0.48  fof(f16,plain,(
% 0.19/0.48    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.19/0.48    inference(flattening,[],[f15])).
% 0.19/0.48  fof(f15,plain,(
% 0.19/0.48    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.19/0.48    inference(ennf_transformation,[],[f6])).
% 0.19/0.48  fof(f6,axiom,(
% 0.19/0.48    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.19/0.48  fof(f87,plain,(
% 0.19/0.48    ~v1_funct_2(sK4,sK2,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 0.19/0.48    inference(subsumption_resolution,[],[f45,f86])).
% 0.19/0.48  fof(f45,plain,(
% 0.19/0.48    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | ~v1_funct_2(sK4,sK2,sK3) | ~v1_funct_1(sK4)),
% 0.19/0.48    inference(cnf_transformation,[],[f28])).
% 0.19/0.48  % SZS output end Proof for theBenchmark
% 0.19/0.48  % (15788)------------------------------
% 0.19/0.48  % (15788)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.48  % (15788)Termination reason: Refutation
% 0.19/0.48  
% 0.19/0.48  % (15788)Memory used [KB]: 6268
% 0.19/0.48  % (15788)Time elapsed: 0.088 s
% 0.19/0.48  % (15788)------------------------------
% 0.19/0.48  % (15788)------------------------------
% 0.19/0.49  % (15784)Success in time 0.148 s
%------------------------------------------------------------------------------
