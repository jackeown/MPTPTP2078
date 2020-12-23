%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1048+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:10 EST 2020

% Result     : Theorem 0.12s
% Output     : Refutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 469 expanded)
%              Number of leaves         :   11 ( 152 expanded)
%              Depth                    :   24
%              Number of atoms          :  470 (3485 expanded)
%              Number of equality atoms :   46 ( 323 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f161,plain,(
    $false ),
    inference(subsumption_resolution,[],[f157,f32])).

fof(f32,plain,(
    ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3))
    & r1_relset_1(sK0,sK1,sK3,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f17,f16])).

fof(f16,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3))
            & r1_relset_1(X0,X1,X3,X2)
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,X3))
          & r1_relset_1(sK0,sK1,X3,sK2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X3] :
        ( ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,X3))
        & r1_relset_1(sK0,sK1,X3,sK2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        & v1_funct_1(X3) )
   => ( ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3))
      & r1_relset_1(sK0,sK1,sK3,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3))
          & r1_relset_1(X0,X1,X3,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3))
          & r1_relset_1(X0,X1,X3,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_1(X3) )
           => ( r1_relset_1(X0,X1,X3,X2)
             => r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3)) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
         => ( r1_relset_1(X0,X1,X3,X2)
           => r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t165_funct_2)).

fof(f157,plain,(
    r1_tarski(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)) ),
    inference(resolution,[],[f156,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f10,f19])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f156,plain,(
    r2_hidden(sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)),k5_partfun1(sK0,sK1,sK3)) ),
    inference(subsumption_resolution,[],[f155,f32])).

fof(f155,plain,
    ( r2_hidden(sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)),k5_partfun1(sK0,sK1,sK3))
    | r1_tarski(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)) ),
    inference(resolution,[],[f153,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f153,plain,
    ( ~ r2_hidden(sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)),k5_partfun1(sK0,sK1,sK2))
    | r2_hidden(sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)),k5_partfun1(sK0,sK1,sK3)) ),
    inference(resolution,[],[f150,f142])).

fof(f142,plain,
    ( v1_partfun1(sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)),sK0)
    | ~ r2_hidden(sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)),k5_partfun1(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f141,f27])).

fof(f27,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f141,plain,
    ( v1_partfun1(sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)),sK0)
    | ~ r2_hidden(sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)),k5_partfun1(sK0,sK1,sK2))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f139,f28])).

fof(f28,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f18])).

fof(f139,plain,
    ( v1_partfun1(sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)),sK0)
    | ~ r2_hidden(sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)),k5_partfun1(sK0,sK1,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f53,f122])).

fof(f122,plain,(
    sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)) = sK7(sK0,sK1,sK2,sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3))) ),
    inference(subsumption_resolution,[],[f121,f27])).

fof(f121,plain,
    ( ~ v1_funct_1(sK2)
    | sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)) = sK7(sK0,sK1,sK2,sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3))) ),
    inference(subsumption_resolution,[],[f120,f28])).

fof(f120,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)) = sK7(sK0,sK1,sK2,sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3))) ),
    inference(resolution,[],[f62,f32])).

% (643)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% (622)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% (671)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% (636)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% (638)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% (669)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k5_partfun1(X0,X1,X2),X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | sK4(k5_partfun1(X0,X1,X2),X3) = sK7(X0,X1,X2,sK4(k5_partfun1(X0,X1,X2),X3)) ) ),
    inference(resolution,[],[f54,f33])).

fof(f54,plain,(
    ! [X2,X0,X7,X1] :
      ( ~ r2_hidden(X7,k5_partfun1(X0,X1,X2))
      | sK7(X0,X1,X2,X7) = X7
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X2,X0,X7,X3,X1] :
      ( sK7(X0,X1,X2,X7) = X7
      | ~ r2_hidden(X7,X3)
      | k5_partfun1(X0,X1,X2) != X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k5_partfun1(X0,X1,X2) = X3
            | ( ( ! [X5] :
                    ( ~ r1_partfun1(X2,X5)
                    | ~ v1_partfun1(X5,X0)
                    | sK5(X0,X1,X2,X3) != X5
                    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                    | ~ v1_funct_1(X5) )
                | ~ r2_hidden(sK5(X0,X1,X2,X3),X3) )
              & ( ( r1_partfun1(X2,sK6(X0,X1,X2,X3))
                  & v1_partfun1(sK6(X0,X1,X2,X3),X0)
                  & sK5(X0,X1,X2,X3) = sK6(X0,X1,X2,X3)
                  & m1_subset_1(sK6(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(sK6(X0,X1,X2,X3)) )
                | r2_hidden(sK5(X0,X1,X2,X3),X3) ) ) )
          & ( ! [X7] :
                ( ( r2_hidden(X7,X3)
                  | ! [X8] :
                      ( ~ r1_partfun1(X2,X8)
                      | ~ v1_partfun1(X8,X0)
                      | X7 != X8
                      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      | ~ v1_funct_1(X8) ) )
                & ( ( r1_partfun1(X2,sK7(X0,X1,X2,X7))
                    & v1_partfun1(sK7(X0,X1,X2,X7),X0)
                    & sK7(X0,X1,X2,X7) = X7
                    & m1_subset_1(sK7(X0,X1,X2,X7),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                    & v1_funct_1(sK7(X0,X1,X2,X7)) )
                  | ~ r2_hidden(X7,X3) ) )
            | k5_partfun1(X0,X1,X2) != X3 ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f22,f25,f24,f23])).

fof(f23,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ! [X5] :
                ( ~ r1_partfun1(X2,X5)
                | ~ v1_partfun1(X5,X0)
                | X4 != X5
                | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                | ~ v1_funct_1(X5) )
            | ~ r2_hidden(X4,X3) )
          & ( ? [X6] :
                ( r1_partfun1(X2,X6)
                & v1_partfun1(X6,X0)
                & X4 = X6
                & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_1(X6) )
            | r2_hidden(X4,X3) ) )
     => ( ( ! [X5] :
              ( ~ r1_partfun1(X2,X5)
              | ~ v1_partfun1(X5,X0)
              | sK5(X0,X1,X2,X3) != X5
              | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_1(X5) )
          | ~ r2_hidden(sK5(X0,X1,X2,X3),X3) )
        & ( ? [X6] :
              ( r1_partfun1(X2,X6)
              & v1_partfun1(X6,X0)
              & sK5(X0,X1,X2,X3) = X6
              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_1(X6) )
          | r2_hidden(sK5(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X6] :
          ( r1_partfun1(X2,X6)
          & v1_partfun1(X6,X0)
          & sK5(X0,X1,X2,X3) = X6
          & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X6) )
     => ( r1_partfun1(X2,sK6(X0,X1,X2,X3))
        & v1_partfun1(sK6(X0,X1,X2,X3),X0)
        & sK5(X0,X1,X2,X3) = sK6(X0,X1,X2,X3)
        & m1_subset_1(sK6(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(sK6(X0,X1,X2,X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X7,X2,X1,X0] :
      ( ? [X9] :
          ( r1_partfun1(X2,X9)
          & v1_partfun1(X9,X0)
          & X7 = X9
          & m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X9) )
     => ( r1_partfun1(X2,sK7(X0,X1,X2,X7))
        & v1_partfun1(sK7(X0,X1,X2,X7),X0)
        & sK7(X0,X1,X2,X7) = X7
        & m1_subset_1(sK7(X0,X1,X2,X7),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(sK7(X0,X1,X2,X7)) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k5_partfun1(X0,X1,X2) = X3
            | ? [X4] :
                ( ( ! [X5] :
                      ( ~ r1_partfun1(X2,X5)
                      | ~ v1_partfun1(X5,X0)
                      | X4 != X5
                      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      | ~ v1_funct_1(X5) )
                  | ~ r2_hidden(X4,X3) )
                & ( ? [X6] :
                      ( r1_partfun1(X2,X6)
                      & v1_partfun1(X6,X0)
                      & X4 = X6
                      & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      & v1_funct_1(X6) )
                  | r2_hidden(X4,X3) ) ) )
          & ( ! [X7] :
                ( ( r2_hidden(X7,X3)
                  | ! [X8] :
                      ( ~ r1_partfun1(X2,X8)
                      | ~ v1_partfun1(X8,X0)
                      | X7 != X8
                      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      | ~ v1_funct_1(X8) ) )
                & ( ? [X9] :
                      ( r1_partfun1(X2,X9)
                      & v1_partfun1(X9,X0)
                      & X7 = X9
                      & m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      & v1_funct_1(X9) )
                  | ~ r2_hidden(X7,X3) ) )
            | k5_partfun1(X0,X1,X2) != X3 ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k5_partfun1(X0,X1,X2) = X3
            | ? [X4] :
                ( ( ! [X5] :
                      ( ~ r1_partfun1(X2,X5)
                      | ~ v1_partfun1(X5,X0)
                      | X4 != X5
                      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      | ~ v1_funct_1(X5) )
                  | ~ r2_hidden(X4,X3) )
                & ( ? [X5] :
                      ( r1_partfun1(X2,X5)
                      & v1_partfun1(X5,X0)
                      & X4 = X5
                      & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      & v1_funct_1(X5) )
                  | r2_hidden(X4,X3) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X3)
                  | ! [X5] :
                      ( ~ r1_partfun1(X2,X5)
                      | ~ v1_partfun1(X5,X0)
                      | X4 != X5
                      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      | ~ v1_funct_1(X5) ) )
                & ( ? [X5] :
                      ( r1_partfun1(X2,X5)
                      & v1_partfun1(X5,X0)
                      & X4 = X5
                      & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      & v1_funct_1(X5) )
                  | ~ r2_hidden(X4,X3) ) )
            | k5_partfun1(X0,X1,X2) != X3 ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_partfun1)).

fof(f53,plain,(
    ! [X2,X0,X7,X1] :
      ( v1_partfun1(sK7(X0,X1,X2,X7),X0)
      | ~ r2_hidden(X7,k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X2,X0,X7,X3,X1] :
      ( v1_partfun1(sK7(X0,X1,X2,X7),X0)
      | ~ r2_hidden(X7,X3)
      | k5_partfun1(X0,X1,X2) != X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f150,plain,
    ( ~ v1_partfun1(sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)),sK0)
    | r2_hidden(sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)),k5_partfun1(sK0,sK1,sK3)) ),
    inference(subsumption_resolution,[],[f149,f124])).

fof(f124,plain,(
    m1_subset_1(sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(backward_demodulation,[],[f91,f122])).

fof(f91,plain,(
    m1_subset_1(sK7(sK0,sK1,sK2,sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3))),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f90,f27])).

fof(f90,plain,
    ( ~ v1_funct_1(sK2)
    | m1_subset_1(sK7(sK0,sK1,sK2,sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3))),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f89,f28])).

fof(f89,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | m1_subset_1(sK7(sK0,sK1,sK2,sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3))),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f63,f32])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k5_partfun1(X0,X1,X2),X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | m1_subset_1(sK7(X0,X1,X2,sK4(k5_partfun1(X0,X1,X2),X3)),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(resolution,[],[f55,f33])).

fof(f55,plain,(
    ! [X2,X0,X7,X1] :
      ( ~ r2_hidden(X7,k5_partfun1(X0,X1,X2))
      | m1_subset_1(sK7(X0,X1,X2,X7),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X7,X3,X1] :
      ( m1_subset_1(sK7(X0,X1,X2,X7),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X7,X3)
      | k5_partfun1(X0,X1,X2) != X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f149,plain,
    ( ~ v1_partfun1(sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)),sK0)
    | ~ m1_subset_1(sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | r2_hidden(sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)),k5_partfun1(sK0,sK1,sK3)) ),
    inference(subsumption_resolution,[],[f147,f123])).

fof(f123,plain,(
    v1_funct_1(sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3))) ),
    inference(backward_demodulation,[],[f66,f122])).

fof(f66,plain,(
    v1_funct_1(sK7(sK0,sK1,sK2,sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)))) ),
    inference(subsumption_resolution,[],[f65,f27])).

fof(f65,plain,
    ( ~ v1_funct_1(sK2)
    | v1_funct_1(sK7(sK0,sK1,sK2,sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)))) ),
    inference(subsumption_resolution,[],[f64,f28])).

fof(f64,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | v1_funct_1(sK7(sK0,sK1,sK2,sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)))) ),
    inference(resolution,[],[f61,f32])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k5_partfun1(X0,X1,X2),X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | v1_funct_1(sK7(X0,X1,X2,sK4(k5_partfun1(X0,X1,X2),X3))) ) ),
    inference(resolution,[],[f56,f33])).

fof(f56,plain,(
    ! [X2,X0,X7,X1] :
      ( ~ r2_hidden(X7,k5_partfun1(X0,X1,X2))
      | v1_funct_1(sK7(X0,X1,X2,X7))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X7,X3,X1] :
      ( v1_funct_1(sK7(X0,X1,X2,X7))
      | ~ r2_hidden(X7,X3)
      | k5_partfun1(X0,X1,X2) != X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f147,plain,
    ( ~ v1_funct_1(sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)))
    | ~ v1_partfun1(sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)),sK0)
    | ~ m1_subset_1(sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | r2_hidden(sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)),k5_partfun1(sK0,sK1,sK3)) ),
    inference(resolution,[],[f146,f115])).

fof(f115,plain,(
    ! [X0] :
      ( ~ r1_partfun1(sK2,X0)
      | ~ v1_funct_1(X0)
      | ~ v1_partfun1(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | r2_hidden(X0,k5_partfun1(sK0,sK1,sK3)) ) ),
    inference(subsumption_resolution,[],[f114,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
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

fof(f114,plain,(
    ! [X0] :
      ( ~ r1_partfun1(sK2,X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_partfun1(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | r2_hidden(X0,k5_partfun1(sK0,sK1,sK3)) ) ),
    inference(duplicate_literal_removal,[],[f113])).

% (668)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
fof(f113,plain,(
    ! [X0] :
      ( ~ r1_partfun1(sK2,X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_partfun1(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(X0)
      | r2_hidden(X0,k5_partfun1(sK0,sK1,sK3)) ) ),
    inference(resolution,[],[f112,f80])).

fof(f80,plain,(
    ! [X1] :
      ( ~ r1_partfun1(sK3,X1)
      | ~ v1_partfun1(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(X1)
      | r2_hidden(X1,k5_partfun1(sK0,sK1,sK3)) ) ),
    inference(subsumption_resolution,[],[f78,f29])).

fof(f29,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f78,plain,(
    ! [X1] :
      ( ~ r1_partfun1(sK3,X1)
      | ~ v1_partfun1(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(X1)
      | r2_hidden(X1,k5_partfun1(sK0,sK1,sK3))
      | ~ v1_funct_1(sK3) ) ),
    inference(resolution,[],[f51,f30])).

fof(f30,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f18])).

fof(f51,plain,(
    ! [X2,X0,X8,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_partfun1(X2,X8)
      | ~ v1_partfun1(X8,X0)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X8)
      | r2_hidden(X8,k5_partfun1(X0,X1,X2))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X2,X0,X8,X3,X1] :
      ( r2_hidden(X8,X3)
      | ~ r1_partfun1(X2,X8)
      | ~ v1_partfun1(X8,X0)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X8)
      | k5_partfun1(X0,X1,X2) != X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X2,X0,X8,X7,X3,X1] :
      ( r2_hidden(X7,X3)
      | ~ r1_partfun1(X2,X8)
      | ~ v1_partfun1(X8,X0)
      | X7 != X8
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X8)
      | k5_partfun1(X0,X1,X2) != X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f112,plain,(
    ! [X0] :
      ( r1_partfun1(sK3,X0)
      | ~ r1_partfun1(sK2,X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f111,f27])).

fof(f111,plain,(
    ! [X0] :
      ( r1_partfun1(sK3,X0)
      | ~ r1_partfun1(sK2,X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(sK2) ) ),
    inference(subsumption_resolution,[],[f110,f28])).

fof(f110,plain,(
    ! [X0] :
      ( r1_partfun1(sK3,X0)
      | ~ r1_partfun1(sK2,X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(sK2) ) ),
    inference(subsumption_resolution,[],[f109,f29])).

fof(f109,plain,(
    ! [X0] :
      ( r1_partfun1(sK3,X0)
      | ~ r1_partfun1(sK2,X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(sK2) ) ),
    inference(subsumption_resolution,[],[f108,f30])).

fof(f108,plain,(
    ! [X0] :
      ( r1_partfun1(sK3,X0)
      | ~ r1_partfun1(sK2,X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(sK2) ) ),
    inference(resolution,[],[f47,f31])).

fof(f31,plain,(
    r1_relset_1(sK0,sK1,sK3,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f47,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r1_relset_1(X0,X1,X3,X2)
      | r1_partfun1(X3,X4)
      | ~ r1_partfun1(X2,X4)
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( r1_partfun1(X3,X4)
              | ~ r1_relset_1(X0,X1,X3,X2)
              | ~ r1_partfun1(X2,X4)
              | ~ v1_funct_1(X4)
              | ~ v1_relat_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( r1_partfun1(X3,X4)
              | ~ r1_relset_1(X0,X1,X3,X2)
              | ~ r1_partfun1(X2,X4)
              | ~ v1_funct_1(X4)
              | ~ v1_relat_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
         => ! [X4] :
              ( ( v1_funct_1(X4)
                & v1_relat_1(X4) )
             => ( ( r1_relset_1(X0,X1,X3,X2)
                  & r1_partfun1(X2,X4) )
               => r1_partfun1(X3,X4) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_partfun1)).

fof(f146,plain,(
    r1_partfun1(sK2,sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3))) ),
    inference(subsumption_resolution,[],[f145,f32])).

fof(f145,plain,
    ( r1_partfun1(sK2,sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)))
    | r1_tarski(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)) ),
    inference(resolution,[],[f144,f33])).

fof(f144,plain,
    ( ~ r2_hidden(sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)),k5_partfun1(sK0,sK1,sK2))
    | r1_partfun1(sK2,sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3))) ),
    inference(subsumption_resolution,[],[f143,f27])).

fof(f143,plain,
    ( r1_partfun1(sK2,sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)))
    | ~ r2_hidden(sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)),k5_partfun1(sK0,sK1,sK2))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f140,f28])).

fof(f140,plain,
    ( r1_partfun1(sK2,sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)))
    | ~ r2_hidden(sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)),k5_partfun1(sK0,sK1,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f52,f122])).

fof(f52,plain,(
    ! [X2,X0,X7,X1] :
      ( r1_partfun1(X2,sK7(X0,X1,X2,X7))
      | ~ r2_hidden(X7,k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X2,X0,X7,X3,X1] :
      ( r1_partfun1(X2,sK7(X0,X1,X2,X7))
      | ~ r2_hidden(X7,X3)
      | k5_partfun1(X0,X1,X2) != X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

%------------------------------------------------------------------------------
