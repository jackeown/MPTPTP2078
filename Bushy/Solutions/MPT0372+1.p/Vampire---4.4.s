%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : subset_1__t53_subset_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:25 EDT 2019

% Result     : Theorem 0.12s
% Output     : Refutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   40 ( 140 expanded)
%              Number of leaves         :    5 (  39 expanded)
%              Depth                    :   16
%              Number of atoms          :  191 (1001 expanded)
%              Number of equality atoms :   26 ( 140 expanded)
%              Maximal formula depth    :   13 (   7 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f189,plain,(
    $false ),
    inference(subsumption_resolution,[],[f188,f41])).

fof(f41,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( k3_subset_1(sK0,sK2) != sK1
    & ! [X3] :
        ( ( ( ~ r2_hidden(X3,sK2)
            | ~ r2_hidden(X3,sK1) )
          & ( r2_hidden(X3,sK2)
            | r2_hidden(X3,sK1) ) )
        | ~ m1_subset_1(X3,sK0) )
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f30,f32,f31])).

fof(f31,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( k3_subset_1(X0,X2) != X1
            & ! [X3] :
                ( ( ( ~ r2_hidden(X3,X2)
                    | ~ r2_hidden(X3,X1) )
                  & ( r2_hidden(X3,X2)
                    | r2_hidden(X3,X1) ) )
                | ~ m1_subset_1(X3,X0) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( k3_subset_1(sK0,X2) != sK1
          & ! [X3] :
              ( ( ( ~ r2_hidden(X3,X2)
                  | ~ r2_hidden(X3,sK1) )
                & ( r2_hidden(X3,X2)
                  | r2_hidden(X3,sK1) ) )
              | ~ m1_subset_1(X3,sK0) )
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & ! [X3] :
              ( ( ( ~ r2_hidden(X3,X2)
                  | ~ r2_hidden(X3,X1) )
                & ( r2_hidden(X3,X2)
                  | r2_hidden(X3,X1) ) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
     => ( k3_subset_1(X0,sK2) != X1
        & ! [X3] :
            ( ( ( ~ r2_hidden(X3,sK2)
                | ~ r2_hidden(X3,X1) )
              & ( r2_hidden(X3,sK2)
                | r2_hidden(X3,X1) ) )
            | ~ m1_subset_1(X3,X0) )
        & m1_subset_1(sK2,k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & ! [X3] :
              ( ( ( ~ r2_hidden(X3,X2)
                  | ~ r2_hidden(X3,X1) )
                & ( r2_hidden(X3,X2)
                  | r2_hidden(X3,X1) ) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( ! [X3] :
                  ( m1_subset_1(X3,X0)
                 => ~ ( r2_hidden(X3,X1)
                    <=> r2_hidden(X3,X2) ) )
             => k3_subset_1(X0,X2) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ~ ( r2_hidden(X3,X1)
                  <=> r2_hidden(X3,X2) ) )
           => k3_subset_1(X0,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t53_subset_1.p',t53_subset_1)).

fof(f188,plain,(
    ~ m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f182,f44])).

fof(f44,plain,(
    k3_subset_1(sK0,sK2) != sK1 ),
    inference(cnf_transformation,[],[f33])).

fof(f182,plain,
    ( k3_subset_1(sK0,sK2) = sK1
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f181,f54])).

fof(f54,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(sK0,sK1,X0),sK0)
      | k3_subset_1(sK0,X0) = sK1
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f40,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k3_subset_1(X0,X2) = X1
      | m1_subset_1(sK3(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k3_subset_1(X0,X2) = X1
          | ( ( r2_hidden(sK3(X0,X1,X2),X2)
              | ~ r2_hidden(sK3(X0,X1,X2),X1) )
            & ( ~ r2_hidden(sK3(X0,X1,X2),X2)
              | r2_hidden(sK3(X0,X1,X2),X1) )
            & m1_subset_1(sK3(X0,X1,X2),X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f35,f36])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X2)
            | ~ r2_hidden(X3,X1) )
          & ( ~ r2_hidden(X3,X2)
            | r2_hidden(X3,X1) )
          & m1_subset_1(X3,X0) )
     => ( ( r2_hidden(sK3(X0,X1,X2),X2)
          | ~ r2_hidden(sK3(X0,X1,X2),X1) )
        & ( ~ r2_hidden(sK3(X0,X1,X2),X2)
          | r2_hidden(sK3(X0,X1,X2),X1) )
        & m1_subset_1(sK3(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k3_subset_1(X0,X2) = X1
          | ? [X3] :
              ( ( r2_hidden(X3,X2)
                | ~ r2_hidden(X3,X1) )
              & ( ~ r2_hidden(X3,X2)
                | r2_hidden(X3,X1) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k3_subset_1(X0,X2) = X1
          | ? [X3] :
              ( ( r2_hidden(X3,X2)
                | ~ r2_hidden(X3,X1) )
              & ( ~ r2_hidden(X3,X2)
                | r2_hidden(X3,X1) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k3_subset_1(X0,X2) = X1
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> ~ r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k3_subset_1(X0,X2) = X1
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> ~ r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                <=> ~ r2_hidden(X3,X2) ) )
           => k3_subset_1(X0,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t53_subset_1.p',t51_subset_1)).

fof(f40,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f33])).

fof(f181,plain,(
    ~ m1_subset_1(sK3(sK0,sK1,sK2),sK0) ),
    inference(subsumption_resolution,[],[f180,f166])).

fof(f166,plain,
    ( r2_hidden(sK3(sK0,sK1,sK2),sK1)
    | ~ m1_subset_1(sK3(sK0,sK1,sK2),sK0) ),
    inference(duplicate_literal_removal,[],[f165])).

fof(f165,plain,
    ( r2_hidden(sK3(sK0,sK1,sK2),sK1)
    | r2_hidden(sK3(sK0,sK1,sK2),sK1)
    | ~ m1_subset_1(sK3(sK0,sK1,sK2),sK0) ),
    inference(resolution,[],[f163,f42])).

fof(f42,plain,(
    ! [X3] :
      ( r2_hidden(X3,sK2)
      | r2_hidden(X3,sK1)
      | ~ m1_subset_1(X3,sK0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f163,plain,
    ( ~ r2_hidden(sK3(sK0,sK1,sK2),sK2)
    | r2_hidden(sK3(sK0,sK1,sK2),sK1) ),
    inference(subsumption_resolution,[],[f162,f40])).

fof(f162,plain,
    ( ~ r2_hidden(sK3(sK0,sK1,sK2),sK2)
    | r2_hidden(sK3(sK0,sK1,sK2),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X1] :
      ( sK1 != X1
      | ~ r2_hidden(sK3(sK0,X1,sK2),sK2)
      | r2_hidden(sK3(sK0,X1,sK2),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f69,f41])).

fof(f69,plain,(
    ! [X1] :
      ( sK1 != X1
      | ~ r2_hidden(sK3(sK0,X1,sK2),sK2)
      | r2_hidden(sK3(sK0,X1,sK2),X1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(sK0)) ) ),
    inference(superposition,[],[f44,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k3_subset_1(X0,X2) = X1
      | ~ r2_hidden(sK3(X0,X1,X2),X2)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f180,plain,
    ( ~ r2_hidden(sK3(sK0,sK1,sK2),sK1)
    | ~ m1_subset_1(sK3(sK0,sK1,sK2),sK0) ),
    inference(duplicate_literal_removal,[],[f177])).

fof(f177,plain,
    ( ~ r2_hidden(sK3(sK0,sK1,sK2),sK1)
    | ~ r2_hidden(sK3(sK0,sK1,sK2),sK1)
    | ~ m1_subset_1(sK3(sK0,sK1,sK2),sK0) ),
    inference(resolution,[],[f174,f43])).

fof(f43,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK2)
      | ~ r2_hidden(X3,sK1)
      | ~ m1_subset_1(X3,sK0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f174,plain,
    ( r2_hidden(sK3(sK0,sK1,sK2),sK2)
    | ~ r2_hidden(sK3(sK0,sK1,sK2),sK1) ),
    inference(subsumption_resolution,[],[f173,f40])).

fof(f173,plain,
    ( r2_hidden(sK3(sK0,sK1,sK2),sK2)
    | ~ r2_hidden(sK3(sK0,sK1,sK2),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X2] :
      ( sK1 != X2
      | r2_hidden(sK3(sK0,X2,sK2),sK2)
      | ~ r2_hidden(sK3(sK0,X2,sK2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f70,f41])).

fof(f70,plain,(
    ! [X2] :
      ( sK1 != X2
      | r2_hidden(sK3(sK0,X2,sK2),sK2)
      | ~ r2_hidden(sK3(sK0,X2,sK2),X2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(sK0)) ) ),
    inference(superposition,[],[f44,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k3_subset_1(X0,X2) = X1
      | r2_hidden(sK3(X0,X1,X2),X2)
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f37])).
%------------------------------------------------------------------------------
