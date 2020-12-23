%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : subset_1__t16_subset_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:21 EDT 2019

% Result     : Theorem 150.25s
% Output     : Refutation 150.25s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 419 expanded)
%              Number of leaves         :   13 ( 128 expanded)
%              Depth                    :   20
%              Number of atoms          :  410 (3593 expanded)
%              Number of equality atoms :   45 ( 364 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f44994,plain,(
    $false ),
    inference(subsumption_resolution,[],[f44974,f10537])).

fof(f10537,plain,(
    ~ r1_tarski(k3_xboole_0(sK2,sK3),sK1) ),
    inference(subsumption_resolution,[],[f10526,f124])).

fof(f124,plain,(
    k3_xboole_0(sK2,sK3) != sK1 ),
    inference(subsumption_resolution,[],[f123,f55])).

fof(f55,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( k9_subset_1(sK0,sK2,sK3) != sK1
    & ! [X4] :
        ( ( ( r2_hidden(X4,sK1)
            | ~ r2_hidden(X4,sK3)
            | ~ r2_hidden(X4,sK2) )
          & ( ( r2_hidden(X4,sK3)
              & r2_hidden(X4,sK2) )
            | ~ r2_hidden(X4,sK1) ) )
        | ~ m1_subset_1(X4,sK0) )
    & m1_subset_1(sK3,k1_zfmisc_1(sK0))
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f37,f40,f39,f38])).

fof(f38,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( k9_subset_1(X0,X2,X3) != X1
                & ! [X4] :
                    ( ( ( r2_hidden(X4,X1)
                        | ~ r2_hidden(X4,X3)
                        | ~ r2_hidden(X4,X2) )
                      & ( ( r2_hidden(X4,X3)
                          & r2_hidden(X4,X2) )
                        | ~ r2_hidden(X4,X1) ) )
                    | ~ m1_subset_1(X4,X0) )
                & m1_subset_1(X3,k1_zfmisc_1(X0)) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ? [X3] :
              ( k9_subset_1(sK0,X2,X3) != sK1
              & ! [X4] :
                  ( ( ( r2_hidden(X4,sK1)
                      | ~ r2_hidden(X4,X3)
                      | ~ r2_hidden(X4,X2) )
                    & ( ( r2_hidden(X4,X3)
                        & r2_hidden(X4,X2) )
                      | ~ r2_hidden(X4,sK1) ) )
                  | ~ m1_subset_1(X4,sK0) )
              & m1_subset_1(X3,k1_zfmisc_1(sK0)) )
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( k9_subset_1(X0,X2,X3) != X1
              & ! [X4] :
                  ( ( ( r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,X3)
                      | ~ r2_hidden(X4,X2) )
                    & ( ( r2_hidden(X4,X3)
                        & r2_hidden(X4,X2) )
                      | ~ r2_hidden(X4,X1) ) )
                  | ~ m1_subset_1(X4,X0) )
              & m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
     => ( ? [X3] :
            ( k9_subset_1(X0,sK2,X3) != X1
            & ! [X4] :
                ( ( ( r2_hidden(X4,X1)
                    | ~ r2_hidden(X4,X3)
                    | ~ r2_hidden(X4,sK2) )
                  & ( ( r2_hidden(X4,X3)
                      & r2_hidden(X4,sK2) )
                    | ~ r2_hidden(X4,X1) ) )
                | ~ m1_subset_1(X4,X0) )
            & m1_subset_1(X3,k1_zfmisc_1(X0)) )
        & m1_subset_1(sK2,k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( k9_subset_1(X0,X2,X3) != X1
          & ! [X4] :
              ( ( ( r2_hidden(X4,X1)
                  | ~ r2_hidden(X4,X3)
                  | ~ r2_hidden(X4,X2) )
                & ( ( r2_hidden(X4,X3)
                    & r2_hidden(X4,X2) )
                  | ~ r2_hidden(X4,X1) ) )
              | ~ m1_subset_1(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(X0)) )
     => ( k9_subset_1(X0,X2,sK3) != X1
        & ! [X4] :
            ( ( ( r2_hidden(X4,X1)
                | ~ r2_hidden(X4,sK3)
                | ~ r2_hidden(X4,X2) )
              & ( ( r2_hidden(X4,sK3)
                  & r2_hidden(X4,X2) )
                | ~ r2_hidden(X4,X1) ) )
            | ~ m1_subset_1(X4,X0) )
        & m1_subset_1(sK3,k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( k9_subset_1(X0,X2,X3) != X1
              & ! [X4] :
                  ( ( ( r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,X3)
                      | ~ r2_hidden(X4,X2) )
                    & ( ( r2_hidden(X4,X3)
                        & r2_hidden(X4,X2) )
                      | ~ r2_hidden(X4,X1) ) )
                  | ~ m1_subset_1(X4,X0) )
              & m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( k9_subset_1(X0,X2,X3) != X1
              & ! [X4] :
                  ( ( ( r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,X3)
                      | ~ r2_hidden(X4,X2) )
                    & ( ( r2_hidden(X4,X3)
                        & r2_hidden(X4,X2) )
                      | ~ r2_hidden(X4,X1) ) )
                  | ~ m1_subset_1(X4,X0) )
              & m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( k9_subset_1(X0,X2,X3) != X1
              & ! [X4] :
                  ( ( r2_hidden(X4,X1)
                  <=> ( r2_hidden(X4,X3)
                      & r2_hidden(X4,X2) ) )
                  | ~ m1_subset_1(X4,X0) )
              & m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( k9_subset_1(X0,X2,X3) != X1
              & ! [X4] :
                  ( ( r2_hidden(X4,X1)
                  <=> ( r2_hidden(X4,X3)
                      & r2_hidden(X4,X2) ) )
                  | ~ m1_subset_1(X4,X0) )
              & m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(X0))
               => ( ! [X4] :
                      ( m1_subset_1(X4,X0)
                     => ( r2_hidden(X4,X1)
                      <=> ( r2_hidden(X4,X3)
                          & r2_hidden(X4,X2) ) ) )
                 => k9_subset_1(X0,X2,X3) = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(X0))
             => ( ! [X4] :
                    ( m1_subset_1(X4,X0)
                   => ( r2_hidden(X4,X1)
                    <=> ( r2_hidden(X4,X3)
                        & r2_hidden(X4,X2) ) ) )
               => k9_subset_1(X0,X2,X3) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t16_subset_1.p',t16_subset_1)).

fof(f123,plain,
    ( k3_xboole_0(sK2,sK3) != sK1
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f59,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t16_subset_1.p',redefinition_k9_subset_1)).

fof(f59,plain,(
    k9_subset_1(sK0,sK2,sK3) != sK1 ),
    inference(cnf_transformation,[],[f41])).

fof(f10526,plain,
    ( k3_xboole_0(sK2,sK3) = sK1
    | ~ r1_tarski(k3_xboole_0(sK2,sK3),sK1) ),
    inference(resolution,[],[f10470,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t16_subset_1.p',d10_xboole_0)).

fof(f10470,plain,(
    r1_tarski(sK1,k3_xboole_0(sK2,sK3)) ),
    inference(forward_demodulation,[],[f10469,f65])).

fof(f65,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t16_subset_1.p',commutativity_k3_xboole_0)).

fof(f10469,plain,(
    r1_tarski(sK1,k3_xboole_0(sK3,sK2)) ),
    inference(subsumption_resolution,[],[f10444,f288])).

fof(f288,plain,(
    ! [X6] : m1_subset_1(k3_xboole_0(sK3,X6),k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f260,f65])).

fof(f260,plain,(
    ! [X6] : m1_subset_1(k3_xboole_0(X6,sK3),k1_zfmisc_1(sK0)) ),
    inference(backward_demodulation,[],[f120,f119])).

fof(f119,plain,(
    ! [X6] : m1_subset_1(k9_subset_1(sK0,X6,sK3),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f55,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t16_subset_1.p',dt_k9_subset_1)).

fof(f120,plain,(
    ! [X7] : k9_subset_1(sK0,X7,sK3) = k3_xboole_0(X7,sK3) ),
    inference(resolution,[],[f55,f77])).

fof(f10444,plain,
    ( r1_tarski(sK1,k3_xboole_0(sK3,sK2))
    | ~ m1_subset_1(k3_xboole_0(sK3,sK2),k1_zfmisc_1(sK0)) ),
    inference(duplicate_literal_removal,[],[f10431])).

fof(f10431,plain,
    ( r1_tarski(sK1,k3_xboole_0(sK3,sK2))
    | ~ m1_subset_1(k3_xboole_0(sK3,sK2),k1_zfmisc_1(sK0))
    | r1_tarski(sK1,k3_xboole_0(sK3,sK2)) ),
    inference(resolution,[],[f4945,f428])).

fof(f428,plain,(
    ! [X0] :
      ( r2_hidden(sK5(sK0,sK1,X0),sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | r1_tarski(sK1,X0) ) ),
    inference(subsumption_resolution,[],[f420,f92])).

fof(f92,plain,(
    ! [X0] :
      ( m1_subset_1(sK5(sK0,sK1,X0),sK0)
      | r1_tarski(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f53,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | m1_subset_1(sK5(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ( ~ r2_hidden(sK5(X0,X1,X2),X2)
            & r2_hidden(sK5(X0,X1,X2),X1)
            & m1_subset_1(sK5(X0,X1,X2),X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f29,f44])).

fof(f44,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,X0) )
     => ( ~ r2_hidden(sK5(X0,X1,X2),X2)
        & r2_hidden(sK5(X0,X1,X2),X1)
        & m1_subset_1(sK5(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                 => r2_hidden(X3,X2) ) )
           => r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t16_subset_1.p',t7_subset_1)).

fof(f53,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f41])).

fof(f420,plain,(
    ! [X0] :
      ( r1_tarski(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | r2_hidden(sK5(sK0,sK1,X0),sK3)
      | ~ m1_subset_1(sK5(sK0,sK1,X0),sK0) ) ),
    inference(resolution,[],[f94,f57])).

fof(f57,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK1)
      | r2_hidden(X4,sK3)
      | ~ m1_subset_1(X4,sK0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f94,plain,(
    ! [X2] :
      ( r2_hidden(sK5(sK0,sK1,X2),sK1)
      | r1_tarski(sK1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f53,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | r2_hidden(sK5(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f4945,plain,(
    ! [X16] :
      ( ~ r2_hidden(sK5(sK0,sK1,k3_xboole_0(X16,sK2)),X16)
      | r1_tarski(sK1,k3_xboole_0(X16,sK2)) ) ),
    inference(subsumption_resolution,[],[f4933,f231])).

fof(f231,plain,(
    ! [X6] : m1_subset_1(k3_xboole_0(X6,sK2),k1_zfmisc_1(sK0)) ),
    inference(backward_demodulation,[],[f110,f109])).

fof(f109,plain,(
    ! [X6] : m1_subset_1(k9_subset_1(sK0,X6,sK2),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f54,f76])).

fof(f54,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f41])).

fof(f110,plain,(
    ! [X7] : k9_subset_1(sK0,X7,sK2) = k3_xboole_0(X7,sK2) ),
    inference(resolution,[],[f54,f77])).

fof(f4933,plain,(
    ! [X16] :
      ( ~ m1_subset_1(k3_xboole_0(X16,sK2),k1_zfmisc_1(sK0))
      | r1_tarski(sK1,k3_xboole_0(X16,sK2))
      | ~ r2_hidden(sK5(sK0,sK1,k3_xboole_0(X16,sK2)),X16) ) ),
    inference(duplicate_literal_removal,[],[f4918])).

fof(f4918,plain,(
    ! [X16] :
      ( ~ m1_subset_1(k3_xboole_0(X16,sK2),k1_zfmisc_1(sK0))
      | r1_tarski(sK1,k3_xboole_0(X16,sK2))
      | ~ r2_hidden(sK5(sK0,sK1,k3_xboole_0(X16,sK2)),X16)
      | ~ m1_subset_1(k3_xboole_0(X16,sK2),k1_zfmisc_1(sK0))
      | r1_tarski(sK1,k3_xboole_0(X16,sK2)) ) ),
    inference(resolution,[],[f467,f429])).

fof(f429,plain,(
    ! [X1] :
      ( r2_hidden(sK5(sK0,sK1,X1),sK2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(sK0))
      | r1_tarski(sK1,X1) ) ),
    inference(subsumption_resolution,[],[f421,f92])).

fof(f421,plain,(
    ! [X1] :
      ( r1_tarski(sK1,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(sK0))
      | r2_hidden(sK5(sK0,sK1,X1),sK2)
      | ~ m1_subset_1(sK5(sK0,sK1,X1),sK0) ) ),
    inference(resolution,[],[f94,f56])).

fof(f56,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK1)
      | r2_hidden(X4,sK2)
      | ~ m1_subset_1(X4,sK0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f467,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(sK5(sK0,sK1,k3_xboole_0(X4,X5)),X5)
      | ~ m1_subset_1(k3_xboole_0(X4,X5),k1_zfmisc_1(sK0))
      | r1_tarski(sK1,k3_xboole_0(X4,X5))
      | ~ r2_hidden(sK5(sK0,sK1,k3_xboole_0(X4,X5)),X4) ) ),
    inference(resolution,[],[f96,f87])).

fof(f87,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK6(X0,X1,X2),X1)
            | ~ r2_hidden(sK6(X0,X1,X2),X0)
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK6(X0,X1,X2),X1)
              & r2_hidden(sK6(X0,X1,X2),X0) )
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f50,f51])).

fof(f51,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK6(X0,X1,X2),X1)
          | ~ r2_hidden(sK6(X0,X1,X2),X0)
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK6(X0,X1,X2),X1)
            & r2_hidden(sK6(X0,X1,X2),X0) )
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t16_subset_1.p',d4_xboole_0)).

fof(f96,plain,(
    ! [X4] :
      ( ~ r2_hidden(sK5(sK0,sK1,X4),X4)
      | r1_tarski(sK1,X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f53,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r2_hidden(sK5(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f44974,plain,(
    r1_tarski(k3_xboole_0(sK2,sK3),sK1) ),
    inference(superposition,[],[f44904,f64])).

fof(f64,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t16_subset_1.p',idempotence_k3_xboole_0)).

fof(f44904,plain,(
    ! [X0] : r1_tarski(k3_xboole_0(sK2,k3_xboole_0(sK3,X0)),sK1) ),
    inference(forward_demodulation,[],[f44903,f65])).

fof(f44903,plain,(
    ! [X0] : r1_tarski(k3_xboole_0(k3_xboole_0(sK3,X0),sK2),sK1) ),
    inference(subsumption_resolution,[],[f44902,f53])).

fof(f44902,plain,(
    ! [X0] :
      ( r1_tarski(k3_xboole_0(k3_xboole_0(sK3,X0),sK2),sK1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f44901,f231])).

fof(f44901,plain,(
    ! [X0] :
      ( r1_tarski(k3_xboole_0(k3_xboole_0(sK3,X0),sK2),sK1)
      | ~ m1_subset_1(k3_xboole_0(k3_xboole_0(sK3,X0),sK2),k1_zfmisc_1(sK0))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    inference(duplicate_literal_removal,[],[f44859])).

fof(f44859,plain,(
    ! [X0] :
      ( r1_tarski(k3_xboole_0(k3_xboole_0(sK3,X0),sK2),sK1)
      | ~ m1_subset_1(k3_xboole_0(k3_xboole_0(sK3,X0),sK2),k1_zfmisc_1(sK0))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
      | r1_tarski(k3_xboole_0(k3_xboole_0(sK3,X0),sK2),sK1) ) ),
    inference(resolution,[],[f2058,f2554])).

fof(f2554,plain,(
    ! [X6,X5] :
      ( r2_hidden(sK5(sK0,k3_xboole_0(X5,sK2),X6),sK2)
      | ~ m1_subset_1(X6,k1_zfmisc_1(sK0))
      | r1_tarski(k3_xboole_0(X5,sK2),X6) ) ),
    inference(resolution,[],[f246,f88])).

fof(f88,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f246,plain,(
    ! [X4,X5] :
      ( r2_hidden(sK5(sK0,k3_xboole_0(X4,sK2),X5),k3_xboole_0(X4,sK2))
      | r1_tarski(k3_xboole_0(X4,sK2),X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f231,f68])).

fof(f2058,plain,(
    ! [X8,X7] :
      ( ~ r2_hidden(sK5(sK0,k3_xboole_0(k3_xboole_0(sK3,X7),X8),sK1),sK2)
      | r1_tarski(k3_xboole_0(k3_xboole_0(sK3,X7),X8),sK1)
      | ~ m1_subset_1(k3_xboole_0(k3_xboole_0(sK3,X7),X8),k1_zfmisc_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f2057,f97])).

fof(f97,plain,(
    ! [X5] :
      ( ~ r2_hidden(sK5(sK0,X5,sK1),sK1)
      | r1_tarski(X5,sK1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f53,f69])).

fof(f2057,plain,(
    ! [X8,X7] :
      ( r2_hidden(sK5(sK0,k3_xboole_0(k3_xboole_0(sK3,X7),X8),sK1),sK1)
      | ~ r2_hidden(sK5(sK0,k3_xboole_0(k3_xboole_0(sK3,X7),X8),sK1),sK2)
      | r1_tarski(k3_xboole_0(k3_xboole_0(sK3,X7),X8),sK1)
      | ~ m1_subset_1(k3_xboole_0(k3_xboole_0(sK3,X7),X8),k1_zfmisc_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f2031,f93])).

fof(f93,plain,(
    ! [X1] :
      ( m1_subset_1(sK5(sK0,X1,sK1),sK0)
      | r1_tarski(X1,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f53,f67])).

fof(f2031,plain,(
    ! [X8,X7] :
      ( ~ m1_subset_1(sK5(sK0,k3_xboole_0(k3_xboole_0(sK3,X7),X8),sK1),sK0)
      | r2_hidden(sK5(sK0,k3_xboole_0(k3_xboole_0(sK3,X7),X8),sK1),sK1)
      | ~ r2_hidden(sK5(sK0,k3_xboole_0(k3_xboole_0(sK3,X7),X8),sK1),sK2)
      | r1_tarski(k3_xboole_0(k3_xboole_0(sK3,X7),X8),sK1)
      | ~ m1_subset_1(k3_xboole_0(k3_xboole_0(sK3,X7),X8),k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f616,f95])).

fof(f95,plain,(
    ! [X3] :
      ( r2_hidden(sK5(sK0,X3,sK1),X3)
      | r1_tarski(X3,sK1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f53,f68])).

fof(f616,plain,(
    ! [X14,X15,X16] :
      ( ~ r2_hidden(X14,k3_xboole_0(k3_xboole_0(sK3,X15),X16))
      | ~ m1_subset_1(X14,sK0)
      | r2_hidden(X14,sK1)
      | ~ r2_hidden(X14,sK2) ) ),
    inference(resolution,[],[f145,f89])).

fof(f89,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f145,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X6,k3_xboole_0(sK3,X7))
      | ~ r2_hidden(X6,sK2)
      | ~ m1_subset_1(X6,sK0)
      | r2_hidden(X6,sK1) ) ),
    inference(resolution,[],[f58,f89])).

fof(f58,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK3)
      | r2_hidden(X4,sK1)
      | ~ r2_hidden(X4,sK2)
      | ~ m1_subset_1(X4,sK0) ) ),
    inference(cnf_transformation,[],[f41])).
%------------------------------------------------------------------------------
