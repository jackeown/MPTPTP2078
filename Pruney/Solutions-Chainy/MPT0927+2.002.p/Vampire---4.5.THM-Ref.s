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
% DateTime   : Thu Dec  3 12:59:51 EST 2020

% Result     : Theorem 1.31s
% Output     : Refutation 1.31s
% Verified   : 
% Statistics : Number of formulae       :  161 ( 627 expanded)
%              Number of leaves         :   31 ( 240 expanded)
%              Depth                    :   16
%              Number of atoms          :  531 (3393 expanded)
%              Number of equality atoms :  105 ( 272 expanded)
%              Maximal formula depth    :   20 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f329,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f90,f145,f150,f155,f160,f231,f274,f295,f316,f319,f322,f325,f328])).

fof(f328,plain,
    ( spl12_1
    | ~ spl12_9 ),
    inference(avatar_contradiction_clause,[],[f327])).

fof(f327,plain,
    ( $false
    | spl12_1
    | ~ spl12_9 ),
    inference(subsumption_resolution,[],[f326,f220])).

fof(f220,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK4) ),
    inference(resolution,[],[f202,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f202,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1(sK8)),k2_zfmisc_1(sK4,sK5)) ),
    inference(resolution,[],[f115,f58])).

fof(f115,plain,(
    r2_hidden(k1_mcart_1(sK8),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
    inference(resolution,[],[f66,f58])).

fof(f66,plain,(
    r2_hidden(sK8,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) ),
    inference(definition_unfolding,[],[f43,f65])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f60,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f60,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f43,plain,(
    r2_hidden(sK8,k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ( ~ r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7)
      | ~ r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6)
      | ~ r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5)
      | ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4) )
    & r2_hidden(sK8,k4_zfmisc_1(sK4,sK5,sK6,sK7))
    & m1_subset_1(sK8,k4_zfmisc_1(sK0,sK1,sK2,sK3))
    & m1_subset_1(sK7,k1_zfmisc_1(sK3))
    & m1_subset_1(sK6,k1_zfmisc_1(sK2))
    & m1_subset_1(sK5,k1_zfmisc_1(sK1))
    & m1_subset_1(sK4,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f14,f24,f23,f22,f21,f20])).

fof(f20,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( ? [X5] :
            ( ? [X6] :
                ( ? [X7] :
                    ( ? [X8] :
                        ( ( ~ r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7)
                          | ~ r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6)
                          | ~ r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5)
                          | ~ r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4) )
                        & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7))
                        & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) )
                    & m1_subset_1(X7,k1_zfmisc_1(X3)) )
                & m1_subset_1(X6,k1_zfmisc_1(X2)) )
            & m1_subset_1(X5,k1_zfmisc_1(X1)) )
        & m1_subset_1(X4,k1_zfmisc_1(X0)) )
   => ( ? [X5] :
          ( ? [X6] :
              ( ? [X7] :
                  ( ? [X8] :
                      ( ( ~ r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),X7)
                        | ~ r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),X6)
                        | ~ r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),X5)
                        | ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4) )
                      & r2_hidden(X8,k4_zfmisc_1(sK4,X5,X6,X7))
                      & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3)) )
                  & m1_subset_1(X7,k1_zfmisc_1(sK3)) )
              & m1_subset_1(X6,k1_zfmisc_1(sK2)) )
          & m1_subset_1(X5,k1_zfmisc_1(sK1)) )
      & m1_subset_1(sK4,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X5] :
        ( ? [X6] :
            ( ? [X7] :
                ( ? [X8] :
                    ( ( ~ r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),X7)
                      | ~ r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),X6)
                      | ~ r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),X5)
                      | ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4) )
                    & r2_hidden(X8,k4_zfmisc_1(sK4,X5,X6,X7))
                    & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3)) )
                & m1_subset_1(X7,k1_zfmisc_1(sK3)) )
            & m1_subset_1(X6,k1_zfmisc_1(sK2)) )
        & m1_subset_1(X5,k1_zfmisc_1(sK1)) )
   => ( ? [X6] :
          ( ? [X7] :
              ( ? [X8] :
                  ( ( ~ r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),X7)
                    | ~ r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),X6)
                    | ~ r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),sK5)
                    | ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4) )
                  & r2_hidden(X8,k4_zfmisc_1(sK4,sK5,X6,X7))
                  & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3)) )
              & m1_subset_1(X7,k1_zfmisc_1(sK3)) )
          & m1_subset_1(X6,k1_zfmisc_1(sK2)) )
      & m1_subset_1(sK5,k1_zfmisc_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X6] :
        ( ? [X7] :
            ( ? [X8] :
                ( ( ~ r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),X7)
                  | ~ r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),X6)
                  | ~ r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),sK5)
                  | ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4) )
                & r2_hidden(X8,k4_zfmisc_1(sK4,sK5,X6,X7))
                & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3)) )
            & m1_subset_1(X7,k1_zfmisc_1(sK3)) )
        & m1_subset_1(X6,k1_zfmisc_1(sK2)) )
   => ( ? [X7] :
          ( ? [X8] :
              ( ( ~ r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),X7)
                | ~ r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),sK6)
                | ~ r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),sK5)
                | ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4) )
              & r2_hidden(X8,k4_zfmisc_1(sK4,sK5,sK6,X7))
              & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3)) )
          & m1_subset_1(X7,k1_zfmisc_1(sK3)) )
      & m1_subset_1(sK6,k1_zfmisc_1(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X7] :
        ( ? [X8] :
            ( ( ~ r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),X7)
              | ~ r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),sK6)
              | ~ r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),sK5)
              | ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4) )
            & r2_hidden(X8,k4_zfmisc_1(sK4,sK5,sK6,X7))
            & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3)) )
        & m1_subset_1(X7,k1_zfmisc_1(sK3)) )
   => ( ? [X8] :
          ( ( ~ r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),sK7)
            | ~ r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),sK6)
            | ~ r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),sK5)
            | ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4) )
          & r2_hidden(X8,k4_zfmisc_1(sK4,sK5,sK6,sK7))
          & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3)) )
      & m1_subset_1(sK7,k1_zfmisc_1(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X8] :
        ( ( ~ r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),sK7)
          | ~ r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),sK6)
          | ~ r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),sK5)
          | ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4) )
        & r2_hidden(X8,k4_zfmisc_1(sK4,sK5,sK6,sK7))
        & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3)) )
   => ( ( ~ r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7)
        | ~ r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6)
        | ~ r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5)
        | ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4) )
      & r2_hidden(sK8,k4_zfmisc_1(sK4,sK5,sK6,sK7))
      & m1_subset_1(sK8,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ? [X5] :
          ( ? [X6] :
              ( ? [X7] :
                  ( ? [X8] :
                      ( ( ~ r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7)
                        | ~ r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6)
                        | ~ r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5)
                        | ~ r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4) )
                      & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7))
                      & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) )
                  & m1_subset_1(X7,k1_zfmisc_1(X3)) )
              & m1_subset_1(X6,k1_zfmisc_1(X2)) )
          & m1_subset_1(X5,k1_zfmisc_1(X1)) )
      & m1_subset_1(X4,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ? [X5] :
          ( ? [X6] :
              ( ? [X7] :
                  ( ? [X8] :
                      ( ( ~ r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7)
                        | ~ r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6)
                        | ~ r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5)
                        | ~ r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4) )
                      & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7))
                      & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) )
                  & m1_subset_1(X7,k1_zfmisc_1(X3)) )
              & m1_subset_1(X6,k1_zfmisc_1(X2)) )
          & m1_subset_1(X5,k1_zfmisc_1(X1)) )
      & m1_subset_1(X4,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( m1_subset_1(X4,k1_zfmisc_1(X0))
       => ! [X5] :
            ( m1_subset_1(X5,k1_zfmisc_1(X1))
           => ! [X6] :
                ( m1_subset_1(X6,k1_zfmisc_1(X2))
               => ! [X7] :
                    ( m1_subset_1(X7,k1_zfmisc_1(X3))
                   => ! [X8] :
                        ( m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))
                       => ( r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7))
                         => ( r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7)
                            & r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6)
                            & r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5)
                            & r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(X0))
     => ! [X5] :
          ( m1_subset_1(X5,k1_zfmisc_1(X1))
         => ! [X6] :
              ( m1_subset_1(X6,k1_zfmisc_1(X2))
             => ! [X7] :
                  ( m1_subset_1(X7,k1_zfmisc_1(X3))
                 => ! [X8] :
                      ( m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))
                     => ( r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7))
                       => ( r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7)
                          & r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6)
                          & r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5)
                          & r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_mcart_1)).

fof(f326,plain,
    ( ~ r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK4)
    | spl12_1
    | ~ spl12_9 ),
    inference(backward_demodulation,[],[f77,f144])).

fof(f144,plain,
    ( k8_mcart_1(sK0,sK1,sK2,sK3,sK8) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | ~ spl12_9 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl12_9
  <=> k8_mcart_1(sK0,sK1,sK2,sK3,sK8) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_9])])).

fof(f77,plain,
    ( ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4)
    | spl12_1 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl12_1
  <=> r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).

fof(f325,plain,
    ( spl12_2
    | ~ spl12_10 ),
    inference(avatar_contradiction_clause,[],[f324])).

fof(f324,plain,
    ( $false
    | spl12_2
    | ~ spl12_10 ),
    inference(subsumption_resolution,[],[f323,f221])).

fof(f221,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK5) ),
    inference(resolution,[],[f202,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k2_mcart_1(X0),X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f323,plain,
    ( ~ r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK5)
    | spl12_2
    | ~ spl12_10 ),
    inference(backward_demodulation,[],[f81,f149])).

fof(f149,plain,
    ( k9_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | ~ spl12_10 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl12_10
  <=> k9_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_10])])).

fof(f81,plain,
    ( ~ r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5)
    | spl12_2 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl12_2
  <=> r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).

fof(f322,plain,
    ( spl12_3
    | ~ spl12_11 ),
    inference(avatar_contradiction_clause,[],[f321])).

fof(f321,plain,
    ( $false
    | spl12_3
    | ~ spl12_11 ),
    inference(subsumption_resolution,[],[f320,f203])).

fof(f203,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),sK6) ),
    inference(resolution,[],[f115,f59])).

fof(f320,plain,
    ( ~ r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),sK6)
    | spl12_3
    | ~ spl12_11 ),
    inference(backward_demodulation,[],[f85,f154])).

fof(f154,plain,
    ( k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(sK8))
    | ~ spl12_11 ),
    inference(avatar_component_clause,[],[f152])).

fof(f152,plain,
    ( spl12_11
  <=> k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_11])])).

fof(f85,plain,
    ( ~ r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6)
    | spl12_3 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl12_3
  <=> r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).

fof(f319,plain,
    ( spl12_4
    | ~ spl12_12 ),
    inference(avatar_contradiction_clause,[],[f318])).

fof(f318,plain,
    ( $false
    | spl12_4
    | ~ spl12_12 ),
    inference(subsumption_resolution,[],[f317,f116])).

fof(f116,plain,(
    r2_hidden(k2_mcart_1(sK8),sK7) ),
    inference(resolution,[],[f66,f59])).

fof(f317,plain,
    ( ~ r2_hidden(k2_mcart_1(sK8),sK7)
    | spl12_4
    | ~ spl12_12 ),
    inference(backward_demodulation,[],[f89,f159])).

fof(f159,plain,
    ( k11_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(sK8)
    | ~ spl12_12 ),
    inference(avatar_component_clause,[],[f157])).

fof(f157,plain,
    ( spl12_12
  <=> k11_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_12])])).

fof(f89,plain,
    ( ~ r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7)
    | spl12_4 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl12_4
  <=> r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).

fof(f316,plain,(
    ~ spl12_8 ),
    inference(avatar_contradiction_clause,[],[f315])).

fof(f315,plain,
    ( $false
    | ~ spl12_8 ),
    inference(subsumption_resolution,[],[f313,f45])).

fof(f45,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f313,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl12_8 ),
    inference(backward_demodulation,[],[f193,f140])).

fof(f140,plain,
    ( k1_xboole_0 = sK3
    | ~ spl12_8 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl12_8
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_8])])).

fof(f193,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(resolution,[],[f191,f47])).

fof(f47,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK9(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f27,f28])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK9(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
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

fof(f191,plain,(
    r2_hidden(k2_mcart_1(sK8),sK3) ),
    inference(resolution,[],[f114,f116])).

fof(f114,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK7)
      | r2_hidden(X0,sK3) ) ),
    inference(resolution,[],[f111,f50])).

fof(f50,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK10(X0,X1),X1)
          & r2_hidden(sK10(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f31,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK10(X0,X1),X1)
        & r2_hidden(sK10(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f111,plain,(
    r1_tarski(sK7,sK3) ),
    inference(resolution,[],[f98,f73])).

fof(f73,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
      | r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK11(X0,X1),X0)
            | ~ r2_hidden(sK11(X0,X1),X1) )
          & ( r1_tarski(sK11(X0,X1),X0)
            | r2_hidden(sK11(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f35,f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK11(X0,X1),X0)
          | ~ r2_hidden(sK11(X0,X1),X1) )
        & ( r1_tarski(sK11(X0,X1),X0)
          | r2_hidden(sK11(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f98,plain,(
    r2_hidden(sK7,k1_zfmisc_1(sK3)) ),
    inference(subsumption_resolution,[],[f97,f46])).

fof(f46,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f97,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK3))
    | r2_hidden(sK7,k1_zfmisc_1(sK3)) ),
    inference(resolution,[],[f41,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f41,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f25])).

fof(f295,plain,(
    ~ spl12_7 ),
    inference(avatar_contradiction_clause,[],[f294])).

fof(f294,plain,
    ( $false
    | ~ spl12_7 ),
    inference(subsumption_resolution,[],[f292,f45])).

fof(f292,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl12_7 ),
    inference(backward_demodulation,[],[f211,f136])).

fof(f136,plain,
    ( k1_xboole_0 = sK2
    | ~ spl12_7 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl12_7
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_7])])).

fof(f211,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(resolution,[],[f209,f47])).

fof(f209,plain,(
    r2_hidden(sK9(sK6),sK2) ),
    inference(resolution,[],[f207,f110])).

fof(f110,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK6)
      | r2_hidden(X0,sK2) ) ),
    inference(resolution,[],[f107,f50])).

fof(f107,plain,(
    r1_tarski(sK6,sK2) ),
    inference(resolution,[],[f96,f73])).

fof(f96,plain,(
    r2_hidden(sK6,k1_zfmisc_1(sK2)) ),
    inference(subsumption_resolution,[],[f95,f46])).

fof(f95,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK2))
    | r2_hidden(sK6,k1_zfmisc_1(sK2)) ),
    inference(resolution,[],[f40,f49])).

fof(f40,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f25])).

fof(f207,plain,(
    r2_hidden(sK9(sK6),sK6) ),
    inference(resolution,[],[f206,f48])).

fof(f48,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK9(X0),X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f206,plain,(
    ~ v1_xboole_0(sK6) ),
    inference(resolution,[],[f203,f47])).

fof(f274,plain,(
    ~ spl12_6 ),
    inference(avatar_contradiction_clause,[],[f273])).

fof(f273,plain,
    ( $false
    | ~ spl12_6 ),
    inference(subsumption_resolution,[],[f272,f45])).

fof(f272,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl12_6 ),
    inference(resolution,[],[f271,f47])).

fof(f271,plain,
    ( r2_hidden(sK9(sK5),k1_xboole_0)
    | ~ spl12_6 ),
    inference(resolution,[],[f240,f263])).

fof(f263,plain,(
    r2_hidden(sK9(sK5),sK5) ),
    inference(resolution,[],[f262,f48])).

fof(f262,plain,(
    ~ v1_xboole_0(sK5) ),
    inference(resolution,[],[f221,f47])).

fof(f240,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK5)
        | r2_hidden(X0,k1_xboole_0) )
    | ~ spl12_6 ),
    inference(backward_demodulation,[],[f106,f132])).

fof(f132,plain,
    ( k1_xboole_0 = sK1
    | ~ spl12_6 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl12_6
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_6])])).

fof(f106,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK5)
      | r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f103,f50])).

fof(f103,plain,(
    r1_tarski(sK5,sK1) ),
    inference(resolution,[],[f94,f73])).

fof(f94,plain,(
    r2_hidden(sK5,k1_zfmisc_1(sK1)) ),
    inference(subsumption_resolution,[],[f93,f46])).

fof(f93,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK1))
    | r2_hidden(sK5,k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f39,f49])).

fof(f39,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f231,plain,(
    ~ spl12_5 ),
    inference(avatar_contradiction_clause,[],[f230])).

fof(f230,plain,
    ( $false
    | ~ spl12_5 ),
    inference(subsumption_resolution,[],[f229,f45])).

fof(f229,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl12_5 ),
    inference(resolution,[],[f227,f47])).

fof(f227,plain,
    ( r2_hidden(sK9(sK4),k1_xboole_0)
    | ~ spl12_5 ),
    inference(resolution,[],[f226,f178])).

fof(f178,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK4)
        | r2_hidden(X0,k1_xboole_0) )
    | ~ spl12_5 ),
    inference(backward_demodulation,[],[f102,f128])).

fof(f128,plain,
    ( k1_xboole_0 = sK0
    | ~ spl12_5 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl12_5
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_5])])).

fof(f102,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK4)
      | r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f99,f50])).

fof(f99,plain,(
    r1_tarski(sK4,sK0) ),
    inference(resolution,[],[f92,f73])).

fof(f92,plain,(
    r2_hidden(sK4,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f91,f46])).

fof(f91,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | r2_hidden(sK4,k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f38,f49])).

fof(f38,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f226,plain,(
    r2_hidden(sK9(sK4),sK4) ),
    inference(resolution,[],[f225,f48])).

fof(f225,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(resolution,[],[f220,f47])).

fof(f160,plain,
    ( spl12_5
    | spl12_6
    | spl12_7
    | spl12_8
    | spl12_12 ),
    inference(avatar_split_clause,[],[f123,f157,f138,f134,f130,f126])).

fof(f123,plain,
    ( k11_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(sK8)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f67,f68])).

fof(f68,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f64,f65])).

fof(f64,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)
            & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
            & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
            & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ~ ! [X4] :
              ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
             => ( k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)
                & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
                & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
                & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) ) )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_mcart_1)).

fof(f67,plain,(
    m1_subset_1(sK8,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) ),
    inference(definition_unfolding,[],[f42,f65])).

fof(f42,plain,(
    m1_subset_1(sK8,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f25])).

fof(f155,plain,
    ( spl12_5
    | spl12_6
    | spl12_7
    | spl12_8
    | spl12_11 ),
    inference(avatar_split_clause,[],[f122,f152,f138,f134,f130,f126])).

fof(f122,plain,
    ( k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(sK8))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f67,f69])).

fof(f69,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f63,f65])).

fof(f63,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f150,plain,
    ( spl12_5
    | spl12_6
    | spl12_7
    | spl12_8
    | spl12_10 ),
    inference(avatar_split_clause,[],[f121,f147,f138,f134,f130,f126])).

fof(f121,plain,
    ( k9_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f67,f70])).

fof(f70,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f62,f65])).

fof(f62,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f145,plain,
    ( spl12_5
    | spl12_6
    | spl12_7
    | spl12_8
    | spl12_9 ),
    inference(avatar_split_clause,[],[f120,f142,f138,f134,f130,f126])).

fof(f120,plain,
    ( k8_mcart_1(sK0,sK1,sK2,sK3,sK8) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f67,f71])).

fof(f71,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f61,f65])).

fof(f61,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f90,plain,
    ( ~ spl12_1
    | ~ spl12_2
    | ~ spl12_3
    | ~ spl12_4 ),
    inference(avatar_split_clause,[],[f44,f87,f83,f79,f75])).

fof(f44,plain,
    ( ~ r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7)
    | ~ r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6)
    | ~ r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5)
    | ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.36  % Computer   : n023.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 13:41:06 EST 2020
% 0.15/0.36  % CPUTime    : 
% 1.07/0.54  % (5828)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.07/0.55  % (5826)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.31/0.55  % (5837)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.31/0.55  % (5828)Refutation not found, incomplete strategy% (5828)------------------------------
% 1.31/0.55  % (5828)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.55  % (5828)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.55  
% 1.31/0.55  % (5828)Memory used [KB]: 10746
% 1.31/0.55  % (5828)Time elapsed: 0.122 s
% 1.31/0.55  % (5828)------------------------------
% 1.31/0.55  % (5828)------------------------------
% 1.31/0.56  % (5845)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.31/0.56  % (5842)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.31/0.56  % (5847)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.31/0.56  % (5826)Refutation found. Thanks to Tanya!
% 1.31/0.56  % SZS status Theorem for theBenchmark
% 1.31/0.56  % SZS output start Proof for theBenchmark
% 1.31/0.56  fof(f329,plain,(
% 1.31/0.56    $false),
% 1.31/0.56    inference(avatar_sat_refutation,[],[f90,f145,f150,f155,f160,f231,f274,f295,f316,f319,f322,f325,f328])).
% 1.31/0.56  fof(f328,plain,(
% 1.31/0.56    spl12_1 | ~spl12_9),
% 1.31/0.56    inference(avatar_contradiction_clause,[],[f327])).
% 1.31/0.56  fof(f327,plain,(
% 1.31/0.56    $false | (spl12_1 | ~spl12_9)),
% 1.31/0.56    inference(subsumption_resolution,[],[f326,f220])).
% 1.31/0.56  fof(f220,plain,(
% 1.31/0.56    r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK4)),
% 1.31/0.56    inference(resolution,[],[f202,f58])).
% 1.31/0.56  fof(f58,plain,(
% 1.31/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 1.31/0.56    inference(cnf_transformation,[],[f18])).
% 1.31/0.56  fof(f18,plain,(
% 1.31/0.56    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 1.31/0.56    inference(ennf_transformation,[],[f9])).
% 1.31/0.56  fof(f9,axiom,(
% 1.31/0.56    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 1.31/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).
% 1.31/0.56  fof(f202,plain,(
% 1.31/0.56    r2_hidden(k1_mcart_1(k1_mcart_1(sK8)),k2_zfmisc_1(sK4,sK5))),
% 1.31/0.56    inference(resolution,[],[f115,f58])).
% 1.31/0.56  fof(f115,plain,(
% 1.31/0.56    r2_hidden(k1_mcart_1(sK8),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))),
% 1.31/0.56    inference(resolution,[],[f66,f58])).
% 1.31/0.56  fof(f66,plain,(
% 1.31/0.56    r2_hidden(sK8,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7))),
% 1.31/0.56    inference(definition_unfolding,[],[f43,f65])).
% 1.31/0.56  fof(f65,plain,(
% 1.31/0.56    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 1.31/0.56    inference(definition_unfolding,[],[f60,f57])).
% 1.31/0.56  fof(f57,plain,(
% 1.31/0.56    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 1.31/0.56    inference(cnf_transformation,[],[f7])).
% 1.31/0.56  fof(f7,axiom,(
% 1.31/0.56    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 1.31/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 1.31/0.56  fof(f60,plain,(
% 1.31/0.56    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 1.31/0.56    inference(cnf_transformation,[],[f8])).
% 1.31/0.56  fof(f8,axiom,(
% 1.31/0.56    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 1.31/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 1.31/0.56  fof(f43,plain,(
% 1.31/0.56    r2_hidden(sK8,k4_zfmisc_1(sK4,sK5,sK6,sK7))),
% 1.31/0.56    inference(cnf_transformation,[],[f25])).
% 1.31/0.56  fof(f25,plain,(
% 1.31/0.56    (((((~r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7) | ~r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6) | ~r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5) | ~r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4)) & r2_hidden(sK8,k4_zfmisc_1(sK4,sK5,sK6,sK7)) & m1_subset_1(sK8,k4_zfmisc_1(sK0,sK1,sK2,sK3))) & m1_subset_1(sK7,k1_zfmisc_1(sK3))) & m1_subset_1(sK6,k1_zfmisc_1(sK2))) & m1_subset_1(sK5,k1_zfmisc_1(sK1))) & m1_subset_1(sK4,k1_zfmisc_1(sK0))),
% 1.31/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f14,f24,f23,f22,f21,f20])).
% 1.31/0.56  fof(f20,plain,(
% 1.31/0.56    ? [X0,X1,X2,X3,X4] : (? [X5] : (? [X6] : (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) | ~r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) | ~r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) | ~r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4)) & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7)) & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))) & m1_subset_1(X7,k1_zfmisc_1(X3))) & m1_subset_1(X6,k1_zfmisc_1(X2))) & m1_subset_1(X5,k1_zfmisc_1(X1))) & m1_subset_1(X4,k1_zfmisc_1(X0))) => (? [X5] : (? [X6] : (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),X7) | ~r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),X6) | ~r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),X5) | ~r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4)) & r2_hidden(X8,k4_zfmisc_1(sK4,X5,X6,X7)) & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3))) & m1_subset_1(X7,k1_zfmisc_1(sK3))) & m1_subset_1(X6,k1_zfmisc_1(sK2))) & m1_subset_1(X5,k1_zfmisc_1(sK1))) & m1_subset_1(sK4,k1_zfmisc_1(sK0)))),
% 1.31/0.56    introduced(choice_axiom,[])).
% 1.31/0.56  fof(f21,plain,(
% 1.31/0.56    ? [X5] : (? [X6] : (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),X7) | ~r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),X6) | ~r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),X5) | ~r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4)) & r2_hidden(X8,k4_zfmisc_1(sK4,X5,X6,X7)) & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3))) & m1_subset_1(X7,k1_zfmisc_1(sK3))) & m1_subset_1(X6,k1_zfmisc_1(sK2))) & m1_subset_1(X5,k1_zfmisc_1(sK1))) => (? [X6] : (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),X7) | ~r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),X6) | ~r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),sK5) | ~r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4)) & r2_hidden(X8,k4_zfmisc_1(sK4,sK5,X6,X7)) & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3))) & m1_subset_1(X7,k1_zfmisc_1(sK3))) & m1_subset_1(X6,k1_zfmisc_1(sK2))) & m1_subset_1(sK5,k1_zfmisc_1(sK1)))),
% 1.31/0.56    introduced(choice_axiom,[])).
% 1.31/0.56  fof(f22,plain,(
% 1.31/0.56    ? [X6] : (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),X7) | ~r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),X6) | ~r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),sK5) | ~r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4)) & r2_hidden(X8,k4_zfmisc_1(sK4,sK5,X6,X7)) & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3))) & m1_subset_1(X7,k1_zfmisc_1(sK3))) & m1_subset_1(X6,k1_zfmisc_1(sK2))) => (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),X7) | ~r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),sK6) | ~r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),sK5) | ~r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4)) & r2_hidden(X8,k4_zfmisc_1(sK4,sK5,sK6,X7)) & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3))) & m1_subset_1(X7,k1_zfmisc_1(sK3))) & m1_subset_1(sK6,k1_zfmisc_1(sK2)))),
% 1.31/0.56    introduced(choice_axiom,[])).
% 1.31/0.56  fof(f23,plain,(
% 1.31/0.56    ? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),X7) | ~r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),sK6) | ~r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),sK5) | ~r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4)) & r2_hidden(X8,k4_zfmisc_1(sK4,sK5,sK6,X7)) & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3))) & m1_subset_1(X7,k1_zfmisc_1(sK3))) => (? [X8] : ((~r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),sK7) | ~r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),sK6) | ~r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),sK5) | ~r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4)) & r2_hidden(X8,k4_zfmisc_1(sK4,sK5,sK6,sK7)) & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3))) & m1_subset_1(sK7,k1_zfmisc_1(sK3)))),
% 1.31/0.56    introduced(choice_axiom,[])).
% 1.31/0.56  fof(f24,plain,(
% 1.31/0.56    ? [X8] : ((~r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),sK7) | ~r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),sK6) | ~r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),sK5) | ~r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4)) & r2_hidden(X8,k4_zfmisc_1(sK4,sK5,sK6,sK7)) & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3))) => ((~r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7) | ~r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6) | ~r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5) | ~r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4)) & r2_hidden(sK8,k4_zfmisc_1(sK4,sK5,sK6,sK7)) & m1_subset_1(sK8,k4_zfmisc_1(sK0,sK1,sK2,sK3)))),
% 1.31/0.56    introduced(choice_axiom,[])).
% 1.31/0.56  fof(f14,plain,(
% 1.31/0.56    ? [X0,X1,X2,X3,X4] : (? [X5] : (? [X6] : (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) | ~r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) | ~r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) | ~r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4)) & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7)) & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))) & m1_subset_1(X7,k1_zfmisc_1(X3))) & m1_subset_1(X6,k1_zfmisc_1(X2))) & m1_subset_1(X5,k1_zfmisc_1(X1))) & m1_subset_1(X4,k1_zfmisc_1(X0)))),
% 1.31/0.56    inference(flattening,[],[f13])).
% 1.31/0.56  fof(f13,plain,(
% 1.31/0.56    ? [X0,X1,X2,X3,X4] : (? [X5] : (? [X6] : (? [X7] : (? [X8] : (((~r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) | ~r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) | ~r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) | ~r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4)) & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7))) & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))) & m1_subset_1(X7,k1_zfmisc_1(X3))) & m1_subset_1(X6,k1_zfmisc_1(X2))) & m1_subset_1(X5,k1_zfmisc_1(X1))) & m1_subset_1(X4,k1_zfmisc_1(X0)))),
% 1.31/0.56    inference(ennf_transformation,[],[f12])).
% 1.31/0.56  fof(f12,negated_conjecture,(
% 1.31/0.56    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k1_zfmisc_1(X0)) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(X1)) => ! [X6] : (m1_subset_1(X6,k1_zfmisc_1(X2)) => ! [X7] : (m1_subset_1(X7,k1_zfmisc_1(X3)) => ! [X8] : (m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) => (r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7)) => (r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) & r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) & r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) & r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4))))))))),
% 1.31/0.56    inference(negated_conjecture,[],[f11])).
% 1.31/0.56  fof(f11,conjecture,(
% 1.31/0.56    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k1_zfmisc_1(X0)) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(X1)) => ! [X6] : (m1_subset_1(X6,k1_zfmisc_1(X2)) => ! [X7] : (m1_subset_1(X7,k1_zfmisc_1(X3)) => ! [X8] : (m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) => (r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7)) => (r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) & r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) & r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) & r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4))))))))),
% 1.31/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_mcart_1)).
% 1.31/0.56  fof(f326,plain,(
% 1.31/0.56    ~r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK4) | (spl12_1 | ~spl12_9)),
% 1.31/0.56    inference(backward_demodulation,[],[f77,f144])).
% 1.31/0.56  fof(f144,plain,(
% 1.31/0.56    k8_mcart_1(sK0,sK1,sK2,sK3,sK8) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) | ~spl12_9),
% 1.31/0.56    inference(avatar_component_clause,[],[f142])).
% 1.31/0.56  fof(f142,plain,(
% 1.31/0.56    spl12_9 <=> k8_mcart_1(sK0,sK1,sK2,sK3,sK8) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))),
% 1.31/0.56    introduced(avatar_definition,[new_symbols(naming,[spl12_9])])).
% 1.31/0.56  fof(f77,plain,(
% 1.31/0.56    ~r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4) | spl12_1),
% 1.31/0.56    inference(avatar_component_clause,[],[f75])).
% 1.31/0.56  fof(f75,plain,(
% 1.31/0.56    spl12_1 <=> r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4)),
% 1.31/0.56    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).
% 1.31/0.56  fof(f325,plain,(
% 1.31/0.56    spl12_2 | ~spl12_10),
% 1.31/0.56    inference(avatar_contradiction_clause,[],[f324])).
% 1.31/0.56  fof(f324,plain,(
% 1.31/0.56    $false | (spl12_2 | ~spl12_10)),
% 1.31/0.56    inference(subsumption_resolution,[],[f323,f221])).
% 1.31/0.56  fof(f221,plain,(
% 1.31/0.56    r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK5)),
% 1.31/0.56    inference(resolution,[],[f202,f59])).
% 1.31/0.56  fof(f59,plain,(
% 1.31/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2)) )),
% 1.31/0.56    inference(cnf_transformation,[],[f18])).
% 1.31/0.56  fof(f323,plain,(
% 1.31/0.56    ~r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK5) | (spl12_2 | ~spl12_10)),
% 1.31/0.56    inference(backward_demodulation,[],[f81,f149])).
% 1.31/0.56  fof(f149,plain,(
% 1.31/0.56    k9_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) | ~spl12_10),
% 1.31/0.56    inference(avatar_component_clause,[],[f147])).
% 1.31/0.56  fof(f147,plain,(
% 1.31/0.56    spl12_10 <=> k9_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))),
% 1.31/0.56    introduced(avatar_definition,[new_symbols(naming,[spl12_10])])).
% 1.31/0.56  fof(f81,plain,(
% 1.31/0.56    ~r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5) | spl12_2),
% 1.31/0.56    inference(avatar_component_clause,[],[f79])).
% 1.31/0.56  fof(f79,plain,(
% 1.31/0.56    spl12_2 <=> r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5)),
% 1.31/0.56    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).
% 1.31/0.56  fof(f322,plain,(
% 1.31/0.56    spl12_3 | ~spl12_11),
% 1.31/0.56    inference(avatar_contradiction_clause,[],[f321])).
% 1.31/0.56  fof(f321,plain,(
% 1.31/0.56    $false | (spl12_3 | ~spl12_11)),
% 1.31/0.56    inference(subsumption_resolution,[],[f320,f203])).
% 1.31/0.56  fof(f203,plain,(
% 1.31/0.56    r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),sK6)),
% 1.31/0.56    inference(resolution,[],[f115,f59])).
% 1.31/0.56  fof(f320,plain,(
% 1.31/0.56    ~r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),sK6) | (spl12_3 | ~spl12_11)),
% 1.31/0.56    inference(backward_demodulation,[],[f85,f154])).
% 1.31/0.56  fof(f154,plain,(
% 1.31/0.56    k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(sK8)) | ~spl12_11),
% 1.31/0.56    inference(avatar_component_clause,[],[f152])).
% 1.31/0.56  fof(f152,plain,(
% 1.31/0.56    spl12_11 <=> k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(sK8))),
% 1.31/0.56    introduced(avatar_definition,[new_symbols(naming,[spl12_11])])).
% 1.31/0.56  fof(f85,plain,(
% 1.31/0.56    ~r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6) | spl12_3),
% 1.31/0.56    inference(avatar_component_clause,[],[f83])).
% 1.31/0.56  fof(f83,plain,(
% 1.31/0.56    spl12_3 <=> r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6)),
% 1.31/0.56    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).
% 1.31/0.56  fof(f319,plain,(
% 1.31/0.56    spl12_4 | ~spl12_12),
% 1.31/0.56    inference(avatar_contradiction_clause,[],[f318])).
% 1.31/0.56  fof(f318,plain,(
% 1.31/0.56    $false | (spl12_4 | ~spl12_12)),
% 1.31/0.56    inference(subsumption_resolution,[],[f317,f116])).
% 1.31/0.56  fof(f116,plain,(
% 1.31/0.56    r2_hidden(k2_mcart_1(sK8),sK7)),
% 1.31/0.56    inference(resolution,[],[f66,f59])).
% 1.31/0.56  fof(f317,plain,(
% 1.31/0.56    ~r2_hidden(k2_mcart_1(sK8),sK7) | (spl12_4 | ~spl12_12)),
% 1.31/0.56    inference(backward_demodulation,[],[f89,f159])).
% 1.31/0.56  fof(f159,plain,(
% 1.31/0.56    k11_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(sK8) | ~spl12_12),
% 1.31/0.56    inference(avatar_component_clause,[],[f157])).
% 1.31/0.56  fof(f157,plain,(
% 1.31/0.56    spl12_12 <=> k11_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(sK8)),
% 1.31/0.56    introduced(avatar_definition,[new_symbols(naming,[spl12_12])])).
% 1.31/0.56  fof(f89,plain,(
% 1.31/0.56    ~r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7) | spl12_4),
% 1.31/0.56    inference(avatar_component_clause,[],[f87])).
% 1.31/0.56  fof(f87,plain,(
% 1.31/0.56    spl12_4 <=> r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7)),
% 1.31/0.56    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).
% 1.31/0.56  fof(f316,plain,(
% 1.31/0.56    ~spl12_8),
% 1.31/0.56    inference(avatar_contradiction_clause,[],[f315])).
% 1.31/0.56  fof(f315,plain,(
% 1.31/0.56    $false | ~spl12_8),
% 1.31/0.56    inference(subsumption_resolution,[],[f313,f45])).
% 1.31/0.56  fof(f45,plain,(
% 1.31/0.56    v1_xboole_0(k1_xboole_0)),
% 1.31/0.56    inference(cnf_transformation,[],[f3])).
% 1.31/0.56  fof(f3,axiom,(
% 1.31/0.56    v1_xboole_0(k1_xboole_0)),
% 1.31/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.31/0.56  fof(f313,plain,(
% 1.31/0.56    ~v1_xboole_0(k1_xboole_0) | ~spl12_8),
% 1.31/0.56    inference(backward_demodulation,[],[f193,f140])).
% 1.31/0.56  fof(f140,plain,(
% 1.31/0.56    k1_xboole_0 = sK3 | ~spl12_8),
% 1.31/0.56    inference(avatar_component_clause,[],[f138])).
% 1.31/0.56  fof(f138,plain,(
% 1.31/0.56    spl12_8 <=> k1_xboole_0 = sK3),
% 1.31/0.56    introduced(avatar_definition,[new_symbols(naming,[spl12_8])])).
% 1.31/0.56  fof(f193,plain,(
% 1.31/0.56    ~v1_xboole_0(sK3)),
% 1.31/0.56    inference(resolution,[],[f191,f47])).
% 1.31/0.56  fof(f47,plain,(
% 1.31/0.56    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 1.31/0.56    inference(cnf_transformation,[],[f29])).
% 1.31/0.56  fof(f29,plain,(
% 1.31/0.56    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK9(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.31/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f27,f28])).
% 1.31/0.56  fof(f28,plain,(
% 1.31/0.56    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK9(X0),X0))),
% 1.31/0.56    introduced(choice_axiom,[])).
% 1.31/0.56  fof(f27,plain,(
% 1.31/0.56    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.31/0.56    inference(rectify,[],[f26])).
% 1.31/0.56  fof(f26,plain,(
% 1.31/0.56    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.31/0.56    inference(nnf_transformation,[],[f1])).
% 1.31/0.56  fof(f1,axiom,(
% 1.31/0.56    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.31/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.31/0.56  fof(f191,plain,(
% 1.31/0.56    r2_hidden(k2_mcart_1(sK8),sK3)),
% 1.31/0.56    inference(resolution,[],[f114,f116])).
% 1.31/0.56  fof(f114,plain,(
% 1.31/0.56    ( ! [X0] : (~r2_hidden(X0,sK7) | r2_hidden(X0,sK3)) )),
% 1.31/0.56    inference(resolution,[],[f111,f50])).
% 1.31/0.56  fof(f50,plain,(
% 1.31/0.56    ( ! [X0,X3,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X3,X0) | r2_hidden(X3,X1)) )),
% 1.31/0.56    inference(cnf_transformation,[],[f33])).
% 1.31/0.56  fof(f33,plain,(
% 1.31/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK10(X0,X1),X1) & r2_hidden(sK10(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.31/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f31,f32])).
% 1.31/0.56  fof(f32,plain,(
% 1.31/0.56    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK10(X0,X1),X1) & r2_hidden(sK10(X0,X1),X0)))),
% 1.31/0.56    introduced(choice_axiom,[])).
% 1.31/0.56  fof(f31,plain,(
% 1.31/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.31/0.56    inference(rectify,[],[f30])).
% 1.31/0.56  fof(f30,plain,(
% 1.31/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.31/0.56    inference(nnf_transformation,[],[f17])).
% 1.31/0.56  fof(f17,plain,(
% 1.31/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.31/0.56    inference(ennf_transformation,[],[f2])).
% 1.31/0.56  fof(f2,axiom,(
% 1.31/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.31/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.31/0.56  fof(f111,plain,(
% 1.31/0.56    r1_tarski(sK7,sK3)),
% 1.31/0.56    inference(resolution,[],[f98,f73])).
% 1.31/0.56  fof(f73,plain,(
% 1.31/0.56    ( ! [X0,X3] : (~r2_hidden(X3,k1_zfmisc_1(X0)) | r1_tarski(X3,X0)) )),
% 1.31/0.56    inference(equality_resolution,[],[f53])).
% 1.31/0.56  fof(f53,plain,(
% 1.31/0.56    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.31/0.56    inference(cnf_transformation,[],[f37])).
% 1.31/0.56  fof(f37,plain,(
% 1.31/0.56    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK11(X0,X1),X0) | ~r2_hidden(sK11(X0,X1),X1)) & (r1_tarski(sK11(X0,X1),X0) | r2_hidden(sK11(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.31/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f35,f36])).
% 1.31/0.56  fof(f36,plain,(
% 1.31/0.56    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK11(X0,X1),X0) | ~r2_hidden(sK11(X0,X1),X1)) & (r1_tarski(sK11(X0,X1),X0) | r2_hidden(sK11(X0,X1),X1))))),
% 1.31/0.56    introduced(choice_axiom,[])).
% 1.31/0.56  fof(f35,plain,(
% 1.31/0.56    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.31/0.56    inference(rectify,[],[f34])).
% 1.31/0.56  fof(f34,plain,(
% 1.31/0.56    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.31/0.56    inference(nnf_transformation,[],[f4])).
% 1.31/0.56  fof(f4,axiom,(
% 1.31/0.56    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.31/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.31/0.56  fof(f98,plain,(
% 1.31/0.56    r2_hidden(sK7,k1_zfmisc_1(sK3))),
% 1.31/0.56    inference(subsumption_resolution,[],[f97,f46])).
% 1.31/0.56  fof(f46,plain,(
% 1.31/0.56    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.31/0.56    inference(cnf_transformation,[],[f5])).
% 1.31/0.56  fof(f5,axiom,(
% 1.31/0.56    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.31/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.31/0.56  fof(f97,plain,(
% 1.31/0.56    v1_xboole_0(k1_zfmisc_1(sK3)) | r2_hidden(sK7,k1_zfmisc_1(sK3))),
% 1.31/0.56    inference(resolution,[],[f41,f49])).
% 1.31/0.56  fof(f49,plain,(
% 1.31/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 1.31/0.56    inference(cnf_transformation,[],[f16])).
% 1.31/0.56  fof(f16,plain,(
% 1.31/0.56    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.31/0.56    inference(flattening,[],[f15])).
% 1.31/0.56  fof(f15,plain,(
% 1.31/0.56    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.31/0.56    inference(ennf_transformation,[],[f6])).
% 1.31/0.56  fof(f6,axiom,(
% 1.31/0.56    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.31/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 1.31/0.56  fof(f41,plain,(
% 1.31/0.56    m1_subset_1(sK7,k1_zfmisc_1(sK3))),
% 1.31/0.56    inference(cnf_transformation,[],[f25])).
% 1.31/0.56  fof(f295,plain,(
% 1.31/0.56    ~spl12_7),
% 1.31/0.56    inference(avatar_contradiction_clause,[],[f294])).
% 1.31/0.56  fof(f294,plain,(
% 1.31/0.56    $false | ~spl12_7),
% 1.31/0.56    inference(subsumption_resolution,[],[f292,f45])).
% 1.31/0.56  fof(f292,plain,(
% 1.31/0.56    ~v1_xboole_0(k1_xboole_0) | ~spl12_7),
% 1.31/0.56    inference(backward_demodulation,[],[f211,f136])).
% 1.31/0.56  fof(f136,plain,(
% 1.31/0.56    k1_xboole_0 = sK2 | ~spl12_7),
% 1.31/0.56    inference(avatar_component_clause,[],[f134])).
% 1.31/0.56  fof(f134,plain,(
% 1.31/0.56    spl12_7 <=> k1_xboole_0 = sK2),
% 1.31/0.56    introduced(avatar_definition,[new_symbols(naming,[spl12_7])])).
% 1.31/0.56  fof(f211,plain,(
% 1.31/0.56    ~v1_xboole_0(sK2)),
% 1.31/0.56    inference(resolution,[],[f209,f47])).
% 1.31/0.56  fof(f209,plain,(
% 1.31/0.56    r2_hidden(sK9(sK6),sK2)),
% 1.31/0.56    inference(resolution,[],[f207,f110])).
% 1.31/0.56  fof(f110,plain,(
% 1.31/0.56    ( ! [X0] : (~r2_hidden(X0,sK6) | r2_hidden(X0,sK2)) )),
% 1.31/0.56    inference(resolution,[],[f107,f50])).
% 1.31/0.56  fof(f107,plain,(
% 1.31/0.56    r1_tarski(sK6,sK2)),
% 1.31/0.56    inference(resolution,[],[f96,f73])).
% 1.31/0.56  fof(f96,plain,(
% 1.31/0.56    r2_hidden(sK6,k1_zfmisc_1(sK2))),
% 1.31/0.56    inference(subsumption_resolution,[],[f95,f46])).
% 1.31/0.56  fof(f95,plain,(
% 1.31/0.56    v1_xboole_0(k1_zfmisc_1(sK2)) | r2_hidden(sK6,k1_zfmisc_1(sK2))),
% 1.31/0.56    inference(resolution,[],[f40,f49])).
% 1.31/0.56  fof(f40,plain,(
% 1.31/0.56    m1_subset_1(sK6,k1_zfmisc_1(sK2))),
% 1.31/0.56    inference(cnf_transformation,[],[f25])).
% 1.31/0.56  fof(f207,plain,(
% 1.31/0.56    r2_hidden(sK9(sK6),sK6)),
% 1.31/0.56    inference(resolution,[],[f206,f48])).
% 1.31/0.56  fof(f48,plain,(
% 1.31/0.56    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK9(X0),X0)) )),
% 1.31/0.56    inference(cnf_transformation,[],[f29])).
% 1.31/0.56  fof(f206,plain,(
% 1.31/0.56    ~v1_xboole_0(sK6)),
% 1.31/0.56    inference(resolution,[],[f203,f47])).
% 1.31/0.56  fof(f274,plain,(
% 1.31/0.56    ~spl12_6),
% 1.31/0.56    inference(avatar_contradiction_clause,[],[f273])).
% 1.31/0.56  fof(f273,plain,(
% 1.31/0.56    $false | ~spl12_6),
% 1.31/0.56    inference(subsumption_resolution,[],[f272,f45])).
% 1.31/0.56  fof(f272,plain,(
% 1.31/0.56    ~v1_xboole_0(k1_xboole_0) | ~spl12_6),
% 1.31/0.56    inference(resolution,[],[f271,f47])).
% 1.31/0.56  fof(f271,plain,(
% 1.31/0.56    r2_hidden(sK9(sK5),k1_xboole_0) | ~spl12_6),
% 1.31/0.56    inference(resolution,[],[f240,f263])).
% 1.31/0.56  fof(f263,plain,(
% 1.31/0.56    r2_hidden(sK9(sK5),sK5)),
% 1.31/0.56    inference(resolution,[],[f262,f48])).
% 1.31/0.56  fof(f262,plain,(
% 1.31/0.56    ~v1_xboole_0(sK5)),
% 1.31/0.56    inference(resolution,[],[f221,f47])).
% 1.31/0.56  fof(f240,plain,(
% 1.31/0.56    ( ! [X0] : (~r2_hidden(X0,sK5) | r2_hidden(X0,k1_xboole_0)) ) | ~spl12_6),
% 1.31/0.56    inference(backward_demodulation,[],[f106,f132])).
% 1.31/0.56  fof(f132,plain,(
% 1.31/0.56    k1_xboole_0 = sK1 | ~spl12_6),
% 1.31/0.56    inference(avatar_component_clause,[],[f130])).
% 1.31/0.56  fof(f130,plain,(
% 1.31/0.56    spl12_6 <=> k1_xboole_0 = sK1),
% 1.31/0.56    introduced(avatar_definition,[new_symbols(naming,[spl12_6])])).
% 1.31/0.56  fof(f106,plain,(
% 1.31/0.56    ( ! [X0] : (~r2_hidden(X0,sK5) | r2_hidden(X0,sK1)) )),
% 1.31/0.56    inference(resolution,[],[f103,f50])).
% 1.31/0.56  fof(f103,plain,(
% 1.31/0.56    r1_tarski(sK5,sK1)),
% 1.31/0.56    inference(resolution,[],[f94,f73])).
% 1.31/0.56  fof(f94,plain,(
% 1.31/0.56    r2_hidden(sK5,k1_zfmisc_1(sK1))),
% 1.31/0.56    inference(subsumption_resolution,[],[f93,f46])).
% 1.31/0.56  fof(f93,plain,(
% 1.31/0.56    v1_xboole_0(k1_zfmisc_1(sK1)) | r2_hidden(sK5,k1_zfmisc_1(sK1))),
% 1.31/0.56    inference(resolution,[],[f39,f49])).
% 1.31/0.56  fof(f39,plain,(
% 1.31/0.56    m1_subset_1(sK5,k1_zfmisc_1(sK1))),
% 1.31/0.56    inference(cnf_transformation,[],[f25])).
% 1.31/0.56  fof(f231,plain,(
% 1.31/0.56    ~spl12_5),
% 1.31/0.56    inference(avatar_contradiction_clause,[],[f230])).
% 1.31/0.56  fof(f230,plain,(
% 1.31/0.56    $false | ~spl12_5),
% 1.31/0.56    inference(subsumption_resolution,[],[f229,f45])).
% 1.31/0.56  fof(f229,plain,(
% 1.31/0.56    ~v1_xboole_0(k1_xboole_0) | ~spl12_5),
% 1.31/0.56    inference(resolution,[],[f227,f47])).
% 1.31/0.56  fof(f227,plain,(
% 1.31/0.56    r2_hidden(sK9(sK4),k1_xboole_0) | ~spl12_5),
% 1.31/0.56    inference(resolution,[],[f226,f178])).
% 1.31/0.56  fof(f178,plain,(
% 1.31/0.56    ( ! [X0] : (~r2_hidden(X0,sK4) | r2_hidden(X0,k1_xboole_0)) ) | ~spl12_5),
% 1.31/0.56    inference(backward_demodulation,[],[f102,f128])).
% 1.31/0.56  fof(f128,plain,(
% 1.31/0.56    k1_xboole_0 = sK0 | ~spl12_5),
% 1.31/0.56    inference(avatar_component_clause,[],[f126])).
% 1.31/0.56  fof(f126,plain,(
% 1.31/0.56    spl12_5 <=> k1_xboole_0 = sK0),
% 1.31/0.56    introduced(avatar_definition,[new_symbols(naming,[spl12_5])])).
% 1.31/0.56  fof(f102,plain,(
% 1.31/0.56    ( ! [X0] : (~r2_hidden(X0,sK4) | r2_hidden(X0,sK0)) )),
% 1.31/0.56    inference(resolution,[],[f99,f50])).
% 1.31/0.56  fof(f99,plain,(
% 1.31/0.56    r1_tarski(sK4,sK0)),
% 1.31/0.56    inference(resolution,[],[f92,f73])).
% 1.31/0.56  fof(f92,plain,(
% 1.31/0.56    r2_hidden(sK4,k1_zfmisc_1(sK0))),
% 1.31/0.56    inference(subsumption_resolution,[],[f91,f46])).
% 1.31/0.56  fof(f91,plain,(
% 1.31/0.56    v1_xboole_0(k1_zfmisc_1(sK0)) | r2_hidden(sK4,k1_zfmisc_1(sK0))),
% 1.31/0.56    inference(resolution,[],[f38,f49])).
% 1.31/0.56  fof(f38,plain,(
% 1.31/0.56    m1_subset_1(sK4,k1_zfmisc_1(sK0))),
% 1.31/0.56    inference(cnf_transformation,[],[f25])).
% 1.31/0.56  fof(f226,plain,(
% 1.31/0.56    r2_hidden(sK9(sK4),sK4)),
% 1.31/0.56    inference(resolution,[],[f225,f48])).
% 1.31/0.56  fof(f225,plain,(
% 1.31/0.56    ~v1_xboole_0(sK4)),
% 1.31/0.56    inference(resolution,[],[f220,f47])).
% 1.31/0.56  fof(f160,plain,(
% 1.31/0.56    spl12_5 | spl12_6 | spl12_7 | spl12_8 | spl12_12),
% 1.31/0.56    inference(avatar_split_clause,[],[f123,f157,f138,f134,f130,f126])).
% 1.31/0.56  fof(f123,plain,(
% 1.31/0.56    k11_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(sK8) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 1.31/0.56    inference(resolution,[],[f67,f68])).
% 1.31/0.56  fof(f68,plain,(
% 1.31/0.56    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.31/0.56    inference(definition_unfolding,[],[f64,f65])).
% 1.31/0.56  fof(f64,plain,(
% 1.31/0.56    ( ! [X4,X2,X0,X3,X1] : (k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.31/0.56    inference(cnf_transformation,[],[f19])).
% 1.31/0.56  fof(f19,plain,(
% 1.31/0.56    ! [X0,X1,X2,X3] : (! [X4] : ((k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.31/0.56    inference(ennf_transformation,[],[f10])).
% 1.31/0.56  fof(f10,axiom,(
% 1.31/0.56    ! [X0,X1,X2,X3] : ~(~! [X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => (k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.31/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_mcart_1)).
% 1.31/0.56  fof(f67,plain,(
% 1.31/0.56    m1_subset_1(sK8,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))),
% 1.31/0.56    inference(definition_unfolding,[],[f42,f65])).
% 1.31/0.56  fof(f42,plain,(
% 1.31/0.56    m1_subset_1(sK8,k4_zfmisc_1(sK0,sK1,sK2,sK3))),
% 1.31/0.56    inference(cnf_transformation,[],[f25])).
% 1.31/0.56  fof(f155,plain,(
% 1.31/0.56    spl12_5 | spl12_6 | spl12_7 | spl12_8 | spl12_11),
% 1.31/0.56    inference(avatar_split_clause,[],[f122,f152,f138,f134,f130,f126])).
% 1.31/0.56  fof(f122,plain,(
% 1.31/0.56    k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(sK8)) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 1.31/0.56    inference(resolution,[],[f67,f69])).
% 1.31/0.56  fof(f69,plain,(
% 1.31/0.56    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.31/0.56    inference(definition_unfolding,[],[f63,f65])).
% 1.31/0.56  fof(f63,plain,(
% 1.31/0.56    ( ! [X4,X2,X0,X3,X1] : (k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.31/0.56    inference(cnf_transformation,[],[f19])).
% 1.31/0.56  fof(f150,plain,(
% 1.31/0.56    spl12_5 | spl12_6 | spl12_7 | spl12_8 | spl12_10),
% 1.31/0.56    inference(avatar_split_clause,[],[f121,f147,f138,f134,f130,f126])).
% 1.31/0.56  fof(f121,plain,(
% 1.31/0.56    k9_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 1.31/0.56    inference(resolution,[],[f67,f70])).
% 1.31/0.56  fof(f70,plain,(
% 1.31/0.56    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.31/0.56    inference(definition_unfolding,[],[f62,f65])).
% 1.31/0.56  fof(f62,plain,(
% 1.31/0.56    ( ! [X4,X2,X0,X3,X1] : (k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.31/0.56    inference(cnf_transformation,[],[f19])).
% 1.31/0.56  fof(f145,plain,(
% 1.31/0.56    spl12_5 | spl12_6 | spl12_7 | spl12_8 | spl12_9),
% 1.31/0.56    inference(avatar_split_clause,[],[f120,f142,f138,f134,f130,f126])).
% 1.31/0.56  fof(f120,plain,(
% 1.31/0.56    k8_mcart_1(sK0,sK1,sK2,sK3,sK8) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 1.31/0.56    inference(resolution,[],[f67,f71])).
% 1.31/0.56  fof(f71,plain,(
% 1.31/0.56    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.31/0.56    inference(definition_unfolding,[],[f61,f65])).
% 1.31/0.56  fof(f61,plain,(
% 1.31/0.56    ( ! [X4,X2,X0,X3,X1] : (k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.31/0.56    inference(cnf_transformation,[],[f19])).
% 1.31/0.56  fof(f90,plain,(
% 1.31/0.56    ~spl12_1 | ~spl12_2 | ~spl12_3 | ~spl12_4),
% 1.31/0.56    inference(avatar_split_clause,[],[f44,f87,f83,f79,f75])).
% 1.31/0.56  fof(f44,plain,(
% 1.31/0.56    ~r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7) | ~r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6) | ~r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5) | ~r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4)),
% 1.31/0.56    inference(cnf_transformation,[],[f25])).
% 1.31/0.56  % SZS output end Proof for theBenchmark
% 1.31/0.56  % (5826)------------------------------
% 1.31/0.56  % (5826)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.56  % (5826)Termination reason: Refutation
% 1.31/0.56  
% 1.31/0.56  % (5826)Memory used [KB]: 10874
% 1.31/0.56  % (5826)Time elapsed: 0.119 s
% 1.31/0.56  % (5826)------------------------------
% 1.31/0.56  % (5826)------------------------------
% 1.31/0.56  % (5829)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.31/0.56  % (5829)Refutation not found, incomplete strategy% (5829)------------------------------
% 1.31/0.56  % (5829)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.56  % (5829)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.56  
% 1.31/0.56  % (5829)Memory used [KB]: 10746
% 1.31/0.56  % (5829)Time elapsed: 0.118 s
% 1.31/0.56  % (5829)------------------------------
% 1.31/0.56  % (5829)------------------------------
% 1.31/0.56  % (5834)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.31/0.57  % (5822)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.31/0.57  % (5821)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.31/0.57  % (5841)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.31/0.57  % (5844)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.31/0.57  % (5818)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.31/0.57  % (5833)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.31/0.57  % (5838)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.31/0.58  % (5835)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.31/0.58  % (5823)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.31/0.58  % (5840)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.31/0.58  % (5830)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.31/0.58  % (5825)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.31/0.58  % (5836)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.31/0.58  % (5817)Success in time 0.203 s
%------------------------------------------------------------------------------
