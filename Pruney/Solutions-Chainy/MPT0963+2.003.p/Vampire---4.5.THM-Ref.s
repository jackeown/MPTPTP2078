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
% DateTime   : Thu Dec  3 13:00:28 EST 2020

% Result     : Theorem 1.68s
% Output     : Refutation 2.29s
% Verified   : 
% Statistics : Number of formulae       :  157 (1250 expanded)
%              Number of leaves         :   19 ( 324 expanded)
%              Depth                    :   25
%              Number of atoms          :  831 (9821 expanded)
%              Number of equality atoms :  162 (1733 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1146,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f89,f91,f965,f1106,f1109,f1137,f1145])).

fof(f1145,plain,
    ( spl10_2
    | ~ spl10_11 ),
    inference(avatar_contradiction_clause,[],[f1144])).

fof(f1144,plain,
    ( $false
    | spl10_2
    | ~ spl10_11 ),
    inference(subsumption_resolution,[],[f1143,f85])).

fof(f85,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | spl10_2 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl10_2
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f1143,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl10_11 ),
    inference(resolution,[],[f1110,f94])).

fof(f94,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK2),X0)
      | v1_funct_2(sK2,sK0,X0) ) ),
    inference(subsumption_resolution,[],[f93,f39])).

fof(f39,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_2(sK2,sK0,sK1)
      | ~ v1_funct_1(sK2) )
    & ! [X3] :
        ( r2_hidden(k1_funct_1(sK2,X3),sK1)
        | ~ r2_hidden(X3,sK0) )
    & sK0 = k1_relat_1(sK2)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f20])).

fof(f20,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2) )
        & ! [X3] :
            ( r2_hidden(k1_funct_1(X2,X3),X1)
            | ~ r2_hidden(X3,X0) )
        & k1_relat_1(X2) = X0
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_2(sK2,sK0,sK1)
        | ~ v1_funct_1(sK2) )
      & ! [X3] :
          ( r2_hidden(k1_funct_1(sK2,X3),sK1)
          | ~ r2_hidden(X3,sK0) )
      & sK0 = k1_relat_1(sK2)
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2) )
      & ! [X3] :
          ( r2_hidden(k1_funct_1(X2,X3),X1)
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2) )
      & ! [X3] :
          ( r2_hidden(k1_funct_1(X2,X3),X1)
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( ! [X3] :
                ( r2_hidden(X3,X0)
               => r2_hidden(k1_funct_1(X2,X3),X1) )
            & k1_relat_1(X2) = X0 )
         => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X2,X0,X1)
            & v1_funct_1(X2) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( ! [X3] :
              ( r2_hidden(X3,X0)
             => r2_hidden(k1_funct_1(X2,X3),X1) )
          & k1_relat_1(X2) = X0 )
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_funct_2)).

fof(f93,plain,(
    ! [X0] :
      ( v1_funct_2(sK2,sK0,X0)
      | ~ r1_tarski(k2_relat_1(sK2),X0)
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f92,f40])).

fof(f40,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f92,plain,(
    ! [X0] :
      ( v1_funct_2(sK2,sK0,X0)
      | ~ r1_tarski(k2_relat_1(sK2),X0)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f66,f41])).

fof(f41,plain,(
    sK0 = k1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

fof(f1110,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | ~ spl10_11 ),
    inference(backward_demodulation,[],[f288,f964])).

fof(f964,plain,
    ( k2_relat_1(sK2) = k9_relat_1(sK2,sK0)
    | ~ spl10_11 ),
    inference(avatar_component_clause,[],[f963])).

fof(f963,plain,
    ( spl10_11
  <=> k2_relat_1(sK2) = k9_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).

fof(f288,plain,(
    r1_tarski(k9_relat_1(sK2,sK0),sK1) ),
    inference(subsumption_resolution,[],[f287,f39])).

fof(f287,plain,
    ( r1_tarski(k9_relat_1(sK2,sK0),sK1)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f283,f40])).

fof(f283,plain,
    ( r1_tarski(k9_relat_1(sK2,sK0),sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f64,f273])).

fof(f273,plain,(
    sK0 = k10_relat_1(sK2,sK1) ),
    inference(subsumption_resolution,[],[f271,f267])).

fof(f267,plain,(
    ! [X0] :
      ( r2_hidden(sK6(sK2,X0,sK0),sK0)
      | sK0 = k10_relat_1(sK2,X0) ) ),
    inference(factoring,[],[f179])).

fof(f179,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(sK2,X0,X1),sK0)
      | k10_relat_1(sK2,X0) = X1
      | r2_hidden(sK6(sK2,X0,X1),X1) ) ),
    inference(subsumption_resolution,[],[f178,f39])).

fof(f178,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(sK2,X0,X1),sK0)
      | k10_relat_1(sK2,X0) = X1
      | r2_hidden(sK6(sK2,X0,X1),X1)
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f177,f40])).

fof(f177,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(sK2,X0,X1),sK0)
      | k10_relat_1(sK2,X0) = X1
      | r2_hidden(sK6(sK2,X0,X1),X1)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f53,f41])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X2),k1_relat_1(X0))
      | k10_relat_1(X0,X1) = X2
      | r2_hidden(sK6(X0,X1,X2),X2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ( ( ~ r2_hidden(k1_funct_1(X0,sK6(X0,X1,X2)),X1)
                | ~ r2_hidden(sK6(X0,X1,X2),k1_relat_1(X0))
                | ~ r2_hidden(sK6(X0,X1,X2),X2) )
              & ( ( r2_hidden(k1_funct_1(X0,sK6(X0,X1,X2)),X1)
                  & r2_hidden(sK6(X0,X1,X2),k1_relat_1(X0)) )
                | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k1_funct_1(X0,X4),X1)
                  | ~ r2_hidden(X4,k1_relat_1(X0)) )
                & ( ( r2_hidden(k1_funct_1(X0,X4),X1)
                    & r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X4,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f30,f31])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
            | ~ r2_hidden(X3,k1_relat_1(X0))
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
              & r2_hidden(X3,k1_relat_1(X0)) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(k1_funct_1(X0,sK6(X0,X1,X2)),X1)
          | ~ r2_hidden(sK6(X0,X1,X2),k1_relat_1(X0))
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( ( r2_hidden(k1_funct_1(X0,sK6(X0,X1,X2)),X1)
            & r2_hidden(sK6(X0,X1,X2),k1_relat_1(X0)) )
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0))
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k1_funct_1(X0,X4),X1)
                  | ~ r2_hidden(X4,k1_relat_1(X0)) )
                & ( ( r2_hidden(k1_funct_1(X0,X4),X1)
                    & r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X4,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0))
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0)) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0))
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0)) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_funct_1)).

fof(f271,plain,
    ( sK0 = k10_relat_1(sK2,sK1)
    | ~ r2_hidden(sK6(sK2,sK1,sK0),sK0) ),
    inference(duplicate_literal_removal,[],[f270])).

fof(f270,plain,
    ( sK0 = k10_relat_1(sK2,sK1)
    | ~ r2_hidden(sK6(sK2,sK1,sK0),sK0)
    | sK0 = k10_relat_1(sK2,sK1) ),
    inference(resolution,[],[f248,f267])).

fof(f248,plain,(
    ! [X8] :
      ( ~ r2_hidden(sK6(sK2,sK1,X8),sK0)
      | k10_relat_1(sK2,sK1) = X8
      | ~ r2_hidden(sK6(sK2,sK1,X8),X8) ) ),
    inference(duplicate_literal_removal,[],[f247])).

fof(f247,plain,(
    ! [X8] :
      ( ~ r2_hidden(sK6(sK2,sK1,X8),sK0)
      | k10_relat_1(sK2,sK1) = X8
      | ~ r2_hidden(sK6(sK2,sK1,X8),X8)
      | ~ r2_hidden(sK6(sK2,sK1,X8),sK0) ) ),
    inference(forward_demodulation,[],[f246,f41])).

fof(f246,plain,(
    ! [X8] :
      ( k10_relat_1(sK2,sK1) = X8
      | ~ r2_hidden(sK6(sK2,sK1,X8),k1_relat_1(sK2))
      | ~ r2_hidden(sK6(sK2,sK1,X8),X8)
      | ~ r2_hidden(sK6(sK2,sK1,X8),sK0) ) ),
    inference(subsumption_resolution,[],[f245,f39])).

fof(f245,plain,(
    ! [X8] :
      ( k10_relat_1(sK2,sK1) = X8
      | ~ r2_hidden(sK6(sK2,sK1,X8),k1_relat_1(sK2))
      | ~ r2_hidden(sK6(sK2,sK1,X8),X8)
      | ~ v1_relat_1(sK2)
      | ~ r2_hidden(sK6(sK2,sK1,X8),sK0) ) ),
    inference(subsumption_resolution,[],[f240,f40])).

fof(f240,plain,(
    ! [X8] :
      ( k10_relat_1(sK2,sK1) = X8
      | ~ r2_hidden(sK6(sK2,sK1,X8),k1_relat_1(sK2))
      | ~ r2_hidden(sK6(sK2,sK1,X8),X8)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2)
      | ~ r2_hidden(sK6(sK2,sK1,X8),sK0) ) ),
    inference(resolution,[],[f55,f42])).

fof(f42,plain,(
    ! [X3] :
      ( r2_hidden(k1_funct_1(sK2,X3),sK1)
      | ~ r2_hidden(X3,sK0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k1_funct_1(X0,sK6(X0,X1,X2)),X1)
      | k10_relat_1(X0,X1) = X2
      | ~ r2_hidden(sK6(X0,X1,X2),k1_relat_1(X0))
      | ~ r2_hidden(sK6(X0,X1,X2),X2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

fof(f1137,plain,
    ( spl10_3
    | ~ spl10_11 ),
    inference(avatar_contradiction_clause,[],[f1136])).

fof(f1136,plain,
    ( $false
    | spl10_3
    | ~ spl10_11 ),
    inference(subsumption_resolution,[],[f1110,f1107])).

fof(f1107,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK1)
    | spl10_3 ),
    inference(resolution,[],[f88,f100])).

fof(f100,plain,(
    ! [X0] :
      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
      | ~ r1_tarski(k2_relat_1(sK2),X0) ) ),
    inference(subsumption_resolution,[],[f99,f39])).

fof(f99,plain,(
    ! [X0] :
      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
      | ~ r1_tarski(k2_relat_1(sK2),X0)
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f98,f40])).

fof(f98,plain,(
    ! [X0] :
      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
      | ~ r1_tarski(k2_relat_1(sK2),X0)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f67,f41])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f88,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl10_3 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl10_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f1109,plain,
    ( spl10_3
    | ~ spl10_8 ),
    inference(avatar_contradiction_clause,[],[f1108])).

fof(f1108,plain,
    ( $false
    | spl10_3
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f1107,f1039])).

fof(f1039,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | ~ spl10_8 ),
    inference(backward_demodulation,[],[f288,f1038])).

fof(f1038,plain,
    ( k2_relat_1(sK2) = k9_relat_1(sK2,sK0)
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f1037,f39])).

fof(f1037,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k9_relat_1(sK2,sK0)
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f1036,f40])).

fof(f1036,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k9_relat_1(sK2,sK0)
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f1034,f569])).

fof(f569,plain,
    ( r2_hidden(sK3(sK2,k9_relat_1(sK2,sK0)),k9_relat_1(sK2,sK0))
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f568])).

fof(f568,plain,
    ( spl10_8
  <=> r2_hidden(sK3(sK2,k9_relat_1(sK2,sK0)),k9_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f1034,plain,
    ( ~ r2_hidden(sK3(sK2,k9_relat_1(sK2,sK0)),k9_relat_1(sK2,sK0))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k9_relat_1(sK2,sK0)
    | ~ spl10_8 ),
    inference(resolution,[],[f985,f368])).

fof(f368,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),k2_relat_1(X0))
      | ~ r2_hidden(sK3(X0,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X0) = X1 ) ),
    inference(equality_resolution,[],[f196])).

fof(f196,plain,(
    ! [X2,X0,X1] :
      ( sK3(X0,X2) != X1
      | k2_relat_1(X0) = X2
      | ~ r2_hidden(sK3(X0,X2),X2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X1,k2_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f195,f71])).

fof(f71,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK5(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK5(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK3(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK3(X0,X1),X1) )
              & ( ( sK3(X0,X1) = k1_funct_1(X0,sK4(X0,X1))
                  & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK3(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK5(X0,X5)) = X5
                    & r2_hidden(sK5(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f23,f26,f25,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k1_funct_1(X0,X3) != X2
                | ~ r2_hidden(X3,k1_relat_1(X0)) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( k1_funct_1(X0,X4) = X2
                & r2_hidden(X4,k1_relat_1(X0)) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( k1_funct_1(X0,X3) != sK3(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK3(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = sK3(X0,X1)
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( sK3(X0,X1) = k1_funct_1(X0,sK4(X0,X1))
        & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK5(X0,X5)) = X5
        & r2_hidden(sK5(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X2
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ? [X7] :
                      ( k1_funct_1(X0,X7) = X5
                      & r2_hidden(X7,k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) ) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

fof(f195,plain,(
    ! [X2,X0,X1] :
      ( sK3(X0,X2) != X1
      | k2_relat_1(X0) = X2
      | ~ r2_hidden(sK5(X0,X1),k1_relat_1(X0))
      | ~ r2_hidden(sK3(X0,X2),X2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X1,k2_relat_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f190])).

fof(f190,plain,(
    ! [X2,X0,X1] :
      ( sK3(X0,X2) != X1
      | k2_relat_1(X0) = X2
      | ~ r2_hidden(sK5(X0,X1),k1_relat_1(X0))
      | ~ r2_hidden(sK3(X0,X2),X2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X1,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f49,f70])).

fof(f70,plain,(
    ! [X0,X5] :
      ( k1_funct_1(X0,sK5(X0,X5)) = X5
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK5(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f49,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(X0,X3) != sK3(X0,X1)
      | k2_relat_1(X0) = X1
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ r2_hidden(sK3(X0,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f985,plain,
    ( r2_hidden(sK3(sK2,k9_relat_1(sK2,sK0)),k2_relat_1(sK2))
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f984,f39])).

fof(f984,plain,
    ( ~ v1_relat_1(sK2)
    | r2_hidden(sK3(sK2,k9_relat_1(sK2,sK0)),k2_relat_1(sK2))
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f983,f40])).

fof(f983,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | r2_hidden(sK3(sK2,k9_relat_1(sK2,sK0)),k2_relat_1(sK2))
    | ~ spl10_8 ),
    inference(resolution,[],[f569,f123])).

fof(f123,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(X4,k9_relat_1(X2,X3))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | r2_hidden(X4,k2_relat_1(X2)) ) ),
    inference(subsumption_resolution,[],[f119,f79])).

fof(f79,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK9(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK9(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( k1_funct_1(X0,X4) != sK7(X0,X1,X2)
                    | ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(X4,k1_relat_1(X0)) )
                | ~ r2_hidden(sK7(X0,X1,X2),X2) )
              & ( ( sK7(X0,X1,X2) = k1_funct_1(X0,sK8(X0,X1,X2))
                  & r2_hidden(sK8(X0,X1,X2),X1)
                  & r2_hidden(sK8(X0,X1,X2),k1_relat_1(X0)) )
                | r2_hidden(sK7(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( k1_funct_1(X0,X7) != X6
                      | ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK9(X0,X1,X6)) = X6
                    & r2_hidden(sK9(X0,X1,X6),X1)
                    & r2_hidden(sK9(X0,X1,X6),k1_relat_1(X0)) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f34,f37,f36,f35])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( k1_funct_1(X0,X4) != X3
                | ~ r2_hidden(X4,X1)
                | ~ r2_hidden(X4,k1_relat_1(X0)) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( k1_funct_1(X0,X5) = X3
                & r2_hidden(X5,X1)
                & r2_hidden(X5,k1_relat_1(X0)) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( k1_funct_1(X0,X4) != sK7(X0,X1,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,k1_relat_1(X0)) )
          | ~ r2_hidden(sK7(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( k1_funct_1(X0,X5) = sK7(X0,X1,X2)
              & r2_hidden(X5,X1)
              & r2_hidden(X5,k1_relat_1(X0)) )
          | r2_hidden(sK7(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( k1_funct_1(X0,X5) = sK7(X0,X1,X2)
          & r2_hidden(X5,X1)
          & r2_hidden(X5,k1_relat_1(X0)) )
     => ( sK7(X0,X1,X2) = k1_funct_1(X0,sK8(X0,X1,X2))
        & r2_hidden(sK8(X0,X1,X2),X1)
        & r2_hidden(sK8(X0,X1,X2),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( k1_funct_1(X0,X8) = X6
          & r2_hidden(X8,X1)
          & r2_hidden(X8,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK9(X0,X1,X6)) = X6
        & r2_hidden(sK9(X0,X1,X6),X1)
        & r2_hidden(sK9(X0,X1,X6),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( k1_funct_1(X0,X5) = X3
                      & r2_hidden(X5,X1)
                      & r2_hidden(X5,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( k1_funct_1(X0,X7) != X6
                      | ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
                & ( ? [X8] :
                      ( k1_funct_1(X0,X8) = X6
                      & r2_hidden(X8,X1)
                      & r2_hidden(X8,k1_relat_1(X0)) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X3
                      & r2_hidden(X4,X1)
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) ) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X3
                      & r2_hidden(X4,X1)
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_funct_1)).

fof(f119,plain,(
    ! [X4,X2,X3] :
      ( r2_hidden(X4,k2_relat_1(X2))
      | ~ r2_hidden(sK9(X2,X3,X4),k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X4,k9_relat_1(X2,X3)) ) ),
    inference(duplicate_literal_removal,[],[f118])).

fof(f118,plain,(
    ! [X4,X2,X3] :
      ( r2_hidden(X4,k2_relat_1(X2))
      | ~ r2_hidden(sK9(X2,X3,X4),k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X4,k9_relat_1(X2,X3))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f69,f77])).

fof(f77,plain,(
    ! [X6,X0,X1] :
      ( k1_funct_1(X0,sK9(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_funct_1(X0,sK9(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f69,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f1106,plain,
    ( spl10_2
    | ~ spl10_8 ),
    inference(avatar_contradiction_clause,[],[f1105])).

fof(f1105,plain,
    ( $false
    | spl10_2
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f1104,f85])).

fof(f1104,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl10_8 ),
    inference(resolution,[],[f1039,f94])).

fof(f965,plain,
    ( spl10_8
    | spl10_11 ),
    inference(avatar_split_clause,[],[f961,f963,f568])).

fof(f961,plain,
    ( k2_relat_1(sK2) = k9_relat_1(sK2,sK0)
    | r2_hidden(sK3(sK2,k9_relat_1(sK2,sK0)),k9_relat_1(sK2,sK0)) ),
    inference(subsumption_resolution,[],[f960,f39])).

fof(f960,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k9_relat_1(sK2,sK0)
    | r2_hidden(sK3(sK2,k9_relat_1(sK2,sK0)),k9_relat_1(sK2,sK0)) ),
    inference(subsumption_resolution,[],[f955,f40])).

fof(f955,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k9_relat_1(sK2,sK0)
    | r2_hidden(sK3(sK2,k9_relat_1(sK2,sK0)),k9_relat_1(sK2,sK0)) ),
    inference(duplicate_literal_removal,[],[f949])).

fof(f949,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k9_relat_1(sK2,sK0)
    | k2_relat_1(sK2) = k9_relat_1(sK2,sK0)
    | r2_hidden(sK3(sK2,k9_relat_1(sK2,sK0)),k9_relat_1(sK2,sK0)) ),
    inference(resolution,[],[f435,f571])).

fof(f571,plain,(
    ! [X0] :
      ( r2_hidden(sK4(sK2,X0),sK0)
      | k2_relat_1(sK2) = X0
      | r2_hidden(sK3(sK2,X0),X0) ) ),
    inference(global_subsumption,[],[f172,f442])).

fof(f442,plain,(
    ! [X0] :
      ( r2_hidden(sK4(sK2,X0),sK0)
      | ~ r2_hidden(sK3(sK2,X0),sK1)
      | k2_relat_1(sK2) = X0
      | r2_hidden(sK3(sK2,X0),X0) ) ),
    inference(subsumption_resolution,[],[f441,f39])).

fof(f441,plain,(
    ! [X0] :
      ( r2_hidden(sK4(sK2,X0),sK0)
      | ~ r2_hidden(sK3(sK2,X0),sK1)
      | ~ v1_relat_1(sK2)
      | k2_relat_1(sK2) = X0
      | r2_hidden(sK3(sK2,X0),X0) ) ),
    inference(subsumption_resolution,[],[f438,f40])).

fof(f438,plain,(
    ! [X0] :
      ( r2_hidden(sK4(sK2,X0),sK0)
      | ~ r2_hidden(sK3(sK2,X0),sK1)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2)
      | k2_relat_1(sK2) = X0
      | r2_hidden(sK3(sK2,X0),X0) ) ),
    inference(superposition,[],[f174,f273])).

fof(f174,plain,(
    ! [X6,X4,X5] :
      ( r2_hidden(sK4(X4,X5),k10_relat_1(X4,X6))
      | ~ r2_hidden(sK3(X4,X5),X6)
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4)
      | k2_relat_1(X4) = X5
      | r2_hidden(sK3(X4,X5),X5) ) ),
    inference(subsumption_resolution,[],[f168,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),k1_relat_1(X0))
      | k2_relat_1(X0) = X1
      | r2_hidden(sK3(X0,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f168,plain,(
    ! [X6,X4,X5] :
      ( ~ r2_hidden(sK3(X4,X5),X6)
      | r2_hidden(sK4(X4,X5),k10_relat_1(X4,X6))
      | ~ r2_hidden(sK4(X4,X5),k1_relat_1(X4))
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4)
      | k2_relat_1(X4) = X5
      | r2_hidden(sK3(X4,X5),X5) ) ),
    inference(duplicate_literal_removal,[],[f165])).

fof(f165,plain,(
    ! [X6,X4,X5] :
      ( ~ r2_hidden(sK3(X4,X5),X6)
      | r2_hidden(sK4(X4,X5),k10_relat_1(X4,X6))
      | ~ r2_hidden(sK4(X4,X5),k1_relat_1(X4))
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4)
      | k2_relat_1(X4) = X5
      | r2_hidden(sK3(X4,X5),X5)
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4) ) ),
    inference(superposition,[],[f72,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( sK3(X0,X1) = k1_funct_1(X0,sK4(X0,X1))
      | k2_relat_1(X0) = X1
      | r2_hidden(sK3(X0,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f72,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(k1_funct_1(X0,X4),X1)
      | r2_hidden(X4,k10_relat_1(X0,X1))
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(k1_funct_1(X0,X4),X1)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | k10_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f172,plain,(
    ! [X0] :
      ( r2_hidden(sK3(sK2,X0),sK1)
      | k2_relat_1(sK2) = X0
      | r2_hidden(sK3(sK2,X0),X0) ) ),
    inference(subsumption_resolution,[],[f171,f158])).

fof(f158,plain,(
    ! [X0] :
      ( r2_hidden(sK4(sK2,X0),sK0)
      | k2_relat_1(sK2) = X0
      | r2_hidden(sK3(sK2,X0),X0) ) ),
    inference(subsumption_resolution,[],[f157,f39])).

fof(f157,plain,(
    ! [X0] :
      ( r2_hidden(sK4(sK2,X0),sK0)
      | k2_relat_1(sK2) = X0
      | r2_hidden(sK3(sK2,X0),X0)
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f156,f40])).

fof(f156,plain,(
    ! [X0] :
      ( r2_hidden(sK4(sK2,X0),sK0)
      | k2_relat_1(sK2) = X0
      | r2_hidden(sK3(sK2,X0),X0)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f47,f41])).

fof(f171,plain,(
    ! [X0] :
      ( r2_hidden(sK3(sK2,X0),sK1)
      | ~ r2_hidden(sK4(sK2,X0),sK0)
      | k2_relat_1(sK2) = X0
      | r2_hidden(sK3(sK2,X0),X0) ) ),
    inference(subsumption_resolution,[],[f170,f39])).

fof(f170,plain,(
    ! [X0] :
      ( r2_hidden(sK3(sK2,X0),sK1)
      | ~ r2_hidden(sK4(sK2,X0),sK0)
      | k2_relat_1(sK2) = X0
      | r2_hidden(sK3(sK2,X0),X0)
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f163,f40])).

fof(f163,plain,(
    ! [X0] :
      ( r2_hidden(sK3(sK2,X0),sK1)
      | ~ r2_hidden(sK4(sK2,X0),sK0)
      | k2_relat_1(sK2) = X0
      | r2_hidden(sK3(sK2,X0),X0)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f42,f48])).

fof(f435,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,k9_relat_1(X0,X1)),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k9_relat_1(X0,X1) = k2_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f426,f391])).

fof(f391,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X0) = X1
      | ~ r2_hidden(sK3(X0,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(sK3(X0,X1),k9_relat_1(X0,X2)) ) ),
    inference(equality_resolution,[],[f197])).

fof(f197,plain,(
    ! [X6,X4,X5,X3] :
      ( sK3(X3,X6) != X5
      | k2_relat_1(X3) = X6
      | ~ r2_hidden(sK3(X3,X6),X6)
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3)
      | ~ r2_hidden(X5,k9_relat_1(X3,X4)) ) ),
    inference(subsumption_resolution,[],[f194,f79])).

fof(f194,plain,(
    ! [X6,X4,X5,X3] :
      ( sK3(X3,X6) != X5
      | k2_relat_1(X3) = X6
      | ~ r2_hidden(sK9(X3,X4,X5),k1_relat_1(X3))
      | ~ r2_hidden(sK3(X3,X6),X6)
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3)
      | ~ r2_hidden(X5,k9_relat_1(X3,X4)) ) ),
    inference(duplicate_literal_removal,[],[f191])).

fof(f191,plain,(
    ! [X6,X4,X5,X3] :
      ( sK3(X3,X6) != X5
      | k2_relat_1(X3) = X6
      | ~ r2_hidden(sK9(X3,X4,X5),k1_relat_1(X3))
      | ~ r2_hidden(sK3(X3,X6),X6)
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3)
      | ~ r2_hidden(X5,k9_relat_1(X3,X4))
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3) ) ),
    inference(superposition,[],[f49,f77])).

fof(f426,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,k9_relat_1(X0,X1)),k9_relat_1(X0,X1))
      | ~ r2_hidden(sK4(X0,k9_relat_1(X0,X1)),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k9_relat_1(X0,X1) = k2_relat_1(X0) ) ),
    inference(factoring,[],[f173])).

fof(f173,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(sK3(X1,X2),k9_relat_1(X1,X3))
      | ~ r2_hidden(sK4(X1,X2),X3)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k2_relat_1(X1) = X2
      | r2_hidden(sK3(X1,X2),X2) ) ),
    inference(subsumption_resolution,[],[f169,f47])).

fof(f169,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(sK3(X1,X2),k9_relat_1(X1,X3))
      | ~ r2_hidden(sK4(X1,X2),X3)
      | ~ r2_hidden(sK4(X1,X2),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k2_relat_1(X1) = X2
      | r2_hidden(sK3(X1,X2),X2) ) ),
    inference(duplicate_literal_removal,[],[f164])).

fof(f164,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(sK3(X1,X2),k9_relat_1(X1,X3))
      | ~ r2_hidden(sK4(X1,X2),X3)
      | ~ r2_hidden(sK4(X1,X2),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k2_relat_1(X1) = X2
      | r2_hidden(sK3(X1,X2),X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f76,f48])).

fof(f76,plain,(
    ! [X0,X7,X1] :
      ( r2_hidden(k1_funct_1(X0,X7),k9_relat_1(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X7,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X2,X0,X7,X1] :
      ( r2_hidden(k1_funct_1(X0,X7),X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X7,k1_relat_1(X0))
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | k1_funct_1(X0,X7) != X6
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X7,k1_relat_1(X0))
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f91,plain,(
    spl10_1 ),
    inference(avatar_contradiction_clause,[],[f90])).

fof(f90,plain,
    ( $false
    | spl10_1 ),
    inference(subsumption_resolution,[],[f82,f40])).

fof(f82,plain,
    ( ~ v1_funct_1(sK2)
    | spl10_1 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl10_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f89,plain,
    ( ~ spl10_1
    | ~ spl10_2
    | ~ spl10_3 ),
    inference(avatar_split_clause,[],[f43,f87,f84,f81])).

fof(f43,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n009.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:27:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (13155)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (13163)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.50  % (13156)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.52  % (13147)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.52  % (13154)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.52  % (13157)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.52  % (13153)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.53  % (13148)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.53  % (13161)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.53  % (13146)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.54  % (13149)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.54  % (13143)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (13144)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (13145)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.54  % (13154)Refutation not found, incomplete strategy% (13154)------------------------------
% 0.21/0.54  % (13154)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (13154)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (13154)Memory used [KB]: 10746
% 0.21/0.54  % (13154)Time elapsed: 0.105 s
% 0.21/0.54  % (13154)------------------------------
% 0.21/0.54  % (13154)------------------------------
% 0.21/0.55  % (13162)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.55  % (13160)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 1.44/0.56  % (13159)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 1.44/0.56  % (13158)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 1.44/0.57  % (13151)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 1.68/0.57  % (13150)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 1.68/0.58  % (13152)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 1.68/0.63  % (13145)Refutation found. Thanks to Tanya!
% 1.68/0.63  % SZS status Theorem for theBenchmark
% 1.68/0.64  % SZS output start Proof for theBenchmark
% 1.68/0.64  fof(f1146,plain,(
% 1.68/0.64    $false),
% 1.68/0.64    inference(avatar_sat_refutation,[],[f89,f91,f965,f1106,f1109,f1137,f1145])).
% 1.68/0.64  fof(f1145,plain,(
% 1.68/0.64    spl10_2 | ~spl10_11),
% 1.68/0.64    inference(avatar_contradiction_clause,[],[f1144])).
% 1.68/0.64  fof(f1144,plain,(
% 1.68/0.64    $false | (spl10_2 | ~spl10_11)),
% 1.68/0.64    inference(subsumption_resolution,[],[f1143,f85])).
% 1.68/0.64  fof(f85,plain,(
% 1.68/0.64    ~v1_funct_2(sK2,sK0,sK1) | spl10_2),
% 1.68/0.64    inference(avatar_component_clause,[],[f84])).
% 1.68/0.64  fof(f84,plain,(
% 1.68/0.64    spl10_2 <=> v1_funct_2(sK2,sK0,sK1)),
% 1.68/0.64    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 1.68/0.64  fof(f1143,plain,(
% 1.68/0.64    v1_funct_2(sK2,sK0,sK1) | ~spl10_11),
% 1.68/0.64    inference(resolution,[],[f1110,f94])).
% 1.68/0.64  fof(f94,plain,(
% 1.68/0.64    ( ! [X0] : (~r1_tarski(k2_relat_1(sK2),X0) | v1_funct_2(sK2,sK0,X0)) )),
% 1.68/0.64    inference(subsumption_resolution,[],[f93,f39])).
% 1.68/0.64  fof(f39,plain,(
% 1.68/0.64    v1_relat_1(sK2)),
% 1.68/0.64    inference(cnf_transformation,[],[f21])).
% 1.68/0.64  fof(f21,plain,(
% 1.68/0.64    (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) & ! [X3] : (r2_hidden(k1_funct_1(sK2,X3),sK1) | ~r2_hidden(X3,sK0)) & sK0 = k1_relat_1(sK2) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 1.68/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f20])).
% 1.68/0.64  fof(f20,plain,(
% 1.68/0.64    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & ! [X3] : (r2_hidden(k1_funct_1(X2,X3),X1) | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => ((~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) & ! [X3] : (r2_hidden(k1_funct_1(sK2,X3),sK1) | ~r2_hidden(X3,sK0)) & sK0 = k1_relat_1(sK2) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 1.68/0.64    introduced(choice_axiom,[])).
% 1.68/0.64  fof(f9,plain,(
% 1.68/0.64    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & ! [X3] : (r2_hidden(k1_funct_1(X2,X3),X1) | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.68/0.64    inference(flattening,[],[f8])).
% 1.68/0.64  fof(f8,plain,(
% 1.68/0.64    ? [X0,X1,X2] : (((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & (! [X3] : (r2_hidden(k1_funct_1(X2,X3),X1) | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0)) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 1.68/0.64    inference(ennf_transformation,[],[f7])).
% 1.68/0.64  fof(f7,negated_conjecture,(
% 1.68/0.64    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,X0) => r2_hidden(k1_funct_1(X2,X3),X1)) & k1_relat_1(X2) = X0) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 1.68/0.64    inference(negated_conjecture,[],[f6])).
% 1.68/0.64  fof(f6,conjecture,(
% 1.68/0.64    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,X0) => r2_hidden(k1_funct_1(X2,X3),X1)) & k1_relat_1(X2) = X0) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 1.68/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_funct_2)).
% 1.68/0.64  fof(f93,plain,(
% 1.68/0.64    ( ! [X0] : (v1_funct_2(sK2,sK0,X0) | ~r1_tarski(k2_relat_1(sK2),X0) | ~v1_relat_1(sK2)) )),
% 1.68/0.64    inference(subsumption_resolution,[],[f92,f40])).
% 1.68/0.64  fof(f40,plain,(
% 1.68/0.64    v1_funct_1(sK2)),
% 1.68/0.64    inference(cnf_transformation,[],[f21])).
% 1.68/0.64  fof(f92,plain,(
% 1.68/0.64    ( ! [X0] : (v1_funct_2(sK2,sK0,X0) | ~r1_tarski(k2_relat_1(sK2),X0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 1.68/0.64    inference(superposition,[],[f66,f41])).
% 1.68/0.64  fof(f41,plain,(
% 1.68/0.64    sK0 = k1_relat_1(sK2)),
% 1.68/0.64    inference(cnf_transformation,[],[f21])).
% 1.68/0.64  fof(f66,plain,(
% 1.68/0.64    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.68/0.64    inference(cnf_transformation,[],[f19])).
% 1.68/0.64  fof(f19,plain,(
% 1.68/0.64    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.68/0.64    inference(flattening,[],[f18])).
% 1.68/0.64  fof(f18,plain,(
% 1.68/0.64    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.68/0.64    inference(ennf_transformation,[],[f5])).
% 1.68/0.64  fof(f5,axiom,(
% 1.68/0.64    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 1.68/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).
% 1.68/0.64  fof(f1110,plain,(
% 1.68/0.64    r1_tarski(k2_relat_1(sK2),sK1) | ~spl10_11),
% 1.68/0.64    inference(backward_demodulation,[],[f288,f964])).
% 1.68/0.64  fof(f964,plain,(
% 1.68/0.64    k2_relat_1(sK2) = k9_relat_1(sK2,sK0) | ~spl10_11),
% 1.68/0.64    inference(avatar_component_clause,[],[f963])).
% 1.68/0.64  fof(f963,plain,(
% 1.68/0.64    spl10_11 <=> k2_relat_1(sK2) = k9_relat_1(sK2,sK0)),
% 1.68/0.64    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).
% 1.68/0.64  fof(f288,plain,(
% 1.68/0.64    r1_tarski(k9_relat_1(sK2,sK0),sK1)),
% 1.68/0.64    inference(subsumption_resolution,[],[f287,f39])).
% 1.68/0.64  fof(f287,plain,(
% 1.68/0.64    r1_tarski(k9_relat_1(sK2,sK0),sK1) | ~v1_relat_1(sK2)),
% 1.68/0.64    inference(subsumption_resolution,[],[f283,f40])).
% 1.68/0.64  fof(f283,plain,(
% 1.68/0.64    r1_tarski(k9_relat_1(sK2,sK0),sK1) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.68/0.64    inference(superposition,[],[f64,f273])).
% 1.68/0.64  fof(f273,plain,(
% 1.68/0.64    sK0 = k10_relat_1(sK2,sK1)),
% 1.68/0.64    inference(subsumption_resolution,[],[f271,f267])).
% 1.68/0.64  fof(f267,plain,(
% 1.68/0.64    ( ! [X0] : (r2_hidden(sK6(sK2,X0,sK0),sK0) | sK0 = k10_relat_1(sK2,X0)) )),
% 1.68/0.64    inference(factoring,[],[f179])).
% 1.68/0.64  fof(f179,plain,(
% 1.68/0.64    ( ! [X0,X1] : (r2_hidden(sK6(sK2,X0,X1),sK0) | k10_relat_1(sK2,X0) = X1 | r2_hidden(sK6(sK2,X0,X1),X1)) )),
% 1.68/0.64    inference(subsumption_resolution,[],[f178,f39])).
% 1.68/0.64  fof(f178,plain,(
% 1.68/0.64    ( ! [X0,X1] : (r2_hidden(sK6(sK2,X0,X1),sK0) | k10_relat_1(sK2,X0) = X1 | r2_hidden(sK6(sK2,X0,X1),X1) | ~v1_relat_1(sK2)) )),
% 1.68/0.64    inference(subsumption_resolution,[],[f177,f40])).
% 1.68/0.64  fof(f177,plain,(
% 1.68/0.64    ( ! [X0,X1] : (r2_hidden(sK6(sK2,X0,X1),sK0) | k10_relat_1(sK2,X0) = X1 | r2_hidden(sK6(sK2,X0,X1),X1) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 1.68/0.64    inference(superposition,[],[f53,f41])).
% 1.68/0.64  fof(f53,plain,(
% 1.68/0.64    ( ! [X2,X0,X1] : (r2_hidden(sK6(X0,X1,X2),k1_relat_1(X0)) | k10_relat_1(X0,X1) = X2 | r2_hidden(sK6(X0,X1,X2),X2) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.68/0.64    inference(cnf_transformation,[],[f32])).
% 1.68/0.64  fof(f32,plain,(
% 1.68/0.64    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ((~r2_hidden(k1_funct_1(X0,sK6(X0,X1,X2)),X1) | ~r2_hidden(sK6(X0,X1,X2),k1_relat_1(X0)) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((r2_hidden(k1_funct_1(X0,sK6(X0,X1,X2)),X1) & r2_hidden(sK6(X0,X1,X2),k1_relat_1(X0))) | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k1_funct_1(X0,X4),X1) | ~r2_hidden(X4,k1_relat_1(X0))) & ((r2_hidden(k1_funct_1(X0,X4),X1) & r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X4,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.68/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f30,f31])).
% 1.68/0.64  fof(f31,plain,(
% 1.68/0.64    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X3,X2))) => ((~r2_hidden(k1_funct_1(X0,sK6(X0,X1,X2)),X1) | ~r2_hidden(sK6(X0,X1,X2),k1_relat_1(X0)) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((r2_hidden(k1_funct_1(X0,sK6(X0,X1,X2)),X1) & r2_hidden(sK6(X0,X1,X2),k1_relat_1(X0))) | r2_hidden(sK6(X0,X1,X2),X2))))),
% 1.68/0.64    introduced(choice_axiom,[])).
% 1.68/0.64  fof(f30,plain,(
% 1.68/0.64    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k1_funct_1(X0,X4),X1) | ~r2_hidden(X4,k1_relat_1(X0))) & ((r2_hidden(k1_funct_1(X0,X4),X1) & r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X4,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.68/0.64    inference(rectify,[],[f29])).
% 1.68/0.64  fof(f29,plain,(
% 1.68/0.64    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0))) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X3,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.68/0.64    inference(flattening,[],[f28])).
% 1.68/0.64  fof(f28,plain,(
% 1.68/0.64    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : (((~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0)))) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X3,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.68/0.64    inference(nnf_transformation,[],[f13])).
% 1.68/0.64  fof(f13,plain,(
% 1.68/0.64    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.68/0.64    inference(flattening,[],[f12])).
% 1.68/0.64  fof(f12,plain,(
% 1.68/0.64    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.68/0.64    inference(ennf_transformation,[],[f2])).
% 1.68/0.64  fof(f2,axiom,(
% 1.68/0.64    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))))),
% 1.68/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_funct_1)).
% 1.68/0.64  fof(f271,plain,(
% 1.68/0.64    sK0 = k10_relat_1(sK2,sK1) | ~r2_hidden(sK6(sK2,sK1,sK0),sK0)),
% 1.68/0.64    inference(duplicate_literal_removal,[],[f270])).
% 1.68/0.64  fof(f270,plain,(
% 1.68/0.64    sK0 = k10_relat_1(sK2,sK1) | ~r2_hidden(sK6(sK2,sK1,sK0),sK0) | sK0 = k10_relat_1(sK2,sK1)),
% 1.68/0.64    inference(resolution,[],[f248,f267])).
% 1.68/0.64  fof(f248,plain,(
% 1.68/0.64    ( ! [X8] : (~r2_hidden(sK6(sK2,sK1,X8),sK0) | k10_relat_1(sK2,sK1) = X8 | ~r2_hidden(sK6(sK2,sK1,X8),X8)) )),
% 1.68/0.64    inference(duplicate_literal_removal,[],[f247])).
% 1.68/0.64  fof(f247,plain,(
% 1.68/0.64    ( ! [X8] : (~r2_hidden(sK6(sK2,sK1,X8),sK0) | k10_relat_1(sK2,sK1) = X8 | ~r2_hidden(sK6(sK2,sK1,X8),X8) | ~r2_hidden(sK6(sK2,sK1,X8),sK0)) )),
% 1.68/0.64    inference(forward_demodulation,[],[f246,f41])).
% 1.68/0.64  fof(f246,plain,(
% 1.68/0.64    ( ! [X8] : (k10_relat_1(sK2,sK1) = X8 | ~r2_hidden(sK6(sK2,sK1,X8),k1_relat_1(sK2)) | ~r2_hidden(sK6(sK2,sK1,X8),X8) | ~r2_hidden(sK6(sK2,sK1,X8),sK0)) )),
% 1.68/0.64    inference(subsumption_resolution,[],[f245,f39])).
% 1.68/0.64  fof(f245,plain,(
% 1.68/0.64    ( ! [X8] : (k10_relat_1(sK2,sK1) = X8 | ~r2_hidden(sK6(sK2,sK1,X8),k1_relat_1(sK2)) | ~r2_hidden(sK6(sK2,sK1,X8),X8) | ~v1_relat_1(sK2) | ~r2_hidden(sK6(sK2,sK1,X8),sK0)) )),
% 1.68/0.64    inference(subsumption_resolution,[],[f240,f40])).
% 1.68/0.64  fof(f240,plain,(
% 1.68/0.64    ( ! [X8] : (k10_relat_1(sK2,sK1) = X8 | ~r2_hidden(sK6(sK2,sK1,X8),k1_relat_1(sK2)) | ~r2_hidden(sK6(sK2,sK1,X8),X8) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~r2_hidden(sK6(sK2,sK1,X8),sK0)) )),
% 1.68/0.64    inference(resolution,[],[f55,f42])).
% 1.68/0.64  fof(f42,plain,(
% 1.68/0.64    ( ! [X3] : (r2_hidden(k1_funct_1(sK2,X3),sK1) | ~r2_hidden(X3,sK0)) )),
% 1.68/0.64    inference(cnf_transformation,[],[f21])).
% 1.68/0.64  fof(f55,plain,(
% 1.68/0.64    ( ! [X2,X0,X1] : (~r2_hidden(k1_funct_1(X0,sK6(X0,X1,X2)),X1) | k10_relat_1(X0,X1) = X2 | ~r2_hidden(sK6(X0,X1,X2),k1_relat_1(X0)) | ~r2_hidden(sK6(X0,X1,X2),X2) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.68/0.64    inference(cnf_transformation,[],[f32])).
% 1.68/0.64  fof(f64,plain,(
% 1.68/0.64    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.68/0.64    inference(cnf_transformation,[],[f17])).
% 1.68/0.64  fof(f17,plain,(
% 1.68/0.64    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.68/0.64    inference(flattening,[],[f16])).
% 1.68/0.64  fof(f16,plain,(
% 1.68/0.64    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.68/0.64    inference(ennf_transformation,[],[f4])).
% 1.68/0.64  fof(f4,axiom,(
% 1.68/0.64    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 1.68/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).
% 1.68/0.64  fof(f1137,plain,(
% 1.68/0.64    spl10_3 | ~spl10_11),
% 1.68/0.64    inference(avatar_contradiction_clause,[],[f1136])).
% 1.68/0.64  fof(f1136,plain,(
% 1.68/0.64    $false | (spl10_3 | ~spl10_11)),
% 1.68/0.64    inference(subsumption_resolution,[],[f1110,f1107])).
% 1.68/0.64  fof(f1107,plain,(
% 1.68/0.64    ~r1_tarski(k2_relat_1(sK2),sK1) | spl10_3),
% 1.68/0.64    inference(resolution,[],[f88,f100])).
% 1.68/0.64  fof(f100,plain,(
% 1.68/0.64    ( ! [X0] : (m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | ~r1_tarski(k2_relat_1(sK2),X0)) )),
% 1.68/0.64    inference(subsumption_resolution,[],[f99,f39])).
% 1.68/0.64  fof(f99,plain,(
% 1.68/0.64    ( ! [X0] : (m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | ~r1_tarski(k2_relat_1(sK2),X0) | ~v1_relat_1(sK2)) )),
% 1.68/0.64    inference(subsumption_resolution,[],[f98,f40])).
% 1.68/0.64  fof(f98,plain,(
% 1.68/0.64    ( ! [X0] : (m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | ~r1_tarski(k2_relat_1(sK2),X0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 1.68/0.64    inference(superposition,[],[f67,f41])).
% 1.68/0.64  fof(f67,plain,(
% 1.68/0.64    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.68/0.64    inference(cnf_transformation,[],[f19])).
% 1.68/0.64  fof(f88,plain,(
% 1.68/0.64    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl10_3),
% 1.68/0.64    inference(avatar_component_clause,[],[f87])).
% 1.68/0.64  fof(f87,plain,(
% 1.68/0.64    spl10_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.68/0.64    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 1.68/0.64  fof(f1109,plain,(
% 1.68/0.64    spl10_3 | ~spl10_8),
% 1.68/0.64    inference(avatar_contradiction_clause,[],[f1108])).
% 1.68/0.64  fof(f1108,plain,(
% 1.68/0.64    $false | (spl10_3 | ~spl10_8)),
% 1.68/0.64    inference(subsumption_resolution,[],[f1107,f1039])).
% 1.68/0.64  fof(f1039,plain,(
% 1.68/0.64    r1_tarski(k2_relat_1(sK2),sK1) | ~spl10_8),
% 1.68/0.64    inference(backward_demodulation,[],[f288,f1038])).
% 1.68/0.64  fof(f1038,plain,(
% 1.68/0.64    k2_relat_1(sK2) = k9_relat_1(sK2,sK0) | ~spl10_8),
% 1.68/0.64    inference(subsumption_resolution,[],[f1037,f39])).
% 1.68/0.64  fof(f1037,plain,(
% 1.68/0.64    ~v1_relat_1(sK2) | k2_relat_1(sK2) = k9_relat_1(sK2,sK0) | ~spl10_8),
% 1.68/0.64    inference(subsumption_resolution,[],[f1036,f40])).
% 1.68/0.64  fof(f1036,plain,(
% 1.68/0.64    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k2_relat_1(sK2) = k9_relat_1(sK2,sK0) | ~spl10_8),
% 1.68/0.64    inference(subsumption_resolution,[],[f1034,f569])).
% 1.68/0.64  fof(f569,plain,(
% 1.68/0.64    r2_hidden(sK3(sK2,k9_relat_1(sK2,sK0)),k9_relat_1(sK2,sK0)) | ~spl10_8),
% 1.68/0.64    inference(avatar_component_clause,[],[f568])).
% 1.68/0.64  fof(f568,plain,(
% 1.68/0.64    spl10_8 <=> r2_hidden(sK3(sK2,k9_relat_1(sK2,sK0)),k9_relat_1(sK2,sK0))),
% 1.68/0.64    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).
% 1.68/0.64  fof(f1034,plain,(
% 1.68/0.64    ~r2_hidden(sK3(sK2,k9_relat_1(sK2,sK0)),k9_relat_1(sK2,sK0)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k2_relat_1(sK2) = k9_relat_1(sK2,sK0) | ~spl10_8),
% 1.68/0.64    inference(resolution,[],[f985,f368])).
% 1.68/0.64  fof(f368,plain,(
% 1.68/0.64    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),k2_relat_1(X0)) | ~r2_hidden(sK3(X0,X1),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_relat_1(X0) = X1) )),
% 1.68/0.64    inference(equality_resolution,[],[f196])).
% 1.68/0.64  fof(f196,plain,(
% 1.68/0.64    ( ! [X2,X0,X1] : (sK3(X0,X2) != X1 | k2_relat_1(X0) = X2 | ~r2_hidden(sK3(X0,X2),X2) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~r2_hidden(X1,k2_relat_1(X0))) )),
% 1.68/0.64    inference(subsumption_resolution,[],[f195,f71])).
% 1.68/0.64  fof(f71,plain,(
% 1.68/0.64    ( ! [X0,X5] : (r2_hidden(sK5(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.68/0.64    inference(equality_resolution,[],[f44])).
% 1.68/0.64  fof(f44,plain,(
% 1.68/0.64    ( ! [X0,X5,X1] : (r2_hidden(sK5(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.68/0.64    inference(cnf_transformation,[],[f27])).
% 1.68/0.64  fof(f27,plain,(
% 1.68/0.64    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK3(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK3(X0,X1),X1)) & ((sK3(X0,X1) = k1_funct_1(X0,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),k1_relat_1(X0))) | r2_hidden(sK3(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK5(X0,X5)) = X5 & r2_hidden(sK5(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.68/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f23,f26,f25,f24])).
% 1.68/0.64  fof(f24,plain,(
% 1.68/0.64    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK3(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK3(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK3(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK3(X0,X1),X1))))),
% 1.68/0.64    introduced(choice_axiom,[])).
% 1.68/0.64  fof(f25,plain,(
% 1.68/0.64    ! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = sK3(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) => (sK3(X0,X1) = k1_funct_1(X0,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),k1_relat_1(X0))))),
% 1.68/0.64    introduced(choice_axiom,[])).
% 1.68/0.64  fof(f26,plain,(
% 1.68/0.64    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK5(X0,X5)) = X5 & r2_hidden(sK5(X0,X5),k1_relat_1(X0))))),
% 1.68/0.64    introduced(choice_axiom,[])).
% 1.68/0.64  fof(f23,plain,(
% 1.68/0.64    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.68/0.64    inference(rectify,[],[f22])).
% 1.68/0.64  fof(f22,plain,(
% 1.68/0.64    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.68/0.64    inference(nnf_transformation,[],[f11])).
% 1.68/0.64  fof(f11,plain,(
% 1.68/0.64    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.68/0.64    inference(flattening,[],[f10])).
% 1.68/0.64  fof(f10,plain,(
% 1.68/0.64    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.68/0.64    inference(ennf_transformation,[],[f3])).
% 1.68/0.64  fof(f3,axiom,(
% 1.68/0.64    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 1.68/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).
% 1.68/0.64  fof(f195,plain,(
% 1.68/0.64    ( ! [X2,X0,X1] : (sK3(X0,X2) != X1 | k2_relat_1(X0) = X2 | ~r2_hidden(sK5(X0,X1),k1_relat_1(X0)) | ~r2_hidden(sK3(X0,X2),X2) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~r2_hidden(X1,k2_relat_1(X0))) )),
% 1.68/0.64    inference(duplicate_literal_removal,[],[f190])).
% 1.68/0.64  fof(f190,plain,(
% 1.68/0.64    ( ! [X2,X0,X1] : (sK3(X0,X2) != X1 | k2_relat_1(X0) = X2 | ~r2_hidden(sK5(X0,X1),k1_relat_1(X0)) | ~r2_hidden(sK3(X0,X2),X2) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~r2_hidden(X1,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.68/0.64    inference(superposition,[],[f49,f70])).
% 1.68/0.64  fof(f70,plain,(
% 1.68/0.64    ( ! [X0,X5] : (k1_funct_1(X0,sK5(X0,X5)) = X5 | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.68/0.64    inference(equality_resolution,[],[f45])).
% 1.68/0.64  fof(f45,plain,(
% 1.68/0.64    ( ! [X0,X5,X1] : (k1_funct_1(X0,sK5(X0,X5)) = X5 | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.68/0.64    inference(cnf_transformation,[],[f27])).
% 1.68/0.64  fof(f49,plain,(
% 1.68/0.64    ( ! [X0,X3,X1] : (k1_funct_1(X0,X3) != sK3(X0,X1) | k2_relat_1(X0) = X1 | ~r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(sK3(X0,X1),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.68/0.64    inference(cnf_transformation,[],[f27])).
% 1.68/0.64  fof(f985,plain,(
% 1.68/0.64    r2_hidden(sK3(sK2,k9_relat_1(sK2,sK0)),k2_relat_1(sK2)) | ~spl10_8),
% 1.68/0.64    inference(subsumption_resolution,[],[f984,f39])).
% 1.68/0.64  fof(f984,plain,(
% 1.68/0.64    ~v1_relat_1(sK2) | r2_hidden(sK3(sK2,k9_relat_1(sK2,sK0)),k2_relat_1(sK2)) | ~spl10_8),
% 1.68/0.64    inference(subsumption_resolution,[],[f983,f40])).
% 1.68/0.64  fof(f983,plain,(
% 1.68/0.64    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | r2_hidden(sK3(sK2,k9_relat_1(sK2,sK0)),k2_relat_1(sK2)) | ~spl10_8),
% 1.68/0.64    inference(resolution,[],[f569,f123])).
% 1.68/0.64  fof(f123,plain,(
% 1.68/0.64    ( ! [X4,X2,X3] : (~r2_hidden(X4,k9_relat_1(X2,X3)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | r2_hidden(X4,k2_relat_1(X2))) )),
% 1.68/0.64    inference(subsumption_resolution,[],[f119,f79])).
% 1.68/0.64  fof(f79,plain,(
% 1.68/0.64    ( ! [X6,X0,X1] : (r2_hidden(sK9(X0,X1,X6),k1_relat_1(X0)) | ~r2_hidden(X6,k9_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.68/0.64    inference(equality_resolution,[],[f56])).
% 1.68/0.64  fof(f56,plain,(
% 1.68/0.64    ( ! [X6,X2,X0,X1] : (r2_hidden(sK9(X0,X1,X6),k1_relat_1(X0)) | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.68/0.64    inference(cnf_transformation,[],[f38])).
% 1.68/0.64  fof(f38,plain,(
% 1.68/0.64    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ((! [X4] : (k1_funct_1(X0,X4) != sK7(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK7(X0,X1,X2),X2)) & ((sK7(X0,X1,X2) = k1_funct_1(X0,sK8(X0,X1,X2)) & r2_hidden(sK8(X0,X1,X2),X1) & r2_hidden(sK8(X0,X1,X2),k1_relat_1(X0))) | r2_hidden(sK7(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK9(X0,X1,X6)) = X6 & r2_hidden(sK9(X0,X1,X6),X1) & r2_hidden(sK9(X0,X1,X6),k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.68/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f34,f37,f36,f35])).
% 1.68/0.64  fof(f35,plain,(
% 1.68/0.64    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2))) => ((! [X4] : (k1_funct_1(X0,X4) != sK7(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK7(X0,X1,X2),X2)) & (? [X5] : (k1_funct_1(X0,X5) = sK7(X0,X1,X2) & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(sK7(X0,X1,X2),X2))))),
% 1.68/0.64    introduced(choice_axiom,[])).
% 1.68/0.64  fof(f36,plain,(
% 1.68/0.64    ! [X2,X1,X0] : (? [X5] : (k1_funct_1(X0,X5) = sK7(X0,X1,X2) & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) => (sK7(X0,X1,X2) = k1_funct_1(X0,sK8(X0,X1,X2)) & r2_hidden(sK8(X0,X1,X2),X1) & r2_hidden(sK8(X0,X1,X2),k1_relat_1(X0))))),
% 1.68/0.64    introduced(choice_axiom,[])).
% 1.68/0.64  fof(f37,plain,(
% 1.68/0.64    ! [X6,X1,X0] : (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) => (k1_funct_1(X0,sK9(X0,X1,X6)) = X6 & r2_hidden(sK9(X0,X1,X6),X1) & r2_hidden(sK9(X0,X1,X6),k1_relat_1(X0))))),
% 1.68/0.64    introduced(choice_axiom,[])).
% 1.68/0.64  fof(f34,plain,(
% 1.68/0.64    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.68/0.64    inference(rectify,[],[f33])).
% 1.68/0.64  fof(f33,plain,(
% 1.68/0.64    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0)))) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.68/0.64    inference(nnf_transformation,[],[f15])).
% 1.68/0.64  fof(f15,plain,(
% 1.68/0.64    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.68/0.64    inference(flattening,[],[f14])).
% 1.68/0.64  fof(f14,plain,(
% 1.68/0.64    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.68/0.64    inference(ennf_transformation,[],[f1])).
% 1.68/0.64  fof(f1,axiom,(
% 1.68/0.64    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))))),
% 1.68/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_funct_1)).
% 1.68/0.64  fof(f119,plain,(
% 1.68/0.64    ( ! [X4,X2,X3] : (r2_hidden(X4,k2_relat_1(X2)) | ~r2_hidden(sK9(X2,X3,X4),k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~r2_hidden(X4,k9_relat_1(X2,X3))) )),
% 1.68/0.64    inference(duplicate_literal_removal,[],[f118])).
% 1.68/0.64  fof(f118,plain,(
% 1.68/0.64    ( ! [X4,X2,X3] : (r2_hidden(X4,k2_relat_1(X2)) | ~r2_hidden(sK9(X2,X3,X4),k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~r2_hidden(X4,k9_relat_1(X2,X3)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.68/0.64    inference(superposition,[],[f69,f77])).
% 1.68/0.64  fof(f77,plain,(
% 1.68/0.64    ( ! [X6,X0,X1] : (k1_funct_1(X0,sK9(X0,X1,X6)) = X6 | ~r2_hidden(X6,k9_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.68/0.64    inference(equality_resolution,[],[f58])).
% 1.68/0.64  fof(f58,plain,(
% 1.68/0.64    ( ! [X6,X2,X0,X1] : (k1_funct_1(X0,sK9(X0,X1,X6)) = X6 | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.68/0.64    inference(cnf_transformation,[],[f38])).
% 2.29/0.65  fof(f69,plain,(
% 2.29/0.65    ( ! [X6,X0] : (r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0)) | ~r2_hidden(X6,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.29/0.65    inference(equality_resolution,[],[f68])).
% 2.29/0.65  fof(f68,plain,(
% 2.29/0.65    ( ! [X6,X0,X1] : (r2_hidden(k1_funct_1(X0,X6),X1) | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.29/0.65    inference(equality_resolution,[],[f46])).
% 2.29/0.65  fof(f46,plain,(
% 2.29/0.65    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.29/0.65    inference(cnf_transformation,[],[f27])).
% 2.29/0.65  fof(f1106,plain,(
% 2.29/0.65    spl10_2 | ~spl10_8),
% 2.29/0.65    inference(avatar_contradiction_clause,[],[f1105])).
% 2.29/0.65  fof(f1105,plain,(
% 2.29/0.65    $false | (spl10_2 | ~spl10_8)),
% 2.29/0.65    inference(subsumption_resolution,[],[f1104,f85])).
% 2.29/0.65  fof(f1104,plain,(
% 2.29/0.65    v1_funct_2(sK2,sK0,sK1) | ~spl10_8),
% 2.29/0.65    inference(resolution,[],[f1039,f94])).
% 2.29/0.65  fof(f965,plain,(
% 2.29/0.65    spl10_8 | spl10_11),
% 2.29/0.65    inference(avatar_split_clause,[],[f961,f963,f568])).
% 2.29/0.65  fof(f961,plain,(
% 2.29/0.65    k2_relat_1(sK2) = k9_relat_1(sK2,sK0) | r2_hidden(sK3(sK2,k9_relat_1(sK2,sK0)),k9_relat_1(sK2,sK0))),
% 2.29/0.65    inference(subsumption_resolution,[],[f960,f39])).
% 2.29/0.65  fof(f960,plain,(
% 2.29/0.65    ~v1_relat_1(sK2) | k2_relat_1(sK2) = k9_relat_1(sK2,sK0) | r2_hidden(sK3(sK2,k9_relat_1(sK2,sK0)),k9_relat_1(sK2,sK0))),
% 2.29/0.65    inference(subsumption_resolution,[],[f955,f40])).
% 2.29/0.65  fof(f955,plain,(
% 2.29/0.65    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k2_relat_1(sK2) = k9_relat_1(sK2,sK0) | r2_hidden(sK3(sK2,k9_relat_1(sK2,sK0)),k9_relat_1(sK2,sK0))),
% 2.29/0.65    inference(duplicate_literal_removal,[],[f949])).
% 2.29/0.65  fof(f949,plain,(
% 2.29/0.65    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k2_relat_1(sK2) = k9_relat_1(sK2,sK0) | k2_relat_1(sK2) = k9_relat_1(sK2,sK0) | r2_hidden(sK3(sK2,k9_relat_1(sK2,sK0)),k9_relat_1(sK2,sK0))),
% 2.29/0.65    inference(resolution,[],[f435,f571])).
% 2.29/0.65  fof(f571,plain,(
% 2.29/0.65    ( ! [X0] : (r2_hidden(sK4(sK2,X0),sK0) | k2_relat_1(sK2) = X0 | r2_hidden(sK3(sK2,X0),X0)) )),
% 2.29/0.65    inference(global_subsumption,[],[f172,f442])).
% 2.29/0.65  fof(f442,plain,(
% 2.29/0.65    ( ! [X0] : (r2_hidden(sK4(sK2,X0),sK0) | ~r2_hidden(sK3(sK2,X0),sK1) | k2_relat_1(sK2) = X0 | r2_hidden(sK3(sK2,X0),X0)) )),
% 2.29/0.65    inference(subsumption_resolution,[],[f441,f39])).
% 2.29/0.65  fof(f441,plain,(
% 2.29/0.65    ( ! [X0] : (r2_hidden(sK4(sK2,X0),sK0) | ~r2_hidden(sK3(sK2,X0),sK1) | ~v1_relat_1(sK2) | k2_relat_1(sK2) = X0 | r2_hidden(sK3(sK2,X0),X0)) )),
% 2.29/0.65    inference(subsumption_resolution,[],[f438,f40])).
% 2.29/0.65  fof(f438,plain,(
% 2.29/0.65    ( ! [X0] : (r2_hidden(sK4(sK2,X0),sK0) | ~r2_hidden(sK3(sK2,X0),sK1) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k2_relat_1(sK2) = X0 | r2_hidden(sK3(sK2,X0),X0)) )),
% 2.29/0.65    inference(superposition,[],[f174,f273])).
% 2.29/0.65  fof(f174,plain,(
% 2.29/0.65    ( ! [X6,X4,X5] : (r2_hidden(sK4(X4,X5),k10_relat_1(X4,X6)) | ~r2_hidden(sK3(X4,X5),X6) | ~v1_funct_1(X4) | ~v1_relat_1(X4) | k2_relat_1(X4) = X5 | r2_hidden(sK3(X4,X5),X5)) )),
% 2.29/0.65    inference(subsumption_resolution,[],[f168,f47])).
% 2.29/0.65  fof(f47,plain,(
% 2.29/0.65    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),k1_relat_1(X0)) | k2_relat_1(X0) = X1 | r2_hidden(sK3(X0,X1),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.29/0.65    inference(cnf_transformation,[],[f27])).
% 2.29/0.65  fof(f168,plain,(
% 2.29/0.65    ( ! [X6,X4,X5] : (~r2_hidden(sK3(X4,X5),X6) | r2_hidden(sK4(X4,X5),k10_relat_1(X4,X6)) | ~r2_hidden(sK4(X4,X5),k1_relat_1(X4)) | ~v1_funct_1(X4) | ~v1_relat_1(X4) | k2_relat_1(X4) = X5 | r2_hidden(sK3(X4,X5),X5)) )),
% 2.29/0.65    inference(duplicate_literal_removal,[],[f165])).
% 2.29/0.65  fof(f165,plain,(
% 2.29/0.65    ( ! [X6,X4,X5] : (~r2_hidden(sK3(X4,X5),X6) | r2_hidden(sK4(X4,X5),k10_relat_1(X4,X6)) | ~r2_hidden(sK4(X4,X5),k1_relat_1(X4)) | ~v1_funct_1(X4) | ~v1_relat_1(X4) | k2_relat_1(X4) = X5 | r2_hidden(sK3(X4,X5),X5) | ~v1_funct_1(X4) | ~v1_relat_1(X4)) )),
% 2.29/0.65    inference(superposition,[],[f72,f48])).
% 2.29/0.65  fof(f48,plain,(
% 2.29/0.65    ( ! [X0,X1] : (sK3(X0,X1) = k1_funct_1(X0,sK4(X0,X1)) | k2_relat_1(X0) = X1 | r2_hidden(sK3(X0,X1),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.29/0.65    inference(cnf_transformation,[],[f27])).
% 2.29/0.65  fof(f72,plain,(
% 2.29/0.65    ( ! [X4,X0,X1] : (~r2_hidden(k1_funct_1(X0,X4),X1) | r2_hidden(X4,k10_relat_1(X0,X1)) | ~r2_hidden(X4,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.29/0.65    inference(equality_resolution,[],[f52])).
% 2.29/0.65  fof(f52,plain,(
% 2.29/0.65    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(k1_funct_1(X0,X4),X1) | ~r2_hidden(X4,k1_relat_1(X0)) | k10_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.29/0.65    inference(cnf_transformation,[],[f32])).
% 2.29/0.65  fof(f172,plain,(
% 2.29/0.65    ( ! [X0] : (r2_hidden(sK3(sK2,X0),sK1) | k2_relat_1(sK2) = X0 | r2_hidden(sK3(sK2,X0),X0)) )),
% 2.29/0.65    inference(subsumption_resolution,[],[f171,f158])).
% 2.29/0.65  fof(f158,plain,(
% 2.29/0.65    ( ! [X0] : (r2_hidden(sK4(sK2,X0),sK0) | k2_relat_1(sK2) = X0 | r2_hidden(sK3(sK2,X0),X0)) )),
% 2.29/0.65    inference(subsumption_resolution,[],[f157,f39])).
% 2.29/0.65  fof(f157,plain,(
% 2.29/0.65    ( ! [X0] : (r2_hidden(sK4(sK2,X0),sK0) | k2_relat_1(sK2) = X0 | r2_hidden(sK3(sK2,X0),X0) | ~v1_relat_1(sK2)) )),
% 2.29/0.65    inference(subsumption_resolution,[],[f156,f40])).
% 2.29/0.65  fof(f156,plain,(
% 2.29/0.65    ( ! [X0] : (r2_hidden(sK4(sK2,X0),sK0) | k2_relat_1(sK2) = X0 | r2_hidden(sK3(sK2,X0),X0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 2.29/0.65    inference(superposition,[],[f47,f41])).
% 2.29/0.65  fof(f171,plain,(
% 2.29/0.65    ( ! [X0] : (r2_hidden(sK3(sK2,X0),sK1) | ~r2_hidden(sK4(sK2,X0),sK0) | k2_relat_1(sK2) = X0 | r2_hidden(sK3(sK2,X0),X0)) )),
% 2.29/0.65    inference(subsumption_resolution,[],[f170,f39])).
% 2.29/0.65  fof(f170,plain,(
% 2.29/0.65    ( ! [X0] : (r2_hidden(sK3(sK2,X0),sK1) | ~r2_hidden(sK4(sK2,X0),sK0) | k2_relat_1(sK2) = X0 | r2_hidden(sK3(sK2,X0),X0) | ~v1_relat_1(sK2)) )),
% 2.29/0.65    inference(subsumption_resolution,[],[f163,f40])).
% 2.29/0.65  fof(f163,plain,(
% 2.29/0.65    ( ! [X0] : (r2_hidden(sK3(sK2,X0),sK1) | ~r2_hidden(sK4(sK2,X0),sK0) | k2_relat_1(sK2) = X0 | r2_hidden(sK3(sK2,X0),X0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 2.29/0.65    inference(superposition,[],[f42,f48])).
% 2.29/0.65  fof(f435,plain,(
% 2.29/0.65    ( ! [X0,X1] : (~r2_hidden(sK4(X0,k9_relat_1(X0,X1)),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k9_relat_1(X0,X1) = k2_relat_1(X0)) )),
% 2.29/0.65    inference(subsumption_resolution,[],[f426,f391])).
% 2.29/0.65  fof(f391,plain,(
% 2.29/0.65    ( ! [X2,X0,X1] : (k2_relat_1(X0) = X1 | ~r2_hidden(sK3(X0,X1),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~r2_hidden(sK3(X0,X1),k9_relat_1(X0,X2))) )),
% 2.29/0.65    inference(equality_resolution,[],[f197])).
% 2.29/0.65  fof(f197,plain,(
% 2.29/0.65    ( ! [X6,X4,X5,X3] : (sK3(X3,X6) != X5 | k2_relat_1(X3) = X6 | ~r2_hidden(sK3(X3,X6),X6) | ~v1_funct_1(X3) | ~v1_relat_1(X3) | ~r2_hidden(X5,k9_relat_1(X3,X4))) )),
% 2.29/0.65    inference(subsumption_resolution,[],[f194,f79])).
% 2.29/0.65  fof(f194,plain,(
% 2.29/0.65    ( ! [X6,X4,X5,X3] : (sK3(X3,X6) != X5 | k2_relat_1(X3) = X6 | ~r2_hidden(sK9(X3,X4,X5),k1_relat_1(X3)) | ~r2_hidden(sK3(X3,X6),X6) | ~v1_funct_1(X3) | ~v1_relat_1(X3) | ~r2_hidden(X5,k9_relat_1(X3,X4))) )),
% 2.29/0.65    inference(duplicate_literal_removal,[],[f191])).
% 2.29/0.65  fof(f191,plain,(
% 2.29/0.65    ( ! [X6,X4,X5,X3] : (sK3(X3,X6) != X5 | k2_relat_1(X3) = X6 | ~r2_hidden(sK9(X3,X4,X5),k1_relat_1(X3)) | ~r2_hidden(sK3(X3,X6),X6) | ~v1_funct_1(X3) | ~v1_relat_1(X3) | ~r2_hidden(X5,k9_relat_1(X3,X4)) | ~v1_funct_1(X3) | ~v1_relat_1(X3)) )),
% 2.29/0.65    inference(superposition,[],[f49,f77])).
% 2.29/0.65  fof(f426,plain,(
% 2.29/0.65    ( ! [X0,X1] : (r2_hidden(sK3(X0,k9_relat_1(X0,X1)),k9_relat_1(X0,X1)) | ~r2_hidden(sK4(X0,k9_relat_1(X0,X1)),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k9_relat_1(X0,X1) = k2_relat_1(X0)) )),
% 2.29/0.65    inference(factoring,[],[f173])).
% 2.29/0.65  fof(f173,plain,(
% 2.29/0.65    ( ! [X2,X3,X1] : (r2_hidden(sK3(X1,X2),k9_relat_1(X1,X3)) | ~r2_hidden(sK4(X1,X2),X3) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | k2_relat_1(X1) = X2 | r2_hidden(sK3(X1,X2),X2)) )),
% 2.29/0.65    inference(subsumption_resolution,[],[f169,f47])).
% 2.29/0.65  fof(f169,plain,(
% 2.29/0.65    ( ! [X2,X3,X1] : (r2_hidden(sK3(X1,X2),k9_relat_1(X1,X3)) | ~r2_hidden(sK4(X1,X2),X3) | ~r2_hidden(sK4(X1,X2),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | k2_relat_1(X1) = X2 | r2_hidden(sK3(X1,X2),X2)) )),
% 2.29/0.65    inference(duplicate_literal_removal,[],[f164])).
% 2.29/0.65  fof(f164,plain,(
% 2.29/0.65    ( ! [X2,X3,X1] : (r2_hidden(sK3(X1,X2),k9_relat_1(X1,X3)) | ~r2_hidden(sK4(X1,X2),X3) | ~r2_hidden(sK4(X1,X2),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | k2_relat_1(X1) = X2 | r2_hidden(sK3(X1,X2),X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.29/0.65    inference(superposition,[],[f76,f48])).
% 2.29/0.65  fof(f76,plain,(
% 2.29/0.65    ( ! [X0,X7,X1] : (r2_hidden(k1_funct_1(X0,X7),k9_relat_1(X0,X1)) | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.29/0.65    inference(equality_resolution,[],[f75])).
% 2.29/0.65  fof(f75,plain,(
% 2.29/0.65    ( ! [X2,X0,X7,X1] : (r2_hidden(k1_funct_1(X0,X7),X2) | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.29/0.65    inference(equality_resolution,[],[f59])).
% 2.29/0.65  fof(f59,plain,(
% 2.29/0.65    ( ! [X6,X2,X0,X7,X1] : (r2_hidden(X6,X2) | k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.29/0.65    inference(cnf_transformation,[],[f38])).
% 2.29/0.65  fof(f91,plain,(
% 2.29/0.65    spl10_1),
% 2.29/0.65    inference(avatar_contradiction_clause,[],[f90])).
% 2.29/0.65  fof(f90,plain,(
% 2.29/0.65    $false | spl10_1),
% 2.29/0.65    inference(subsumption_resolution,[],[f82,f40])).
% 2.29/0.65  fof(f82,plain,(
% 2.29/0.65    ~v1_funct_1(sK2) | spl10_1),
% 2.29/0.65    inference(avatar_component_clause,[],[f81])).
% 2.29/0.65  fof(f81,plain,(
% 2.29/0.65    spl10_1 <=> v1_funct_1(sK2)),
% 2.29/0.65    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 2.29/0.65  fof(f89,plain,(
% 2.29/0.65    ~spl10_1 | ~spl10_2 | ~spl10_3),
% 2.29/0.65    inference(avatar_split_clause,[],[f43,f87,f84,f81])).
% 2.29/0.65  fof(f43,plain,(
% 2.29/0.65    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 2.29/0.65    inference(cnf_transformation,[],[f21])).
% 2.29/0.65  % SZS output end Proof for theBenchmark
% 2.29/0.65  % (13145)------------------------------
% 2.29/0.65  % (13145)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.29/0.65  % (13145)Termination reason: Refutation
% 2.29/0.65  
% 2.29/0.65  % (13145)Memory used [KB]: 11769
% 2.29/0.65  % (13145)Time elapsed: 0.213 s
% 2.29/0.65  % (13145)------------------------------
% 2.29/0.65  % (13145)------------------------------
% 2.29/0.66  % (13142)Success in time 0.287 s
%------------------------------------------------------------------------------
