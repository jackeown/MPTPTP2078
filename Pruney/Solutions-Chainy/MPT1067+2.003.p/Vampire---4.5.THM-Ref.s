%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:36 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 292 expanded)
%              Number of leaves         :   17 ( 119 expanded)
%              Depth                    :   19
%              Number of atoms          :  381 (1854 expanded)
%              Number of equality atoms :    9 (  12 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f169,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f125,f143,f168])).

fof(f168,plain,(
    spl5_9 ),
    inference(avatar_contradiction_clause,[],[f167])).

fof(f167,plain,
    ( $false
    | spl5_9 ),
    inference(subsumption_resolution,[],[f166,f106])).

fof(f106,plain,(
    r1_tarski(k3_tarski(sK3),sK0) ),
    inference(duplicate_literal_removal,[],[f104])).

fof(f104,plain,
    ( r1_tarski(k3_tarski(sK3),sK0)
    | r1_tarski(k3_tarski(sK3),sK0) ),
    inference(resolution,[],[f103,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK4(X0,X1),X1)
      | r1_tarski(k3_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ( ~ r1_tarski(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f17,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r1_tarski(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ? [X2] :
          ( ~ r1_tarski(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X2,X1) )
     => r1_tarski(k3_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_zfmisc_1)).

fof(f103,plain,(
    ! [X0] :
      ( r1_tarski(sK4(sK3,X0),sK0)
      | r1_tarski(k3_tarski(sK3),X0) ) ),
    inference(resolution,[],[f102,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(k3_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f102,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK3)
      | r1_tarski(X2,sK0) ) ),
    inference(resolution,[],[f86,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f86,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(sK0))
      | ~ r2_hidden(X0,sK3) ) ),
    inference(resolution,[],[f53,f40])).

fof(f40,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ~ r1_tarski(k5_setfam_1(sK0,sK3),k5_setfam_1(sK0,k6_funct_2(sK0,sK1,sK2,k7_funct_2(sK0,sK1,sK2,sK3))))
    & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2)
    & ~ v1_xboole_0(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f27,f26,f25,f24])).

fof(f24,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ r1_tarski(k5_setfam_1(X0,X3),k5_setfam_1(X0,k6_funct_2(X0,X1,X2,k7_funct_2(X0,X1,X2,X3))))
                    & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0))) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X2,X0,X1)
                & v1_funct_1(X2) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tarski(k5_setfam_1(sK0,X3),k5_setfam_1(sK0,k6_funct_2(sK0,X1,X2,k7_funct_2(sK0,X1,X2,X3))))
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
              & v1_funct_2(X2,sK0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ r1_tarski(k5_setfam_1(sK0,X3),k5_setfam_1(sK0,k6_funct_2(sK0,X1,X2,k7_funct_2(sK0,X1,X2,X3))))
                & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
            & v1_funct_2(X2,sK0,X1)
            & v1_funct_1(X2) )
        & ~ v1_xboole_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(k5_setfam_1(sK0,X3),k5_setfam_1(sK0,k6_funct_2(sK0,sK1,X2,k7_funct_2(sK0,sK1,X2,X3))))
              & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
          & v1_funct_2(X2,sK0,sK1)
          & v1_funct_1(X2) )
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ r1_tarski(k5_setfam_1(sK0,X3),k5_setfam_1(sK0,k6_funct_2(sK0,sK1,X2,k7_funct_2(sK0,sK1,X2,X3))))
            & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        & v1_funct_2(X2,sK0,sK1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ~ r1_tarski(k5_setfam_1(sK0,X3),k5_setfam_1(sK0,k6_funct_2(sK0,sK1,sK2,k7_funct_2(sK0,sK1,sK2,X3))))
          & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X3] :
        ( ~ r1_tarski(k5_setfam_1(sK0,X3),k5_setfam_1(sK0,k6_funct_2(sK0,sK1,sK2,k7_funct_2(sK0,sK1,sK2,X3))))
        & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
   => ( ~ r1_tarski(k5_setfam_1(sK0,sK3),k5_setfam_1(sK0,k6_funct_2(sK0,sK1,sK2,k7_funct_2(sK0,sK1,sK2,sK3))))
      & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tarski(k5_setfam_1(X0,X3),k5_setfam_1(X0,k6_funct_2(X0,X1,X2,k7_funct_2(X0,X1,X2,X3))))
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tarski(k5_setfam_1(X0,X3),k5_setfam_1(X0,k6_funct_2(X0,X1,X2,k7_funct_2(X0,X1,X2,X3))))
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_2(X2,X0,X1)
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0)))
                   => r1_tarski(k5_setfam_1(X0,X3),k5_setfam_1(X0,k6_funct_2(X0,X1,X2,k7_funct_2(X0,X1,X2,X3)))) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X2,X0,X1)
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0)))
                 => r1_tarski(k5_setfam_1(X0,X3),k5_setfam_1(X0,k6_funct_2(X0,X1,X2,k7_funct_2(X0,X1,X2,X3)))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t184_funct_2)).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f166,plain,
    ( ~ r1_tarski(k3_tarski(sK3),sK0)
    | spl5_9 ),
    inference(resolution,[],[f164,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f164,plain,
    ( ~ m1_subset_1(k3_tarski(sK3),k1_zfmisc_1(sK0))
    | spl5_9 ),
    inference(subsumption_resolution,[],[f163,f35])).

fof(f35,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f163,plain,
    ( ~ m1_subset_1(k3_tarski(sK3),k1_zfmisc_1(sK0))
    | v1_xboole_0(sK0)
    | spl5_9 ),
    inference(subsumption_resolution,[],[f162,f36])).

fof(f36,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f162,plain,
    ( ~ m1_subset_1(k3_tarski(sK3),k1_zfmisc_1(sK0))
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl5_9 ),
    inference(subsumption_resolution,[],[f161,f37])).

fof(f37,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f161,plain,
    ( ~ m1_subset_1(k3_tarski(sK3),k1_zfmisc_1(sK0))
    | ~ v1_funct_1(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl5_9 ),
    inference(subsumption_resolution,[],[f160,f38])).

fof(f38,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f160,plain,
    ( ~ m1_subset_1(k3_tarski(sK3),k1_zfmisc_1(sK0))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl5_9 ),
    inference(subsumption_resolution,[],[f159,f39])).

fof(f39,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f28])).

fof(f159,plain,
    ( ~ m1_subset_1(k3_tarski(sK3),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl5_9 ),
    inference(subsumption_resolution,[],[f158,f40])).

fof(f158,plain,
    ( ~ m1_subset_1(k3_tarski(sK3),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl5_9 ),
    inference(subsumption_resolution,[],[f157,f59])).

fof(f59,plain,(
    ! [X2] : m1_setfam_1(X2,k3_tarski(X2)) ),
    inference(resolution,[],[f50,f56])).

fof(f56,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k3_tarski(X1))
      | m1_setfam_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_setfam_1(X1,X0)
        | ~ r1_tarski(X0,k3_tarski(X1)) )
      & ( r1_tarski(X0,k3_tarski(X1))
        | ~ m1_setfam_1(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_setfam_1(X1,X0)
    <=> r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_setfam_1)).

fof(f157,plain,
    ( ~ m1_setfam_1(sK3,k3_tarski(sK3))
    | ~ m1_subset_1(k3_tarski(sK3),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl5_9 ),
    inference(resolution,[],[f42,f156])).

fof(f156,plain,
    ( ~ m1_setfam_1(k6_funct_2(sK0,sK1,sK2,k7_funct_2(sK0,sK1,sK2,sK3)),k3_tarski(sK3))
    | spl5_9 ),
    inference(resolution,[],[f124,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ m1_setfam_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f124,plain,
    ( ~ r1_tarski(k3_tarski(sK3),k3_tarski(k6_funct_2(sK0,sK1,sK2,k7_funct_2(sK0,sK1,sK2,sK3))))
    | spl5_9 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl5_9
  <=> r1_tarski(k3_tarski(sK3),k3_tarski(k6_funct_2(sK0,sK1,sK2,k7_funct_2(sK0,sK1,sK2,sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f42,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_setfam_1(k6_funct_2(X0,X1,X2,k7_funct_2(X0,X1,X2,X3)),X4)
      | ~ m1_setfam_1(X3,X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( m1_setfam_1(k6_funct_2(X0,X1,X2,k7_funct_2(X0,X1,X2,X3)),X4)
                      | ~ m1_setfam_1(X3,X4)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(X0)) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X2,X0,X1)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( m1_setfam_1(k6_funct_2(X0,X1,X2,k7_funct_2(X0,X1,X2,X3)),X4)
                      | ~ m1_setfam_1(X3,X4)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(X0)) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X2,X0,X1)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X2,X0,X1)
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0)))
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(X0))
                     => ( m1_setfam_1(X3,X4)
                       => m1_setfam_1(k6_funct_2(X0,X1,X2,k7_funct_2(X0,X1,X2,X3)),X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_funct_2)).

fof(f143,plain,(
    spl5_5 ),
    inference(avatar_contradiction_clause,[],[f142])).

fof(f142,plain,
    ( $false
    | spl5_5 ),
    inference(subsumption_resolution,[],[f141,f35])).

fof(f141,plain,
    ( v1_xboole_0(sK0)
    | spl5_5 ),
    inference(subsumption_resolution,[],[f140,f36])).

fof(f140,plain,
    ( v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl5_5 ),
    inference(subsumption_resolution,[],[f139,f37])).

fof(f139,plain,
    ( ~ v1_funct_1(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl5_5 ),
    inference(subsumption_resolution,[],[f138,f38])).

fof(f138,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl5_5 ),
    inference(subsumption_resolution,[],[f137,f39])).

fof(f137,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl5_5 ),
    inference(subsumption_resolution,[],[f135,f40])).

fof(f135,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl5_5 ),
    inference(resolution,[],[f134,f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k7_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_funct_2)).

fof(f134,plain,
    ( ~ m1_subset_1(k7_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k1_zfmisc_1(sK1)))
    | spl5_5 ),
    inference(subsumption_resolution,[],[f133,f35])).

fof(f133,plain,
    ( ~ m1_subset_1(k7_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k1_zfmisc_1(sK1)))
    | v1_xboole_0(sK0)
    | spl5_5 ),
    inference(subsumption_resolution,[],[f132,f36])).

fof(f132,plain,
    ( ~ m1_subset_1(k7_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k1_zfmisc_1(sK1)))
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl5_5 ),
    inference(subsumption_resolution,[],[f131,f37])).

fof(f131,plain,
    ( ~ m1_subset_1(k7_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k1_zfmisc_1(sK1)))
    | ~ v1_funct_1(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl5_5 ),
    inference(subsumption_resolution,[],[f130,f38])).

fof(f130,plain,
    ( ~ m1_subset_1(k7_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k1_zfmisc_1(sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl5_5 ),
    inference(subsumption_resolution,[],[f127,f39])).

fof(f127,plain,
    ( ~ m1_subset_1(k7_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k1_zfmisc_1(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl5_5 ),
    inference(resolution,[],[f55,f95])).

fof(f95,plain,
    ( ~ m1_subset_1(k6_funct_2(sK0,sK1,sK2,k7_funct_2(sK0,sK1,sK2,sK3)),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl5_5 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl5_5
  <=> m1_subset_1(k6_funct_2(sK0,sK1,sK2,k7_funct_2(sK0,sK1,sK2,sK3)),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k6_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k6_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k6_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_funct_2)).

fof(f125,plain,
    ( ~ spl5_5
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f120,f122,f93])).

fof(f120,plain,
    ( ~ r1_tarski(k3_tarski(sK3),k3_tarski(k6_funct_2(sK0,sK1,sK2,k7_funct_2(sK0,sK1,sK2,sK3))))
    | ~ m1_subset_1(k6_funct_2(sK0,sK1,sK2,k7_funct_2(sK0,sK1,sK2,sK3)),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(superposition,[],[f91,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k3_tarski(X1) = k5_setfam_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_tarski(X1) = k5_setfam_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k3_tarski(X1) = k5_setfam_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

fof(f91,plain,(
    ~ r1_tarski(k3_tarski(sK3),k5_setfam_1(sK0,k6_funct_2(sK0,sK1,sK2,k7_funct_2(sK0,sK1,sK2,sK3)))) ),
    inference(subsumption_resolution,[],[f89,f40])).

fof(f89,plain,
    ( ~ r1_tarski(k3_tarski(sK3),k5_setfam_1(sK0,k6_funct_2(sK0,sK1,sK2,k7_funct_2(sK0,sK1,sK2,sK3))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(superposition,[],[f41,f43])).

fof(f41,plain,(
    ~ r1_tarski(k5_setfam_1(sK0,sK3),k5_setfam_1(sK0,k6_funct_2(sK0,sK1,sK2,k7_funct_2(sK0,sK1,sK2,sK3)))) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n016.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:08:04 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.46  % (9963)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.19/0.47  % (9953)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.19/0.47  % (9952)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.19/0.48  % (9951)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.49  % (9955)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.19/0.49  % (9969)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.19/0.49  % (9964)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.19/0.49  % (9962)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.19/0.49  % (9973)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.19/0.49  % (9966)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.19/0.49  % (9965)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.19/0.49  % (9950)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.19/0.50  % (9960)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.19/0.50  % (9968)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.19/0.50  % (9957)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.19/0.50  % (9970)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.19/0.50  % (9958)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.19/0.50  % (9961)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.19/0.51  % (9954)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.19/0.51  % (9954)Refutation found. Thanks to Tanya!
% 0.19/0.51  % SZS status Theorem for theBenchmark
% 0.19/0.51  % SZS output start Proof for theBenchmark
% 0.19/0.51  fof(f169,plain,(
% 0.19/0.51    $false),
% 0.19/0.51    inference(avatar_sat_refutation,[],[f125,f143,f168])).
% 0.19/0.51  fof(f168,plain,(
% 0.19/0.51    spl5_9),
% 0.19/0.51    inference(avatar_contradiction_clause,[],[f167])).
% 0.19/0.51  fof(f167,plain,(
% 0.19/0.51    $false | spl5_9),
% 0.19/0.51    inference(subsumption_resolution,[],[f166,f106])).
% 0.19/0.51  fof(f106,plain,(
% 0.19/0.51    r1_tarski(k3_tarski(sK3),sK0)),
% 0.19/0.51    inference(duplicate_literal_removal,[],[f104])).
% 0.19/0.51  fof(f104,plain,(
% 0.19/0.51    r1_tarski(k3_tarski(sK3),sK0) | r1_tarski(k3_tarski(sK3),sK0)),
% 0.19/0.51    inference(resolution,[],[f103,f45])).
% 0.19/0.51  fof(f45,plain,(
% 0.19/0.51    ( ! [X0,X1] : (~r1_tarski(sK4(X0,X1),X1) | r1_tarski(k3_tarski(X0),X1)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f30])).
% 0.19/0.51  fof(f30,plain,(
% 0.19/0.51    ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | (~r1_tarski(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.19/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f17,f29])).
% 0.19/0.51  fof(f29,plain,(
% 0.19/0.51    ! [X1,X0] : (? [X2] : (~r1_tarski(X2,X1) & r2_hidden(X2,X0)) => (~r1_tarski(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.19/0.51    introduced(choice_axiom,[])).
% 0.19/0.51  fof(f17,plain,(
% 0.19/0.51    ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | ? [X2] : (~r1_tarski(X2,X1) & r2_hidden(X2,X0)))),
% 0.19/0.51    inference(ennf_transformation,[],[f2])).
% 0.19/0.51  fof(f2,axiom,(
% 0.19/0.51    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X2,X1)) => r1_tarski(k3_tarski(X0),X1))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_zfmisc_1)).
% 0.19/0.51  fof(f103,plain,(
% 0.19/0.51    ( ! [X0] : (r1_tarski(sK4(sK3,X0),sK0) | r1_tarski(k3_tarski(sK3),X0)) )),
% 0.19/0.51    inference(resolution,[],[f102,f44])).
% 0.19/0.51  fof(f44,plain,(
% 0.19/0.51    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(k3_tarski(X0),X1)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f30])).
% 0.19/0.51  fof(f102,plain,(
% 0.19/0.51    ( ! [X2] : (~r2_hidden(X2,sK3) | r1_tarski(X2,sK0)) )),
% 0.19/0.51    inference(resolution,[],[f86,f51])).
% 0.19/0.51  fof(f51,plain,(
% 0.19/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f34])).
% 0.19/0.51  fof(f34,plain,(
% 0.19/0.51    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.19/0.51    inference(nnf_transformation,[],[f5])).
% 0.19/0.51  fof(f5,axiom,(
% 0.19/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.19/0.51  fof(f86,plain,(
% 0.19/0.51    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~r2_hidden(X0,sK3)) )),
% 0.19/0.51    inference(resolution,[],[f53,f40])).
% 0.19/0.51  fof(f40,plain,(
% 0.19/0.51    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.19/0.51    inference(cnf_transformation,[],[f28])).
% 0.19/0.51  fof(f28,plain,(
% 0.19/0.51    (((~r1_tarski(k5_setfam_1(sK0,sK3),k5_setfam_1(sK0,k6_funct_2(sK0,sK1,sK2,k7_funct_2(sK0,sK1,sK2,sK3)))) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK0)))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 0.19/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f27,f26,f25,f24])).
% 0.19/0.51  fof(f24,plain,(
% 0.19/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_tarski(k5_setfam_1(X0,X3),k5_setfam_1(X0,k6_funct_2(X0,X1,X2,k7_funct_2(X0,X1,X2,X3)))) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~r1_tarski(k5_setfam_1(sK0,X3),k5_setfam_1(sK0,k6_funct_2(sK0,X1,X2,k7_funct_2(sK0,X1,X2,X3)))) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) & v1_funct_2(X2,sK0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 0.19/0.51    introduced(choice_axiom,[])).
% 0.19/0.51  fof(f25,plain,(
% 0.19/0.51    ? [X1] : (? [X2] : (? [X3] : (~r1_tarski(k5_setfam_1(sK0,X3),k5_setfam_1(sK0,k6_funct_2(sK0,X1,X2,k7_funct_2(sK0,X1,X2,X3)))) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) & v1_funct_2(X2,sK0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (~r1_tarski(k5_setfam_1(sK0,X3),k5_setfam_1(sK0,k6_funct_2(sK0,sK1,X2,k7_funct_2(sK0,sK1,X2,X3)))) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X2,sK0,sK1) & v1_funct_1(X2)) & ~v1_xboole_0(sK1))),
% 0.19/0.51    introduced(choice_axiom,[])).
% 0.19/0.51  fof(f26,plain,(
% 0.19/0.51    ? [X2] : (? [X3] : (~r1_tarski(k5_setfam_1(sK0,X3),k5_setfam_1(sK0,k6_funct_2(sK0,sK1,X2,k7_funct_2(sK0,sK1,X2,X3)))) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X2,sK0,sK1) & v1_funct_1(X2)) => (? [X3] : (~r1_tarski(k5_setfam_1(sK0,X3),k5_setfam_1(sK0,k6_funct_2(sK0,sK1,sK2,k7_funct_2(sK0,sK1,sK2,X3)))) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(sK0)))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 0.19/0.51    introduced(choice_axiom,[])).
% 0.19/0.51  fof(f27,plain,(
% 0.19/0.51    ? [X3] : (~r1_tarski(k5_setfam_1(sK0,X3),k5_setfam_1(sK0,k6_funct_2(sK0,sK1,sK2,k7_funct_2(sK0,sK1,sK2,X3)))) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(sK0)))) => (~r1_tarski(k5_setfam_1(sK0,sK3),k5_setfam_1(sK0,k6_funct_2(sK0,sK1,sK2,k7_funct_2(sK0,sK1,sK2,sK3)))) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 0.19/0.51    introduced(choice_axiom,[])).
% 0.19/0.51  fof(f13,plain,(
% 0.19/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_tarski(k5_setfam_1(X0,X3),k5_setfam_1(X0,k6_funct_2(X0,X1,X2,k7_funct_2(X0,X1,X2,X3)))) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.19/0.51    inference(flattening,[],[f12])).
% 0.19/0.51  fof(f12,plain,(
% 0.19/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_tarski(k5_setfam_1(X0,X3),k5_setfam_1(X0,k6_funct_2(X0,X1,X2,k7_funct_2(X0,X1,X2,X3)))) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0)))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.19/0.51    inference(ennf_transformation,[],[f11])).
% 0.19/0.51  fof(f11,negated_conjecture,(
% 0.19/0.51    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0))) => r1_tarski(k5_setfam_1(X0,X3),k5_setfam_1(X0,k6_funct_2(X0,X1,X2,k7_funct_2(X0,X1,X2,X3))))))))),
% 0.19/0.51    inference(negated_conjecture,[],[f10])).
% 0.19/0.51  fof(f10,conjecture,(
% 0.19/0.51    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0))) => r1_tarski(k5_setfam_1(X0,X3),k5_setfam_1(X0,k6_funct_2(X0,X1,X2,k7_funct_2(X0,X1,X2,X3))))))))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t184_funct_2)).
% 0.19/0.51  fof(f53,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f19])).
% 0.19/0.51  fof(f19,plain,(
% 0.19/0.51    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.19/0.51    inference(flattening,[],[f18])).
% 0.19/0.51  fof(f18,plain,(
% 0.19/0.51    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.19/0.51    inference(ennf_transformation,[],[f6])).
% 0.19/0.51  fof(f6,axiom,(
% 0.19/0.51    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 0.19/0.51  fof(f166,plain,(
% 0.19/0.51    ~r1_tarski(k3_tarski(sK3),sK0) | spl5_9),
% 0.19/0.51    inference(resolution,[],[f164,f52])).
% 0.19/0.51  fof(f52,plain,(
% 0.19/0.51    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f34])).
% 0.19/0.51  fof(f164,plain,(
% 0.19/0.51    ~m1_subset_1(k3_tarski(sK3),k1_zfmisc_1(sK0)) | spl5_9),
% 0.19/0.51    inference(subsumption_resolution,[],[f163,f35])).
% 0.19/0.51  fof(f35,plain,(
% 0.19/0.51    ~v1_xboole_0(sK0)),
% 0.19/0.51    inference(cnf_transformation,[],[f28])).
% 0.19/0.51  fof(f163,plain,(
% 0.19/0.51    ~m1_subset_1(k3_tarski(sK3),k1_zfmisc_1(sK0)) | v1_xboole_0(sK0) | spl5_9),
% 0.19/0.51    inference(subsumption_resolution,[],[f162,f36])).
% 0.19/0.51  fof(f36,plain,(
% 0.19/0.51    ~v1_xboole_0(sK1)),
% 0.19/0.51    inference(cnf_transformation,[],[f28])).
% 0.19/0.51  fof(f162,plain,(
% 0.19/0.51    ~m1_subset_1(k3_tarski(sK3),k1_zfmisc_1(sK0)) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | spl5_9),
% 0.19/0.51    inference(subsumption_resolution,[],[f161,f37])).
% 0.19/0.51  fof(f37,plain,(
% 0.19/0.51    v1_funct_1(sK2)),
% 0.19/0.51    inference(cnf_transformation,[],[f28])).
% 0.19/0.51  fof(f161,plain,(
% 0.19/0.51    ~m1_subset_1(k3_tarski(sK3),k1_zfmisc_1(sK0)) | ~v1_funct_1(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | spl5_9),
% 0.19/0.51    inference(subsumption_resolution,[],[f160,f38])).
% 0.19/0.51  fof(f38,plain,(
% 0.19/0.51    v1_funct_2(sK2,sK0,sK1)),
% 0.19/0.51    inference(cnf_transformation,[],[f28])).
% 0.19/0.51  fof(f160,plain,(
% 0.19/0.51    ~m1_subset_1(k3_tarski(sK3),k1_zfmisc_1(sK0)) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | spl5_9),
% 0.19/0.51    inference(subsumption_resolution,[],[f159,f39])).
% 0.19/0.51  fof(f39,plain,(
% 0.19/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.19/0.51    inference(cnf_transformation,[],[f28])).
% 0.19/0.51  fof(f159,plain,(
% 0.19/0.51    ~m1_subset_1(k3_tarski(sK3),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | spl5_9),
% 0.19/0.51    inference(subsumption_resolution,[],[f158,f40])).
% 0.19/0.51  fof(f158,plain,(
% 0.19/0.51    ~m1_subset_1(k3_tarski(sK3),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | spl5_9),
% 0.19/0.51    inference(subsumption_resolution,[],[f157,f59])).
% 0.19/0.51  fof(f59,plain,(
% 0.19/0.51    ( ! [X2] : (m1_setfam_1(X2,k3_tarski(X2))) )),
% 0.19/0.51    inference(resolution,[],[f50,f56])).
% 0.19/0.51  fof(f56,plain,(
% 0.19/0.51    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.19/0.51    inference(equality_resolution,[],[f47])).
% 0.19/0.51  fof(f47,plain,(
% 0.19/0.51    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.19/0.51    inference(cnf_transformation,[],[f32])).
% 0.19/0.51  fof(f32,plain,(
% 0.19/0.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.19/0.51    inference(flattening,[],[f31])).
% 0.19/0.51  fof(f31,plain,(
% 0.19/0.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.19/0.51    inference(nnf_transformation,[],[f1])).
% 0.19/0.51  fof(f1,axiom,(
% 0.19/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.19/0.51  fof(f50,plain,(
% 0.19/0.51    ( ! [X0,X1] : (~r1_tarski(X0,k3_tarski(X1)) | m1_setfam_1(X1,X0)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f33])).
% 0.19/0.51  fof(f33,plain,(
% 0.19/0.51    ! [X0,X1] : ((m1_setfam_1(X1,X0) | ~r1_tarski(X0,k3_tarski(X1))) & (r1_tarski(X0,k3_tarski(X1)) | ~m1_setfam_1(X1,X0)))),
% 0.19/0.51    inference(nnf_transformation,[],[f3])).
% 0.19/0.51  fof(f3,axiom,(
% 0.19/0.51    ! [X0,X1] : (m1_setfam_1(X1,X0) <=> r1_tarski(X0,k3_tarski(X1)))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_setfam_1)).
% 0.19/0.51  fof(f157,plain,(
% 0.19/0.51    ~m1_setfam_1(sK3,k3_tarski(sK3)) | ~m1_subset_1(k3_tarski(sK3),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | spl5_9),
% 0.19/0.51    inference(resolution,[],[f42,f156])).
% 0.19/0.51  fof(f156,plain,(
% 0.19/0.51    ~m1_setfam_1(k6_funct_2(sK0,sK1,sK2,k7_funct_2(sK0,sK1,sK2,sK3)),k3_tarski(sK3)) | spl5_9),
% 0.19/0.51    inference(resolution,[],[f124,f49])).
% 0.19/0.51  fof(f49,plain,(
% 0.19/0.51    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~m1_setfam_1(X1,X0)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f33])).
% 0.19/0.51  fof(f124,plain,(
% 0.19/0.51    ~r1_tarski(k3_tarski(sK3),k3_tarski(k6_funct_2(sK0,sK1,sK2,k7_funct_2(sK0,sK1,sK2,sK3)))) | spl5_9),
% 0.19/0.51    inference(avatar_component_clause,[],[f122])).
% 0.19/0.51  fof(f122,plain,(
% 0.19/0.51    spl5_9 <=> r1_tarski(k3_tarski(sK3),k3_tarski(k6_funct_2(sK0,sK1,sK2,k7_funct_2(sK0,sK1,sK2,sK3))))),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.19/0.51  fof(f42,plain,(
% 0.19/0.51    ( ! [X4,X2,X0,X3,X1] : (m1_setfam_1(k6_funct_2(X0,X1,X2,k7_funct_2(X0,X1,X2,X3)),X4) | ~m1_setfam_1(X3,X4) | ~m1_subset_1(X4,k1_zfmisc_1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f15])).
% 0.19/0.51  fof(f15,plain,(
% 0.19/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (m1_setfam_1(k6_funct_2(X0,X1,X2,k7_funct_2(X0,X1,X2,X3)),X4) | ~m1_setfam_1(X3,X4) | ~m1_subset_1(X4,k1_zfmisc_1(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.19/0.51    inference(flattening,[],[f14])).
% 0.19/0.51  fof(f14,plain,(
% 0.19/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((m1_setfam_1(k6_funct_2(X0,X1,X2,k7_funct_2(X0,X1,X2,X3)),X4) | ~m1_setfam_1(X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0)))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.19/0.51    inference(ennf_transformation,[],[f9])).
% 0.19/0.51  fof(f9,axiom,(
% 0.19/0.51    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X0)) => (m1_setfam_1(X3,X4) => m1_setfam_1(k6_funct_2(X0,X1,X2,k7_funct_2(X0,X1,X2,X3)),X4)))))))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_funct_2)).
% 0.19/0.51  fof(f143,plain,(
% 0.19/0.51    spl5_5),
% 0.19/0.51    inference(avatar_contradiction_clause,[],[f142])).
% 0.19/0.51  fof(f142,plain,(
% 0.19/0.51    $false | spl5_5),
% 0.19/0.51    inference(subsumption_resolution,[],[f141,f35])).
% 0.19/0.51  fof(f141,plain,(
% 0.19/0.51    v1_xboole_0(sK0) | spl5_5),
% 0.19/0.51    inference(subsumption_resolution,[],[f140,f36])).
% 0.19/0.51  fof(f140,plain,(
% 0.19/0.51    v1_xboole_0(sK1) | v1_xboole_0(sK0) | spl5_5),
% 0.19/0.51    inference(subsumption_resolution,[],[f139,f37])).
% 0.19/0.51  fof(f139,plain,(
% 0.19/0.51    ~v1_funct_1(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | spl5_5),
% 0.19/0.51    inference(subsumption_resolution,[],[f138,f38])).
% 0.19/0.51  fof(f138,plain,(
% 0.19/0.51    ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | spl5_5),
% 0.19/0.51    inference(subsumption_resolution,[],[f137,f39])).
% 0.19/0.51  fof(f137,plain,(
% 0.19/0.51    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | spl5_5),
% 0.19/0.51    inference(subsumption_resolution,[],[f135,f40])).
% 0.19/0.51  fof(f135,plain,(
% 0.19/0.51    ~m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | spl5_5),
% 0.19/0.51    inference(resolution,[],[f134,f54])).
% 0.19/0.51  fof(f54,plain,(
% 0.19/0.51    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f21])).
% 0.19/0.51  fof(f21,plain,(
% 0.19/0.51    ! [X0,X1,X2,X3] : (m1_subset_1(k7_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 0.19/0.51    inference(flattening,[],[f20])).
% 0.19/0.51  fof(f20,plain,(
% 0.19/0.51    ! [X0,X1,X2,X3] : (m1_subset_1(k7_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 0.19/0.51    inference(ennf_transformation,[],[f8])).
% 0.19/0.51  fof(f8,axiom,(
% 0.19/0.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => m1_subset_1(k7_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X1))))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_funct_2)).
% 0.19/0.51  fof(f134,plain,(
% 0.19/0.51    ~m1_subset_1(k7_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k1_zfmisc_1(sK1))) | spl5_5),
% 0.19/0.51    inference(subsumption_resolution,[],[f133,f35])).
% 0.19/0.51  fof(f133,plain,(
% 0.19/0.51    ~m1_subset_1(k7_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k1_zfmisc_1(sK1))) | v1_xboole_0(sK0) | spl5_5),
% 0.19/0.51    inference(subsumption_resolution,[],[f132,f36])).
% 0.19/0.51  fof(f132,plain,(
% 0.19/0.51    ~m1_subset_1(k7_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k1_zfmisc_1(sK1))) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | spl5_5),
% 0.19/0.51    inference(subsumption_resolution,[],[f131,f37])).
% 0.19/0.51  fof(f131,plain,(
% 0.19/0.51    ~m1_subset_1(k7_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k1_zfmisc_1(sK1))) | ~v1_funct_1(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | spl5_5),
% 0.19/0.51    inference(subsumption_resolution,[],[f130,f38])).
% 0.19/0.51  fof(f130,plain,(
% 0.19/0.51    ~m1_subset_1(k7_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k1_zfmisc_1(sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | spl5_5),
% 0.19/0.51    inference(subsumption_resolution,[],[f127,f39])).
% 0.19/0.51  fof(f127,plain,(
% 0.19/0.51    ~m1_subset_1(k7_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k1_zfmisc_1(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | spl5_5),
% 0.19/0.51    inference(resolution,[],[f55,f95])).
% 0.19/0.51  fof(f95,plain,(
% 0.19/0.51    ~m1_subset_1(k6_funct_2(sK0,sK1,sK2,k7_funct_2(sK0,sK1,sK2,sK3)),k1_zfmisc_1(k1_zfmisc_1(sK0))) | spl5_5),
% 0.19/0.51    inference(avatar_component_clause,[],[f93])).
% 0.19/0.51  fof(f93,plain,(
% 0.19/0.51    spl5_5 <=> m1_subset_1(k6_funct_2(sK0,sK1,sK2,k7_funct_2(sK0,sK1,sK2,sK3)),k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.19/0.51  fof(f55,plain,(
% 0.19/0.51    ( ! [X2,X0,X3,X1] : (m1_subset_1(k6_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f23])).
% 0.19/0.51  fof(f23,plain,(
% 0.19/0.51    ! [X0,X1,X2,X3] : (m1_subset_1(k6_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 0.19/0.51    inference(flattening,[],[f22])).
% 0.19/0.51  fof(f22,plain,(
% 0.19/0.51    ! [X0,X1,X2,X3] : (m1_subset_1(k6_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 0.19/0.51    inference(ennf_transformation,[],[f7])).
% 0.19/0.51  fof(f7,axiom,(
% 0.19/0.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => m1_subset_1(k6_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_funct_2)).
% 0.19/0.51  fof(f125,plain,(
% 0.19/0.51    ~spl5_5 | ~spl5_9),
% 0.19/0.51    inference(avatar_split_clause,[],[f120,f122,f93])).
% 0.19/0.51  fof(f120,plain,(
% 0.19/0.51    ~r1_tarski(k3_tarski(sK3),k3_tarski(k6_funct_2(sK0,sK1,sK2,k7_funct_2(sK0,sK1,sK2,sK3)))) | ~m1_subset_1(k6_funct_2(sK0,sK1,sK2,k7_funct_2(sK0,sK1,sK2,sK3)),k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.19/0.51    inference(superposition,[],[f91,f43])).
% 0.19/0.51  fof(f43,plain,(
% 0.19/0.51    ( ! [X0,X1] : (k3_tarski(X1) = k5_setfam_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.19/0.51    inference(cnf_transformation,[],[f16])).
% 0.19/0.51  fof(f16,plain,(
% 0.19/0.51    ! [X0,X1] : (k3_tarski(X1) = k5_setfam_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.19/0.51    inference(ennf_transformation,[],[f4])).
% 0.19/0.51  fof(f4,axiom,(
% 0.19/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k3_tarski(X1) = k5_setfam_1(X0,X1))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).
% 0.19/0.51  fof(f91,plain,(
% 0.19/0.51    ~r1_tarski(k3_tarski(sK3),k5_setfam_1(sK0,k6_funct_2(sK0,sK1,sK2,k7_funct_2(sK0,sK1,sK2,sK3))))),
% 0.19/0.51    inference(subsumption_resolution,[],[f89,f40])).
% 0.19/0.51  fof(f89,plain,(
% 0.19/0.51    ~r1_tarski(k3_tarski(sK3),k5_setfam_1(sK0,k6_funct_2(sK0,sK1,sK2,k7_funct_2(sK0,sK1,sK2,sK3)))) | ~m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.19/0.51    inference(superposition,[],[f41,f43])).
% 0.19/0.51  fof(f41,plain,(
% 0.19/0.51    ~r1_tarski(k5_setfam_1(sK0,sK3),k5_setfam_1(sK0,k6_funct_2(sK0,sK1,sK2,k7_funct_2(sK0,sK1,sK2,sK3))))),
% 0.19/0.51    inference(cnf_transformation,[],[f28])).
% 0.19/0.51  % SZS output end Proof for theBenchmark
% 0.19/0.51  % (9954)------------------------------
% 0.19/0.51  % (9954)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (9954)Termination reason: Refutation
% 0.19/0.51  
% 0.19/0.51  % (9954)Memory used [KB]: 6268
% 0.19/0.51  % (9954)Time elapsed: 0.107 s
% 0.19/0.51  % (9954)------------------------------
% 0.19/0.51  % (9954)------------------------------
% 0.19/0.51  % (9956)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.19/0.51  % (9949)Success in time 0.164 s
%------------------------------------------------------------------------------
