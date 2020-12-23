%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1053+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:10 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 374 expanded)
%              Number of leaves         :   19 ( 124 expanded)
%              Depth                    :   20
%              Number of atoms          :  455 (1648 expanded)
%              Number of equality atoms :   62 ( 302 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f179,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f90,f118,f123,f133,f149,f165,f178])).

fof(f178,plain,
    ( spl5_2
    | ~ spl5_6 ),
    inference(avatar_contradiction_clause,[],[f177])).

fof(f177,plain,
    ( $false
    | spl5_2
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f176,f30])).

fof(f30,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ! [X2] :
        ( ( k11_relat_1(X2,sK2(X2)) != k1_funct_1(sK1,sK2(X2))
          & r2_hidden(sK2(X2),sK0) )
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) )
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,k9_setfam_1(sK0))))
    & v1_funct_2(sK1,sK0,k9_setfam_1(sK0))
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f24,f23])).

fof(f23,plain,
    ( ? [X0,X1] :
        ( ! [X2] :
            ( ? [X3] :
                ( k11_relat_1(X2,X3) != k1_funct_1(X1,X3)
                & r2_hidden(X3,X0) )
            | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k9_setfam_1(X0))))
        & v1_funct_2(X1,X0,k9_setfam_1(X0))
        & v1_funct_1(X1) )
   => ( ! [X2] :
          ( ? [X3] :
              ( k11_relat_1(X2,X3) != k1_funct_1(sK1,X3)
              & r2_hidden(X3,sK0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,k9_setfam_1(sK0))))
      & v1_funct_2(sK1,sK0,k9_setfam_1(sK0))
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X2] :
      ( ? [X3] :
          ( k11_relat_1(X2,X3) != k1_funct_1(sK1,X3)
          & r2_hidden(X3,sK0) )
     => ( k11_relat_1(X2,sK2(X2)) != k1_funct_1(sK1,sK2(X2))
        & r2_hidden(sK2(X2),sK0) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ? [X3] :
              ( k11_relat_1(X2,X3) != k1_funct_1(X1,X3)
              & r2_hidden(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k9_setfam_1(X0))))
      & v1_funct_2(X1,X0,k9_setfam_1(X0))
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ? [X3] :
              ( k11_relat_1(X2,X3) != k1_funct_1(X1,X3)
              & r2_hidden(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k9_setfam_1(X0))))
      & v1_funct_2(X1,X0,k9_setfam_1(X0))
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k9_setfam_1(X0))))
          & v1_funct_2(X1,X0,k9_setfam_1(X0))
          & v1_funct_1(X1) )
       => ? [X2] :
            ( ! [X3] :
                ( r2_hidden(X3,X0)
               => k11_relat_1(X2,X3) = k1_funct_1(X1,X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k9_setfam_1(X0))))
        & v1_funct_2(X1,X0,k9_setfam_1(X0))
        & v1_funct_1(X1) )
     => ? [X2] :
          ( ! [X3] :
              ( r2_hidden(X3,X0)
             => k11_relat_1(X2,X3) = k1_funct_1(X1,X3) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t170_funct_2)).

fof(f176,plain,
    ( ~ v1_funct_1(sK1)
    | spl5_2
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f175,f31])).

fof(f31,plain,(
    v1_funct_2(sK1,sK0,k9_setfam_1(sK0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f175,plain,
    ( ~ v1_funct_2(sK1,sK0,k9_setfam_1(sK0))
    | ~ v1_funct_1(sK1)
    | spl5_2
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f174,f51])).

fof(f51,plain,(
    m1_subset_1(sK1,k9_setfam_1(k2_zfmisc_1(sK0,k9_setfam_1(sK0)))) ),
    inference(definition_unfolding,[],[f32,f38])).

fof(f38,plain,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

fof(f32,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,k9_setfam_1(sK0)))) ),
    inference(cnf_transformation,[],[f25])).

fof(f174,plain,
    ( ~ m1_subset_1(sK1,k9_setfam_1(k2_zfmisc_1(sK0,k9_setfam_1(sK0))))
    | ~ v1_funct_2(sK1,sK0,k9_setfam_1(sK0))
    | ~ v1_funct_1(sK1)
    | spl5_2
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f173,f88])).

fof(f88,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1),k9_setfam_1(k2_zfmisc_1(sK0,sK0)))
    | spl5_2 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl5_2
  <=> m1_subset_1(sK3(sK0,sK1),k9_setfam_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f173,plain,
    ( m1_subset_1(sK3(sK0,sK1),k9_setfam_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK1,k9_setfam_1(k2_zfmisc_1(sK0,k9_setfam_1(sK0))))
    | ~ v1_funct_2(sK1,sK0,k9_setfam_1(sK0))
    | ~ v1_funct_1(sK1)
    | ~ spl5_6 ),
    inference(resolution,[],[f136,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_funct_1(X1,sK4(X0,X1)),X0)
      | m1_subset_1(sK3(X0,X1),k9_setfam_1(k2_zfmisc_1(X0,X0)))
      | ~ m1_subset_1(X1,k9_setfam_1(k2_zfmisc_1(X0,k9_setfam_1(X0))))
      | ~ v1_funct_2(X1,X0,k9_setfam_1(X0))
      | ~ v1_funct_1(X1) ) ),
    inference(forward_demodulation,[],[f69,f37])).

fof(f37,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f69,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(X0,X1),k9_setfam_1(k2_zfmisc_1(X0,X0)))
      | ~ r1_tarski(k1_funct_1(X1,sK4(X0,X1)),k2_subset_1(X0))
      | ~ m1_subset_1(X1,k9_setfam_1(k2_zfmisc_1(X0,k9_setfam_1(X0))))
      | ~ v1_funct_2(X1,X0,k9_setfam_1(X0))
      | ~ v1_funct_1(X1) ) ),
    inference(forward_demodulation,[],[f56,f37])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(X0,X1),k9_setfam_1(k2_zfmisc_1(k2_subset_1(X0),k2_subset_1(X0))))
      | ~ r1_tarski(k1_funct_1(X1,sK4(X0,X1)),k2_subset_1(X0))
      | ~ m1_subset_1(X1,k9_setfam_1(k2_zfmisc_1(X0,k9_setfam_1(X0))))
      | ~ v1_funct_2(X1,X0,k9_setfam_1(X0))
      | ~ v1_funct_1(X1) ) ),
    inference(definition_unfolding,[],[f43,f38,f38])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k2_zfmisc_1(k2_subset_1(X0),k2_subset_1(X0))))
      | ~ r1_tarski(k1_funct_1(X1,sK4(X0,X1)),k2_subset_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k9_setfam_1(X0))))
      | ~ v1_funct_2(X1,X0,k9_setfam_1(X0))
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ! [X3] :
            ( k1_funct_1(X1,X3) = k11_relat_1(sK3(X0,X1),X3)
            | ~ r2_hidden(X3,k2_subset_1(X0))
            | ~ m1_subset_1(X3,X0) )
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k2_zfmisc_1(k2_subset_1(X0),k2_subset_1(X0)))) )
      | ( ~ r1_tarski(k1_funct_1(X1,sK4(X0,X1)),k2_subset_1(X0))
        & r2_hidden(sK4(X0,X1),k2_subset_1(X0))
        & m1_subset_1(sK4(X0,X1),X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k9_setfam_1(X0))))
      | ~ v1_funct_2(X1,X0,k9_setfam_1(X0))
      | ~ v1_funct_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f26,f28,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k11_relat_1(X2,X3) = k1_funct_1(X1,X3)
              | ~ r2_hidden(X3,k2_subset_1(X0))
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_subset_1(X0),k2_subset_1(X0)))) )
     => ( ! [X3] :
            ( k1_funct_1(X1,X3) = k11_relat_1(sK3(X0,X1),X3)
            | ~ r2_hidden(X3,k2_subset_1(X0))
            | ~ m1_subset_1(X3,X0) )
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k2_zfmisc_1(k2_subset_1(X0),k2_subset_1(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( ~ r1_tarski(k1_funct_1(X1,X4),k2_subset_1(X0))
          & r2_hidden(X4,k2_subset_1(X0))
          & m1_subset_1(X4,X0) )
     => ( ~ r1_tarski(k1_funct_1(X1,sK4(X0,X1)),k2_subset_1(X0))
        & r2_hidden(sK4(X0,X1),k2_subset_1(X0))
        & m1_subset_1(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( k11_relat_1(X2,X3) = k1_funct_1(X1,X3)
              | ~ r2_hidden(X3,k2_subset_1(X0))
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_subset_1(X0),k2_subset_1(X0)))) )
      | ? [X4] :
          ( ~ r1_tarski(k1_funct_1(X1,X4),k2_subset_1(X0))
          & r2_hidden(X4,k2_subset_1(X0))
          & m1_subset_1(X4,X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k9_setfam_1(X0))))
      | ~ v1_funct_2(X1,X0,k9_setfam_1(X0))
      | ~ v1_funct_1(X1) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ? [X3] :
          ( ! [X4] :
              ( k11_relat_1(X3,X4) = k1_funct_1(X1,X4)
              | ~ r2_hidden(X4,k2_subset_1(X0))
              | ~ m1_subset_1(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_subset_1(X0),k2_subset_1(X0)))) )
      | ? [X2] :
          ( ~ r1_tarski(k1_funct_1(X1,X2),k2_subset_1(X0))
          & r2_hidden(X2,k2_subset_1(X0))
          & m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k9_setfam_1(X0))))
      | ~ v1_funct_2(X1,X0,k9_setfam_1(X0))
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ? [X3] :
          ( ! [X4] :
              ( k11_relat_1(X3,X4) = k1_funct_1(X1,X4)
              | ~ r2_hidden(X4,k2_subset_1(X0))
              | ~ m1_subset_1(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_subset_1(X0),k2_subset_1(X0)))) )
      | ? [X2] :
          ( ~ r1_tarski(k1_funct_1(X1,X2),k2_subset_1(X0))
          & r2_hidden(X2,k2_subset_1(X0))
          & m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k9_setfam_1(X0))))
      | ~ v1_funct_2(X1,X0,k9_setfam_1(X0))
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k9_setfam_1(X0))))
        & v1_funct_2(X1,X0,k9_setfam_1(X0))
        & v1_funct_1(X1) )
     => ( ! [X2] :
            ( m1_subset_1(X2,X0)
           => ( r2_hidden(X2,k2_subset_1(X0))
             => r1_tarski(k1_funct_1(X1,X2),k2_subset_1(X0)) ) )
       => ? [X3] :
            ( ! [X4] :
                ( m1_subset_1(X4,X0)
               => ( r2_hidden(X4,k2_subset_1(X0))
                 => k11_relat_1(X3,X4) = k1_funct_1(X1,X4) ) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_subset_1(X0),k2_subset_1(X0)))) ) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k9_setfam_1(X0))))
        & v1_funct_2(X1,X0,k9_setfam_1(X0))
        & v1_funct_1(X1) )
     => ( ! [X2] :
            ( m1_subset_1(X2,X0)
           => ( r2_hidden(X2,k2_subset_1(X0))
             => r1_tarski(k1_funct_1(X1,X2),k2_subset_1(X0)) ) )
       => ? [X2] :
            ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,k2_subset_1(X0))
                 => k11_relat_1(X2,X3) = k1_funct_1(X1,X3) ) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_subset_1(X0),k2_subset_1(X0)))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_relset_1__e2_192__funct_2)).

fof(f136,plain,
    ( r1_tarski(k1_funct_1(sK1,sK4(sK0,sK1)),sK0)
    | ~ spl5_6 ),
    inference(resolution,[],[f135,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k9_setfam_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f47,f38])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f135,plain,
    ( m1_subset_1(k1_funct_1(sK1,sK4(sK0,sK1)),k9_setfam_1(sK0))
    | ~ spl5_6 ),
    inference(resolution,[],[f132,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f132,plain,
    ( r2_hidden(k1_funct_1(sK1,sK4(sK0,sK1)),k9_setfam_1(sK0))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl5_6
  <=> r2_hidden(k1_funct_1(sK1,sK4(sK0,sK1)),k9_setfam_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f165,plain,(
    ~ spl5_4 ),
    inference(avatar_contradiction_clause,[],[f164])).

fof(f164,plain,
    ( $false
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f157,f35])).

fof(f35,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(f157,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | ~ spl5_4 ),
    inference(superposition,[],[f52,f105])).

fof(f105,plain,
    ( o_0_0_xboole_0 = k9_setfam_1(sK0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl5_4
  <=> o_0_0_xboole_0 = k9_setfam_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f52,plain,(
    ! [X0] : ~ v1_xboole_0(k9_setfam_1(X0)) ),
    inference(definition_unfolding,[],[f36,f38])).

fof(f36,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f149,plain,
    ( ~ spl5_2
    | ~ spl5_6 ),
    inference(avatar_contradiction_clause,[],[f148])).

fof(f148,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f147,f89])).

fof(f89,plain,
    ( m1_subset_1(sK3(sK0,sK1),k9_setfam_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f87])).

fof(f147,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1),k9_setfam_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl5_2
    | ~ spl5_6 ),
    inference(trivial_inequality_removal,[],[f146])).

fof(f146,plain,
    ( k1_funct_1(sK1,sK2(sK3(sK0,sK1))) != k1_funct_1(sK1,sK2(sK3(sK0,sK1)))
    | ~ m1_subset_1(sK3(sK0,sK1),k9_setfam_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl5_2
    | ~ spl5_6 ),
    inference(superposition,[],[f49,f144])).

fof(f144,plain,
    ( k1_funct_1(sK1,sK2(sK3(sK0,sK1))) = k11_relat_1(sK3(sK0,sK1),sK2(sK3(sK0,sK1)))
    | ~ spl5_2
    | ~ spl5_6 ),
    inference(resolution,[],[f143,f91])).

fof(f91,plain,
    ( r2_hidden(sK2(sK3(sK0,sK1)),sK0)
    | ~ spl5_2 ),
    inference(resolution,[],[f89,f50])).

fof(f50,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k9_setfam_1(k2_zfmisc_1(sK0,sK0)))
      | r2_hidden(sK2(X2),sK0) ) ),
    inference(definition_unfolding,[],[f33,f38])).

fof(f33,plain,(
    ! [X2] :
      ( r2_hidden(sK2(X2),sK0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f143,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | k1_funct_1(sK1,X0) = k11_relat_1(sK3(sK0,sK1),X0) )
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f142,f136])).

fof(f142,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,X0) = k11_relat_1(sK3(sK0,sK1),X0)
      | ~ r2_hidden(X0,sK0)
      | ~ r1_tarski(k1_funct_1(sK1,sK4(sK0,sK1)),sK0) ) ),
    inference(subsumption_resolution,[],[f141,f31])).

fof(f141,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,X0) = k11_relat_1(sK3(sK0,sK1),X0)
      | ~ r2_hidden(X0,sK0)
      | ~ v1_funct_2(sK1,sK0,k9_setfam_1(sK0))
      | ~ r1_tarski(k1_funct_1(sK1,sK4(sK0,sK1)),sK0) ) ),
    inference(resolution,[],[f140,f51])).

fof(f140,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK1,k9_setfam_1(k2_zfmisc_1(X1,k9_setfam_1(X1))))
      | k1_funct_1(sK1,X0) = k11_relat_1(sK3(X1,sK1),X0)
      | ~ r2_hidden(X0,X1)
      | ~ v1_funct_2(sK1,X1,k9_setfam_1(X1))
      | ~ r1_tarski(k1_funct_1(sK1,sK4(X1,sK1)),X1) ) ),
    inference(resolution,[],[f63,f30])).

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r2_hidden(X3,X0)
      | k1_funct_1(X1,X3) = k11_relat_1(sK3(X0,X1),X3)
      | ~ m1_subset_1(X1,k9_setfam_1(k2_zfmisc_1(X0,k9_setfam_1(X0))))
      | ~ v1_funct_2(X1,X0,k9_setfam_1(X0))
      | ~ r1_tarski(k1_funct_1(X1,sK4(X0,X1)),X0) ) ),
    inference(forward_demodulation,[],[f62,f37])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | k1_funct_1(X1,X3) = k11_relat_1(sK3(X0,X1),X3)
      | ~ r1_tarski(k1_funct_1(X1,sK4(X0,X1)),k2_subset_1(X0))
      | ~ m1_subset_1(X1,k9_setfam_1(k2_zfmisc_1(X0,k9_setfam_1(X0))))
      | ~ v1_funct_2(X1,X0,k9_setfam_1(X0))
      | ~ v1_funct_1(X1) ) ),
    inference(subsumption_resolution,[],[f61,f40])).

fof(f61,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | k1_funct_1(X1,X3) = k11_relat_1(sK3(X0,X1),X3)
      | ~ m1_subset_1(X3,X0)
      | ~ r1_tarski(k1_funct_1(X1,sK4(X0,X1)),k2_subset_1(X0))
      | ~ m1_subset_1(X1,k9_setfam_1(k2_zfmisc_1(X0,k9_setfam_1(X0))))
      | ~ v1_funct_2(X1,X0,k9_setfam_1(X0))
      | ~ v1_funct_1(X1) ) ),
    inference(forward_demodulation,[],[f53,f37])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(X1,X3) = k11_relat_1(sK3(X0,X1),X3)
      | ~ r2_hidden(X3,k2_subset_1(X0))
      | ~ m1_subset_1(X3,X0)
      | ~ r1_tarski(k1_funct_1(X1,sK4(X0,X1)),k2_subset_1(X0))
      | ~ m1_subset_1(X1,k9_setfam_1(k2_zfmisc_1(X0,k9_setfam_1(X0))))
      | ~ v1_funct_2(X1,X0,k9_setfam_1(X0))
      | ~ v1_funct_1(X1) ) ),
    inference(definition_unfolding,[],[f46,f38])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(X1,X3) = k11_relat_1(sK3(X0,X1),X3)
      | ~ r2_hidden(X3,k2_subset_1(X0))
      | ~ m1_subset_1(X3,X0)
      | ~ r1_tarski(k1_funct_1(X1,sK4(X0,X1)),k2_subset_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k9_setfam_1(X0))))
      | ~ v1_funct_2(X1,X0,k9_setfam_1(X0))
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f49,plain,(
    ! [X2] :
      ( k11_relat_1(X2,sK2(X2)) != k1_funct_1(sK1,sK2(X2))
      | ~ m1_subset_1(X2,k9_setfam_1(k2_zfmisc_1(sK0,sK0))) ) ),
    inference(definition_unfolding,[],[f34,f38])).

fof(f34,plain,(
    ! [X2] :
      ( k11_relat_1(X2,sK2(X2)) != k1_funct_1(sK1,sK2(X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f133,plain,
    ( spl5_6
    | spl5_4
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f128,f83,f103,f130])).

fof(f83,plain,
    ( spl5_1
  <=> r2_hidden(sK4(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f128,plain,
    ( o_0_0_xboole_0 = k9_setfam_1(sK0)
    | r2_hidden(k1_funct_1(sK1,sK4(sK0,sK1)),k9_setfam_1(sK0))
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f127,f31])).

fof(f127,plain,
    ( o_0_0_xboole_0 = k9_setfam_1(sK0)
    | ~ v1_funct_2(sK1,sK0,k9_setfam_1(sK0))
    | r2_hidden(k1_funct_1(sK1,sK4(sK0,sK1)),k9_setfam_1(sK0))
    | ~ spl5_1 ),
    inference(resolution,[],[f126,f51])).

fof(f126,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k9_setfam_1(k2_zfmisc_1(sK0,X0)))
        | o_0_0_xboole_0 = X0
        | ~ v1_funct_2(sK1,sK0,X0)
        | r2_hidden(k1_funct_1(sK1,sK4(sK0,sK1)),X0) )
    | ~ spl5_1 ),
    inference(resolution,[],[f124,f30])).

fof(f124,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(X0)
        | o_0_0_xboole_0 = X1
        | ~ m1_subset_1(X0,k9_setfam_1(k2_zfmisc_1(sK0,X1)))
        | ~ v1_funct_2(X0,sK0,X1)
        | r2_hidden(k1_funct_1(X0,sK4(sK0,sK1)),X1) )
    | ~ spl5_1 ),
    inference(resolution,[],[f85,f75])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(k1_funct_1(X3,X2),X1)
      | o_0_0_xboole_0 = X1
      | ~ m1_subset_1(X3,k9_setfam_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(backward_demodulation,[],[f60,f74])).

fof(f74,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[],[f39,f35])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k9_setfam_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(definition_unfolding,[],[f48,f38])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

fof(f85,plain,
    ( r2_hidden(sK4(sK0,sK1),sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f83])).

fof(f123,plain,
    ( ~ spl5_2
    | ~ spl5_5 ),
    inference(avatar_contradiction_clause,[],[f122])).

fof(f122,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f121,f89])).

fof(f121,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1),k9_setfam_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl5_2
    | ~ spl5_5 ),
    inference(trivial_inequality_removal,[],[f120])).

fof(f120,plain,
    ( k1_funct_1(sK1,sK2(sK3(sK0,sK1))) != k1_funct_1(sK1,sK2(sK3(sK0,sK1)))
    | ~ m1_subset_1(sK3(sK0,sK1),k9_setfam_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl5_2
    | ~ spl5_5 ),
    inference(superposition,[],[f49,f119])).

fof(f119,plain,
    ( k1_funct_1(sK1,sK2(sK3(sK0,sK1))) = k11_relat_1(sK3(sK0,sK1),sK2(sK3(sK0,sK1)))
    | ~ spl5_2
    | ~ spl5_5 ),
    inference(resolution,[],[f117,f91])).

fof(f117,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | k1_funct_1(sK1,X0) = k11_relat_1(sK3(sK0,sK1),X0) )
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl5_5
  <=> ! [X0] :
        ( k1_funct_1(sK1,X0) = k11_relat_1(sK3(sK0,sK1),X0)
        | ~ r2_hidden(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f118,plain,
    ( spl5_1
    | spl5_5 ),
    inference(avatar_split_clause,[],[f114,f116,f83])).

fof(f114,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,X0) = k11_relat_1(sK3(sK0,sK1),X0)
      | ~ r2_hidden(X0,sK0)
      | r2_hidden(sK4(sK0,sK1),sK0) ) ),
    inference(subsumption_resolution,[],[f113,f31])).

fof(f113,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,X0) = k11_relat_1(sK3(sK0,sK1),X0)
      | ~ r2_hidden(X0,sK0)
      | ~ v1_funct_2(sK1,sK0,k9_setfam_1(sK0))
      | r2_hidden(sK4(sK0,sK1),sK0) ) ),
    inference(resolution,[],[f112,f51])).

fof(f112,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK1,k9_setfam_1(k2_zfmisc_1(X1,k9_setfam_1(X1))))
      | k1_funct_1(sK1,X0) = k11_relat_1(sK3(X1,sK1),X0)
      | ~ r2_hidden(X0,X1)
      | ~ v1_funct_2(sK1,X1,k9_setfam_1(X1))
      | r2_hidden(sK4(X1,sK1),X1) ) ),
    inference(resolution,[],[f66,f30])).

fof(f66,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r2_hidden(X3,X0)
      | k1_funct_1(X1,X3) = k11_relat_1(sK3(X0,X1),X3)
      | ~ m1_subset_1(X1,k9_setfam_1(k2_zfmisc_1(X0,k9_setfam_1(X0))))
      | ~ v1_funct_2(X1,X0,k9_setfam_1(X0))
      | r2_hidden(sK4(X0,X1),X0) ) ),
    inference(forward_demodulation,[],[f65,f37])).

fof(f65,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | k1_funct_1(X1,X3) = k11_relat_1(sK3(X0,X1),X3)
      | r2_hidden(sK4(X0,X1),k2_subset_1(X0))
      | ~ m1_subset_1(X1,k9_setfam_1(k2_zfmisc_1(X0,k9_setfam_1(X0))))
      | ~ v1_funct_2(X1,X0,k9_setfam_1(X0))
      | ~ v1_funct_1(X1) ) ),
    inference(subsumption_resolution,[],[f64,f40])).

fof(f64,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | k1_funct_1(X1,X3) = k11_relat_1(sK3(X0,X1),X3)
      | ~ m1_subset_1(X3,X0)
      | r2_hidden(sK4(X0,X1),k2_subset_1(X0))
      | ~ m1_subset_1(X1,k9_setfam_1(k2_zfmisc_1(X0,k9_setfam_1(X0))))
      | ~ v1_funct_2(X1,X0,k9_setfam_1(X0))
      | ~ v1_funct_1(X1) ) ),
    inference(forward_demodulation,[],[f54,f37])).

fof(f54,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(X1,X3) = k11_relat_1(sK3(X0,X1),X3)
      | ~ r2_hidden(X3,k2_subset_1(X0))
      | ~ m1_subset_1(X3,X0)
      | r2_hidden(sK4(X0,X1),k2_subset_1(X0))
      | ~ m1_subset_1(X1,k9_setfam_1(k2_zfmisc_1(X0,k9_setfam_1(X0))))
      | ~ v1_funct_2(X1,X0,k9_setfam_1(X0))
      | ~ v1_funct_1(X1) ) ),
    inference(definition_unfolding,[],[f45,f38])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(X1,X3) = k11_relat_1(sK3(X0,X1),X3)
      | ~ r2_hidden(X3,k2_subset_1(X0))
      | ~ m1_subset_1(X3,X0)
      | r2_hidden(sK4(X0,X1),k2_subset_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k9_setfam_1(X0))))
      | ~ v1_funct_2(X1,X0,k9_setfam_1(X0))
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f90,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f81,f87,f83])).

fof(f81,plain,
    ( m1_subset_1(sK3(sK0,sK1),k9_setfam_1(k2_zfmisc_1(sK0,sK0)))
    | r2_hidden(sK4(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f80,f31])).

fof(f80,plain,
    ( m1_subset_1(sK3(sK0,sK1),k9_setfam_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,k9_setfam_1(sK0))
    | r2_hidden(sK4(sK0,sK1),sK0) ),
    inference(resolution,[],[f79,f51])).

fof(f79,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK1,k9_setfam_1(k2_zfmisc_1(X0,k9_setfam_1(X0))))
      | m1_subset_1(sK3(X0,sK1),k9_setfam_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(sK1,X0,k9_setfam_1(X0))
      | r2_hidden(sK4(X0,sK1),X0) ) ),
    inference(resolution,[],[f72,f30])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | m1_subset_1(sK3(X0,X1),k9_setfam_1(k2_zfmisc_1(X0,X0)))
      | ~ m1_subset_1(X1,k9_setfam_1(k2_zfmisc_1(X0,k9_setfam_1(X0))))
      | ~ v1_funct_2(X1,X0,k9_setfam_1(X0))
      | r2_hidden(sK4(X0,X1),X0) ) ),
    inference(forward_demodulation,[],[f71,f37])).

fof(f71,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(X0,X1),k9_setfam_1(k2_zfmisc_1(X0,X0)))
      | r2_hidden(sK4(X0,X1),k2_subset_1(X0))
      | ~ m1_subset_1(X1,k9_setfam_1(k2_zfmisc_1(X0,k9_setfam_1(X0))))
      | ~ v1_funct_2(X1,X0,k9_setfam_1(X0))
      | ~ v1_funct_1(X1) ) ),
    inference(forward_demodulation,[],[f57,f37])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(X0,X1),k9_setfam_1(k2_zfmisc_1(k2_subset_1(X0),k2_subset_1(X0))))
      | r2_hidden(sK4(X0,X1),k2_subset_1(X0))
      | ~ m1_subset_1(X1,k9_setfam_1(k2_zfmisc_1(X0,k9_setfam_1(X0))))
      | ~ v1_funct_2(X1,X0,k9_setfam_1(X0))
      | ~ v1_funct_1(X1) ) ),
    inference(definition_unfolding,[],[f42,f38,f38])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k2_zfmisc_1(k2_subset_1(X0),k2_subset_1(X0))))
      | r2_hidden(sK4(X0,X1),k2_subset_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k9_setfam_1(X0))))
      | ~ v1_funct_2(X1,X0,k9_setfam_1(X0))
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

%------------------------------------------------------------------------------
