%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_2__t184_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:38 EDT 2019

% Result     : Theorem 96.51s
% Output     : Refutation 96.51s
% Verified   : 
% Statistics : Number of formulae       :  179 ( 852 expanded)
%              Number of leaves         :   37 ( 354 expanded)
%              Depth                    :   25
%              Number of atoms          : 1022 (5709 expanded)
%              Number of equality atoms :  150 ( 217 expanded)
%              Maximal formula depth    :   21 (   8 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15573,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f352,f504,f662,f15508])).

fof(f15508,plain,
    ( ~ spl17_0
    | ~ spl17_6 ),
    inference(avatar_contradiction_clause,[],[f15507])).

fof(f15507,plain,
    ( $false
    | ~ spl17_0
    | ~ spl17_6 ),
    inference(subsumption_resolution,[],[f15490,f5581])).

fof(f5581,plain,
    ( r1_tarski(sK14(sK3,sK11(k3_tarski(sK3),k3_tarski(k6_funct_2(sK0,sK1,sK2,k7_funct_2(sK0,sK1,sK2,sK3))))),k10_relat_1(sK2,k9_relat_1(sK2,sK14(sK3,sK11(k3_tarski(sK3),k3_tarski(k6_funct_2(sK0,sK1,sK2,k7_funct_2(sK0,sK1,sK2,sK3))))))))
    | ~ spl17_0
    | ~ spl17_6 ),
    inference(unit_resulting_resolution,[],[f3402,f1066])).

fof(f1066,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | r1_tarski(X0,k10_relat_1(sK2,k9_relat_1(sK2,X0))) )
    | ~ spl17_6 ),
    inference(subsumption_resolution,[],[f1065,f202])).

fof(f202,plain,(
    v1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f114,f157])).

fof(f157,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f38])).

fof(f38,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t184_funct_2.p',cc1_relset_1)).

fof(f114,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,
    ( ~ r1_tarski(k5_setfam_1(sK0,sK3),k5_setfam_1(sK0,k6_funct_2(sK0,sK1,sK2,k7_funct_2(sK0,sK1,sK2,sK3))))
    & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2)
    & ~ v1_xboole_0(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f42,f78,f77,f76,f75])).

fof(f75,plain,
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

fof(f76,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tarski(k5_setfam_1(X0,X3),k5_setfam_1(X0,k6_funct_2(X0,X1,X2,k7_funct_2(X0,X1,X2,X3))))
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ~ r1_tarski(k5_setfam_1(X0,X3),k5_setfam_1(X0,k6_funct_2(X0,sK1,X2,k7_funct_2(X0,sK1,X2,X3))))
                & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0))) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
            & v1_funct_2(X2,X0,sK1)
            & v1_funct_1(X2) )
        & ~ v1_xboole_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(k5_setfam_1(X0,X3),k5_setfam_1(X0,k6_funct_2(X0,X1,X2,k7_funct_2(X0,X1,X2,X3))))
              & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0))) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
     => ( ? [X3] :
            ( ~ r1_tarski(k5_setfam_1(X0,X3),k5_setfam_1(X0,k6_funct_2(X0,X1,sK2,k7_funct_2(X0,X1,sK2,X3))))
            & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0))) )
        & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(sK2,X0,X1)
        & v1_funct_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r1_tarski(k5_setfam_1(X0,X3),k5_setfam_1(X0,k6_funct_2(X0,X1,X2,k7_funct_2(X0,X1,X2,X3))))
          & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0))) )
     => ( ~ r1_tarski(k5_setfam_1(X0,sK3),k5_setfam_1(X0,k6_funct_2(X0,X1,X2,k7_funct_2(X0,X1,X2,sK3))))
        & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f41,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
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
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/funct_2__t184_funct_2.p',t184_funct_2)).

fof(f1065,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | r1_tarski(X0,k10_relat_1(sK2,k9_relat_1(sK2,X0)))
        | ~ v1_relat_1(sK2) )
    | ~ spl17_6 ),
    inference(superposition,[],[f138,f348])).

fof(f348,plain,
    ( k1_relat_1(sK2) = sK0
    | ~ spl17_6 ),
    inference(avatar_component_clause,[],[f347])).

fof(f347,plain,
    ( spl17_6
  <=> k1_relat_1(sK2) = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_6])])).

fof(f138,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t184_funct_2.p',t146_funct_1)).

fof(f3402,plain,
    ( r1_tarski(sK14(sK3,sK11(k3_tarski(sK3),k3_tarski(k6_funct_2(sK0,sK1,sK2,k7_funct_2(sK0,sK1,sK2,sK3))))),sK0)
    | ~ spl17_0 ),
    inference(unit_resulting_resolution,[],[f1909,f153])).

fof(f153,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t184_funct_2.p',t3_subset)).

fof(f1909,plain,
    ( m1_subset_1(sK14(sK3,sK11(k3_tarski(sK3),k3_tarski(k6_funct_2(sK0,sK1,sK2,k7_funct_2(sK0,sK1,sK2,sK3))))),k1_zfmisc_1(sK0))
    | ~ spl17_0 ),
    inference(unit_resulting_resolution,[],[f115,f878,f166])).

fof(f166,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t184_funct_2.p',t4_subset)).

fof(f878,plain,
    ( r2_hidden(sK14(sK3,sK11(k3_tarski(sK3),k3_tarski(k6_funct_2(sK0,sK1,sK2,k7_funct_2(sK0,sK1,sK2,sK3))))),sK3)
    | ~ spl17_0 ),
    inference(unit_resulting_resolution,[],[f705,f186])).

fof(f186,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK14(X0,X5),X0)
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f148])).

fof(f148,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK14(X0,X5),X0)
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(sK12(X0,X1),X3) )
            | ~ r2_hidden(sK12(X0,X1),X1) )
          & ( ( r2_hidden(sK13(X0,X1),X0)
              & r2_hidden(sK12(X0,X1),sK13(X0,X1)) )
            | r2_hidden(sK12(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ( r2_hidden(sK14(X0,X5),X0)
                & r2_hidden(X5,sK14(X0,X5)) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12,sK13,sK14])],[f101,f104,f103,f102])).

fof(f102,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X3) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( r2_hidden(X4,X0)
                & r2_hidden(X2,X4) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( ~ r2_hidden(X3,X0)
              | ~ r2_hidden(sK12(X0,X1),X3) )
          | ~ r2_hidden(sK12(X0,X1),X1) )
        & ( ? [X4] :
              ( r2_hidden(X4,X0)
              & r2_hidden(sK12(X0,X1),X4) )
          | r2_hidden(sK12(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f103,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(X2,X4) )
     => ( r2_hidden(sK13(X0,X1),X0)
        & r2_hidden(X2,sK13(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f104,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( r2_hidden(X7,X0)
          & r2_hidden(X5,X7) )
     => ( r2_hidden(sK14(X0,X5),X0)
        & r2_hidden(X5,sK14(X0,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] :
                  ( r2_hidden(X4,X0)
                  & r2_hidden(X2,X4) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ? [X7] :
                  ( r2_hidden(X7,X0)
                  & r2_hidden(X5,X7) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) ) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t184_funct_2.p',d4_tarski)).

fof(f705,plain,
    ( r2_hidden(sK11(k3_tarski(sK3),k3_tarski(k6_funct_2(sK0,sK1,sK2,k7_funct_2(sK0,sK1,sK2,sK3)))),k3_tarski(sK3))
    | ~ spl17_0 ),
    inference(backward_demodulation,[],[f689,f217])).

fof(f217,plain,(
    r2_hidden(sK11(k3_tarski(sK3),k5_setfam_1(sK0,k6_funct_2(sK0,sK1,sK2,k7_funct_2(sK0,sK1,sK2,sK3)))),k3_tarski(sK3)) ),
    inference(unit_resulting_resolution,[],[f201,f145])).

fof(f145,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK11(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK11(X0,X1),X1)
          & r2_hidden(sK11(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f97,f98])).

fof(f98,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK11(X0,X1),X1)
        & r2_hidden(sK11(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t184_funct_2.p',d3_tarski)).

fof(f201,plain,(
    ~ r1_tarski(k3_tarski(sK3),k5_setfam_1(sK0,k6_funct_2(sK0,sK1,sK2,k7_funct_2(sK0,sK1,sK2,sK3)))) ),
    inference(backward_demodulation,[],[f197,f116])).

fof(f116,plain,(
    ~ r1_tarski(k5_setfam_1(sK0,sK3),k5_setfam_1(sK0,k6_funct_2(sK0,sK1,sK2,k7_funct_2(sK0,sK1,sK2,sK3)))) ),
    inference(cnf_transformation,[],[f79])).

fof(f197,plain,(
    k5_setfam_1(sK0,sK3) = k3_tarski(sK3) ),
    inference(unit_resulting_resolution,[],[f115,f142])).

fof(f142,plain,(
    ! [X0,X1] :
      ( k5_setfam_1(X0,X1) = k3_tarski(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k5_setfam_1(X0,X1) = k3_tarski(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k5_setfam_1(X0,X1) = k3_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t184_funct_2.p',redefinition_k5_setfam_1)).

fof(f689,plain,
    ( k5_setfam_1(sK0,k6_funct_2(sK0,sK1,sK2,k7_funct_2(sK0,sK1,sK2,sK3))) = k3_tarski(k6_funct_2(sK0,sK1,sK2,k7_funct_2(sK0,sK1,sK2,sK3)))
    | ~ spl17_0 ),
    inference(unit_resulting_resolution,[],[f299,f142])).

fof(f299,plain,
    ( m1_subset_1(k6_funct_2(sK0,sK1,sK2,k7_funct_2(sK0,sK1,sK2,sK3)),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl17_0 ),
    inference(avatar_component_clause,[],[f298])).

fof(f298,plain,
    ( spl17_0
  <=> m1_subset_1(k6_funct_2(sK0,sK1,sK2,k7_funct_2(sK0,sK1,sK2,sK3)),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_0])])).

fof(f115,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f79])).

fof(f15490,plain,
    ( ~ r1_tarski(sK14(sK3,sK11(k3_tarski(sK3),k3_tarski(k6_funct_2(sK0,sK1,sK2,k7_funct_2(sK0,sK1,sK2,sK3))))),k10_relat_1(sK2,k9_relat_1(sK2,sK14(sK3,sK11(k3_tarski(sK3),k3_tarski(k6_funct_2(sK0,sK1,sK2,k7_funct_2(sK0,sK1,sK2,sK3))))))))
    | ~ spl17_0 ),
    inference(unit_resulting_resolution,[],[f877,f7405,f144])).

fof(f144,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f99])).

fof(f7405,plain,
    ( ~ r2_hidden(sK11(k3_tarski(sK3),k3_tarski(k6_funct_2(sK0,sK1,sK2,k7_funct_2(sK0,sK1,sK2,sK3)))),k10_relat_1(sK2,k9_relat_1(sK2,sK14(sK3,sK11(k3_tarski(sK3),k3_tarski(k6_funct_2(sK0,sK1,sK2,k7_funct_2(sK0,sK1,sK2,sK3))))))))
    | ~ spl17_0 ),
    inference(unit_resulting_resolution,[],[f706,f3699,f185])).

fof(f185,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k3_tarski(X0))
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6) ) ),
    inference(equality_resolution,[],[f149])).

fof(f149,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f105])).

fof(f3699,plain,
    ( r2_hidden(k10_relat_1(sK2,k9_relat_1(sK2,sK14(sK3,sK11(k3_tarski(sK3),k3_tarski(k6_funct_2(sK0,sK1,sK2,k7_funct_2(sK0,sK1,sK2,sK3))))))),k6_funct_2(sK0,sK1,sK2,k7_funct_2(sK0,sK1,sK2,sK3)))
    | ~ spl17_0 ),
    inference(unit_resulting_resolution,[],[f211,f299,f2055,f644])).

fof(f644,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,X3)
      | r2_hidden(k10_relat_1(sK2,X2),k6_funct_2(sK0,sK1,sK2,X3))
      | ~ m1_subset_1(k6_funct_2(sK0,sK1,sK2,X3),k1_zfmisc_1(k1_zfmisc_1(sK0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(sK1))) ) ),
    inference(forward_demodulation,[],[f643,f208])).

fof(f208,plain,(
    ! [X0] : k8_relset_1(sK0,sK1,sK2,X0) = k10_relat_1(sK2,X0) ),
    inference(unit_resulting_resolution,[],[f114,f171])).

fof(f171,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t184_funct_2.p',redefinition_k8_relset_1)).

fof(f643,plain,(
    ! [X2,X3] :
      ( r2_hidden(k8_relset_1(sK0,sK1,sK2,X2),k6_funct_2(sK0,sK1,sK2,X3))
      | ~ r2_hidden(X2,X3)
      | ~ m1_subset_1(k6_funct_2(sK0,sK1,sK2,X3),k1_zfmisc_1(k1_zfmisc_1(sK0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(sK1))) ) ),
    inference(subsumption_resolution,[],[f642,f166])).

fof(f642,plain,(
    ! [X2,X3] :
      ( r2_hidden(k8_relset_1(sK0,sK1,sK2,X2),k6_funct_2(sK0,sK1,sK2,X3))
      | ~ r2_hidden(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(sK1))
      | ~ m1_subset_1(k6_funct_2(sK0,sK1,sK2,X3),k1_zfmisc_1(k1_zfmisc_1(sK0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(sK1))) ) ),
    inference(subsumption_resolution,[],[f641,f110])).

fof(f110,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f79])).

fof(f641,plain,(
    ! [X2,X3] :
      ( r2_hidden(k8_relset_1(sK0,sK1,sK2,X2),k6_funct_2(sK0,sK1,sK2,X3))
      | ~ r2_hidden(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(sK1))
      | ~ m1_subset_1(k6_funct_2(sK0,sK1,sK2,X3),k1_zfmisc_1(k1_zfmisc_1(sK0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(sK1)))
      | v1_xboole_0(sK0) ) ),
    inference(subsumption_resolution,[],[f640,f111])).

fof(f111,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f79])).

fof(f640,plain,(
    ! [X2,X3] :
      ( r2_hidden(k8_relset_1(sK0,sK1,sK2,X2),k6_funct_2(sK0,sK1,sK2,X3))
      | ~ r2_hidden(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(sK1))
      | ~ m1_subset_1(k6_funct_2(sK0,sK1,sK2,X3),k1_zfmisc_1(k1_zfmisc_1(sK0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(sK1)))
      | v1_xboole_0(sK1)
      | v1_xboole_0(sK0) ) ),
    inference(subsumption_resolution,[],[f639,f112])).

fof(f112,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f79])).

fof(f639,plain,(
    ! [X2,X3] :
      ( r2_hidden(k8_relset_1(sK0,sK1,sK2,X2),k6_funct_2(sK0,sK1,sK2,X3))
      | ~ r2_hidden(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(sK1))
      | ~ m1_subset_1(k6_funct_2(sK0,sK1,sK2,X3),k1_zfmisc_1(k1_zfmisc_1(sK0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(sK1)))
      | ~ v1_funct_1(sK2)
      | v1_xboole_0(sK1)
      | v1_xboole_0(sK0) ) ),
    inference(subsumption_resolution,[],[f638,f113])).

fof(f113,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f79])).

fof(f638,plain,(
    ! [X2,X3] :
      ( r2_hidden(k8_relset_1(sK0,sK1,sK2,X2),k6_funct_2(sK0,sK1,sK2,X3))
      | ~ r2_hidden(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(sK1))
      | ~ m1_subset_1(k6_funct_2(sK0,sK1,sK2,X3),k1_zfmisc_1(k1_zfmisc_1(sK0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(sK1)))
      | ~ v1_funct_2(sK2,sK0,sK1)
      | ~ v1_funct_1(sK2)
      | v1_xboole_0(sK1)
      | v1_xboole_0(sK0) ) ),
    inference(subsumption_resolution,[],[f637,f114])).

fof(f637,plain,(
    ! [X2,X3] :
      ( r2_hidden(k8_relset_1(sK0,sK1,sK2,X2),k6_funct_2(sK0,sK1,sK2,X3))
      | ~ r2_hidden(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(sK1))
      | ~ m1_subset_1(k6_funct_2(sK0,sK1,sK2,X3),k1_zfmisc_1(k1_zfmisc_1(sK0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(sK1)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_2(sK2,sK0,sK1)
      | ~ v1_funct_1(sK2)
      | v1_xboole_0(sK1)
      | v1_xboole_0(sK0) ) ),
    inference(subsumption_resolution,[],[f621,f213])).

fof(f213,plain,(
    ! [X0] : m1_subset_1(k10_relat_1(sK2,X0),k1_zfmisc_1(sK0)) ),
    inference(forward_demodulation,[],[f206,f208])).

fof(f206,plain,(
    ! [X0] : m1_subset_1(k8_relset_1(sK0,sK1,sK2,X0),k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f114,f169])).

fof(f169,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t184_funct_2.p',dt_k8_relset_1)).

fof(f621,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(k10_relat_1(sK2,X2),k1_zfmisc_1(sK0))
      | r2_hidden(k8_relset_1(sK0,sK1,sK2,X2),k6_funct_2(sK0,sK1,sK2,X3))
      | ~ r2_hidden(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(sK1))
      | ~ m1_subset_1(k6_funct_2(sK0,sK1,sK2,X3),k1_zfmisc_1(k1_zfmisc_1(sK0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(sK1)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_2(sK2,sK0,sK1)
      | ~ v1_funct_1(sK2)
      | v1_xboole_0(sK1)
      | v1_xboole_0(sK0) ) ),
    inference(superposition,[],[f176,f208])).

fof(f176,plain,(
    ! [X2,X0,X3,X1,X9] :
      ( r2_hidden(k8_relset_1(X0,X1,X2,X9),k6_funct_2(X0,X1,X2,X3))
      | ~ r2_hidden(X9,X3)
      | ~ m1_subset_1(X9,k1_zfmisc_1(X1))
      | ~ m1_subset_1(k8_relset_1(X0,X1,X2,X9),k1_zfmisc_1(X0))
      | ~ m1_subset_1(k6_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(equality_resolution,[],[f175])).

fof(f175,plain,(
    ! [X4,X2,X0,X3,X1,X9] :
      ( r2_hidden(k8_relset_1(X0,X1,X2,X9),X4)
      | ~ r2_hidden(X9,X3)
      | ~ m1_subset_1(X9,k1_zfmisc_1(X1))
      | ~ m1_subset_1(k8_relset_1(X0,X1,X2,X9),k1_zfmisc_1(X0))
      | k6_funct_2(X0,X1,X2,X3) != X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(equality_resolution,[],[f121])).

fof(f121,plain,(
    ! [X4,X2,X0,X8,X3,X1,X9] :
      ( r2_hidden(X8,X4)
      | k8_relset_1(X0,X1,X2,X9) != X8
      | ~ r2_hidden(X9,X3)
      | ~ m1_subset_1(X9,k1_zfmisc_1(X1))
      | ~ m1_subset_1(X8,k1_zfmisc_1(X0))
      | k6_funct_2(X0,X1,X2,X3) != X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f86,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( k6_funct_2(X0,X1,X2,X3) = X4
                          | ( ( ! [X6] :
                                  ( k8_relset_1(X0,X1,X2,X6) != sK4(X0,X1,X2,X3,X4)
                                  | ~ r2_hidden(X6,X3)
                                  | ~ m1_subset_1(X6,k1_zfmisc_1(X1)) )
                              | ~ r2_hidden(sK4(X0,X1,X2,X3,X4),X4) )
                            & ( ( k8_relset_1(X0,X1,X2,sK5(X0,X1,X2,X3,X4)) = sK4(X0,X1,X2,X3,X4)
                                & r2_hidden(sK5(X0,X1,X2,X3,X4),X3)
                                & m1_subset_1(sK5(X0,X1,X2,X3,X4),k1_zfmisc_1(X1)) )
                              | r2_hidden(sK4(X0,X1,X2,X3,X4),X4) )
                            & m1_subset_1(sK4(X0,X1,X2,X3,X4),k1_zfmisc_1(X0)) ) )
                        & ( ! [X8] :
                              ( ( ( r2_hidden(X8,X4)
                                  | ! [X9] :
                                      ( k8_relset_1(X0,X1,X2,X9) != X8
                                      | ~ r2_hidden(X9,X3)
                                      | ~ m1_subset_1(X9,k1_zfmisc_1(X1)) ) )
                                & ( ( k8_relset_1(X0,X1,X2,sK6(X0,X1,X2,X3,X8)) = X8
                                    & r2_hidden(sK6(X0,X1,X2,X3,X8),X3)
                                    & m1_subset_1(sK6(X0,X1,X2,X3,X8),k1_zfmisc_1(X1)) )
                                  | ~ r2_hidden(X8,X4) ) )
                              | ~ m1_subset_1(X8,k1_zfmisc_1(X0)) )
                          | k6_funct_2(X0,X1,X2,X3) != X4 ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X0))) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X2,X0,X1)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f82,f85,f84,f83])).

fof(f83,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( ( ! [X6] :
                ( k8_relset_1(X0,X1,X2,X6) != X5
                | ~ r2_hidden(X6,X3)
                | ~ m1_subset_1(X6,k1_zfmisc_1(X1)) )
            | ~ r2_hidden(X5,X4) )
          & ( ? [X7] :
                ( k8_relset_1(X0,X1,X2,X7) = X5
                & r2_hidden(X7,X3)
                & m1_subset_1(X7,k1_zfmisc_1(X1)) )
            | r2_hidden(X5,X4) )
          & m1_subset_1(X5,k1_zfmisc_1(X0)) )
     => ( ( ! [X6] :
              ( k8_relset_1(X0,X1,X2,X6) != sK4(X0,X1,X2,X3,X4)
              | ~ r2_hidden(X6,X3)
              | ~ m1_subset_1(X6,k1_zfmisc_1(X1)) )
          | ~ r2_hidden(sK4(X0,X1,X2,X3,X4),X4) )
        & ( ? [X7] :
              ( k8_relset_1(X0,X1,X2,X7) = sK4(X0,X1,X2,X3,X4)
              & r2_hidden(X7,X3)
              & m1_subset_1(X7,k1_zfmisc_1(X1)) )
          | r2_hidden(sK4(X0,X1,X2,X3,X4),X4) )
        & m1_subset_1(sK4(X0,X1,X2,X3,X4),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f84,plain,(
    ! [X5,X4,X3,X2,X1,X0] :
      ( ? [X7] :
          ( k8_relset_1(X0,X1,X2,X7) = X5
          & r2_hidden(X7,X3)
          & m1_subset_1(X7,k1_zfmisc_1(X1)) )
     => ( k8_relset_1(X0,X1,X2,sK5(X0,X1,X2,X3,X4)) = X5
        & r2_hidden(sK5(X0,X1,X2,X3,X4),X3)
        & m1_subset_1(sK5(X0,X1,X2,X3,X4),k1_zfmisc_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f85,plain,(
    ! [X8,X3,X2,X1,X0] :
      ( ? [X10] :
          ( k8_relset_1(X0,X1,X2,X10) = X8
          & r2_hidden(X10,X3)
          & m1_subset_1(X10,k1_zfmisc_1(X1)) )
     => ( k8_relset_1(X0,X1,X2,sK6(X0,X1,X2,X3,X8)) = X8
        & r2_hidden(sK6(X0,X1,X2,X3,X8),X3)
        & m1_subset_1(sK6(X0,X1,X2,X3,X8),k1_zfmisc_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f82,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( k6_funct_2(X0,X1,X2,X3) = X4
                          | ? [X5] :
                              ( ( ! [X6] :
                                    ( k8_relset_1(X0,X1,X2,X6) != X5
                                    | ~ r2_hidden(X6,X3)
                                    | ~ m1_subset_1(X6,k1_zfmisc_1(X1)) )
                                | ~ r2_hidden(X5,X4) )
                              & ( ? [X7] :
                                    ( k8_relset_1(X0,X1,X2,X7) = X5
                                    & r2_hidden(X7,X3)
                                    & m1_subset_1(X7,k1_zfmisc_1(X1)) )
                                | r2_hidden(X5,X4) )
                              & m1_subset_1(X5,k1_zfmisc_1(X0)) ) )
                        & ( ! [X8] :
                              ( ( ( r2_hidden(X8,X4)
                                  | ! [X9] :
                                      ( k8_relset_1(X0,X1,X2,X9) != X8
                                      | ~ r2_hidden(X9,X3)
                                      | ~ m1_subset_1(X9,k1_zfmisc_1(X1)) ) )
                                & ( ? [X10] :
                                      ( k8_relset_1(X0,X1,X2,X10) = X8
                                      & r2_hidden(X10,X3)
                                      & m1_subset_1(X10,k1_zfmisc_1(X1)) )
                                  | ~ r2_hidden(X8,X4) ) )
                              | ~ m1_subset_1(X8,k1_zfmisc_1(X0)) )
                          | k6_funct_2(X0,X1,X2,X3) != X4 ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X0))) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X2,X0,X1)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(rectify,[],[f81])).

fof(f81,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( k6_funct_2(X0,X1,X2,X3) = X4
                          | ? [X5] :
                              ( ( ! [X6] :
                                    ( k8_relset_1(X0,X1,X2,X6) != X5
                                    | ~ r2_hidden(X6,X3)
                                    | ~ m1_subset_1(X6,k1_zfmisc_1(X1)) )
                                | ~ r2_hidden(X5,X4) )
                              & ( ? [X6] :
                                    ( k8_relset_1(X0,X1,X2,X6) = X5
                                    & r2_hidden(X6,X3)
                                    & m1_subset_1(X6,k1_zfmisc_1(X1)) )
                                | r2_hidden(X5,X4) )
                              & m1_subset_1(X5,k1_zfmisc_1(X0)) ) )
                        & ( ! [X5] :
                              ( ( ( r2_hidden(X5,X4)
                                  | ! [X6] :
                                      ( k8_relset_1(X0,X1,X2,X6) != X5
                                      | ~ r2_hidden(X6,X3)
                                      | ~ m1_subset_1(X6,k1_zfmisc_1(X1)) ) )
                                & ( ? [X6] :
                                      ( k8_relset_1(X0,X1,X2,X6) = X5
                                      & r2_hidden(X6,X3)
                                      & m1_subset_1(X6,k1_zfmisc_1(X1)) )
                                  | ~ r2_hidden(X5,X4) ) )
                              | ~ m1_subset_1(X5,k1_zfmisc_1(X0)) )
                          | k6_funct_2(X0,X1,X2,X3) != X4 ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X0))) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X2,X0,X1)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f80])).

fof(f80,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( k6_funct_2(X0,X1,X2,X3) = X4
                          | ? [X5] :
                              ( ( ! [X6] :
                                    ( k8_relset_1(X0,X1,X2,X6) != X5
                                    | ~ r2_hidden(X6,X3)
                                    | ~ m1_subset_1(X6,k1_zfmisc_1(X1)) )
                                | ~ r2_hidden(X5,X4) )
                              & ( ? [X6] :
                                    ( k8_relset_1(X0,X1,X2,X6) = X5
                                    & r2_hidden(X6,X3)
                                    & m1_subset_1(X6,k1_zfmisc_1(X1)) )
                                | r2_hidden(X5,X4) )
                              & m1_subset_1(X5,k1_zfmisc_1(X0)) ) )
                        & ( ! [X5] :
                              ( ( ( r2_hidden(X5,X4)
                                  | ! [X6] :
                                      ( k8_relset_1(X0,X1,X2,X6) != X5
                                      | ~ r2_hidden(X6,X3)
                                      | ~ m1_subset_1(X6,k1_zfmisc_1(X1)) ) )
                                & ( ? [X6] :
                                      ( k8_relset_1(X0,X1,X2,X6) = X5
                                      & r2_hidden(X6,X3)
                                      & m1_subset_1(X6,k1_zfmisc_1(X1)) )
                                  | ~ r2_hidden(X5,X4) ) )
                              | ~ m1_subset_1(X5,k1_zfmisc_1(X0)) )
                          | k6_funct_2(X0,X1,X2,X3) != X4 ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X0))) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X2,X0,X1)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( k6_funct_2(X0,X1,X2,X3) = X4
                      <=> ! [X5] :
                            ( ( r2_hidden(X5,X4)
                            <=> ? [X6] :
                                  ( k8_relset_1(X0,X1,X2,X6) = X5
                                  & r2_hidden(X6,X3)
                                  & m1_subset_1(X6,k1_zfmisc_1(X1)) ) )
                            | ~ m1_subset_1(X5,k1_zfmisc_1(X0)) ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X0))) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X2,X0,X1)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( k6_funct_2(X0,X1,X2,X3) = X4
                      <=> ! [X5] :
                            ( ( r2_hidden(X5,X4)
                            <=> ? [X6] :
                                  ( k8_relset_1(X0,X1,X2,X6) = X5
                                  & r2_hidden(X6,X3)
                                  & m1_subset_1(X6,k1_zfmisc_1(X1)) ) )
                            | ~ m1_subset_1(X5,k1_zfmisc_1(X0)) ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X0))) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X2,X0,X1)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X2,X0,X1)
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X0)))
                     => ( k6_funct_2(X0,X1,X2,X3) = X4
                      <=> ! [X5] :
                            ( m1_subset_1(X5,k1_zfmisc_1(X0))
                           => ( r2_hidden(X5,X4)
                            <=> ? [X6] :
                                  ( k8_relset_1(X0,X1,X2,X6) = X5
                                  & r2_hidden(X6,X3)
                                  & m1_subset_1(X6,k1_zfmisc_1(X1)) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t184_funct_2.p',d10_funct_2)).

fof(f2055,plain,
    ( r2_hidden(k9_relat_1(sK2,sK14(sK3,sK11(k3_tarski(sK3),k3_tarski(k6_funct_2(sK0,sK1,sK2,k7_funct_2(sK0,sK1,sK2,sK3)))))),k7_funct_2(sK0,sK1,sK2,sK3))
    | ~ spl17_0 ),
    inference(unit_resulting_resolution,[],[f878,f115,f211,f611])).

fof(f611,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,X3)
      | r2_hidden(k9_relat_1(sK2,X2),k7_funct_2(sK0,sK1,sK2,X3))
      | ~ m1_subset_1(k7_funct_2(sK0,sK1,sK2,X3),k1_zfmisc_1(k1_zfmisc_1(sK1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    inference(forward_demodulation,[],[f610,f207])).

fof(f207,plain,(
    ! [X0] : k7_relset_1(sK0,sK1,sK2,X0) = k9_relat_1(sK2,X0) ),
    inference(unit_resulting_resolution,[],[f114,f170])).

fof(f170,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t184_funct_2.p',redefinition_k7_relset_1)).

fof(f610,plain,(
    ! [X2,X3] :
      ( r2_hidden(k7_relset_1(sK0,sK1,sK2,X2),k7_funct_2(sK0,sK1,sK2,X3))
      | ~ r2_hidden(X2,X3)
      | ~ m1_subset_1(k7_funct_2(sK0,sK1,sK2,X3),k1_zfmisc_1(k1_zfmisc_1(sK1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    inference(subsumption_resolution,[],[f609,f166])).

fof(f609,plain,(
    ! [X2,X3] :
      ( r2_hidden(k7_relset_1(sK0,sK1,sK2,X2),k7_funct_2(sK0,sK1,sK2,X3))
      | ~ r2_hidden(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(sK0))
      | ~ m1_subset_1(k7_funct_2(sK0,sK1,sK2,X3),k1_zfmisc_1(k1_zfmisc_1(sK1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    inference(subsumption_resolution,[],[f608,f110])).

fof(f608,plain,(
    ! [X2,X3] :
      ( r2_hidden(k7_relset_1(sK0,sK1,sK2,X2),k7_funct_2(sK0,sK1,sK2,X3))
      | ~ r2_hidden(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(sK0))
      | ~ m1_subset_1(k7_funct_2(sK0,sK1,sK2,X3),k1_zfmisc_1(k1_zfmisc_1(sK1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(sK0)))
      | v1_xboole_0(sK0) ) ),
    inference(subsumption_resolution,[],[f607,f111])).

fof(f607,plain,(
    ! [X2,X3] :
      ( r2_hidden(k7_relset_1(sK0,sK1,sK2,X2),k7_funct_2(sK0,sK1,sK2,X3))
      | ~ r2_hidden(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(sK0))
      | ~ m1_subset_1(k7_funct_2(sK0,sK1,sK2,X3),k1_zfmisc_1(k1_zfmisc_1(sK1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(sK0)))
      | v1_xboole_0(sK1)
      | v1_xboole_0(sK0) ) ),
    inference(subsumption_resolution,[],[f606,f112])).

fof(f606,plain,(
    ! [X2,X3] :
      ( r2_hidden(k7_relset_1(sK0,sK1,sK2,X2),k7_funct_2(sK0,sK1,sK2,X3))
      | ~ r2_hidden(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(sK0))
      | ~ m1_subset_1(k7_funct_2(sK0,sK1,sK2,X3),k1_zfmisc_1(k1_zfmisc_1(sK1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(sK0)))
      | ~ v1_funct_1(sK2)
      | v1_xboole_0(sK1)
      | v1_xboole_0(sK0) ) ),
    inference(subsumption_resolution,[],[f605,f113])).

fof(f605,plain,(
    ! [X2,X3] :
      ( r2_hidden(k7_relset_1(sK0,sK1,sK2,X2),k7_funct_2(sK0,sK1,sK2,X3))
      | ~ r2_hidden(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(sK0))
      | ~ m1_subset_1(k7_funct_2(sK0,sK1,sK2,X3),k1_zfmisc_1(k1_zfmisc_1(sK1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(sK0)))
      | ~ v1_funct_2(sK2,sK0,sK1)
      | ~ v1_funct_1(sK2)
      | v1_xboole_0(sK1)
      | v1_xboole_0(sK0) ) ),
    inference(subsumption_resolution,[],[f604,f114])).

fof(f604,plain,(
    ! [X2,X3] :
      ( r2_hidden(k7_relset_1(sK0,sK1,sK2,X2),k7_funct_2(sK0,sK1,sK2,X3))
      | ~ r2_hidden(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(sK0))
      | ~ m1_subset_1(k7_funct_2(sK0,sK1,sK2,X3),k1_zfmisc_1(k1_zfmisc_1(sK1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(sK0)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_2(sK2,sK0,sK1)
      | ~ v1_funct_1(sK2)
      | v1_xboole_0(sK1)
      | v1_xboole_0(sK0) ) ),
    inference(subsumption_resolution,[],[f588,f214])).

fof(f214,plain,(
    ! [X0] : m1_subset_1(k9_relat_1(sK2,X0),k1_zfmisc_1(sK1)) ),
    inference(forward_demodulation,[],[f205,f207])).

fof(f205,plain,(
    ! [X0] : m1_subset_1(k7_relset_1(sK0,sK1,sK2,X0),k1_zfmisc_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f114,f168])).

fof(f168,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t184_funct_2.p',dt_k7_relset_1)).

fof(f588,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(k9_relat_1(sK2,X2),k1_zfmisc_1(sK1))
      | r2_hidden(k7_relset_1(sK0,sK1,sK2,X2),k7_funct_2(sK0,sK1,sK2,X3))
      | ~ r2_hidden(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(sK0))
      | ~ m1_subset_1(k7_funct_2(sK0,sK1,sK2,X3),k1_zfmisc_1(k1_zfmisc_1(sK1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(sK0)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_2(sK2,sK0,sK1)
      | ~ v1_funct_1(sK2)
      | v1_xboole_0(sK1)
      | v1_xboole_0(sK0) ) ),
    inference(superposition,[],[f181,f207])).

fof(f181,plain,(
    ! [X2,X0,X3,X1,X9] :
      ( r2_hidden(k7_relset_1(X0,X1,X2,X9),k7_funct_2(X0,X1,X2,X3))
      | ~ r2_hidden(X9,X3)
      | ~ m1_subset_1(X9,k1_zfmisc_1(X0))
      | ~ m1_subset_1(k7_relset_1(X0,X1,X2,X9),k1_zfmisc_1(X1))
      | ~ m1_subset_1(k7_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(equality_resolution,[],[f180])).

fof(f180,plain,(
    ! [X4,X2,X0,X3,X1,X9] :
      ( r2_hidden(k7_relset_1(X0,X1,X2,X9),X4)
      | ~ r2_hidden(X9,X3)
      | ~ m1_subset_1(X9,k1_zfmisc_1(X0))
      | ~ m1_subset_1(k7_relset_1(X0,X1,X2,X9),k1_zfmisc_1(X1))
      | k7_funct_2(X0,X1,X2,X3) != X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(equality_resolution,[],[f130])).

fof(f130,plain,(
    ! [X4,X2,X0,X8,X3,X1,X9] :
      ( r2_hidden(X8,X4)
      | k7_relset_1(X0,X1,X2,X9) != X8
      | ~ r2_hidden(X9,X3)
      | ~ m1_subset_1(X9,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X8,k1_zfmisc_1(X1))
      | k7_funct_2(X0,X1,X2,X3) != X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f93])).

fof(f93,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( k7_funct_2(X0,X1,X2,X3) = X4
                          | ( ( ! [X6] :
                                  ( k7_relset_1(X0,X1,X2,X6) != sK7(X0,X1,X2,X3,X4)
                                  | ~ r2_hidden(X6,X3)
                                  | ~ m1_subset_1(X6,k1_zfmisc_1(X0)) )
                              | ~ r2_hidden(sK7(X0,X1,X2,X3,X4),X4) )
                            & ( ( k7_relset_1(X0,X1,X2,sK8(X0,X1,X2,X3,X4)) = sK7(X0,X1,X2,X3,X4)
                                & r2_hidden(sK8(X0,X1,X2,X3,X4),X3)
                                & m1_subset_1(sK8(X0,X1,X2,X3,X4),k1_zfmisc_1(X0)) )
                              | r2_hidden(sK7(X0,X1,X2,X3,X4),X4) )
                            & m1_subset_1(sK7(X0,X1,X2,X3,X4),k1_zfmisc_1(X1)) ) )
                        & ( ! [X8] :
                              ( ( ( r2_hidden(X8,X4)
                                  | ! [X9] :
                                      ( k7_relset_1(X0,X1,X2,X9) != X8
                                      | ~ r2_hidden(X9,X3)
                                      | ~ m1_subset_1(X9,k1_zfmisc_1(X0)) ) )
                                & ( ( k7_relset_1(X0,X1,X2,sK9(X0,X1,X2,X3,X8)) = X8
                                    & r2_hidden(sK9(X0,X1,X2,X3,X8),X3)
                                    & m1_subset_1(sK9(X0,X1,X2,X3,X8),k1_zfmisc_1(X0)) )
                                  | ~ r2_hidden(X8,X4) ) )
                              | ~ m1_subset_1(X8,k1_zfmisc_1(X1)) )
                          | k7_funct_2(X0,X1,X2,X3) != X4 ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1))) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X2,X0,X1)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f89,f92,f91,f90])).

fof(f90,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( ( ! [X6] :
                ( k7_relset_1(X0,X1,X2,X6) != X5
                | ~ r2_hidden(X6,X3)
                | ~ m1_subset_1(X6,k1_zfmisc_1(X0)) )
            | ~ r2_hidden(X5,X4) )
          & ( ? [X7] :
                ( k7_relset_1(X0,X1,X2,X7) = X5
                & r2_hidden(X7,X3)
                & m1_subset_1(X7,k1_zfmisc_1(X0)) )
            | r2_hidden(X5,X4) )
          & m1_subset_1(X5,k1_zfmisc_1(X1)) )
     => ( ( ! [X6] :
              ( k7_relset_1(X0,X1,X2,X6) != sK7(X0,X1,X2,X3,X4)
              | ~ r2_hidden(X6,X3)
              | ~ m1_subset_1(X6,k1_zfmisc_1(X0)) )
          | ~ r2_hidden(sK7(X0,X1,X2,X3,X4),X4) )
        & ( ? [X7] :
              ( k7_relset_1(X0,X1,X2,X7) = sK7(X0,X1,X2,X3,X4)
              & r2_hidden(X7,X3)
              & m1_subset_1(X7,k1_zfmisc_1(X0)) )
          | r2_hidden(sK7(X0,X1,X2,X3,X4),X4) )
        & m1_subset_1(sK7(X0,X1,X2,X3,X4),k1_zfmisc_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f91,plain,(
    ! [X5,X4,X3,X2,X1,X0] :
      ( ? [X7] :
          ( k7_relset_1(X0,X1,X2,X7) = X5
          & r2_hidden(X7,X3)
          & m1_subset_1(X7,k1_zfmisc_1(X0)) )
     => ( k7_relset_1(X0,X1,X2,sK8(X0,X1,X2,X3,X4)) = X5
        & r2_hidden(sK8(X0,X1,X2,X3,X4),X3)
        & m1_subset_1(sK8(X0,X1,X2,X3,X4),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f92,plain,(
    ! [X8,X3,X2,X1,X0] :
      ( ? [X10] :
          ( k7_relset_1(X0,X1,X2,X10) = X8
          & r2_hidden(X10,X3)
          & m1_subset_1(X10,k1_zfmisc_1(X0)) )
     => ( k7_relset_1(X0,X1,X2,sK9(X0,X1,X2,X3,X8)) = X8
        & r2_hidden(sK9(X0,X1,X2,X3,X8),X3)
        & m1_subset_1(sK9(X0,X1,X2,X3,X8),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f89,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( k7_funct_2(X0,X1,X2,X3) = X4
                          | ? [X5] :
                              ( ( ! [X6] :
                                    ( k7_relset_1(X0,X1,X2,X6) != X5
                                    | ~ r2_hidden(X6,X3)
                                    | ~ m1_subset_1(X6,k1_zfmisc_1(X0)) )
                                | ~ r2_hidden(X5,X4) )
                              & ( ? [X7] :
                                    ( k7_relset_1(X0,X1,X2,X7) = X5
                                    & r2_hidden(X7,X3)
                                    & m1_subset_1(X7,k1_zfmisc_1(X0)) )
                                | r2_hidden(X5,X4) )
                              & m1_subset_1(X5,k1_zfmisc_1(X1)) ) )
                        & ( ! [X8] :
                              ( ( ( r2_hidden(X8,X4)
                                  | ! [X9] :
                                      ( k7_relset_1(X0,X1,X2,X9) != X8
                                      | ~ r2_hidden(X9,X3)
                                      | ~ m1_subset_1(X9,k1_zfmisc_1(X0)) ) )
                                & ( ? [X10] :
                                      ( k7_relset_1(X0,X1,X2,X10) = X8
                                      & r2_hidden(X10,X3)
                                      & m1_subset_1(X10,k1_zfmisc_1(X0)) )
                                  | ~ r2_hidden(X8,X4) ) )
                              | ~ m1_subset_1(X8,k1_zfmisc_1(X1)) )
                          | k7_funct_2(X0,X1,X2,X3) != X4 ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1))) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X2,X0,X1)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(rectify,[],[f88])).

fof(f88,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( k7_funct_2(X0,X1,X2,X3) = X4
                          | ? [X5] :
                              ( ( ! [X6] :
                                    ( k7_relset_1(X0,X1,X2,X6) != X5
                                    | ~ r2_hidden(X6,X3)
                                    | ~ m1_subset_1(X6,k1_zfmisc_1(X0)) )
                                | ~ r2_hidden(X5,X4) )
                              & ( ? [X6] :
                                    ( k7_relset_1(X0,X1,X2,X6) = X5
                                    & r2_hidden(X6,X3)
                                    & m1_subset_1(X6,k1_zfmisc_1(X0)) )
                                | r2_hidden(X5,X4) )
                              & m1_subset_1(X5,k1_zfmisc_1(X1)) ) )
                        & ( ! [X5] :
                              ( ( ( r2_hidden(X5,X4)
                                  | ! [X6] :
                                      ( k7_relset_1(X0,X1,X2,X6) != X5
                                      | ~ r2_hidden(X6,X3)
                                      | ~ m1_subset_1(X6,k1_zfmisc_1(X0)) ) )
                                & ( ? [X6] :
                                      ( k7_relset_1(X0,X1,X2,X6) = X5
                                      & r2_hidden(X6,X3)
                                      & m1_subset_1(X6,k1_zfmisc_1(X0)) )
                                  | ~ r2_hidden(X5,X4) ) )
                              | ~ m1_subset_1(X5,k1_zfmisc_1(X1)) )
                          | k7_funct_2(X0,X1,X2,X3) != X4 ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1))) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X2,X0,X1)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f87])).

fof(f87,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( k7_funct_2(X0,X1,X2,X3) = X4
                          | ? [X5] :
                              ( ( ! [X6] :
                                    ( k7_relset_1(X0,X1,X2,X6) != X5
                                    | ~ r2_hidden(X6,X3)
                                    | ~ m1_subset_1(X6,k1_zfmisc_1(X0)) )
                                | ~ r2_hidden(X5,X4) )
                              & ( ? [X6] :
                                    ( k7_relset_1(X0,X1,X2,X6) = X5
                                    & r2_hidden(X6,X3)
                                    & m1_subset_1(X6,k1_zfmisc_1(X0)) )
                                | r2_hidden(X5,X4) )
                              & m1_subset_1(X5,k1_zfmisc_1(X1)) ) )
                        & ( ! [X5] :
                              ( ( ( r2_hidden(X5,X4)
                                  | ! [X6] :
                                      ( k7_relset_1(X0,X1,X2,X6) != X5
                                      | ~ r2_hidden(X6,X3)
                                      | ~ m1_subset_1(X6,k1_zfmisc_1(X0)) ) )
                                & ( ? [X6] :
                                      ( k7_relset_1(X0,X1,X2,X6) = X5
                                      & r2_hidden(X6,X3)
                                      & m1_subset_1(X6,k1_zfmisc_1(X0)) )
                                  | ~ r2_hidden(X5,X4) ) )
                              | ~ m1_subset_1(X5,k1_zfmisc_1(X1)) )
                          | k7_funct_2(X0,X1,X2,X3) != X4 ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1))) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X2,X0,X1)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( k7_funct_2(X0,X1,X2,X3) = X4
                      <=> ! [X5] :
                            ( ( r2_hidden(X5,X4)
                            <=> ? [X6] :
                                  ( k7_relset_1(X0,X1,X2,X6) = X5
                                  & r2_hidden(X6,X3)
                                  & m1_subset_1(X6,k1_zfmisc_1(X0)) ) )
                            | ~ m1_subset_1(X5,k1_zfmisc_1(X1)) ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1))) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X2,X0,X1)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( k7_funct_2(X0,X1,X2,X3) = X4
                      <=> ! [X5] :
                            ( ( r2_hidden(X5,X4)
                            <=> ? [X6] :
                                  ( k7_relset_1(X0,X1,X2,X6) = X5
                                  & r2_hidden(X6,X3)
                                  & m1_subset_1(X6,k1_zfmisc_1(X0)) ) )
                            | ~ m1_subset_1(X5,k1_zfmisc_1(X1)) ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1))) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X2,X0,X1)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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
                      ( m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1)))
                     => ( k7_funct_2(X0,X1,X2,X3) = X4
                      <=> ! [X5] :
                            ( m1_subset_1(X5,k1_zfmisc_1(X1))
                           => ( r2_hidden(X5,X4)
                            <=> ? [X6] :
                                  ( k7_relset_1(X0,X1,X2,X6) = X5
                                  & r2_hidden(X6,X3)
                                  & m1_subset_1(X6,k1_zfmisc_1(X0)) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t184_funct_2.p',d11_funct_2)).

fof(f211,plain,(
    m1_subset_1(k7_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(unit_resulting_resolution,[],[f110,f111,f112,f113,f115,f114,f173])).

fof(f173,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f73])).

fof(f73,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k7_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t184_funct_2.p',dt_k7_funct_2)).

fof(f706,plain,
    ( ~ r2_hidden(sK11(k3_tarski(sK3),k3_tarski(k6_funct_2(sK0,sK1,sK2,k7_funct_2(sK0,sK1,sK2,sK3)))),k3_tarski(k6_funct_2(sK0,sK1,sK2,k7_funct_2(sK0,sK1,sK2,sK3))))
    | ~ spl17_0 ),
    inference(backward_demodulation,[],[f689,f218])).

fof(f218,plain,(
    ~ r2_hidden(sK11(k3_tarski(sK3),k5_setfam_1(sK0,k6_funct_2(sK0,sK1,sK2,k7_funct_2(sK0,sK1,sK2,sK3)))),k5_setfam_1(sK0,k6_funct_2(sK0,sK1,sK2,k7_funct_2(sK0,sK1,sK2,sK3)))) ),
    inference(unit_resulting_resolution,[],[f201,f146])).

fof(f146,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK11(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f99])).

fof(f877,plain,
    ( r2_hidden(sK11(k3_tarski(sK3),k3_tarski(k6_funct_2(sK0,sK1,sK2,k7_funct_2(sK0,sK1,sK2,sK3)))),sK14(sK3,sK11(k3_tarski(sK3),k3_tarski(k6_funct_2(sK0,sK1,sK2,k7_funct_2(sK0,sK1,sK2,sK3))))))
    | ~ spl17_0 ),
    inference(unit_resulting_resolution,[],[f705,f187])).

fof(f187,plain,(
    ! [X0,X5] :
      ( r2_hidden(X5,sK14(X0,X5))
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f147])).

fof(f147,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,sK14(X0,X5))
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f105])).

fof(f662,plain,(
    spl17_0 ),
    inference(avatar_split_clause,[],[f653,f298])).

fof(f653,plain,(
    m1_subset_1(k6_funct_2(sK0,sK1,sK2,k7_funct_2(sK0,sK1,sK2,sK3)),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(unit_resulting_resolution,[],[f110,f111,f112,f113,f114,f211,f172])).

fof(f172,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k6_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k6_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f71])).

fof(f71,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k6_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t184_funct_2.p',dt_k6_funct_2)).

fof(f504,plain,(
    ~ spl17_4 ),
    inference(avatar_contradiction_clause,[],[f491])).

fof(f491,plain,
    ( $false
    | ~ spl17_4 ),
    inference(unit_resulting_resolution,[],[f117,f413])).

fof(f413,plain,
    ( ! [X0] : ~ v1_xboole_0(X0)
    | ~ spl17_4 ),
    inference(duplicate_literal_removal,[],[f412])).

fof(f412,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | ~ v1_xboole_0(X0) )
    | ~ spl17_4 ),
    inference(superposition,[],[f353,f136])).

fof(f136,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t184_funct_2.p',t6_boole)).

fof(f353,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl17_4 ),
    inference(backward_demodulation,[],[f342,f111])).

fof(f342,plain,
    ( k1_xboole_0 = sK1
    | ~ spl17_4 ),
    inference(avatar_component_clause,[],[f341])).

fof(f341,plain,
    ( spl17_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_4])])).

fof(f117,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t184_funct_2.p',dt_o_0_0_xboole_0)).

fof(f352,plain,
    ( spl17_4
    | spl17_6 ),
    inference(avatar_split_clause,[],[f351,f347,f341])).

fof(f351,plain,
    ( k1_relat_1(sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f350,f114])).

fof(f350,plain,
    ( k1_relat_1(sK2) = sK0
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f332,f113])).

fof(f332,plain,
    ( k1_relat_1(sK2) = sK0
    | ~ v1_funct_2(sK2,sK0,sK1)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f160,f203])).

fof(f203,plain,(
    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f114,f158])).

fof(f158,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t184_funct_2.p',redefinition_k1_relset_1)).

fof(f160,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f107])).

fof(f107,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f63])).

fof(f63,plain,(
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
    inference(flattening,[],[f62])).

fof(f62,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox/benchmark/funct_2__t184_funct_2.p',d1_funct_2)).
%------------------------------------------------------------------------------
