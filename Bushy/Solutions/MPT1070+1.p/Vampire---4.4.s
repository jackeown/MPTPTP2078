%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_2__t187_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:38 EDT 2019

% Result     : Theorem 28.21s
% Output     : Refutation 28.21s
% Verified   : 
% Statistics : Number of formulae       :  322 (1756 expanded)
%              Number of leaves         :   50 ( 733 expanded)
%              Depth                    :   24
%              Number of atoms          : 1359 (17198 expanded)
%              Number of equality atoms :   80 ( 205 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15400,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f426,f473,f2629,f2675,f3172,f3511,f3794,f3849,f4092,f4153,f4165,f4168,f4201,f4411,f4547,f5508,f5527,f5795,f7146,f15399])).

fof(f15399,plain,
    ( spl9_115
    | spl9_131
    | ~ spl9_172
    | ~ spl9_180
    | ~ spl9_444 ),
    inference(avatar_contradiction_clause,[],[f15398])).

fof(f15398,plain,
    ( $false
    | ~ spl9_115
    | ~ spl9_131
    | ~ spl9_172
    | ~ spl9_180
    | ~ spl9_444 ),
    inference(subsumption_resolution,[],[f15397,f155])).

fof(f155,plain,(
    v1_relat_1(sK6) ),
    inference(resolution,[],[f116,f100])).

fof(f100,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f83])).

fof(f83,plain,
    ( ~ r2_funct_2(sK2,sK1,k1_partfun1(sK2,sK2,sK2,sK1,sK6,k8_funct_2(sK2,sK3,sK1,sK4,sK5)),k8_funct_2(sK2,sK3,sK1,k1_partfun1(sK2,sK2,sK2,sK3,sK6,sK4),sK5))
    & r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5))
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    & v1_funct_2(sK6,sK2,sK2)
    & v1_funct_1(sK6)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    & v1_funct_1(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK4,sK2,sK3)
    & v1_funct_1(sK4)
    & ~ v1_xboole_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6])],[f39,f82,f81,f80,f79])).

fof(f79,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ~ r2_funct_2(X1,X0,k1_partfun1(X1,X1,X1,X0,X5,k8_funct_2(X1,X2,X0,X3,X4)),k8_funct_2(X1,X2,X0,k1_partfun1(X1,X1,X1,X2,X5,X3),X4))
                    & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
                    & v1_funct_2(X5,X1,X1)
                    & v1_funct_1(X5) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
        & ~ v1_xboole_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ~ r2_funct_2(sK2,sK1,k1_partfun1(sK2,sK2,sK2,sK1,X5,k8_funct_2(sK2,sK3,sK1,X3,X4)),k8_funct_2(sK2,sK3,sK1,k1_partfun1(sK2,sK2,sK2,sK3,X5,X3),X4))
                  & r1_tarski(k2_relset_1(sK2,sK3,X3),k1_relset_1(sK3,sK1,X4))
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
                  & v1_funct_2(X5,sK2,sK2)
                  & v1_funct_1(X5) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
          & v1_funct_2(X3,sK2,sK3)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ~ r2_funct_2(X1,X0,k1_partfun1(X1,X1,X1,X0,X5,k8_funct_2(X1,X2,X0,X3,X4)),k8_funct_2(X1,X2,X0,k1_partfun1(X1,X1,X1,X2,X5,X3),X4))
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
                  & v1_funct_2(X5,X1,X1)
                  & v1_funct_1(X5) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ~ r2_funct_2(X1,X0,k1_partfun1(X1,X1,X1,X0,X5,k8_funct_2(X1,X2,X0,sK4,X4)),k8_funct_2(X1,X2,X0,k1_partfun1(X1,X1,X1,X2,X5,sK4),X4))
                & r1_tarski(k2_relset_1(X1,X2,sK4),k1_relset_1(X2,X0,X4))
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
                & v1_funct_2(X5,X1,X1)
                & v1_funct_1(X5) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
            & v1_funct_1(X4) )
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(sK4,X1,X2)
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ~ r2_funct_2(X1,X0,k1_partfun1(X1,X1,X1,X0,X5,k8_funct_2(X1,X2,X0,X3,X4)),k8_funct_2(X1,X2,X0,k1_partfun1(X1,X1,X1,X2,X5,X3),X4))
              & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
              & v1_funct_2(X5,X1,X1)
              & v1_funct_1(X5) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
          & v1_funct_1(X4) )
     => ( ? [X5] :
            ( ~ r2_funct_2(X1,X0,k1_partfun1(X1,X1,X1,X0,X5,k8_funct_2(X1,X2,X0,X3,sK5)),k8_funct_2(X1,X2,X0,k1_partfun1(X1,X1,X1,X2,X5,X3),sK5))
            & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,sK5))
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
            & v1_funct_2(X5,X1,X1)
            & v1_funct_1(X5) )
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f82,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ~ r2_funct_2(X1,X0,k1_partfun1(X1,X1,X1,X0,X5,k8_funct_2(X1,X2,X0,X3,X4)),k8_funct_2(X1,X2,X0,k1_partfun1(X1,X1,X1,X2,X5,X3),X4))
          & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
          & v1_funct_2(X5,X1,X1)
          & v1_funct_1(X5) )
     => ( ~ r2_funct_2(X1,X0,k1_partfun1(X1,X1,X1,X0,sK6,k8_funct_2(X1,X2,X0,X3,X4)),k8_funct_2(X1,X2,X0,k1_partfun1(X1,X1,X1,X2,sK6,X3),X4))
        & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
        & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
        & v1_funct_2(sK6,X1,X1)
        & v1_funct_1(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ~ r2_funct_2(X1,X0,k1_partfun1(X1,X1,X1,X0,X5,k8_funct_2(X1,X2,X0,X3,X4)),k8_funct_2(X1,X2,X0,k1_partfun1(X1,X1,X1,X2,X5,X3),X4))
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
                  & v1_funct_2(X5,X1,X1)
                  & v1_funct_1(X5) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ~ r2_funct_2(X1,X0,k1_partfun1(X1,X1,X1,X0,X5,k8_funct_2(X1,X2,X0,X3,X4)),k8_funct_2(X1,X2,X0,k1_partfun1(X1,X1,X1,X2,X5,X3),X4))
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
                  & v1_funct_2(X5,X1,X1)
                  & v1_funct_1(X5) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ~ v1_xboole_0(X2)
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X3,X1,X2)
              & v1_funct_1(X3) )
           => ! [X4] :
                ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                  & v1_funct_1(X4) )
               => ! [X5] :
                    ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
                      & v1_funct_2(X5,X1,X1)
                      & v1_funct_1(X5) )
                   => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                     => r2_funct_2(X1,X0,k1_partfun1(X1,X1,X1,X0,X5,k8_funct_2(X1,X2,X0,X3,X4)),k8_funct_2(X1,X2,X0,k1_partfun1(X1,X1,X1,X2,X5,X3),X4)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
         => ! [X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
             => ! [X5] :
                  ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
                    & v1_funct_2(X5,X1,X1)
                    & v1_funct_1(X5) )
                 => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                   => r2_funct_2(X1,X0,k1_partfun1(X1,X1,X1,X0,X5,k8_funct_2(X1,X2,X0,X3,X4)),k8_funct_2(X1,X2,X0,k1_partfun1(X1,X1,X1,X2,X5,X3),X4)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t187_funct_2.p',t187_funct_2)).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t187_funct_2.p',cc1_relset_1)).

fof(f15397,plain,
    ( ~ v1_relat_1(sK6)
    | ~ spl9_115
    | ~ spl9_131
    | ~ spl9_172
    | ~ spl9_180
    | ~ spl9_444 ),
    inference(subsumption_resolution,[],[f15396,f153])).

fof(f153,plain,(
    v1_relat_1(sK4) ),
    inference(resolution,[],[f116,f95])).

fof(f95,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f83])).

fof(f15396,plain,
    ( ~ v1_relat_1(sK4)
    | ~ v1_relat_1(sK6)
    | ~ spl9_115
    | ~ spl9_131
    | ~ spl9_172
    | ~ spl9_180
    | ~ spl9_444 ),
    inference(subsumption_resolution,[],[f15395,f154])).

fof(f154,plain,(
    v1_relat_1(sK5) ),
    inference(resolution,[],[f116,f97])).

fof(f97,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f83])).

fof(f15395,plain,
    ( ~ v1_relat_1(sK5)
    | ~ v1_relat_1(sK4)
    | ~ v1_relat_1(sK6)
    | ~ spl9_115
    | ~ spl9_131
    | ~ spl9_172
    | ~ spl9_180
    | ~ spl9_444 ),
    inference(subsumption_resolution,[],[f15394,f7219])).

fof(f7219,plain,
    ( r2_funct_2(sK2,sK1,k5_relat_1(sK6,k5_relat_1(sK4,sK5)),k5_relat_1(sK6,k5_relat_1(sK4,sK5)))
    | ~ spl9_172
    | ~ spl9_180
    | ~ spl9_444 ),
    inference(subsumption_resolution,[],[f7218,f2628])).

fof(f2628,plain,
    ( v1_funct_1(k5_relat_1(sK6,k5_relat_1(sK4,sK5)))
    | ~ spl9_172 ),
    inference(avatar_component_clause,[],[f2627])).

fof(f2627,plain,
    ( spl9_172
  <=> v1_funct_1(k5_relat_1(sK6,k5_relat_1(sK4,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_172])])).

fof(f7218,plain,
    ( r2_funct_2(sK2,sK1,k5_relat_1(sK6,k5_relat_1(sK4,sK5)),k5_relat_1(sK6,k5_relat_1(sK4,sK5)))
    | ~ v1_funct_1(k5_relat_1(sK6,k5_relat_1(sK4,sK5)))
    | ~ spl9_180
    | ~ spl9_444 ),
    inference(subsumption_resolution,[],[f7197,f2674])).

fof(f2674,plain,
    ( v1_funct_2(k5_relat_1(sK6,k5_relat_1(sK4,sK5)),sK2,sK1)
    | ~ spl9_180 ),
    inference(avatar_component_clause,[],[f2673])).

fof(f2673,plain,
    ( spl9_180
  <=> v1_funct_2(k5_relat_1(sK6,k5_relat_1(sK4,sK5)),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_180])])).

fof(f7197,plain,
    ( r2_funct_2(sK2,sK1,k5_relat_1(sK6,k5_relat_1(sK4,sK5)),k5_relat_1(sK6,k5_relat_1(sK4,sK5)))
    | ~ v1_funct_2(k5_relat_1(sK6,k5_relat_1(sK4,sK5)),sK2,sK1)
    | ~ v1_funct_1(k5_relat_1(sK6,k5_relat_1(sK4,sK5)))
    | ~ spl9_444 ),
    inference(resolution,[],[f7191,f141])).

fof(f141,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_funct_2(X0,X1,X3,X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(duplicate_literal_removal,[],[f140])).

fof(f140,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f129])).

fof(f129,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f87])).

fof(f87,plain,(
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
    inference(nnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f67])).

fof(f67,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t187_funct_2.p',redefinition_r2_funct_2)).

fof(f7191,plain,
    ( m1_subset_1(k5_relat_1(sK6,k5_relat_1(sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl9_444 ),
    inference(subsumption_resolution,[],[f7190,f155])).

fof(f7190,plain,
    ( m1_subset_1(k5_relat_1(sK6,k5_relat_1(sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_relat_1(sK6)
    | ~ spl9_444 ),
    inference(subsumption_resolution,[],[f7189,f153])).

fof(f7189,plain,
    ( m1_subset_1(k5_relat_1(sK6,k5_relat_1(sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_relat_1(sK4)
    | ~ v1_relat_1(sK6)
    | ~ spl9_444 ),
    inference(subsumption_resolution,[],[f7170,f154])).

fof(f7170,plain,
    ( m1_subset_1(k5_relat_1(sK6,k5_relat_1(sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_relat_1(sK5)
    | ~ v1_relat_1(sK4)
    | ~ v1_relat_1(sK6)
    | ~ spl9_444 ),
    inference(superposition,[],[f7108,f106])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t187_funct_2.p',t55_relat_1)).

fof(f7108,plain,
    ( m1_subset_1(k5_relat_1(k5_relat_1(sK6,sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl9_444 ),
    inference(avatar_component_clause,[],[f7107])).

fof(f7107,plain,
    ( spl9_444
  <=> m1_subset_1(k5_relat_1(k5_relat_1(sK6,sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_444])])).

fof(f15394,plain,
    ( ~ r2_funct_2(sK2,sK1,k5_relat_1(sK6,k5_relat_1(sK4,sK5)),k5_relat_1(sK6,k5_relat_1(sK4,sK5)))
    | ~ v1_relat_1(sK5)
    | ~ v1_relat_1(sK4)
    | ~ v1_relat_1(sK6)
    | ~ spl9_115
    | ~ spl9_131 ),
    inference(superposition,[],[f15278,f106])).

fof(f15278,plain,
    ( ~ r2_funct_2(sK2,sK1,k5_relat_1(sK6,k5_relat_1(sK4,sK5)),k5_relat_1(k5_relat_1(sK6,sK4),sK5))
    | ~ spl9_115
    | ~ spl9_131 ),
    inference(subsumption_resolution,[],[f15277,f94])).

fof(f94,plain,(
    v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f83])).

fof(f15277,plain,
    ( ~ r2_funct_2(sK2,sK1,k5_relat_1(sK6,k5_relat_1(sK4,sK5)),k5_relat_1(k5_relat_1(sK6,sK4),sK5))
    | ~ v1_funct_2(sK4,sK2,sK3)
    | ~ spl9_115
    | ~ spl9_131 ),
    inference(subsumption_resolution,[],[f15276,f101])).

fof(f101,plain,(
    r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5)) ),
    inference(cnf_transformation,[],[f83])).

fof(f15276,plain,
    ( ~ r2_funct_2(sK2,sK1,k5_relat_1(sK6,k5_relat_1(sK4,sK5)),k5_relat_1(k5_relat_1(sK6,sK4),sK5))
    | ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5))
    | ~ v1_funct_2(sK4,sK2,sK3)
    | ~ spl9_115
    | ~ spl9_131 ),
    inference(subsumption_resolution,[],[f15275,f2339])).

fof(f2339,plain,
    ( k1_xboole_0 != sK3
    | ~ spl9_115 ),
    inference(avatar_component_clause,[],[f2338])).

fof(f2338,plain,
    ( spl9_115
  <=> k1_xboole_0 != sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_115])])).

fof(f15275,plain,
    ( ~ r2_funct_2(sK2,sK1,k5_relat_1(sK6,k5_relat_1(sK4,sK5)),k5_relat_1(k5_relat_1(sK6,sK4),sK5))
    | k1_xboole_0 = sK3
    | ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5))
    | ~ v1_funct_2(sK4,sK2,sK3)
    | ~ spl9_131 ),
    inference(subsumption_resolution,[],[f15274,f93])).

fof(f93,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f83])).

fof(f15274,plain,
    ( ~ r2_funct_2(sK2,sK1,k5_relat_1(sK6,k5_relat_1(sK4,sK5)),k5_relat_1(k5_relat_1(sK6,sK4),sK5))
    | ~ v1_funct_1(sK4)
    | k1_xboole_0 = sK3
    | ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5))
    | ~ v1_funct_2(sK4,sK2,sK3)
    | ~ spl9_131 ),
    inference(subsumption_resolution,[],[f15273,f95])).

fof(f15273,plain,
    ( ~ r2_funct_2(sK2,sK1,k5_relat_1(sK6,k5_relat_1(sK4,sK5)),k5_relat_1(k5_relat_1(sK6,sK4),sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(sK4)
    | k1_xboole_0 = sK3
    | ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5))
    | ~ v1_funct_2(sK4,sK2,sK3)
    | ~ spl9_131 ),
    inference(subsumption_resolution,[],[f15272,f96])).

fof(f96,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f83])).

fof(f15272,plain,
    ( ~ r2_funct_2(sK2,sK1,k5_relat_1(sK6,k5_relat_1(sK4,sK5)),k5_relat_1(k5_relat_1(sK6,sK4),sK5))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(sK4)
    | k1_xboole_0 = sK3
    | ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5))
    | ~ v1_funct_2(sK4,sK2,sK3)
    | ~ spl9_131 ),
    inference(subsumption_resolution,[],[f15270,f97])).

fof(f15270,plain,
    ( ~ r2_funct_2(sK2,sK1,k5_relat_1(sK6,k5_relat_1(sK4,sK5)),k5_relat_1(k5_relat_1(sK6,sK4),sK5))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(sK4)
    | k1_xboole_0 = sK3
    | ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5))
    | ~ v1_funct_2(sK4,sK2,sK3)
    | ~ spl9_131 ),
    inference(superposition,[],[f7061,f607])).

fof(f607,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( k8_funct_2(X5,X6,X7,X8,X9) = k5_relat_1(X8,X9)
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | ~ v1_funct_1(X9)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | ~ v1_funct_1(X8)
      | k1_xboole_0 = X6
      | ~ r1_tarski(k2_relset_1(X5,X6,X8),k1_relset_1(X6,X7,X9))
      | ~ v1_funct_2(X8,X5,X6) ) ),
    inference(duplicate_literal_removal,[],[f604])).

fof(f604,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( k8_funct_2(X5,X6,X7,X8,X9) = k5_relat_1(X8,X9)
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | ~ v1_funct_1(X9)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | ~ v1_funct_1(X8)
      | k1_xboole_0 = X6
      | ~ r1_tarski(k2_relset_1(X5,X6,X8),k1_relset_1(X6,X7,X9))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | ~ v1_funct_1(X9)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | ~ v1_funct_2(X8,X5,X6)
      | ~ v1_funct_1(X8) ) ),
    inference(superposition,[],[f135,f130])).

fof(f130,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4)
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4)
          | k1_xboole_0 = X1
          | ~ r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f69])).

fof(f69,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4)
          | k1_xboole_0 = X1
          | ~ r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_1(X4) )
         => ( r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))
           => ( k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4)
              | k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t187_funct_2.p',d12_funct_2)).

fof(f135,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f73])).

fof(f73,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t187_funct_2.p',redefinition_k1_partfun1)).

fof(f7061,plain,
    ( ~ r2_funct_2(sK2,sK1,k5_relat_1(sK6,k8_funct_2(sK2,sK3,sK1,sK4,sK5)),k5_relat_1(k5_relat_1(sK6,sK4),sK5))
    | ~ spl9_131 ),
    inference(subsumption_resolution,[],[f7060,f98])).

fof(f98,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f83])).

fof(f7060,plain,
    ( ~ r2_funct_2(sK2,sK1,k5_relat_1(sK6,k8_funct_2(sK2,sK3,sK1,sK4,sK5)),k5_relat_1(k5_relat_1(sK6,sK4),sK5))
    | ~ v1_funct_1(sK6)
    | ~ spl9_131 ),
    inference(subsumption_resolution,[],[f7059,f100])).

fof(f7059,plain,
    ( ~ r2_funct_2(sK2,sK1,k5_relat_1(sK6,k8_funct_2(sK2,sK3,sK1,sK4,sK5)),k5_relat_1(k5_relat_1(sK6,sK4),sK5))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_1(sK6)
    | ~ spl9_131 ),
    inference(subsumption_resolution,[],[f7058,f93])).

fof(f7058,plain,
    ( ~ r2_funct_2(sK2,sK1,k5_relat_1(sK6,k8_funct_2(sK2,sK3,sK1,sK4,sK5)),k5_relat_1(k5_relat_1(sK6,sK4),sK5))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_1(sK6)
    | ~ spl9_131 ),
    inference(subsumption_resolution,[],[f7049,f95])).

fof(f7049,plain,
    ( ~ r2_funct_2(sK2,sK1,k5_relat_1(sK6,k8_funct_2(sK2,sK3,sK1,sK4,sK5)),k5_relat_1(k5_relat_1(sK6,sK4),sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_1(sK6)
    | ~ spl9_131 ),
    inference(superposition,[],[f2393,f135])).

fof(f2393,plain,
    ( ~ r2_funct_2(sK2,sK1,k5_relat_1(sK6,k8_funct_2(sK2,sK3,sK1,sK4,sK5)),k5_relat_1(k1_partfun1(sK2,sK2,sK2,sK3,sK6,sK4),sK5))
    | ~ spl9_131 ),
    inference(avatar_component_clause,[],[f2392])).

fof(f2392,plain,
    ( spl9_131
  <=> ~ r2_funct_2(sK2,sK1,k5_relat_1(sK6,k8_funct_2(sK2,sK3,sK1,sK4,sK5)),k5_relat_1(k1_partfun1(sK2,sK2,sK2,sK3,sK6,sK4),sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_131])])).

fof(f7146,plain,
    ( spl9_115
    | ~ spl9_134
    | ~ spl9_136
    | ~ spl9_354
    | spl9_445 ),
    inference(avatar_contradiction_clause,[],[f7145])).

fof(f7145,plain,
    ( $false
    | ~ spl9_115
    | ~ spl9_134
    | ~ spl9_136
    | ~ spl9_354
    | ~ spl9_445 ),
    inference(subsumption_resolution,[],[f7134,f5943])).

fof(f5943,plain,
    ( r1_tarski(k5_relat_1(k5_relat_1(sK6,sK4),sK5),k2_zfmisc_1(sK2,sK1))
    | ~ spl9_115
    | ~ spl9_134
    | ~ spl9_136
    | ~ spl9_354 ),
    inference(subsumption_resolution,[],[f5942,f597])).

fof(f597,plain,(
    v1_funct_2(k5_relat_1(sK6,sK4),sK2,sK3) ),
    inference(subsumption_resolution,[],[f596,f93])).

fof(f596,plain,
    ( v1_funct_2(k5_relat_1(sK6,sK4),sK2,sK3)
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f585,f94])).

fof(f585,plain,
    ( v1_funct_2(k5_relat_1(sK6,sK4),sK2,sK3)
    | ~ v1_funct_2(sK4,sK2,sK3)
    | ~ v1_funct_1(sK4) ),
    inference(resolution,[],[f514,f95])).

fof(f514,plain,(
    ! [X14,X13] :
      ( ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(sK2,X14)))
      | v1_funct_2(k5_relat_1(sK6,X13),sK2,X14)
      | ~ v1_funct_2(X13,sK2,X14)
      | ~ v1_funct_1(X13) ) ),
    inference(subsumption_resolution,[],[f513,f98])).

fof(f513,plain,(
    ! [X14,X13] :
      ( v1_funct_2(k5_relat_1(sK6,X13),sK2,X14)
      | ~ v1_funct_1(sK6)
      | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(sK2,X14)))
      | ~ v1_funct_2(X13,sK2,X14)
      | ~ v1_funct_1(X13) ) ),
    inference(subsumption_resolution,[],[f505,f99])).

fof(f99,plain,(
    v1_funct_2(sK6,sK2,sK2) ),
    inference(cnf_transformation,[],[f83])).

fof(f505,plain,(
    ! [X14,X13] :
      ( v1_funct_2(k5_relat_1(sK6,X13),sK2,X14)
      | ~ v1_funct_2(sK6,sK2,sK2)
      | ~ v1_funct_1(sK6)
      | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(sK2,X14)))
      | ~ v1_funct_2(X13,sK2,X14)
      | ~ v1_funct_1(X13) ) ),
    inference(resolution,[],[f126,f100])).

fof(f126,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | v1_funct_2(k5_relat_1(X3,X2),X0,X1)
      | ~ v1_funct_2(X3,X0,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2,X3] :
      ( ( v1_funct_2(k5_relat_1(X3,X2),X0,X1)
        & v1_funct_1(k5_relat_1(X3,X2)) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X3,X0,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2,X3] :
      ( ( v1_funct_2(k5_relat_1(X3,X2),X0,X1)
        & v1_funct_1(k5_relat_1(X3,X2)) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X3,X0,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X3,X0,X0)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( v1_funct_2(k5_relat_1(X3,X2),X0,X1)
        & v1_funct_1(k5_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t187_funct_2.p',fc4_funct_2)).

fof(f5942,plain,
    ( r1_tarski(k5_relat_1(k5_relat_1(sK6,sK4),sK5),k2_zfmisc_1(sK2,sK1))
    | ~ v1_funct_2(k5_relat_1(sK6,sK4),sK2,sK3)
    | ~ spl9_115
    | ~ spl9_134
    | ~ spl9_136
    | ~ spl9_354 ),
    inference(subsumption_resolution,[],[f5941,f2410])).

fof(f2410,plain,
    ( r1_tarski(k2_relset_1(sK2,sK3,k5_relat_1(sK6,sK4)),k1_relset_1(sK3,sK1,sK5))
    | ~ spl9_134 ),
    inference(avatar_component_clause,[],[f2409])).

fof(f2409,plain,
    ( spl9_134
  <=> r1_tarski(k2_relset_1(sK2,sK3,k5_relat_1(sK6,sK4)),k1_relset_1(sK3,sK1,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_134])])).

fof(f5941,plain,
    ( r1_tarski(k5_relat_1(k5_relat_1(sK6,sK4),sK5),k2_zfmisc_1(sK2,sK1))
    | ~ r1_tarski(k2_relset_1(sK2,sK3,k5_relat_1(sK6,sK4)),k1_relset_1(sK3,sK1,sK5))
    | ~ v1_funct_2(k5_relat_1(sK6,sK4),sK2,sK3)
    | ~ spl9_115
    | ~ spl9_136
    | ~ spl9_354 ),
    inference(subsumption_resolution,[],[f5940,f2339])).

fof(f5940,plain,
    ( r1_tarski(k5_relat_1(k5_relat_1(sK6,sK4),sK5),k2_zfmisc_1(sK2,sK1))
    | k1_xboole_0 = sK3
    | ~ r1_tarski(k2_relset_1(sK2,sK3,k5_relat_1(sK6,sK4)),k1_relset_1(sK3,sK1,sK5))
    | ~ v1_funct_2(k5_relat_1(sK6,sK4),sK2,sK3)
    | ~ spl9_136
    | ~ spl9_354 ),
    inference(subsumption_resolution,[],[f5939,f530])).

fof(f530,plain,(
    v1_funct_1(k5_relat_1(sK6,sK4)) ),
    inference(subsumption_resolution,[],[f529,f93])).

fof(f529,plain,
    ( v1_funct_1(k5_relat_1(sK6,sK4))
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f518,f94])).

fof(f518,plain,
    ( v1_funct_1(k5_relat_1(sK6,sK4))
    | ~ v1_funct_2(sK4,sK2,sK3)
    | ~ v1_funct_1(sK4) ),
    inference(resolution,[],[f465,f95])).

fof(f465,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(sK2,X7)))
      | v1_funct_1(k5_relat_1(sK6,X6))
      | ~ v1_funct_2(X6,sK2,X7)
      | ~ v1_funct_1(X6) ) ),
    inference(subsumption_resolution,[],[f464,f98])).

fof(f464,plain,(
    ! [X6,X7] :
      ( v1_funct_1(k5_relat_1(sK6,X6))
      | ~ v1_funct_1(sK6)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(sK2,X7)))
      | ~ v1_funct_2(X6,sK2,X7)
      | ~ v1_funct_1(X6) ) ),
    inference(subsumption_resolution,[],[f457,f99])).

fof(f457,plain,(
    ! [X6,X7] :
      ( v1_funct_1(k5_relat_1(sK6,X6))
      | ~ v1_funct_2(sK6,sK2,sK2)
      | ~ v1_funct_1(sK6)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(sK2,X7)))
      | ~ v1_funct_2(X6,sK2,X7)
      | ~ v1_funct_1(X6) ) ),
    inference(resolution,[],[f125,f100])).

fof(f125,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | v1_funct_1(k5_relat_1(X3,X2))
      | ~ v1_funct_2(X3,X0,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f5939,plain,
    ( r1_tarski(k5_relat_1(k5_relat_1(sK6,sK4),sK5),k2_zfmisc_1(sK2,sK1))
    | ~ v1_funct_1(k5_relat_1(sK6,sK4))
    | k1_xboole_0 = sK3
    | ~ r1_tarski(k2_relset_1(sK2,sK3,k5_relat_1(sK6,sK4)),k1_relset_1(sK3,sK1,sK5))
    | ~ v1_funct_2(k5_relat_1(sK6,sK4),sK2,sK3)
    | ~ spl9_136
    | ~ spl9_354 ),
    inference(subsumption_resolution,[],[f5938,f2416])).

fof(f2416,plain,
    ( m1_subset_1(k5_relat_1(sK6,sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ spl9_136 ),
    inference(avatar_component_clause,[],[f2415])).

fof(f2415,plain,
    ( spl9_136
  <=> m1_subset_1(k5_relat_1(sK6,sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_136])])).

fof(f5938,plain,
    ( r1_tarski(k5_relat_1(k5_relat_1(sK6,sK4),sK5),k2_zfmisc_1(sK2,sK1))
    | ~ m1_subset_1(k5_relat_1(sK6,sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(k5_relat_1(sK6,sK4))
    | k1_xboole_0 = sK3
    | ~ r1_tarski(k2_relset_1(sK2,sK3,k5_relat_1(sK6,sK4)),k1_relset_1(sK3,sK1,sK5))
    | ~ v1_funct_2(k5_relat_1(sK6,sK4),sK2,sK3)
    | ~ spl9_354 ),
    inference(subsumption_resolution,[],[f5937,f96])).

fof(f5937,plain,
    ( r1_tarski(k5_relat_1(k5_relat_1(sK6,sK4),sK5),k2_zfmisc_1(sK2,sK1))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(k5_relat_1(sK6,sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(k5_relat_1(sK6,sK4))
    | k1_xboole_0 = sK3
    | ~ r1_tarski(k2_relset_1(sK2,sK3,k5_relat_1(sK6,sK4)),k1_relset_1(sK3,sK1,sK5))
    | ~ v1_funct_2(k5_relat_1(sK6,sK4),sK2,sK3)
    | ~ spl9_354 ),
    inference(subsumption_resolution,[],[f5931,f97])).

fof(f5931,plain,
    ( r1_tarski(k5_relat_1(k5_relat_1(sK6,sK4),sK5),k2_zfmisc_1(sK2,sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(k5_relat_1(sK6,sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(k5_relat_1(sK6,sK4))
    | k1_xboole_0 = sK3
    | ~ r1_tarski(k2_relset_1(sK2,sK3,k5_relat_1(sK6,sK4)),k1_relset_1(sK3,sK1,sK5))
    | ~ v1_funct_2(k5_relat_1(sK6,sK4),sK2,sK3)
    | ~ spl9_354 ),
    inference(superposition,[],[f5828,f607])).

fof(f5828,plain,
    ( r1_tarski(k8_funct_2(sK2,sK3,sK1,k5_relat_1(sK6,sK4),sK5),k2_zfmisc_1(sK2,sK1))
    | ~ spl9_354 ),
    inference(resolution,[],[f5199,f112])).

fof(f112,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t187_funct_2.p',t3_subset)).

fof(f5199,plain,
    ( m1_subset_1(k8_funct_2(sK2,sK3,sK1,k5_relat_1(sK6,sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl9_354 ),
    inference(avatar_component_clause,[],[f5198])).

fof(f5198,plain,
    ( spl9_354
  <=> m1_subset_1(k8_funct_2(sK2,sK3,sK1,k5_relat_1(sK6,sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_354])])).

fof(f7134,plain,
    ( ~ r1_tarski(k5_relat_1(k5_relat_1(sK6,sK4),sK5),k2_zfmisc_1(sK2,sK1))
    | ~ spl9_445 ),
    inference(resolution,[],[f7111,f113])).

fof(f113,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f7111,plain,
    ( ~ m1_subset_1(k5_relat_1(k5_relat_1(sK6,sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl9_445 ),
    inference(avatar_component_clause,[],[f7110])).

fof(f7110,plain,
    ( spl9_445
  <=> ~ m1_subset_1(k5_relat_1(k5_relat_1(sK6,sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_445])])).

fof(f5795,plain,
    ( spl9_115
    | ~ spl9_134
    | ~ spl9_136
    | spl9_355 ),
    inference(avatar_contradiction_clause,[],[f5794])).

fof(f5794,plain,
    ( $false
    | ~ spl9_115
    | ~ spl9_134
    | ~ spl9_136
    | ~ spl9_355 ),
    inference(subsumption_resolution,[],[f5793,f597])).

fof(f5793,plain,
    ( ~ v1_funct_2(k5_relat_1(sK6,sK4),sK2,sK3)
    | ~ spl9_115
    | ~ spl9_134
    | ~ spl9_136
    | ~ spl9_355 ),
    inference(subsumption_resolution,[],[f5792,f2410])).

fof(f5792,plain,
    ( ~ r1_tarski(k2_relset_1(sK2,sK3,k5_relat_1(sK6,sK4)),k1_relset_1(sK3,sK1,sK5))
    | ~ v1_funct_2(k5_relat_1(sK6,sK4),sK2,sK3)
    | ~ spl9_115
    | ~ spl9_136
    | ~ spl9_355 ),
    inference(subsumption_resolution,[],[f5791,f2339])).

fof(f5791,plain,
    ( k1_xboole_0 = sK3
    | ~ r1_tarski(k2_relset_1(sK2,sK3,k5_relat_1(sK6,sK4)),k1_relset_1(sK3,sK1,sK5))
    | ~ v1_funct_2(k5_relat_1(sK6,sK4),sK2,sK3)
    | ~ spl9_136
    | ~ spl9_355 ),
    inference(subsumption_resolution,[],[f5790,f530])).

fof(f5790,plain,
    ( ~ v1_funct_1(k5_relat_1(sK6,sK4))
    | k1_xboole_0 = sK3
    | ~ r1_tarski(k2_relset_1(sK2,sK3,k5_relat_1(sK6,sK4)),k1_relset_1(sK3,sK1,sK5))
    | ~ v1_funct_2(k5_relat_1(sK6,sK4),sK2,sK3)
    | ~ spl9_136
    | ~ spl9_355 ),
    inference(subsumption_resolution,[],[f5789,f2416])).

fof(f5789,plain,
    ( ~ m1_subset_1(k5_relat_1(sK6,sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(k5_relat_1(sK6,sK4))
    | k1_xboole_0 = sK3
    | ~ r1_tarski(k2_relset_1(sK2,sK3,k5_relat_1(sK6,sK4)),k1_relset_1(sK3,sK1,sK5))
    | ~ v1_funct_2(k5_relat_1(sK6,sK4),sK2,sK3)
    | ~ spl9_355 ),
    inference(subsumption_resolution,[],[f5788,f96])).

fof(f5788,plain,
    ( ~ v1_funct_1(sK5)
    | ~ m1_subset_1(k5_relat_1(sK6,sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(k5_relat_1(sK6,sK4))
    | k1_xboole_0 = sK3
    | ~ r1_tarski(k2_relset_1(sK2,sK3,k5_relat_1(sK6,sK4)),k1_relset_1(sK3,sK1,sK5))
    | ~ v1_funct_2(k5_relat_1(sK6,sK4),sK2,sK3)
    | ~ spl9_355 ),
    inference(subsumption_resolution,[],[f5784,f97])).

fof(f5784,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(k5_relat_1(sK6,sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(k5_relat_1(sK6,sK4))
    | k1_xboole_0 = sK3
    | ~ r1_tarski(k2_relset_1(sK2,sK3,k5_relat_1(sK6,sK4)),k1_relset_1(sK3,sK1,sK5))
    | ~ v1_funct_2(k5_relat_1(sK6,sK4),sK2,sK3)
    | ~ spl9_355 ),
    inference(resolution,[],[f5202,f608])).

fof(f608,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))
      | ~ v1_funct_2(X3,X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f603])).

fof(f603,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(superposition,[],[f137,f130])).

fof(f137,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f75])).

fof(f75,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t187_funct_2.p',dt_k1_partfun1)).

fof(f5202,plain,
    ( ~ m1_subset_1(k8_funct_2(sK2,sK3,sK1,k5_relat_1(sK6,sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl9_355 ),
    inference(avatar_component_clause,[],[f5201])).

fof(f5201,plain,
    ( spl9_355
  <=> ~ m1_subset_1(k8_funct_2(sK2,sK3,sK1,k5_relat_1(sK6,sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_355])])).

fof(f5527,plain,(
    spl9_129 ),
    inference(avatar_contradiction_clause,[],[f5526])).

fof(f5526,plain,
    ( $false
    | ~ spl9_129 ),
    inference(subsumption_resolution,[],[f5525,f98])).

fof(f5525,plain,
    ( ~ v1_funct_1(sK6)
    | ~ spl9_129 ),
    inference(subsumption_resolution,[],[f5524,f100])).

fof(f5524,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_1(sK6)
    | ~ spl9_129 ),
    inference(subsumption_resolution,[],[f5523,f93])).

fof(f5523,plain,
    ( ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_1(sK6)
    | ~ spl9_129 ),
    inference(subsumption_resolution,[],[f5519,f95])).

fof(f5519,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_1(sK6)
    | ~ spl9_129 ),
    inference(resolution,[],[f2387,f137])).

fof(f2387,plain,
    ( ~ m1_subset_1(k1_partfun1(sK2,sK2,sK2,sK3,sK6,sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ spl9_129 ),
    inference(avatar_component_clause,[],[f2386])).

fof(f2386,plain,
    ( spl9_129
  <=> ~ m1_subset_1(k1_partfun1(sK2,sK2,sK2,sK3,sK6,sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_129])])).

fof(f5508,plain,
    ( spl9_125
    | ~ spl9_134 ),
    inference(avatar_contradiction_clause,[],[f5507])).

fof(f5507,plain,
    ( $false
    | ~ spl9_125
    | ~ spl9_134 ),
    inference(subsumption_resolution,[],[f5506,f98])).

fof(f5506,plain,
    ( ~ v1_funct_1(sK6)
    | ~ spl9_125
    | ~ spl9_134 ),
    inference(subsumption_resolution,[],[f5505,f100])).

fof(f5505,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_1(sK6)
    | ~ spl9_125
    | ~ spl9_134 ),
    inference(subsumption_resolution,[],[f5504,f93])).

fof(f5504,plain,
    ( ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_1(sK6)
    | ~ spl9_125
    | ~ spl9_134 ),
    inference(subsumption_resolution,[],[f5503,f95])).

fof(f5503,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_1(sK6)
    | ~ spl9_125
    | ~ spl9_134 ),
    inference(subsumption_resolution,[],[f5499,f2410])).

fof(f5499,plain,
    ( ~ r1_tarski(k2_relset_1(sK2,sK3,k5_relat_1(sK6,sK4)),k1_relset_1(sK3,sK1,sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_1(sK6)
    | ~ spl9_125 ),
    inference(superposition,[],[f2375,f135])).

fof(f2375,plain,
    ( ~ r1_tarski(k2_relset_1(sK2,sK3,k1_partfun1(sK2,sK2,sK2,sK3,sK6,sK4)),k1_relset_1(sK3,sK1,sK5))
    | ~ spl9_125 ),
    inference(avatar_component_clause,[],[f2374])).

fof(f2374,plain,
    ( spl9_125
  <=> ~ r1_tarski(k2_relset_1(sK2,sK3,k1_partfun1(sK2,sK2,sK2,sK3,sK6,sK4)),k1_relset_1(sK3,sK1,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_125])])).

fof(f4547,plain,
    ( ~ spl9_125
    | ~ spl9_129
    | ~ spl9_131
    | spl9_21
    | spl9_115
    | ~ spl9_122
    | ~ spl9_126 ),
    inference(avatar_split_clause,[],[f4546,f2377,f2365,f2338,f403,f2392,f2386,f2374])).

fof(f403,plain,
    ( spl9_21
  <=> ~ r2_funct_2(sK2,sK1,k5_relat_1(sK6,k8_funct_2(sK2,sK3,sK1,sK4,sK5)),k8_funct_2(sK2,sK3,sK1,k1_partfun1(sK2,sK2,sK2,sK3,sK6,sK4),sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).

fof(f2365,plain,
    ( spl9_122
  <=> v1_funct_2(k1_partfun1(sK2,sK2,sK2,sK3,sK6,sK4),sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_122])])).

fof(f2377,plain,
    ( spl9_126
  <=> v1_funct_1(k1_partfun1(sK2,sK2,sK2,sK3,sK6,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_126])])).

fof(f4546,plain,
    ( ~ r2_funct_2(sK2,sK1,k5_relat_1(sK6,k8_funct_2(sK2,sK3,sK1,sK4,sK5)),k5_relat_1(k1_partfun1(sK2,sK2,sK2,sK3,sK6,sK4),sK5))
    | ~ m1_subset_1(k1_partfun1(sK2,sK2,sK2,sK3,sK6,sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ r1_tarski(k2_relset_1(sK2,sK3,k1_partfun1(sK2,sK2,sK2,sK3,sK6,sK4)),k1_relset_1(sK3,sK1,sK5))
    | ~ spl9_21
    | ~ spl9_115
    | ~ spl9_122
    | ~ spl9_126 ),
    inference(subsumption_resolution,[],[f4545,f2366])).

fof(f2366,plain,
    ( v1_funct_2(k1_partfun1(sK2,sK2,sK2,sK3,sK6,sK4),sK2,sK3)
    | ~ spl9_122 ),
    inference(avatar_component_clause,[],[f2365])).

fof(f4545,plain,
    ( ~ r2_funct_2(sK2,sK1,k5_relat_1(sK6,k8_funct_2(sK2,sK3,sK1,sK4,sK5)),k5_relat_1(k1_partfun1(sK2,sK2,sK2,sK3,sK6,sK4),sK5))
    | ~ m1_subset_1(k1_partfun1(sK2,sK2,sK2,sK3,sK6,sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ r1_tarski(k2_relset_1(sK2,sK3,k1_partfun1(sK2,sK2,sK2,sK3,sK6,sK4)),k1_relset_1(sK3,sK1,sK5))
    | ~ v1_funct_2(k1_partfun1(sK2,sK2,sK2,sK3,sK6,sK4),sK2,sK3)
    | ~ spl9_21
    | ~ spl9_115
    | ~ spl9_126 ),
    inference(subsumption_resolution,[],[f4544,f2339])).

fof(f4544,plain,
    ( ~ r2_funct_2(sK2,sK1,k5_relat_1(sK6,k8_funct_2(sK2,sK3,sK1,sK4,sK5)),k5_relat_1(k1_partfun1(sK2,sK2,sK2,sK3,sK6,sK4),sK5))
    | ~ m1_subset_1(k1_partfun1(sK2,sK2,sK2,sK3,sK6,sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | k1_xboole_0 = sK3
    | ~ r1_tarski(k2_relset_1(sK2,sK3,k1_partfun1(sK2,sK2,sK2,sK3,sK6,sK4)),k1_relset_1(sK3,sK1,sK5))
    | ~ v1_funct_2(k1_partfun1(sK2,sK2,sK2,sK3,sK6,sK4),sK2,sK3)
    | ~ spl9_21
    | ~ spl9_126 ),
    inference(subsumption_resolution,[],[f4543,f2378])).

fof(f2378,plain,
    ( v1_funct_1(k1_partfun1(sK2,sK2,sK2,sK3,sK6,sK4))
    | ~ spl9_126 ),
    inference(avatar_component_clause,[],[f2377])).

fof(f4543,plain,
    ( ~ r2_funct_2(sK2,sK1,k5_relat_1(sK6,k8_funct_2(sK2,sK3,sK1,sK4,sK5)),k5_relat_1(k1_partfun1(sK2,sK2,sK2,sK3,sK6,sK4),sK5))
    | ~ m1_subset_1(k1_partfun1(sK2,sK2,sK2,sK3,sK6,sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(k1_partfun1(sK2,sK2,sK2,sK3,sK6,sK4))
    | k1_xboole_0 = sK3
    | ~ r1_tarski(k2_relset_1(sK2,sK3,k1_partfun1(sK2,sK2,sK2,sK3,sK6,sK4)),k1_relset_1(sK3,sK1,sK5))
    | ~ v1_funct_2(k1_partfun1(sK2,sK2,sK2,sK3,sK6,sK4),sK2,sK3)
    | ~ spl9_21 ),
    inference(subsumption_resolution,[],[f4542,f96])).

fof(f4542,plain,
    ( ~ r2_funct_2(sK2,sK1,k5_relat_1(sK6,k8_funct_2(sK2,sK3,sK1,sK4,sK5)),k5_relat_1(k1_partfun1(sK2,sK2,sK2,sK3,sK6,sK4),sK5))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(k1_partfun1(sK2,sK2,sK2,sK3,sK6,sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(k1_partfun1(sK2,sK2,sK2,sK3,sK6,sK4))
    | k1_xboole_0 = sK3
    | ~ r1_tarski(k2_relset_1(sK2,sK3,k1_partfun1(sK2,sK2,sK2,sK3,sK6,sK4)),k1_relset_1(sK3,sK1,sK5))
    | ~ v1_funct_2(k1_partfun1(sK2,sK2,sK2,sK3,sK6,sK4),sK2,sK3)
    | ~ spl9_21 ),
    inference(subsumption_resolution,[],[f4529,f97])).

fof(f4529,plain,
    ( ~ r2_funct_2(sK2,sK1,k5_relat_1(sK6,k8_funct_2(sK2,sK3,sK1,sK4,sK5)),k5_relat_1(k1_partfun1(sK2,sK2,sK2,sK3,sK6,sK4),sK5))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(k1_partfun1(sK2,sK2,sK2,sK3,sK6,sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(k1_partfun1(sK2,sK2,sK2,sK3,sK6,sK4))
    | k1_xboole_0 = sK3
    | ~ r1_tarski(k2_relset_1(sK2,sK3,k1_partfun1(sK2,sK2,sK2,sK3,sK6,sK4)),k1_relset_1(sK3,sK1,sK5))
    | ~ v1_funct_2(k1_partfun1(sK2,sK2,sK2,sK3,sK6,sK4),sK2,sK3)
    | ~ spl9_21 ),
    inference(superposition,[],[f404,f607])).

fof(f404,plain,
    ( ~ r2_funct_2(sK2,sK1,k5_relat_1(sK6,k8_funct_2(sK2,sK3,sK1,sK4,sK5)),k8_funct_2(sK2,sK3,sK1,k1_partfun1(sK2,sK2,sK2,sK3,sK6,sK4),sK5))
    | ~ spl9_21 ),
    inference(avatar_component_clause,[],[f403])).

fof(f4411,plain,(
    spl9_291 ),
    inference(avatar_contradiction_clause,[],[f4410])).

fof(f4410,plain,
    ( $false
    | ~ spl9_291 ),
    inference(subsumption_resolution,[],[f4409,f155])).

fof(f4409,plain,
    ( ~ v1_relat_1(sK6)
    | ~ spl9_291 ),
    inference(subsumption_resolution,[],[f4408,f153])).

fof(f4408,plain,
    ( ~ v1_relat_1(sK4)
    | ~ v1_relat_1(sK6)
    | ~ spl9_291 ),
    inference(subsumption_resolution,[],[f4405,f231])).

fof(f231,plain,(
    r1_tarski(k2_relat_1(sK4),k1_relat_1(sK5)) ),
    inference(subsumption_resolution,[],[f229,f97])).

fof(f229,plain,
    ( r1_tarski(k2_relat_1(sK4),k1_relat_1(sK5))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(superposition,[],[f220,f118])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t187_funct_2.p',redefinition_k1_relset_1)).

fof(f220,plain,(
    r1_tarski(k2_relat_1(sK4),k1_relset_1(sK3,sK1,sK5)) ),
    inference(subsumption_resolution,[],[f219,f95])).

fof(f219,plain,
    ( r1_tarski(k2_relat_1(sK4),k1_relset_1(sK3,sK1,sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(superposition,[],[f101,f117])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t187_funct_2.p',redefinition_k2_relset_1)).

fof(f4405,plain,
    ( ~ r1_tarski(k2_relat_1(sK4),k1_relat_1(sK5))
    | ~ v1_relat_1(sK4)
    | ~ v1_relat_1(sK6)
    | ~ spl9_291 ),
    inference(resolution,[],[f4371,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t187_funct_2.p',t45_relat_1)).

fof(f4371,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(k5_relat_1(sK6,sK4)),X0)
        | ~ r1_tarski(X0,k1_relat_1(sK5)) )
    | ~ spl9_291 ),
    inference(resolution,[],[f4370,f122])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t187_funct_2.p',t1_xboole_1)).

fof(f4370,plain,
    ( ~ r1_tarski(k2_relat_1(k5_relat_1(sK6,sK4)),k1_relat_1(sK5))
    | ~ spl9_291 ),
    inference(subsumption_resolution,[],[f4369,f97])).

fof(f4369,plain,
    ( ~ r1_tarski(k2_relat_1(k5_relat_1(sK6,sK4)),k1_relat_1(sK5))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ spl9_291 ),
    inference(superposition,[],[f4152,f118])).

fof(f4152,plain,
    ( ~ r1_tarski(k2_relat_1(k5_relat_1(sK6,sK4)),k1_relset_1(sK3,sK1,sK5))
    | ~ spl9_291 ),
    inference(avatar_component_clause,[],[f4151])).

fof(f4151,plain,
    ( spl9_291
  <=> ~ r1_tarski(k2_relat_1(k5_relat_1(sK6,sK4)),k1_relset_1(sK3,sK1,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_291])])).

fof(f4201,plain,(
    ~ spl9_294 ),
    inference(avatar_contradiction_clause,[],[f4199])).

fof(f4199,plain,
    ( $false
    | ~ spl9_294 ),
    inference(subsumption_resolution,[],[f95,f4164])).

fof(f4164,plain,
    ( ! [X0] : ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK3)))
    | ~ spl9_294 ),
    inference(avatar_component_clause,[],[f4163])).

fof(f4163,plain,
    ( spl9_294
  <=> ! [X0] : ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_294])])).

fof(f4168,plain,(
    ~ spl9_292 ),
    inference(avatar_contradiction_clause,[],[f4166])).

fof(f4166,plain,
    ( $false
    | ~ spl9_292 ),
    inference(subsumption_resolution,[],[f100,f4161])).

fof(f4161,plain,
    ( ! [X1] : ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
    | ~ spl9_292 ),
    inference(avatar_component_clause,[],[f4160])).

fof(f4160,plain,
    ( spl9_292
  <=> ! [X1] : ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_292])])).

fof(f4165,plain,
    ( spl9_292
    | spl9_294
    | spl9_137 ),
    inference(avatar_split_clause,[],[f4158,f2418,f4163,f4160])).

fof(f2418,plain,
    ( spl9_137
  <=> ~ m1_subset_1(k5_relat_1(sK6,sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_137])])).

fof(f4158,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK3)))
        | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) )
    | ~ spl9_137 ),
    inference(subsumption_resolution,[],[f4157,f98])).

fof(f4157,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK3)))
        | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
        | ~ v1_funct_1(sK6) )
    | ~ spl9_137 ),
    inference(subsumption_resolution,[],[f4155,f93])).

fof(f4155,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK3)))
        | ~ v1_funct_1(sK4)
        | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
        | ~ v1_funct_1(sK6) )
    | ~ spl9_137 ),
    inference(resolution,[],[f2419,f483])).

fof(f483,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(duplicate_literal_removal,[],[f482])).

fof(f482,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(superposition,[],[f137,f135])).

fof(f2419,plain,
    ( ~ m1_subset_1(k5_relat_1(sK6,sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ spl9_137 ),
    inference(avatar_component_clause,[],[f2418])).

fof(f4153,plain,
    ( ~ spl9_137
    | ~ spl9_291
    | spl9_135 ),
    inference(avatar_split_clause,[],[f4145,f2412,f4151,f2418])).

fof(f2412,plain,
    ( spl9_135
  <=> ~ r1_tarski(k2_relset_1(sK2,sK3,k5_relat_1(sK6,sK4)),k1_relset_1(sK3,sK1,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_135])])).

fof(f4145,plain,
    ( ~ r1_tarski(k2_relat_1(k5_relat_1(sK6,sK4)),k1_relset_1(sK3,sK1,sK5))
    | ~ m1_subset_1(k5_relat_1(sK6,sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ spl9_135 ),
    inference(superposition,[],[f2413,f117])).

fof(f2413,plain,
    ( ~ r1_tarski(k2_relset_1(sK2,sK3,k5_relat_1(sK6,sK4)),k1_relset_1(sK3,sK1,sK5))
    | ~ spl9_135 ),
    inference(avatar_component_clause,[],[f2412])).

fof(f4092,plain,(
    spl9_123 ),
    inference(avatar_contradiction_clause,[],[f4091])).

fof(f4091,plain,
    ( $false
    | ~ spl9_123 ),
    inference(subsumption_resolution,[],[f4090,f98])).

fof(f4090,plain,
    ( ~ v1_funct_1(sK6)
    | ~ spl9_123 ),
    inference(subsumption_resolution,[],[f4089,f100])).

fof(f4089,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_1(sK6)
    | ~ spl9_123 ),
    inference(subsumption_resolution,[],[f4088,f93])).

fof(f4088,plain,
    ( ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_1(sK6)
    | ~ spl9_123 ),
    inference(subsumption_resolution,[],[f4087,f95])).

fof(f4087,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_1(sK6)
    | ~ spl9_123 ),
    inference(subsumption_resolution,[],[f4085,f597])).

fof(f4085,plain,
    ( ~ v1_funct_2(k5_relat_1(sK6,sK4),sK2,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_1(sK6)
    | ~ spl9_123 ),
    inference(superposition,[],[f2369,f135])).

fof(f2369,plain,
    ( ~ v1_funct_2(k1_partfun1(sK2,sK2,sK2,sK3,sK6,sK4),sK2,sK3)
    | ~ spl9_123 ),
    inference(avatar_component_clause,[],[f2368])).

fof(f2368,plain,
    ( spl9_123
  <=> ~ v1_funct_2(k1_partfun1(sK2,sK2,sK2,sK3,sK6,sK4),sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_123])])).

fof(f3849,plain,
    ( ~ spl9_17
    | ~ spl9_19
    | ~ spl9_21 ),
    inference(avatar_split_clause,[],[f3848,f403,f397,f391])).

fof(f391,plain,
    ( spl9_17
  <=> ~ v1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).

fof(f397,plain,
    ( spl9_19
  <=> ~ m1_subset_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).

fof(f3848,plain,
    ( ~ r2_funct_2(sK2,sK1,k5_relat_1(sK6,k8_funct_2(sK2,sK3,sK1,sK4,sK5)),k8_funct_2(sK2,sK3,sK1,k1_partfun1(sK2,sK2,sK2,sK3,sK6,sK4),sK5))
    | ~ m1_subset_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5)) ),
    inference(subsumption_resolution,[],[f3847,f98])).

fof(f3847,plain,
    ( ~ r2_funct_2(sK2,sK1,k5_relat_1(sK6,k8_funct_2(sK2,sK3,sK1,sK4,sK5)),k8_funct_2(sK2,sK3,sK1,k1_partfun1(sK2,sK2,sK2,sK3,sK6,sK4),sK5))
    | ~ m1_subset_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5))
    | ~ v1_funct_1(sK6) ),
    inference(subsumption_resolution,[],[f3834,f100])).

fof(f3834,plain,
    ( ~ r2_funct_2(sK2,sK1,k5_relat_1(sK6,k8_funct_2(sK2,sK3,sK1,sK4,sK5)),k8_funct_2(sK2,sK3,sK1,k1_partfun1(sK2,sK2,sK2,sK3,sK6,sK4),sK5))
    | ~ m1_subset_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_1(sK6) ),
    inference(superposition,[],[f102,f135])).

fof(f102,plain,(
    ~ r2_funct_2(sK2,sK1,k1_partfun1(sK2,sK2,sK2,sK1,sK6,k8_funct_2(sK2,sK3,sK1,sK4,sK5)),k8_funct_2(sK2,sK3,sK1,k1_partfun1(sK2,sK2,sK2,sK3,sK6,sK4),sK5)) ),
    inference(cnf_transformation,[],[f83])).

fof(f3794,plain,
    ( spl9_16
    | spl9_115 ),
    inference(avatar_split_clause,[],[f3793,f2338,f388])).

fof(f388,plain,
    ( spl9_16
  <=> v1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f3793,plain,
    ( v1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5))
    | ~ spl9_115 ),
    inference(subsumption_resolution,[],[f3792,f94])).

fof(f3792,plain,
    ( v1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5))
    | ~ v1_funct_2(sK4,sK2,sK3)
    | ~ spl9_115 ),
    inference(subsumption_resolution,[],[f3791,f2339])).

fof(f3791,plain,
    ( k1_xboole_0 = sK3
    | v1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5))
    | ~ v1_funct_2(sK4,sK2,sK3) ),
    inference(subsumption_resolution,[],[f3790,f93])).

fof(f3790,plain,
    ( ~ v1_funct_1(sK4)
    | k1_xboole_0 = sK3
    | v1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5))
    | ~ v1_funct_2(sK4,sK2,sK3) ),
    inference(subsumption_resolution,[],[f3789,f95])).

fof(f3789,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(sK4)
    | k1_xboole_0 = sK3
    | v1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5))
    | ~ v1_funct_2(sK4,sK2,sK3) ),
    inference(subsumption_resolution,[],[f3788,f96])).

fof(f3788,plain,
    ( ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(sK4)
    | k1_xboole_0 = sK3
    | v1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5))
    | ~ v1_funct_2(sK4,sK2,sK3) ),
    inference(subsumption_resolution,[],[f3785,f97])).

fof(f3785,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(sK4)
    | k1_xboole_0 = sK3
    | v1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5))
    | ~ v1_funct_2(sK4,sK2,sK3) ),
    inference(resolution,[],[f101,f606])).

fof(f606,plain,(
    ! [X14,X12,X10,X13,X11] :
      ( ~ r1_tarski(k2_relset_1(X10,X11,X13),k1_relset_1(X11,X12,X14))
      | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))
      | ~ v1_funct_1(X14)
      | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
      | ~ v1_funct_1(X13)
      | k1_xboole_0 = X11
      | v1_funct_1(k8_funct_2(X10,X11,X12,X13,X14))
      | ~ v1_funct_2(X13,X10,X11) ) ),
    inference(duplicate_literal_removal,[],[f605])).

fof(f605,plain,(
    ! [X14,X12,X10,X13,X11] :
      ( v1_funct_1(k8_funct_2(X10,X11,X12,X13,X14))
      | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))
      | ~ v1_funct_1(X14)
      | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
      | ~ v1_funct_1(X13)
      | k1_xboole_0 = X11
      | ~ r1_tarski(k2_relset_1(X10,X11,X13),k1_relset_1(X11,X12,X14))
      | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))
      | ~ v1_funct_1(X14)
      | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
      | ~ v1_funct_2(X13,X10,X11)
      | ~ v1_funct_1(X13) ) ),
    inference(superposition,[],[f136,f130])).

fof(f136,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f3511,plain,(
    spl9_127 ),
    inference(avatar_contradiction_clause,[],[f3510])).

fof(f3510,plain,
    ( $false
    | ~ spl9_127 ),
    inference(subsumption_resolution,[],[f3509,f98])).

fof(f3509,plain,
    ( ~ v1_funct_1(sK6)
    | ~ spl9_127 ),
    inference(subsumption_resolution,[],[f3508,f100])).

fof(f3508,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_1(sK6)
    | ~ spl9_127 ),
    inference(subsumption_resolution,[],[f3507,f93])).

fof(f3507,plain,
    ( ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_1(sK6)
    | ~ spl9_127 ),
    inference(subsumption_resolution,[],[f3506,f95])).

fof(f3506,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_1(sK6)
    | ~ spl9_127 ),
    inference(subsumption_resolution,[],[f3499,f530])).

fof(f3499,plain,
    ( ~ v1_funct_1(k5_relat_1(sK6,sK4))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_1(sK6)
    | ~ spl9_127 ),
    inference(superposition,[],[f2381,f135])).

fof(f2381,plain,
    ( ~ v1_funct_1(k1_partfun1(sK2,sK2,sK2,sK3,sK6,sK4))
    | ~ spl9_127 ),
    inference(avatar_component_clause,[],[f2380])).

fof(f2380,plain,
    ( spl9_127
  <=> ~ v1_funct_1(k1_partfun1(sK2,sK2,sK2,sK3,sK6,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_127])])).

fof(f3172,plain,(
    ~ spl9_114 ),
    inference(avatar_contradiction_clause,[],[f3165])).

fof(f3165,plain,
    ( $false
    | ~ spl9_114 ),
    inference(subsumption_resolution,[],[f103,f3162])).

fof(f3162,plain,
    ( ! [X0] : ~ v1_xboole_0(X0)
    | ~ spl9_114 ),
    inference(duplicate_literal_removal,[],[f3161])).

fof(f3161,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | ~ v1_xboole_0(X0) )
    | ~ spl9_114 ),
    inference(superposition,[],[f3062,f104])).

fof(f104,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t187_funct_2.p',t6_boole)).

fof(f3062,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl9_114 ),
    inference(backward_demodulation,[],[f2342,f92])).

fof(f92,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f83])).

fof(f2342,plain,
    ( k1_xboole_0 = sK3
    | ~ spl9_114 ),
    inference(avatar_component_clause,[],[f2341])).

fof(f2341,plain,
    ( spl9_114
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_114])])).

fof(f103,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t187_funct_2.p',dt_o_0_0_xboole_0)).

fof(f2675,plain,
    ( spl9_114
    | spl9_180
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_22 ),
    inference(avatar_split_clause,[],[f2668,f434,f394,f388,f2673,f2341])).

fof(f394,plain,
    ( spl9_18
  <=> m1_subset_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).

fof(f434,plain,
    ( spl9_22
  <=> v1_funct_2(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).

fof(f2668,plain,
    ( v1_funct_2(k5_relat_1(sK6,k5_relat_1(sK4,sK5)),sK2,sK1)
    | k1_xboole_0 = sK3
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f2667,f94])).

fof(f2667,plain,
    ( v1_funct_2(k5_relat_1(sK6,k5_relat_1(sK4,sK5)),sK2,sK1)
    | k1_xboole_0 = sK3
    | ~ v1_funct_2(sK4,sK2,sK3)
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f2666,f101])).

fof(f2666,plain,
    ( v1_funct_2(k5_relat_1(sK6,k5_relat_1(sK4,sK5)),sK2,sK1)
    | k1_xboole_0 = sK3
    | ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5))
    | ~ v1_funct_2(sK4,sK2,sK3)
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f2665,f93])).

fof(f2665,plain,
    ( v1_funct_2(k5_relat_1(sK6,k5_relat_1(sK4,sK5)),sK2,sK1)
    | ~ v1_funct_1(sK4)
    | k1_xboole_0 = sK3
    | ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5))
    | ~ v1_funct_2(sK4,sK2,sK3)
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f2664,f95])).

fof(f2664,plain,
    ( v1_funct_2(k5_relat_1(sK6,k5_relat_1(sK4,sK5)),sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(sK4)
    | k1_xboole_0 = sK3
    | ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5))
    | ~ v1_funct_2(sK4,sK2,sK3)
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f2663,f96])).

fof(f2663,plain,
    ( v1_funct_2(k5_relat_1(sK6,k5_relat_1(sK4,sK5)),sK2,sK1)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(sK4)
    | k1_xboole_0 = sK3
    | ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5))
    | ~ v1_funct_2(sK4,sK2,sK3)
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f2275,f97])).

fof(f2275,plain,
    ( v1_funct_2(k5_relat_1(sK6,k5_relat_1(sK4,sK5)),sK2,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(sK4)
    | k1_xboole_0 = sK3
    | ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5))
    | ~ v1_funct_2(sK4,sK2,sK3)
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_22 ),
    inference(superposition,[],[f592,f607])).

fof(f592,plain,
    ( v1_funct_2(k5_relat_1(sK6,k8_funct_2(sK2,sK3,sK1,sK4,sK5)),sK2,sK1)
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f591,f389])).

fof(f389,plain,
    ( v1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5))
    | ~ spl9_16 ),
    inference(avatar_component_clause,[],[f388])).

fof(f591,plain,
    ( v1_funct_2(k5_relat_1(sK6,k8_funct_2(sK2,sK3,sK1,sK4,sK5)),sK2,sK1)
    | ~ v1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5))
    | ~ spl9_18
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f582,f435])).

fof(f435,plain,
    ( v1_funct_2(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK2,sK1)
    | ~ spl9_22 ),
    inference(avatar_component_clause,[],[f434])).

fof(f582,plain,
    ( v1_funct_2(k5_relat_1(sK6,k8_funct_2(sK2,sK3,sK1,sK4,sK5)),sK2,sK1)
    | ~ v1_funct_2(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK2,sK1)
    | ~ v1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5))
    | ~ spl9_18 ),
    inference(resolution,[],[f514,f395])).

fof(f395,plain,
    ( m1_subset_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl9_18 ),
    inference(avatar_component_clause,[],[f394])).

fof(f2629,plain,
    ( spl9_114
    | spl9_172
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_22 ),
    inference(avatar_split_clause,[],[f2622,f434,f394,f388,f2627,f2341])).

fof(f2622,plain,
    ( v1_funct_1(k5_relat_1(sK6,k5_relat_1(sK4,sK5)))
    | k1_xboole_0 = sK3
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f2621,f94])).

fof(f2621,plain,
    ( v1_funct_1(k5_relat_1(sK6,k5_relat_1(sK4,sK5)))
    | k1_xboole_0 = sK3
    | ~ v1_funct_2(sK4,sK2,sK3)
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f2620,f101])).

fof(f2620,plain,
    ( v1_funct_1(k5_relat_1(sK6,k5_relat_1(sK4,sK5)))
    | k1_xboole_0 = sK3
    | ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5))
    | ~ v1_funct_2(sK4,sK2,sK3)
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f2619,f93])).

fof(f2619,plain,
    ( v1_funct_1(k5_relat_1(sK6,k5_relat_1(sK4,sK5)))
    | ~ v1_funct_1(sK4)
    | k1_xboole_0 = sK3
    | ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5))
    | ~ v1_funct_2(sK4,sK2,sK3)
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f2618,f95])).

fof(f2618,plain,
    ( v1_funct_1(k5_relat_1(sK6,k5_relat_1(sK4,sK5)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(sK4)
    | k1_xboole_0 = sK3
    | ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5))
    | ~ v1_funct_2(sK4,sK2,sK3)
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f2617,f96])).

fof(f2617,plain,
    ( v1_funct_1(k5_relat_1(sK6,k5_relat_1(sK4,sK5)))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(sK4)
    | k1_xboole_0 = sK3
    | ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5))
    | ~ v1_funct_2(sK4,sK2,sK3)
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f2271,f97])).

fof(f2271,plain,
    ( v1_funct_1(k5_relat_1(sK6,k5_relat_1(sK4,sK5)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(sK4)
    | k1_xboole_0 = sK3
    | ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5))
    | ~ v1_funct_2(sK4,sK2,sK3)
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_22 ),
    inference(superposition,[],[f525,f607])).

fof(f525,plain,
    ( v1_funct_1(k5_relat_1(sK6,k8_funct_2(sK2,sK3,sK1,sK4,sK5)))
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f524,f389])).

fof(f524,plain,
    ( v1_funct_1(k5_relat_1(sK6,k8_funct_2(sK2,sK3,sK1,sK4,sK5)))
    | ~ v1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5))
    | ~ spl9_18
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f515,f435])).

fof(f515,plain,
    ( v1_funct_1(k5_relat_1(sK6,k8_funct_2(sK2,sK3,sK1,sK4,sK5)))
    | ~ v1_funct_2(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK2,sK1)
    | ~ v1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5))
    | ~ spl9_18 ),
    inference(resolution,[],[f465,f395])).

fof(f473,plain,(
    spl9_23 ),
    inference(avatar_contradiction_clause,[],[f472])).

fof(f472,plain,
    ( $false
    | ~ spl9_23 ),
    inference(subsumption_resolution,[],[f471,f93])).

fof(f471,plain,
    ( ~ v1_funct_1(sK4)
    | ~ spl9_23 ),
    inference(subsumption_resolution,[],[f470,f94])).

fof(f470,plain,
    ( ~ v1_funct_2(sK4,sK2,sK3)
    | ~ v1_funct_1(sK4)
    | ~ spl9_23 ),
    inference(subsumption_resolution,[],[f469,f95])).

fof(f469,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_2(sK4,sK2,sK3)
    | ~ v1_funct_1(sK4)
    | ~ spl9_23 ),
    inference(subsumption_resolution,[],[f468,f96])).

fof(f468,plain,
    ( ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_2(sK4,sK2,sK3)
    | ~ v1_funct_1(sK4)
    | ~ spl9_23 ),
    inference(subsumption_resolution,[],[f467,f97])).

fof(f467,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_2(sK4,sK2,sK3)
    | ~ v1_funct_1(sK4)
    | ~ spl9_23 ),
    inference(resolution,[],[f466,f134])).

fof(f134,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP0(X2,X0,X4,X3,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( sP0(X2,X0,X4,X3,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(definition_folding,[],[f72,f77])).

fof(f77,plain,(
    ! [X2,X0,X4,X3,X1] :
      ( ( m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)
        & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) )
      | ~ sP0(X2,X0,X4,X3,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f72,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)
        & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f71])).

fof(f71,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)
        & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X4)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)
        & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t187_funct_2.p',dt_k8_funct_2)).

fof(f466,plain,
    ( ~ sP0(sK1,sK2,sK5,sK4,sK3)
    | ~ spl9_23 ),
    inference(resolution,[],[f438,f132])).

fof(f132,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k8_funct_2(X1,X4,X0,X3,X2),X1,X0)
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f89])).

fof(f89,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k8_funct_2(X1,X4,X0,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k8_funct_2(X1,X4,X0,X3,X2),X1,X0)
        & v1_funct_1(k8_funct_2(X1,X4,X0,X3,X2)) )
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(rectify,[],[f88])).

fof(f88,plain,(
    ! [X2,X0,X4,X3,X1] :
      ( ( m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)
        & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) )
      | ~ sP0(X2,X0,X4,X3,X1) ) ),
    inference(nnf_transformation,[],[f77])).

fof(f438,plain,
    ( ~ v1_funct_2(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK2,sK1)
    | ~ spl9_23 ),
    inference(avatar_component_clause,[],[f437])).

fof(f437,plain,
    ( spl9_23
  <=> ~ v1_funct_2(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).

fof(f426,plain,(
    spl9_19 ),
    inference(avatar_contradiction_clause,[],[f425])).

fof(f425,plain,
    ( $false
    | ~ spl9_19 ),
    inference(subsumption_resolution,[],[f424,f93])).

fof(f424,plain,
    ( ~ v1_funct_1(sK4)
    | ~ spl9_19 ),
    inference(subsumption_resolution,[],[f423,f94])).

fof(f423,plain,
    ( ~ v1_funct_2(sK4,sK2,sK3)
    | ~ v1_funct_1(sK4)
    | ~ spl9_19 ),
    inference(subsumption_resolution,[],[f422,f95])).

fof(f422,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_2(sK4,sK2,sK3)
    | ~ v1_funct_1(sK4)
    | ~ spl9_19 ),
    inference(subsumption_resolution,[],[f421,f96])).

fof(f421,plain,
    ( ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_2(sK4,sK2,sK3)
    | ~ v1_funct_1(sK4)
    | ~ spl9_19 ),
    inference(subsumption_resolution,[],[f420,f97])).

fof(f420,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_2(sK4,sK2,sK3)
    | ~ v1_funct_1(sK4)
    | ~ spl9_19 ),
    inference(resolution,[],[f418,f134])).

fof(f418,plain,
    ( ~ sP0(sK1,sK2,sK5,sK4,sK3)
    | ~ spl9_19 ),
    inference(resolution,[],[f398,f133])).

fof(f133,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k8_funct_2(X1,X4,X0,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f89])).

fof(f398,plain,
    ( ~ m1_subset_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl9_19 ),
    inference(avatar_component_clause,[],[f397])).
%------------------------------------------------------------------------------
