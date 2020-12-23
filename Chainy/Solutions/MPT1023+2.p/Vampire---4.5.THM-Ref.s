%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1023+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:03 EST 2020

% Result     : Theorem 3.36s
% Output     : Refutation 3.36s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 155 expanded)
%              Number of leaves         :    7 (  52 expanded)
%              Depth                    :   14
%              Number of atoms          :  216 (1315 expanded)
%              Number of equality atoms :   18 ( 151 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10241,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f10183,f10228,f5716])).

fof(f5716,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f2286])).

fof(f2286,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f591])).

fof(f591,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f10228,plain,(
    ~ m1_subset_1(sK377(sK11,sK13,sK14),sK11) ),
    inference(resolution,[],[f10201,f7874])).

fof(f7874,plain,(
    ! [X4] :
      ( sQ522_eqProxy(k1_funct_1(sK13,X4),k1_funct_1(sK14,X4))
      | ~ m1_subset_1(X4,sK11) ) ),
    inference(equality_proxy_replacement,[],[f4462,f7846])).

fof(f7846,plain,(
    ! [X1,X0] :
      ( sQ522_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ522_eqProxy])])).

fof(f4462,plain,(
    ! [X4] :
      ( k1_funct_1(sK13,X4) = k1_funct_1(sK14,X4)
      | ~ m1_subset_1(X4,sK11) ) ),
    inference(cnf_transformation,[],[f3265])).

fof(f3265,plain,
    ( ~ r2_relset_1(sK11,sK12,sK13,sK14)
    & ! [X4] :
        ( k1_funct_1(sK13,X4) = k1_funct_1(sK14,X4)
        | ~ m1_subset_1(X4,sK11) )
    & m1_subset_1(sK14,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12)))
    & v1_funct_2(sK14,sK11,sK12)
    & v1_funct_1(sK14)
    & m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12)))
    & v1_funct_2(sK13,sK11,sK12)
    & v1_funct_1(sK13) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11,sK12,sK13,sK14])],[f1608,f3264,f3263])).

fof(f3263,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r2_relset_1(X0,X1,X2,X3)
            & ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ m1_subset_1(X4,X0) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ~ r2_relset_1(sK11,sK12,sK13,X3)
          & ! [X4] :
              ( k1_funct_1(X3,X4) = k1_funct_1(sK13,X4)
              | ~ m1_subset_1(X4,sK11) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12)))
          & v1_funct_2(X3,sK11,sK12)
          & v1_funct_1(X3) )
      & m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12)))
      & v1_funct_2(sK13,sK11,sK12)
      & v1_funct_1(sK13) ) ),
    introduced(choice_axiom,[])).

fof(f3264,plain,
    ( ? [X3] :
        ( ~ r2_relset_1(sK11,sK12,sK13,X3)
        & ! [X4] :
            ( k1_funct_1(X3,X4) = k1_funct_1(sK13,X4)
            | ~ m1_subset_1(X4,sK11) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12)))
        & v1_funct_2(X3,sK11,sK12)
        & v1_funct_1(X3) )
   => ( ~ r2_relset_1(sK11,sK12,sK13,sK14)
      & ! [X4] :
          ( k1_funct_1(sK13,X4) = k1_funct_1(sK14,X4)
          | ~ m1_subset_1(X4,sK11) )
      & m1_subset_1(sK14,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12)))
      & v1_funct_2(sK14,sK11,sK12)
      & v1_funct_1(sK14) ) ),
    introduced(choice_axiom,[])).

fof(f1608,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ m1_subset_1(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f1607])).

fof(f1607,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ m1_subset_1(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1508])).

fof(f1508,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
           => ( ! [X4] :
                  ( m1_subset_1(X4,X0)
                 => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
             => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    inference(negated_conjecture,[],[f1507])).

fof(f1507,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( ! [X4] :
                ( m1_subset_1(X4,X0)
               => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
           => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_funct_2)).

fof(f10201,plain,(
    ~ sQ522_eqProxy(k1_funct_1(sK13,sK377(sK11,sK13,sK14)),k1_funct_1(sK14,sK377(sK11,sK13,sK14))) ),
    inference(subsumption_resolution,[],[f10200,f4456])).

fof(f4456,plain,(
    v1_funct_1(sK13) ),
    inference(cnf_transformation,[],[f3265])).

fof(f10200,plain,
    ( ~ sQ522_eqProxy(k1_funct_1(sK13,sK377(sK11,sK13,sK14)),k1_funct_1(sK14,sK377(sK11,sK13,sK14)))
    | ~ v1_funct_1(sK13) ),
    inference(subsumption_resolution,[],[f10199,f4457])).

fof(f4457,plain,(
    v1_funct_2(sK13,sK11,sK12) ),
    inference(cnf_transformation,[],[f3265])).

fof(f10199,plain,
    ( ~ sQ522_eqProxy(k1_funct_1(sK13,sK377(sK11,sK13,sK14)),k1_funct_1(sK14,sK377(sK11,sK13,sK14)))
    | ~ v1_funct_2(sK13,sK11,sK12)
    | ~ v1_funct_1(sK13) ),
    inference(subsumption_resolution,[],[f10198,f4458])).

fof(f4458,plain,(
    m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12))) ),
    inference(cnf_transformation,[],[f3265])).

fof(f10198,plain,
    ( ~ sQ522_eqProxy(k1_funct_1(sK13,sK377(sK11,sK13,sK14)),k1_funct_1(sK14,sK377(sK11,sK13,sK14)))
    | ~ m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12)))
    | ~ v1_funct_2(sK13,sK11,sK12)
    | ~ v1_funct_1(sK13) ),
    inference(subsumption_resolution,[],[f10197,f4459])).

fof(f4459,plain,(
    v1_funct_1(sK14) ),
    inference(cnf_transformation,[],[f3265])).

fof(f10197,plain,
    ( ~ sQ522_eqProxy(k1_funct_1(sK13,sK377(sK11,sK13,sK14)),k1_funct_1(sK14,sK377(sK11,sK13,sK14)))
    | ~ v1_funct_1(sK14)
    | ~ m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12)))
    | ~ v1_funct_2(sK13,sK11,sK12)
    | ~ v1_funct_1(sK13) ),
    inference(subsumption_resolution,[],[f10196,f4460])).

fof(f4460,plain,(
    v1_funct_2(sK14,sK11,sK12) ),
    inference(cnf_transformation,[],[f3265])).

fof(f10196,plain,
    ( ~ sQ522_eqProxy(k1_funct_1(sK13,sK377(sK11,sK13,sK14)),k1_funct_1(sK14,sK377(sK11,sK13,sK14)))
    | ~ v1_funct_2(sK14,sK11,sK12)
    | ~ v1_funct_1(sK14)
    | ~ m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12)))
    | ~ v1_funct_2(sK13,sK11,sK12)
    | ~ v1_funct_1(sK13) ),
    inference(subsumption_resolution,[],[f10190,f4461])).

fof(f4461,plain,(
    m1_subset_1(sK14,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12))) ),
    inference(cnf_transformation,[],[f3265])).

fof(f10190,plain,
    ( ~ sQ522_eqProxy(k1_funct_1(sK13,sK377(sK11,sK13,sK14)),k1_funct_1(sK14,sK377(sK11,sK13,sK14)))
    | ~ m1_subset_1(sK14,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12)))
    | ~ v1_funct_2(sK14,sK11,sK12)
    | ~ v1_funct_1(sK14)
    | ~ m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12)))
    | ~ v1_funct_2(sK13,sK11,sK12)
    | ~ v1_funct_1(sK13) ),
    inference(resolution,[],[f8798,f4463])).

fof(f4463,plain,(
    ~ r2_relset_1(sK11,sK12,sK13,sK14) ),
    inference(cnf_transformation,[],[f3265])).

fof(f8798,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | ~ sQ522_eqProxy(k1_funct_1(X2,sK377(X0,X2,X3)),k1_funct_1(X3,sK377(X0,X2,X3)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(equality_proxy_replacement,[],[f6581,f7846])).

fof(f6581,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | k1_funct_1(X2,sK377(X0,X2,X3)) != k1_funct_1(X3,sK377(X0,X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f4162])).

fof(f4162,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,X1,X2,X3)
          | ( k1_funct_1(X2,sK377(X0,X2,X3)) != k1_funct_1(X3,sK377(X0,X2,X3))
            & r2_hidden(sK377(X0,X2,X3),X0) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK377])],[f2835,f4161])).

fof(f4161,plain,(
    ! [X3,X2,X0] :
      ( ? [X4] :
          ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
          & r2_hidden(X4,X0) )
     => ( k1_funct_1(X2,sK377(X0,X2,X3)) != k1_funct_1(X3,sK377(X0,X2,X3))
        & r2_hidden(sK377(X0,X2,X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f2835,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,X1,X2,X3)
          | ? [X4] :
              ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
              & r2_hidden(X4,X0) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f2834])).

fof(f2834,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,X1,X2,X3)
          | ? [X4] :
              ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
              & r2_hidden(X4,X0) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1513])).

fof(f1513,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( ! [X4] :
                ( r2_hidden(X4,X0)
               => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
           => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_2)).

fof(f10183,plain,(
    r2_hidden(sK377(sK11,sK13,sK14),sK11) ),
    inference(subsumption_resolution,[],[f10182,f4456])).

fof(f10182,plain,
    ( r2_hidden(sK377(sK11,sK13,sK14),sK11)
    | ~ v1_funct_1(sK13) ),
    inference(subsumption_resolution,[],[f10181,f4457])).

fof(f10181,plain,
    ( r2_hidden(sK377(sK11,sK13,sK14),sK11)
    | ~ v1_funct_2(sK13,sK11,sK12)
    | ~ v1_funct_1(sK13) ),
    inference(subsumption_resolution,[],[f10180,f4458])).

fof(f10180,plain,
    ( r2_hidden(sK377(sK11,sK13,sK14),sK11)
    | ~ m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12)))
    | ~ v1_funct_2(sK13,sK11,sK12)
    | ~ v1_funct_1(sK13) ),
    inference(subsumption_resolution,[],[f10179,f4459])).

fof(f10179,plain,
    ( r2_hidden(sK377(sK11,sK13,sK14),sK11)
    | ~ v1_funct_1(sK14)
    | ~ m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12)))
    | ~ v1_funct_2(sK13,sK11,sK12)
    | ~ v1_funct_1(sK13) ),
    inference(subsumption_resolution,[],[f10178,f4460])).

fof(f10178,plain,
    ( r2_hidden(sK377(sK11,sK13,sK14),sK11)
    | ~ v1_funct_2(sK14,sK11,sK12)
    | ~ v1_funct_1(sK14)
    | ~ m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12)))
    | ~ v1_funct_2(sK13,sK11,sK12)
    | ~ v1_funct_1(sK13) ),
    inference(subsumption_resolution,[],[f10172,f4461])).

fof(f10172,plain,
    ( r2_hidden(sK377(sK11,sK13,sK14),sK11)
    | ~ m1_subset_1(sK14,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12)))
    | ~ v1_funct_2(sK14,sK11,sK12)
    | ~ v1_funct_1(sK14)
    | ~ m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12)))
    | ~ v1_funct_2(sK13,sK11,sK12)
    | ~ v1_funct_1(sK13) ),
    inference(resolution,[],[f6580,f4463])).

fof(f6580,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | r2_hidden(sK377(X0,X2,X3),X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f4162])).
%------------------------------------------------------------------------------
