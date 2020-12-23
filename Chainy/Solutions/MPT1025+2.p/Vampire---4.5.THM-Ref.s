%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1025+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:03 EST 2020

% Result     : Theorem 1.85s
% Output     : Refutation 1.85s
% Verified   : 
% Statistics : Number of formulae       :   42 ( 145 expanded)
%              Number of leaves         :    7 (  48 expanded)
%              Depth                    :   12
%              Number of atoms          :  164 ( 926 expanded)
%              Number of equality atoms :   18 ( 139 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2655,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2654,f2332])).

fof(f2332,plain,(
    m1_subset_1(sK20(sK0,sK2,sK3,sK4),sK0) ),
    inference(resolution,[],[f2205,f1836])).

fof(f1836,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f1632])).

fof(f1632,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f591])).

fof(f591,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f2205,plain,(
    r2_hidden(sK20(sK0,sK2,sK3,sK4),sK0) ),
    inference(subsumption_resolution,[],[f2204,f1757])).

fof(f1757,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f1690])).

fof(f1690,plain,
    ( ! [X5] :
        ( k1_funct_1(sK3,X5) != sK4
        | ~ r2_hidden(X5,sK2)
        | ~ m1_subset_1(X5,sK0) )
    & r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f1582,f1689,f1688])).

fof(f1688,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ! [X5] :
                ( k1_funct_1(X3,X5) != X4
                | ~ r2_hidden(X5,X2)
                | ~ m1_subset_1(X5,X0) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(sK3,X5) != X4
              | ~ r2_hidden(X5,sK2)
              | ~ m1_subset_1(X5,sK0) )
          & r2_hidden(X4,k7_relset_1(sK0,sK1,sK3,sK2)) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f1689,plain,
    ( ? [X4] :
        ( ! [X5] :
            ( k1_funct_1(sK3,X5) != X4
            | ~ r2_hidden(X5,sK2)
            | ~ m1_subset_1(X5,sK0) )
        & r2_hidden(X4,k7_relset_1(sK0,sK1,sK3,sK2)) )
   => ( ! [X5] :
          ( k1_funct_1(sK3,X5) != sK4
          | ~ r2_hidden(X5,sK2)
          | ~ m1_subset_1(X5,sK0) )
      & r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f1582,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f1581])).

fof(f1581,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f1510])).

fof(f1510,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ( m1_subset_1(X5,X0)
                 => ~ ( k1_funct_1(X3,X5) = X4
                      & r2_hidden(X5,X2) ) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(negated_conjecture,[],[f1509])).

fof(f1509,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ~ ( ! [X5] :
                ( m1_subset_1(X5,X0)
               => ~ ( k1_funct_1(X3,X5) = X4
                    & r2_hidden(X5,X2) ) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_funct_2)).

fof(f2204,plain,
    ( r2_hidden(sK20(sK0,sK2,sK3,sK4),sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f2203,f1758])).

fof(f1758,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f1690])).

fof(f2203,plain,
    ( r2_hidden(sK20(sK0,sK2,sK3,sK4),sK0)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f2174,f1759])).

fof(f1759,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f1690])).

fof(f2174,plain,
    ( r2_hidden(sK20(sK0,sK2,sK3,sK4),sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f1760,f1826])).

fof(f1826,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(sK20(X0,X2,X3,X4),X0)
      | ~ r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f1729])).

fof(f1729,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( k1_funct_1(X3,sK20(X0,X2,X3,X4)) = X4
            & r2_hidden(sK20(X0,X2,X3,X4),X2)
            & r2_hidden(sK20(X0,X2,X3,X4),X0) )
          | ~ r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK20])],[f1621,f1728])).

fof(f1728,plain,(
    ! [X4,X3,X2,X0] :
      ( ? [X5] :
          ( k1_funct_1(X3,X5) = X4
          & r2_hidden(X5,X2)
          & r2_hidden(X5,X0) )
     => ( k1_funct_1(X3,sK20(X0,X2,X3,X4)) = X4
        & r2_hidden(sK20(X0,X2,X3,X4),X2)
        & r2_hidden(sK20(X0,X2,X3,X4),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1621,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ? [X5] :
              ( k1_funct_1(X3,X5) = X4
              & r2_hidden(X5,X2)
              & r2_hidden(X5,X0) )
          | ~ r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f1620])).

fof(f1620,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ? [X5] :
              ( k1_funct_1(X3,X5) = X4
              & r2_hidden(X5,X2)
              & r2_hidden(X5,X0) )
          | ~ r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f1508])).

fof(f1508,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ~ ( ! [X5] :
                ~ ( k1_funct_1(X3,X5) = X4
                  & r2_hidden(X5,X2)
                  & r2_hidden(X5,X0) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t115_funct_2)).

fof(f1760,plain,(
    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f1690])).

fof(f2654,plain,(
    ~ m1_subset_1(sK20(sK0,sK2,sK3,sK4),sK0) ),
    inference(subsumption_resolution,[],[f2653,f2208])).

fof(f2208,plain,(
    r2_hidden(sK20(sK0,sK2,sK3,sK4),sK2) ),
    inference(subsumption_resolution,[],[f2207,f1757])).

fof(f2207,plain,
    ( r2_hidden(sK20(sK0,sK2,sK3,sK4),sK2)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f2206,f1758])).

fof(f2206,plain,
    ( r2_hidden(sK20(sK0,sK2,sK3,sK4),sK2)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f2175,f1759])).

fof(f2175,plain,
    ( r2_hidden(sK20(sK0,sK2,sK3,sK4),sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f1760,f1827])).

fof(f1827,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(sK20(X0,X2,X3,X4),X2)
      | ~ r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f1729])).

fof(f2653,plain,
    ( ~ r2_hidden(sK20(sK0,sK2,sK3,sK4),sK2)
    | ~ m1_subset_1(sK20(sK0,sK2,sK3,sK4),sK0) ),
    inference(resolution,[],[f2211,f1937])).

fof(f1937,plain,(
    ! [X5] :
      ( ~ sQ30_eqProxy(k1_funct_1(sK3,X5),sK4)
      | ~ r2_hidden(X5,sK2)
      | ~ m1_subset_1(X5,sK0) ) ),
    inference(equality_proxy_replacement,[],[f1761,f1936])).

fof(f1936,plain,(
    ! [X1,X0] :
      ( sQ30_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ30_eqProxy])])).

fof(f1761,plain,(
    ! [X5] :
      ( k1_funct_1(sK3,X5) != sK4
      | ~ r2_hidden(X5,sK2)
      | ~ m1_subset_1(X5,sK0) ) ),
    inference(cnf_transformation,[],[f1690])).

fof(f2211,plain,(
    sQ30_eqProxy(k1_funct_1(sK3,sK20(sK0,sK2,sK3,sK4)),sK4) ),
    inference(subsumption_resolution,[],[f2210,f1757])).

fof(f2210,plain,
    ( sQ30_eqProxy(k1_funct_1(sK3,sK20(sK0,sK2,sK3,sK4)),sK4)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f2209,f1758])).

fof(f2209,plain,
    ( sQ30_eqProxy(k1_funct_1(sK3,sK20(sK0,sK2,sK3,sK4)),sK4)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f2176,f1759])).

fof(f2176,plain,
    ( sQ30_eqProxy(k1_funct_1(sK3,sK20(sK0,sK2,sK3,sK4)),sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f1760,f1973])).

fof(f1973,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sQ30_eqProxy(k1_funct_1(X3,sK20(X0,X2,X3,X4)),X4)
      | ~ r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_proxy_replacement,[],[f1828,f1936])).

fof(f1828,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_funct_1(X3,sK20(X0,X2,X3,X4)) = X4
      | ~ r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f1729])).
%------------------------------------------------------------------------------
