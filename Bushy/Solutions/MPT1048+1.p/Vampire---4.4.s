%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_2__t165_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:35 EDT 2019

% Result     : Theorem 22.34s
% Output     : Refutation 22.34s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 326 expanded)
%              Number of leaves         :   11 (  63 expanded)
%              Depth                    :   16
%              Number of atoms          :  330 (1413 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3512,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f3494,f3496,f3505])).

fof(f3505,plain,(
    ~ spl13_92 ),
    inference(avatar_contradiction_clause,[],[f3504])).

fof(f3504,plain,
    ( $false
    | ~ spl13_92 ),
    inference(subsumption_resolution,[],[f3503,f718])).

fof(f718,plain,(
    ~ r1_partfun1(sK3,sK5(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3))) ),
    inference(subsumption_resolution,[],[f717,f684])).

fof(f684,plain,(
    v1_partfun1(sK5(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)),sK0) ),
    inference(resolution,[],[f304,f286])).

fof(f286,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k5_partfun1(sK0,sK1,sK2))
      | v1_partfun1(X3,sK0) ) ),
    inference(subsumption_resolution,[],[f285,f281])).

fof(f281,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k5_partfun1(sK0,sK1,sK2))
      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    inference(subsumption_resolution,[],[f254,f68])).

fof(f68,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3))
          & r1_relset_1(X0,X1,X3,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3))
          & r1_relset_1(X0,X1,X3,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_1(X3) )
           => ( r1_relset_1(X0,X1,X3,X2)
             => r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3)) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
         => ( r1_relset_1(X0,X1,X3,X2)
           => r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t165_funct_2.p',t165_funct_2)).

fof(f254,plain,(
    ! [X1] :
      ( ~ v1_funct_1(sK2)
      | ~ r2_hidden(X1,k5_partfun1(sK0,sK1,sK2))
      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    inference(resolution,[],[f69,f87])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
          | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
          | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
         => ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t165_funct_2.p',t168_partfun1)).

fof(f69,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f35])).

fof(f285,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ r2_hidden(X3,k5_partfun1(sK0,sK1,sK2))
      | v1_partfun1(X3,sK0) ) ),
    inference(subsumption_resolution,[],[f284,f280])).

fof(f280,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k5_partfun1(sK0,sK1,sK2))
      | v1_funct_1(X0) ) ),
    inference(subsumption_resolution,[],[f253,f68])).

fof(f253,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK2)
      | ~ r2_hidden(X0,k5_partfun1(sK0,sK1,sK2))
      | v1_funct_1(X0) ) ),
    inference(resolution,[],[f69,f86])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f284,plain,(
    ! [X3] :
      ( ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ r2_hidden(X3,k5_partfun1(sK0,sK1,sK2))
      | v1_partfun1(X3,sK0) ) ),
    inference(subsumption_resolution,[],[f256,f68])).

fof(f256,plain,(
    ! [X3] :
      ( ~ v1_funct_1(sK2)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ r2_hidden(X3,k5_partfun1(sK0,sK1,sK2))
      | v1_partfun1(X3,sK0) ) ),
    inference(resolution,[],[f69,f89])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | v1_partfun1(X3,X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( v1_partfun1(X3,X0)
          | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( v1_partfun1(X3,X0)
          | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
         => ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
           => v1_partfun1(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t165_funct_2.p',t169_partfun1)).

fof(f304,plain,(
    r2_hidden(sK5(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)),k5_partfun1(sK0,sK1,sK2)) ),
    inference(resolution,[],[f67,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t165_funct_2.p',d3_tarski)).

fof(f67,plain,(
    ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)) ),
    inference(cnf_transformation,[],[f35])).

fof(f717,plain,
    ( ~ v1_partfun1(sK5(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)),sK0)
    | ~ r1_partfun1(sK3,sK5(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3))) ),
    inference(subsumption_resolution,[],[f716,f682])).

fof(f682,plain,(
    m1_subset_1(sK5(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f304,f281])).

fof(f716,plain,
    ( ~ m1_subset_1(sK5(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_partfun1(sK5(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)),sK0)
    | ~ r1_partfun1(sK3,sK5(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3))) ),
    inference(subsumption_resolution,[],[f715,f685])).

fof(f685,plain,(
    v1_funct_1(sK5(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3))) ),
    inference(resolution,[],[f304,f280])).

fof(f715,plain,
    ( ~ v1_funct_1(sK5(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)))
    | ~ m1_subset_1(sK5(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_partfun1(sK5(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)),sK0)
    | ~ r1_partfun1(sK3,sK5(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3))) ),
    inference(subsumption_resolution,[],[f714,f65])).

fof(f65,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f35])).

fof(f714,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK5(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)))
    | ~ m1_subset_1(sK5(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_partfun1(sK5(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)),sK0)
    | ~ r1_partfun1(sK3,sK5(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3))) ),
    inference(subsumption_resolution,[],[f711,f64])).

fof(f64,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f711,plain,
    ( ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK5(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)))
    | ~ m1_subset_1(sK5(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_partfun1(sK5(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)),sK0)
    | ~ r1_partfun1(sK3,sK5(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3))) ),
    inference(resolution,[],[f305,f109])).

fof(f109,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_partfun1(X5,X0)
      | ~ r1_partfun1(X2,X5)
      | r2_hidden(X5,k5_partfun1(X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f108])).

fof(f108,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_partfun1(X5,X0)
      | ~ r1_partfun1(X2,X5)
      | r2_hidden(X5,X3)
      | k5_partfun1(X0,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f102])).

fof(f102,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X4 != X5
      | ~ v1_partfun1(X5,X0)
      | ~ r1_partfun1(X2,X5)
      | r2_hidden(X4,X3)
      | k5_partfun1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t165_funct_2.p',d7_partfun1)).

fof(f305,plain,(
    ~ r2_hidden(sK5(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)),k5_partfun1(sK0,sK1,sK3)) ),
    inference(resolution,[],[f67,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f3503,plain,
    ( r1_partfun1(sK3,sK5(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)))
    | ~ spl13_92 ),
    inference(subsumption_resolution,[],[f3502,f1972])).

fof(f1972,plain,(
    v1_relat_1(sK5(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3))) ),
    inference(resolution,[],[f682,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t165_funct_2.p',cc1_relset_1)).

fof(f3502,plain,
    ( ~ v1_relat_1(sK5(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)))
    | r1_partfun1(sK3,sK5(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)))
    | ~ spl13_92 ),
    inference(subsumption_resolution,[],[f3497,f685])).

fof(f3497,plain,
    ( ~ v1_funct_1(sK5(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)))
    | ~ v1_relat_1(sK5(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)))
    | r1_partfun1(sK3,sK5(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)))
    | ~ spl13_92 ),
    inference(resolution,[],[f3487,f354])).

fof(f354,plain,(
    ! [X0] :
      ( ~ r1_partfun1(sK2,X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r1_partfun1(sK3,X0) ) ),
    inference(resolution,[],[f201,f118])).

fof(f118,plain,(
    ! [X4,X2,X3] :
      ( ~ v1_relat_1(X4)
      | ~ v1_funct_1(X4)
      | ~ r1_partfun1(X2,X4)
      | r1_partfun1(X3,X4)
      | sP10(X3,X2) ) ),
    inference(cnf_transformation,[],[f118_D])).

fof(f118_D,plain,(
    ! [X2,X3] :
      ( ! [X4] :
          ( ~ v1_relat_1(X4)
          | ~ v1_funct_1(X4)
          | ~ r1_partfun1(X2,X4)
          | r1_partfun1(X3,X4) )
    <=> ~ sP10(X3,X2) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP10])])).

fof(f201,plain,(
    ~ sP10(sK3,sK2) ),
    inference(subsumption_resolution,[],[f200,f65])).

fof(f200,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ sP10(sK3,sK2) ),
    inference(subsumption_resolution,[],[f199,f64])).

fof(f199,plain,
    ( ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ sP10(sK3,sK2) ),
    inference(subsumption_resolution,[],[f198,f69])).

fof(f198,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ sP10(sK3,sK2) ),
    inference(subsumption_resolution,[],[f196,f68])).

fof(f196,plain,
    ( ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ sP10(sK3,sK2) ),
    inference(resolution,[],[f66,f119])).

fof(f119,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_relset_1(X0,X1,X3,X2)
      | ~ sP10(X3,X2) ) ),
    inference(general_splitting,[],[f90,f118_D])).

fof(f90,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_relat_1(X4)
      | ~ v1_funct_1(X4)
      | ~ r1_partfun1(X2,X4)
      | ~ r1_relset_1(X0,X1,X3,X2)
      | r1_partfun1(X3,X4) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( r1_partfun1(X3,X4)
              | ~ r1_relset_1(X0,X1,X3,X2)
              | ~ r1_partfun1(X2,X4)
              | ~ v1_funct_1(X4)
              | ~ v1_relat_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( r1_partfun1(X3,X4)
              | ~ r1_relset_1(X0,X1,X3,X2)
              | ~ r1_partfun1(X2,X4)
              | ~ v1_funct_1(X4)
              | ~ v1_relat_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
         => ! [X4] :
              ( ( v1_funct_1(X4)
                & v1_relat_1(X4) )
             => ( ( r1_relset_1(X0,X1,X3,X2)
                  & r1_partfun1(X2,X4) )
               => r1_partfun1(X3,X4) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t165_funct_2.p',t140_partfun1)).

fof(f66,plain,(
    r1_relset_1(sK0,sK1,sK3,sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f3487,plain,
    ( r1_partfun1(sK2,sK5(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)))
    | ~ spl13_92 ),
    inference(avatar_component_clause,[],[f3486])).

fof(f3486,plain,
    ( spl13_92
  <=> r1_partfun1(sK2,sK5(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_92])])).

fof(f3496,plain,(
    spl13_95 ),
    inference(avatar_contradiction_clause,[],[f3495])).

fof(f3495,plain,
    ( $false
    | ~ spl13_95 ),
    inference(subsumption_resolution,[],[f3493,f1972])).

fof(f3493,plain,
    ( ~ v1_relat_1(sK5(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)))
    | ~ spl13_95 ),
    inference(avatar_component_clause,[],[f3492])).

fof(f3492,plain,
    ( spl13_95
  <=> ~ v1_relat_1(sK5(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_95])])).

fof(f3494,plain,
    ( spl13_92
    | ~ spl13_95 ),
    inference(avatar_split_clause,[],[f683,f3492,f3486])).

fof(f683,plain,
    ( ~ v1_relat_1(sK5(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)))
    | r1_partfun1(sK2,sK5(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3))) ),
    inference(resolution,[],[f304,f283])).

fof(f283,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k5_partfun1(sK0,sK1,sK2))
      | ~ v1_relat_1(X2)
      | r1_partfun1(sK2,X2) ) ),
    inference(subsumption_resolution,[],[f282,f280])).

fof(f282,plain,(
    ! [X2] :
      ( ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ r2_hidden(X2,k5_partfun1(sK0,sK1,sK2))
      | r1_partfun1(sK2,X2) ) ),
    inference(subsumption_resolution,[],[f255,f68])).

fof(f255,plain,(
    ! [X2] :
      ( ~ v1_funct_1(sK2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ r2_hidden(X2,k5_partfun1(sK0,sK1,sK2))
      | r1_partfun1(sK2,X2) ) ),
    inference(resolution,[],[f69,f88])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_relat_1(X3)
      | ~ v1_funct_1(X3)
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | r1_partfun1(X2,X3) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_partfun1(X2,X3)
          | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
          | ~ v1_funct_1(X3)
          | ~ v1_relat_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_partfun1(X2,X3)
          | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
          | ~ v1_funct_1(X3)
          | ~ v1_relat_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( v1_funct_1(X3)
            & v1_relat_1(X3) )
         => ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
           => r1_partfun1(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t165_funct_2.p',t171_partfun1)).
%------------------------------------------------------------------------------
