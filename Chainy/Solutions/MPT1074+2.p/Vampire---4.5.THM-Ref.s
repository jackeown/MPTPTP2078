%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1074+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:05 EST 2020

% Result     : Theorem 48.59s
% Output     : Refutation 48.59s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 225 expanded)
%              Number of leaves         :   11 (  82 expanded)
%              Depth                    :   16
%              Number of atoms          :  259 (1659 expanded)
%              Number of equality atoms :   18 (  36 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f44312,plain,(
    $false ),
    inference(subsumption_resolution,[],[f44175,f3213])).

fof(f3213,plain,(
    ~ r2_hidden(sK24(k2_relat_1(sK22),sK19),sK19) ),
    inference(forward_demodulation,[],[f3186,f3059])).

fof(f3059,plain,(
    k2_relset_1(sK20,sK21,sK22) = k2_relat_1(sK22) ),
    inference(resolution,[],[f2258,f2298])).

fof(f2298,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f1712])).

fof(f1712,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1228])).

fof(f1228,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f2258,plain,(
    m1_subset_1(sK22,k1_zfmisc_1(k2_zfmisc_1(sK20,sK21))) ),
    inference(cnf_transformation,[],[f1987])).

fof(f1987,plain,
    ( ~ r1_tarski(k2_relset_1(sK20,sK21,sK22),sK19)
    & ! [X4] :
        ( r2_hidden(k3_funct_2(sK20,sK21,sK22,X4),sK19)
        | ~ m1_subset_1(X4,sK20) )
    & m1_subset_1(sK22,k1_zfmisc_1(k2_zfmisc_1(sK20,sK21)))
    & v1_funct_2(sK22,sK20,sK21)
    & v1_funct_1(sK22)
    & ~ v1_xboole_0(sK21)
    & ~ v1_xboole_0(sK20) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK19,sK20,sK21,sK22])],[f1688,f1986,f1985,f1984])).

fof(f1984,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ r1_tarski(k2_relset_1(X1,X2,X3),X0)
                & ! [X4] :
                    ( r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)
                    | ~ m1_subset_1(X4,X1) )
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                & v1_funct_2(X3,X1,X2)
                & v1_funct_1(X3) )
            & ~ v1_xboole_0(X2) )
        & ~ v1_xboole_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(k2_relset_1(sK20,X2,X3),sK19)
              & ! [X4] :
                  ( r2_hidden(k3_funct_2(sK20,X2,X3,X4),sK19)
                  | ~ m1_subset_1(X4,sK20) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK20,X2)))
              & v1_funct_2(X3,sK20,X2)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X2) )
      & ~ v1_xboole_0(sK20) ) ),
    introduced(choice_axiom,[])).

fof(f1985,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ r1_tarski(k2_relset_1(sK20,X2,X3),sK19)
            & ! [X4] :
                ( r2_hidden(k3_funct_2(sK20,X2,X3,X4),sK19)
                | ~ m1_subset_1(X4,sK20) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK20,X2)))
            & v1_funct_2(X3,sK20,X2)
            & v1_funct_1(X3) )
        & ~ v1_xboole_0(X2) )
   => ( ? [X3] :
          ( ~ r1_tarski(k2_relset_1(sK20,sK21,X3),sK19)
          & ! [X4] :
              ( r2_hidden(k3_funct_2(sK20,sK21,X3,X4),sK19)
              | ~ m1_subset_1(X4,sK20) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK20,sK21)))
          & v1_funct_2(X3,sK20,sK21)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(sK21) ) ),
    introduced(choice_axiom,[])).

fof(f1986,plain,
    ( ? [X3] :
        ( ~ r1_tarski(k2_relset_1(sK20,sK21,X3),sK19)
        & ! [X4] :
            ( r2_hidden(k3_funct_2(sK20,sK21,X3,X4),sK19)
            | ~ m1_subset_1(X4,sK20) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK20,sK21)))
        & v1_funct_2(X3,sK20,sK21)
        & v1_funct_1(X3) )
   => ( ~ r1_tarski(k2_relset_1(sK20,sK21,sK22),sK19)
      & ! [X4] :
          ( r2_hidden(k3_funct_2(sK20,sK21,sK22,X4),sK19)
          | ~ m1_subset_1(X4,sK20) )
      & m1_subset_1(sK22,k1_zfmisc_1(k2_zfmisc_1(sK20,sK21)))
      & v1_funct_2(sK22,sK20,sK21)
      & v1_funct_1(sK22) ) ),
    introduced(choice_axiom,[])).

fof(f1688,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(k2_relset_1(X1,X2,X3),X0)
              & ! [X4] :
                  ( r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)
                  | ~ m1_subset_1(X4,X1) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X3,X1,X2)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X2) )
      & ~ v1_xboole_0(X1) ) ),
    inference(flattening,[],[f1687])).

fof(f1687,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(k2_relset_1(X1,X2,X3),X0)
              & ! [X4] :
                  ( r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)
                  | ~ m1_subset_1(X4,X1) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X3,X1,X2)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X2) )
      & ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f1620])).

fof(f1620,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( ~ v1_xboole_0(X2)
           => ! [X3] :
                ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  & v1_funct_2(X3,X1,X2)
                  & v1_funct_1(X3) )
               => ( ! [X4] :
                      ( m1_subset_1(X4,X1)
                     => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) )
                 => r1_tarski(k2_relset_1(X1,X2,X3),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f1619])).

fof(f1619,conjecture,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                & v1_funct_2(X3,X1,X2)
                & v1_funct_1(X3) )
             => ( ! [X4] :
                    ( m1_subset_1(X4,X1)
                   => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) )
               => r1_tarski(k2_relset_1(X1,X2,X3),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t191_funct_2)).

fof(f3186,plain,(
    ~ r2_hidden(sK24(k2_relset_1(sK20,sK21,sK22),sK19),sK19) ),
    inference(resolution,[],[f2260,f2271])).

fof(f2271,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK24(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f1996])).

fof(f1996,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK24(X0,X1),X1)
          & r2_hidden(sK24(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK24])],[f1994,f1995])).

fof(f1995,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK24(X0,X1),X1)
        & r2_hidden(sK24(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1994,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f1993])).

fof(f1993,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1692])).

fof(f1692,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f2260,plain,(
    ~ r1_tarski(k2_relset_1(sK20,sK21,sK22),sK19) ),
    inference(cnf_transformation,[],[f1987])).

fof(f44175,plain,(
    r2_hidden(sK24(k2_relat_1(sK22),sK19),sK19) ),
    inference(resolution,[],[f14734,f3212])).

fof(f3212,plain,(
    r2_hidden(sK24(k2_relat_1(sK22),sK19),k2_relat_1(sK22)) ),
    inference(forward_demodulation,[],[f3185,f3059])).

fof(f3185,plain,(
    r2_hidden(sK24(k2_relset_1(sK20,sK21,sK22),sK19),k2_relset_1(sK20,sK21,sK22)) ),
    inference(resolution,[],[f2260,f2270])).

fof(f2270,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK24(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f1996])).

fof(f14734,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,k2_relat_1(sK22))
      | r2_hidden(X5,sK19) ) ),
    inference(subsumption_resolution,[],[f14733,f9736])).

fof(f9736,plain,(
    ! [X16] :
      ( ~ r2_hidden(X16,k2_relat_1(sK22))
      | m1_subset_1(sK27(sK20,X16,sK22),sK20) ) ),
    inference(forward_demodulation,[],[f9645,f3059])).

fof(f9645,plain,(
    ! [X16] :
      ( ~ r2_hidden(X16,k2_relset_1(sK20,sK21,sK22))
      | m1_subset_1(sK27(sK20,X16,sK22),sK20) ) ),
    inference(resolution,[],[f3016,f2310])).

fof(f2310,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f1720])).

fof(f1720,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f591])).

fof(f591,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f3016,plain,(
    ! [X0] :
      ( r2_hidden(sK27(sK20,X0,sK22),sK20)
      | ~ r2_hidden(X0,k2_relset_1(sK20,sK21,sK22)) ) ),
    inference(subsumption_resolution,[],[f3015,f2256])).

fof(f2256,plain,(
    v1_funct_1(sK22) ),
    inference(cnf_transformation,[],[f1987])).

fof(f3015,plain,(
    ! [X0] :
      ( r2_hidden(sK27(sK20,X0,sK22),sK20)
      | ~ r2_hidden(X0,k2_relset_1(sK20,sK21,sK22))
      | ~ v1_funct_1(sK22) ) ),
    inference(subsumption_resolution,[],[f3001,f2258])).

fof(f3001,plain,(
    ! [X0] :
      ( r2_hidden(sK27(sK20,X0,sK22),sK20)
      | ~ r2_hidden(X0,k2_relset_1(sK20,sK21,sK22))
      | ~ m1_subset_1(sK22,k1_zfmisc_1(k2_zfmisc_1(sK20,sK21)))
      | ~ v1_funct_1(sK22) ) ),
    inference(resolution,[],[f2257,f2281])).

fof(f2281,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK27(X0,X2,X3),X0)
      | ~ r2_hidden(X2,k2_relset_1(X0,X1,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f2004])).

fof(f2004,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_funct_1(X3,sK27(X0,X2,X3)) = X2
        & r2_hidden(sK27(X0,X2,X3),X0) )
      | ~ r2_hidden(X2,k2_relset_1(X0,X1,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK27])],[f1699,f2003])).

fof(f2003,plain,(
    ! [X3,X2,X0] :
      ( ? [X4] :
          ( k1_funct_1(X3,X4) = X2
          & r2_hidden(X4,X0) )
     => ( k1_funct_1(X3,sK27(X0,X2,X3)) = X2
        & r2_hidden(sK27(X0,X2,X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1699,plain,(
    ! [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k1_funct_1(X3,X4) = X2
          & r2_hidden(X4,X0) )
      | ~ r2_hidden(X2,k2_relset_1(X0,X1,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f1698])).

fof(f1698,plain,(
    ! [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k1_funct_1(X3,X4) = X2
          & r2_hidden(X4,X0) )
      | ~ r2_hidden(X2,k2_relset_1(X0,X1,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f1606])).

fof(f1606,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ~ ( ! [X4] :
              ~ ( k1_funct_1(X3,X4) = X2
                & r2_hidden(X4,X0) )
          & r2_hidden(X2,k2_relset_1(X0,X1,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_funct_2)).

fof(f2257,plain,(
    v1_funct_2(sK22,sK20,sK21) ),
    inference(cnf_transformation,[],[f1987])).

fof(f14733,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,k2_relat_1(sK22))
      | r2_hidden(X5,sK19)
      | ~ m1_subset_1(sK27(sK20,X5,sK22),sK20) ) ),
    inference(forward_demodulation,[],[f14675,f3059])).

fof(f14675,plain,(
    ! [X5] :
      ( r2_hidden(X5,sK19)
      | ~ m1_subset_1(sK27(sK20,X5,sK22),sK20)
      | ~ r2_hidden(X5,k2_relset_1(sK20,sK21,sK22)) ) ),
    inference(superposition,[],[f3356,f3018])).

fof(f3018,plain,(
    ! [X1] :
      ( k1_funct_1(sK22,sK27(sK20,X1,sK22)) = X1
      | ~ r2_hidden(X1,k2_relset_1(sK20,sK21,sK22)) ) ),
    inference(subsumption_resolution,[],[f3017,f2256])).

fof(f3017,plain,(
    ! [X1] :
      ( k1_funct_1(sK22,sK27(sK20,X1,sK22)) = X1
      | ~ r2_hidden(X1,k2_relset_1(sK20,sK21,sK22))
      | ~ v1_funct_1(sK22) ) ),
    inference(subsumption_resolution,[],[f3002,f2258])).

fof(f3002,plain,(
    ! [X1] :
      ( k1_funct_1(sK22,sK27(sK20,X1,sK22)) = X1
      | ~ r2_hidden(X1,k2_relset_1(sK20,sK21,sK22))
      | ~ m1_subset_1(sK22,k1_zfmisc_1(k2_zfmisc_1(sK20,sK21)))
      | ~ v1_funct_1(sK22) ) ),
    inference(resolution,[],[f2257,f2282])).

fof(f2282,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(X3,sK27(X0,X2,X3)) = X2
      | ~ r2_hidden(X2,k2_relset_1(X0,X1,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f2004])).

fof(f3356,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK22,X0),sK19)
      | ~ m1_subset_1(X0,sK20) ) ),
    inference(subsumption_resolution,[],[f3355,f2254])).

fof(f2254,plain,(
    ~ v1_xboole_0(sK20) ),
    inference(cnf_transformation,[],[f1987])).

fof(f3355,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK22,X0),sK19)
      | ~ m1_subset_1(X0,sK20)
      | v1_xboole_0(sK20) ) ),
    inference(subsumption_resolution,[],[f3354,f2256])).

fof(f3354,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK22,X0),sK19)
      | ~ m1_subset_1(X0,sK20)
      | ~ v1_funct_1(sK22)
      | v1_xboole_0(sK20) ) ),
    inference(subsumption_resolution,[],[f3353,f2257])).

fof(f3353,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK22,X0),sK19)
      | ~ m1_subset_1(X0,sK20)
      | ~ v1_funct_2(sK22,sK20,sK21)
      | ~ v1_funct_1(sK22)
      | v1_xboole_0(sK20) ) ),
    inference(subsumption_resolution,[],[f3349,f2258])).

fof(f3349,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK22,X0),sK19)
      | ~ m1_subset_1(X0,sK20)
      | ~ m1_subset_1(sK22,k1_zfmisc_1(k2_zfmisc_1(sK20,sK21)))
      | ~ v1_funct_2(sK22,sK20,sK21)
      | ~ v1_funct_1(sK22)
      | v1_xboole_0(sK20) ) ),
    inference(duplicate_literal_removal,[],[f3348])).

fof(f3348,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK22,X0),sK19)
      | ~ m1_subset_1(X0,sK20)
      | ~ m1_subset_1(X0,sK20)
      | ~ m1_subset_1(sK22,k1_zfmisc_1(k2_zfmisc_1(sK20,sK21)))
      | ~ v1_funct_2(sK22,sK20,sK21)
      | ~ v1_funct_1(sK22)
      | v1_xboole_0(sK20) ) ),
    inference(superposition,[],[f2259,f2312])).

fof(f2312,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1723])).

fof(f1723,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f1722])).

fof(f1722,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1540])).

fof(f1540,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(f2259,plain,(
    ! [X4] :
      ( r2_hidden(k3_funct_2(sK20,sK21,sK22,X4),sK19)
      | ~ m1_subset_1(X4,sK20) ) ),
    inference(cnf_transformation,[],[f1987])).
%------------------------------------------------------------------------------
