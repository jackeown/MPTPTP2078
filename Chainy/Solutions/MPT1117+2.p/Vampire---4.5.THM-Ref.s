%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1117+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:07 EST 2020

% Result     : Theorem 2.86s
% Output     : Refutation 2.86s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 176 expanded)
%              Number of leaves         :    8 (  55 expanded)
%              Depth                    :   12
%              Number of atoms          :  177 ( 701 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3656,plain,(
    $false ),
    inference(global_subsumption,[],[f2138,f2880,f3655])).

fof(f3655,plain,(
    r2_hidden(sK3(sK1,k2_pre_topc(sK0,sK1)),sK6(sK0,sK1,sK3(sK1,k2_pre_topc(sK0,sK1)))) ),
    inference(subsumption_resolution,[],[f3645,f2880])).

fof(f3645,plain,
    ( ~ r2_hidden(sK3(sK1,k2_pre_topc(sK0,sK1)),u1_struct_0(sK0))
    | r2_hidden(sK3(sK1,k2_pre_topc(sK0,sK1)),sK6(sK0,sK1,sK3(sK1,k2_pre_topc(sK0,sK1)))) ),
    inference(resolution,[],[f2136,f2087])).

fof(f2087,plain,(
    ! [X2] :
      ( ~ r1_tarski(sK1,X2)
      | r2_hidden(sK3(sK1,k2_pre_topc(sK0,sK1)),X2) ) ),
    inference(resolution,[],[f1993,f1908])).

fof(f1908,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1872])).

fof(f1872,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f1870,f1871])).

fof(f1871,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1870,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f1869])).

fof(f1869,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1839])).

fof(f1839,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f1993,plain,(
    r2_hidden(sK3(sK1,k2_pre_topc(sK0,sK1)),sK1) ),
    inference(resolution,[],[f1899,f1909])).

fof(f1909,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f1872])).

fof(f1899,plain,(
    ~ r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    inference(cnf_transformation,[],[f1863])).

fof(f1863,plain,
    ( ~ r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f1835,f1862,f1861])).

fof(f1861,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(X1,k2_pre_topc(X0,X1))
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(X1,k2_pre_topc(sK0,X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f1862,plain,
    ( ? [X1] :
        ( ~ r1_tarski(X1,k2_pre_topc(sK0,X1))
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ r1_tarski(sK1,k2_pre_topc(sK0,sK1))
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f1835,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X1,k2_pre_topc(X0,X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1831])).

fof(f1831,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f1830])).

fof(f1830,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

fof(f2136,plain,
    ( r1_tarski(sK1,sK6(sK0,sK1,sK3(sK1,k2_pre_topc(sK0,sK1))))
    | ~ r2_hidden(sK3(sK1,k2_pre_topc(sK0,sK1)),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f2135,f1897])).

fof(f1897,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f1863])).

fof(f2135,plain,
    ( r1_tarski(sK1,sK6(sK0,sK1,sK3(sK1,k2_pre_topc(sK0,sK1))))
    | ~ r2_hidden(sK3(sK1,k2_pre_topc(sK0,sK1)),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f2126,f1898])).

fof(f1898,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f1863])).

fof(f2126,plain,
    ( r1_tarski(sK1,sK6(sK0,sK1,sK3(sK1,k2_pre_topc(sK0,sK1))))
    | ~ r2_hidden(sK3(sK1,k2_pre_topc(sK0,sK1)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f1994,f1925])).

fof(f1925,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k2_pre_topc(X0,X1))
      | r1_tarski(X1,sK6(X0,X1,X2))
      | ~ r2_hidden(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f1882])).

fof(f1882,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ( ~ r2_hidden(X2,sK6(X0,X1,X2))
                    & r1_tarski(X1,sK6(X0,X1,X2))
                    & v4_pre_topc(sK6(X0,X1,X2),X0)
                    & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( r2_hidden(X2,X4)
                      | ~ r1_tarski(X1,X4)
                      | ~ v4_pre_topc(X4,X0)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ r2_hidden(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f1880,f1881])).

fof(f1881,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X2,X3)
          & r1_tarski(X1,X3)
          & v4_pre_topc(X3,X0)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r2_hidden(X2,sK6(X0,X1,X2))
        & r1_tarski(X1,sK6(X0,X1,X2))
        & v4_pre_topc(sK6(X0,X1,X2),X0)
        & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f1880,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r1_tarski(X1,X3)
                      & v4_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( r2_hidden(X2,X4)
                      | ~ r1_tarski(X1,X4)
                      | ~ v4_pre_topc(X4,X0)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ r2_hidden(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f1879])).

fof(f1879,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r1_tarski(X1,X3)
                      & v4_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X3] :
                      ( r2_hidden(X2,X3)
                      | ~ r1_tarski(X1,X3)
                      | ~ v4_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ r2_hidden(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f1850])).

fof(f1850,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ! [X3] :
                    ( r2_hidden(X2,X3)
                    | ~ r1_tarski(X1,X3)
                    | ~ v4_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ r2_hidden(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f1849])).

fof(f1849,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ! [X3] :
                    ( r2_hidden(X2,X3)
                    | ~ r1_tarski(X1,X3)
                    | ~ v4_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ r2_hidden(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1827])).

fof(f1827,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( r2_hidden(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( ( r1_tarski(X1,X3)
                        & v4_pre_topc(X3,X0) )
                     => r2_hidden(X2,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_pre_topc)).

fof(f1994,plain,(
    ~ r2_hidden(sK3(sK1,k2_pre_topc(sK0,sK1)),k2_pre_topc(sK0,sK1)) ),
    inference(resolution,[],[f1899,f1910])).

fof(f1910,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f1872])).

fof(f2880,plain,(
    r2_hidden(sK3(sK1,k2_pre_topc(sK0,sK1)),u1_struct_0(sK0)) ),
    inference(resolution,[],[f2087,f1971])).

fof(f1971,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f1898,f1902])).

fof(f1902,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f1864])).

fof(f1864,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f609])).

fof(f609,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f2138,plain,
    ( ~ r2_hidden(sK3(sK1,k2_pre_topc(sK0,sK1)),sK6(sK0,sK1,sK3(sK1,k2_pre_topc(sK0,sK1))))
    | ~ r2_hidden(sK3(sK1,k2_pre_topc(sK0,sK1)),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f2137,f1897])).

fof(f2137,plain,
    ( ~ r2_hidden(sK3(sK1,k2_pre_topc(sK0,sK1)),sK6(sK0,sK1,sK3(sK1,k2_pre_topc(sK0,sK1))))
    | ~ r2_hidden(sK3(sK1,k2_pre_topc(sK0,sK1)),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f2127,f1898])).

fof(f2127,plain,
    ( ~ r2_hidden(sK3(sK1,k2_pre_topc(sK0,sK1)),sK6(sK0,sK1,sK3(sK1,k2_pre_topc(sK0,sK1))))
    | ~ r2_hidden(sK3(sK1,k2_pre_topc(sK0,sK1)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f1994,f1926])).

fof(f1926,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ r2_hidden(X2,sK6(X0,X1,X2))
      | ~ r2_hidden(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f1882])).
%------------------------------------------------------------------------------
