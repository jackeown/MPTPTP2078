%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:54 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 168 expanded)
%              Number of leaves         :   13 (  69 expanded)
%              Depth                    :   20
%              Number of atoms          :  215 (1101 expanded)
%              Number of equality atoms :   15 (  15 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f188,plain,(
    $false ),
    inference(subsumption_resolution,[],[f176,f76])).

fof(f76,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f74,f48])).

fof(f48,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f2,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f2,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f74,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_xboole_0)
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[],[f49,f67])).

fof(f67,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f63,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f63,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f53,f46])).

fof(f46,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f176,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(backward_demodulation,[],[f40,f175])).

fof(f175,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f174,f41])).

fof(f41,plain,(
    m1_subset_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( ~ r2_hidden(k3_funct_2(sK0,sK1,sK3,sK2),k2_relset_1(sK0,sK1,sK3))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,sK0)
    & ~ v1_xboole_0(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f33,f32,f31,f30])).

fof(f30,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3))
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                    & v1_funct_2(X3,X0,X1)
                    & v1_funct_1(X3) )
                & m1_subset_1(X2,X0) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k3_funct_2(sK0,X1,X3,X2),k2_relset_1(sK0,X1,X3))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
                  & v1_funct_2(X3,sK0,X1)
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,sK0) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ r2_hidden(k3_funct_2(sK0,X1,X3,X2),k2_relset_1(sK0,X1,X3))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
                & v1_funct_2(X3,sK0,X1)
                & v1_funct_1(X3) )
            & m1_subset_1(X2,sK0) )
        & ~ v1_xboole_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(k3_funct_2(sK0,sK1,X3,X2),k2_relset_1(sK0,sK1,X3))
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
              & v1_funct_2(X3,sK0,sK1)
              & v1_funct_1(X3) )
          & m1_subset_1(X2,sK0) )
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

% (29668)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
fof(f32,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ r2_hidden(k3_funct_2(sK0,sK1,X3,X2),k2_relset_1(sK0,sK1,X3))
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
            & v1_funct_2(X3,sK0,sK1)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,sK0) )
   => ( ? [X3] :
          ( ~ r2_hidden(k3_funct_2(sK0,sK1,X3,sK2),k2_relset_1(sK0,sK1,X3))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
          & v1_funct_2(X3,sK0,sK1)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X3] :
        ( ~ r2_hidden(k3_funct_2(sK0,sK1,X3,sK2),k2_relset_1(sK0,sK1,X3))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        & v1_funct_2(X3,sK0,sK1)
        & v1_funct_1(X3) )
   => ( ~ r2_hidden(k3_funct_2(sK0,sK1,sK3,sK2),k2_relset_1(sK0,sK1,sK3))
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_2(X3,X0,X1)
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,X0) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_2(X3,X0,X1)
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,X0) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( m1_subset_1(X2,X0)
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      & v1_funct_2(X3,X0,X1)
                      & v1_funct_1(X3) )
                   => r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3)) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,X0)
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                    & v1_funct_2(X3,X0,X1)
                    & v1_funct_1(X3) )
                 => r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t189_funct_2)).

fof(f174,plain,
    ( k1_xboole_0 = sK1
    | ~ m1_subset_1(sK2,sK0) ),
    inference(subsumption_resolution,[],[f173,f39])).

fof(f39,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f173,plain,
    ( k1_xboole_0 = sK1
    | v1_xboole_0(sK0)
    | ~ m1_subset_1(sK2,sK0) ),
    inference(resolution,[],[f172,f49])).

fof(f172,plain,
    ( ~ r2_hidden(sK2,sK0)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f171,f42])).

fof(f42,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f171,plain,
    ( k1_xboole_0 = sK1
    | ~ r2_hidden(sK2,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f170,f43])).

fof(f43,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f170,plain,
    ( k1_xboole_0 = sK1
    | ~ r2_hidden(sK2,sK0)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f169,f44])).

fof(f44,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f34])).

fof(f169,plain,
    ( k1_xboole_0 = sK1
    | ~ r2_hidden(sK2,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f60,f147])).

fof(f147,plain,(
    ~ r2_hidden(k1_funct_1(sK3,sK2),k2_relset_1(sK0,sK1,sK3)) ),
    inference(subsumption_resolution,[],[f146,f39])).

fof(f146,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK2),k2_relset_1(sK0,sK1,sK3))
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f145,f42])).

fof(f145,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK2),k2_relset_1(sK0,sK1,sK3))
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f144,f43])).

fof(f144,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK2),k2_relset_1(sK0,sK1,sK3))
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f143,f44])).

fof(f143,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK2),k2_relset_1(sK0,sK1,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f137,f41])).

fof(f137,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK2),k2_relset_1(sK0,sK1,sK3))
    | ~ m1_subset_1(sK2,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK0) ),
    inference(superposition,[],[f45,f59])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(f45,plain,(
    ~ r2_hidden(k3_funct_2(sK0,sK1,sK3,sK2),k2_relset_1(sK0,sK1,sK3)) ),
    inference(cnf_transformation,[],[f34])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).

fof(f40,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:55:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (29658)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.48  % (29671)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.50  % (29671)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f188,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(subsumption_resolution,[],[f176,f76])).
% 0.22/0.50  fof(f76,plain,(
% 0.22/0.50    v1_xboole_0(k1_xboole_0)),
% 0.22/0.50    inference(resolution,[],[f74,f48])).
% 0.22/0.50  fof(f48,plain,(
% 0.22/0.50    ( ! [X0] : (m1_subset_1(sK4(X0),X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f36])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    ! [X0] : m1_subset_1(sK4(X0),X0)),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f2,f35])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ! [X0] : (? [X1] : m1_subset_1(X1,X0) => m1_subset_1(sK4(X0),X0))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).
% 0.22/0.50  fof(f74,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_xboole_0) | v1_xboole_0(k1_xboole_0)) )),
% 0.22/0.50    inference(resolution,[],[f49,f67])).
% 0.22/0.50  fof(f67,plain,(
% 0.22/0.50    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.22/0.50    inference(resolution,[],[f63,f57])).
% 0.22/0.50  fof(f57,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,axiom,(
% 0.22/0.50    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.22/0.50  fof(f63,plain,(
% 0.22/0.50    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.50    inference(resolution,[],[f53,f46])).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.22/0.50  fof(f53,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f22])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.22/0.50    inference(ennf_transformation,[],[f14])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 0.22/0.50    inference(unused_predicate_definition_removal,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.50  fof(f49,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.22/0.50    inference(flattening,[],[f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.22/0.50  fof(f176,plain,(
% 0.22/0.50    ~v1_xboole_0(k1_xboole_0)),
% 0.22/0.50    inference(backward_demodulation,[],[f40,f175])).
% 0.22/0.50  fof(f175,plain,(
% 0.22/0.50    k1_xboole_0 = sK1),
% 0.22/0.50    inference(subsumption_resolution,[],[f174,f41])).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    m1_subset_1(sK2,sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f34])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    (((~r2_hidden(k3_funct_2(sK0,sK1,sK3,sK2),k2_relset_1(sK0,sK1,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)) & m1_subset_1(sK2,sK0)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f33,f32,f31,f30])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,X0)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~r2_hidden(k3_funct_2(sK0,X1,X3,X2),k2_relset_1(sK0,X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) & v1_funct_2(X3,sK0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,sK0)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ? [X1] : (? [X2] : (? [X3] : (~r2_hidden(k3_funct_2(sK0,X1,X3,X2),k2_relset_1(sK0,X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) & v1_funct_2(X3,sK0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,sK0)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (~r2_hidden(k3_funct_2(sK0,sK1,X3,X2),k2_relset_1(sK0,sK1,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X3,sK0,sK1) & v1_funct_1(X3)) & m1_subset_1(X2,sK0)) & ~v1_xboole_0(sK1))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.51  % (29668)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    ? [X2] : (? [X3] : (~r2_hidden(k3_funct_2(sK0,sK1,X3,X2),k2_relset_1(sK0,sK1,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X3,sK0,sK1) & v1_funct_1(X3)) & m1_subset_1(X2,sK0)) => (? [X3] : (~r2_hidden(k3_funct_2(sK0,sK1,X3,sK2),k2_relset_1(sK0,sK1,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X3,sK0,sK1) & v1_funct_1(X3)) & m1_subset_1(sK2,sK0))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    ? [X3] : (~r2_hidden(k3_funct_2(sK0,sK1,X3,sK2),k2_relset_1(sK0,sK1,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X3,sK0,sK1) & v1_funct_1(X3)) => (~r2_hidden(k3_funct_2(sK0,sK1,sK3,sK2),k2_relset_1(sK0,sK1,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,X0)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.22/0.51    inference(flattening,[],[f15])).
% 0.22/0.51  fof(f15,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & m1_subset_1(X2,X0)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f13])).
% 0.22/0.51  fof(f13,negated_conjecture,(
% 0.22/0.51    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3))))))),
% 0.22/0.51    inference(negated_conjecture,[],[f12])).
% 0.22/0.51  fof(f12,conjecture,(
% 0.22/0.51    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3))))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t189_funct_2)).
% 0.22/0.51  fof(f174,plain,(
% 0.22/0.51    k1_xboole_0 = sK1 | ~m1_subset_1(sK2,sK0)),
% 0.22/0.51    inference(subsumption_resolution,[],[f173,f39])).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    ~v1_xboole_0(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f34])).
% 0.22/0.51  fof(f173,plain,(
% 0.22/0.51    k1_xboole_0 = sK1 | v1_xboole_0(sK0) | ~m1_subset_1(sK2,sK0)),
% 0.22/0.51    inference(resolution,[],[f172,f49])).
% 0.22/0.51  fof(f172,plain,(
% 0.22/0.51    ~r2_hidden(sK2,sK0) | k1_xboole_0 = sK1),
% 0.22/0.51    inference(subsumption_resolution,[],[f171,f42])).
% 0.22/0.51  fof(f42,plain,(
% 0.22/0.51    v1_funct_1(sK3)),
% 0.22/0.51    inference(cnf_transformation,[],[f34])).
% 0.22/0.51  fof(f171,plain,(
% 0.22/0.51    k1_xboole_0 = sK1 | ~r2_hidden(sK2,sK0) | ~v1_funct_1(sK3)),
% 0.22/0.51    inference(subsumption_resolution,[],[f170,f43])).
% 0.22/0.51  fof(f43,plain,(
% 0.22/0.51    v1_funct_2(sK3,sK0,sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f34])).
% 0.22/0.51  fof(f170,plain,(
% 0.22/0.51    k1_xboole_0 = sK1 | ~r2_hidden(sK2,sK0) | ~v1_funct_2(sK3,sK0,sK1) | ~v1_funct_1(sK3)),
% 0.22/0.51    inference(subsumption_resolution,[],[f169,f44])).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.51    inference(cnf_transformation,[],[f34])).
% 0.22/0.51  fof(f169,plain,(
% 0.22/0.51    k1_xboole_0 = sK1 | ~r2_hidden(sK2,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK3,sK0,sK1) | ~v1_funct_1(sK3)),
% 0.22/0.51    inference(resolution,[],[f60,f147])).
% 0.22/0.51  fof(f147,plain,(
% 0.22/0.51    ~r2_hidden(k1_funct_1(sK3,sK2),k2_relset_1(sK0,sK1,sK3))),
% 0.22/0.51    inference(subsumption_resolution,[],[f146,f39])).
% 0.22/0.51  fof(f146,plain,(
% 0.22/0.51    ~r2_hidden(k1_funct_1(sK3,sK2),k2_relset_1(sK0,sK1,sK3)) | v1_xboole_0(sK0)),
% 0.22/0.51    inference(subsumption_resolution,[],[f145,f42])).
% 0.22/0.51  fof(f145,plain,(
% 0.22/0.51    ~r2_hidden(k1_funct_1(sK3,sK2),k2_relset_1(sK0,sK1,sK3)) | ~v1_funct_1(sK3) | v1_xboole_0(sK0)),
% 0.22/0.51    inference(subsumption_resolution,[],[f144,f43])).
% 0.22/0.51  fof(f144,plain,(
% 0.22/0.51    ~r2_hidden(k1_funct_1(sK3,sK2),k2_relset_1(sK0,sK1,sK3)) | ~v1_funct_2(sK3,sK0,sK1) | ~v1_funct_1(sK3) | v1_xboole_0(sK0)),
% 0.22/0.51    inference(subsumption_resolution,[],[f143,f44])).
% 0.22/0.51  fof(f143,plain,(
% 0.22/0.51    ~r2_hidden(k1_funct_1(sK3,sK2),k2_relset_1(sK0,sK1,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK3,sK0,sK1) | ~v1_funct_1(sK3) | v1_xboole_0(sK0)),
% 0.22/0.51    inference(subsumption_resolution,[],[f137,f41])).
% 0.22/0.51  fof(f137,plain,(
% 0.22/0.51    ~r2_hidden(k1_funct_1(sK3,sK2),k2_relset_1(sK0,sK1,sK3)) | ~m1_subset_1(sK2,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK3,sK0,sK1) | ~v1_funct_1(sK3) | v1_xboole_0(sK0)),
% 0.22/0.51    inference(superposition,[],[f45,f59])).
% 0.22/0.51  fof(f59,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f27])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 0.22/0.51    inference(flattening,[],[f26])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f10])).
% 0.22/0.51  fof(f10,axiom,(
% 0.22/0.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).
% 0.22/0.51  fof(f45,plain,(
% 0.22/0.51    ~r2_hidden(k3_funct_2(sK0,sK1,sK3,sK2),k2_relset_1(sK0,sK1,sK3))),
% 0.22/0.51    inference(cnf_transformation,[],[f34])).
% 0.22/0.51  fof(f60,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f29])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.22/0.51    inference(flattening,[],[f28])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.22/0.51    inference(ennf_transformation,[],[f11])).
% 0.22/0.51  fof(f11,axiom,(
% 0.22/0.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    ~v1_xboole_0(sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f34])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (29671)------------------------------
% 0.22/0.51  % (29671)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (29671)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (29671)Memory used [KB]: 1791
% 0.22/0.51  % (29671)Time elapsed: 0.077 s
% 0.22/0.51  % (29671)------------------------------
% 0.22/0.51  % (29671)------------------------------
% 0.22/0.51  % (29650)Success in time 0.153 s
%------------------------------------------------------------------------------
