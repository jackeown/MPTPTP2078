%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:11:37 EST 2020

% Result     : Theorem 11.86s
% Output     : CNFRefutation 11.86s
% Verified   : 
% Statistics : Number of formulae       :  213 (1582 expanded)
%              Number of clauses        :  121 ( 616 expanded)
%              Number of leaves         :   25 ( 338 expanded)
%              Depth                    :   22
%              Number of atoms          :  779 (6680 expanded)
%              Number of equality atoms :  315 (2090 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f67,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
                & v2_pre_topc(X0) )
             => v3_pre_topc(X1,X0) )
            & ( v3_pre_topc(X1,X0)
             => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ( ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
                  & v2_pre_topc(X0) )
               => v3_pre_topc(X1,X0) )
              & ( v3_pre_topc(X1,X0)
               => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f67])).

fof(f150,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( ~ v3_pre_topc(X1,X0)
              & k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
              & v2_pre_topc(X0) )
            | ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
              & v3_pre_topc(X1,X0) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f68])).

fof(f151,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( ~ v3_pre_topc(X1,X0)
              & k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
              & v2_pre_topc(X0) )
            | ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
              & v3_pre_topc(X1,X0) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f150])).

fof(f213,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ( ~ v3_pre_topc(X1,X0)
              & k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
              & v2_pre_topc(X0) )
            | ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
              & v3_pre_topc(X1,X0) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ( ~ v3_pre_topc(sK21,X0)
            & k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),sK21) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),sK21))
            & v2_pre_topc(X0) )
          | ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),sK21) != k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),sK21))
            & v3_pre_topc(sK21,X0) ) )
        & m1_subset_1(sK21,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f212,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ( ~ v3_pre_topc(X1,X0)
                & k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
                & v2_pre_topc(X0) )
              | ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
                & v3_pre_topc(X1,X0) ) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ( ~ v3_pre_topc(X1,sK20)
              & k7_subset_1(u1_struct_0(sK20),k2_struct_0(sK20),X1) = k2_pre_topc(sK20,k7_subset_1(u1_struct_0(sK20),k2_struct_0(sK20),X1))
              & v2_pre_topc(sK20) )
            | ( k7_subset_1(u1_struct_0(sK20),k2_struct_0(sK20),X1) != k2_pre_topc(sK20,k7_subset_1(u1_struct_0(sK20),k2_struct_0(sK20),X1))
              & v3_pre_topc(X1,sK20) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK20))) )
      & l1_pre_topc(sK20) ) ),
    introduced(choice_axiom,[])).

fof(f214,plain,
    ( ( ( ~ v3_pre_topc(sK21,sK20)
        & k7_subset_1(u1_struct_0(sK20),k2_struct_0(sK20),sK21) = k2_pre_topc(sK20,k7_subset_1(u1_struct_0(sK20),k2_struct_0(sK20),sK21))
        & v2_pre_topc(sK20) )
      | ( k7_subset_1(u1_struct_0(sK20),k2_struct_0(sK20),sK21) != k2_pre_topc(sK20,k7_subset_1(u1_struct_0(sK20),k2_struct_0(sK20),sK21))
        & v3_pre_topc(sK21,sK20) ) )
    & m1_subset_1(sK21,k1_zfmisc_1(u1_struct_0(sK20)))
    & l1_pre_topc(sK20) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK20,sK21])],[f151,f213,f212])).

fof(f340,plain,(
    m1_subset_1(sK21,k1_zfmisc_1(u1_struct_0(sK20))) ),
    inference(cnf_transformation,[],[f214])).

fof(f29,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f171,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f257,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f171])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f237,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f258,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f171])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f238,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f65,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f146,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f65])).

fof(f147,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f146])).

fof(f336,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f147])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f158,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f159,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f158])).

fof(f217,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f159])).

fof(f353,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f217])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f81,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f244,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f85,plain,(
    ! [X0,X1] :
      ( k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f248,plain,(
    ! [X0,X1] :
      ( k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f85])).

fof(f12,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f236,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f47,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f119,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f47])).

fof(f309,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f119])).

fof(f60,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) = k2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f140,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) = k2_struct_0(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f60])).

fof(f330,plain,(
    ! [X0,X1] :
      ( k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) = k2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f140])).

fof(f339,plain,(
    l1_pre_topc(sK20) ),
    inference(cnf_transformation,[],[f214])).

fof(f346,plain,
    ( ~ v3_pre_topc(sK21,sK20)
    | k7_subset_1(u1_struct_0(sK20),k2_struct_0(sK20),sK21) != k2_pre_topc(sK20,k7_subset_1(u1_struct_0(sK20),k2_struct_0(sK20),sK21)) ),
    inference(cnf_transformation,[],[f214])).

fof(f61,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f141,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f61])).

fof(f331,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f141])).

fof(f43,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f113,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f43])).

fof(f193,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) )
            & ( v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f113])).

fof(f292,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f193])).

fof(f343,plain,
    ( k7_subset_1(u1_struct_0(sK20),k2_struct_0(sK20),sK21) = k2_pre_topc(sK20,k7_subset_1(u1_struct_0(sK20),k2_struct_0(sK20),sK21))
    | v3_pre_topc(sK21,sK20) ),
    inference(cnf_transformation,[],[f214])).

fof(f42,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f112,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f42])).

fof(f192,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f112])).

fof(f289,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,u1_pre_topc(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f192])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f161,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f228,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f161])).

fof(f46,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f117,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f46])).

fof(f118,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f117])).

fof(f308,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f118])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f163,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f73])).

fof(f235,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f163])).

fof(f40,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_pre_topc(X2) )
             => ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f108,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f40])).

fof(f109,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f108])).

fof(f181,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k1_pre_topc(X0,X1) = X2
                  | k2_struct_0(X2) != X1 )
                & ( k2_struct_0(X2) = X1
                  | k1_pre_topc(X0,X1) != X2 ) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f109])).

fof(f275,plain,(
    ! [X2,X0,X1] :
      ( k2_struct_0(X2) = X1
      | k1_pre_topc(X0,X1) != X2
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_pre_topc(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f181])).

fof(f357,plain,(
    ! [X0,X1] :
      ( k2_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f275])).

fof(f45,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f115,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f45])).

fof(f116,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f115])).

fof(f307,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f116])).

fof(f306,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f116])).

fof(f154,plain,(
    ! [X1,X0] :
      ( sP1(X1,X0)
    <=> ( ! [X2] :
            ( ( r2_hidden(X2,u1_pre_topc(X1))
            <=> ? [X3] :
                  ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                  & r2_hidden(X3,u1_pre_topc(X0))
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
        & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f195,plain,(
    ! [X1,X0] :
      ( ( sP1(X1,X0)
        | ? [X2] :
            ( ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                  | ~ r2_hidden(X3,u1_pre_topc(X0))
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X2,u1_pre_topc(X1)) )
            & ( ? [X3] :
                  ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                  & r2_hidden(X3,u1_pre_topc(X0))
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | r2_hidden(X2,u1_pre_topc(X1)) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
      & ( ( ! [X2] :
              ( ( ( r2_hidden(X2,u1_pre_topc(X1))
                  | ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ r2_hidden(X3,u1_pre_topc(X0))
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                      & r2_hidden(X3,u1_pre_topc(X0))
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X2,u1_pre_topc(X1)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
        | ~ sP1(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f154])).

fof(f196,plain,(
    ! [X1,X0] :
      ( ( sP1(X1,X0)
        | ? [X2] :
            ( ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                  | ~ r2_hidden(X3,u1_pre_topc(X0))
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X2,u1_pre_topc(X1)) )
            & ( ? [X3] :
                  ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                  & r2_hidden(X3,u1_pre_topc(X0))
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | r2_hidden(X2,u1_pre_topc(X1)) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
      & ( ( ! [X2] :
              ( ( ( r2_hidden(X2,u1_pre_topc(X1))
                  | ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ r2_hidden(X3,u1_pre_topc(X0))
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                      & r2_hidden(X3,u1_pre_topc(X0))
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X2,u1_pre_topc(X1)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
        | ~ sP1(X1,X0) ) ) ),
    inference(flattening,[],[f195])).

fof(f197,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ? [X2] :
            ( ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != X2
                  | ~ r2_hidden(X3,u1_pre_topc(X1))
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ r2_hidden(X2,u1_pre_topc(X0)) )
            & ( ? [X4] :
                  ( k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2
                  & r2_hidden(X4,u1_pre_topc(X1))
                  & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
              | r2_hidden(X2,u1_pre_topc(X0)) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) )
      & ( ( ! [X5] :
              ( ( ( r2_hidden(X5,u1_pre_topc(X0))
                  | ! [X6] :
                      ( k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5
                      | ~ r2_hidden(X6,u1_pre_topc(X1))
                      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ? [X7] :
                      ( k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5
                      & r2_hidden(X7,u1_pre_topc(X1))
                      & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ r2_hidden(X5,u1_pre_topc(X0)) ) )
              | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
          & r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) )
        | ~ sP1(X0,X1) ) ) ),
    inference(rectify,[],[f196])).

fof(f200,plain,(
    ! [X5,X1,X0] :
      ( ? [X7] :
          ( k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5
          & r2_hidden(X7,u1_pre_topc(X1))
          & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k9_subset_1(u1_struct_0(X0),sK14(X0,X1,X5),k2_struct_0(X0)) = X5
        & r2_hidden(sK14(X0,X1,X5),u1_pre_topc(X1))
        & m1_subset_1(sK14(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f199,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2
          & r2_hidden(X4,u1_pre_topc(X1))
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k9_subset_1(u1_struct_0(X0),sK13(X0,X1),k2_struct_0(X0)) = X2
        & r2_hidden(sK13(X0,X1),u1_pre_topc(X1))
        & m1_subset_1(sK13(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f198,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != X2
                | ~ r2_hidden(X3,u1_pre_topc(X1))
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            | ~ r2_hidden(X2,u1_pre_topc(X0)) )
          & ( ? [X4] :
                ( k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2
                & r2_hidden(X4,u1_pre_topc(X1))
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
            | r2_hidden(X2,u1_pre_topc(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK12(X0,X1)
              | ~ r2_hidden(X3,u1_pre_topc(X1))
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ r2_hidden(sK12(X0,X1),u1_pre_topc(X0)) )
        & ( ? [X4] :
              ( k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = sK12(X0,X1)
              & r2_hidden(X4,u1_pre_topc(X1))
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
          | r2_hidden(sK12(X0,X1),u1_pre_topc(X0)) )
        & m1_subset_1(sK12(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f201,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ( ( ! [X3] :
                ( k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK12(X0,X1)
                | ~ r2_hidden(X3,u1_pre_topc(X1))
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            | ~ r2_hidden(sK12(X0,X1),u1_pre_topc(X0)) )
          & ( ( k9_subset_1(u1_struct_0(X0),sK13(X0,X1),k2_struct_0(X0)) = sK12(X0,X1)
              & r2_hidden(sK13(X0,X1),u1_pre_topc(X1))
              & m1_subset_1(sK13(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) )
            | r2_hidden(sK12(X0,X1),u1_pre_topc(X0)) )
          & m1_subset_1(sK12(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) )
      & ( ( ! [X5] :
              ( ( ( r2_hidden(X5,u1_pre_topc(X0))
                  | ! [X6] :
                      ( k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5
                      | ~ r2_hidden(X6,u1_pre_topc(X1))
                      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ( k9_subset_1(u1_struct_0(X0),sK14(X0,X1,X5),k2_struct_0(X0)) = X5
                    & r2_hidden(sK14(X0,X1,X5),u1_pre_topc(X1))
                    & m1_subset_1(sK14(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ r2_hidden(X5,u1_pre_topc(X0)) ) )
              | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
          & r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) )
        | ~ sP1(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12,sK13,sK14])],[f197,f200,f199,f198])).

fof(f299,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,u1_pre_topc(X0))
      | k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5
      | ~ r2_hidden(X6,u1_pre_topc(X1))
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f201])).

fof(f358,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)),u1_pre_topc(X0))
      | ~ r2_hidden(X6,u1_pre_topc(X1))
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP1(X0,X1) ) ),
    inference(equality_resolution,[],[f299])).

fof(f337,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f147])).

fof(f341,plain,
    ( v2_pre_topc(sK20)
    | v3_pre_topc(sK21,sK20) ),
    inference(cnf_transformation,[],[f214])).

fof(f291,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f193])).

fof(f227,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f161])).

fof(f290,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f192])).

cnf(c_129,negated_conjecture,
    ( m1_subset_1(sK21,k1_zfmisc_1(u1_struct_0(sK20))) ),
    inference(cnf_transformation,[],[f340])).

cnf(c_10102,plain,
    ( m1_subset_1(sK21,k1_zfmisc_1(u1_struct_0(sK20))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_129])).

cnf(c_42,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f257])).

cnf(c_10162,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_12185,plain,
    ( r1_tarski(sK21,u1_struct_0(sK20)) = iProver_top ),
    inference(superposition,[status(thm)],[c_10102,c_10162])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f237])).

cnf(c_41,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f258])).

cnf(c_1068,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_41])).

cnf(c_1069,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_1068])).

cnf(c_1273,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_21,c_1069])).

cnf(c_10099,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1273])).

cnf(c_13374,plain,
    ( k3_subset_1(u1_struct_0(sK20),sK21) = k4_xboole_0(u1_struct_0(sK20),sK21) ),
    inference(superposition,[status(thm)],[c_12185,c_10099])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f238])).

cnf(c_1274,plain,
    ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
    | ~ r1_tarski(X1,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_22,c_1069])).

cnf(c_10098,plain,
    ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) = iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1274])).

cnf(c_50792,plain,
    ( m1_subset_1(k4_xboole_0(u1_struct_0(sK20),sK21),k1_zfmisc_1(u1_struct_0(sK20))) = iProver_top
    | r1_tarski(sK21,u1_struct_0(sK20)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13374,c_10098])).

cnf(c_51100,plain,
    ( m1_subset_1(k4_xboole_0(u1_struct_0(sK20),sK21),k1_zfmisc_1(u1_struct_0(sK20))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_50792,c_12185])).

cnf(c_121,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f336])).

cnf(c_10107,plain,
    ( k2_pre_topc(X0,X1) = X1
    | v4_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_121])).

cnf(c_51110,plain,
    ( k2_pre_topc(sK20,k4_xboole_0(u1_struct_0(sK20),sK21)) = k4_xboole_0(u1_struct_0(sK20),sK21)
    | v4_pre_topc(k4_xboole_0(u1_struct_0(sK20),sK21),sK20) != iProver_top
    | l1_pre_topc(sK20) != iProver_top ),
    inference(superposition,[status(thm)],[c_51100,c_10107])).

cnf(c_4,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f353])).

cnf(c_10181,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f244])).

cnf(c_1278,plain,
    ( ~ r1_tarski(X0,X1)
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_28,c_1069])).

cnf(c_10095,plain,
    ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1278])).

cnf(c_49827,plain,
    ( k7_subset_1(X0,X0,X1) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_10181,c_10095])).

cnf(c_32,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X0,k3_subset_1(X1,X0)) = k2_subset_1(X1) ),
    inference(cnf_transformation,[],[f248])).

cnf(c_1282,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_subset_1(X1,X0,k3_subset_1(X1,X0)) = k2_subset_1(X1) ),
    inference(bin_hyper_res,[status(thm)],[c_32,c_1069])).

cnf(c_10091,plain,
    ( k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = k2_subset_1(X0)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1282])).

cnf(c_20,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f236])).

cnf(c_10186,plain,
    ( k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0
    | r1_tarski(X1,X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10091,c_20])).

cnf(c_14133,plain,
    ( k4_subset_1(u1_struct_0(sK20),sK21,k3_subset_1(u1_struct_0(sK20),sK21)) = u1_struct_0(sK20) ),
    inference(superposition,[status(thm)],[c_12185,c_10186])).

cnf(c_93,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f309])).

cnf(c_114,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X1)
    | k4_subset_1(u1_struct_0(X1),X0,k3_subset_1(u1_struct_0(X1),X0)) = k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f330])).

cnf(c_1814,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X2)
    | X1 != X2
    | k4_subset_1(u1_struct_0(X1),X0,k3_subset_1(u1_struct_0(X1),X0)) = k2_struct_0(X1) ),
    inference(resolution_lifted,[status(thm)],[c_93,c_114])).

cnf(c_1815,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k4_subset_1(u1_struct_0(X1),X0,k3_subset_1(u1_struct_0(X1),X0)) = k2_struct_0(X1) ),
    inference(unflattening,[status(thm)],[c_1814])).

cnf(c_10078,plain,
    ( k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) = k2_struct_0(X0)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1815])).

cnf(c_10809,plain,
    ( k4_subset_1(u1_struct_0(sK20),sK21,k3_subset_1(u1_struct_0(sK20),sK21)) = k2_struct_0(sK20)
    | l1_pre_topc(sK20) != iProver_top ),
    inference(superposition,[status(thm)],[c_10102,c_10078])).

cnf(c_130,negated_conjecture,
    ( l1_pre_topc(sK20) ),
    inference(cnf_transformation,[],[f339])).

cnf(c_131,plain,
    ( l1_pre_topc(sK20) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_130])).

cnf(c_11036,plain,
    ( k4_subset_1(u1_struct_0(sK20),sK21,k3_subset_1(u1_struct_0(sK20),sK21)) = k2_struct_0(sK20) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10809,c_131])).

cnf(c_13685,plain,
    ( k4_subset_1(u1_struct_0(sK20),sK21,k4_xboole_0(u1_struct_0(sK20),sK21)) = k2_struct_0(sK20) ),
    inference(demodulation,[status(thm)],[c_13374,c_11036])).

cnf(c_14134,plain,
    ( k2_struct_0(sK20) = u1_struct_0(sK20) ),
    inference(light_normalisation,[status(thm)],[c_14133,c_13374,c_13685])).

cnf(c_123,negated_conjecture,
    ( ~ v3_pre_topc(sK21,sK20)
    | k7_subset_1(u1_struct_0(sK20),k2_struct_0(sK20),sK21) != k2_pre_topc(sK20,k7_subset_1(u1_struct_0(sK20),k2_struct_0(sK20),sK21)) ),
    inference(cnf_transformation,[],[f346])).

cnf(c_10105,plain,
    ( k7_subset_1(u1_struct_0(sK20),k2_struct_0(sK20),sK21) != k2_pre_topc(sK20,k7_subset_1(u1_struct_0(sK20),k2_struct_0(sK20),sK21))
    | v3_pre_topc(sK21,sK20) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_123])).

cnf(c_14217,plain,
    ( k2_pre_topc(sK20,k7_subset_1(u1_struct_0(sK20),u1_struct_0(sK20),sK21)) != k7_subset_1(u1_struct_0(sK20),u1_struct_0(sK20),sK21)
    | v3_pre_topc(sK21,sK20) != iProver_top ),
    inference(demodulation,[status(thm)],[c_14134,c_10105])).

cnf(c_49907,plain,
    ( k2_pre_topc(sK20,k4_xboole_0(u1_struct_0(sK20),sK21)) != k4_xboole_0(u1_struct_0(sK20),sK21)
    | v3_pre_topc(sK21,sK20) != iProver_top ),
    inference(demodulation,[status(thm)],[c_49827,c_14217])).

cnf(c_49939,plain,
    ( ~ v3_pre_topc(sK21,sK20)
    | k2_pre_topc(sK20,k4_xboole_0(u1_struct_0(sK20),sK21)) != k4_xboole_0(u1_struct_0(sK20),sK21) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_49907])).

cnf(c_115,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X1)
    | k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0)) = X0 ),
    inference(cnf_transformation,[],[f331])).

cnf(c_1799,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X2)
    | X1 != X2
    | k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0)) = X0 ),
    inference(resolution_lifted,[status(thm)],[c_93,c_115])).

cnf(c_1800,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_1799])).

cnf(c_10079,plain,
    ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1800])).

cnf(c_11388,plain,
    ( k7_subset_1(u1_struct_0(sK20),k2_struct_0(sK20),k7_subset_1(u1_struct_0(sK20),k2_struct_0(sK20),sK21)) = sK21
    | l1_pre_topc(sK20) != iProver_top ),
    inference(superposition,[status(thm)],[c_10102,c_10079])).

cnf(c_11800,plain,
    ( k7_subset_1(u1_struct_0(sK20),k2_struct_0(sK20),k7_subset_1(u1_struct_0(sK20),k2_struct_0(sK20),sK21)) = sK21 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11388,c_131])).

cnf(c_14215,plain,
    ( k7_subset_1(u1_struct_0(sK20),u1_struct_0(sK20),k7_subset_1(u1_struct_0(sK20),u1_struct_0(sK20),sK21)) = sK21 ),
    inference(demodulation,[status(thm)],[c_14134,c_11800])).

cnf(c_75,plain,
    ( v4_pre_topc(X0,X1)
    | ~ v3_pre_topc(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f292])).

cnf(c_10138,plain,
    ( v4_pre_topc(X0,X1) = iProver_top
    | v3_pre_topc(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0),X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_75])).

cnf(c_24013,plain,
    ( v4_pre_topc(X0,sK20) = iProver_top
    | v3_pre_topc(k7_subset_1(u1_struct_0(sK20),u1_struct_0(sK20),X0),sK20) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK20))) != iProver_top
    | l1_pre_topc(sK20) != iProver_top ),
    inference(superposition,[status(thm)],[c_14134,c_10138])).

cnf(c_26391,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK20))) != iProver_top
    | v3_pre_topc(k7_subset_1(u1_struct_0(sK20),u1_struct_0(sK20),X0),sK20) != iProver_top
    | v4_pre_topc(X0,sK20) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_24013,c_131])).

cnf(c_26392,plain,
    ( v4_pre_topc(X0,sK20) = iProver_top
    | v3_pre_topc(k7_subset_1(u1_struct_0(sK20),u1_struct_0(sK20),X0),sK20) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK20))) != iProver_top ),
    inference(renaming,[status(thm)],[c_26391])).

cnf(c_26398,plain,
    ( v4_pre_topc(k7_subset_1(u1_struct_0(sK20),u1_struct_0(sK20),sK21),sK20) = iProver_top
    | v3_pre_topc(sK21,sK20) != iProver_top
    | m1_subset_1(k7_subset_1(u1_struct_0(sK20),u1_struct_0(sK20),sK21),k1_zfmisc_1(u1_struct_0(sK20))) != iProver_top ),
    inference(superposition,[status(thm)],[c_14215,c_26392])).

cnf(c_49896,plain,
    ( v4_pre_topc(k4_xboole_0(u1_struct_0(sK20),sK21),sK20) = iProver_top
    | v3_pre_topc(sK21,sK20) != iProver_top
    | m1_subset_1(k4_xboole_0(u1_struct_0(sK20),sK21),k1_zfmisc_1(u1_struct_0(sK20))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_49827,c_26398])).

cnf(c_126,negated_conjecture,
    ( v3_pre_topc(sK21,sK20)
    | k7_subset_1(u1_struct_0(sK20),k2_struct_0(sK20),sK21) = k2_pre_topc(sK20,k7_subset_1(u1_struct_0(sK20),k2_struct_0(sK20),sK21)) ),
    inference(cnf_transformation,[],[f343])).

cnf(c_10104,plain,
    ( k7_subset_1(u1_struct_0(sK20),k2_struct_0(sK20),sK21) = k2_pre_topc(sK20,k7_subset_1(u1_struct_0(sK20),k2_struct_0(sK20),sK21))
    | v3_pre_topc(sK21,sK20) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_126])).

cnf(c_14216,plain,
    ( k2_pre_topc(sK20,k7_subset_1(u1_struct_0(sK20),u1_struct_0(sK20),sK21)) = k7_subset_1(u1_struct_0(sK20),u1_struct_0(sK20),sK21)
    | v3_pre_topc(sK21,sK20) = iProver_top ),
    inference(demodulation,[status(thm)],[c_14134,c_10104])).

cnf(c_74,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X0,u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f289])).

cnf(c_10139,plain,
    ( v3_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r2_hidden(X0,u1_pre_topc(X1)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_74])).

cnf(c_22161,plain,
    ( v3_pre_topc(sK21,sK20) != iProver_top
    | r2_hidden(sK21,u1_pre_topc(sK20)) = iProver_top
    | l1_pre_topc(sK20) != iProver_top ),
    inference(superposition,[status(thm)],[c_10102,c_10139])).

cnf(c_22805,plain,
    ( r2_hidden(sK21,u1_pre_topc(sK20)) = iProver_top
    | v3_pre_topc(sK21,sK20) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_22161,c_131])).

cnf(c_22806,plain,
    ( v3_pre_topc(sK21,sK20) != iProver_top
    | r2_hidden(sK21,u1_pre_topc(sK20)) = iProver_top ),
    inference(renaming,[status(thm)],[c_22805])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f228])).

cnf(c_10176,plain,
    ( k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_22809,plain,
    ( k4_xboole_0(k1_tarski(sK21),u1_pre_topc(sK20)) = k1_xboole_0
    | v3_pre_topc(sK21,sK20) != iProver_top ),
    inference(superposition,[status(thm)],[c_22806,c_10176])).

cnf(c_23347,plain,
    ( k2_pre_topc(sK20,k7_subset_1(u1_struct_0(sK20),u1_struct_0(sK20),sK21)) = k7_subset_1(u1_struct_0(sK20),u1_struct_0(sK20),sK21)
    | k4_xboole_0(k1_tarski(sK21),u1_pre_topc(sK20)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_14216,c_22809])).

cnf(c_92,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f308])).

cnf(c_10124,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_92])).

cnf(c_16,plain,
    ( m1_subset_1(X0,X1)
    | ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f235])).

cnf(c_10171,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_60,plain,
    ( ~ m1_pre_topc(k1_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(k1_pre_topc(X0,X1))
    | k2_struct_0(k1_pre_topc(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f357])).

cnf(c_90,plain,
    ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f307])).

cnf(c_814,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(k1_pre_topc(X0,X1))
    | k2_struct_0(k1_pre_topc(X0,X1)) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_60,c_90])).

cnf(c_815,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v1_pre_topc(k1_pre_topc(X1,X0))
    | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
    inference(renaming,[status(thm)],[c_814])).

cnf(c_91,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | v1_pre_topc(k1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f306])).

cnf(c_820,plain,
    ( ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_815,c_91])).

cnf(c_821,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
    inference(renaming,[status(thm)],[c_820])).

cnf(c_10100,plain,
    ( k2_struct_0(k1_pre_topc(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_821])).

cnf(c_18018,plain,
    ( k2_struct_0(k1_pre_topc(sK20,sK21)) = sK21
    | l1_pre_topc(sK20) != iProver_top ),
    inference(superposition,[status(thm)],[c_10102,c_10100])).

cnf(c_18277,plain,
    ( k2_struct_0(k1_pre_topc(sK20,sK21)) = sK21 ),
    inference(global_propositional_subsumption,[status(thm)],[c_18018,c_131])).

cnf(c_84,plain,
    ( ~ sP1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(X0),X2,k2_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X2,u1_pre_topc(X1))
    | r2_hidden(k9_subset_1(u1_struct_0(X0),X2,k2_struct_0(X0)),u1_pre_topc(X0)) ),
    inference(cnf_transformation,[],[f358])).

cnf(c_10131,plain,
    ( sP1(X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k9_subset_1(u1_struct_0(X0),X2,k2_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | r2_hidden(X2,u1_pre_topc(X1)) != iProver_top
    | r2_hidden(k9_subset_1(u1_struct_0(X0),X2,k2_struct_0(X0)),u1_pre_topc(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_84])).

cnf(c_26543,plain,
    ( sP1(k1_pre_topc(sK20,sK21),X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(k9_subset_1(u1_struct_0(k1_pre_topc(sK20,sK21)),X1,sK21),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK20,sK21)))) != iProver_top
    | r2_hidden(X1,u1_pre_topc(X0)) != iProver_top
    | r2_hidden(k9_subset_1(u1_struct_0(k1_pre_topc(sK20,sK21)),X1,k2_struct_0(k1_pre_topc(sK20,sK21))),u1_pre_topc(k1_pre_topc(sK20,sK21))) = iProver_top ),
    inference(superposition,[status(thm)],[c_18277,c_10131])).

cnf(c_26544,plain,
    ( sP1(k1_pre_topc(sK20,sK21),X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(k9_subset_1(u1_struct_0(k1_pre_topc(sK20,sK21)),X1,sK21),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK20,sK21)))) != iProver_top
    | r2_hidden(X1,u1_pre_topc(X0)) != iProver_top
    | r2_hidden(k9_subset_1(u1_struct_0(k1_pre_topc(sK20,sK21)),X1,sK21),u1_pre_topc(k1_pre_topc(sK20,sK21))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_26543,c_18277])).

cnf(c_26980,plain,
    ( sP1(k1_pre_topc(sK20,sK21),X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | r2_hidden(X1,u1_pre_topc(X0)) != iProver_top
    | r2_hidden(k9_subset_1(u1_struct_0(k1_pre_topc(sK20,sK21)),X1,sK21),u1_pre_topc(k1_pre_topc(sK20,sK21))) = iProver_top
    | v1_xboole_0(k9_subset_1(u1_struct_0(k1_pre_topc(sK20,sK21)),X1,sK21)) != iProver_top
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK20,sK21)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_10171,c_26544])).

cnf(c_27147,plain,
    ( sP1(k1_pre_topc(sK20,sK21),X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | r2_hidden(k9_subset_1(u1_struct_0(k1_pre_topc(sK20,sK21)),k2_pre_topc(X0,X1),sK21),u1_pre_topc(k1_pre_topc(sK20,sK21))) = iProver_top
    | r2_hidden(k2_pre_topc(X0,X1),u1_pre_topc(X0)) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(k9_subset_1(u1_struct_0(k1_pre_topc(sK20,sK21)),k2_pre_topc(X0,X1),sK21)) != iProver_top
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK20,sK21)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_10124,c_26980])).

cnf(c_32225,plain,
    ( k4_xboole_0(k1_tarski(sK21),u1_pre_topc(sK20)) = k1_xboole_0
    | sP1(k1_pre_topc(sK20,sK21),sK20) != iProver_top
    | m1_subset_1(k7_subset_1(u1_struct_0(sK20),u1_struct_0(sK20),sK21),k1_zfmisc_1(u1_struct_0(sK20))) != iProver_top
    | r2_hidden(k7_subset_1(u1_struct_0(sK20),u1_struct_0(sK20),sK21),u1_pre_topc(sK20)) != iProver_top
    | r2_hidden(k9_subset_1(u1_struct_0(k1_pre_topc(sK20,sK21)),k2_pre_topc(sK20,k7_subset_1(u1_struct_0(sK20),u1_struct_0(sK20),sK21)),sK21),u1_pre_topc(k1_pre_topc(sK20,sK21))) = iProver_top
    | l1_pre_topc(sK20) != iProver_top
    | v1_xboole_0(k9_subset_1(u1_struct_0(k1_pre_topc(sK20,sK21)),k2_pre_topc(sK20,k7_subset_1(u1_struct_0(sK20),u1_struct_0(sK20),sK21)),sK21)) != iProver_top
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK20,sK21)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_23347,c_27147])).

cnf(c_120,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f337])).

cnf(c_10108,plain,
    ( k2_pre_topc(X0,X1) != X1
    | v4_pre_topc(X1,X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_120])).

cnf(c_23849,plain,
    ( k4_xboole_0(k1_tarski(sK21),u1_pre_topc(sK20)) = k1_xboole_0
    | v4_pre_topc(k7_subset_1(u1_struct_0(sK20),u1_struct_0(sK20),sK21),sK20) = iProver_top
    | m1_subset_1(k7_subset_1(u1_struct_0(sK20),u1_struct_0(sK20),sK21),k1_zfmisc_1(u1_struct_0(sK20))) != iProver_top
    | v2_pre_topc(sK20) != iProver_top
    | l1_pre_topc(sK20) != iProver_top ),
    inference(superposition,[status(thm)],[c_23347,c_10108])).

cnf(c_128,negated_conjecture,
    ( v3_pre_topc(sK21,sK20)
    | v2_pre_topc(sK20) ),
    inference(cnf_transformation,[],[f341])).

cnf(c_10103,plain,
    ( v3_pre_topc(sK21,sK20) = iProver_top
    | v2_pre_topc(sK20) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_128])).

cnf(c_23348,plain,
    ( k4_xboole_0(k1_tarski(sK21),u1_pre_topc(sK20)) = k1_xboole_0
    | v2_pre_topc(sK20) = iProver_top ),
    inference(superposition,[status(thm)],[c_10103,c_22809])).

cnf(c_25514,plain,
    ( k4_xboole_0(k1_tarski(sK21),u1_pre_topc(sK20)) = k1_xboole_0
    | v4_pre_topc(k7_subset_1(u1_struct_0(sK20),u1_struct_0(sK20),sK21),sK20) = iProver_top
    | m1_subset_1(k7_subset_1(u1_struct_0(sK20),u1_struct_0(sK20),sK21),k1_zfmisc_1(u1_struct_0(sK20))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_23849,c_131,c_23348])).

cnf(c_76,plain,
    ( ~ v4_pre_topc(X0,X1)
    | v3_pre_topc(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f291])).

cnf(c_10137,plain,
    ( v4_pre_topc(X0,X1) != iProver_top
    | v3_pre_topc(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0),X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_76])).

cnf(c_24003,plain,
    ( v4_pre_topc(X0,sK20) != iProver_top
    | v3_pre_topc(k7_subset_1(u1_struct_0(sK20),u1_struct_0(sK20),X0),sK20) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK20))) != iProver_top
    | l1_pre_topc(sK20) != iProver_top ),
    inference(superposition,[status(thm)],[c_14134,c_10137])).

cnf(c_26187,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK20))) != iProver_top
    | v3_pre_topc(k7_subset_1(u1_struct_0(sK20),u1_struct_0(sK20),X0),sK20) = iProver_top
    | v4_pre_topc(X0,sK20) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_24003,c_131])).

cnf(c_26188,plain,
    ( v4_pre_topc(X0,sK20) != iProver_top
    | v3_pre_topc(k7_subset_1(u1_struct_0(sK20),u1_struct_0(sK20),X0),sK20) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK20))) != iProver_top ),
    inference(renaming,[status(thm)],[c_26187])).

cnf(c_26193,plain,
    ( v4_pre_topc(k7_subset_1(u1_struct_0(sK20),u1_struct_0(sK20),sK21),sK20) != iProver_top
    | v3_pre_topc(sK21,sK20) = iProver_top
    | m1_subset_1(k7_subset_1(u1_struct_0(sK20),u1_struct_0(sK20),sK21),k1_zfmisc_1(u1_struct_0(sK20))) != iProver_top ),
    inference(superposition,[status(thm)],[c_14215,c_26188])).

cnf(c_32655,plain,
    ( m1_subset_1(k7_subset_1(u1_struct_0(sK20),u1_struct_0(sK20),sK21),k1_zfmisc_1(u1_struct_0(sK20))) != iProver_top
    | k4_xboole_0(k1_tarski(sK21),u1_pre_topc(sK20)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_32225,c_22809,c_25514,c_26193])).

cnf(c_32656,plain,
    ( k4_xboole_0(k1_tarski(sK21),u1_pre_topc(sK20)) = k1_xboole_0
    | m1_subset_1(k7_subset_1(u1_struct_0(sK20),u1_struct_0(sK20),sK21),k1_zfmisc_1(u1_struct_0(sK20))) != iProver_top ),
    inference(renaming,[status(thm)],[c_32655])).

cnf(c_49892,plain,
    ( k4_xboole_0(k1_tarski(sK21),u1_pre_topc(sK20)) = k1_xboole_0
    | m1_subset_1(k4_xboole_0(u1_struct_0(sK20),sK21),k1_zfmisc_1(u1_struct_0(sK20))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_49827,c_32656])).

cnf(c_12,plain,
    ( r2_hidden(X0,X1)
    | k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f227])).

cnf(c_48607,plain,
    ( r2_hidden(sK21,u1_pre_topc(sK20))
    | k4_xboole_0(k1_tarski(sK21),u1_pre_topc(sK20)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_48608,plain,
    ( k4_xboole_0(k1_tarski(sK21),u1_pre_topc(sK20)) != k1_xboole_0
    | r2_hidden(sK21,u1_pre_topc(sK20)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48607])).

cnf(c_73,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f290])).

cnf(c_10140,plain,
    ( v3_pre_topc(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r2_hidden(X0,u1_pre_topc(X1)) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_73])).

cnf(c_22432,plain,
    ( v3_pre_topc(sK21,sK20) = iProver_top
    | r2_hidden(sK21,u1_pre_topc(sK20)) != iProver_top
    | l1_pre_topc(sK20) != iProver_top ),
    inference(superposition,[status(thm)],[c_10102,c_10140])).

cnf(c_23070,plain,
    ( r2_hidden(sK21,u1_pre_topc(sK20)) != iProver_top
    | v3_pre_topc(sK21,sK20) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_22432,c_131])).

cnf(c_23071,plain,
    ( v3_pre_topc(sK21,sK20) = iProver_top
    | r2_hidden(sK21,u1_pre_topc(sK20)) != iProver_top ),
    inference(renaming,[status(thm)],[c_23070])).

cnf(c_23072,plain,
    ( v3_pre_topc(sK21,sK20)
    | ~ r2_hidden(sK21,u1_pre_topc(sK20)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_23071])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_51110,c_50792,c_49939,c_49896,c_49892,c_48608,c_48607,c_23072,c_23071,c_12185,c_131])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:02:51 EST 2020
% 0.19/0.35  % CPUTime    : 
% 0.19/0.35  % Running in FOF mode
% 11.86/2.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.86/2.00  
% 11.86/2.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.86/2.00  
% 11.86/2.00  ------  iProver source info
% 11.86/2.00  
% 11.86/2.00  git: date: 2020-06-30 10:37:57 +0100
% 11.86/2.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.86/2.00  git: non_committed_changes: false
% 11.86/2.00  git: last_make_outside_of_git: false
% 11.86/2.00  
% 11.86/2.00  ------ 
% 11.86/2.00  
% 11.86/2.00  ------ Input Options
% 11.86/2.00  
% 11.86/2.00  --out_options                           all
% 11.86/2.00  --tptp_safe_out                         true
% 11.86/2.00  --problem_path                          ""
% 11.86/2.00  --include_path                          ""
% 11.86/2.00  --clausifier                            res/vclausify_rel
% 11.86/2.00  --clausifier_options                    ""
% 11.86/2.00  --stdin                                 false
% 11.86/2.00  --stats_out                             all
% 11.86/2.00  
% 11.86/2.00  ------ General Options
% 11.86/2.00  
% 11.86/2.00  --fof                                   false
% 11.86/2.00  --time_out_real                         305.
% 11.86/2.00  --time_out_virtual                      -1.
% 11.86/2.00  --symbol_type_check                     false
% 11.86/2.00  --clausify_out                          false
% 11.86/2.00  --sig_cnt_out                           false
% 11.86/2.00  --trig_cnt_out                          false
% 11.86/2.00  --trig_cnt_out_tolerance                1.
% 11.86/2.00  --trig_cnt_out_sk_spl                   false
% 11.86/2.00  --abstr_cl_out                          false
% 11.86/2.00  
% 11.86/2.00  ------ Global Options
% 11.86/2.00  
% 11.86/2.00  --schedule                              default
% 11.86/2.00  --add_important_lit                     false
% 11.86/2.00  --prop_solver_per_cl                    1000
% 11.86/2.00  --min_unsat_core                        false
% 11.86/2.00  --soft_assumptions                      false
% 11.86/2.00  --soft_lemma_size                       3
% 11.86/2.00  --prop_impl_unit_size                   0
% 11.86/2.00  --prop_impl_unit                        []
% 11.86/2.00  --share_sel_clauses                     true
% 11.86/2.00  --reset_solvers                         false
% 11.86/2.00  --bc_imp_inh                            [conj_cone]
% 11.86/2.00  --conj_cone_tolerance                   3.
% 11.86/2.00  --extra_neg_conj                        none
% 11.86/2.00  --large_theory_mode                     true
% 11.86/2.00  --prolific_symb_bound                   200
% 11.86/2.00  --lt_threshold                          2000
% 11.86/2.00  --clause_weak_htbl                      true
% 11.86/2.00  --gc_record_bc_elim                     false
% 11.86/2.00  
% 11.86/2.00  ------ Preprocessing Options
% 11.86/2.00  
% 11.86/2.00  --preprocessing_flag                    true
% 11.86/2.00  --time_out_prep_mult                    0.1
% 11.86/2.00  --splitting_mode                        input
% 11.86/2.00  --splitting_grd                         true
% 11.86/2.00  --splitting_cvd                         false
% 11.86/2.00  --splitting_cvd_svl                     false
% 11.86/2.00  --splitting_nvd                         32
% 11.86/2.00  --sub_typing                            true
% 11.86/2.00  --prep_gs_sim                           true
% 11.86/2.00  --prep_unflatten                        true
% 11.86/2.00  --prep_res_sim                          true
% 11.86/2.00  --prep_upred                            true
% 11.86/2.00  --prep_sem_filter                       exhaustive
% 11.86/2.00  --prep_sem_filter_out                   false
% 11.86/2.00  --pred_elim                             true
% 11.86/2.00  --res_sim_input                         true
% 11.86/2.00  --eq_ax_congr_red                       true
% 11.86/2.00  --pure_diseq_elim                       true
% 11.86/2.00  --brand_transform                       false
% 11.86/2.00  --non_eq_to_eq                          false
% 11.86/2.00  --prep_def_merge                        true
% 11.86/2.00  --prep_def_merge_prop_impl              false
% 11.86/2.00  --prep_def_merge_mbd                    true
% 11.86/2.00  --prep_def_merge_tr_red                 false
% 11.86/2.00  --prep_def_merge_tr_cl                  false
% 11.86/2.00  --smt_preprocessing                     true
% 11.86/2.00  --smt_ac_axioms                         fast
% 11.86/2.00  --preprocessed_out                      false
% 11.86/2.00  --preprocessed_stats                    false
% 11.86/2.00  
% 11.86/2.00  ------ Abstraction refinement Options
% 11.86/2.00  
% 11.86/2.00  --abstr_ref                             []
% 11.86/2.00  --abstr_ref_prep                        false
% 11.86/2.00  --abstr_ref_until_sat                   false
% 11.86/2.00  --abstr_ref_sig_restrict                funpre
% 11.86/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 11.86/2.00  --abstr_ref_under                       []
% 11.86/2.00  
% 11.86/2.00  ------ SAT Options
% 11.86/2.00  
% 11.86/2.00  --sat_mode                              false
% 11.86/2.00  --sat_fm_restart_options                ""
% 11.86/2.00  --sat_gr_def                            false
% 11.86/2.00  --sat_epr_types                         true
% 11.86/2.00  --sat_non_cyclic_types                  false
% 11.86/2.00  --sat_finite_models                     false
% 11.86/2.00  --sat_fm_lemmas                         false
% 11.86/2.00  --sat_fm_prep                           false
% 11.86/2.00  --sat_fm_uc_incr                        true
% 11.86/2.00  --sat_out_model                         small
% 11.86/2.00  --sat_out_clauses                       false
% 11.86/2.00  
% 11.86/2.00  ------ QBF Options
% 11.86/2.00  
% 11.86/2.00  --qbf_mode                              false
% 11.86/2.00  --qbf_elim_univ                         false
% 11.86/2.00  --qbf_dom_inst                          none
% 11.86/2.00  --qbf_dom_pre_inst                      false
% 11.86/2.00  --qbf_sk_in                             false
% 11.86/2.00  --qbf_pred_elim                         true
% 11.86/2.00  --qbf_split                             512
% 11.86/2.00  
% 11.86/2.00  ------ BMC1 Options
% 11.86/2.00  
% 11.86/2.00  --bmc1_incremental                      false
% 11.86/2.00  --bmc1_axioms                           reachable_all
% 11.86/2.00  --bmc1_min_bound                        0
% 11.86/2.00  --bmc1_max_bound                        -1
% 11.86/2.00  --bmc1_max_bound_default                -1
% 11.86/2.00  --bmc1_symbol_reachability              true
% 11.86/2.00  --bmc1_property_lemmas                  false
% 11.86/2.00  --bmc1_k_induction                      false
% 11.86/2.00  --bmc1_non_equiv_states                 false
% 11.86/2.00  --bmc1_deadlock                         false
% 11.86/2.00  --bmc1_ucm                              false
% 11.86/2.00  --bmc1_add_unsat_core                   none
% 11.86/2.00  --bmc1_unsat_core_children              false
% 11.86/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 11.86/2.00  --bmc1_out_stat                         full
% 11.86/2.00  --bmc1_ground_init                      false
% 11.86/2.00  --bmc1_pre_inst_next_state              false
% 11.86/2.00  --bmc1_pre_inst_state                   false
% 11.86/2.00  --bmc1_pre_inst_reach_state             false
% 11.86/2.00  --bmc1_out_unsat_core                   false
% 11.86/2.00  --bmc1_aig_witness_out                  false
% 11.86/2.00  --bmc1_verbose                          false
% 11.86/2.00  --bmc1_dump_clauses_tptp                false
% 11.86/2.00  --bmc1_dump_unsat_core_tptp             false
% 11.86/2.00  --bmc1_dump_file                        -
% 11.86/2.00  --bmc1_ucm_expand_uc_limit              128
% 11.86/2.00  --bmc1_ucm_n_expand_iterations          6
% 11.86/2.00  --bmc1_ucm_extend_mode                  1
% 11.86/2.00  --bmc1_ucm_init_mode                    2
% 11.86/2.00  --bmc1_ucm_cone_mode                    none
% 11.86/2.00  --bmc1_ucm_reduced_relation_type        0
% 11.86/2.00  --bmc1_ucm_relax_model                  4
% 11.86/2.00  --bmc1_ucm_full_tr_after_sat            true
% 11.86/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 11.86/2.00  --bmc1_ucm_layered_model                none
% 11.86/2.00  --bmc1_ucm_max_lemma_size               10
% 11.86/2.00  
% 11.86/2.00  ------ AIG Options
% 11.86/2.00  
% 11.86/2.00  --aig_mode                              false
% 11.86/2.00  
% 11.86/2.00  ------ Instantiation Options
% 11.86/2.00  
% 11.86/2.00  --instantiation_flag                    true
% 11.86/2.00  --inst_sos_flag                         true
% 11.86/2.00  --inst_sos_phase                        true
% 11.86/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.86/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.86/2.00  --inst_lit_sel_side                     num_symb
% 11.86/2.00  --inst_solver_per_active                1400
% 11.86/2.00  --inst_solver_calls_frac                1.
% 11.86/2.00  --inst_passive_queue_type               priority_queues
% 11.86/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.86/2.00  --inst_passive_queues_freq              [25;2]
% 11.86/2.00  --inst_dismatching                      true
% 11.86/2.00  --inst_eager_unprocessed_to_passive     true
% 11.86/2.00  --inst_prop_sim_given                   true
% 11.86/2.00  --inst_prop_sim_new                     false
% 11.86/2.00  --inst_subs_new                         false
% 11.86/2.00  --inst_eq_res_simp                      false
% 11.86/2.00  --inst_subs_given                       false
% 11.86/2.00  --inst_orphan_elimination               true
% 11.86/2.00  --inst_learning_loop_flag               true
% 11.86/2.00  --inst_learning_start                   3000
% 11.86/2.00  --inst_learning_factor                  2
% 11.86/2.00  --inst_start_prop_sim_after_learn       3
% 11.86/2.00  --inst_sel_renew                        solver
% 11.86/2.00  --inst_lit_activity_flag                true
% 11.86/2.00  --inst_restr_to_given                   false
% 11.86/2.00  --inst_activity_threshold               500
% 11.86/2.00  --inst_out_proof                        true
% 11.86/2.00  
% 11.86/2.00  ------ Resolution Options
% 11.86/2.00  
% 11.86/2.00  --resolution_flag                       true
% 11.86/2.00  --res_lit_sel                           adaptive
% 11.86/2.00  --res_lit_sel_side                      none
% 11.86/2.00  --res_ordering                          kbo
% 11.86/2.00  --res_to_prop_solver                    active
% 11.86/2.00  --res_prop_simpl_new                    false
% 11.86/2.00  --res_prop_simpl_given                  true
% 11.86/2.00  --res_passive_queue_type                priority_queues
% 11.86/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.86/2.00  --res_passive_queues_freq               [15;5]
% 11.86/2.00  --res_forward_subs                      full
% 11.86/2.00  --res_backward_subs                     full
% 11.86/2.00  --res_forward_subs_resolution           true
% 11.86/2.00  --res_backward_subs_resolution          true
% 11.86/2.00  --res_orphan_elimination                true
% 11.86/2.00  --res_time_limit                        2.
% 11.86/2.00  --res_out_proof                         true
% 11.86/2.00  
% 11.86/2.00  ------ Superposition Options
% 11.86/2.00  
% 11.86/2.00  --superposition_flag                    true
% 11.86/2.00  --sup_passive_queue_type                priority_queues
% 11.86/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.86/2.00  --sup_passive_queues_freq               [8;1;4]
% 11.86/2.00  --demod_completeness_check              fast
% 11.86/2.00  --demod_use_ground                      true
% 11.86/2.00  --sup_to_prop_solver                    passive
% 11.86/2.00  --sup_prop_simpl_new                    true
% 11.86/2.00  --sup_prop_simpl_given                  true
% 11.86/2.00  --sup_fun_splitting                     true
% 11.86/2.00  --sup_smt_interval                      50000
% 11.86/2.00  
% 11.86/2.00  ------ Superposition Simplification Setup
% 11.86/2.00  
% 11.86/2.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.86/2.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.86/2.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.86/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.86/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 11.86/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.86/2.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.86/2.00  --sup_immed_triv                        [TrivRules]
% 11.86/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.86/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.86/2.00  --sup_immed_bw_main                     []
% 11.86/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.86/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.86/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.86/2.00  --sup_input_bw                          []
% 11.86/2.00  
% 11.86/2.00  ------ Combination Options
% 11.86/2.00  
% 11.86/2.00  --comb_res_mult                         3
% 11.86/2.00  --comb_sup_mult                         2
% 11.86/2.00  --comb_inst_mult                        10
% 11.86/2.00  
% 11.86/2.00  ------ Debug Options
% 11.86/2.00  
% 11.86/2.00  --dbg_backtrace                         false
% 11.86/2.00  --dbg_dump_prop_clauses                 false
% 11.86/2.00  --dbg_dump_prop_clauses_file            -
% 11.86/2.00  --dbg_out_stat                          false
% 11.86/2.00  ------ Parsing...
% 11.86/2.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.86/2.00  
% 11.86/2.00  ------ Preprocessing... sf_s  rm: 13 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 11.86/2.00  
% 11.86/2.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.86/2.00  
% 11.86/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.86/2.00  ------ Proving...
% 11.86/2.00  ------ Problem Properties 
% 11.86/2.00  
% 11.86/2.00  
% 11.86/2.00  clauses                                 111
% 11.86/2.00  conjectures                             5
% 11.86/2.00  EPR                                     17
% 11.86/2.00  Horn                                    86
% 11.86/2.00  unary                                   7
% 11.86/2.00  binary                                  39
% 11.86/2.00  lits                                    322
% 11.86/2.00  lits eq                                 53
% 11.86/2.00  fd_pure                                 0
% 11.86/2.00  fd_pseudo                               0
% 11.86/2.00  fd_cond                                 10
% 11.86/2.00  fd_pseudo_cond                          6
% 11.86/2.00  AC symbols                              0
% 11.86/2.00  
% 11.86/2.00  ------ Schedule dynamic 5 is on 
% 11.86/2.00  
% 11.86/2.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.86/2.00  
% 11.86/2.00  
% 11.86/2.00  ------ 
% 11.86/2.00  Current options:
% 11.86/2.00  ------ 
% 11.86/2.00  
% 11.86/2.00  ------ Input Options
% 11.86/2.00  
% 11.86/2.00  --out_options                           all
% 11.86/2.00  --tptp_safe_out                         true
% 11.86/2.00  --problem_path                          ""
% 11.86/2.00  --include_path                          ""
% 11.86/2.00  --clausifier                            res/vclausify_rel
% 11.86/2.00  --clausifier_options                    ""
% 11.86/2.00  --stdin                                 false
% 11.86/2.00  --stats_out                             all
% 11.86/2.00  
% 11.86/2.00  ------ General Options
% 11.86/2.00  
% 11.86/2.00  --fof                                   false
% 11.86/2.00  --time_out_real                         305.
% 11.86/2.00  --time_out_virtual                      -1.
% 11.86/2.00  --symbol_type_check                     false
% 11.86/2.00  --clausify_out                          false
% 11.86/2.00  --sig_cnt_out                           false
% 11.86/2.00  --trig_cnt_out                          false
% 11.86/2.00  --trig_cnt_out_tolerance                1.
% 11.86/2.00  --trig_cnt_out_sk_spl                   false
% 11.86/2.00  --abstr_cl_out                          false
% 11.86/2.00  
% 11.86/2.00  ------ Global Options
% 11.86/2.00  
% 11.86/2.00  --schedule                              default
% 11.86/2.00  --add_important_lit                     false
% 11.86/2.00  --prop_solver_per_cl                    1000
% 11.86/2.00  --min_unsat_core                        false
% 11.86/2.00  --soft_assumptions                      false
% 11.86/2.00  --soft_lemma_size                       3
% 11.86/2.00  --prop_impl_unit_size                   0
% 11.86/2.00  --prop_impl_unit                        []
% 11.86/2.00  --share_sel_clauses                     true
% 11.86/2.00  --reset_solvers                         false
% 11.86/2.00  --bc_imp_inh                            [conj_cone]
% 11.86/2.00  --conj_cone_tolerance                   3.
% 11.86/2.00  --extra_neg_conj                        none
% 11.86/2.00  --large_theory_mode                     true
% 11.86/2.00  --prolific_symb_bound                   200
% 11.86/2.00  --lt_threshold                          2000
% 11.86/2.00  --clause_weak_htbl                      true
% 11.86/2.00  --gc_record_bc_elim                     false
% 11.86/2.00  
% 11.86/2.00  ------ Preprocessing Options
% 11.86/2.00  
% 11.86/2.00  --preprocessing_flag                    true
% 11.86/2.00  --time_out_prep_mult                    0.1
% 11.86/2.00  --splitting_mode                        input
% 11.86/2.00  --splitting_grd                         true
% 11.86/2.00  --splitting_cvd                         false
% 11.86/2.00  --splitting_cvd_svl                     false
% 11.86/2.00  --splitting_nvd                         32
% 11.86/2.00  --sub_typing                            true
% 11.86/2.00  --prep_gs_sim                           true
% 11.86/2.00  --prep_unflatten                        true
% 11.86/2.00  --prep_res_sim                          true
% 11.86/2.00  --prep_upred                            true
% 11.86/2.00  --prep_sem_filter                       exhaustive
% 11.86/2.00  --prep_sem_filter_out                   false
% 11.86/2.00  --pred_elim                             true
% 11.86/2.00  --res_sim_input                         true
% 11.86/2.00  --eq_ax_congr_red                       true
% 11.86/2.00  --pure_diseq_elim                       true
% 11.86/2.00  --brand_transform                       false
% 11.86/2.00  --non_eq_to_eq                          false
% 11.86/2.00  --prep_def_merge                        true
% 11.86/2.00  --prep_def_merge_prop_impl              false
% 11.86/2.00  --prep_def_merge_mbd                    true
% 11.86/2.00  --prep_def_merge_tr_red                 false
% 11.86/2.00  --prep_def_merge_tr_cl                  false
% 11.86/2.00  --smt_preprocessing                     true
% 11.86/2.00  --smt_ac_axioms                         fast
% 11.86/2.00  --preprocessed_out                      false
% 11.86/2.00  --preprocessed_stats                    false
% 11.86/2.00  
% 11.86/2.00  ------ Abstraction refinement Options
% 11.86/2.00  
% 11.86/2.00  --abstr_ref                             []
% 11.86/2.00  --abstr_ref_prep                        false
% 11.86/2.00  --abstr_ref_until_sat                   false
% 11.86/2.00  --abstr_ref_sig_restrict                funpre
% 11.86/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 11.86/2.00  --abstr_ref_under                       []
% 11.86/2.00  
% 11.86/2.00  ------ SAT Options
% 11.86/2.00  
% 11.86/2.00  --sat_mode                              false
% 11.86/2.00  --sat_fm_restart_options                ""
% 11.86/2.00  --sat_gr_def                            false
% 11.86/2.00  --sat_epr_types                         true
% 11.86/2.00  --sat_non_cyclic_types                  false
% 11.86/2.00  --sat_finite_models                     false
% 11.86/2.00  --sat_fm_lemmas                         false
% 11.86/2.00  --sat_fm_prep                           false
% 11.86/2.00  --sat_fm_uc_incr                        true
% 11.86/2.00  --sat_out_model                         small
% 11.86/2.00  --sat_out_clauses                       false
% 11.86/2.00  
% 11.86/2.00  ------ QBF Options
% 11.86/2.00  
% 11.86/2.00  --qbf_mode                              false
% 11.86/2.00  --qbf_elim_univ                         false
% 11.86/2.00  --qbf_dom_inst                          none
% 11.86/2.00  --qbf_dom_pre_inst                      false
% 11.86/2.00  --qbf_sk_in                             false
% 11.86/2.00  --qbf_pred_elim                         true
% 11.86/2.00  --qbf_split                             512
% 11.86/2.00  
% 11.86/2.00  ------ BMC1 Options
% 11.86/2.00  
% 11.86/2.00  --bmc1_incremental                      false
% 11.86/2.00  --bmc1_axioms                           reachable_all
% 11.86/2.00  --bmc1_min_bound                        0
% 11.86/2.00  --bmc1_max_bound                        -1
% 11.86/2.00  --bmc1_max_bound_default                -1
% 11.86/2.00  --bmc1_symbol_reachability              true
% 11.86/2.00  --bmc1_property_lemmas                  false
% 11.86/2.00  --bmc1_k_induction                      false
% 11.86/2.00  --bmc1_non_equiv_states                 false
% 11.86/2.00  --bmc1_deadlock                         false
% 11.86/2.00  --bmc1_ucm                              false
% 11.86/2.00  --bmc1_add_unsat_core                   none
% 11.86/2.00  --bmc1_unsat_core_children              false
% 11.86/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 11.86/2.00  --bmc1_out_stat                         full
% 11.86/2.00  --bmc1_ground_init                      false
% 11.86/2.00  --bmc1_pre_inst_next_state              false
% 11.86/2.00  --bmc1_pre_inst_state                   false
% 11.86/2.00  --bmc1_pre_inst_reach_state             false
% 11.86/2.00  --bmc1_out_unsat_core                   false
% 11.86/2.00  --bmc1_aig_witness_out                  false
% 11.86/2.00  --bmc1_verbose                          false
% 11.86/2.00  --bmc1_dump_clauses_tptp                false
% 11.86/2.00  --bmc1_dump_unsat_core_tptp             false
% 11.86/2.00  --bmc1_dump_file                        -
% 11.86/2.00  --bmc1_ucm_expand_uc_limit              128
% 11.86/2.00  --bmc1_ucm_n_expand_iterations          6
% 11.86/2.00  --bmc1_ucm_extend_mode                  1
% 11.86/2.00  --bmc1_ucm_init_mode                    2
% 11.86/2.00  --bmc1_ucm_cone_mode                    none
% 11.86/2.00  --bmc1_ucm_reduced_relation_type        0
% 11.86/2.00  --bmc1_ucm_relax_model                  4
% 11.86/2.00  --bmc1_ucm_full_tr_after_sat            true
% 11.86/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 11.86/2.00  --bmc1_ucm_layered_model                none
% 11.86/2.00  --bmc1_ucm_max_lemma_size               10
% 11.86/2.00  
% 11.86/2.00  ------ AIG Options
% 11.86/2.00  
% 11.86/2.00  --aig_mode                              false
% 11.86/2.00  
% 11.86/2.00  ------ Instantiation Options
% 11.86/2.00  
% 11.86/2.00  --instantiation_flag                    true
% 11.86/2.00  --inst_sos_flag                         true
% 11.86/2.00  --inst_sos_phase                        true
% 11.86/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.86/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.86/2.00  --inst_lit_sel_side                     none
% 11.86/2.00  --inst_solver_per_active                1400
% 11.86/2.00  --inst_solver_calls_frac                1.
% 11.86/2.00  --inst_passive_queue_type               priority_queues
% 11.86/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.86/2.00  --inst_passive_queues_freq              [25;2]
% 11.86/2.00  --inst_dismatching                      true
% 11.86/2.00  --inst_eager_unprocessed_to_passive     true
% 11.86/2.00  --inst_prop_sim_given                   true
% 11.86/2.00  --inst_prop_sim_new                     false
% 11.86/2.00  --inst_subs_new                         false
% 11.86/2.00  --inst_eq_res_simp                      false
% 11.86/2.00  --inst_subs_given                       false
% 11.86/2.00  --inst_orphan_elimination               true
% 11.86/2.00  --inst_learning_loop_flag               true
% 11.86/2.00  --inst_learning_start                   3000
% 11.86/2.00  --inst_learning_factor                  2
% 11.86/2.00  --inst_start_prop_sim_after_learn       3
% 11.86/2.00  --inst_sel_renew                        solver
% 11.86/2.00  --inst_lit_activity_flag                true
% 11.86/2.00  --inst_restr_to_given                   false
% 11.86/2.00  --inst_activity_threshold               500
% 11.86/2.00  --inst_out_proof                        true
% 11.86/2.00  
% 11.86/2.00  ------ Resolution Options
% 11.86/2.00  
% 11.86/2.00  --resolution_flag                       false
% 11.86/2.00  --res_lit_sel                           adaptive
% 11.86/2.00  --res_lit_sel_side                      none
% 11.86/2.00  --res_ordering                          kbo
% 11.86/2.00  --res_to_prop_solver                    active
% 11.86/2.00  --res_prop_simpl_new                    false
% 11.86/2.00  --res_prop_simpl_given                  true
% 11.86/2.00  --res_passive_queue_type                priority_queues
% 11.86/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.86/2.00  --res_passive_queues_freq               [15;5]
% 11.86/2.00  --res_forward_subs                      full
% 11.86/2.00  --res_backward_subs                     full
% 11.86/2.00  --res_forward_subs_resolution           true
% 11.86/2.00  --res_backward_subs_resolution          true
% 11.86/2.00  --res_orphan_elimination                true
% 11.86/2.00  --res_time_limit                        2.
% 11.86/2.00  --res_out_proof                         true
% 11.86/2.00  
% 11.86/2.00  ------ Superposition Options
% 11.86/2.00  
% 11.86/2.00  --superposition_flag                    true
% 11.86/2.00  --sup_passive_queue_type                priority_queues
% 11.86/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.86/2.00  --sup_passive_queues_freq               [8;1;4]
% 11.86/2.00  --demod_completeness_check              fast
% 11.86/2.00  --demod_use_ground                      true
% 11.86/2.00  --sup_to_prop_solver                    passive
% 11.86/2.00  --sup_prop_simpl_new                    true
% 11.86/2.00  --sup_prop_simpl_given                  true
% 11.86/2.00  --sup_fun_splitting                     true
% 11.86/2.00  --sup_smt_interval                      50000
% 11.86/2.00  
% 11.86/2.00  ------ Superposition Simplification Setup
% 11.86/2.00  
% 11.86/2.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.86/2.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.86/2.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.86/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.86/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 11.86/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.86/2.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.86/2.00  --sup_immed_triv                        [TrivRules]
% 11.86/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.86/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.86/2.00  --sup_immed_bw_main                     []
% 11.86/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.86/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.86/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.86/2.00  --sup_input_bw                          []
% 11.86/2.00  
% 11.86/2.00  ------ Combination Options
% 11.86/2.00  
% 11.86/2.00  --comb_res_mult                         3
% 11.86/2.00  --comb_sup_mult                         2
% 11.86/2.00  --comb_inst_mult                        10
% 11.86/2.00  
% 11.86/2.00  ------ Debug Options
% 11.86/2.00  
% 11.86/2.00  --dbg_backtrace                         false
% 11.86/2.00  --dbg_dump_prop_clauses                 false
% 11.86/2.00  --dbg_dump_prop_clauses_file            -
% 11.86/2.00  --dbg_out_stat                          false
% 11.86/2.00  
% 11.86/2.00  
% 11.86/2.00  
% 11.86/2.00  
% 11.86/2.00  ------ Proving...
% 11.86/2.00  
% 11.86/2.00  
% 11.86/2.00  % SZS status Theorem for theBenchmark.p
% 11.86/2.00  
% 11.86/2.00  % SZS output start CNFRefutation for theBenchmark.p
% 11.86/2.00  
% 11.86/2.00  fof(f67,conjecture,(
% 11.86/2.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) & v2_pre_topc(X0)) => v3_pre_topc(X1,X0)) & (v3_pre_topc(X1,X0) => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))))))),
% 11.86/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.86/2.00  
% 11.86/2.00  fof(f68,negated_conjecture,(
% 11.86/2.00    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) & v2_pre_topc(X0)) => v3_pre_topc(X1,X0)) & (v3_pre_topc(X1,X0) => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))))))),
% 11.86/2.00    inference(negated_conjecture,[],[f67])).
% 11.86/2.00  
% 11.86/2.00  fof(f150,plain,(
% 11.86/2.00    ? [X0] : (? [X1] : (((~v3_pre_topc(X1,X0) & (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) & v2_pre_topc(X0))) | (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) & v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 11.86/2.00    inference(ennf_transformation,[],[f68])).
% 11.86/2.00  
% 11.86/2.00  fof(f151,plain,(
% 11.86/2.00    ? [X0] : (? [X1] : (((~v3_pre_topc(X1,X0) & k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) & v2_pre_topc(X0)) | (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) & v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 11.86/2.00    inference(flattening,[],[f150])).
% 11.86/2.00  
% 11.86/2.00  fof(f213,plain,(
% 11.86/2.00    ( ! [X0] : (? [X1] : (((~v3_pre_topc(X1,X0) & k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) & v2_pre_topc(X0)) | (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) & v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (((~v3_pre_topc(sK21,X0) & k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),sK21) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),sK21)) & v2_pre_topc(X0)) | (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),sK21) != k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),sK21)) & v3_pre_topc(sK21,X0))) & m1_subset_1(sK21,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 11.86/2.00    introduced(choice_axiom,[])).
% 11.86/2.00  
% 11.86/2.00  fof(f212,plain,(
% 11.86/2.00    ? [X0] : (? [X1] : (((~v3_pre_topc(X1,X0) & k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) & v2_pre_topc(X0)) | (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) & v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (((~v3_pre_topc(X1,sK20) & k7_subset_1(u1_struct_0(sK20),k2_struct_0(sK20),X1) = k2_pre_topc(sK20,k7_subset_1(u1_struct_0(sK20),k2_struct_0(sK20),X1)) & v2_pre_topc(sK20)) | (k7_subset_1(u1_struct_0(sK20),k2_struct_0(sK20),X1) != k2_pre_topc(sK20,k7_subset_1(u1_struct_0(sK20),k2_struct_0(sK20),X1)) & v3_pre_topc(X1,sK20))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK20)))) & l1_pre_topc(sK20))),
% 11.86/2.00    introduced(choice_axiom,[])).
% 11.86/2.00  
% 11.86/2.00  fof(f214,plain,(
% 11.86/2.00    (((~v3_pre_topc(sK21,sK20) & k7_subset_1(u1_struct_0(sK20),k2_struct_0(sK20),sK21) = k2_pre_topc(sK20,k7_subset_1(u1_struct_0(sK20),k2_struct_0(sK20),sK21)) & v2_pre_topc(sK20)) | (k7_subset_1(u1_struct_0(sK20),k2_struct_0(sK20),sK21) != k2_pre_topc(sK20,k7_subset_1(u1_struct_0(sK20),k2_struct_0(sK20),sK21)) & v3_pre_topc(sK21,sK20))) & m1_subset_1(sK21,k1_zfmisc_1(u1_struct_0(sK20)))) & l1_pre_topc(sK20)),
% 11.86/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK20,sK21])],[f151,f213,f212])).
% 11.86/2.00  
% 11.86/2.00  fof(f340,plain,(
% 11.86/2.00    m1_subset_1(sK21,k1_zfmisc_1(u1_struct_0(sK20)))),
% 11.86/2.00    inference(cnf_transformation,[],[f214])).
% 11.86/2.00  
% 11.86/2.00  fof(f29,axiom,(
% 11.86/2.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 11.86/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.86/2.00  
% 11.86/2.00  fof(f171,plain,(
% 11.86/2.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 11.86/2.00    inference(nnf_transformation,[],[f29])).
% 11.86/2.00  
% 11.86/2.00  fof(f257,plain,(
% 11.86/2.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 11.86/2.00    inference(cnf_transformation,[],[f171])).
% 11.86/2.00  
% 11.86/2.00  fof(f13,axiom,(
% 11.86/2.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 11.86/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.86/2.00  
% 11.86/2.00  fof(f74,plain,(
% 11.86/2.00    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.86/2.00    inference(ennf_transformation,[],[f13])).
% 11.86/2.00  
% 11.86/2.00  fof(f237,plain,(
% 11.86/2.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.86/2.00    inference(cnf_transformation,[],[f74])).
% 11.86/2.00  
% 11.86/2.00  fof(f258,plain,(
% 11.86/2.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 11.86/2.00    inference(cnf_transformation,[],[f171])).
% 11.86/2.00  
% 11.86/2.00  fof(f14,axiom,(
% 11.86/2.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 11.86/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.86/2.00  
% 11.86/2.00  fof(f75,plain,(
% 11.86/2.00    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.86/2.00    inference(ennf_transformation,[],[f14])).
% 11.86/2.00  
% 11.86/2.00  fof(f238,plain,(
% 11.86/2.00    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.86/2.00    inference(cnf_transformation,[],[f75])).
% 11.86/2.00  
% 11.86/2.00  fof(f65,axiom,(
% 11.86/2.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 11.86/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.86/2.00  
% 11.86/2.00  fof(f146,plain,(
% 11.86/2.00    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.86/2.00    inference(ennf_transformation,[],[f65])).
% 11.86/2.00  
% 11.86/2.00  fof(f147,plain,(
% 11.86/2.00    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.86/2.00    inference(flattening,[],[f146])).
% 11.86/2.00  
% 11.86/2.00  fof(f336,plain,(
% 11.86/2.00    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.86/2.00    inference(cnf_transformation,[],[f147])).
% 11.86/2.00  
% 11.86/2.00  fof(f2,axiom,(
% 11.86/2.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.86/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.86/2.00  
% 11.86/2.00  fof(f158,plain,(
% 11.86/2.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.86/2.00    inference(nnf_transformation,[],[f2])).
% 11.86/2.00  
% 11.86/2.00  fof(f159,plain,(
% 11.86/2.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.86/2.00    inference(flattening,[],[f158])).
% 11.86/2.00  
% 11.86/2.00  fof(f217,plain,(
% 11.86/2.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 11.86/2.00    inference(cnf_transformation,[],[f159])).
% 11.86/2.00  
% 11.86/2.00  fof(f353,plain,(
% 11.86/2.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 11.86/2.00    inference(equality_resolution,[],[f217])).
% 11.86/2.00  
% 11.86/2.00  fof(f19,axiom,(
% 11.86/2.00    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 11.86/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.86/2.00  
% 11.86/2.00  fof(f81,plain,(
% 11.86/2.00    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.86/2.00    inference(ennf_transformation,[],[f19])).
% 11.86/2.00  
% 11.86/2.00  fof(f244,plain,(
% 11.86/2.00    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.86/2.00    inference(cnf_transformation,[],[f81])).
% 11.86/2.00  
% 11.86/2.00  fof(f22,axiom,(
% 11.86/2.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 11.86/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.86/2.00  
% 11.86/2.00  fof(f85,plain,(
% 11.86/2.00    ! [X0,X1] : (k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.86/2.00    inference(ennf_transformation,[],[f22])).
% 11.86/2.00  
% 11.86/2.00  fof(f248,plain,(
% 11.86/2.00    ( ! [X0,X1] : (k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.86/2.00    inference(cnf_transformation,[],[f85])).
% 11.86/2.00  
% 11.86/2.00  fof(f12,axiom,(
% 11.86/2.00    ! [X0] : k2_subset_1(X0) = X0),
% 11.86/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.86/2.00  
% 11.86/2.00  fof(f236,plain,(
% 11.86/2.00    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 11.86/2.00    inference(cnf_transformation,[],[f12])).
% 11.86/2.00  
% 11.86/2.00  fof(f47,axiom,(
% 11.86/2.00    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 11.86/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.86/2.00  
% 11.86/2.00  fof(f119,plain,(
% 11.86/2.00    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 11.86/2.00    inference(ennf_transformation,[],[f47])).
% 11.86/2.00  
% 11.86/2.00  fof(f309,plain,(
% 11.86/2.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 11.86/2.00    inference(cnf_transformation,[],[f119])).
% 11.86/2.00  
% 11.86/2.00  fof(f60,axiom,(
% 11.86/2.00    ! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) = k2_struct_0(X0)))),
% 11.86/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.86/2.00  
% 11.86/2.00  fof(f140,plain,(
% 11.86/2.00    ! [X0] : (! [X1] : (k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) = k2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_struct_0(X0))),
% 11.86/2.00    inference(ennf_transformation,[],[f60])).
% 11.86/2.00  
% 11.86/2.00  fof(f330,plain,(
% 11.86/2.00    ( ! [X0,X1] : (k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) = k2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0)) )),
% 11.86/2.00    inference(cnf_transformation,[],[f140])).
% 11.86/2.00  
% 11.86/2.00  fof(f339,plain,(
% 11.86/2.00    l1_pre_topc(sK20)),
% 11.86/2.00    inference(cnf_transformation,[],[f214])).
% 11.86/2.00  
% 11.86/2.00  fof(f346,plain,(
% 11.86/2.00    ~v3_pre_topc(sK21,sK20) | k7_subset_1(u1_struct_0(sK20),k2_struct_0(sK20),sK21) != k2_pre_topc(sK20,k7_subset_1(u1_struct_0(sK20),k2_struct_0(sK20),sK21))),
% 11.86/2.00    inference(cnf_transformation,[],[f214])).
% 11.86/2.00  
% 11.86/2.00  fof(f61,axiom,(
% 11.86/2.00    ! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1))),
% 11.86/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.86/2.00  
% 11.86/2.00  fof(f141,plain,(
% 11.86/2.00    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_struct_0(X0))),
% 11.86/2.00    inference(ennf_transformation,[],[f61])).
% 11.86/2.00  
% 11.86/2.00  fof(f331,plain,(
% 11.86/2.00    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0)) )),
% 11.86/2.00    inference(cnf_transformation,[],[f141])).
% 11.86/2.00  
% 11.86/2.00  fof(f43,axiom,(
% 11.86/2.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0))))),
% 11.86/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.86/2.00  
% 11.86/2.00  fof(f113,plain,(
% 11.86/2.00    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.86/2.00    inference(ennf_transformation,[],[f43])).
% 11.86/2.00  
% 11.86/2.00  fof(f193,plain,(
% 11.86/2.00    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | ~v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)) & (v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.86/2.00    inference(nnf_transformation,[],[f113])).
% 11.86/2.00  
% 11.86/2.00  fof(f292,plain,(
% 11.86/2.00    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.86/2.00    inference(cnf_transformation,[],[f193])).
% 11.86/2.00  
% 11.86/2.00  fof(f343,plain,(
% 11.86/2.00    k7_subset_1(u1_struct_0(sK20),k2_struct_0(sK20),sK21) = k2_pre_topc(sK20,k7_subset_1(u1_struct_0(sK20),k2_struct_0(sK20),sK21)) | v3_pre_topc(sK21,sK20)),
% 11.86/2.00    inference(cnf_transformation,[],[f214])).
% 11.86/2.00  
% 11.86/2.00  fof(f42,axiom,(
% 11.86/2.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 11.86/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.86/2.00  
% 11.86/2.00  fof(f112,plain,(
% 11.86/2.00    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.86/2.00    inference(ennf_transformation,[],[f42])).
% 11.86/2.00  
% 11.86/2.00  fof(f192,plain,(
% 11.86/2.00    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0))) & (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.86/2.00    inference(nnf_transformation,[],[f112])).
% 11.86/2.00  
% 11.86/2.00  fof(f289,plain,(
% 11.86/2.00    ( ! [X0,X1] : (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.86/2.00    inference(cnf_transformation,[],[f192])).
% 11.86/2.00  
% 11.86/2.00  fof(f8,axiom,(
% 11.86/2.00    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 11.86/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.86/2.00  
% 11.86/2.00  fof(f161,plain,(
% 11.86/2.00    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)))),
% 11.86/2.00    inference(nnf_transformation,[],[f8])).
% 11.86/2.00  
% 11.86/2.00  fof(f228,plain,(
% 11.86/2.00    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 11.86/2.00    inference(cnf_transformation,[],[f161])).
% 11.86/2.00  
% 11.86/2.00  fof(f46,axiom,(
% 11.86/2.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 11.86/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.86/2.00  
% 11.86/2.00  fof(f117,plain,(
% 11.86/2.00    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 11.86/2.00    inference(ennf_transformation,[],[f46])).
% 11.86/2.00  
% 11.86/2.00  fof(f118,plain,(
% 11.86/2.00    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 11.86/2.00    inference(flattening,[],[f117])).
% 11.86/2.00  
% 11.86/2.00  fof(f308,plain,(
% 11.86/2.00    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.86/2.00    inference(cnf_transformation,[],[f118])).
% 11.86/2.00  
% 11.86/2.00  fof(f11,axiom,(
% 11.86/2.00    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 11.86/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.86/2.00  
% 11.86/2.00  fof(f73,plain,(
% 11.86/2.00    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 11.86/2.00    inference(ennf_transformation,[],[f11])).
% 11.86/2.00  
% 11.86/2.00  fof(f163,plain,(
% 11.86/2.00    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 11.86/2.00    inference(nnf_transformation,[],[f73])).
% 11.86/2.00  
% 11.86/2.00  fof(f235,plain,(
% 11.86/2.00    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 11.86/2.00    inference(cnf_transformation,[],[f163])).
% 11.86/2.00  
% 11.86/2.00  fof(f40,axiom,(
% 11.86/2.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_pre_topc(X2)) => (k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1))))),
% 11.86/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.86/2.00  
% 11.86/2.00  fof(f108,plain,(
% 11.86/2.00    ! [X0] : (! [X1] : (! [X2] : ((k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1) | (~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.86/2.00    inference(ennf_transformation,[],[f40])).
% 11.86/2.00  
% 11.86/2.00  fof(f109,plain,(
% 11.86/2.00    ! [X0] : (! [X1] : (! [X2] : ((k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.86/2.00    inference(flattening,[],[f108])).
% 11.86/2.00  
% 11.86/2.00  fof(f181,plain,(
% 11.86/2.00    ! [X0] : (! [X1] : (! [X2] : (((k1_pre_topc(X0,X1) = X2 | k2_struct_0(X2) != X1) & (k2_struct_0(X2) = X1 | k1_pre_topc(X0,X1) != X2)) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.86/2.00    inference(nnf_transformation,[],[f109])).
% 11.86/2.00  
% 11.86/2.00  fof(f275,plain,(
% 11.86/2.00    ( ! [X2,X0,X1] : (k2_struct_0(X2) = X1 | k1_pre_topc(X0,X1) != X2 | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.86/2.00    inference(cnf_transformation,[],[f181])).
% 11.86/2.00  
% 11.86/2.00  fof(f357,plain,(
% 11.86/2.00    ( ! [X0,X1] : (k2_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~v1_pre_topc(k1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.86/2.00    inference(equality_resolution,[],[f275])).
% 11.86/2.00  
% 11.86/2.00  fof(f45,axiom,(
% 11.86/2.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => (m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))))),
% 11.86/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.86/2.00  
% 11.86/2.00  fof(f115,plain,(
% 11.86/2.00    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 11.86/2.00    inference(ennf_transformation,[],[f45])).
% 11.86/2.00  
% 11.86/2.00  fof(f116,plain,(
% 11.86/2.00    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 11.86/2.00    inference(flattening,[],[f115])).
% 11.86/2.00  
% 11.86/2.00  fof(f307,plain,(
% 11.86/2.00    ( ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.86/2.00    inference(cnf_transformation,[],[f116])).
% 11.86/2.00  
% 11.86/2.00  fof(f306,plain,(
% 11.86/2.00    ( ! [X0,X1] : (v1_pre_topc(k1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.86/2.00    inference(cnf_transformation,[],[f116])).
% 11.86/2.00  
% 11.86/2.00  fof(f154,plain,(
% 11.86/2.00    ! [X1,X0] : (sP1(X1,X0) <=> (! [X2] : ((r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))))),
% 11.86/2.00    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 11.86/2.00  
% 11.86/2.00  fof(f195,plain,(
% 11.86/2.00    ! [X1,X0] : ((sP1(X1,X0) | (? [X2] : (((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,u1_pre_topc(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) & ((! [X2] : (((r2_hidden(X2,u1_pre_topc(X1)) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~sP1(X1,X0)))),
% 11.86/2.00    inference(nnf_transformation,[],[f154])).
% 11.86/2.00  
% 11.86/2.00  fof(f196,plain,(
% 11.86/2.00    ! [X1,X0] : ((sP1(X1,X0) | ? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,u1_pre_topc(X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) & ((! [X2] : (((r2_hidden(X2,u1_pre_topc(X1)) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~sP1(X1,X0)))),
% 11.86/2.00    inference(flattening,[],[f195])).
% 11.86/2.00  
% 11.86/2.00  fof(f197,plain,(
% 11.86/2.00    ! [X0,X1] : ((sP1(X0,X1) | ? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != X2 | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X2,u1_pre_topc(X0))) & (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2 & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(X2,u1_pre_topc(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) & ((! [X5] : (((r2_hidden(X5,u1_pre_topc(X0)) | ! [X6] : (k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5 | ~r2_hidden(X6,u1_pre_topc(X1)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))))) & (? [X7] : (k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5 & r2_hidden(X7,u1_pre_topc(X1)) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X5,u1_pre_topc(X0)))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) | ~sP1(X0,X1)))),
% 11.86/2.00    inference(rectify,[],[f196])).
% 11.86/2.00  
% 11.86/2.00  fof(f200,plain,(
% 11.86/2.00    ! [X5,X1,X0] : (? [X7] : (k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5 & r2_hidden(X7,u1_pre_topc(X1)) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))) => (k9_subset_1(u1_struct_0(X0),sK14(X0,X1,X5),k2_struct_0(X0)) = X5 & r2_hidden(sK14(X0,X1,X5),u1_pre_topc(X1)) & m1_subset_1(sK14(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1)))))),
% 11.86/2.00    introduced(choice_axiom,[])).
% 11.86/2.00  
% 11.86/2.00  fof(f199,plain,(
% 11.86/2.00    ( ! [X2] : (! [X1,X0] : (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2 & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) => (k9_subset_1(u1_struct_0(X0),sK13(X0,X1),k2_struct_0(X0)) = X2 & r2_hidden(sK13(X0,X1),u1_pre_topc(X1)) & m1_subset_1(sK13(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))))) )),
% 11.86/2.00    introduced(choice_axiom,[])).
% 11.86/2.00  
% 11.86/2.00  fof(f198,plain,(
% 11.86/2.00    ! [X1,X0] : (? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != X2 | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X2,u1_pre_topc(X0))) & (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2 & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(X2,u1_pre_topc(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK12(X0,X1) | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(sK12(X0,X1),u1_pre_topc(X0))) & (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = sK12(X0,X1) & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(sK12(X0,X1),u1_pre_topc(X0))) & m1_subset_1(sK12(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 11.86/2.00    introduced(choice_axiom,[])).
% 11.86/2.00  
% 11.86/2.00  fof(f201,plain,(
% 11.86/2.00    ! [X0,X1] : ((sP1(X0,X1) | ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK12(X0,X1) | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(sK12(X0,X1),u1_pre_topc(X0))) & ((k9_subset_1(u1_struct_0(X0),sK13(X0,X1),k2_struct_0(X0)) = sK12(X0,X1) & r2_hidden(sK13(X0,X1),u1_pre_topc(X1)) & m1_subset_1(sK13(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(sK12(X0,X1),u1_pre_topc(X0))) & m1_subset_1(sK12(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) & ((! [X5] : (((r2_hidden(X5,u1_pre_topc(X0)) | ! [X6] : (k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5 | ~r2_hidden(X6,u1_pre_topc(X1)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))))) & ((k9_subset_1(u1_struct_0(X0),sK14(X0,X1,X5),k2_struct_0(X0)) = X5 & r2_hidden(sK14(X0,X1,X5),u1_pre_topc(X1)) & m1_subset_1(sK14(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X5,u1_pre_topc(X0)))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) | ~sP1(X0,X1)))),
% 11.86/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12,sK13,sK14])],[f197,f200,f199,f198])).
% 11.86/2.00  
% 11.86/2.00  fof(f299,plain,(
% 11.86/2.00    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,u1_pre_topc(X0)) | k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5 | ~r2_hidden(X6,u1_pre_topc(X1)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) | ~sP1(X0,X1)) )),
% 11.86/2.00    inference(cnf_transformation,[],[f201])).
% 11.86/2.00  
% 11.86/2.00  fof(f358,plain,(
% 11.86/2.00    ( ! [X6,X0,X1] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)),u1_pre_topc(X0)) | ~r2_hidden(X6,u1_pre_topc(X1)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0))) | ~sP1(X0,X1)) )),
% 11.86/2.00    inference(equality_resolution,[],[f299])).
% 11.86/2.00  
% 11.86/2.00  fof(f337,plain,(
% 11.86/2.00    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.86/2.00    inference(cnf_transformation,[],[f147])).
% 11.86/2.00  
% 11.86/2.00  fof(f341,plain,(
% 11.86/2.00    v2_pre_topc(sK20) | v3_pre_topc(sK21,sK20)),
% 11.86/2.00    inference(cnf_transformation,[],[f214])).
% 11.86/2.00  
% 11.86/2.00  fof(f291,plain,(
% 11.86/2.00    ( ! [X0,X1] : (v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.86/2.00    inference(cnf_transformation,[],[f193])).
% 11.86/2.00  
% 11.86/2.00  fof(f227,plain,(
% 11.86/2.00    ( ! [X0,X1] : (r2_hidden(X0,X1) | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)) )),
% 11.86/2.00    inference(cnf_transformation,[],[f161])).
% 11.86/2.00  
% 11.86/2.00  fof(f290,plain,(
% 11.86/2.00    ( ! [X0,X1] : (v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.86/2.00    inference(cnf_transformation,[],[f192])).
% 11.86/2.00  
% 11.86/2.00  cnf(c_129,negated_conjecture,
% 11.86/2.00      ( m1_subset_1(sK21,k1_zfmisc_1(u1_struct_0(sK20))) ),
% 11.86/2.00      inference(cnf_transformation,[],[f340]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_10102,plain,
% 11.86/2.00      ( m1_subset_1(sK21,k1_zfmisc_1(u1_struct_0(sK20))) = iProver_top ),
% 11.86/2.00      inference(predicate_to_equality,[status(thm)],[c_129]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_42,plain,
% 11.86/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 11.86/2.00      inference(cnf_transformation,[],[f257]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_10162,plain,
% 11.86/2.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 11.86/2.00      | r1_tarski(X0,X1) = iProver_top ),
% 11.86/2.00      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_12185,plain,
% 11.86/2.00      ( r1_tarski(sK21,u1_struct_0(sK20)) = iProver_top ),
% 11.86/2.00      inference(superposition,[status(thm)],[c_10102,c_10162]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_21,plain,
% 11.86/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.86/2.00      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 11.86/2.00      inference(cnf_transformation,[],[f237]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_41,plain,
% 11.86/2.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 11.86/2.00      inference(cnf_transformation,[],[f258]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_1068,plain,
% 11.86/2.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 11.86/2.00      inference(prop_impl,[status(thm)],[c_41]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_1069,plain,
% 11.86/2.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 11.86/2.00      inference(renaming,[status(thm)],[c_1068]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_1273,plain,
% 11.86/2.00      ( ~ r1_tarski(X0,X1) | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 11.86/2.00      inference(bin_hyper_res,[status(thm)],[c_21,c_1069]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_10099,plain,
% 11.86/2.00      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 11.86/2.00      | r1_tarski(X1,X0) != iProver_top ),
% 11.86/2.00      inference(predicate_to_equality,[status(thm)],[c_1273]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_13374,plain,
% 11.86/2.00      ( k3_subset_1(u1_struct_0(sK20),sK21) = k4_xboole_0(u1_struct_0(sK20),sK21) ),
% 11.86/2.00      inference(superposition,[status(thm)],[c_12185,c_10099]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_22,plain,
% 11.86/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.86/2.00      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 11.86/2.00      inference(cnf_transformation,[],[f238]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_1274,plain,
% 11.86/2.00      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
% 11.86/2.00      | ~ r1_tarski(X1,X0) ),
% 11.86/2.00      inference(bin_hyper_res,[status(thm)],[c_22,c_1069]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_10098,plain,
% 11.86/2.00      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) = iProver_top
% 11.86/2.00      | r1_tarski(X1,X0) != iProver_top ),
% 11.86/2.00      inference(predicate_to_equality,[status(thm)],[c_1274]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_50792,plain,
% 11.86/2.00      ( m1_subset_1(k4_xboole_0(u1_struct_0(sK20),sK21),k1_zfmisc_1(u1_struct_0(sK20))) = iProver_top
% 11.86/2.00      | r1_tarski(sK21,u1_struct_0(sK20)) != iProver_top ),
% 11.86/2.00      inference(superposition,[status(thm)],[c_13374,c_10098]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_51100,plain,
% 11.86/2.00      ( m1_subset_1(k4_xboole_0(u1_struct_0(sK20),sK21),k1_zfmisc_1(u1_struct_0(sK20))) = iProver_top ),
% 11.86/2.00      inference(global_propositional_subsumption,
% 11.86/2.00                [status(thm)],
% 11.86/2.00                [c_50792,c_12185]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_121,plain,
% 11.86/2.00      ( ~ v4_pre_topc(X0,X1)
% 11.86/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.86/2.00      | ~ l1_pre_topc(X1)
% 11.86/2.00      | k2_pre_topc(X1,X0) = X0 ),
% 11.86/2.00      inference(cnf_transformation,[],[f336]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_10107,plain,
% 11.86/2.00      ( k2_pre_topc(X0,X1) = X1
% 11.86/2.00      | v4_pre_topc(X1,X0) != iProver_top
% 11.86/2.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 11.86/2.00      | l1_pre_topc(X0) != iProver_top ),
% 11.86/2.00      inference(predicate_to_equality,[status(thm)],[c_121]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_51110,plain,
% 11.86/2.00      ( k2_pre_topc(sK20,k4_xboole_0(u1_struct_0(sK20),sK21)) = k4_xboole_0(u1_struct_0(sK20),sK21)
% 11.86/2.00      | v4_pre_topc(k4_xboole_0(u1_struct_0(sK20),sK21),sK20) != iProver_top
% 11.86/2.00      | l1_pre_topc(sK20) != iProver_top ),
% 11.86/2.00      inference(superposition,[status(thm)],[c_51100,c_10107]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_4,plain,
% 11.86/2.00      ( r1_tarski(X0,X0) ),
% 11.86/2.00      inference(cnf_transformation,[],[f353]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_10181,plain,
% 11.86/2.00      ( r1_tarski(X0,X0) = iProver_top ),
% 11.86/2.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_28,plain,
% 11.86/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.86/2.00      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 11.86/2.00      inference(cnf_transformation,[],[f244]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_1278,plain,
% 11.86/2.00      ( ~ r1_tarski(X0,X1) | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 11.86/2.00      inference(bin_hyper_res,[status(thm)],[c_28,c_1069]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_10095,plain,
% 11.86/2.00      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
% 11.86/2.00      | r1_tarski(X1,X0) != iProver_top ),
% 11.86/2.00      inference(predicate_to_equality,[status(thm)],[c_1278]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_49827,plain,
% 11.86/2.00      ( k7_subset_1(X0,X0,X1) = k4_xboole_0(X0,X1) ),
% 11.86/2.00      inference(superposition,[status(thm)],[c_10181,c_10095]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_32,plain,
% 11.86/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.86/2.00      | k4_subset_1(X1,X0,k3_subset_1(X1,X0)) = k2_subset_1(X1) ),
% 11.86/2.00      inference(cnf_transformation,[],[f248]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_1282,plain,
% 11.86/2.00      ( ~ r1_tarski(X0,X1)
% 11.86/2.00      | k4_subset_1(X1,X0,k3_subset_1(X1,X0)) = k2_subset_1(X1) ),
% 11.86/2.00      inference(bin_hyper_res,[status(thm)],[c_32,c_1069]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_10091,plain,
% 11.86/2.00      ( k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = k2_subset_1(X0)
% 11.86/2.00      | r1_tarski(X1,X0) != iProver_top ),
% 11.86/2.00      inference(predicate_to_equality,[status(thm)],[c_1282]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_20,plain,
% 11.86/2.00      ( k2_subset_1(X0) = X0 ),
% 11.86/2.00      inference(cnf_transformation,[],[f236]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_10186,plain,
% 11.86/2.00      ( k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0
% 11.86/2.00      | r1_tarski(X1,X0) != iProver_top ),
% 11.86/2.00      inference(light_normalisation,[status(thm)],[c_10091,c_20]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_14133,plain,
% 11.86/2.00      ( k4_subset_1(u1_struct_0(sK20),sK21,k3_subset_1(u1_struct_0(sK20),sK21)) = u1_struct_0(sK20) ),
% 11.86/2.00      inference(superposition,[status(thm)],[c_12185,c_10186]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_93,plain,
% 11.86/2.00      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 11.86/2.00      inference(cnf_transformation,[],[f309]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_114,plain,
% 11.86/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.86/2.00      | ~ l1_struct_0(X1)
% 11.86/2.00      | k4_subset_1(u1_struct_0(X1),X0,k3_subset_1(u1_struct_0(X1),X0)) = k2_struct_0(X1) ),
% 11.86/2.00      inference(cnf_transformation,[],[f330]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_1814,plain,
% 11.86/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.86/2.00      | ~ l1_pre_topc(X2)
% 11.86/2.00      | X1 != X2
% 11.86/2.00      | k4_subset_1(u1_struct_0(X1),X0,k3_subset_1(u1_struct_0(X1),X0)) = k2_struct_0(X1) ),
% 11.86/2.00      inference(resolution_lifted,[status(thm)],[c_93,c_114]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_1815,plain,
% 11.86/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.86/2.00      | ~ l1_pre_topc(X1)
% 11.86/2.00      | k4_subset_1(u1_struct_0(X1),X0,k3_subset_1(u1_struct_0(X1),X0)) = k2_struct_0(X1) ),
% 11.86/2.00      inference(unflattening,[status(thm)],[c_1814]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_10078,plain,
% 11.86/2.00      ( k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) = k2_struct_0(X0)
% 11.86/2.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 11.86/2.00      | l1_pre_topc(X0) != iProver_top ),
% 11.86/2.00      inference(predicate_to_equality,[status(thm)],[c_1815]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_10809,plain,
% 11.86/2.00      ( k4_subset_1(u1_struct_0(sK20),sK21,k3_subset_1(u1_struct_0(sK20),sK21)) = k2_struct_0(sK20)
% 11.86/2.00      | l1_pre_topc(sK20) != iProver_top ),
% 11.86/2.00      inference(superposition,[status(thm)],[c_10102,c_10078]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_130,negated_conjecture,
% 11.86/2.00      ( l1_pre_topc(sK20) ),
% 11.86/2.00      inference(cnf_transformation,[],[f339]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_131,plain,
% 11.86/2.00      ( l1_pre_topc(sK20) = iProver_top ),
% 11.86/2.00      inference(predicate_to_equality,[status(thm)],[c_130]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_11036,plain,
% 11.86/2.00      ( k4_subset_1(u1_struct_0(sK20),sK21,k3_subset_1(u1_struct_0(sK20),sK21)) = k2_struct_0(sK20) ),
% 11.86/2.00      inference(global_propositional_subsumption,
% 11.86/2.00                [status(thm)],
% 11.86/2.00                [c_10809,c_131]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_13685,plain,
% 11.86/2.00      ( k4_subset_1(u1_struct_0(sK20),sK21,k4_xboole_0(u1_struct_0(sK20),sK21)) = k2_struct_0(sK20) ),
% 11.86/2.00      inference(demodulation,[status(thm)],[c_13374,c_11036]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_14134,plain,
% 11.86/2.00      ( k2_struct_0(sK20) = u1_struct_0(sK20) ),
% 11.86/2.00      inference(light_normalisation,
% 11.86/2.00                [status(thm)],
% 11.86/2.00                [c_14133,c_13374,c_13685]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_123,negated_conjecture,
% 11.86/2.00      ( ~ v3_pre_topc(sK21,sK20)
% 11.86/2.00      | k7_subset_1(u1_struct_0(sK20),k2_struct_0(sK20),sK21) != k2_pre_topc(sK20,k7_subset_1(u1_struct_0(sK20),k2_struct_0(sK20),sK21)) ),
% 11.86/2.00      inference(cnf_transformation,[],[f346]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_10105,plain,
% 11.86/2.00      ( k7_subset_1(u1_struct_0(sK20),k2_struct_0(sK20),sK21) != k2_pre_topc(sK20,k7_subset_1(u1_struct_0(sK20),k2_struct_0(sK20),sK21))
% 11.86/2.00      | v3_pre_topc(sK21,sK20) != iProver_top ),
% 11.86/2.00      inference(predicate_to_equality,[status(thm)],[c_123]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_14217,plain,
% 11.86/2.00      ( k2_pre_topc(sK20,k7_subset_1(u1_struct_0(sK20),u1_struct_0(sK20),sK21)) != k7_subset_1(u1_struct_0(sK20),u1_struct_0(sK20),sK21)
% 11.86/2.00      | v3_pre_topc(sK21,sK20) != iProver_top ),
% 11.86/2.00      inference(demodulation,[status(thm)],[c_14134,c_10105]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_49907,plain,
% 11.86/2.00      ( k2_pre_topc(sK20,k4_xboole_0(u1_struct_0(sK20),sK21)) != k4_xboole_0(u1_struct_0(sK20),sK21)
% 11.86/2.00      | v3_pre_topc(sK21,sK20) != iProver_top ),
% 11.86/2.00      inference(demodulation,[status(thm)],[c_49827,c_14217]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_49939,plain,
% 11.86/2.00      ( ~ v3_pre_topc(sK21,sK20)
% 11.86/2.00      | k2_pre_topc(sK20,k4_xboole_0(u1_struct_0(sK20),sK21)) != k4_xboole_0(u1_struct_0(sK20),sK21) ),
% 11.86/2.00      inference(predicate_to_equality_rev,[status(thm)],[c_49907]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_115,plain,
% 11.86/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.86/2.00      | ~ l1_struct_0(X1)
% 11.86/2.00      | k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0)) = X0 ),
% 11.86/2.00      inference(cnf_transformation,[],[f331]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_1799,plain,
% 11.86/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.86/2.00      | ~ l1_pre_topc(X2)
% 11.86/2.00      | X1 != X2
% 11.86/2.00      | k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0)) = X0 ),
% 11.86/2.00      inference(resolution_lifted,[status(thm)],[c_93,c_115]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_1800,plain,
% 11.86/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.86/2.00      | ~ l1_pre_topc(X1)
% 11.86/2.00      | k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0)) = X0 ),
% 11.86/2.00      inference(unflattening,[status(thm)],[c_1799]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_10079,plain,
% 11.86/2.00      ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1
% 11.86/2.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 11.86/2.00      | l1_pre_topc(X0) != iProver_top ),
% 11.86/2.00      inference(predicate_to_equality,[status(thm)],[c_1800]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_11388,plain,
% 11.86/2.00      ( k7_subset_1(u1_struct_0(sK20),k2_struct_0(sK20),k7_subset_1(u1_struct_0(sK20),k2_struct_0(sK20),sK21)) = sK21
% 11.86/2.00      | l1_pre_topc(sK20) != iProver_top ),
% 11.86/2.00      inference(superposition,[status(thm)],[c_10102,c_10079]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_11800,plain,
% 11.86/2.00      ( k7_subset_1(u1_struct_0(sK20),k2_struct_0(sK20),k7_subset_1(u1_struct_0(sK20),k2_struct_0(sK20),sK21)) = sK21 ),
% 11.86/2.00      inference(global_propositional_subsumption,
% 11.86/2.00                [status(thm)],
% 11.86/2.00                [c_11388,c_131]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_14215,plain,
% 11.86/2.00      ( k7_subset_1(u1_struct_0(sK20),u1_struct_0(sK20),k7_subset_1(u1_struct_0(sK20),u1_struct_0(sK20),sK21)) = sK21 ),
% 11.86/2.00      inference(demodulation,[status(thm)],[c_14134,c_11800]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_75,plain,
% 11.86/2.00      ( v4_pre_topc(X0,X1)
% 11.86/2.00      | ~ v3_pre_topc(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0),X1)
% 11.86/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.86/2.00      | ~ l1_pre_topc(X1) ),
% 11.86/2.00      inference(cnf_transformation,[],[f292]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_10138,plain,
% 11.86/2.00      ( v4_pre_topc(X0,X1) = iProver_top
% 11.86/2.00      | v3_pre_topc(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0),X1) != iProver_top
% 11.86/2.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 11.86/2.00      | l1_pre_topc(X1) != iProver_top ),
% 11.86/2.00      inference(predicate_to_equality,[status(thm)],[c_75]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_24013,plain,
% 11.86/2.00      ( v4_pre_topc(X0,sK20) = iProver_top
% 11.86/2.00      | v3_pre_topc(k7_subset_1(u1_struct_0(sK20),u1_struct_0(sK20),X0),sK20) != iProver_top
% 11.86/2.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK20))) != iProver_top
% 11.86/2.00      | l1_pre_topc(sK20) != iProver_top ),
% 11.86/2.00      inference(superposition,[status(thm)],[c_14134,c_10138]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_26391,plain,
% 11.86/2.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK20))) != iProver_top
% 11.86/2.00      | v3_pre_topc(k7_subset_1(u1_struct_0(sK20),u1_struct_0(sK20),X0),sK20) != iProver_top
% 11.86/2.00      | v4_pre_topc(X0,sK20) = iProver_top ),
% 11.86/2.00      inference(global_propositional_subsumption,
% 11.86/2.00                [status(thm)],
% 11.86/2.00                [c_24013,c_131]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_26392,plain,
% 11.86/2.00      ( v4_pre_topc(X0,sK20) = iProver_top
% 11.86/2.00      | v3_pre_topc(k7_subset_1(u1_struct_0(sK20),u1_struct_0(sK20),X0),sK20) != iProver_top
% 11.86/2.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK20))) != iProver_top ),
% 11.86/2.00      inference(renaming,[status(thm)],[c_26391]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_26398,plain,
% 11.86/2.00      ( v4_pre_topc(k7_subset_1(u1_struct_0(sK20),u1_struct_0(sK20),sK21),sK20) = iProver_top
% 11.86/2.00      | v3_pre_topc(sK21,sK20) != iProver_top
% 11.86/2.00      | m1_subset_1(k7_subset_1(u1_struct_0(sK20),u1_struct_0(sK20),sK21),k1_zfmisc_1(u1_struct_0(sK20))) != iProver_top ),
% 11.86/2.00      inference(superposition,[status(thm)],[c_14215,c_26392]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_49896,plain,
% 11.86/2.00      ( v4_pre_topc(k4_xboole_0(u1_struct_0(sK20),sK21),sK20) = iProver_top
% 11.86/2.00      | v3_pre_topc(sK21,sK20) != iProver_top
% 11.86/2.00      | m1_subset_1(k4_xboole_0(u1_struct_0(sK20),sK21),k1_zfmisc_1(u1_struct_0(sK20))) != iProver_top ),
% 11.86/2.00      inference(demodulation,[status(thm)],[c_49827,c_26398]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_126,negated_conjecture,
% 11.86/2.00      ( v3_pre_topc(sK21,sK20)
% 11.86/2.00      | k7_subset_1(u1_struct_0(sK20),k2_struct_0(sK20),sK21) = k2_pre_topc(sK20,k7_subset_1(u1_struct_0(sK20),k2_struct_0(sK20),sK21)) ),
% 11.86/2.00      inference(cnf_transformation,[],[f343]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_10104,plain,
% 11.86/2.00      ( k7_subset_1(u1_struct_0(sK20),k2_struct_0(sK20),sK21) = k2_pre_topc(sK20,k7_subset_1(u1_struct_0(sK20),k2_struct_0(sK20),sK21))
% 11.86/2.00      | v3_pre_topc(sK21,sK20) = iProver_top ),
% 11.86/2.00      inference(predicate_to_equality,[status(thm)],[c_126]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_14216,plain,
% 11.86/2.00      ( k2_pre_topc(sK20,k7_subset_1(u1_struct_0(sK20),u1_struct_0(sK20),sK21)) = k7_subset_1(u1_struct_0(sK20),u1_struct_0(sK20),sK21)
% 11.86/2.00      | v3_pre_topc(sK21,sK20) = iProver_top ),
% 11.86/2.00      inference(demodulation,[status(thm)],[c_14134,c_10104]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_74,plain,
% 11.86/2.00      ( ~ v3_pre_topc(X0,X1)
% 11.86/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.86/2.00      | r2_hidden(X0,u1_pre_topc(X1))
% 11.86/2.00      | ~ l1_pre_topc(X1) ),
% 11.86/2.00      inference(cnf_transformation,[],[f289]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_10139,plain,
% 11.86/2.00      ( v3_pre_topc(X0,X1) != iProver_top
% 11.86/2.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 11.86/2.00      | r2_hidden(X0,u1_pre_topc(X1)) = iProver_top
% 11.86/2.00      | l1_pre_topc(X1) != iProver_top ),
% 11.86/2.00      inference(predicate_to_equality,[status(thm)],[c_74]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_22161,plain,
% 11.86/2.00      ( v3_pre_topc(sK21,sK20) != iProver_top
% 11.86/2.00      | r2_hidden(sK21,u1_pre_topc(sK20)) = iProver_top
% 11.86/2.00      | l1_pre_topc(sK20) != iProver_top ),
% 11.86/2.00      inference(superposition,[status(thm)],[c_10102,c_10139]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_22805,plain,
% 11.86/2.00      ( r2_hidden(sK21,u1_pre_topc(sK20)) = iProver_top
% 11.86/2.00      | v3_pre_topc(sK21,sK20) != iProver_top ),
% 11.86/2.00      inference(global_propositional_subsumption,
% 11.86/2.00                [status(thm)],
% 11.86/2.00                [c_22161,c_131]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_22806,plain,
% 11.86/2.00      ( v3_pre_topc(sK21,sK20) != iProver_top
% 11.86/2.00      | r2_hidden(sK21,u1_pre_topc(sK20)) = iProver_top ),
% 11.86/2.00      inference(renaming,[status(thm)],[c_22805]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_11,plain,
% 11.86/2.00      ( ~ r2_hidden(X0,X1)
% 11.86/2.00      | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 ),
% 11.86/2.00      inference(cnf_transformation,[],[f228]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_10176,plain,
% 11.86/2.00      ( k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
% 11.86/2.00      | r2_hidden(X0,X1) != iProver_top ),
% 11.86/2.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_22809,plain,
% 11.86/2.00      ( k4_xboole_0(k1_tarski(sK21),u1_pre_topc(sK20)) = k1_xboole_0
% 11.86/2.00      | v3_pre_topc(sK21,sK20) != iProver_top ),
% 11.86/2.00      inference(superposition,[status(thm)],[c_22806,c_10176]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_23347,plain,
% 11.86/2.00      ( k2_pre_topc(sK20,k7_subset_1(u1_struct_0(sK20),u1_struct_0(sK20),sK21)) = k7_subset_1(u1_struct_0(sK20),u1_struct_0(sK20),sK21)
% 11.86/2.00      | k4_xboole_0(k1_tarski(sK21),u1_pre_topc(sK20)) = k1_xboole_0 ),
% 11.86/2.00      inference(superposition,[status(thm)],[c_14216,c_22809]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_92,plain,
% 11.86/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.86/2.00      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 11.86/2.00      | ~ l1_pre_topc(X1) ),
% 11.86/2.00      inference(cnf_transformation,[],[f308]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_10124,plain,
% 11.86/2.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 11.86/2.00      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 11.86/2.00      | l1_pre_topc(X1) != iProver_top ),
% 11.86/2.00      inference(predicate_to_equality,[status(thm)],[c_92]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_16,plain,
% 11.86/2.00      ( m1_subset_1(X0,X1) | ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) ),
% 11.86/2.00      inference(cnf_transformation,[],[f235]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_10171,plain,
% 11.86/2.00      ( m1_subset_1(X0,X1) = iProver_top
% 11.86/2.00      | v1_xboole_0(X0) != iProver_top
% 11.86/2.00      | v1_xboole_0(X1) != iProver_top ),
% 11.86/2.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_60,plain,
% 11.86/2.00      ( ~ m1_pre_topc(k1_pre_topc(X0,X1),X0)
% 11.86/2.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 11.86/2.00      | ~ l1_pre_topc(X0)
% 11.86/2.00      | ~ v1_pre_topc(k1_pre_topc(X0,X1))
% 11.86/2.00      | k2_struct_0(k1_pre_topc(X0,X1)) = X1 ),
% 11.86/2.00      inference(cnf_transformation,[],[f357]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_90,plain,
% 11.86/2.00      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
% 11.86/2.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 11.86/2.00      | ~ l1_pre_topc(X0) ),
% 11.86/2.00      inference(cnf_transformation,[],[f307]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_814,plain,
% 11.86/2.00      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 11.86/2.00      | ~ l1_pre_topc(X0)
% 11.86/2.00      | ~ v1_pre_topc(k1_pre_topc(X0,X1))
% 11.86/2.00      | k2_struct_0(k1_pre_topc(X0,X1)) = X1 ),
% 11.86/2.00      inference(global_propositional_subsumption,
% 11.86/2.00                [status(thm)],
% 11.86/2.00                [c_60,c_90]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_815,plain,
% 11.86/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.86/2.00      | ~ l1_pre_topc(X1)
% 11.86/2.00      | ~ v1_pre_topc(k1_pre_topc(X1,X0))
% 11.86/2.00      | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
% 11.86/2.00      inference(renaming,[status(thm)],[c_814]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_91,plain,
% 11.86/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.86/2.00      | ~ l1_pre_topc(X1)
% 11.86/2.00      | v1_pre_topc(k1_pre_topc(X1,X0)) ),
% 11.86/2.00      inference(cnf_transformation,[],[f306]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_820,plain,
% 11.86/2.00      ( ~ l1_pre_topc(X1)
% 11.86/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.86/2.00      | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
% 11.86/2.00      inference(global_propositional_subsumption,
% 11.86/2.00                [status(thm)],
% 11.86/2.00                [c_815,c_91]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_821,plain,
% 11.86/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.86/2.00      | ~ l1_pre_topc(X1)
% 11.86/2.00      | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
% 11.86/2.00      inference(renaming,[status(thm)],[c_820]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_10100,plain,
% 11.86/2.00      ( k2_struct_0(k1_pre_topc(X0,X1)) = X1
% 11.86/2.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 11.86/2.00      | l1_pre_topc(X0) != iProver_top ),
% 11.86/2.00      inference(predicate_to_equality,[status(thm)],[c_821]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_18018,plain,
% 11.86/2.00      ( k2_struct_0(k1_pre_topc(sK20,sK21)) = sK21
% 11.86/2.00      | l1_pre_topc(sK20) != iProver_top ),
% 11.86/2.00      inference(superposition,[status(thm)],[c_10102,c_10100]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_18277,plain,
% 11.86/2.00      ( k2_struct_0(k1_pre_topc(sK20,sK21)) = sK21 ),
% 11.86/2.00      inference(global_propositional_subsumption,
% 11.86/2.00                [status(thm)],
% 11.86/2.00                [c_18018,c_131]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_84,plain,
% 11.86/2.00      ( ~ sP1(X0,X1)
% 11.86/2.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 11.86/2.00      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X0),X2,k2_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0)))
% 11.86/2.00      | ~ r2_hidden(X2,u1_pre_topc(X1))
% 11.86/2.00      | r2_hidden(k9_subset_1(u1_struct_0(X0),X2,k2_struct_0(X0)),u1_pre_topc(X0)) ),
% 11.86/2.00      inference(cnf_transformation,[],[f358]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_10131,plain,
% 11.86/2.00      ( sP1(X0,X1) != iProver_top
% 11.86/2.00      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 11.86/2.00      | m1_subset_1(k9_subset_1(u1_struct_0(X0),X2,k2_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 11.86/2.00      | r2_hidden(X2,u1_pre_topc(X1)) != iProver_top
% 11.86/2.00      | r2_hidden(k9_subset_1(u1_struct_0(X0),X2,k2_struct_0(X0)),u1_pre_topc(X0)) = iProver_top ),
% 11.86/2.00      inference(predicate_to_equality,[status(thm)],[c_84]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_26543,plain,
% 11.86/2.00      ( sP1(k1_pre_topc(sK20,sK21),X0) != iProver_top
% 11.86/2.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 11.86/2.00      | m1_subset_1(k9_subset_1(u1_struct_0(k1_pre_topc(sK20,sK21)),X1,sK21),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK20,sK21)))) != iProver_top
% 11.86/2.00      | r2_hidden(X1,u1_pre_topc(X0)) != iProver_top
% 11.86/2.00      | r2_hidden(k9_subset_1(u1_struct_0(k1_pre_topc(sK20,sK21)),X1,k2_struct_0(k1_pre_topc(sK20,sK21))),u1_pre_topc(k1_pre_topc(sK20,sK21))) = iProver_top ),
% 11.86/2.00      inference(superposition,[status(thm)],[c_18277,c_10131]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_26544,plain,
% 11.86/2.00      ( sP1(k1_pre_topc(sK20,sK21),X0) != iProver_top
% 11.86/2.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 11.86/2.00      | m1_subset_1(k9_subset_1(u1_struct_0(k1_pre_topc(sK20,sK21)),X1,sK21),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK20,sK21)))) != iProver_top
% 11.86/2.00      | r2_hidden(X1,u1_pre_topc(X0)) != iProver_top
% 11.86/2.00      | r2_hidden(k9_subset_1(u1_struct_0(k1_pre_topc(sK20,sK21)),X1,sK21),u1_pre_topc(k1_pre_topc(sK20,sK21))) = iProver_top ),
% 11.86/2.00      inference(light_normalisation,[status(thm)],[c_26543,c_18277]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_26980,plain,
% 11.86/2.00      ( sP1(k1_pre_topc(sK20,sK21),X0) != iProver_top
% 11.86/2.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 11.86/2.00      | r2_hidden(X1,u1_pre_topc(X0)) != iProver_top
% 11.86/2.00      | r2_hidden(k9_subset_1(u1_struct_0(k1_pre_topc(sK20,sK21)),X1,sK21),u1_pre_topc(k1_pre_topc(sK20,sK21))) = iProver_top
% 11.86/2.00      | v1_xboole_0(k9_subset_1(u1_struct_0(k1_pre_topc(sK20,sK21)),X1,sK21)) != iProver_top
% 11.86/2.00      | v1_xboole_0(k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK20,sK21)))) != iProver_top ),
% 11.86/2.00      inference(superposition,[status(thm)],[c_10171,c_26544]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_27147,plain,
% 11.86/2.00      ( sP1(k1_pre_topc(sK20,sK21),X0) != iProver_top
% 11.86/2.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 11.86/2.00      | r2_hidden(k9_subset_1(u1_struct_0(k1_pre_topc(sK20,sK21)),k2_pre_topc(X0,X1),sK21),u1_pre_topc(k1_pre_topc(sK20,sK21))) = iProver_top
% 11.86/2.00      | r2_hidden(k2_pre_topc(X0,X1),u1_pre_topc(X0)) != iProver_top
% 11.86/2.00      | l1_pre_topc(X0) != iProver_top
% 11.86/2.00      | v1_xboole_0(k9_subset_1(u1_struct_0(k1_pre_topc(sK20,sK21)),k2_pre_topc(X0,X1),sK21)) != iProver_top
% 11.86/2.00      | v1_xboole_0(k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK20,sK21)))) != iProver_top ),
% 11.86/2.00      inference(superposition,[status(thm)],[c_10124,c_26980]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_32225,plain,
% 11.86/2.00      ( k4_xboole_0(k1_tarski(sK21),u1_pre_topc(sK20)) = k1_xboole_0
% 11.86/2.00      | sP1(k1_pre_topc(sK20,sK21),sK20) != iProver_top
% 11.86/2.00      | m1_subset_1(k7_subset_1(u1_struct_0(sK20),u1_struct_0(sK20),sK21),k1_zfmisc_1(u1_struct_0(sK20))) != iProver_top
% 11.86/2.00      | r2_hidden(k7_subset_1(u1_struct_0(sK20),u1_struct_0(sK20),sK21),u1_pre_topc(sK20)) != iProver_top
% 11.86/2.00      | r2_hidden(k9_subset_1(u1_struct_0(k1_pre_topc(sK20,sK21)),k2_pre_topc(sK20,k7_subset_1(u1_struct_0(sK20),u1_struct_0(sK20),sK21)),sK21),u1_pre_topc(k1_pre_topc(sK20,sK21))) = iProver_top
% 11.86/2.00      | l1_pre_topc(sK20) != iProver_top
% 11.86/2.00      | v1_xboole_0(k9_subset_1(u1_struct_0(k1_pre_topc(sK20,sK21)),k2_pre_topc(sK20,k7_subset_1(u1_struct_0(sK20),u1_struct_0(sK20),sK21)),sK21)) != iProver_top
% 11.86/2.00      | v1_xboole_0(k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK20,sK21)))) != iProver_top ),
% 11.86/2.00      inference(superposition,[status(thm)],[c_23347,c_27147]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_120,plain,
% 11.86/2.00      ( v4_pre_topc(X0,X1)
% 11.86/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.86/2.00      | ~ v2_pre_topc(X1)
% 11.86/2.00      | ~ l1_pre_topc(X1)
% 11.86/2.00      | k2_pre_topc(X1,X0) != X0 ),
% 11.86/2.00      inference(cnf_transformation,[],[f337]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_10108,plain,
% 11.86/2.00      ( k2_pre_topc(X0,X1) != X1
% 11.86/2.00      | v4_pre_topc(X1,X0) = iProver_top
% 11.86/2.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 11.86/2.00      | v2_pre_topc(X0) != iProver_top
% 11.86/2.00      | l1_pre_topc(X0) != iProver_top ),
% 11.86/2.00      inference(predicate_to_equality,[status(thm)],[c_120]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_23849,plain,
% 11.86/2.00      ( k4_xboole_0(k1_tarski(sK21),u1_pre_topc(sK20)) = k1_xboole_0
% 11.86/2.00      | v4_pre_topc(k7_subset_1(u1_struct_0(sK20),u1_struct_0(sK20),sK21),sK20) = iProver_top
% 11.86/2.00      | m1_subset_1(k7_subset_1(u1_struct_0(sK20),u1_struct_0(sK20),sK21),k1_zfmisc_1(u1_struct_0(sK20))) != iProver_top
% 11.86/2.00      | v2_pre_topc(sK20) != iProver_top
% 11.86/2.00      | l1_pre_topc(sK20) != iProver_top ),
% 11.86/2.00      inference(superposition,[status(thm)],[c_23347,c_10108]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_128,negated_conjecture,
% 11.86/2.00      ( v3_pre_topc(sK21,sK20) | v2_pre_topc(sK20) ),
% 11.86/2.00      inference(cnf_transformation,[],[f341]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_10103,plain,
% 11.86/2.00      ( v3_pre_topc(sK21,sK20) = iProver_top
% 11.86/2.00      | v2_pre_topc(sK20) = iProver_top ),
% 11.86/2.00      inference(predicate_to_equality,[status(thm)],[c_128]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_23348,plain,
% 11.86/2.00      ( k4_xboole_0(k1_tarski(sK21),u1_pre_topc(sK20)) = k1_xboole_0
% 11.86/2.00      | v2_pre_topc(sK20) = iProver_top ),
% 11.86/2.00      inference(superposition,[status(thm)],[c_10103,c_22809]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_25514,plain,
% 11.86/2.00      ( k4_xboole_0(k1_tarski(sK21),u1_pre_topc(sK20)) = k1_xboole_0
% 11.86/2.00      | v4_pre_topc(k7_subset_1(u1_struct_0(sK20),u1_struct_0(sK20),sK21),sK20) = iProver_top
% 11.86/2.00      | m1_subset_1(k7_subset_1(u1_struct_0(sK20),u1_struct_0(sK20),sK21),k1_zfmisc_1(u1_struct_0(sK20))) != iProver_top ),
% 11.86/2.00      inference(global_propositional_subsumption,
% 11.86/2.00                [status(thm)],
% 11.86/2.00                [c_23849,c_131,c_23348]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_76,plain,
% 11.86/2.00      ( ~ v4_pre_topc(X0,X1)
% 11.86/2.00      | v3_pre_topc(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0),X1)
% 11.86/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.86/2.00      | ~ l1_pre_topc(X1) ),
% 11.86/2.00      inference(cnf_transformation,[],[f291]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_10137,plain,
% 11.86/2.00      ( v4_pre_topc(X0,X1) != iProver_top
% 11.86/2.00      | v3_pre_topc(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0),X1) = iProver_top
% 11.86/2.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 11.86/2.00      | l1_pre_topc(X1) != iProver_top ),
% 11.86/2.00      inference(predicate_to_equality,[status(thm)],[c_76]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_24003,plain,
% 11.86/2.00      ( v4_pre_topc(X0,sK20) != iProver_top
% 11.86/2.00      | v3_pre_topc(k7_subset_1(u1_struct_0(sK20),u1_struct_0(sK20),X0),sK20) = iProver_top
% 11.86/2.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK20))) != iProver_top
% 11.86/2.00      | l1_pre_topc(sK20) != iProver_top ),
% 11.86/2.00      inference(superposition,[status(thm)],[c_14134,c_10137]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_26187,plain,
% 11.86/2.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK20))) != iProver_top
% 11.86/2.00      | v3_pre_topc(k7_subset_1(u1_struct_0(sK20),u1_struct_0(sK20),X0),sK20) = iProver_top
% 11.86/2.00      | v4_pre_topc(X0,sK20) != iProver_top ),
% 11.86/2.00      inference(global_propositional_subsumption,
% 11.86/2.00                [status(thm)],
% 11.86/2.00                [c_24003,c_131]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_26188,plain,
% 11.86/2.00      ( v4_pre_topc(X0,sK20) != iProver_top
% 11.86/2.00      | v3_pre_topc(k7_subset_1(u1_struct_0(sK20),u1_struct_0(sK20),X0),sK20) = iProver_top
% 11.86/2.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK20))) != iProver_top ),
% 11.86/2.00      inference(renaming,[status(thm)],[c_26187]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_26193,plain,
% 11.86/2.00      ( v4_pre_topc(k7_subset_1(u1_struct_0(sK20),u1_struct_0(sK20),sK21),sK20) != iProver_top
% 11.86/2.00      | v3_pre_topc(sK21,sK20) = iProver_top
% 11.86/2.00      | m1_subset_1(k7_subset_1(u1_struct_0(sK20),u1_struct_0(sK20),sK21),k1_zfmisc_1(u1_struct_0(sK20))) != iProver_top ),
% 11.86/2.00      inference(superposition,[status(thm)],[c_14215,c_26188]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_32655,plain,
% 11.86/2.00      ( m1_subset_1(k7_subset_1(u1_struct_0(sK20),u1_struct_0(sK20),sK21),k1_zfmisc_1(u1_struct_0(sK20))) != iProver_top
% 11.86/2.00      | k4_xboole_0(k1_tarski(sK21),u1_pre_topc(sK20)) = k1_xboole_0 ),
% 11.86/2.00      inference(global_propositional_subsumption,
% 11.86/2.00                [status(thm)],
% 11.86/2.00                [c_32225,c_22809,c_25514,c_26193]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_32656,plain,
% 11.86/2.00      ( k4_xboole_0(k1_tarski(sK21),u1_pre_topc(sK20)) = k1_xboole_0
% 11.86/2.00      | m1_subset_1(k7_subset_1(u1_struct_0(sK20),u1_struct_0(sK20),sK21),k1_zfmisc_1(u1_struct_0(sK20))) != iProver_top ),
% 11.86/2.00      inference(renaming,[status(thm)],[c_32655]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_49892,plain,
% 11.86/2.00      ( k4_xboole_0(k1_tarski(sK21),u1_pre_topc(sK20)) = k1_xboole_0
% 11.86/2.00      | m1_subset_1(k4_xboole_0(u1_struct_0(sK20),sK21),k1_zfmisc_1(u1_struct_0(sK20))) != iProver_top ),
% 11.86/2.00      inference(demodulation,[status(thm)],[c_49827,c_32656]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_12,plain,
% 11.86/2.00      ( r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
% 11.86/2.00      inference(cnf_transformation,[],[f227]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_48607,plain,
% 11.86/2.00      ( r2_hidden(sK21,u1_pre_topc(sK20))
% 11.86/2.00      | k4_xboole_0(k1_tarski(sK21),u1_pre_topc(sK20)) != k1_xboole_0 ),
% 11.86/2.00      inference(instantiation,[status(thm)],[c_12]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_48608,plain,
% 11.86/2.00      ( k4_xboole_0(k1_tarski(sK21),u1_pre_topc(sK20)) != k1_xboole_0
% 11.86/2.00      | r2_hidden(sK21,u1_pre_topc(sK20)) = iProver_top ),
% 11.86/2.00      inference(predicate_to_equality,[status(thm)],[c_48607]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_73,plain,
% 11.86/2.00      ( v3_pre_topc(X0,X1)
% 11.86/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.86/2.00      | ~ r2_hidden(X0,u1_pre_topc(X1))
% 11.86/2.00      | ~ l1_pre_topc(X1) ),
% 11.86/2.00      inference(cnf_transformation,[],[f290]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_10140,plain,
% 11.86/2.00      ( v3_pre_topc(X0,X1) = iProver_top
% 11.86/2.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 11.86/2.00      | r2_hidden(X0,u1_pre_topc(X1)) != iProver_top
% 11.86/2.00      | l1_pre_topc(X1) != iProver_top ),
% 11.86/2.00      inference(predicate_to_equality,[status(thm)],[c_73]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_22432,plain,
% 11.86/2.00      ( v3_pre_topc(sK21,sK20) = iProver_top
% 11.86/2.00      | r2_hidden(sK21,u1_pre_topc(sK20)) != iProver_top
% 11.86/2.00      | l1_pre_topc(sK20) != iProver_top ),
% 11.86/2.00      inference(superposition,[status(thm)],[c_10102,c_10140]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_23070,plain,
% 11.86/2.00      ( r2_hidden(sK21,u1_pre_topc(sK20)) != iProver_top
% 11.86/2.00      | v3_pre_topc(sK21,sK20) = iProver_top ),
% 11.86/2.00      inference(global_propositional_subsumption,
% 11.86/2.00                [status(thm)],
% 11.86/2.00                [c_22432,c_131]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_23071,plain,
% 11.86/2.00      ( v3_pre_topc(sK21,sK20) = iProver_top
% 11.86/2.00      | r2_hidden(sK21,u1_pre_topc(sK20)) != iProver_top ),
% 11.86/2.00      inference(renaming,[status(thm)],[c_23070]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_23072,plain,
% 11.86/2.00      ( v3_pre_topc(sK21,sK20) | ~ r2_hidden(sK21,u1_pre_topc(sK20)) ),
% 11.86/2.00      inference(predicate_to_equality_rev,[status(thm)],[c_23071]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(contradiction,plain,
% 11.86/2.00      ( $false ),
% 11.86/2.00      inference(minisat,
% 11.86/2.00                [status(thm)],
% 11.86/2.00                [c_51110,c_50792,c_49939,c_49896,c_49892,c_48608,c_48607,
% 11.86/2.00                 c_23072,c_23071,c_12185,c_131]) ).
% 11.86/2.00  
% 11.86/2.00  
% 11.86/2.00  % SZS output end CNFRefutation for theBenchmark.p
% 11.86/2.00  
% 11.86/2.00  ------                               Statistics
% 11.86/2.00  
% 11.86/2.00  ------ General
% 11.86/2.00  
% 11.86/2.00  abstr_ref_over_cycles:                  0
% 11.86/2.00  abstr_ref_under_cycles:                 0
% 11.86/2.00  gc_basic_clause_elim:                   0
% 11.86/2.00  forced_gc_time:                         0
% 11.86/2.00  parsing_time:                           0.013
% 11.86/2.00  unif_index_cands_time:                  0.
% 11.86/2.00  unif_index_add_time:                    0.
% 11.86/2.00  orderings_time:                         0.
% 11.86/2.00  out_proof_time:                         0.026
% 11.86/2.00  total_time:                             1.402
% 11.86/2.00  num_of_symbols:                         88
% 11.86/2.00  num_of_terms:                           36972
% 11.86/2.00  
% 11.86/2.00  ------ Preprocessing
% 11.86/2.00  
% 11.86/2.00  num_of_splits:                          0
% 11.86/2.00  num_of_split_atoms:                     0
% 11.86/2.00  num_of_reused_defs:                     0
% 11.86/2.00  num_eq_ax_congr_red:                    109
% 11.86/2.00  num_of_sem_filtered_clauses:            12
% 11.86/2.00  num_of_subtypes:                        0
% 11.86/2.00  monotx_restored_types:                  0
% 11.86/2.00  sat_num_of_epr_types:                   0
% 11.86/2.00  sat_num_of_non_cyclic_types:            0
% 11.86/2.00  sat_guarded_non_collapsed_types:        0
% 11.86/2.00  num_pure_diseq_elim:                    0
% 11.86/2.00  simp_replaced_by:                       0
% 11.86/2.00  res_preprocessed:                       508
% 11.86/2.00  prep_upred:                             0
% 11.86/2.00  prep_unflattend:                        200
% 11.86/2.00  smt_new_axioms:                         0
% 11.86/2.00  pred_elim_cands:                        13
% 11.86/2.00  pred_elim:                              2
% 11.86/2.00  pred_elim_cl:                           2
% 11.86/2.00  pred_elim_cycles:                       16
% 11.86/2.00  merged_defs:                            48
% 11.86/2.00  merged_defs_ncl:                        0
% 11.86/2.00  bin_hyper_res:                          67
% 11.86/2.00  prep_cycles:                            4
% 11.86/2.00  pred_elim_time:                         0.111
% 11.86/2.00  splitting_time:                         0.
% 11.86/2.00  sem_filter_time:                        0.
% 11.86/2.00  monotx_time:                            0.001
% 11.86/2.00  subtype_inf_time:                       0.
% 11.86/2.00  
% 11.86/2.00  ------ Problem properties
% 11.86/2.00  
% 11.86/2.00  clauses:                                111
% 11.86/2.00  conjectures:                            5
% 11.86/2.00  epr:                                    17
% 11.86/2.00  horn:                                   86
% 11.86/2.00  ground:                                 6
% 11.86/2.00  unary:                                  7
% 11.86/2.00  binary:                                 39
% 11.86/2.00  lits:                                   322
% 11.86/2.00  lits_eq:                                53
% 11.86/2.00  fd_pure:                                0
% 11.86/2.00  fd_pseudo:                              0
% 11.86/2.00  fd_cond:                                10
% 11.86/2.00  fd_pseudo_cond:                         6
% 11.86/2.00  ac_symbols:                             0
% 11.86/2.00  
% 11.86/2.00  ------ Propositional Solver
% 11.86/2.00  
% 11.86/2.00  prop_solver_calls:                      32
% 11.86/2.00  prop_fast_solver_calls:                 5703
% 11.86/2.00  smt_solver_calls:                       0
% 11.86/2.00  smt_fast_solver_calls:                  0
% 11.86/2.00  prop_num_of_clauses:                    19825
% 11.86/2.00  prop_preprocess_simplified:             46169
% 11.86/2.00  prop_fo_subsumed:                       142
% 11.86/2.00  prop_solver_time:                       0.
% 11.86/2.00  smt_solver_time:                        0.
% 11.86/2.00  smt_fast_solver_time:                   0.
% 11.86/2.00  prop_fast_solver_time:                  0.
% 11.86/2.00  prop_unsat_core_time:                   0.001
% 11.86/2.00  
% 11.86/2.00  ------ QBF
% 11.86/2.00  
% 11.86/2.00  qbf_q_res:                              0
% 11.86/2.00  qbf_num_tautologies:                    0
% 11.86/2.00  qbf_prep_cycles:                        0
% 11.86/2.00  
% 11.86/2.00  ------ BMC1
% 11.86/2.00  
% 11.86/2.00  bmc1_current_bound:                     -1
% 11.86/2.00  bmc1_last_solved_bound:                 -1
% 11.86/2.00  bmc1_unsat_core_size:                   -1
% 11.86/2.00  bmc1_unsat_core_parents_size:           -1
% 11.86/2.00  bmc1_merge_next_fun:                    0
% 11.86/2.00  bmc1_unsat_core_clauses_time:           0.
% 11.86/2.00  
% 11.86/2.00  ------ Instantiation
% 11.86/2.00  
% 11.86/2.00  inst_num_of_clauses:                    4937
% 11.86/2.00  inst_num_in_passive:                    3091
% 11.86/2.00  inst_num_in_active:                     1530
% 11.86/2.00  inst_num_in_unprocessed:                316
% 11.86/2.00  inst_num_of_loops:                      2220
% 11.86/2.00  inst_num_of_learning_restarts:          0
% 11.86/2.00  inst_num_moves_active_passive:          689
% 11.86/2.00  inst_lit_activity:                      0
% 11.86/2.00  inst_lit_activity_moves:                0
% 11.86/2.00  inst_num_tautologies:                   0
% 11.86/2.00  inst_num_prop_implied:                  0
% 11.86/2.00  inst_num_existing_simplified:           0
% 11.86/2.00  inst_num_eq_res_simplified:             0
% 11.86/2.00  inst_num_child_elim:                    0
% 11.86/2.00  inst_num_of_dismatching_blockings:      2225
% 11.86/2.00  inst_num_of_non_proper_insts:           6369
% 11.86/2.00  inst_num_of_duplicates:                 0
% 11.86/2.00  inst_inst_num_from_inst_to_res:         0
% 11.86/2.00  inst_dismatching_checking_time:         0.
% 11.86/2.00  
% 11.86/2.00  ------ Resolution
% 11.86/2.00  
% 11.86/2.00  res_num_of_clauses:                     0
% 11.86/2.00  res_num_in_passive:                     0
% 11.86/2.00  res_num_in_active:                      0
% 11.86/2.00  res_num_of_loops:                       512
% 11.86/2.00  res_forward_subset_subsumed:            355
% 11.86/2.00  res_backward_subset_subsumed:           0
% 11.86/2.00  res_forward_subsumed:                   4
% 11.86/2.00  res_backward_subsumed:                  0
% 11.86/2.00  res_forward_subsumption_resolution:     0
% 11.86/2.00  res_backward_subsumption_resolution:    0
% 11.86/2.00  res_clause_to_clause_subsumption:       7193
% 11.86/2.00  res_orphan_elimination:                 0
% 11.86/2.00  res_tautology_del:                      427
% 11.86/2.00  res_num_eq_res_simplified:              0
% 11.86/2.00  res_num_sel_changes:                    0
% 11.86/2.00  res_moves_from_active_to_pass:          0
% 11.86/2.00  
% 11.86/2.00  ------ Superposition
% 11.86/2.00  
% 11.86/2.00  sup_time_total:                         0.
% 11.86/2.00  sup_time_generating:                    0.
% 11.86/2.00  sup_time_sim_full:                      0.
% 11.86/2.00  sup_time_sim_immed:                     0.
% 11.86/2.00  
% 11.86/2.00  sup_num_of_clauses:                     1477
% 11.86/2.00  sup_num_in_active:                      345
% 11.86/2.00  sup_num_in_passive:                     1132
% 11.86/2.00  sup_num_of_loops:                       443
% 11.86/2.00  sup_fw_superposition:                   1045
% 11.86/2.00  sup_bw_superposition:                   1680
% 11.86/2.00  sup_immediate_simplified:               728
% 11.86/2.00  sup_given_eliminated:                   2
% 11.86/2.00  comparisons_done:                       0
% 11.86/2.00  comparisons_avoided:                    196
% 11.86/2.00  
% 11.86/2.00  ------ Simplifications
% 11.86/2.00  
% 11.86/2.00  
% 11.86/2.00  sim_fw_subset_subsumed:                 163
% 11.86/2.00  sim_bw_subset_subsumed:                 51
% 11.86/2.00  sim_fw_subsumed:                        195
% 11.86/2.00  sim_bw_subsumed:                        48
% 11.86/2.00  sim_fw_subsumption_res:                 0
% 11.86/2.00  sim_bw_subsumption_res:                 0
% 11.86/2.00  sim_tautology_del:                      34
% 11.86/2.00  sim_eq_tautology_del:                   147
% 11.86/2.00  sim_eq_res_simp:                        4
% 11.86/2.00  sim_fw_demodulated:                     278
% 11.86/2.00  sim_bw_demodulated:                     75
% 11.86/2.00  sim_light_normalised:                   187
% 11.86/2.00  sim_joinable_taut:                      0
% 11.86/2.00  sim_joinable_simp:                      0
% 11.86/2.00  sim_ac_normalised:                      0
% 11.86/2.00  sim_smt_subsumption:                    0
% 11.86/2.00  
%------------------------------------------------------------------------------
