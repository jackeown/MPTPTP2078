%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1219+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:30 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   20 (  47 expanded)
%              Number of leaves         :    4 (  14 expanded)
%              Depth                    :   10
%              Number of atoms          :   55 ( 181 expanded)
%              Number of equality atoms :   29 (  92 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,plain,(
    $false ),
    inference(global_subsumption,[],[f14,f19])).

fof(f19,plain,(
    sK1 = sK2 ),
    inference(forward_demodulation,[],[f18,f16])).

fof(f16,plain,(
    sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(unit_resulting_resolution,[],[f11,f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f11,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( sK1 != sK2
    & k3_subset_1(u1_struct_0(sK0),sK1) = k3_subset_1(u1_struct_0(sK0),sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f9,f8])).

fof(f8,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( X1 != X2
            & k3_subset_1(u1_struct_0(X0),X1) = k3_subset_1(u1_struct_0(X0),X2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
   => ( ? [X2] :
          ( sK1 != X2
          & k3_subset_1(u1_struct_0(sK0),sK1) = k3_subset_1(u1_struct_0(sK0),X2)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,
    ( ? [X2] :
        ( sK1 != X2
        & k3_subset_1(u1_struct_0(sK0),sK1) = k3_subset_1(u1_struct_0(sK0),X2)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( sK1 != sK2
      & k3_subset_1(u1_struct_0(sK0),sK1) = k3_subset_1(u1_struct_0(sK0),sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & k3_subset_1(u1_struct_0(X0),X1) = k3_subset_1(u1_struct_0(X0),X2)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & k3_subset_1(u1_struct_0(X0),X1) = k3_subset_1(u1_struct_0(X0),X2)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,plain,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
           => ( k3_subset_1(u1_struct_0(X0),X1) = k3_subset_1(u1_struct_0(X0),X2)
             => X1 = X2 ) ) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f3,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( k3_subset_1(u1_struct_0(X0),X1) = k3_subset_1(u1_struct_0(X0),X2)
                 => X1 = X2 ) ) ) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( k3_subset_1(u1_struct_0(X0),X1) = k3_subset_1(u1_struct_0(X0),X2)
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_tops_1)).

fof(f18,plain,(
    sK2 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(forward_demodulation,[],[f17,f13])).

fof(f13,plain,(
    k3_subset_1(u1_struct_0(sK0),sK1) = k3_subset_1(u1_struct_0(sK0),sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f17,plain,(
    sK2 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2)) ),
    inference(unit_resulting_resolution,[],[f12,f15])).

fof(f12,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f10])).

fof(f14,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f10])).

%------------------------------------------------------------------------------
