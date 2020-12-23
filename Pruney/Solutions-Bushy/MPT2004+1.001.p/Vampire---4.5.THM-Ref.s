%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT2004+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:02 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   15 (  39 expanded)
%              Number of leaves         :    2 (   8 expanded)
%              Depth                    :   10
%              Number of atoms          :   53 ( 191 expanded)
%              Number of equality atoms :   20 (  74 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,plain,(
    $false ),
    inference(subsumption_resolution,[],[f14,f11])).

fof(f11,plain,(
    m1_setfam_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,
    ( ~ m1_setfam_1(sK3,u1_struct_0(sK1))
    & m1_setfam_1(sK2,u1_struct_0(sK0))
    & sK2 = sK3
    & u1_struct_0(sK1) = u1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f6,f7])).

fof(f7,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ m1_setfam_1(X3,u1_struct_0(X1))
        & m1_setfam_1(X2,u1_struct_0(X0))
        & X2 = X3
        & u1_struct_0(X0) = u1_struct_0(X1) )
   => ( ~ m1_setfam_1(sK3,u1_struct_0(sK1))
      & m1_setfam_1(sK2,u1_struct_0(sK0))
      & sK2 = sK3
      & u1_struct_0(sK1) = u1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_setfam_1(X3,u1_struct_0(X1))
      & m1_setfam_1(X2,u1_struct_0(X0))
      & X2 = X3
      & u1_struct_0(X0) = u1_struct_0(X1) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_setfam_1(X3,u1_struct_0(X1))
      & m1_setfam_1(X2,u1_struct_0(X0))
      & X2 = X3
      & u1_struct_0(X0) = u1_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_setfam_1(X2,u1_struct_0(X0))
          & X2 = X3
          & u1_struct_0(X0) = u1_struct_0(X1) )
       => m1_setfam_1(X3,u1_struct_0(X1)) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f3,plain,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( l1_struct_0(X1)
           => ! [X2,X3] :
                ( ( m1_setfam_1(X2,u1_struct_0(X0))
                  & X2 = X3
                  & u1_struct_0(X0) = u1_struct_0(X1) )
               => m1_setfam_1(X3,u1_struct_0(X1)) ) ) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( l1_struct_0(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
                   => ( ( m1_setfam_1(X2,u1_struct_0(X0))
                        & X2 = X3
                        & u1_struct_0(X0) = u1_struct_0(X1) )
                     => m1_setfam_1(X3,u1_struct_0(X1)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
                 => ( ( m1_setfam_1(X2,u1_struct_0(X0))
                      & X2 = X3
                      & u1_struct_0(X0) = u1_struct_0(X1) )
                   => m1_setfam_1(X3,u1_struct_0(X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_waybel_9)).

fof(f14,plain,(
    ~ m1_setfam_1(sK2,u1_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f13,f9])).

fof(f9,plain,(
    u1_struct_0(sK1) = u1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f13,plain,(
    ~ m1_setfam_1(sK2,u1_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f12,f10])).

fof(f10,plain,(
    sK2 = sK3 ),
    inference(cnf_transformation,[],[f8])).

fof(f12,plain,(
    ~ m1_setfam_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f8])).

%------------------------------------------------------------------------------
