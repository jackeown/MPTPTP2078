%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1840+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:33 EST 2020

% Result     : Theorem 0.54s
% Output     : Refutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :   26 (  54 expanded)
%              Number of leaves         :    5 (  17 expanded)
%              Depth                    :    9
%              Number of atoms          :   80 ( 252 expanded)
%              Number of equality atoms :   10 (  46 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4126,plain,(
    $false ),
    inference(subsumption_resolution,[],[f4125,f4030])).

fof(f4030,plain,(
    v1_zfmisc_1(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f4029,f3788])).

fof(f3788,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f3690])).

fof(f3690,plain,
    ( ~ v7_struct_0(sK1)
    & v7_struct_0(sK0)
    & u1_struct_0(sK0) = u1_struct_0(sK1)
    & l1_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f3575,f3689,f3688])).

fof(f3688,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v7_struct_0(X1)
            & v7_struct_0(X0)
            & u1_struct_0(X0) = u1_struct_0(X1)
            & l1_struct_0(X1) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ~ v7_struct_0(X1)
          & v7_struct_0(sK0)
          & u1_struct_0(X1) = u1_struct_0(sK0)
          & l1_struct_0(X1) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f3689,plain,
    ( ? [X1] :
        ( ~ v7_struct_0(X1)
        & v7_struct_0(sK0)
        & u1_struct_0(X1) = u1_struct_0(sK0)
        & l1_struct_0(X1) )
   => ( ~ v7_struct_0(sK1)
      & v7_struct_0(sK0)
      & u1_struct_0(sK0) = u1_struct_0(sK1)
      & l1_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f3575,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v7_struct_0(X1)
          & v7_struct_0(X0)
          & u1_struct_0(X0) = u1_struct_0(X1)
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f3574])).

fof(f3574,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v7_struct_0(X1)
          & v7_struct_0(X0)
          & u1_struct_0(X0) = u1_struct_0(X1)
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3551])).

fof(f3551,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( l1_struct_0(X1)
           => ( ( v7_struct_0(X0)
                & u1_struct_0(X0) = u1_struct_0(X1) )
             => v7_struct_0(X1) ) ) ) ),
    inference(negated_conjecture,[],[f3550])).

fof(f3550,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ( ( v7_struct_0(X0)
              & u1_struct_0(X0) = u1_struct_0(X1) )
           => v7_struct_0(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tex_2)).

fof(f4029,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | ~ l1_struct_0(sK0) ),
    inference(resolution,[],[f3791,f3806])).

fof(f3806,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3578])).

fof(f3578,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f3577])).

fof(f3577,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1804])).

fof(f1804,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).

fof(f3791,plain,(
    v7_struct_0(sK0) ),
    inference(cnf_transformation,[],[f3690])).

fof(f4125,plain,(
    ~ v1_zfmisc_1(u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f4036,f3790])).

fof(f3790,plain,(
    u1_struct_0(sK0) = u1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f3690])).

fof(f4036,plain,(
    ~ v1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f4033,f3789])).

fof(f3789,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f3690])).

fof(f4033,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK1))
    | ~ l1_struct_0(sK1) ),
    inference(resolution,[],[f3792,f3807])).

fof(f3807,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3580])).

fof(f3580,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(flattening,[],[f3579])).

fof(f3579,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1802])).

fof(f1802,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v7_struct_0(X0) )
     => ~ v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_struct_0)).

fof(f3792,plain,(
    ~ v7_struct_0(sK1) ),
    inference(cnf_transformation,[],[f3690])).
%------------------------------------------------------------------------------
