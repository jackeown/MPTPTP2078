%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:26 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   65 (  65 expanded)
%              Number of leaves         :   65 (  65 expanded)
%              Depth                    :    0
%              Number of atoms          :  215 ( 215 expanded)
%              Number of equality atoms :   82 (  82 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u395,negated_conjecture,(
    k13_lattice3(sK1,sK2,sK3) != k13_lattice3(sK0,sK2,sK3) )).

tff(u394,negated_conjecture,
    ( ~ ! [X0] :
          ( ~ m1_subset_1(X0,u1_struct_0(sK1))
          | k7_domain_1(u1_struct_0(sK1),X0,sK3) = k2_tarski(X0,sK3) )
    | k7_domain_1(u1_struct_0(sK1),sK3,sK3) = k2_tarski(sK3,sK3) )).

tff(u393,negated_conjecture,
    ( ~ ! [X0] :
          ( ~ m1_subset_1(X0,u1_struct_0(sK1))
          | k7_domain_1(u1_struct_0(sK1),X0,sK3) = k2_tarski(X0,sK3) )
    | k7_domain_1(u1_struct_0(sK1),sK2,sK3) = k2_tarski(sK2,sK3) )).

tff(u392,negated_conjecture,
    ( ~ ! [X1] :
          ( ~ m1_subset_1(X1,u1_struct_0(sK1))
          | k7_domain_1(u1_struct_0(sK1),X1,sK2) = k2_tarski(X1,sK2) )
    | k7_domain_1(u1_struct_0(sK1),sK3,sK2) = k2_tarski(sK3,sK2) )).

tff(u391,negated_conjecture,
    ( ~ ! [X1] :
          ( ~ m1_subset_1(X1,u1_struct_0(sK1))
          | k7_domain_1(u1_struct_0(sK1),X1,sK2) = k2_tarski(X1,sK2) )
    | k7_domain_1(u1_struct_0(sK1),sK2,sK2) = k2_tarski(sK2,sK2) )).

tff(u390,negated_conjecture,
    ( k7_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k2_tarski(sK3,sK3),k2_tarski(sK3,sK3)) != k2_tarski(k2_tarski(sK3,sK3),k2_tarski(sK3,sK3))
    | k7_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k2_tarski(sK3,sK3),k2_tarski(sK3,sK3)) = k2_tarski(k2_tarski(sK3,sK3),k2_tarski(sK3,sK3)) )).

tff(u389,negated_conjecture,
    ( ~ ! [X2] :
          ( ~ m1_subset_1(X2,u1_struct_0(sK0))
          | k7_domain_1(u1_struct_0(sK0),X2,sK3) = k2_tarski(X2,sK3) )
    | k2_tarski(sK3,sK3) = k7_domain_1(u1_struct_0(sK0),sK3,sK3) )).

tff(u388,negated_conjecture,
    ( ~ ! [X2] :
          ( ~ m1_subset_1(X2,u1_struct_0(sK0))
          | k7_domain_1(u1_struct_0(sK0),X2,sK3) = k2_tarski(X2,sK3) )
    | k2_tarski(sK2,sK3) = k7_domain_1(u1_struct_0(sK0),sK2,sK3) )).

tff(u387,negated_conjecture,
    ( ~ ! [X3] :
          ( ~ m1_subset_1(X3,u1_struct_0(sK0))
          | k7_domain_1(u1_struct_0(sK0),X3,sK2) = k2_tarski(X3,sK2) )
    | k2_tarski(sK3,sK2) = k7_domain_1(u1_struct_0(sK0),sK3,sK2) )).

tff(u386,negated_conjecture,
    ( ~ ! [X3] :
          ( ~ m1_subset_1(X3,u1_struct_0(sK0))
          | k7_domain_1(u1_struct_0(sK0),X3,sK2) = k2_tarski(X3,sK2) )
    | k2_tarski(sK2,sK2) = k7_domain_1(u1_struct_0(sK0),sK2,sK2) )).

tff(u385,negated_conjecture,
    ( ~ ! [X0] :
          ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
          | k2_tarski(k2_tarski(sK3,sK3),X0) = k7_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k2_tarski(sK3,sK3),X0) )
    | ~ m1_subset_1(k2_tarski(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_tarski(k2_tarski(sK3,sK3),k2_tarski(sK2,sK3)) = k7_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k2_tarski(sK3,sK3),k2_tarski(sK2,sK3)) )).

tff(u384,negated_conjecture,
    ( ~ ! [X0] :
          ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
          | k2_tarski(k2_tarski(sK3,sK3),X0) = k7_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k2_tarski(sK3,sK3),X0) )
    | ~ m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_tarski(k2_tarski(sK3,sK3),k2_tarski(sK2,sK2)) = k7_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k2_tarski(sK3,sK3),k2_tarski(sK2,sK2)) )).

tff(u383,negated_conjecture,
    ( ~ ! [X0] :
          ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
          | k2_tarski(k2_tarski(sK3,sK3),X0) = k7_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k2_tarski(sK3,sK3),X0) )
    | ~ m1_subset_1(k2_tarski(sK3,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_tarski(k2_tarski(sK3,sK3),k2_tarski(sK3,sK2)) = k7_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k2_tarski(sK3,sK3),k2_tarski(sK3,sK2)) )).

tff(u382,negated_conjecture,
    ( ~ ! [X1] :
          ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
          | k2_tarski(X1,k2_tarski(sK3,sK3)) = k7_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,k2_tarski(sK3,sK3)) )
    | ~ m1_subset_1(k2_tarski(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_tarski(k2_tarski(sK2,sK3),k2_tarski(sK3,sK3)) = k7_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k2_tarski(sK2,sK3),k2_tarski(sK3,sK3)) )).

tff(u381,negated_conjecture,
    ( ~ ! [X1] :
          ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
          | k2_tarski(X1,k2_tarski(sK3,sK3)) = k7_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,k2_tarski(sK3,sK3)) )
    | ~ m1_subset_1(k2_tarski(sK3,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_tarski(k2_tarski(sK3,sK2),k2_tarski(sK3,sK3)) = k7_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k2_tarski(sK3,sK2),k2_tarski(sK3,sK3)) )).

tff(u380,negated_conjecture,
    ( ~ ! [X1] :
          ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
          | k2_tarski(X1,k2_tarski(sK3,sK3)) = k7_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,k2_tarski(sK3,sK3)) )
    | ~ m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_tarski(k2_tarski(sK2,sK2),k2_tarski(sK3,sK3)) = k7_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k2_tarski(sK2,sK2),k2_tarski(sK3,sK3)) )).

tff(u379,negated_conjecture,(
    sK2 = sK4 )).

tff(u378,negated_conjecture,(
    sK3 = sK5 )).

tff(u377,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | k7_domain_1(X1,X0,X0) = k2_tarski(X0,X0) ) )).

tff(u376,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2) ) )).

tff(u375,negated_conjecture,
    ( ~ ! [X1] :
          ( ~ m1_subset_1(X1,u1_struct_0(sK1))
          | k7_domain_1(u1_struct_0(sK1),sK2,X1) = k2_tarski(sK2,X1) )
    | ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK1))
        | k7_domain_1(u1_struct_0(sK1),sK2,X1) = k2_tarski(sK2,X1) ) )).

tff(u374,negated_conjecture,
    ( ~ ! [X0] :
          ( ~ m1_subset_1(X0,u1_struct_0(sK1))
          | k7_domain_1(u1_struct_0(sK1),sK3,X0) = k2_tarski(sK3,X0) )
    | ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | k7_domain_1(u1_struct_0(sK1),sK3,X0) = k2_tarski(sK3,X0) ) )).

tff(u373,negated_conjecture,
    ( ~ ! [X1] :
          ( ~ m1_subset_1(X1,u1_struct_0(sK1))
          | k7_domain_1(u1_struct_0(sK1),X1,sK2) = k2_tarski(X1,sK2) )
    | ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK1))
        | k7_domain_1(u1_struct_0(sK1),X1,sK2) = k2_tarski(X1,sK2) ) )).

tff(u372,negated_conjecture,
    ( ~ ! [X0] :
          ( ~ m1_subset_1(X0,u1_struct_0(sK1))
          | k7_domain_1(u1_struct_0(sK1),X0,sK3) = k2_tarski(X0,sK3) )
    | ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | k7_domain_1(u1_struct_0(sK1),X0,sK3) = k2_tarski(X0,sK3) ) )).

tff(u371,negated_conjecture,
    ( ~ ! [X2] :
          ( ~ m1_subset_1(X2,u1_struct_0(sK0))
          | k7_domain_1(u1_struct_0(sK0),X2,sK3) = k2_tarski(X2,sK3) )
    | ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k7_domain_1(u1_struct_0(sK0),X2,sK3) = k2_tarski(X2,sK3) ) )).

tff(u370,negated_conjecture,
    ( ~ ! [X3] :
          ( ~ m1_subset_1(X3,u1_struct_0(sK0))
          | k7_domain_1(u1_struct_0(sK0),X3,sK2) = k2_tarski(X3,sK2) )
    | ! [X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | k7_domain_1(u1_struct_0(sK0),X3,sK2) = k2_tarski(X3,sK2) ) )).

tff(u369,negated_conjecture,
    ( ~ ! [X2] :
          ( ~ m1_subset_1(X2,u1_struct_0(sK0))
          | k7_domain_1(u1_struct_0(sK0),sK3,X2) = k2_tarski(sK3,X2) )
    | ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k7_domain_1(u1_struct_0(sK0),sK3,X2) = k2_tarski(sK3,X2) ) )).

tff(u368,negated_conjecture,
    ( ~ ! [X3] :
          ( ~ m1_subset_1(X3,u1_struct_0(sK0))
          | k7_domain_1(u1_struct_0(sK0),sK2,X3) = k2_tarski(sK2,X3) )
    | ! [X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | k7_domain_1(u1_struct_0(sK0),sK2,X3) = k2_tarski(sK2,X3) ) )).

tff(u367,negated_conjecture,
    ( ~ ! [X1,X0] :
          ( ~ m1_subset_1(X1,u1_struct_0(sK0))
          | ~ m1_subset_1(X0,u1_struct_0(sK0))
          | k2_tarski(k2_tarski(sK3,sK3),k7_domain_1(u1_struct_0(sK0),X0,X1)) = k7_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k2_tarski(sK3,sK3),k7_domain_1(u1_struct_0(sK0),X0,X1)) )
    | ! [X1,X0] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_tarski(k2_tarski(sK3,sK3),k7_domain_1(u1_struct_0(sK0),X0,X1)) = k7_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k2_tarski(sK3,sK3),k7_domain_1(u1_struct_0(sK0),X0,X1)) ) )).

tff(u366,negated_conjecture,
    ( ~ ! [X1,X0] :
          ( ~ m1_subset_1(X1,u1_struct_0(sK0))
          | ~ m1_subset_1(X0,u1_struct_0(sK0))
          | k2_tarski(k7_domain_1(u1_struct_0(sK0),X0,X1),k2_tarski(sK3,sK3)) = k7_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k7_domain_1(u1_struct_0(sK0),X0,X1),k2_tarski(sK3,sK3)) )
    | ! [X1,X0] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_tarski(k7_domain_1(u1_struct_0(sK0),X0,X1),k2_tarski(sK3,sK3)) = k7_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k7_domain_1(u1_struct_0(sK0),X0,X1),k2_tarski(sK3,sK3)) ) )).

tff(u365,negated_conjecture,
    ( ~ ! [X1,X0] :
          ( ~ m1_subset_1(X1,u1_struct_0(sK0))
          | ~ m1_subset_1(X0,u1_struct_0(sK0))
          | k2_tarski(k2_tarski(sK3,sK3),k7_domain_1(u1_struct_0(sK0),X0,X1)) = k7_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k2_tarski(sK3,sK3),k7_domain_1(u1_struct_0(sK0),X0,X1)) )
    | ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_tarski(k2_tarski(sK3,sK3),k7_domain_1(u1_struct_0(sK0),X0,sK3)) = k7_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k2_tarski(sK3,sK3),k7_domain_1(u1_struct_0(sK0),X0,sK3)) ) )).

tff(u364,negated_conjecture,
    ( ~ ! [X1,X0] :
          ( ~ m1_subset_1(X1,u1_struct_0(sK0))
          | ~ m1_subset_1(X0,u1_struct_0(sK0))
          | k2_tarski(k2_tarski(sK3,sK3),k7_domain_1(u1_struct_0(sK0),X0,X1)) = k7_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k2_tarski(sK3,sK3),k7_domain_1(u1_struct_0(sK0),X0,X1)) )
    | ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k2_tarski(k2_tarski(sK3,sK3),k7_domain_1(u1_struct_0(sK0),X1,sK2)) = k7_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k2_tarski(sK3,sK3),k7_domain_1(u1_struct_0(sK0),X1,sK2)) ) )).

tff(u363,negated_conjecture,
    ( ~ ! [X1,X0] :
          ( ~ m1_subset_1(X1,u1_struct_0(sK0))
          | ~ m1_subset_1(X0,u1_struct_0(sK0))
          | k2_tarski(k2_tarski(sK3,sK3),k7_domain_1(u1_struct_0(sK0),X0,X1)) = k7_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k2_tarski(sK3,sK3),k7_domain_1(u1_struct_0(sK0),X0,X1)) )
    | ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_tarski(k2_tarski(sK3,sK3),k7_domain_1(u1_struct_0(sK0),sK3,X0)) = k7_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k2_tarski(sK3,sK3),k7_domain_1(u1_struct_0(sK0),sK3,X0)) ) )).

tff(u362,negated_conjecture,
    ( ~ ! [X1,X0] :
          ( ~ m1_subset_1(X1,u1_struct_0(sK0))
          | ~ m1_subset_1(X0,u1_struct_0(sK0))
          | k2_tarski(k2_tarski(sK3,sK3),k7_domain_1(u1_struct_0(sK0),X0,X1)) = k7_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k2_tarski(sK3,sK3),k7_domain_1(u1_struct_0(sK0),X0,X1)) )
    | ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k2_tarski(k2_tarski(sK3,sK3),k7_domain_1(u1_struct_0(sK0),sK2,X1)) = k7_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k2_tarski(sK3,sK3),k7_domain_1(u1_struct_0(sK0),sK2,X1)) ) )).

tff(u361,negated_conjecture,
    ( ~ ! [X1,X0] :
          ( ~ m1_subset_1(X1,u1_struct_0(sK0))
          | ~ m1_subset_1(X0,u1_struct_0(sK0))
          | k2_tarski(k2_tarski(sK3,sK3),k7_domain_1(u1_struct_0(sK0),X0,X1)) = k7_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k2_tarski(sK3,sK3),k7_domain_1(u1_struct_0(sK0),X0,X1)) )
    | ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_tarski(k2_tarski(sK3,sK3),k7_domain_1(u1_struct_0(sK0),X0,X0)) = k7_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k2_tarski(sK3,sK3),k7_domain_1(u1_struct_0(sK0),X0,X0)) ) )).

tff(u360,negated_conjecture,
    ( ~ ! [X1,X0] :
          ( ~ m1_subset_1(X1,u1_struct_0(sK0))
          | ~ m1_subset_1(X0,u1_struct_0(sK0))
          | k2_tarski(k7_domain_1(u1_struct_0(sK0),X0,X1),k2_tarski(sK3,sK3)) = k7_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k7_domain_1(u1_struct_0(sK0),X0,X1),k2_tarski(sK3,sK3)) )
    | ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_tarski(k7_domain_1(u1_struct_0(sK0),X0,sK3),k2_tarski(sK3,sK3)) = k7_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k7_domain_1(u1_struct_0(sK0),X0,sK3),k2_tarski(sK3,sK3)) ) )).

tff(u359,negated_conjecture,
    ( ~ ! [X1,X0] :
          ( ~ m1_subset_1(X1,u1_struct_0(sK0))
          | ~ m1_subset_1(X0,u1_struct_0(sK0))
          | k2_tarski(k7_domain_1(u1_struct_0(sK0),X0,X1),k2_tarski(sK3,sK3)) = k7_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k7_domain_1(u1_struct_0(sK0),X0,X1),k2_tarski(sK3,sK3)) )
    | ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k2_tarski(k7_domain_1(u1_struct_0(sK0),X1,sK2),k2_tarski(sK3,sK3)) = k7_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k7_domain_1(u1_struct_0(sK0),X1,sK2),k2_tarski(sK3,sK3)) ) )).

tff(u358,negated_conjecture,
    ( ~ ! [X1,X0] :
          ( ~ m1_subset_1(X1,u1_struct_0(sK0))
          | ~ m1_subset_1(X0,u1_struct_0(sK0))
          | k2_tarski(k7_domain_1(u1_struct_0(sK0),X0,X1),k2_tarski(sK3,sK3)) = k7_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k7_domain_1(u1_struct_0(sK0),X0,X1),k2_tarski(sK3,sK3)) )
    | ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_tarski(k7_domain_1(u1_struct_0(sK0),sK3,X0),k2_tarski(sK3,sK3)) = k7_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k7_domain_1(u1_struct_0(sK0),sK3,X0),k2_tarski(sK3,sK3)) ) )).

tff(u357,negated_conjecture,
    ( ~ ! [X1,X0] :
          ( ~ m1_subset_1(X1,u1_struct_0(sK0))
          | ~ m1_subset_1(X0,u1_struct_0(sK0))
          | k2_tarski(k7_domain_1(u1_struct_0(sK0),X0,X1),k2_tarski(sK3,sK3)) = k7_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k7_domain_1(u1_struct_0(sK0),X0,X1),k2_tarski(sK3,sK3)) )
    | ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k2_tarski(k7_domain_1(u1_struct_0(sK0),sK2,X1),k2_tarski(sK3,sK3)) = k7_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k7_domain_1(u1_struct_0(sK0),sK2,X1),k2_tarski(sK3,sK3)) ) )).

tff(u356,negated_conjecture,
    ( ~ ! [X1,X0] :
          ( ~ m1_subset_1(X1,u1_struct_0(sK0))
          | ~ m1_subset_1(X0,u1_struct_0(sK0))
          | k2_tarski(k7_domain_1(u1_struct_0(sK0),X0,X1),k2_tarski(sK3,sK3)) = k7_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k7_domain_1(u1_struct_0(sK0),X0,X1),k2_tarski(sK3,sK3)) )
    | ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_tarski(k7_domain_1(u1_struct_0(sK0),X0,X0),k2_tarski(sK3,sK3)) = k7_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k7_domain_1(u1_struct_0(sK0),X0,X0),k2_tarski(sK3,sK3)) ) )).

tff(u355,negated_conjecture,
    ( ~ ! [X1] :
          ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
          | k2_tarski(X1,k2_tarski(sK3,sK3)) = k7_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,k2_tarski(sK3,sK3)) )
    | ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_tarski(X1,k2_tarski(sK3,sK3)) = k7_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,k2_tarski(sK3,sK3)) ) )).

tff(u354,negated_conjecture,
    ( ~ ! [X0] :
          ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
          | k2_tarski(k2_tarski(sK3,sK3),X0) = k7_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k2_tarski(sK3,sK3),X0) )
    | ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_tarski(k2_tarski(sK3,sK3),X0) = k7_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k2_tarski(sK3,sK3),X0) ) )).

tff(u353,negated_conjecture,(
    m1_subset_1(sK3,u1_struct_0(sK1)) )).

tff(u352,negated_conjecture,(
    m1_subset_1(sK2,u1_struct_0(sK1)) )).

tff(u351,negated_conjecture,(
    m1_subset_1(sK3,u1_struct_0(sK0)) )).

tff(u350,negated_conjecture,(
    m1_subset_1(sK2,u1_struct_0(sK0)) )).

tff(u349,axiom,(
    ! [X1,X0,X2] :
      ( m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | ~ m1_subset_1(X2,X0)
      | v1_xboole_0(X0) ) )).

tff(u348,negated_conjecture,
    ( ~ m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u347,negated_conjecture,
    ( ~ m1_subset_1(k2_tarski(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_tarski(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u346,negated_conjecture,
    ( ~ m1_subset_1(k2_tarski(sK3,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_tarski(sK3,sK2),k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u345,negated_conjecture,
    ( ~ m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u344,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) )).

tff(u343,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1)) )).

tff(u342,axiom,(
    ! [X1,X0,X2] :
      ( v1_xboole_0(k1_zfmisc_1(X0))
      | k7_domain_1(k1_zfmisc_1(X0),k7_domain_1(X0,X1,X2),k7_domain_1(X0,X1,X2)) = k2_tarski(k7_domain_1(X0,X1,X2),k7_domain_1(X0,X1,X2))
      | ~ m1_subset_1(X1,X0)
      | ~ m1_subset_1(X2,X0)
      | v1_xboole_0(X0) ) )).

tff(u341,axiom,(
    ! [X5,X7,X4,X6] :
      ( v1_xboole_0(k1_zfmisc_1(X5))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
      | k7_domain_1(k1_zfmisc_1(X5),k7_domain_1(X5,X6,X7),X4) = k2_tarski(k7_domain_1(X5,X6,X7),X4)
      | ~ m1_subset_1(X6,X5)
      | ~ m1_subset_1(X7,X5)
      | v1_xboole_0(X5) ) )).

tff(u340,axiom,(
    ! [X5,X7,X4,X6] :
      ( v1_xboole_0(k1_zfmisc_1(X5))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
      | k7_domain_1(k1_zfmisc_1(X5),X4,k7_domain_1(X5,X6,X7)) = k2_tarski(X4,k7_domain_1(X5,X6,X7))
      | ~ m1_subset_1(X6,X5)
      | ~ m1_subset_1(X7,X5)
      | v1_xboole_0(X5) ) )).

tff(u339,negated_conjecture,
    ( ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u338,negated_conjecture,(
    ~ v2_struct_0(sK1) )).

tff(u337,negated_conjecture,(
    ~ v2_struct_0(sK0) )).

tff(u336,negated_conjecture,
    ( ~ ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK1) )).

tff(u335,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) )).

tff(u334,negated_conjecture,
    ( ~ ~ l1_struct_0(sK1)
    | ~ l1_orders_2(sK1) )).

tff(u333,negated_conjecture,(
    l1_orders_2(sK0) )).

tff(u332,axiom,(
    ! [X0] :
      ( ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ v2_struct_0(X0) ) )).

tff(u331,negated_conjecture,(
    v1_lattice3(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:37:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (2117)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.21/0.47  % (2125)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.47  % (2111)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.48  % (2104)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.48  % (2111)Refutation not found, incomplete strategy% (2111)------------------------------
% 0.21/0.48  % (2111)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (2111)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (2111)Memory used [KB]: 6140
% 0.21/0.48  % (2111)Time elapsed: 0.072 s
% 0.21/0.48  % (2111)------------------------------
% 0.21/0.48  % (2111)------------------------------
% 0.21/0.48  % (2126)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.21/0.49  % (2106)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.49  % (2118)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.21/0.49  % (2107)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.49  % (2107)Refutation not found, incomplete strategy% (2107)------------------------------
% 0.21/0.49  % (2107)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (2107)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (2107)Memory used [KB]: 10618
% 0.21/0.49  % (2107)Time elapsed: 0.095 s
% 0.21/0.49  % (2107)------------------------------
% 0.21/0.49  % (2107)------------------------------
% 0.21/0.50  % (2123)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.21/0.50  % (2105)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.50  % (2124)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.21/0.50  % (2113)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.21/0.50  % (2114)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.21/0.51  % (2109)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.51  % (2112)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.21/0.51  % (2112)Refutation not found, incomplete strategy% (2112)------------------------------
% 0.21/0.51  % (2112)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (2112)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (2112)Memory used [KB]: 10618
% 0.21/0.51  % (2112)Time elapsed: 0.109 s
% 0.21/0.51  % (2112)------------------------------
% 0.21/0.51  % (2112)------------------------------
% 0.21/0.51  % (2115)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.51  % (2122)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.21/0.51  % (2123)Refutation not found, incomplete strategy% (2123)------------------------------
% 0.21/0.51  % (2123)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (2123)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (2123)Memory used [KB]: 6140
% 0.21/0.51  % (2123)Time elapsed: 0.106 s
% 0.21/0.51  % (2123)------------------------------
% 0.21/0.51  % (2123)------------------------------
% 0.21/0.51  % (2108)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.52  % (2120)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.21/0.52  % (2119)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.21/0.52  % (2120)Refutation not found, incomplete strategy% (2120)------------------------------
% 0.21/0.52  % (2120)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (2120)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (2120)Memory used [KB]: 1535
% 0.21/0.52  % (2120)Time elapsed: 0.117 s
% 0.21/0.52  % (2120)------------------------------
% 0.21/0.52  % (2120)------------------------------
% 0.21/0.52  % (2114)Refutation not found, incomplete strategy% (2114)------------------------------
% 0.21/0.52  % (2114)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (2114)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (2114)Memory used [KB]: 10490
% 0.21/0.52  % (2114)Time elapsed: 0.119 s
% 0.21/0.52  % (2114)------------------------------
% 0.21/0.52  % (2114)------------------------------
% 0.21/0.52  % (2110)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.52  % (2121)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.21/0.52  % (2104)Refutation not found, incomplete strategy% (2104)------------------------------
% 0.21/0.52  % (2104)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (2104)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (2104)Memory used [KB]: 1663
% 0.21/0.52  % (2104)Time elapsed: 0.120 s
% 0.21/0.52  % (2104)------------------------------
% 0.21/0.52  % (2104)------------------------------
% 0.21/0.52  % (2110)Refutation not found, incomplete strategy% (2110)------------------------------
% 0.21/0.52  % (2110)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (2110)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (2110)Memory used [KB]: 10746
% 0.21/0.52  % (2110)Time elapsed: 0.089 s
% 0.21/0.52  % (2110)------------------------------
% 0.21/0.52  % (2110)------------------------------
% 0.21/0.52  % (2116)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.53  % (2127)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.21/0.53  % (2121)Refutation not found, incomplete strategy% (2121)------------------------------
% 0.21/0.53  % (2121)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (2121)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (2121)Memory used [KB]: 1791
% 0.21/0.53  % (2121)Time elapsed: 0.127 s
% 0.21/0.53  % (2121)------------------------------
% 0.21/0.53  % (2121)------------------------------
% 0.21/0.53  % (2127)Refutation not found, incomplete strategy% (2127)------------------------------
% 0.21/0.53  % (2127)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (2127)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (2127)Memory used [KB]: 10618
% 0.21/0.53  % (2127)Time elapsed: 0.130 s
% 0.21/0.53  % (2127)------------------------------
% 0.21/0.53  % (2127)------------------------------
% 0.21/0.53  % (2115)Refutation not found, incomplete strategy% (2115)------------------------------
% 0.21/0.53  % (2115)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (2115)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (2115)Memory used [KB]: 1663
% 0.21/0.53  % (2115)Time elapsed: 0.117 s
% 0.21/0.53  % (2115)------------------------------
% 0.21/0.53  % (2115)------------------------------
% 0.21/0.53  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.53  % (2116)# SZS output start Saturation.
% 0.21/0.53  tff(u395,negated_conjecture,
% 0.21/0.53      (k13_lattice3(sK1,sK2,sK3) != k13_lattice3(sK0,sK2,sK3))).
% 0.21/0.53  
% 0.21/0.53  tff(u394,negated_conjecture,
% 0.21/0.53      ((~(![X0] : ((~m1_subset_1(X0,u1_struct_0(sK1)) | (k7_domain_1(u1_struct_0(sK1),X0,sK3) = k2_tarski(X0,sK3)))))) | (k7_domain_1(u1_struct_0(sK1),sK3,sK3) = k2_tarski(sK3,sK3)))).
% 0.21/0.53  
% 0.21/0.53  tff(u393,negated_conjecture,
% 0.21/0.53      ((~(![X0] : ((~m1_subset_1(X0,u1_struct_0(sK1)) | (k7_domain_1(u1_struct_0(sK1),X0,sK3) = k2_tarski(X0,sK3)))))) | (k7_domain_1(u1_struct_0(sK1),sK2,sK3) = k2_tarski(sK2,sK3)))).
% 0.21/0.53  
% 0.21/0.53  tff(u392,negated_conjecture,
% 0.21/0.53      ((~(![X1] : ((~m1_subset_1(X1,u1_struct_0(sK1)) | (k7_domain_1(u1_struct_0(sK1),X1,sK2) = k2_tarski(X1,sK2)))))) | (k7_domain_1(u1_struct_0(sK1),sK3,sK2) = k2_tarski(sK3,sK2)))).
% 0.21/0.53  
% 0.21/0.53  tff(u391,negated_conjecture,
% 0.21/0.53      ((~(![X1] : ((~m1_subset_1(X1,u1_struct_0(sK1)) | (k7_domain_1(u1_struct_0(sK1),X1,sK2) = k2_tarski(X1,sK2)))))) | (k7_domain_1(u1_struct_0(sK1),sK2,sK2) = k2_tarski(sK2,sK2)))).
% 0.21/0.53  
% 0.21/0.53  tff(u390,negated_conjecture,
% 0.21/0.53      ((~(k7_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k2_tarski(sK3,sK3),k2_tarski(sK3,sK3)) = k2_tarski(k2_tarski(sK3,sK3),k2_tarski(sK3,sK3)))) | (k7_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k2_tarski(sK3,sK3),k2_tarski(sK3,sK3)) = k2_tarski(k2_tarski(sK3,sK3),k2_tarski(sK3,sK3))))).
% 0.21/0.53  
% 0.21/0.53  tff(u389,negated_conjecture,
% 0.21/0.53      ((~(![X2] : ((~m1_subset_1(X2,u1_struct_0(sK0)) | (k7_domain_1(u1_struct_0(sK0),X2,sK3) = k2_tarski(X2,sK3)))))) | (k2_tarski(sK3,sK3) = k7_domain_1(u1_struct_0(sK0),sK3,sK3)))).
% 0.21/0.53  
% 0.21/0.53  tff(u388,negated_conjecture,
% 0.21/0.53      ((~(![X2] : ((~m1_subset_1(X2,u1_struct_0(sK0)) | (k7_domain_1(u1_struct_0(sK0),X2,sK3) = k2_tarski(X2,sK3)))))) | (k2_tarski(sK2,sK3) = k7_domain_1(u1_struct_0(sK0),sK2,sK3)))).
% 0.21/0.53  
% 0.21/0.53  tff(u387,negated_conjecture,
% 0.21/0.53      ((~(![X3] : ((~m1_subset_1(X3,u1_struct_0(sK0)) | (k7_domain_1(u1_struct_0(sK0),X3,sK2) = k2_tarski(X3,sK2)))))) | (k2_tarski(sK3,sK2) = k7_domain_1(u1_struct_0(sK0),sK3,sK2)))).
% 0.21/0.53  
% 0.21/0.53  tff(u386,negated_conjecture,
% 0.21/0.53      ((~(![X3] : ((~m1_subset_1(X3,u1_struct_0(sK0)) | (k7_domain_1(u1_struct_0(sK0),X3,sK2) = k2_tarski(X3,sK2)))))) | (k2_tarski(sK2,sK2) = k7_domain_1(u1_struct_0(sK0),sK2,sK2)))).
% 0.21/0.53  
% 0.21/0.53  tff(u385,negated_conjecture,
% 0.21/0.53      ((~(![X0] : ((~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | (k2_tarski(k2_tarski(sK3,sK3),X0) = k7_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k2_tarski(sK3,sK3),X0)))))) | (~m1_subset_1(k2_tarski(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))) | (k2_tarski(k2_tarski(sK3,sK3),k2_tarski(sK2,sK3)) = k7_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k2_tarski(sK3,sK3),k2_tarski(sK2,sK3))))).
% 0.21/0.53  
% 0.21/0.53  tff(u384,negated_conjecture,
% 0.21/0.53      ((~(![X0] : ((~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | (k2_tarski(k2_tarski(sK3,sK3),X0) = k7_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k2_tarski(sK3,sK3),X0)))))) | (~m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))) | (k2_tarski(k2_tarski(sK3,sK3),k2_tarski(sK2,sK2)) = k7_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k2_tarski(sK3,sK3),k2_tarski(sK2,sK2))))).
% 0.21/0.53  
% 0.21/0.53  tff(u383,negated_conjecture,
% 0.21/0.53      ((~(![X0] : ((~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | (k2_tarski(k2_tarski(sK3,sK3),X0) = k7_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k2_tarski(sK3,sK3),X0)))))) | (~m1_subset_1(k2_tarski(sK3,sK2),k1_zfmisc_1(u1_struct_0(sK0)))) | (k2_tarski(k2_tarski(sK3,sK3),k2_tarski(sK3,sK2)) = k7_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k2_tarski(sK3,sK3),k2_tarski(sK3,sK2))))).
% 0.21/0.53  
% 0.21/0.53  tff(u382,negated_conjecture,
% 0.21/0.53      ((~(![X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | (k2_tarski(X1,k2_tarski(sK3,sK3)) = k7_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,k2_tarski(sK3,sK3))))))) | (~m1_subset_1(k2_tarski(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))) | (k2_tarski(k2_tarski(sK2,sK3),k2_tarski(sK3,sK3)) = k7_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k2_tarski(sK2,sK3),k2_tarski(sK3,sK3))))).
% 0.21/0.53  
% 0.21/0.53  tff(u381,negated_conjecture,
% 0.21/0.53      ((~(![X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | (k2_tarski(X1,k2_tarski(sK3,sK3)) = k7_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,k2_tarski(sK3,sK3))))))) | (~m1_subset_1(k2_tarski(sK3,sK2),k1_zfmisc_1(u1_struct_0(sK0)))) | (k2_tarski(k2_tarski(sK3,sK2),k2_tarski(sK3,sK3)) = k7_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k2_tarski(sK3,sK2),k2_tarski(sK3,sK3))))).
% 0.21/0.53  
% 0.21/0.53  tff(u380,negated_conjecture,
% 0.21/0.53      ((~(![X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | (k2_tarski(X1,k2_tarski(sK3,sK3)) = k7_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,k2_tarski(sK3,sK3))))))) | (~m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))) | (k2_tarski(k2_tarski(sK2,sK2),k2_tarski(sK3,sK3)) = k7_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k2_tarski(sK2,sK2),k2_tarski(sK3,sK3))))).
% 0.21/0.53  
% 0.21/0.53  tff(u379,negated_conjecture,
% 0.21/0.53      (sK2 = sK4)).
% 0.21/0.53  
% 0.21/0.53  tff(u378,negated_conjecture,
% 0.21/0.53      (sK3 = sK5)).
% 0.21/0.53  
% 0.21/0.53  tff(u377,axiom,
% 0.21/0.53      (![X1, X0] : ((~m1_subset_1(X0,X1) | v1_xboole_0(X1) | (k7_domain_1(X1,X0,X0) = k2_tarski(X0,X0)))))).
% 0.21/0.53  
% 0.21/0.53  tff(u376,axiom,
% 0.21/0.53      (![X1, X0, X2] : ((~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0) | (k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2)))))).
% 0.21/0.53  
% 0.21/0.53  tff(u375,negated_conjecture,
% 0.21/0.53      ((~(![X1] : ((~m1_subset_1(X1,u1_struct_0(sK1)) | (k7_domain_1(u1_struct_0(sK1),sK2,X1) = k2_tarski(sK2,X1)))))) | (![X1] : ((~m1_subset_1(X1,u1_struct_0(sK1)) | (k7_domain_1(u1_struct_0(sK1),sK2,X1) = k2_tarski(sK2,X1))))))).
% 0.21/0.53  
% 0.21/0.53  tff(u374,negated_conjecture,
% 0.21/0.53      ((~(![X0] : ((~m1_subset_1(X0,u1_struct_0(sK1)) | (k7_domain_1(u1_struct_0(sK1),sK3,X0) = k2_tarski(sK3,X0)))))) | (![X0] : ((~m1_subset_1(X0,u1_struct_0(sK1)) | (k7_domain_1(u1_struct_0(sK1),sK3,X0) = k2_tarski(sK3,X0))))))).
% 0.21/0.53  
% 0.21/0.53  tff(u373,negated_conjecture,
% 0.21/0.53      ((~(![X1] : ((~m1_subset_1(X1,u1_struct_0(sK1)) | (k7_domain_1(u1_struct_0(sK1),X1,sK2) = k2_tarski(X1,sK2)))))) | (![X1] : ((~m1_subset_1(X1,u1_struct_0(sK1)) | (k7_domain_1(u1_struct_0(sK1),X1,sK2) = k2_tarski(X1,sK2))))))).
% 0.21/0.53  
% 0.21/0.53  tff(u372,negated_conjecture,
% 0.21/0.53      ((~(![X0] : ((~m1_subset_1(X0,u1_struct_0(sK1)) | (k7_domain_1(u1_struct_0(sK1),X0,sK3) = k2_tarski(X0,sK3)))))) | (![X0] : ((~m1_subset_1(X0,u1_struct_0(sK1)) | (k7_domain_1(u1_struct_0(sK1),X0,sK3) = k2_tarski(X0,sK3))))))).
% 0.21/0.53  
% 0.21/0.53  tff(u371,negated_conjecture,
% 0.21/0.53      ((~(![X2] : ((~m1_subset_1(X2,u1_struct_0(sK0)) | (k7_domain_1(u1_struct_0(sK0),X2,sK3) = k2_tarski(X2,sK3)))))) | (![X2] : ((~m1_subset_1(X2,u1_struct_0(sK0)) | (k7_domain_1(u1_struct_0(sK0),X2,sK3) = k2_tarski(X2,sK3))))))).
% 0.21/0.53  
% 0.21/0.53  tff(u370,negated_conjecture,
% 0.21/0.53      ((~(![X3] : ((~m1_subset_1(X3,u1_struct_0(sK0)) | (k7_domain_1(u1_struct_0(sK0),X3,sK2) = k2_tarski(X3,sK2)))))) | (![X3] : ((~m1_subset_1(X3,u1_struct_0(sK0)) | (k7_domain_1(u1_struct_0(sK0),X3,sK2) = k2_tarski(X3,sK2))))))).
% 0.21/0.53  
% 0.21/0.53  tff(u369,negated_conjecture,
% 0.21/0.53      ((~(![X2] : ((~m1_subset_1(X2,u1_struct_0(sK0)) | (k7_domain_1(u1_struct_0(sK0),sK3,X2) = k2_tarski(sK3,X2)))))) | (![X2] : ((~m1_subset_1(X2,u1_struct_0(sK0)) | (k7_domain_1(u1_struct_0(sK0),sK3,X2) = k2_tarski(sK3,X2))))))).
% 0.21/0.53  
% 0.21/0.53  tff(u368,negated_conjecture,
% 0.21/0.53      ((~(![X3] : ((~m1_subset_1(X3,u1_struct_0(sK0)) | (k7_domain_1(u1_struct_0(sK0),sK2,X3) = k2_tarski(sK2,X3)))))) | (![X3] : ((~m1_subset_1(X3,u1_struct_0(sK0)) | (k7_domain_1(u1_struct_0(sK0),sK2,X3) = k2_tarski(sK2,X3))))))).
% 0.21/0.53  
% 0.21/0.53  tff(u367,negated_conjecture,
% 0.21/0.53      ((~(![X1, X0] : ((~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | (k2_tarski(k2_tarski(sK3,sK3),k7_domain_1(u1_struct_0(sK0),X0,X1)) = k7_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k2_tarski(sK3,sK3),k7_domain_1(u1_struct_0(sK0),X0,X1))))))) | (![X1, X0] : ((~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | (k2_tarski(k2_tarski(sK3,sK3),k7_domain_1(u1_struct_0(sK0),X0,X1)) = k7_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k2_tarski(sK3,sK3),k7_domain_1(u1_struct_0(sK0),X0,X1)))))))).
% 0.21/0.53  
% 0.21/0.53  tff(u366,negated_conjecture,
% 0.21/0.53      ((~(![X1, X0] : ((~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | (k2_tarski(k7_domain_1(u1_struct_0(sK0),X0,X1),k2_tarski(sK3,sK3)) = k7_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k7_domain_1(u1_struct_0(sK0),X0,X1),k2_tarski(sK3,sK3))))))) | (![X1, X0] : ((~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | (k2_tarski(k7_domain_1(u1_struct_0(sK0),X0,X1),k2_tarski(sK3,sK3)) = k7_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k7_domain_1(u1_struct_0(sK0),X0,X1),k2_tarski(sK3,sK3)))))))).
% 0.21/0.53  
% 0.21/0.53  tff(u365,negated_conjecture,
% 0.21/0.53      ((~(![X1, X0] : ((~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | (k2_tarski(k2_tarski(sK3,sK3),k7_domain_1(u1_struct_0(sK0),X0,X1)) = k7_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k2_tarski(sK3,sK3),k7_domain_1(u1_struct_0(sK0),X0,X1))))))) | (![X0] : ((~m1_subset_1(X0,u1_struct_0(sK0)) | (k2_tarski(k2_tarski(sK3,sK3),k7_domain_1(u1_struct_0(sK0),X0,sK3)) = k7_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k2_tarski(sK3,sK3),k7_domain_1(u1_struct_0(sK0),X0,sK3)))))))).
% 0.21/0.53  
% 0.21/0.53  tff(u364,negated_conjecture,
% 0.21/0.53      ((~(![X1, X0] : ((~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | (k2_tarski(k2_tarski(sK3,sK3),k7_domain_1(u1_struct_0(sK0),X0,X1)) = k7_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k2_tarski(sK3,sK3),k7_domain_1(u1_struct_0(sK0),X0,X1))))))) | (![X1] : ((~m1_subset_1(X1,u1_struct_0(sK0)) | (k2_tarski(k2_tarski(sK3,sK3),k7_domain_1(u1_struct_0(sK0),X1,sK2)) = k7_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k2_tarski(sK3,sK3),k7_domain_1(u1_struct_0(sK0),X1,sK2)))))))).
% 0.21/0.53  
% 0.21/0.53  tff(u363,negated_conjecture,
% 0.21/0.53      ((~(![X1, X0] : ((~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | (k2_tarski(k2_tarski(sK3,sK3),k7_domain_1(u1_struct_0(sK0),X0,X1)) = k7_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k2_tarski(sK3,sK3),k7_domain_1(u1_struct_0(sK0),X0,X1))))))) | (![X0] : ((~m1_subset_1(X0,u1_struct_0(sK0)) | (k2_tarski(k2_tarski(sK3,sK3),k7_domain_1(u1_struct_0(sK0),sK3,X0)) = k7_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k2_tarski(sK3,sK3),k7_domain_1(u1_struct_0(sK0),sK3,X0)))))))).
% 0.21/0.53  
% 0.21/0.53  tff(u362,negated_conjecture,
% 0.21/0.53      ((~(![X1, X0] : ((~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | (k2_tarski(k2_tarski(sK3,sK3),k7_domain_1(u1_struct_0(sK0),X0,X1)) = k7_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k2_tarski(sK3,sK3),k7_domain_1(u1_struct_0(sK0),X0,X1))))))) | (![X1] : ((~m1_subset_1(X1,u1_struct_0(sK0)) | (k2_tarski(k2_tarski(sK3,sK3),k7_domain_1(u1_struct_0(sK0),sK2,X1)) = k7_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k2_tarski(sK3,sK3),k7_domain_1(u1_struct_0(sK0),sK2,X1)))))))).
% 0.21/0.53  
% 0.21/0.53  tff(u361,negated_conjecture,
% 0.21/0.53      ((~(![X1, X0] : ((~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | (k2_tarski(k2_tarski(sK3,sK3),k7_domain_1(u1_struct_0(sK0),X0,X1)) = k7_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k2_tarski(sK3,sK3),k7_domain_1(u1_struct_0(sK0),X0,X1))))))) | (![X0] : ((~m1_subset_1(X0,u1_struct_0(sK0)) | (k2_tarski(k2_tarski(sK3,sK3),k7_domain_1(u1_struct_0(sK0),X0,X0)) = k7_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k2_tarski(sK3,sK3),k7_domain_1(u1_struct_0(sK0),X0,X0)))))))).
% 0.21/0.53  
% 0.21/0.53  tff(u360,negated_conjecture,
% 0.21/0.53      ((~(![X1, X0] : ((~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | (k2_tarski(k7_domain_1(u1_struct_0(sK0),X0,X1),k2_tarski(sK3,sK3)) = k7_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k7_domain_1(u1_struct_0(sK0),X0,X1),k2_tarski(sK3,sK3))))))) | (![X0] : ((~m1_subset_1(X0,u1_struct_0(sK0)) | (k2_tarski(k7_domain_1(u1_struct_0(sK0),X0,sK3),k2_tarski(sK3,sK3)) = k7_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k7_domain_1(u1_struct_0(sK0),X0,sK3),k2_tarski(sK3,sK3)))))))).
% 0.21/0.53  
% 0.21/0.53  tff(u359,negated_conjecture,
% 0.21/0.53      ((~(![X1, X0] : ((~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | (k2_tarski(k7_domain_1(u1_struct_0(sK0),X0,X1),k2_tarski(sK3,sK3)) = k7_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k7_domain_1(u1_struct_0(sK0),X0,X1),k2_tarski(sK3,sK3))))))) | (![X1] : ((~m1_subset_1(X1,u1_struct_0(sK0)) | (k2_tarski(k7_domain_1(u1_struct_0(sK0),X1,sK2),k2_tarski(sK3,sK3)) = k7_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k7_domain_1(u1_struct_0(sK0),X1,sK2),k2_tarski(sK3,sK3)))))))).
% 0.21/0.53  
% 0.21/0.53  tff(u358,negated_conjecture,
% 0.21/0.53      ((~(![X1, X0] : ((~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | (k2_tarski(k7_domain_1(u1_struct_0(sK0),X0,X1),k2_tarski(sK3,sK3)) = k7_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k7_domain_1(u1_struct_0(sK0),X0,X1),k2_tarski(sK3,sK3))))))) | (![X0] : ((~m1_subset_1(X0,u1_struct_0(sK0)) | (k2_tarski(k7_domain_1(u1_struct_0(sK0),sK3,X0),k2_tarski(sK3,sK3)) = k7_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k7_domain_1(u1_struct_0(sK0),sK3,X0),k2_tarski(sK3,sK3)))))))).
% 0.21/0.53  
% 0.21/0.53  tff(u357,negated_conjecture,
% 0.21/0.53      ((~(![X1, X0] : ((~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | (k2_tarski(k7_domain_1(u1_struct_0(sK0),X0,X1),k2_tarski(sK3,sK3)) = k7_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k7_domain_1(u1_struct_0(sK0),X0,X1),k2_tarski(sK3,sK3))))))) | (![X1] : ((~m1_subset_1(X1,u1_struct_0(sK0)) | (k2_tarski(k7_domain_1(u1_struct_0(sK0),sK2,X1),k2_tarski(sK3,sK3)) = k7_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k7_domain_1(u1_struct_0(sK0),sK2,X1),k2_tarski(sK3,sK3)))))))).
% 0.21/0.53  
% 0.21/0.53  tff(u356,negated_conjecture,
% 0.21/0.53      ((~(![X1, X0] : ((~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | (k2_tarski(k7_domain_1(u1_struct_0(sK0),X0,X1),k2_tarski(sK3,sK3)) = k7_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k7_domain_1(u1_struct_0(sK0),X0,X1),k2_tarski(sK3,sK3))))))) | (![X0] : ((~m1_subset_1(X0,u1_struct_0(sK0)) | (k2_tarski(k7_domain_1(u1_struct_0(sK0),X0,X0),k2_tarski(sK3,sK3)) = k7_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k7_domain_1(u1_struct_0(sK0),X0,X0),k2_tarski(sK3,sK3)))))))).
% 0.21/0.53  
% 0.21/0.53  tff(u355,negated_conjecture,
% 0.21/0.53      ((~(![X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | (k2_tarski(X1,k2_tarski(sK3,sK3)) = k7_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,k2_tarski(sK3,sK3))))))) | (![X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | (k2_tarski(X1,k2_tarski(sK3,sK3)) = k7_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,k2_tarski(sK3,sK3)))))))).
% 0.21/0.53  
% 0.21/0.53  tff(u354,negated_conjecture,
% 0.21/0.53      ((~(![X0] : ((~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | (k2_tarski(k2_tarski(sK3,sK3),X0) = k7_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k2_tarski(sK3,sK3),X0)))))) | (![X0] : ((~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | (k2_tarski(k2_tarski(sK3,sK3),X0) = k7_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k2_tarski(sK3,sK3),X0))))))).
% 0.21/0.53  
% 0.21/0.53  tff(u353,negated_conjecture,
% 0.21/0.53      m1_subset_1(sK3,u1_struct_0(sK1))).
% 0.21/0.53  
% 0.21/0.53  tff(u352,negated_conjecture,
% 0.21/0.53      m1_subset_1(sK2,u1_struct_0(sK1))).
% 0.21/0.53  
% 0.21/0.53  tff(u351,negated_conjecture,
% 0.21/0.53      m1_subset_1(sK3,u1_struct_0(sK0))).
% 0.21/0.53  
% 0.21/0.53  tff(u350,negated_conjecture,
% 0.21/0.53      m1_subset_1(sK2,u1_struct_0(sK0))).
% 0.21/0.53  
% 0.21/0.53  tff(u349,axiom,
% 0.21/0.53      (![X1, X0, X2] : ((m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | ~m1_subset_1(X2,X0) | v1_xboole_0(X0))))).
% 0.21/0.53  
% 0.21/0.53  tff(u348,negated_conjecture,
% 0.21/0.53      ((~m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(u1_struct_0(sK0)))) | m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(u1_struct_0(sK0))))).
% 0.21/0.53  
% 0.21/0.53  tff(u347,negated_conjecture,
% 0.21/0.53      ((~m1_subset_1(k2_tarski(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))) | m1_subset_1(k2_tarski(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))))).
% 0.21/0.53  
% 0.21/0.53  tff(u346,negated_conjecture,
% 0.21/0.53      ((~m1_subset_1(k2_tarski(sK3,sK2),k1_zfmisc_1(u1_struct_0(sK0)))) | m1_subset_1(k2_tarski(sK3,sK2),k1_zfmisc_1(u1_struct_0(sK0))))).
% 0.21/0.53  
% 0.21/0.53  tff(u345,negated_conjecture,
% 0.21/0.53      ((~m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))) | m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))))).
% 0.21/0.53  
% 0.21/0.53  tff(u344,axiom,
% 0.21/0.53      (![X0] : ((~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))))).
% 0.21/0.53  
% 0.21/0.53  tff(u343,negated_conjecture,
% 0.21/0.53      ((~v1_xboole_0(u1_struct_0(sK1))) | v1_xboole_0(u1_struct_0(sK1)))).
% 0.21/0.53  
% 0.21/0.53  tff(u342,axiom,
% 0.21/0.53      (![X1, X0, X2] : ((v1_xboole_0(k1_zfmisc_1(X0)) | (k7_domain_1(k1_zfmisc_1(X0),k7_domain_1(X0,X1,X2),k7_domain_1(X0,X1,X2)) = k2_tarski(k7_domain_1(X0,X1,X2),k7_domain_1(X0,X1,X2))) | ~m1_subset_1(X1,X0) | ~m1_subset_1(X2,X0) | v1_xboole_0(X0))))).
% 0.21/0.53  
% 0.21/0.53  tff(u341,axiom,
% 0.21/0.53      (![X5, X7, X4, X6] : ((v1_xboole_0(k1_zfmisc_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(X5)) | (k7_domain_1(k1_zfmisc_1(X5),k7_domain_1(X5,X6,X7),X4) = k2_tarski(k7_domain_1(X5,X6,X7),X4)) | ~m1_subset_1(X6,X5) | ~m1_subset_1(X7,X5) | v1_xboole_0(X5))))).
% 0.21/0.53  
% 0.21/0.53  tff(u340,axiom,
% 0.21/0.53      (![X5, X7, X4, X6] : ((v1_xboole_0(k1_zfmisc_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(X5)) | (k7_domain_1(k1_zfmisc_1(X5),X4,k7_domain_1(X5,X6,X7)) = k2_tarski(X4,k7_domain_1(X5,X6,X7))) | ~m1_subset_1(X6,X5) | ~m1_subset_1(X7,X5) | v1_xboole_0(X5))))).
% 0.21/0.53  
% 0.21/0.53  tff(u339,negated_conjecture,
% 0.21/0.53      ((~v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))) | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))))).
% 0.21/0.53  
% 0.21/0.53  tff(u338,negated_conjecture,
% 0.21/0.53      ~v2_struct_0(sK1)).
% 0.21/0.53  
% 0.21/0.53  tff(u337,negated_conjecture,
% 0.21/0.53      ~v2_struct_0(sK0)).
% 0.21/0.53  
% 0.21/0.53  tff(u336,negated_conjecture,
% 0.21/0.53      ((~~l1_struct_0(sK1)) | ~l1_struct_0(sK1))).
% 0.21/0.53  
% 0.21/0.53  tff(u335,axiom,
% 0.21/0.53      (![X0] : ((l1_struct_0(X0) | ~l1_orders_2(X0))))).
% 0.21/0.53  
% 0.21/0.53  tff(u334,negated_conjecture,
% 0.21/0.53      ((~~l1_struct_0(sK1)) | ~l1_orders_2(sK1))).
% 0.21/0.53  
% 0.21/0.53  tff(u333,negated_conjecture,
% 0.21/0.53      l1_orders_2(sK0)).
% 0.21/0.53  
% 0.21/0.53  tff(u332,axiom,
% 0.21/0.53      (![X0] : ((~v1_lattice3(X0) | ~l1_orders_2(X0) | ~v2_struct_0(X0))))).
% 0.21/0.53  
% 0.21/0.53  tff(u331,negated_conjecture,
% 0.21/0.53      v1_lattice3(sK0)).
% 0.21/0.53  
% 0.21/0.53  % (2116)# SZS output end Saturation.
% 0.21/0.53  % (2116)------------------------------
% 0.21/0.53  % (2116)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (2116)Termination reason: Satisfiable
% 0.21/0.53  
% 0.21/0.53  % (2116)Memory used [KB]: 10746
% 0.21/0.53  % (2116)Time elapsed: 0.131 s
% 0.21/0.53  % (2116)------------------------------
% 0.21/0.53  % (2116)------------------------------
% 0.21/0.53  % (2103)Success in time 0.175 s
%------------------------------------------------------------------------------
