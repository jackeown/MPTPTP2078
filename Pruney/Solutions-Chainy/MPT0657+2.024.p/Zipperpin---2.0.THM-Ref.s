%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rVTr8nSAZ0

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:43 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :  184 ( 568 expanded)
%              Number of leaves         :   15 ( 159 expanded)
%              Depth                    :   69
%              Number of atoms          : 2848 (11795 expanded)
%              Number of equality atoms :  199 ( 882 expanded)
%              Maximal formula depth    :   19 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(fc6_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) )
        & ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('1',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('5',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k1_relat_1 @ X5 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('8',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X6 ) @ X6 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X6 ) ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('9',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_relat_1 @ X5 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('16',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k1_relat_1 @ X5 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('17',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_relat_1 @ X5 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('20',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_relat_1 @ X5 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('21',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k5_relat_1 @ X6 @ ( k2_funct_1 @ X6 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X6 ) ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('22',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k5_relat_1 @ X6 @ ( k2_funct_1 @ X6 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X6 ) ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(l72_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ! [D: $i] :
              ( ( ( v1_relat_1 @ D )
                & ( v1_funct_1 @ D ) )
             => ( ( ( ( k2_relat_1 @ B )
                    = A )
                  & ( ( k5_relat_1 @ B @ C )
                    = ( k6_relat_1 @ ( k1_relat_1 @ D ) ) )
                  & ( ( k5_relat_1 @ C @ D )
                    = ( k6_relat_1 @ A ) ) )
               => ( D = B ) ) ) ) ) )).

thf('23',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k2_relat_1 @ X3 )
       != X2 )
      | ( ( k5_relat_1 @ X3 @ X1 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X4 ) ) )
      | ( ( k5_relat_1 @ X1 @ X4 )
       != ( k6_relat_1 @ X2 ) )
      | ( X4 = X3 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l72_funct_1])).

thf('24',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ( X4 = X3 )
      | ( ( k5_relat_1 @ X1 @ X4 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X3 ) ) )
      | ( ( k5_relat_1 @ X3 @ X1 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k6_relat_1 @ ( k1_relat_1 @ X0 ) )
       != ( k6_relat_1 @ ( k2_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k5_relat_1 @ X1 @ X0 )
       != ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ( ( k2_funct_1 @ X0 )
        = X1 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_funct_1 @ X0 )
        = X1 )
      | ( ( k5_relat_1 @ X1 @ X0 )
       != ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k6_relat_1 @ ( k1_relat_1 @ X0 ) )
       != ( k6_relat_1 @ ( k2_relat_1 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k6_relat_1 @ ( k1_relat_1 @ X0 ) )
       != ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
       != ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
       != ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k6_relat_1 @ ( k1_relat_1 @ X0 ) )
       != ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( k6_relat_1 @ ( k1_relat_1 @ X0 ) )
       != ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
       != ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['20','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = X0 )
      | ( ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
       != ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k6_relat_1 @ ( k1_relat_1 @ X0 ) )
       != ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k6_relat_1 @ ( k1_relat_1 @ X0 ) )
       != ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
       != ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['19','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = X0 )
      | ( ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
       != ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k6_relat_1 @ ( k1_relat_1 @ X0 ) )
       != ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k6_relat_1 @ ( k1_relat_1 @ X0 ) )
       != ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
       != ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['18','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = X0 )
      | ( ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
       != ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k6_relat_1 @ ( k1_relat_1 @ X0 ) )
       != ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( ( k6_relat_1 @ ( k2_relat_1 @ X0 ) )
       != ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k6_relat_1 @ ( k1_relat_1 @ X0 ) )
       != ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['17','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = X0 )
      | ( ( k6_relat_1 @ ( k1_relat_1 @ X0 ) )
       != ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( ( k6_relat_1 @ ( k1_relat_1 @ X0 ) )
       != ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['16','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['15','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['14','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['13','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k5_relat_1 @ X6 @ ( k2_funct_1 @ X6 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X6 ) ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['12','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['11','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['10','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('61',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X6 ) @ X6 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X6 ) ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['59','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['58','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['57','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['56','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['55','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['54','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['53','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['52','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf(t64_funct_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ A )
              & ( ( k2_relat_1 @ B )
                = ( k1_relat_1 @ A ) )
              & ( ( k5_relat_1 @ B @ A )
                = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) )
           => ( B
              = ( k2_funct_1 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ! [B: $i] :
            ( ( ( v1_relat_1 @ B )
              & ( v1_funct_1 @ B ) )
           => ( ( ( v2_funct_1 @ A )
                & ( ( k2_relat_1 @ B )
                  = ( k1_relat_1 @ A ) )
                & ( ( k5_relat_1 @ B @ A )
                  = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) )
             => ( B
                = ( k2_funct_1 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t64_funct_1])).

thf('80',plain,
    ( ( k5_relat_1 @ sk_B @ sk_A )
    = ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X6 ) @ X6 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X6 ) ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('82',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ( X4 = X3 )
      | ( ( k5_relat_1 @ X1 @ X4 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X3 ) ) )
      | ( ( k5_relat_1 @ X3 @ X1 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k6_relat_1 @ ( k2_relat_1 @ X0 ) )
       != ( k6_relat_1 @ ( k2_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k5_relat_1 @ X1 @ ( k2_funct_1 @ X0 ) )
       != ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ( X0 = X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( X0 = X1 )
      | ( ( k5_relat_1 @ X1 @ ( k2_funct_1 @ X0 ) )
       != ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k6_relat_1 @ ( k2_relat_1 @ X0 ) )
       != ( k6_relat_1 @ ( k2_relat_1 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_B @ sk_A )
       != ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v2_funct_1 @ sk_A )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_A ) )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ sk_A ) )
       != ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) )
      | ( sk_A = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['80','84'])).

thf('86',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( k2_relat_1 @ sk_B )
    = ( k1_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_B @ sk_A )
       != ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_A ) )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ sk_A ) )
       != ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) )
      | ( sk_A = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['85','86','87','88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v2_funct_1 @ sk_A )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( sk_A = X0 )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ sk_A ) )
       != ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_A ) )
      | ( ( k5_relat_1 @ sk_B @ sk_A )
       != ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['79','90'])).

thf('92',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( sk_A = X0 )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ sk_A ) )
       != ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_A ) )
      | ( ( k5_relat_1 @ sk_B @ sk_A )
       != ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['91','92','93','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v2_funct_1 @ sk_A )
      | ( ( k5_relat_1 @ sk_B @ sk_A )
       != ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ sk_A ) )
       != ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) )
      | ( sk_A = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['78','95'])).

thf('97',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_B @ sk_A )
       != ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ sk_A ) )
       != ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) )
      | ( sk_A = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['96','97','98','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_B @ sk_A )
       != ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( sk_A
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_funct_1 @ sk_A ) )
       != ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['77','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_B @ sk_A )
       != ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_funct_1 @ sk_A ) )
       != ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) )
      | ( sk_A
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( sk_A
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_funct_1 @ sk_A ) )
       != ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ sk_B @ sk_A )
       != ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,
    ( ( ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
     != ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_A ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_A ) )
    | ( ( k5_relat_1 @ sk_B @ sk_A )
     != ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A )
    | ( sk_A
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['8','103'])).

thf('105',plain,
    ( ( k5_relat_1 @ sk_B @ sk_A )
    = ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
     != ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_A ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_A ) )
    | ( ( k5_relat_1 @ sk_B @ sk_A )
     != ( k5_relat_1 @ sk_B @ sk_A ) )
    | ( sk_A
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['104','105','106','107','108'])).

thf('110',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_A ) ) )
    | ( sk_A
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_A ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) )
    | ( ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
     != ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_A ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_A ) )
    | ( ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
     != ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_A ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_A ) )
    | ( sk_A
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','110'])).

thf('112',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_A ) ) )
    | ( sk_A
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_A ) ) )
    | ( ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
     != ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_A ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_A ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_A ) )
    | ( ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
     != ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) )
    | ( sk_A
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['6','112'])).

thf('114',plain,
    ( ( sk_A
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_A ) ) )
    | ( ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
     != ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,
    ( ( ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) )
     != ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_A ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_A ) )
    | ( sk_A
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['5','114'])).

thf('116',plain,
    ( ( k2_relat_1 @ sk_B )
    = ( k1_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) )
     != ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_A ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_A ) )
    | ( sk_A
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['115','116','117','118','119'])).

thf('121',plain,
    ( ( sk_A
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_A ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['120'])).

thf('122',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_A ) )
    | ( sk_A
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['4','121'])).

thf('123',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_A ) )
    | ( sk_A
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['122','123','124','125'])).

thf('127',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A )
    | ( sk_A
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','126'])).

thf('128',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( ( sk_A
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['127','128','129','130'])).

thf('132',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A )
    | ( sk_A
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','131'])).

thf('133',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,
    ( sk_A
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['132','133','134','135'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('138',plain,
    ( ( ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
      = ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['136','137'])).

thf('139',plain,
    ( ( k5_relat_1 @ sk_B @ sk_A )
    = ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,
    ( ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
    = ( k5_relat_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['138','139','140','141','142'])).

thf('144',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_funct_1 @ X0 )
        = X1 )
      | ( ( k5_relat_1 @ X1 @ X0 )
       != ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k6_relat_1 @ ( k1_relat_1 @ X0 ) )
       != ( k6_relat_1 @ ( k2_relat_1 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('145',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ sk_A )
       != ( k5_relat_1 @ sk_B @ sk_A ) )
      | ( ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) )
       != ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v2_funct_1 @ sk_A )
      | ( ( k2_funct_1 @ sk_A )
        = X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,
    ( ( k2_relat_1 @ sk_B )
    = ( k1_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ sk_A )
       != ( k5_relat_1 @ sk_B @ sk_A ) )
      | ( ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) )
       != ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
      | ( ( k2_funct_1 @ sk_A )
        = X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['145','146','147','148','149'])).

thf('151',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v2_funct_1 @ sk_A )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) )
      | ( ( k2_funct_1 @ sk_A )
        = X0 )
      | ( ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) )
       != ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
      | ( ( k5_relat_1 @ X0 @ sk_A )
       != ( k5_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','150'])).

thf('152',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) )
      | ( ( k2_funct_1 @ sk_A )
        = X0 )
      | ( ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) )
       != ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
      | ( ( k5_relat_1 @ X0 @ sk_A )
       != ( k5_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['151','152','153','154'])).

thf('156',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v2_funct_1 @ sk_A )
      | ( ( k5_relat_1 @ X0 @ sk_A )
       != ( k5_relat_1 @ sk_B @ sk_A ) )
      | ( ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) )
       != ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
      | ( ( k2_funct_1 @ sk_A )
        = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','155'])).

thf('157',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ sk_A )
       != ( k5_relat_1 @ sk_B @ sk_A ) )
      | ( ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) )
       != ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
      | ( ( k2_funct_1 @ sk_A )
        = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['156','157','158','159'])).

thf('161',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( ( k2_funct_1 @ sk_A )
      = sk_B )
    | ( ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) )
     != ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(eq_res,[status(thm)],['160'])).

thf('162',plain,
    ( ( ( k2_funct_1 @ sk_A )
      = sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['161'])).

thf('163',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,
    ( ( k2_funct_1 @ sk_A )
    = sk_B ),
    inference(demod,[status(thm)],['162','163','164'])).

thf('166',plain,(
    sk_B
 != ( k2_funct_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['165','166'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rVTr8nSAZ0
% 0.16/0.38  % Computer   : n012.cluster.edu
% 0.16/0.38  % Model      : x86_64 x86_64
% 0.16/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.38  % Memory     : 8042.1875MB
% 0.16/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.38  % CPULimit   : 60
% 0.16/0.38  % DateTime   : Tue Dec  1 19:20:37 EST 2020
% 0.16/0.38  % CPUTime    : 
% 0.16/0.38  % Running portfolio for 600 s
% 0.16/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.38  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 0.59/0.82  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.59/0.82  % Solved by: fo/fo7.sh
% 0.59/0.82  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.82  % done 269 iterations in 0.326s
% 0.59/0.82  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.59/0.82  % SZS output start Refutation
% 0.59/0.82  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.59/0.82  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.82  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.59/0.82  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.59/0.82  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.59/0.82  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.59/0.82  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.59/0.82  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.59/0.82  thf(sk_B_type, type, sk_B: $i).
% 0.59/0.82  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.59/0.82  thf(fc6_funct_1, axiom,
% 0.59/0.82    (![A:$i]:
% 0.59/0.82     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 0.59/0.82       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.59/0.82         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) & 
% 0.59/0.82         ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.59/0.82  thf('0', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ~ (v2_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_relat_1 @ X0))),
% 0.59/0.82      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.59/0.82  thf('1', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         ((v1_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ~ (v2_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_relat_1 @ X0))),
% 0.59/0.82      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.59/0.82  thf('2', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         ((v1_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ~ (v2_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_relat_1 @ X0))),
% 0.59/0.82      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.59/0.82  thf('3', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ~ (v2_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_relat_1 @ X0))),
% 0.59/0.82      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.59/0.82  thf('4', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ~ (v2_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_relat_1 @ X0))),
% 0.59/0.82      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.59/0.82  thf(t55_funct_1, axiom,
% 0.59/0.82    (![A:$i]:
% 0.59/0.82     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.59/0.82       ( ( v2_funct_1 @ A ) =>
% 0.59/0.82         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.59/0.82           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.59/0.82  thf('5', plain,
% 0.59/0.82      (![X5 : $i]:
% 0.59/0.82         (~ (v2_funct_1 @ X5)
% 0.59/0.82          | ((k1_relat_1 @ X5) = (k2_relat_1 @ (k2_funct_1 @ X5)))
% 0.59/0.82          | ~ (v1_funct_1 @ X5)
% 0.59/0.82          | ~ (v1_relat_1 @ X5))),
% 0.59/0.82      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.59/0.82  thf('6', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         ((v1_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ~ (v2_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_relat_1 @ X0))),
% 0.59/0.82      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.59/0.82  thf('7', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ~ (v2_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_relat_1 @ X0))),
% 0.59/0.82      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.59/0.82  thf(t61_funct_1, axiom,
% 0.59/0.82    (![A:$i]:
% 0.59/0.82     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.59/0.82       ( ( v2_funct_1 @ A ) =>
% 0.59/0.82         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.59/0.82             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.59/0.82           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.59/0.82             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.59/0.82  thf('8', plain,
% 0.59/0.82      (![X6 : $i]:
% 0.59/0.82         (~ (v2_funct_1 @ X6)
% 0.59/0.82          | ((k5_relat_1 @ (k2_funct_1 @ X6) @ X6)
% 0.59/0.82              = (k6_relat_1 @ (k2_relat_1 @ X6)))
% 0.59/0.82          | ~ (v1_funct_1 @ X6)
% 0.59/0.82          | ~ (v1_relat_1 @ X6))),
% 0.59/0.82      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.59/0.82  thf('9', plain,
% 0.59/0.82      (![X5 : $i]:
% 0.59/0.82         (~ (v2_funct_1 @ X5)
% 0.59/0.82          | ((k2_relat_1 @ X5) = (k1_relat_1 @ (k2_funct_1 @ X5)))
% 0.59/0.82          | ~ (v1_funct_1 @ X5)
% 0.59/0.82          | ~ (v1_relat_1 @ X5))),
% 0.59/0.82      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.59/0.82  thf('10', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ~ (v2_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_relat_1 @ X0))),
% 0.59/0.82      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.59/0.82  thf('11', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         ((v1_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ~ (v2_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_relat_1 @ X0))),
% 0.59/0.82      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.59/0.82  thf('12', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ~ (v2_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_relat_1 @ X0))),
% 0.59/0.82      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.59/0.82  thf('13', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ~ (v2_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_relat_1 @ X0))),
% 0.59/0.82      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.59/0.82  thf('14', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         ((v1_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ~ (v2_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_relat_1 @ X0))),
% 0.59/0.82      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.59/0.82  thf('15', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ~ (v2_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_relat_1 @ X0))),
% 0.59/0.82      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.59/0.82  thf('16', plain,
% 0.59/0.82      (![X5 : $i]:
% 0.59/0.82         (~ (v2_funct_1 @ X5)
% 0.59/0.82          | ((k1_relat_1 @ X5) = (k2_relat_1 @ (k2_funct_1 @ X5)))
% 0.59/0.82          | ~ (v1_funct_1 @ X5)
% 0.59/0.82          | ~ (v1_relat_1 @ X5))),
% 0.59/0.82      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.59/0.82  thf('17', plain,
% 0.59/0.82      (![X5 : $i]:
% 0.59/0.82         (~ (v2_funct_1 @ X5)
% 0.59/0.82          | ((k2_relat_1 @ X5) = (k1_relat_1 @ (k2_funct_1 @ X5)))
% 0.59/0.82          | ~ (v1_funct_1 @ X5)
% 0.59/0.82          | ~ (v1_relat_1 @ X5))),
% 0.59/0.82      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.59/0.82  thf('18', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         ((v1_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ~ (v2_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_relat_1 @ X0))),
% 0.59/0.82      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.59/0.82  thf('19', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ~ (v2_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_relat_1 @ X0))),
% 0.59/0.82      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.59/0.82  thf('20', plain,
% 0.59/0.82      (![X5 : $i]:
% 0.59/0.82         (~ (v2_funct_1 @ X5)
% 0.59/0.82          | ((k2_relat_1 @ X5) = (k1_relat_1 @ (k2_funct_1 @ X5)))
% 0.59/0.82          | ~ (v1_funct_1 @ X5)
% 0.59/0.82          | ~ (v1_relat_1 @ X5))),
% 0.59/0.82      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.59/0.82  thf('21', plain,
% 0.59/0.82      (![X6 : $i]:
% 0.59/0.82         (~ (v2_funct_1 @ X6)
% 0.59/0.82          | ((k5_relat_1 @ X6 @ (k2_funct_1 @ X6))
% 0.59/0.82              = (k6_relat_1 @ (k1_relat_1 @ X6)))
% 0.59/0.82          | ~ (v1_funct_1 @ X6)
% 0.59/0.82          | ~ (v1_relat_1 @ X6))),
% 0.59/0.82      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.59/0.82  thf('22', plain,
% 0.59/0.82      (![X6 : $i]:
% 0.59/0.82         (~ (v2_funct_1 @ X6)
% 0.59/0.82          | ((k5_relat_1 @ X6 @ (k2_funct_1 @ X6))
% 0.59/0.82              = (k6_relat_1 @ (k1_relat_1 @ X6)))
% 0.59/0.82          | ~ (v1_funct_1 @ X6)
% 0.59/0.82          | ~ (v1_relat_1 @ X6))),
% 0.59/0.82      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.59/0.82  thf(l72_funct_1, axiom,
% 0.59/0.82    (![A:$i,B:$i]:
% 0.59/0.82     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.59/0.82       ( ![C:$i]:
% 0.59/0.82         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.59/0.82           ( ![D:$i]:
% 0.59/0.82             ( ( ( v1_relat_1 @ D ) & ( v1_funct_1 @ D ) ) =>
% 0.59/0.82               ( ( ( ( k2_relat_1 @ B ) = ( A ) ) & 
% 0.59/0.82                   ( ( k5_relat_1 @ B @ C ) =
% 0.59/0.82                     ( k6_relat_1 @ ( k1_relat_1 @ D ) ) ) & 
% 0.59/0.82                   ( ( k5_relat_1 @ C @ D ) = ( k6_relat_1 @ A ) ) ) =>
% 0.59/0.82                 ( ( D ) = ( B ) ) ) ) ) ) ) ))).
% 0.59/0.82  thf('23', plain,
% 0.59/0.82      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.59/0.82         (~ (v1_relat_1 @ X1)
% 0.59/0.82          | ~ (v1_funct_1 @ X1)
% 0.59/0.82          | ((k2_relat_1 @ X3) != (X2))
% 0.59/0.82          | ((k5_relat_1 @ X3 @ X1) != (k6_relat_1 @ (k1_relat_1 @ X4)))
% 0.59/0.82          | ((k5_relat_1 @ X1 @ X4) != (k6_relat_1 @ X2))
% 0.59/0.82          | ((X4) = (X3))
% 0.59/0.82          | ~ (v1_funct_1 @ X4)
% 0.59/0.82          | ~ (v1_relat_1 @ X4)
% 0.59/0.82          | ~ (v1_funct_1 @ X3)
% 0.59/0.82          | ~ (v1_relat_1 @ X3))),
% 0.59/0.82      inference('cnf', [status(esa)], [l72_funct_1])).
% 0.59/0.82  thf('24', plain,
% 0.59/0.82      (![X1 : $i, X3 : $i, X4 : $i]:
% 0.59/0.82         (~ (v1_relat_1 @ X3)
% 0.59/0.82          | ~ (v1_funct_1 @ X3)
% 0.59/0.82          | ~ (v1_relat_1 @ X4)
% 0.59/0.82          | ~ (v1_funct_1 @ X4)
% 0.59/0.82          | ((X4) = (X3))
% 0.59/0.82          | ((k5_relat_1 @ X1 @ X4) != (k6_relat_1 @ (k2_relat_1 @ X3)))
% 0.59/0.82          | ((k5_relat_1 @ X3 @ X1) != (k6_relat_1 @ (k1_relat_1 @ X4)))
% 0.59/0.82          | ~ (v1_funct_1 @ X1)
% 0.59/0.82          | ~ (v1_relat_1 @ X1))),
% 0.59/0.82      inference('simplify', [status(thm)], ['23'])).
% 0.59/0.82  thf('25', plain,
% 0.59/0.82      (![X0 : $i, X1 : $i]:
% 0.59/0.82         (((k6_relat_1 @ (k1_relat_1 @ X0)) != (k6_relat_1 @ (k2_relat_1 @ X1)))
% 0.59/0.82          | ~ (v1_relat_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v2_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_relat_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ((k5_relat_1 @ X1 @ X0)
% 0.59/0.82              != (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 0.59/0.82          | ((k2_funct_1 @ X0) = (X1))
% 0.59/0.82          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ~ (v1_funct_1 @ X1)
% 0.59/0.82          | ~ (v1_relat_1 @ X1))),
% 0.59/0.82      inference('sup-', [status(thm)], ['22', '24'])).
% 0.59/0.82  thf('26', plain,
% 0.59/0.82      (![X0 : $i, X1 : $i]:
% 0.59/0.82         (~ (v1_relat_1 @ X1)
% 0.59/0.82          | ~ (v1_funct_1 @ X1)
% 0.59/0.82          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ((k2_funct_1 @ X0) = (X1))
% 0.59/0.82          | ((k5_relat_1 @ X1 @ X0)
% 0.59/0.82              != (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 0.59/0.82          | ~ (v2_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_relat_1 @ X0)
% 0.59/0.82          | ((k6_relat_1 @ (k1_relat_1 @ X0))
% 0.59/0.82              != (k6_relat_1 @ (k2_relat_1 @ X1))))),
% 0.59/0.82      inference('simplify', [status(thm)], ['25'])).
% 0.59/0.82  thf('27', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         (((k6_relat_1 @ (k1_relat_1 @ X0))
% 0.59/0.82            != (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))
% 0.59/0.82          | ~ (v1_relat_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v2_funct_1 @ X0)
% 0.59/0.82          | ((k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.59/0.82              != (k6_relat_1 @ (k2_relat_1 @ X0)))
% 0.59/0.82          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ((k2_funct_1 @ (k2_funct_1 @ X0)) = (X0))
% 0.59/0.82          | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.59/0.82          | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_relat_1 @ X0))),
% 0.59/0.82      inference('sup-', [status(thm)], ['21', '26'])).
% 0.59/0.82  thf('28', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         (~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.59/0.82          | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.59/0.82          | ((k2_funct_1 @ (k2_funct_1 @ X0)) = (X0))
% 0.59/0.82          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ((k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.59/0.82              != (k6_relat_1 @ (k2_relat_1 @ X0)))
% 0.59/0.82          | ~ (v2_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_relat_1 @ X0)
% 0.59/0.82          | ((k6_relat_1 @ (k1_relat_1 @ X0))
% 0.59/0.82              != (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))))),
% 0.59/0.82      inference('simplify', [status(thm)], ['27'])).
% 0.59/0.82  thf('29', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         (((k6_relat_1 @ (k1_relat_1 @ X0))
% 0.59/0.82            != (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 0.59/0.82          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ~ (v1_relat_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v2_funct_1 @ X0)
% 0.59/0.82          | ((k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.59/0.82              != (k6_relat_1 @ (k2_relat_1 @ X0)))
% 0.59/0.82          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ((k2_funct_1 @ (k2_funct_1 @ X0)) = (X0))
% 0.59/0.82          | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.59/0.82          | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 0.59/0.82      inference('sup-', [status(thm)], ['20', '28'])).
% 0.59/0.82  thf('30', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         (~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.59/0.82          | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.59/0.82          | ((k2_funct_1 @ (k2_funct_1 @ X0)) = (X0))
% 0.59/0.82          | ((k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.59/0.82              != (k6_relat_1 @ (k2_relat_1 @ X0)))
% 0.59/0.82          | ~ (v2_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_relat_1 @ X0)
% 0.59/0.82          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ((k6_relat_1 @ (k1_relat_1 @ X0))
% 0.59/0.82              != (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.59/0.82      inference('simplify', [status(thm)], ['29'])).
% 0.59/0.82  thf('31', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ((k6_relat_1 @ (k1_relat_1 @ X0))
% 0.59/0.82              != (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 0.59/0.82          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ~ (v1_relat_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v2_funct_1 @ X0)
% 0.59/0.82          | ((k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.59/0.82              != (k6_relat_1 @ (k2_relat_1 @ X0)))
% 0.59/0.82          | ((k2_funct_1 @ (k2_funct_1 @ X0)) = (X0))
% 0.59/0.82          | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 0.59/0.82      inference('sup-', [status(thm)], ['19', '30'])).
% 0.59/0.82  thf('32', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         (~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.59/0.82          | ((k2_funct_1 @ (k2_funct_1 @ X0)) = (X0))
% 0.59/0.82          | ((k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.59/0.82              != (k6_relat_1 @ (k2_relat_1 @ X0)))
% 0.59/0.82          | ~ (v2_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_relat_1 @ X0)
% 0.59/0.82          | ((k6_relat_1 @ (k1_relat_1 @ X0))
% 0.59/0.82              != (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 0.59/0.82          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.59/0.82      inference('simplify', [status(thm)], ['31'])).
% 0.59/0.82  thf('33', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ((k6_relat_1 @ (k1_relat_1 @ X0))
% 0.59/0.82              != (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 0.59/0.82          | ~ (v1_relat_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v2_funct_1 @ X0)
% 0.59/0.82          | ((k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.59/0.82              != (k6_relat_1 @ (k2_relat_1 @ X0)))
% 0.59/0.82          | ((k2_funct_1 @ (k2_funct_1 @ X0)) = (X0)))),
% 0.59/0.82      inference('sup-', [status(thm)], ['18', '32'])).
% 0.59/0.82  thf('34', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         (((k2_funct_1 @ (k2_funct_1 @ X0)) = (X0))
% 0.59/0.82          | ((k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.59/0.82              != (k6_relat_1 @ (k2_relat_1 @ X0)))
% 0.59/0.82          | ~ (v2_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_relat_1 @ X0)
% 0.59/0.82          | ((k6_relat_1 @ (k1_relat_1 @ X0))
% 0.59/0.82              != (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 0.59/0.82          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.59/0.82      inference('simplify', [status(thm)], ['33'])).
% 0.59/0.82  thf('35', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         (((k6_relat_1 @ (k2_relat_1 @ X0)) != (k6_relat_1 @ (k2_relat_1 @ X0)))
% 0.59/0.82          | ~ (v1_relat_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v2_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ((k6_relat_1 @ (k1_relat_1 @ X0))
% 0.59/0.82              != (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 0.59/0.82          | ~ (v1_relat_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v2_funct_1 @ X0)
% 0.59/0.82          | ((k2_funct_1 @ (k2_funct_1 @ X0)) = (X0)))),
% 0.59/0.82      inference('sup-', [status(thm)], ['17', '34'])).
% 0.59/0.82  thf('36', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         (((k2_funct_1 @ (k2_funct_1 @ X0)) = (X0))
% 0.59/0.82          | ((k6_relat_1 @ (k1_relat_1 @ X0))
% 0.59/0.82              != (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 0.59/0.82          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ~ (v2_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_relat_1 @ X0))),
% 0.59/0.82      inference('simplify', [status(thm)], ['35'])).
% 0.59/0.82  thf('37', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         (((k6_relat_1 @ (k1_relat_1 @ X0)) != (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.59/0.82          | ~ (v1_relat_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v2_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_relat_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v2_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ((k2_funct_1 @ (k2_funct_1 @ X0)) = (X0)))),
% 0.59/0.82      inference('sup-', [status(thm)], ['16', '36'])).
% 0.59/0.82  thf('38', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         (((k2_funct_1 @ (k2_funct_1 @ X0)) = (X0))
% 0.59/0.82          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ~ (v2_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_relat_1 @ X0))),
% 0.59/0.82      inference('simplify', [status(thm)], ['37'])).
% 0.59/0.82  thf('39', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         (~ (v1_relat_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v2_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_relat_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v2_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ((k2_funct_1 @ (k2_funct_1 @ X0)) = (X0)))),
% 0.59/0.82      inference('sup-', [status(thm)], ['15', '38'])).
% 0.59/0.82  thf('40', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         (((k2_funct_1 @ (k2_funct_1 @ X0)) = (X0))
% 0.59/0.82          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ~ (v2_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_relat_1 @ X0))),
% 0.59/0.82      inference('simplify', [status(thm)], ['39'])).
% 0.59/0.82  thf('41', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         (~ (v1_relat_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v2_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_relat_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v2_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ((k2_funct_1 @ (k2_funct_1 @ X0)) = (X0)))),
% 0.59/0.82      inference('sup-', [status(thm)], ['14', '40'])).
% 0.59/0.82  thf('42', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         (((k2_funct_1 @ (k2_funct_1 @ X0)) = (X0))
% 0.59/0.82          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ~ (v2_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_relat_1 @ X0))),
% 0.59/0.82      inference('simplify', [status(thm)], ['41'])).
% 0.59/0.82  thf('43', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         (~ (v1_relat_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v2_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_relat_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v2_funct_1 @ X0)
% 0.59/0.82          | ((k2_funct_1 @ (k2_funct_1 @ X0)) = (X0)))),
% 0.59/0.82      inference('sup-', [status(thm)], ['13', '42'])).
% 0.59/0.82  thf('44', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         (((k2_funct_1 @ (k2_funct_1 @ X0)) = (X0))
% 0.59/0.82          | ~ (v2_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_relat_1 @ X0))),
% 0.59/0.82      inference('simplify', [status(thm)], ['43'])).
% 0.59/0.82  thf('45', plain,
% 0.59/0.82      (![X6 : $i]:
% 0.59/0.82         (~ (v2_funct_1 @ X6)
% 0.59/0.82          | ((k5_relat_1 @ X6 @ (k2_funct_1 @ X6))
% 0.59/0.82              = (k6_relat_1 @ (k1_relat_1 @ X6)))
% 0.59/0.82          | ~ (v1_funct_1 @ X6)
% 0.59/0.82          | ~ (v1_relat_1 @ X6))),
% 0.59/0.82      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.59/0.82  thf('46', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         (((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.59/0.82            = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 0.59/0.82          | ~ (v1_relat_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v2_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.59/0.82      inference('sup+', [status(thm)], ['44', '45'])).
% 0.59/0.82  thf('47', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         (~ (v1_relat_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v2_funct_1 @ X0)
% 0.59/0.82          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ~ (v2_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_relat_1 @ X0)
% 0.59/0.82          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.59/0.82              = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.59/0.82      inference('sup-', [status(thm)], ['12', '46'])).
% 0.59/0.82  thf('48', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         (((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.59/0.82            = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 0.59/0.82          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ~ (v2_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_relat_1 @ X0))),
% 0.59/0.82      inference('simplify', [status(thm)], ['47'])).
% 0.59/0.82  thf('49', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         (~ (v1_relat_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v2_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_relat_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v2_funct_1 @ X0)
% 0.59/0.82          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.59/0.82              = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.59/0.82      inference('sup-', [status(thm)], ['11', '48'])).
% 0.59/0.82  thf('50', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         (((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.59/0.82            = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 0.59/0.82          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ~ (v2_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_relat_1 @ X0))),
% 0.59/0.82      inference('simplify', [status(thm)], ['49'])).
% 0.59/0.82  thf('51', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         (~ (v1_relat_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v2_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_relat_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v2_funct_1 @ X0)
% 0.59/0.82          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.59/0.82              = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.59/0.82      inference('sup-', [status(thm)], ['10', '50'])).
% 0.59/0.82  thf('52', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         (((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.59/0.82            = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 0.59/0.82          | ~ (v2_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_relat_1 @ X0))),
% 0.59/0.82      inference('simplify', [status(thm)], ['51'])).
% 0.59/0.82  thf('53', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ~ (v2_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_relat_1 @ X0))),
% 0.59/0.82      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.59/0.82  thf('54', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         ((v1_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ~ (v2_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_relat_1 @ X0))),
% 0.59/0.82      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.59/0.82  thf('55', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ~ (v2_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_relat_1 @ X0))),
% 0.59/0.82      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.59/0.82  thf('56', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         (((k2_funct_1 @ (k2_funct_1 @ X0)) = (X0))
% 0.59/0.82          | ~ (v2_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_relat_1 @ X0))),
% 0.59/0.82      inference('simplify', [status(thm)], ['43'])).
% 0.59/0.82  thf('57', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ~ (v2_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_relat_1 @ X0))),
% 0.59/0.82      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.59/0.82  thf('58', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         ((v1_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ~ (v2_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_relat_1 @ X0))),
% 0.59/0.82      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.59/0.82  thf('59', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ~ (v2_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_relat_1 @ X0))),
% 0.59/0.82      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.59/0.82  thf('60', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         (((k2_funct_1 @ (k2_funct_1 @ X0)) = (X0))
% 0.59/0.82          | ~ (v2_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_relat_1 @ X0))),
% 0.59/0.82      inference('simplify', [status(thm)], ['43'])).
% 0.59/0.82  thf('61', plain,
% 0.59/0.82      (![X6 : $i]:
% 0.59/0.82         (~ (v2_funct_1 @ X6)
% 0.59/0.82          | ((k5_relat_1 @ (k2_funct_1 @ X6) @ X6)
% 0.59/0.82              = (k6_relat_1 @ (k2_relat_1 @ X6)))
% 0.59/0.82          | ~ (v1_funct_1 @ X6)
% 0.59/0.82          | ~ (v1_relat_1 @ X6))),
% 0.59/0.82      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.59/0.82  thf('62', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         (((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.59/0.82            = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 0.59/0.82          | ~ (v1_relat_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v2_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.59/0.82      inference('sup+', [status(thm)], ['60', '61'])).
% 0.59/0.82  thf('63', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         (~ (v1_relat_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v2_funct_1 @ X0)
% 0.59/0.82          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ~ (v2_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_relat_1 @ X0)
% 0.59/0.82          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.59/0.82              = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.59/0.82      inference('sup-', [status(thm)], ['59', '62'])).
% 0.59/0.82  thf('64', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         (((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.59/0.82            = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 0.59/0.82          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ~ (v2_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_relat_1 @ X0))),
% 0.59/0.82      inference('simplify', [status(thm)], ['63'])).
% 0.59/0.82  thf('65', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         (~ (v1_relat_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v2_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_relat_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v2_funct_1 @ X0)
% 0.59/0.82          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.59/0.82              = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.59/0.82      inference('sup-', [status(thm)], ['58', '64'])).
% 0.59/0.82  thf('66', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         (((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.59/0.82            = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 0.59/0.82          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ~ (v2_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_relat_1 @ X0))),
% 0.59/0.82      inference('simplify', [status(thm)], ['65'])).
% 0.59/0.82  thf('67', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         (~ (v1_relat_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v2_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_relat_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v2_funct_1 @ X0)
% 0.59/0.82          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.59/0.82              = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.59/0.82      inference('sup-', [status(thm)], ['57', '66'])).
% 0.59/0.82  thf('68', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         (((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.59/0.82            = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 0.59/0.82          | ~ (v2_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_relat_1 @ X0))),
% 0.59/0.82      inference('simplify', [status(thm)], ['67'])).
% 0.59/0.82  thf('69', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         (((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.59/0.82            = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))
% 0.59/0.82          | ~ (v1_relat_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v2_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.59/0.82      inference('sup+', [status(thm)], ['56', '68'])).
% 0.59/0.82  thf('70', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         (~ (v1_relat_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v2_funct_1 @ X0)
% 0.59/0.82          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ~ (v2_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_relat_1 @ X0)
% 0.59/0.82          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.59/0.82              = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))))),
% 0.59/0.82      inference('sup-', [status(thm)], ['55', '69'])).
% 0.59/0.82  thf('71', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         (((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.59/0.82            = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))
% 0.59/0.82          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ~ (v2_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_relat_1 @ X0))),
% 0.59/0.82      inference('simplify', [status(thm)], ['70'])).
% 0.59/0.82  thf('72', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         (~ (v1_relat_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v2_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_relat_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v2_funct_1 @ X0)
% 0.59/0.82          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.59/0.82              = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))))),
% 0.59/0.82      inference('sup-', [status(thm)], ['54', '71'])).
% 0.59/0.82  thf('73', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         (((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.59/0.82            = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))
% 0.59/0.82          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ~ (v2_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_relat_1 @ X0))),
% 0.59/0.82      inference('simplify', [status(thm)], ['72'])).
% 0.59/0.82  thf('74', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         (~ (v1_relat_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v2_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_relat_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v2_funct_1 @ X0)
% 0.59/0.82          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.59/0.82              = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))))),
% 0.59/0.82      inference('sup-', [status(thm)], ['53', '73'])).
% 0.59/0.82  thf('75', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         (((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.59/0.82            = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))
% 0.59/0.82          | ~ (v2_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_relat_1 @ X0))),
% 0.59/0.82      inference('simplify', [status(thm)], ['74'])).
% 0.59/0.82  thf('76', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         (((k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.59/0.82            = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))
% 0.59/0.82          | ~ (v1_relat_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v2_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_relat_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v2_funct_1 @ X0))),
% 0.59/0.82      inference('sup+', [status(thm)], ['52', '75'])).
% 0.59/0.82  thf('77', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         (~ (v2_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_relat_1 @ X0)
% 0.59/0.82          | ((k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.59/0.82              = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))))),
% 0.59/0.82      inference('simplify', [status(thm)], ['76'])).
% 0.59/0.82  thf('78', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         ((v1_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ~ (v2_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_relat_1 @ X0))),
% 0.59/0.82      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.59/0.82  thf('79', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ~ (v2_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_relat_1 @ X0))),
% 0.59/0.82      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.59/0.82  thf(t64_funct_1, conjecture,
% 0.59/0.82    (![A:$i]:
% 0.59/0.82     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.59/0.82       ( ![B:$i]:
% 0.59/0.82         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.59/0.82           ( ( ( v2_funct_1 @ A ) & 
% 0.59/0.82               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 0.59/0.82               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 0.59/0.82             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.59/0.82  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.82    (~( ![A:$i]:
% 0.59/0.82        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.59/0.82          ( ![B:$i]:
% 0.59/0.82            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.59/0.82              ( ( ( v2_funct_1 @ A ) & 
% 0.59/0.82                  ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 0.59/0.82                  ( ( k5_relat_1 @ B @ A ) =
% 0.59/0.82                    ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 0.59/0.82                ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ) )),
% 0.59/0.82    inference('cnf.neg', [status(esa)], [t64_funct_1])).
% 0.59/0.82  thf('80', plain,
% 0.59/0.82      (((k5_relat_1 @ sk_B @ sk_A) = (k6_relat_1 @ (k2_relat_1 @ sk_A)))),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('81', plain,
% 0.59/0.82      (![X6 : $i]:
% 0.59/0.82         (~ (v2_funct_1 @ X6)
% 0.59/0.82          | ((k5_relat_1 @ (k2_funct_1 @ X6) @ X6)
% 0.59/0.82              = (k6_relat_1 @ (k2_relat_1 @ X6)))
% 0.59/0.82          | ~ (v1_funct_1 @ X6)
% 0.59/0.82          | ~ (v1_relat_1 @ X6))),
% 0.59/0.82      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.59/0.82  thf('82', plain,
% 0.59/0.82      (![X1 : $i, X3 : $i, X4 : $i]:
% 0.59/0.82         (~ (v1_relat_1 @ X3)
% 0.59/0.82          | ~ (v1_funct_1 @ X3)
% 0.59/0.82          | ~ (v1_relat_1 @ X4)
% 0.59/0.82          | ~ (v1_funct_1 @ X4)
% 0.59/0.82          | ((X4) = (X3))
% 0.59/0.82          | ((k5_relat_1 @ X1 @ X4) != (k6_relat_1 @ (k2_relat_1 @ X3)))
% 0.59/0.82          | ((k5_relat_1 @ X3 @ X1) != (k6_relat_1 @ (k1_relat_1 @ X4)))
% 0.59/0.82          | ~ (v1_funct_1 @ X1)
% 0.59/0.82          | ~ (v1_relat_1 @ X1))),
% 0.59/0.82      inference('simplify', [status(thm)], ['23'])).
% 0.59/0.82  thf('83', plain,
% 0.59/0.82      (![X0 : $i, X1 : $i]:
% 0.59/0.82         (((k6_relat_1 @ (k2_relat_1 @ X0)) != (k6_relat_1 @ (k2_relat_1 @ X1)))
% 0.59/0.82          | ~ (v1_relat_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v2_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ((k5_relat_1 @ X1 @ (k2_funct_1 @ X0))
% 0.59/0.82              != (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.59/0.82          | ((X0) = (X1))
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_relat_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X1)
% 0.59/0.82          | ~ (v1_relat_1 @ X1))),
% 0.59/0.82      inference('sup-', [status(thm)], ['81', '82'])).
% 0.59/0.82  thf('84', plain,
% 0.59/0.82      (![X0 : $i, X1 : $i]:
% 0.59/0.82         (~ (v1_relat_1 @ X1)
% 0.59/0.82          | ~ (v1_funct_1 @ X1)
% 0.59/0.82          | ((X0) = (X1))
% 0.59/0.82          | ((k5_relat_1 @ X1 @ (k2_funct_1 @ X0))
% 0.59/0.82              != (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.59/0.82          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ~ (v2_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_relat_1 @ X0)
% 0.59/0.82          | ((k6_relat_1 @ (k2_relat_1 @ X0))
% 0.59/0.82              != (k6_relat_1 @ (k2_relat_1 @ X1))))),
% 0.59/0.82      inference('simplify', [status(thm)], ['83'])).
% 0.59/0.82  thf('85', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         (((k5_relat_1 @ sk_B @ sk_A) != (k6_relat_1 @ (k2_relat_1 @ X0)))
% 0.59/0.82          | ~ (v1_relat_1 @ sk_A)
% 0.59/0.82          | ~ (v1_funct_1 @ sk_A)
% 0.59/0.82          | ~ (v2_funct_1 @ sk_A)
% 0.59/0.82          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))
% 0.59/0.82          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_A))
% 0.59/0.82          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ sk_A))
% 0.59/0.82              != (k6_relat_1 @ (k1_relat_1 @ sk_A)))
% 0.59/0.82          | ((sk_A) = (X0))
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_relat_1 @ X0))),
% 0.59/0.82      inference('sup-', [status(thm)], ['80', '84'])).
% 0.59/0.82  thf('86', plain, ((v1_relat_1 @ sk_A)),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('87', plain, ((v1_funct_1 @ sk_A)),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('88', plain, ((v2_funct_1 @ sk_A)),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('89', plain, (((k2_relat_1 @ sk_B) = (k1_relat_1 @ sk_A))),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('90', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         (((k5_relat_1 @ sk_B @ sk_A) != (k6_relat_1 @ (k2_relat_1 @ X0)))
% 0.59/0.82          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))
% 0.59/0.82          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_A))
% 0.59/0.82          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ sk_A))
% 0.59/0.82              != (k6_relat_1 @ (k2_relat_1 @ sk_B)))
% 0.59/0.82          | ((sk_A) = (X0))
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_relat_1 @ X0))),
% 0.59/0.82      inference('demod', [status(thm)], ['85', '86', '87', '88', '89'])).
% 0.59/0.82  thf('91', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         (~ (v1_relat_1 @ sk_A)
% 0.59/0.82          | ~ (v1_funct_1 @ sk_A)
% 0.59/0.82          | ~ (v2_funct_1 @ sk_A)
% 0.59/0.82          | ~ (v1_relat_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ((sk_A) = (X0))
% 0.59/0.82          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ sk_A))
% 0.59/0.82              != (k6_relat_1 @ (k2_relat_1 @ sk_B)))
% 0.59/0.82          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_A))
% 0.59/0.82          | ((k5_relat_1 @ sk_B @ sk_A) != (k6_relat_1 @ (k2_relat_1 @ X0))))),
% 0.59/0.82      inference('sup-', [status(thm)], ['79', '90'])).
% 0.59/0.82  thf('92', plain, ((v1_relat_1 @ sk_A)),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('93', plain, ((v1_funct_1 @ sk_A)),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('94', plain, ((v2_funct_1 @ sk_A)),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('95', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         (~ (v1_relat_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ((sk_A) = (X0))
% 0.59/0.82          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ sk_A))
% 0.59/0.82              != (k6_relat_1 @ (k2_relat_1 @ sk_B)))
% 0.59/0.82          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_A))
% 0.59/0.82          | ((k5_relat_1 @ sk_B @ sk_A) != (k6_relat_1 @ (k2_relat_1 @ X0))))),
% 0.59/0.82      inference('demod', [status(thm)], ['91', '92', '93', '94'])).
% 0.59/0.82  thf('96', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         (~ (v1_relat_1 @ sk_A)
% 0.59/0.82          | ~ (v1_funct_1 @ sk_A)
% 0.59/0.82          | ~ (v2_funct_1 @ sk_A)
% 0.59/0.82          | ((k5_relat_1 @ sk_B @ sk_A) != (k6_relat_1 @ (k2_relat_1 @ X0)))
% 0.59/0.82          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ sk_A))
% 0.59/0.82              != (k6_relat_1 @ (k2_relat_1 @ sk_B)))
% 0.59/0.82          | ((sk_A) = (X0))
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_relat_1 @ X0))),
% 0.59/0.82      inference('sup-', [status(thm)], ['78', '95'])).
% 0.59/0.82  thf('97', plain, ((v1_relat_1 @ sk_A)),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('98', plain, ((v1_funct_1 @ sk_A)),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('99', plain, ((v2_funct_1 @ sk_A)),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('100', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         (((k5_relat_1 @ sk_B @ sk_A) != (k6_relat_1 @ (k2_relat_1 @ X0)))
% 0.59/0.82          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ sk_A))
% 0.59/0.82              != (k6_relat_1 @ (k2_relat_1 @ sk_B)))
% 0.59/0.82          | ((sk_A) = (X0))
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_relat_1 @ X0))),
% 0.59/0.82      inference('demod', [status(thm)], ['96', '97', '98', '99'])).
% 0.59/0.82  thf('101', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         (((k5_relat_1 @ sk_B @ sk_A)
% 0.59/0.82            != (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 0.59/0.82          | ~ (v1_relat_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v2_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.59/0.82          | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.59/0.82          | ((sk_A) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.59/0.82          | ((k5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.59/0.82              (k2_funct_1 @ sk_A)) != (k6_relat_1 @ (k2_relat_1 @ sk_B))))),
% 0.59/0.82      inference('sup-', [status(thm)], ['77', '100'])).
% 0.59/0.82  thf('102', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         (((k5_relat_1 @ sk_B @ sk_A) != (k6_relat_1 @ (k2_relat_1 @ X0)))
% 0.59/0.82          | ~ (v1_relat_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v2_funct_1 @ X0)
% 0.59/0.82          | ((k5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.59/0.82              (k2_funct_1 @ sk_A)) != (k6_relat_1 @ (k2_relat_1 @ sk_B)))
% 0.59/0.82          | ((sk_A) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.59/0.82          | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.59/0.82          | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.59/0.82          | ~ (v2_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_relat_1 @ X0))),
% 0.59/0.82      inference('sup-', [status(thm)], ['9', '101'])).
% 0.59/0.82  thf('103', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         (~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.59/0.82          | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.59/0.82          | ((sk_A) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.59/0.82          | ((k5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.59/0.82              (k2_funct_1 @ sk_A)) != (k6_relat_1 @ (k2_relat_1 @ sk_B)))
% 0.59/0.82          | ~ (v2_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_relat_1 @ X0)
% 0.59/0.82          | ((k5_relat_1 @ sk_B @ sk_A) != (k6_relat_1 @ (k2_relat_1 @ X0))))),
% 0.59/0.82      inference('simplify', [status(thm)], ['102'])).
% 0.59/0.82  thf('104', plain,
% 0.59/0.82      ((((k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_A)))
% 0.59/0.82          != (k6_relat_1 @ (k2_relat_1 @ sk_B)))
% 0.59/0.82        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))
% 0.59/0.82        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_A))
% 0.59/0.82        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_A))
% 0.59/0.82        | ((k5_relat_1 @ sk_B @ sk_A) != (k6_relat_1 @ (k2_relat_1 @ sk_A)))
% 0.59/0.82        | ~ (v1_relat_1 @ sk_A)
% 0.59/0.82        | ~ (v1_funct_1 @ sk_A)
% 0.59/0.82        | ~ (v2_funct_1 @ sk_A)
% 0.59/0.82        | ((sk_A) = (k2_funct_1 @ (k2_funct_1 @ sk_A)))
% 0.59/0.82        | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_A)))
% 0.59/0.82        | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_A))))),
% 0.59/0.82      inference('sup-', [status(thm)], ['8', '103'])).
% 0.59/0.82  thf('105', plain,
% 0.59/0.82      (((k5_relat_1 @ sk_B @ sk_A) = (k6_relat_1 @ (k2_relat_1 @ sk_A)))),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('106', plain, ((v1_relat_1 @ sk_A)),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('107', plain, ((v1_funct_1 @ sk_A)),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('108', plain, ((v2_funct_1 @ sk_A)),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('109', plain,
% 0.59/0.82      ((((k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_A)))
% 0.59/0.82          != (k6_relat_1 @ (k2_relat_1 @ sk_B)))
% 0.59/0.82        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))
% 0.59/0.82        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_A))
% 0.59/0.82        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_A))
% 0.59/0.82        | ((k5_relat_1 @ sk_B @ sk_A) != (k5_relat_1 @ sk_B @ sk_A))
% 0.59/0.82        | ((sk_A) = (k2_funct_1 @ (k2_funct_1 @ sk_A)))
% 0.59/0.82        | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_A)))
% 0.59/0.82        | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_A))))),
% 0.59/0.82      inference('demod', [status(thm)], ['104', '105', '106', '107', '108'])).
% 0.59/0.82  thf('110', plain,
% 0.59/0.82      ((~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_A)))
% 0.59/0.82        | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_A)))
% 0.59/0.82        | ((sk_A) = (k2_funct_1 @ (k2_funct_1 @ sk_A)))
% 0.59/0.82        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_A))
% 0.59/0.82        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_A))
% 0.59/0.82        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))
% 0.59/0.82        | ((k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_A)))
% 0.59/0.82            != (k6_relat_1 @ (k2_relat_1 @ sk_B))))),
% 0.59/0.82      inference('simplify', [status(thm)], ['109'])).
% 0.59/0.82  thf('111', plain,
% 0.59/0.82      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_A))
% 0.59/0.82        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_A))
% 0.59/0.82        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_A))
% 0.59/0.82        | ((k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_A)))
% 0.59/0.82            != (k6_relat_1 @ (k2_relat_1 @ sk_B)))
% 0.59/0.82        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))
% 0.59/0.82        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_A))
% 0.59/0.82        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_A))
% 0.59/0.82        | ((sk_A) = (k2_funct_1 @ (k2_funct_1 @ sk_A)))
% 0.59/0.82        | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_A))))),
% 0.59/0.82      inference('sup-', [status(thm)], ['7', '110'])).
% 0.59/0.82  thf('112', plain,
% 0.59/0.82      ((~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_A)))
% 0.59/0.82        | ((sk_A) = (k2_funct_1 @ (k2_funct_1 @ sk_A)))
% 0.59/0.82        | ((k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_A)))
% 0.59/0.82            != (k6_relat_1 @ (k2_relat_1 @ sk_B)))
% 0.59/0.82        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_A))
% 0.59/0.82        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_A))
% 0.59/0.82        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A)))),
% 0.59/0.82      inference('simplify', [status(thm)], ['111'])).
% 0.59/0.82  thf('113', plain,
% 0.59/0.82      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_A))
% 0.59/0.82        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_A))
% 0.59/0.82        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_A))
% 0.59/0.82        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))
% 0.59/0.82        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_A))
% 0.59/0.82        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_A))
% 0.59/0.82        | ((k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_A)))
% 0.59/0.82            != (k6_relat_1 @ (k2_relat_1 @ sk_B)))
% 0.59/0.82        | ((sk_A) = (k2_funct_1 @ (k2_funct_1 @ sk_A))))),
% 0.59/0.82      inference('sup-', [status(thm)], ['6', '112'])).
% 0.59/0.82  thf('114', plain,
% 0.59/0.82      ((((sk_A) = (k2_funct_1 @ (k2_funct_1 @ sk_A)))
% 0.59/0.82        | ((k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_A)))
% 0.59/0.82            != (k6_relat_1 @ (k2_relat_1 @ sk_B)))
% 0.59/0.82        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_A))
% 0.59/0.82        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_A))
% 0.59/0.82        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A)))),
% 0.59/0.82      inference('simplify', [status(thm)], ['113'])).
% 0.59/0.82  thf('115', plain,
% 0.59/0.82      ((((k6_relat_1 @ (k1_relat_1 @ sk_A))
% 0.59/0.82          != (k6_relat_1 @ (k2_relat_1 @ sk_B)))
% 0.59/0.82        | ~ (v1_relat_1 @ sk_A)
% 0.59/0.82        | ~ (v1_funct_1 @ sk_A)
% 0.59/0.82        | ~ (v2_funct_1 @ sk_A)
% 0.59/0.82        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))
% 0.59/0.82        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_A))
% 0.59/0.82        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_A))
% 0.59/0.82        | ((sk_A) = (k2_funct_1 @ (k2_funct_1 @ sk_A))))),
% 0.59/0.82      inference('sup-', [status(thm)], ['5', '114'])).
% 0.59/0.82  thf('116', plain, (((k2_relat_1 @ sk_B) = (k1_relat_1 @ sk_A))),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('117', plain, ((v1_relat_1 @ sk_A)),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('118', plain, ((v1_funct_1 @ sk_A)),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('119', plain, ((v2_funct_1 @ sk_A)),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('120', plain,
% 0.59/0.82      ((((k6_relat_1 @ (k2_relat_1 @ sk_B))
% 0.59/0.82          != (k6_relat_1 @ (k2_relat_1 @ sk_B)))
% 0.59/0.82        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))
% 0.59/0.82        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_A))
% 0.59/0.82        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_A))
% 0.59/0.82        | ((sk_A) = (k2_funct_1 @ (k2_funct_1 @ sk_A))))),
% 0.59/0.82      inference('demod', [status(thm)], ['115', '116', '117', '118', '119'])).
% 0.59/0.82  thf('121', plain,
% 0.59/0.82      ((((sk_A) = (k2_funct_1 @ (k2_funct_1 @ sk_A)))
% 0.59/0.82        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_A))
% 0.59/0.82        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_A))
% 0.59/0.82        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A)))),
% 0.59/0.82      inference('simplify', [status(thm)], ['120'])).
% 0.59/0.82  thf('122', plain,
% 0.59/0.82      ((~ (v1_relat_1 @ sk_A)
% 0.59/0.82        | ~ (v1_funct_1 @ sk_A)
% 0.59/0.82        | ~ (v2_funct_1 @ sk_A)
% 0.59/0.82        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))
% 0.59/0.82        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_A))
% 0.59/0.82        | ((sk_A) = (k2_funct_1 @ (k2_funct_1 @ sk_A))))),
% 0.59/0.82      inference('sup-', [status(thm)], ['4', '121'])).
% 0.59/0.82  thf('123', plain, ((v1_relat_1 @ sk_A)),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('124', plain, ((v1_funct_1 @ sk_A)),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('125', plain, ((v2_funct_1 @ sk_A)),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('126', plain,
% 0.59/0.82      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_A))
% 0.59/0.82        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_A))
% 0.59/0.82        | ((sk_A) = (k2_funct_1 @ (k2_funct_1 @ sk_A))))),
% 0.59/0.82      inference('demod', [status(thm)], ['122', '123', '124', '125'])).
% 0.59/0.82  thf('127', plain,
% 0.59/0.82      ((~ (v1_relat_1 @ sk_A)
% 0.59/0.82        | ~ (v1_funct_1 @ sk_A)
% 0.59/0.82        | ~ (v2_funct_1 @ sk_A)
% 0.59/0.82        | ((sk_A) = (k2_funct_1 @ (k2_funct_1 @ sk_A)))
% 0.59/0.82        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_A)))),
% 0.59/0.82      inference('sup-', [status(thm)], ['3', '126'])).
% 0.59/0.82  thf('128', plain, ((v1_relat_1 @ sk_A)),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('129', plain, ((v1_funct_1 @ sk_A)),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('130', plain, ((v2_funct_1 @ sk_A)),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('131', plain,
% 0.59/0.82      ((((sk_A) = (k2_funct_1 @ (k2_funct_1 @ sk_A)))
% 0.59/0.82        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_A)))),
% 0.59/0.82      inference('demod', [status(thm)], ['127', '128', '129', '130'])).
% 0.59/0.82  thf('132', plain,
% 0.59/0.82      ((~ (v1_relat_1 @ sk_A)
% 0.59/0.82        | ~ (v1_funct_1 @ sk_A)
% 0.59/0.82        | ~ (v2_funct_1 @ sk_A)
% 0.59/0.82        | ((sk_A) = (k2_funct_1 @ (k2_funct_1 @ sk_A))))),
% 0.59/0.82      inference('sup-', [status(thm)], ['2', '131'])).
% 0.59/0.82  thf('133', plain, ((v1_relat_1 @ sk_A)),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('134', plain, ((v1_funct_1 @ sk_A)),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('135', plain, ((v2_funct_1 @ sk_A)),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('136', plain, (((sk_A) = (k2_funct_1 @ (k2_funct_1 @ sk_A)))),
% 0.59/0.82      inference('demod', [status(thm)], ['132', '133', '134', '135'])).
% 0.59/0.82  thf('137', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         (~ (v2_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_relat_1 @ X0)
% 0.59/0.82          | ((k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.59/0.82              = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))))),
% 0.59/0.82      inference('simplify', [status(thm)], ['76'])).
% 0.59/0.82  thf('138', plain,
% 0.59/0.82      ((((k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_A)))
% 0.59/0.82          = (k6_relat_1 @ (k2_relat_1 @ sk_A)))
% 0.59/0.82        | ~ (v1_relat_1 @ sk_A)
% 0.59/0.82        | ~ (v1_funct_1 @ sk_A)
% 0.59/0.82        | ~ (v2_funct_1 @ sk_A))),
% 0.59/0.82      inference('sup+', [status(thm)], ['136', '137'])).
% 0.59/0.82  thf('139', plain,
% 0.59/0.82      (((k5_relat_1 @ sk_B @ sk_A) = (k6_relat_1 @ (k2_relat_1 @ sk_A)))),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('140', plain, ((v1_relat_1 @ sk_A)),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('141', plain, ((v1_funct_1 @ sk_A)),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('142', plain, ((v2_funct_1 @ sk_A)),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('143', plain,
% 0.59/0.82      (((k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_A)))
% 0.59/0.82         = (k5_relat_1 @ sk_B @ sk_A))),
% 0.59/0.82      inference('demod', [status(thm)], ['138', '139', '140', '141', '142'])).
% 0.59/0.82  thf('144', plain,
% 0.59/0.82      (![X0 : $i, X1 : $i]:
% 0.59/0.82         (~ (v1_relat_1 @ X1)
% 0.59/0.82          | ~ (v1_funct_1 @ X1)
% 0.59/0.82          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.82          | ((k2_funct_1 @ X0) = (X1))
% 0.59/0.82          | ((k5_relat_1 @ X1 @ X0)
% 0.59/0.82              != (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 0.59/0.82          | ~ (v2_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_relat_1 @ X0)
% 0.59/0.82          | ((k6_relat_1 @ (k1_relat_1 @ X0))
% 0.59/0.82              != (k6_relat_1 @ (k2_relat_1 @ X1))))),
% 0.59/0.82      inference('simplify', [status(thm)], ['25'])).
% 0.59/0.82  thf('145', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         (((k5_relat_1 @ X0 @ sk_A) != (k5_relat_1 @ sk_B @ sk_A))
% 0.59/0.82          | ((k6_relat_1 @ (k1_relat_1 @ sk_A))
% 0.59/0.82              != (k6_relat_1 @ (k2_relat_1 @ X0)))
% 0.59/0.82          | ~ (v1_relat_1 @ sk_A)
% 0.59/0.82          | ~ (v1_funct_1 @ sk_A)
% 0.59/0.82          | ~ (v2_funct_1 @ sk_A)
% 0.59/0.82          | ((k2_funct_1 @ sk_A) = (X0))
% 0.59/0.82          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_A))
% 0.59/0.82          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_relat_1 @ X0))),
% 0.59/0.82      inference('sup-', [status(thm)], ['143', '144'])).
% 0.59/0.82  thf('146', plain, (((k2_relat_1 @ sk_B) = (k1_relat_1 @ sk_A))),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('147', plain, ((v1_relat_1 @ sk_A)),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('148', plain, ((v1_funct_1 @ sk_A)),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('149', plain, ((v2_funct_1 @ sk_A)),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('150', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         (((k5_relat_1 @ X0 @ sk_A) != (k5_relat_1 @ sk_B @ sk_A))
% 0.59/0.82          | ((k6_relat_1 @ (k2_relat_1 @ sk_B))
% 0.59/0.82              != (k6_relat_1 @ (k2_relat_1 @ X0)))
% 0.59/0.82          | ((k2_funct_1 @ sk_A) = (X0))
% 0.59/0.82          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_A))
% 0.59/0.82          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_relat_1 @ X0))),
% 0.59/0.82      inference('demod', [status(thm)], ['145', '146', '147', '148', '149'])).
% 0.59/0.82  thf('151', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         (~ (v1_relat_1 @ sk_A)
% 0.59/0.82          | ~ (v1_funct_1 @ sk_A)
% 0.59/0.82          | ~ (v2_funct_1 @ sk_A)
% 0.59/0.82          | ~ (v1_relat_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))
% 0.59/0.82          | ((k2_funct_1 @ sk_A) = (X0))
% 0.59/0.82          | ((k6_relat_1 @ (k2_relat_1 @ sk_B))
% 0.59/0.82              != (k6_relat_1 @ (k2_relat_1 @ X0)))
% 0.59/0.82          | ((k5_relat_1 @ X0 @ sk_A) != (k5_relat_1 @ sk_B @ sk_A)))),
% 0.59/0.82      inference('sup-', [status(thm)], ['1', '150'])).
% 0.59/0.82  thf('152', plain, ((v1_relat_1 @ sk_A)),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('153', plain, ((v1_funct_1 @ sk_A)),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('154', plain, ((v2_funct_1 @ sk_A)),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('155', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         (~ (v1_relat_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))
% 0.59/0.82          | ((k2_funct_1 @ sk_A) = (X0))
% 0.59/0.82          | ((k6_relat_1 @ (k2_relat_1 @ sk_B))
% 0.59/0.82              != (k6_relat_1 @ (k2_relat_1 @ X0)))
% 0.59/0.82          | ((k5_relat_1 @ X0 @ sk_A) != (k5_relat_1 @ sk_B @ sk_A)))),
% 0.59/0.82      inference('demod', [status(thm)], ['151', '152', '153', '154'])).
% 0.59/0.82  thf('156', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         (~ (v1_relat_1 @ sk_A)
% 0.59/0.82          | ~ (v1_funct_1 @ sk_A)
% 0.59/0.82          | ~ (v2_funct_1 @ sk_A)
% 0.59/0.82          | ((k5_relat_1 @ X0 @ sk_A) != (k5_relat_1 @ sk_B @ sk_A))
% 0.59/0.82          | ((k6_relat_1 @ (k2_relat_1 @ sk_B))
% 0.59/0.82              != (k6_relat_1 @ (k2_relat_1 @ X0)))
% 0.59/0.82          | ((k2_funct_1 @ sk_A) = (X0))
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_relat_1 @ X0))),
% 0.59/0.82      inference('sup-', [status(thm)], ['0', '155'])).
% 0.59/0.82  thf('157', plain, ((v1_relat_1 @ sk_A)),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('158', plain, ((v1_funct_1 @ sk_A)),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('159', plain, ((v2_funct_1 @ sk_A)),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('160', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         (((k5_relat_1 @ X0 @ sk_A) != (k5_relat_1 @ sk_B @ sk_A))
% 0.59/0.82          | ((k6_relat_1 @ (k2_relat_1 @ sk_B))
% 0.59/0.82              != (k6_relat_1 @ (k2_relat_1 @ X0)))
% 0.59/0.82          | ((k2_funct_1 @ sk_A) = (X0))
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_relat_1 @ X0))),
% 0.59/0.82      inference('demod', [status(thm)], ['156', '157', '158', '159'])).
% 0.59/0.82  thf('161', plain,
% 0.59/0.82      ((~ (v1_relat_1 @ sk_B)
% 0.59/0.82        | ~ (v1_funct_1 @ sk_B)
% 0.59/0.82        | ((k2_funct_1 @ sk_A) = (sk_B))
% 0.59/0.82        | ((k6_relat_1 @ (k2_relat_1 @ sk_B))
% 0.59/0.82            != (k6_relat_1 @ (k2_relat_1 @ sk_B))))),
% 0.59/0.82      inference('eq_res', [status(thm)], ['160'])).
% 0.59/0.82  thf('162', plain,
% 0.59/0.82      ((((k2_funct_1 @ sk_A) = (sk_B))
% 0.59/0.82        | ~ (v1_funct_1 @ sk_B)
% 0.59/0.82        | ~ (v1_relat_1 @ sk_B))),
% 0.59/0.82      inference('simplify', [status(thm)], ['161'])).
% 0.59/0.82  thf('163', plain, ((v1_funct_1 @ sk_B)),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('164', plain, ((v1_relat_1 @ sk_B)),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('165', plain, (((k2_funct_1 @ sk_A) = (sk_B))),
% 0.59/0.82      inference('demod', [status(thm)], ['162', '163', '164'])).
% 0.59/0.82  thf('166', plain, (((sk_B) != (k2_funct_1 @ sk_A))),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('167', plain, ($false),
% 0.59/0.82      inference('simplify_reflect-', [status(thm)], ['165', '166'])).
% 0.59/0.82  
% 0.59/0.82  % SZS output end Refutation
% 0.59/0.82  
% 0.59/0.83  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
