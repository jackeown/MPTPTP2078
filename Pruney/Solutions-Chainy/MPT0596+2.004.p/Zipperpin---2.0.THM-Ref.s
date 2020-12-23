%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tIUHX9e0yT

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:38 EST 2020

% Result     : Theorem 0.60s
% Output     : Refutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 166 expanded)
%              Number of leaves         :   21 (  56 expanded)
%              Depth                    :   20
%              Number of atoms          :  754 (1779 expanded)
%              Number of equality atoms :   50 ( 102 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('0',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k7_relat_1 @ X17 @ X16 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X16 ) @ X17 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('1',plain,(
    ! [X11: $i] :
      ( ( ( k5_relat_1 @ X11 @ ( k6_relat_1 @ ( k2_relat_1 @ X11 ) ) )
        = X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X9 @ X8 ) @ X10 )
        = ( k5_relat_1 @ X9 @ ( k5_relat_1 @ X8 @ X10 ) ) )
      | ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('4',plain,(
    ! [X2: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ X0 @ ( k7_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ X0 @ ( k7_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k7_relat_1 @ X17 @ X16 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X16 ) @ X17 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X2: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('16',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X12 @ X13 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X12 ) @ X13 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf(t200_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ ( k7_relat_1 @ C @ A ) ) )
           => ( ( k5_relat_1 @ B @ ( k7_relat_1 @ C @ A ) )
              = ( k5_relat_1 @ B @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ! [C: $i] :
            ( ( v1_relat_1 @ C )
           => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ ( k7_relat_1 @ C @ A ) ) )
             => ( ( k5_relat_1 @ B @ ( k7_relat_1 @ C @ A ) )
                = ( k5_relat_1 @ B @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t200_relat_1])).

thf('18',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_B ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('19',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X14 @ ( k1_relat_1 @ X15 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X15 @ X14 ) )
        = X14 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('20',plain,
    ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) )
    | ( ( k1_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) )
      = ( k2_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k1_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) )
      = ( k2_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) )
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( ( k3_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) ) @ ( k2_relat_1 @ sk_B ) )
      = ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference('sup+',[status(thm)],['16','23'])).

thf('25',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k3_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) ) @ ( k2_relat_1 @ sk_B ) )
      = ( k2_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( k3_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) ) @ ( k2_relat_1 @ sk_B ) )
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['25','26'])).

thf(t192_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ) )).

thf('28',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k7_relat_1 @ X6 @ X7 )
        = ( k7_relat_1 @ X6 @ ( k3_xboole_0 @ ( k1_relat_1 @ X6 ) @ X7 ) ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t192_relat_1])).

thf(t100_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('29',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X3 @ X4 ) @ X5 )
        = ( k7_relat_1 @ X3 @ ( k3_xboole_0 @ X4 @ X5 ) ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 )
        = ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) ) @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 )
        = ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) ) @ X0 ) ) ) ) ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( ( k7_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ ( k2_relat_1 @ sk_B ) )
      = ( k7_relat_1 @ sk_C @ ( k3_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_B ) ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['27','32'])).

thf('34',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X3 @ X4 ) @ X5 )
        = ( k7_relat_1 @ X3 @ ( k3_xboole_0 @ X4 @ X5 ) ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('35',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) )
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('36',plain,
    ( ( ( k1_relat_1 @ ( k7_relat_1 @ sk_C @ ( k3_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_B ) ) ) )
      = ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_C @ ( k3_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_B ) ) ) )
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X12 @ X13 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X12 ) @ X13 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('40',plain,
    ( ( ( k2_relat_1 @ sk_B )
      = ( k3_xboole_0 @ ( k1_relat_1 @ sk_C ) @ ( k3_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_B ) ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( k2_relat_1 @ sk_B )
    = ( k3_xboole_0 @ ( k1_relat_1 @ sk_C ) @ ( k3_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k7_relat_1 @ X6 @ X7 )
        = ( k7_relat_1 @ X6 @ ( k3_xboole_0 @ ( k1_relat_1 @ X6 ) @ X7 ) ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t192_relat_1])).

thf('44',plain,
    ( ( ( k7_relat_1 @ sk_C @ ( k3_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_B ) ) )
      = ( k7_relat_1 @ sk_C @ ( k2_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( k7_relat_1 @ sk_C @ ( k3_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_B ) ) )
    = ( k7_relat_1 @ sk_C @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( k7_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ ( k2_relat_1 @ sk_B ) )
    = ( k7_relat_1 @ sk_C @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['33','46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ X0 @ ( k7_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('50',plain,
    ( ( ( k5_relat_1 @ sk_B @ ( k7_relat_1 @ sk_C @ sk_A ) )
      = ( k5_relat_1 @ sk_B @ ( k7_relat_1 @ sk_C @ ( k2_relat_1 @ sk_B ) ) ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( ( k5_relat_1 @ sk_B @ ( k7_relat_1 @ sk_C @ sk_A ) )
      = ( k5_relat_1 @ sk_B @ ( k7_relat_1 @ sk_C @ ( k2_relat_1 @ sk_B ) ) ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_B @ ( k7_relat_1 @ sk_C @ sk_A ) )
      = ( k5_relat_1 @ sk_B @ ( k7_relat_1 @ sk_C @ ( k2_relat_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['14','52'])).

thf('54',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( k5_relat_1 @ sk_B @ ( k7_relat_1 @ sk_C @ sk_A ) )
    = ( k5_relat_1 @ sk_B @ ( k7_relat_1 @ sk_C @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( ( k5_relat_1 @ sk_B @ ( k7_relat_1 @ sk_C @ sk_A ) )
      = ( k5_relat_1 @ sk_B @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['8','55'])).

thf('57',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( k5_relat_1 @ sk_B @ ( k7_relat_1 @ sk_C @ sk_A ) )
    = ( k5_relat_1 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,(
    ( k5_relat_1 @ sk_B @ ( k7_relat_1 @ sk_C @ sk_A ) )
 != ( k5_relat_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['59','60'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tIUHX9e0yT
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:54:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.60/0.83  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.60/0.83  % Solved by: fo/fo7.sh
% 0.60/0.83  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.60/0.83  % done 404 iterations in 0.386s
% 0.60/0.83  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.60/0.83  % SZS output start Refutation
% 0.60/0.83  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.60/0.83  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.60/0.83  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.60/0.83  thf(sk_C_type, type, sk_C: $i).
% 0.60/0.83  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.60/0.83  thf(sk_A_type, type, sk_A: $i).
% 0.60/0.83  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.60/0.83  thf(sk_B_type, type, sk_B: $i).
% 0.60/0.83  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.60/0.83  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.60/0.83  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.60/0.83  thf(t94_relat_1, axiom,
% 0.60/0.83    (![A:$i,B:$i]:
% 0.60/0.83     ( ( v1_relat_1 @ B ) =>
% 0.60/0.83       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.60/0.83  thf('0', plain,
% 0.60/0.83      (![X16 : $i, X17 : $i]:
% 0.60/0.83         (((k7_relat_1 @ X17 @ X16) = (k5_relat_1 @ (k6_relat_1 @ X16) @ X17))
% 0.60/0.83          | ~ (v1_relat_1 @ X17))),
% 0.60/0.83      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.60/0.83  thf(t80_relat_1, axiom,
% 0.60/0.83    (![A:$i]:
% 0.60/0.83     ( ( v1_relat_1 @ A ) =>
% 0.60/0.83       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 0.60/0.83  thf('1', plain,
% 0.60/0.83      (![X11 : $i]:
% 0.60/0.83         (((k5_relat_1 @ X11 @ (k6_relat_1 @ (k2_relat_1 @ X11))) = (X11))
% 0.60/0.83          | ~ (v1_relat_1 @ X11))),
% 0.60/0.83      inference('cnf', [status(esa)], [t80_relat_1])).
% 0.60/0.83  thf(t55_relat_1, axiom,
% 0.60/0.83    (![A:$i]:
% 0.60/0.83     ( ( v1_relat_1 @ A ) =>
% 0.60/0.83       ( ![B:$i]:
% 0.60/0.83         ( ( v1_relat_1 @ B ) =>
% 0.60/0.83           ( ![C:$i]:
% 0.60/0.83             ( ( v1_relat_1 @ C ) =>
% 0.60/0.83               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 0.60/0.83                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 0.60/0.83  thf('2', plain,
% 0.60/0.83      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.60/0.83         (~ (v1_relat_1 @ X8)
% 0.60/0.83          | ((k5_relat_1 @ (k5_relat_1 @ X9 @ X8) @ X10)
% 0.60/0.83              = (k5_relat_1 @ X9 @ (k5_relat_1 @ X8 @ X10)))
% 0.60/0.83          | ~ (v1_relat_1 @ X10)
% 0.60/0.83          | ~ (v1_relat_1 @ X9))),
% 0.60/0.83      inference('cnf', [status(esa)], [t55_relat_1])).
% 0.60/0.83  thf('3', plain,
% 0.60/0.83      (![X0 : $i, X1 : $i]:
% 0.60/0.83         (((k5_relat_1 @ X0 @ X1)
% 0.60/0.83            = (k5_relat_1 @ X0 @ 
% 0.60/0.83               (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ X1)))
% 0.60/0.83          | ~ (v1_relat_1 @ X0)
% 0.60/0.83          | ~ (v1_relat_1 @ X0)
% 0.60/0.83          | ~ (v1_relat_1 @ X1)
% 0.60/0.83          | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0))))),
% 0.60/0.83      inference('sup+', [status(thm)], ['1', '2'])).
% 0.60/0.83  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.60/0.83  thf('4', plain, (![X2 : $i]: (v1_relat_1 @ (k6_relat_1 @ X2))),
% 0.60/0.83      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.60/0.83  thf('5', plain,
% 0.60/0.83      (![X0 : $i, X1 : $i]:
% 0.60/0.83         (((k5_relat_1 @ X0 @ X1)
% 0.60/0.83            = (k5_relat_1 @ X0 @ 
% 0.60/0.83               (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ X1)))
% 0.60/0.83          | ~ (v1_relat_1 @ X0)
% 0.60/0.83          | ~ (v1_relat_1 @ X0)
% 0.60/0.83          | ~ (v1_relat_1 @ X1))),
% 0.60/0.83      inference('demod', [status(thm)], ['3', '4'])).
% 0.60/0.83  thf('6', plain,
% 0.60/0.83      (![X0 : $i, X1 : $i]:
% 0.60/0.83         (~ (v1_relat_1 @ X1)
% 0.60/0.83          | ~ (v1_relat_1 @ X0)
% 0.60/0.83          | ((k5_relat_1 @ X0 @ X1)
% 0.60/0.83              = (k5_relat_1 @ X0 @ 
% 0.60/0.83                 (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ X1))))),
% 0.60/0.83      inference('simplify', [status(thm)], ['5'])).
% 0.60/0.83  thf('7', plain,
% 0.60/0.83      (![X0 : $i, X1 : $i]:
% 0.60/0.83         (((k5_relat_1 @ X0 @ X1)
% 0.60/0.83            = (k5_relat_1 @ X0 @ (k7_relat_1 @ X1 @ (k2_relat_1 @ X0))))
% 0.60/0.83          | ~ (v1_relat_1 @ X1)
% 0.60/0.83          | ~ (v1_relat_1 @ X0)
% 0.60/0.83          | ~ (v1_relat_1 @ X1))),
% 0.60/0.83      inference('sup+', [status(thm)], ['0', '6'])).
% 0.60/0.83  thf('8', plain,
% 0.60/0.83      (![X0 : $i, X1 : $i]:
% 0.60/0.83         (~ (v1_relat_1 @ X0)
% 0.60/0.83          | ~ (v1_relat_1 @ X1)
% 0.60/0.83          | ((k5_relat_1 @ X0 @ X1)
% 0.60/0.83              = (k5_relat_1 @ X0 @ (k7_relat_1 @ X1 @ (k2_relat_1 @ X0)))))),
% 0.60/0.83      inference('simplify', [status(thm)], ['7'])).
% 0.60/0.83  thf('9', plain,
% 0.60/0.83      (![X16 : $i, X17 : $i]:
% 0.60/0.83         (((k7_relat_1 @ X17 @ X16) = (k5_relat_1 @ (k6_relat_1 @ X16) @ X17))
% 0.60/0.83          | ~ (v1_relat_1 @ X17))),
% 0.60/0.83      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.60/0.83  thf(dt_k5_relat_1, axiom,
% 0.60/0.83    (![A:$i,B:$i]:
% 0.60/0.83     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.60/0.83       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.60/0.83  thf('10', plain,
% 0.60/0.83      (![X0 : $i, X1 : $i]:
% 0.60/0.83         (~ (v1_relat_1 @ X0)
% 0.60/0.83          | ~ (v1_relat_1 @ X1)
% 0.60/0.83          | (v1_relat_1 @ (k5_relat_1 @ X0 @ X1)))),
% 0.60/0.83      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.60/0.83  thf('11', plain,
% 0.60/0.83      (![X0 : $i, X1 : $i]:
% 0.60/0.83         ((v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.60/0.83          | ~ (v1_relat_1 @ X1)
% 0.60/0.83          | ~ (v1_relat_1 @ X1)
% 0.60/0.83          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.60/0.83      inference('sup+', [status(thm)], ['9', '10'])).
% 0.60/0.83  thf('12', plain, (![X2 : $i]: (v1_relat_1 @ (k6_relat_1 @ X2))),
% 0.60/0.83      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.60/0.83  thf('13', plain,
% 0.60/0.83      (![X0 : $i, X1 : $i]:
% 0.60/0.83         ((v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.60/0.83          | ~ (v1_relat_1 @ X1)
% 0.60/0.83          | ~ (v1_relat_1 @ X1))),
% 0.60/0.83      inference('demod', [status(thm)], ['11', '12'])).
% 0.60/0.83  thf('14', plain,
% 0.60/0.83      (![X0 : $i, X1 : $i]:
% 0.60/0.83         (~ (v1_relat_1 @ X1) | (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.60/0.83      inference('simplify', [status(thm)], ['13'])).
% 0.60/0.83  thf('15', plain,
% 0.60/0.83      (![X0 : $i, X1 : $i]:
% 0.60/0.83         (~ (v1_relat_1 @ X1) | (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.60/0.83      inference('simplify', [status(thm)], ['13'])).
% 0.60/0.83  thf(t90_relat_1, axiom,
% 0.60/0.83    (![A:$i,B:$i]:
% 0.60/0.83     ( ( v1_relat_1 @ B ) =>
% 0.60/0.83       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 0.60/0.83         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.60/0.83  thf('16', plain,
% 0.60/0.83      (![X12 : $i, X13 : $i]:
% 0.60/0.83         (((k1_relat_1 @ (k7_relat_1 @ X12 @ X13))
% 0.60/0.83            = (k3_xboole_0 @ (k1_relat_1 @ X12) @ X13))
% 0.60/0.83          | ~ (v1_relat_1 @ X12))),
% 0.60/0.83      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.60/0.83  thf('17', plain,
% 0.60/0.83      (![X0 : $i, X1 : $i]:
% 0.60/0.83         (~ (v1_relat_1 @ X1) | (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.60/0.83      inference('simplify', [status(thm)], ['13'])).
% 0.60/0.83  thf(t200_relat_1, conjecture,
% 0.60/0.83    (![A:$i,B:$i]:
% 0.60/0.83     ( ( v1_relat_1 @ B ) =>
% 0.60/0.83       ( ![C:$i]:
% 0.60/0.83         ( ( v1_relat_1 @ C ) =>
% 0.60/0.83           ( ( r1_tarski @
% 0.60/0.83               ( k2_relat_1 @ B ) @ ( k1_relat_1 @ ( k7_relat_1 @ C @ A ) ) ) =>
% 0.60/0.83             ( ( k5_relat_1 @ B @ ( k7_relat_1 @ C @ A ) ) =
% 0.60/0.83               ( k5_relat_1 @ B @ C ) ) ) ) ) ))).
% 0.60/0.83  thf(zf_stmt_0, negated_conjecture,
% 0.60/0.83    (~( ![A:$i,B:$i]:
% 0.60/0.83        ( ( v1_relat_1 @ B ) =>
% 0.60/0.83          ( ![C:$i]:
% 0.60/0.83            ( ( v1_relat_1 @ C ) =>
% 0.60/0.83              ( ( r1_tarski @
% 0.60/0.83                  ( k2_relat_1 @ B ) @ ( k1_relat_1 @ ( k7_relat_1 @ C @ A ) ) ) =>
% 0.60/0.83                ( ( k5_relat_1 @ B @ ( k7_relat_1 @ C @ A ) ) =
% 0.60/0.83                  ( k5_relat_1 @ B @ C ) ) ) ) ) ) )),
% 0.60/0.83    inference('cnf.neg', [status(esa)], [t200_relat_1])).
% 0.60/0.83  thf('18', plain,
% 0.60/0.83      ((r1_tarski @ (k2_relat_1 @ sk_B) @ 
% 0.60/0.83        (k1_relat_1 @ (k7_relat_1 @ sk_C @ sk_A)))),
% 0.60/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.83  thf(t91_relat_1, axiom,
% 0.60/0.83    (![A:$i,B:$i]:
% 0.60/0.83     ( ( v1_relat_1 @ B ) =>
% 0.60/0.83       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.60/0.83         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.60/0.83  thf('19', plain,
% 0.60/0.83      (![X14 : $i, X15 : $i]:
% 0.60/0.83         (~ (r1_tarski @ X14 @ (k1_relat_1 @ X15))
% 0.60/0.83          | ((k1_relat_1 @ (k7_relat_1 @ X15 @ X14)) = (X14))
% 0.60/0.83          | ~ (v1_relat_1 @ X15))),
% 0.60/0.83      inference('cnf', [status(esa)], [t91_relat_1])).
% 0.60/0.83  thf('20', plain,
% 0.60/0.83      ((~ (v1_relat_1 @ (k7_relat_1 @ sk_C @ sk_A))
% 0.60/0.83        | ((k1_relat_1 @ 
% 0.60/0.83            (k7_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ (k2_relat_1 @ sk_B)))
% 0.60/0.83            = (k2_relat_1 @ sk_B)))),
% 0.60/0.83      inference('sup-', [status(thm)], ['18', '19'])).
% 0.60/0.83  thf('21', plain,
% 0.60/0.83      ((~ (v1_relat_1 @ sk_C)
% 0.60/0.83        | ((k1_relat_1 @ 
% 0.60/0.83            (k7_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ (k2_relat_1 @ sk_B)))
% 0.60/0.83            = (k2_relat_1 @ sk_B)))),
% 0.60/0.83      inference('sup-', [status(thm)], ['17', '20'])).
% 0.60/0.83  thf('22', plain, ((v1_relat_1 @ sk_C)),
% 0.60/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.83  thf('23', plain,
% 0.60/0.83      (((k1_relat_1 @ 
% 0.60/0.83         (k7_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ (k2_relat_1 @ sk_B)))
% 0.60/0.83         = (k2_relat_1 @ sk_B))),
% 0.60/0.83      inference('demod', [status(thm)], ['21', '22'])).
% 0.60/0.83  thf('24', plain,
% 0.60/0.83      ((((k3_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ sk_C @ sk_A)) @ 
% 0.60/0.83          (k2_relat_1 @ sk_B)) = (k2_relat_1 @ sk_B))
% 0.60/0.83        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_C @ sk_A)))),
% 0.60/0.83      inference('sup+', [status(thm)], ['16', '23'])).
% 0.60/0.83  thf('25', plain,
% 0.60/0.83      ((~ (v1_relat_1 @ sk_C)
% 0.60/0.83        | ((k3_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ sk_C @ sk_A)) @ 
% 0.60/0.83            (k2_relat_1 @ sk_B)) = (k2_relat_1 @ sk_B)))),
% 0.60/0.83      inference('sup-', [status(thm)], ['15', '24'])).
% 0.60/0.83  thf('26', plain, ((v1_relat_1 @ sk_C)),
% 0.60/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.83  thf('27', plain,
% 0.60/0.83      (((k3_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ sk_C @ sk_A)) @ 
% 0.60/0.83         (k2_relat_1 @ sk_B)) = (k2_relat_1 @ sk_B))),
% 0.60/0.83      inference('demod', [status(thm)], ['25', '26'])).
% 0.60/0.83  thf(t192_relat_1, axiom,
% 0.60/0.83    (![A:$i,B:$i]:
% 0.60/0.83     ( ( v1_relat_1 @ B ) =>
% 0.60/0.83       ( ( k7_relat_1 @ B @ A ) =
% 0.60/0.83         ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ))).
% 0.60/0.83  thf('28', plain,
% 0.60/0.83      (![X6 : $i, X7 : $i]:
% 0.60/0.83         (((k7_relat_1 @ X6 @ X7)
% 0.60/0.83            = (k7_relat_1 @ X6 @ (k3_xboole_0 @ (k1_relat_1 @ X6) @ X7)))
% 0.60/0.83          | ~ (v1_relat_1 @ X6))),
% 0.60/0.83      inference('cnf', [status(esa)], [t192_relat_1])).
% 0.60/0.83  thf(t100_relat_1, axiom,
% 0.60/0.83    (![A:$i,B:$i,C:$i]:
% 0.60/0.83     ( ( v1_relat_1 @ C ) =>
% 0.60/0.83       ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.60/0.83         ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 0.60/0.83  thf('29', plain,
% 0.60/0.83      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.60/0.83         (((k7_relat_1 @ (k7_relat_1 @ X3 @ X4) @ X5)
% 0.60/0.83            = (k7_relat_1 @ X3 @ (k3_xboole_0 @ X4 @ X5)))
% 0.60/0.83          | ~ (v1_relat_1 @ X3))),
% 0.60/0.83      inference('cnf', [status(esa)], [t100_relat_1])).
% 0.60/0.83  thf('30', plain,
% 0.60/0.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.60/0.83         (((k7_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0)
% 0.60/0.83            = (k7_relat_1 @ X2 @ 
% 0.60/0.83               (k3_xboole_0 @ X1 @ 
% 0.60/0.83                (k3_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ X2 @ X1)) @ X0))))
% 0.60/0.83          | ~ (v1_relat_1 @ (k7_relat_1 @ X2 @ X1))
% 0.60/0.83          | ~ (v1_relat_1 @ X2))),
% 0.60/0.83      inference('sup+', [status(thm)], ['28', '29'])).
% 0.60/0.83  thf('31', plain,
% 0.60/0.83      (![X0 : $i, X1 : $i]:
% 0.60/0.83         (~ (v1_relat_1 @ X1) | (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.60/0.83      inference('simplify', [status(thm)], ['13'])).
% 0.60/0.83  thf('32', plain,
% 0.60/0.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.60/0.83         (~ (v1_relat_1 @ X2)
% 0.60/0.83          | ((k7_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0)
% 0.60/0.83              = (k7_relat_1 @ X2 @ 
% 0.60/0.83                 (k3_xboole_0 @ X1 @ 
% 0.60/0.83                  (k3_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ X2 @ X1)) @ X0)))))),
% 0.60/0.83      inference('clc', [status(thm)], ['30', '31'])).
% 0.60/0.83  thf('33', plain,
% 0.60/0.83      ((((k7_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ (k2_relat_1 @ sk_B))
% 0.60/0.83          = (k7_relat_1 @ sk_C @ (k3_xboole_0 @ sk_A @ (k2_relat_1 @ sk_B))))
% 0.60/0.83        | ~ (v1_relat_1 @ sk_C))),
% 0.60/0.83      inference('sup+', [status(thm)], ['27', '32'])).
% 0.60/0.83  thf('34', plain,
% 0.60/0.83      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.60/0.83         (((k7_relat_1 @ (k7_relat_1 @ X3 @ X4) @ X5)
% 0.60/0.83            = (k7_relat_1 @ X3 @ (k3_xboole_0 @ X4 @ X5)))
% 0.60/0.83          | ~ (v1_relat_1 @ X3))),
% 0.60/0.83      inference('cnf', [status(esa)], [t100_relat_1])).
% 0.60/0.83  thf('35', plain,
% 0.60/0.83      (((k1_relat_1 @ 
% 0.60/0.83         (k7_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ (k2_relat_1 @ sk_B)))
% 0.60/0.83         = (k2_relat_1 @ sk_B))),
% 0.60/0.83      inference('demod', [status(thm)], ['21', '22'])).
% 0.60/0.83  thf('36', plain,
% 0.60/0.83      ((((k1_relat_1 @ 
% 0.60/0.83          (k7_relat_1 @ sk_C @ (k3_xboole_0 @ sk_A @ (k2_relat_1 @ sk_B))))
% 0.60/0.83          = (k2_relat_1 @ sk_B))
% 0.60/0.83        | ~ (v1_relat_1 @ sk_C))),
% 0.60/0.83      inference('sup+', [status(thm)], ['34', '35'])).
% 0.60/0.83  thf('37', plain, ((v1_relat_1 @ sk_C)),
% 0.60/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.83  thf('38', plain,
% 0.60/0.83      (((k1_relat_1 @ 
% 0.60/0.83         (k7_relat_1 @ sk_C @ (k3_xboole_0 @ sk_A @ (k2_relat_1 @ sk_B))))
% 0.60/0.83         = (k2_relat_1 @ sk_B))),
% 0.60/0.83      inference('demod', [status(thm)], ['36', '37'])).
% 0.60/0.83  thf('39', plain,
% 0.60/0.83      (![X12 : $i, X13 : $i]:
% 0.60/0.83         (((k1_relat_1 @ (k7_relat_1 @ X12 @ X13))
% 0.60/0.83            = (k3_xboole_0 @ (k1_relat_1 @ X12) @ X13))
% 0.60/0.83          | ~ (v1_relat_1 @ X12))),
% 0.60/0.83      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.60/0.83  thf('40', plain,
% 0.60/0.83      ((((k2_relat_1 @ sk_B)
% 0.60/0.83          = (k3_xboole_0 @ (k1_relat_1 @ sk_C) @ 
% 0.60/0.83             (k3_xboole_0 @ sk_A @ (k2_relat_1 @ sk_B))))
% 0.60/0.83        | ~ (v1_relat_1 @ sk_C))),
% 0.60/0.83      inference('sup+', [status(thm)], ['38', '39'])).
% 0.60/0.83  thf('41', plain, ((v1_relat_1 @ sk_C)),
% 0.60/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.83  thf('42', plain,
% 0.60/0.83      (((k2_relat_1 @ sk_B)
% 0.60/0.83         = (k3_xboole_0 @ (k1_relat_1 @ sk_C) @ 
% 0.60/0.83            (k3_xboole_0 @ sk_A @ (k2_relat_1 @ sk_B))))),
% 0.60/0.83      inference('demod', [status(thm)], ['40', '41'])).
% 0.60/0.83  thf('43', plain,
% 0.60/0.83      (![X6 : $i, X7 : $i]:
% 0.60/0.83         (((k7_relat_1 @ X6 @ X7)
% 0.60/0.83            = (k7_relat_1 @ X6 @ (k3_xboole_0 @ (k1_relat_1 @ X6) @ X7)))
% 0.60/0.83          | ~ (v1_relat_1 @ X6))),
% 0.60/0.83      inference('cnf', [status(esa)], [t192_relat_1])).
% 0.60/0.83  thf('44', plain,
% 0.60/0.83      ((((k7_relat_1 @ sk_C @ (k3_xboole_0 @ sk_A @ (k2_relat_1 @ sk_B)))
% 0.60/0.83          = (k7_relat_1 @ sk_C @ (k2_relat_1 @ sk_B)))
% 0.60/0.83        | ~ (v1_relat_1 @ sk_C))),
% 0.60/0.83      inference('sup+', [status(thm)], ['42', '43'])).
% 0.60/0.83  thf('45', plain, ((v1_relat_1 @ sk_C)),
% 0.60/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.83  thf('46', plain,
% 0.60/0.83      (((k7_relat_1 @ sk_C @ (k3_xboole_0 @ sk_A @ (k2_relat_1 @ sk_B)))
% 0.60/0.83         = (k7_relat_1 @ sk_C @ (k2_relat_1 @ sk_B)))),
% 0.60/0.83      inference('demod', [status(thm)], ['44', '45'])).
% 0.60/0.83  thf('47', plain, ((v1_relat_1 @ sk_C)),
% 0.60/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.83  thf('48', plain,
% 0.60/0.83      (((k7_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ (k2_relat_1 @ sk_B))
% 0.60/0.83         = (k7_relat_1 @ sk_C @ (k2_relat_1 @ sk_B)))),
% 0.60/0.83      inference('demod', [status(thm)], ['33', '46', '47'])).
% 0.60/0.83  thf('49', plain,
% 0.60/0.83      (![X0 : $i, X1 : $i]:
% 0.60/0.83         (~ (v1_relat_1 @ X0)
% 0.60/0.83          | ~ (v1_relat_1 @ X1)
% 0.60/0.83          | ((k5_relat_1 @ X0 @ X1)
% 0.60/0.83              = (k5_relat_1 @ X0 @ (k7_relat_1 @ X1 @ (k2_relat_1 @ X0)))))),
% 0.60/0.83      inference('simplify', [status(thm)], ['7'])).
% 0.60/0.83  thf('50', plain,
% 0.60/0.83      ((((k5_relat_1 @ sk_B @ (k7_relat_1 @ sk_C @ sk_A))
% 0.60/0.83          = (k5_relat_1 @ sk_B @ (k7_relat_1 @ sk_C @ (k2_relat_1 @ sk_B))))
% 0.60/0.83        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_C @ sk_A))
% 0.60/0.83        | ~ (v1_relat_1 @ sk_B))),
% 0.60/0.83      inference('sup+', [status(thm)], ['48', '49'])).
% 0.60/0.83  thf('51', plain, ((v1_relat_1 @ sk_B)),
% 0.60/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.83  thf('52', plain,
% 0.60/0.83      ((((k5_relat_1 @ sk_B @ (k7_relat_1 @ sk_C @ sk_A))
% 0.60/0.83          = (k5_relat_1 @ sk_B @ (k7_relat_1 @ sk_C @ (k2_relat_1 @ sk_B))))
% 0.60/0.83        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_C @ sk_A)))),
% 0.60/0.83      inference('demod', [status(thm)], ['50', '51'])).
% 0.60/0.83  thf('53', plain,
% 0.60/0.83      ((~ (v1_relat_1 @ sk_C)
% 0.60/0.83        | ((k5_relat_1 @ sk_B @ (k7_relat_1 @ sk_C @ sk_A))
% 0.60/0.83            = (k5_relat_1 @ sk_B @ (k7_relat_1 @ sk_C @ (k2_relat_1 @ sk_B)))))),
% 0.60/0.83      inference('sup-', [status(thm)], ['14', '52'])).
% 0.60/0.83  thf('54', plain, ((v1_relat_1 @ sk_C)),
% 0.60/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.83  thf('55', plain,
% 0.60/0.83      (((k5_relat_1 @ sk_B @ (k7_relat_1 @ sk_C @ sk_A))
% 0.60/0.83         = (k5_relat_1 @ sk_B @ (k7_relat_1 @ sk_C @ (k2_relat_1 @ sk_B))))),
% 0.60/0.83      inference('demod', [status(thm)], ['53', '54'])).
% 0.60/0.83  thf('56', plain,
% 0.60/0.83      ((((k5_relat_1 @ sk_B @ (k7_relat_1 @ sk_C @ sk_A))
% 0.60/0.83          = (k5_relat_1 @ sk_B @ sk_C))
% 0.60/0.83        | ~ (v1_relat_1 @ sk_C)
% 0.60/0.83        | ~ (v1_relat_1 @ sk_B))),
% 0.60/0.83      inference('sup+', [status(thm)], ['8', '55'])).
% 0.60/0.83  thf('57', plain, ((v1_relat_1 @ sk_C)),
% 0.60/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.83  thf('58', plain, ((v1_relat_1 @ sk_B)),
% 0.60/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.83  thf('59', plain,
% 0.60/0.83      (((k5_relat_1 @ sk_B @ (k7_relat_1 @ sk_C @ sk_A))
% 0.60/0.83         = (k5_relat_1 @ sk_B @ sk_C))),
% 0.60/0.83      inference('demod', [status(thm)], ['56', '57', '58'])).
% 0.60/0.83  thf('60', plain,
% 0.60/0.83      (((k5_relat_1 @ sk_B @ (k7_relat_1 @ sk_C @ sk_A))
% 0.60/0.83         != (k5_relat_1 @ sk_B @ sk_C))),
% 0.60/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.83  thf('61', plain, ($false),
% 0.60/0.83      inference('simplify_reflect-', [status(thm)], ['59', '60'])).
% 0.60/0.83  
% 0.60/0.83  % SZS output end Refutation
% 0.60/0.83  
% 0.60/0.84  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
