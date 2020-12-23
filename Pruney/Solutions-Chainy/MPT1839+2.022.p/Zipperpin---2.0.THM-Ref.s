%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0lQiQokftm

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:25 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 248 expanded)
%              Number of leaves         :   19 (  81 expanded)
%              Depth                    :   21
%              Number of atoms          :  682 (1863 expanded)
%              Number of equality atoms :   70 ( 151 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t2_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_zfmisc_1 @ A ) )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ ( k3_xboole_0 @ A @ B ) )
         => ( r1_tarski @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v1_xboole_0 @ A )
          & ( v1_zfmisc_1 @ A ) )
       => ! [B: $i] :
            ( ~ ( v1_xboole_0 @ ( k3_xboole_0 @ A @ B ) )
           => ( r1_tarski @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t2_tex_2])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('1',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_zfmisc_1 @ B ) )
         => ( ( r1_tarski @ A @ B )
           => ( A = B ) ) ) ) )).

thf('2',plain,(
    ! [X26: $i,X27: $i] :
      ( ( v1_xboole_0 @ X26 )
      | ~ ( v1_zfmisc_1 @ X26 )
      | ( X27 = X26 )
      | ~ ( r1_tarski @ X27 @ X26 )
      | ( v1_xboole_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t1_tex_2])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( ( k3_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( v1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( v1_zfmisc_1 @ sk_A )
    | ( ( k3_xboole_0 @ sk_A @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_zfmisc_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( ( k3_xboole_0 @ sk_A @ sk_B )
      = sk_A ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference(clc,[status(thm)],['7','8'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('10',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ ( k4_xboole_0 @ X13 @ X14 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('11',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = sk_A ),
    inference('sup+',[status(thm)],['9','10'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('13',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['12'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('14',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ X6 @ ( k2_xboole_0 @ X8 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('16',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ k1_xboole_0 )
    = ( k3_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['11','19'])).

thf('21',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ ( k4_xboole_0 @ X13 @ X14 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('22',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('23',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ X6 @ ( k2_xboole_0 @ X8 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) @ X0 ) ),
    inference('sup+',[status(thm)],['21','24'])).

thf('26',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ k1_xboole_0 ) @ sk_A ),
    inference('sup+',[status(thm)],['20','25'])).

thf('27',plain,(
    ! [X26: $i,X27: $i] :
      ( ( v1_xboole_0 @ X26 )
      | ~ ( v1_zfmisc_1 @ X26 )
      | ( X27 = X26 )
      | ~ ( r1_tarski @ X27 @ X26 )
      | ( v1_xboole_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t1_tex_2])).

thf('28',plain,
    ( ( v1_xboole_0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ k1_xboole_0 ) )
    | ( ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ k1_xboole_0 )
      = sk_A )
    | ~ ( v1_zfmisc_1 @ sk_A )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_zfmisc_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( v1_xboole_0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ k1_xboole_0 ) )
    | ( ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ k1_xboole_0 )
      = sk_A )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ k1_xboole_0 )
      = sk_A )
    | ( v1_xboole_0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['30','31'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('33',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('34',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_xboole_0 @ X15 )
      | ~ ( v1_xboole_0 @ X16 )
      | ( X15 = X16 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ k1_xboole_0 )
      = sk_A )
    | ( k1_xboole_0
      = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ ( k4_xboole_0 @ X13 @ X14 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) )
      = k1_xboole_0 )
    | ( k1_xboole_0
      = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['36','41'])).

thf('43',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('44',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( k1_xboole_0
      = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference(clc,[status(thm)],['7','8'])).

thf('46',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( k1_xboole_0
      = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ k1_xboole_0 )
      = sk_A )
    | ( k1_xboole_0
      = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('48',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( k1_xboole_0
      = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ k1_xboole_0 ) ) ),
    inference(eq_fact,[status(thm)],['47'])).

thf('49',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['46','48'])).

thf('50',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('51',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ ( k4_xboole_0 @ X13 @ X14 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) @ ( k4_xboole_0 @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['49','58'])).

thf('60',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('61',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['62','65'])).

thf('67',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('70',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ ( k4_xboole_0 @ X13 @ X14 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['62','65'])).

thf('74',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['59','74'])).

thf('76',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k4_xboole_0 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('77',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    $false ),
    inference(demod,[status(thm)],['0','78'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0lQiQokftm
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:09:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.40/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.40/0.58  % Solved by: fo/fo7.sh
% 0.40/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.58  % done 267 iterations in 0.127s
% 0.40/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.40/0.58  % SZS output start Refutation
% 0.40/0.58  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.40/0.58  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.40/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.40/0.58  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.40/0.58  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.40/0.58  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.40/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.58  thf(t2_tex_2, conjecture,
% 0.40/0.58    (![A:$i]:
% 0.40/0.58     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_zfmisc_1 @ A ) ) =>
% 0.40/0.58       ( ![B:$i]:
% 0.40/0.58         ( ( ~( v1_xboole_0 @ ( k3_xboole_0 @ A @ B ) ) ) =>
% 0.40/0.58           ( r1_tarski @ A @ B ) ) ) ))).
% 0.40/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.58    (~( ![A:$i]:
% 0.40/0.58        ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_zfmisc_1 @ A ) ) =>
% 0.40/0.58          ( ![B:$i]:
% 0.40/0.58            ( ( ~( v1_xboole_0 @ ( k3_xboole_0 @ A @ B ) ) ) =>
% 0.40/0.58              ( r1_tarski @ A @ B ) ) ) ) )),
% 0.40/0.58    inference('cnf.neg', [status(esa)], [t2_tex_2])).
% 0.40/0.58  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf(t17_xboole_1, axiom,
% 0.40/0.58    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.40/0.58  thf('1', plain,
% 0.40/0.58      (![X9 : $i, X10 : $i]: (r1_tarski @ (k3_xboole_0 @ X9 @ X10) @ X9)),
% 0.40/0.58      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.40/0.58  thf(t1_tex_2, axiom,
% 0.40/0.58    (![A:$i]:
% 0.40/0.58     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.40/0.58       ( ![B:$i]:
% 0.40/0.58         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.40/0.58           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 0.40/0.58  thf('2', plain,
% 0.40/0.58      (![X26 : $i, X27 : $i]:
% 0.40/0.58         ((v1_xboole_0 @ X26)
% 0.40/0.58          | ~ (v1_zfmisc_1 @ X26)
% 0.40/0.58          | ((X27) = (X26))
% 0.40/0.58          | ~ (r1_tarski @ X27 @ X26)
% 0.40/0.58          | (v1_xboole_0 @ X27))),
% 0.40/0.58      inference('cnf', [status(esa)], [t1_tex_2])).
% 0.40/0.58  thf('3', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         ((v1_xboole_0 @ (k3_xboole_0 @ X0 @ X1))
% 0.40/0.58          | ((k3_xboole_0 @ X0 @ X1) = (X0))
% 0.40/0.58          | ~ (v1_zfmisc_1 @ X0)
% 0.40/0.58          | (v1_xboole_0 @ X0))),
% 0.40/0.58      inference('sup-', [status(thm)], ['1', '2'])).
% 0.40/0.58  thf('4', plain, (~ (v1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('5', plain,
% 0.40/0.58      (((v1_xboole_0 @ sk_A)
% 0.40/0.58        | ~ (v1_zfmisc_1 @ sk_A)
% 0.40/0.58        | ((k3_xboole_0 @ sk_A @ sk_B) = (sk_A)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['3', '4'])).
% 0.40/0.58  thf('6', plain, ((v1_zfmisc_1 @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('7', plain,
% 0.40/0.58      (((v1_xboole_0 @ sk_A) | ((k3_xboole_0 @ sk_A @ sk_B) = (sk_A)))),
% 0.40/0.58      inference('demod', [status(thm)], ['5', '6'])).
% 0.40/0.58  thf('8', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('9', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.40/0.58      inference('clc', [status(thm)], ['7', '8'])).
% 0.40/0.58  thf(t51_xboole_1, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.40/0.58       ( A ) ))).
% 0.40/0.58  thf('10', plain,
% 0.40/0.58      (![X13 : $i, X14 : $i]:
% 0.40/0.58         ((k2_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ (k4_xboole_0 @ X13 @ X14))
% 0.40/0.58           = (X13))),
% 0.40/0.58      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.40/0.58  thf('11', plain,
% 0.40/0.58      (((k2_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B)) = (sk_A))),
% 0.40/0.58      inference('sup+', [status(thm)], ['9', '10'])).
% 0.40/0.58  thf(d10_xboole_0, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.40/0.58  thf('12', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.40/0.58      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.40/0.58  thf('13', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.40/0.58      inference('simplify', [status(thm)], ['12'])).
% 0.40/0.58  thf(t10_xboole_1, axiom,
% 0.40/0.58    (![A:$i,B:$i,C:$i]:
% 0.40/0.58     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 0.40/0.58  thf('14', plain,
% 0.40/0.58      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.40/0.58         (~ (r1_tarski @ X6 @ X7) | (r1_tarski @ X6 @ (k2_xboole_0 @ X8 @ X7)))),
% 0.40/0.58      inference('cnf', [status(esa)], [t10_xboole_1])).
% 0.40/0.58  thf('15', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.40/0.58      inference('sup-', [status(thm)], ['13', '14'])).
% 0.40/0.58  thf(l32_xboole_1, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.40/0.58  thf('16', plain,
% 0.40/0.58      (![X3 : $i, X5 : $i]:
% 0.40/0.58         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.40/0.58      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.40/0.58  thf('17', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.40/0.58      inference('sup-', [status(thm)], ['15', '16'])).
% 0.40/0.58  thf(t48_xboole_1, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.40/0.58  thf('18', plain,
% 0.40/0.58      (![X11 : $i, X12 : $i]:
% 0.40/0.58         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.40/0.58           = (k3_xboole_0 @ X11 @ X12))),
% 0.40/0.58      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.40/0.58  thf('19', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 0.40/0.58           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.40/0.58      inference('sup+', [status(thm)], ['17', '18'])).
% 0.40/0.58  thf('20', plain,
% 0.40/0.58      (((k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ k1_xboole_0)
% 0.40/0.58         = (k3_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_A))),
% 0.40/0.58      inference('sup+', [status(thm)], ['11', '19'])).
% 0.40/0.58  thf('21', plain,
% 0.40/0.58      (![X13 : $i, X14 : $i]:
% 0.40/0.58         ((k2_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ (k4_xboole_0 @ X13 @ X14))
% 0.40/0.58           = (X13))),
% 0.40/0.58      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.40/0.58  thf('22', plain,
% 0.40/0.58      (![X9 : $i, X10 : $i]: (r1_tarski @ (k3_xboole_0 @ X9 @ X10) @ X9)),
% 0.40/0.58      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.40/0.58  thf('23', plain,
% 0.40/0.58      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.40/0.58         (~ (r1_tarski @ X6 @ X7) | (r1_tarski @ X6 @ (k2_xboole_0 @ X8 @ X7)))),
% 0.40/0.58      inference('cnf', [status(esa)], [t10_xboole_1])).
% 0.40/0.58  thf('24', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.58         (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X2 @ X0))),
% 0.40/0.58      inference('sup-', [status(thm)], ['22', '23'])).
% 0.40/0.58  thf('25', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.58         (r1_tarski @ (k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2) @ X0)),
% 0.40/0.58      inference('sup+', [status(thm)], ['21', '24'])).
% 0.40/0.58  thf('26', plain,
% 0.40/0.58      ((r1_tarski @ 
% 0.40/0.58        (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ k1_xboole_0) @ sk_A)),
% 0.40/0.58      inference('sup+', [status(thm)], ['20', '25'])).
% 0.40/0.58  thf('27', plain,
% 0.40/0.58      (![X26 : $i, X27 : $i]:
% 0.40/0.58         ((v1_xboole_0 @ X26)
% 0.40/0.58          | ~ (v1_zfmisc_1 @ X26)
% 0.40/0.58          | ((X27) = (X26))
% 0.40/0.58          | ~ (r1_tarski @ X27 @ X26)
% 0.40/0.58          | (v1_xboole_0 @ X27))),
% 0.40/0.58      inference('cnf', [status(esa)], [t1_tex_2])).
% 0.40/0.58  thf('28', plain,
% 0.40/0.58      (((v1_xboole_0 @ 
% 0.40/0.58         (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ k1_xboole_0))
% 0.40/0.58        | ((k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ k1_xboole_0) = (sk_A))
% 0.40/0.58        | ~ (v1_zfmisc_1 @ sk_A)
% 0.40/0.58        | (v1_xboole_0 @ sk_A))),
% 0.40/0.58      inference('sup-', [status(thm)], ['26', '27'])).
% 0.40/0.58  thf('29', plain, ((v1_zfmisc_1 @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('30', plain,
% 0.40/0.58      (((v1_xboole_0 @ 
% 0.40/0.58         (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ k1_xboole_0))
% 0.40/0.58        | ((k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ k1_xboole_0) = (sk_A))
% 0.40/0.58        | (v1_xboole_0 @ sk_A))),
% 0.40/0.58      inference('demod', [status(thm)], ['28', '29'])).
% 0.40/0.58  thf('31', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('32', plain,
% 0.40/0.58      ((((k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ k1_xboole_0) = (sk_A))
% 0.40/0.58        | (v1_xboole_0 @ 
% 0.40/0.58           (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ k1_xboole_0)))),
% 0.40/0.58      inference('clc', [status(thm)], ['30', '31'])).
% 0.40/0.58  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.40/0.58  thf('33', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.40/0.58      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.40/0.58  thf(t8_boole, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.40/0.58  thf('34', plain,
% 0.40/0.58      (![X15 : $i, X16 : $i]:
% 0.40/0.58         (~ (v1_xboole_0 @ X15) | ~ (v1_xboole_0 @ X16) | ((X15) = (X16)))),
% 0.40/0.58      inference('cnf', [status(esa)], [t8_boole])).
% 0.40/0.58  thf('35', plain,
% 0.40/0.58      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.40/0.58      inference('sup-', [status(thm)], ['33', '34'])).
% 0.40/0.58  thf('36', plain,
% 0.40/0.58      ((((k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ k1_xboole_0) = (sk_A))
% 0.40/0.58        | ((k1_xboole_0)
% 0.40/0.58            = (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ k1_xboole_0)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['32', '35'])).
% 0.40/0.58  thf('37', plain,
% 0.40/0.58      (![X13 : $i, X14 : $i]:
% 0.40/0.58         ((k2_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ (k4_xboole_0 @ X13 @ X14))
% 0.40/0.58           = (X13))),
% 0.40/0.58      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.40/0.58  thf('38', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.40/0.58      inference('sup-', [status(thm)], ['13', '14'])).
% 0.40/0.58  thf('39', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 0.40/0.58      inference('sup+', [status(thm)], ['37', '38'])).
% 0.40/0.58  thf('40', plain,
% 0.40/0.58      (![X3 : $i, X5 : $i]:
% 0.40/0.58         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.40/0.58      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.40/0.58  thf('41', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.40/0.58      inference('sup-', [status(thm)], ['39', '40'])).
% 0.40/0.58  thf('42', plain,
% 0.40/0.58      ((((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B)) = (k1_xboole_0))
% 0.40/0.58        | ((k1_xboole_0)
% 0.40/0.58            = (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ k1_xboole_0)))),
% 0.40/0.58      inference('sup+', [status(thm)], ['36', '41'])).
% 0.40/0.58  thf('43', plain,
% 0.40/0.58      (![X11 : $i, X12 : $i]:
% 0.40/0.58         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.40/0.58           = (k3_xboole_0 @ X11 @ X12))),
% 0.40/0.58      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.40/0.58  thf('44', plain,
% 0.40/0.58      ((((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.40/0.58        | ((k1_xboole_0)
% 0.40/0.58            = (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ k1_xboole_0)))),
% 0.40/0.58      inference('demod', [status(thm)], ['42', '43'])).
% 0.40/0.58  thf('45', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.40/0.58      inference('clc', [status(thm)], ['7', '8'])).
% 0.40/0.58  thf('46', plain,
% 0.40/0.58      ((((sk_A) = (k1_xboole_0))
% 0.40/0.58        | ((k1_xboole_0)
% 0.40/0.58            = (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ k1_xboole_0)))),
% 0.40/0.58      inference('demod', [status(thm)], ['44', '45'])).
% 0.40/0.58  thf('47', plain,
% 0.40/0.58      ((((k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ k1_xboole_0) = (sk_A))
% 0.40/0.58        | ((k1_xboole_0)
% 0.40/0.58            = (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ k1_xboole_0)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['32', '35'])).
% 0.40/0.58  thf('48', plain,
% 0.40/0.58      ((((sk_A) != (k1_xboole_0))
% 0.40/0.58        | ((k1_xboole_0)
% 0.40/0.58            = (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ k1_xboole_0)))),
% 0.40/0.58      inference('eq_fact', [status(thm)], ['47'])).
% 0.40/0.58  thf('49', plain,
% 0.40/0.58      (((k1_xboole_0)
% 0.40/0.58         = (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ k1_xboole_0))),
% 0.40/0.58      inference('clc', [status(thm)], ['46', '48'])).
% 0.40/0.58  thf('50', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.40/0.58      inference('simplify', [status(thm)], ['12'])).
% 0.40/0.58  thf('51', plain,
% 0.40/0.58      (![X3 : $i, X5 : $i]:
% 0.40/0.58         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.40/0.58      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.40/0.58  thf('52', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.40/0.58      inference('sup-', [status(thm)], ['50', '51'])).
% 0.40/0.58  thf('53', plain,
% 0.40/0.58      (![X11 : $i, X12 : $i]:
% 0.40/0.58         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.40/0.58           = (k3_xboole_0 @ X11 @ X12))),
% 0.40/0.58      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.40/0.58  thf('54', plain,
% 0.40/0.58      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.40/0.58      inference('sup+', [status(thm)], ['52', '53'])).
% 0.40/0.58  thf('55', plain,
% 0.40/0.58      (![X13 : $i, X14 : $i]:
% 0.40/0.58         ((k2_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ (k4_xboole_0 @ X13 @ X14))
% 0.40/0.58           = (X13))),
% 0.40/0.58      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.40/0.58  thf('56', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0) @ 
% 0.40/0.58           (k4_xboole_0 @ X0 @ X0)) = (X0))),
% 0.40/0.58      inference('sup+', [status(thm)], ['54', '55'])).
% 0.40/0.58  thf('57', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.40/0.58      inference('sup-', [status(thm)], ['50', '51'])).
% 0.40/0.58  thf('58', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0) @ k1_xboole_0) = (X0))),
% 0.40/0.58      inference('demod', [status(thm)], ['56', '57'])).
% 0.40/0.58  thf('59', plain,
% 0.40/0.58      (((k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.40/0.58      inference('sup+', [status(thm)], ['49', '58'])).
% 0.40/0.58  thf('60', plain,
% 0.40/0.58      (![X9 : $i, X10 : $i]: (r1_tarski @ (k3_xboole_0 @ X9 @ X10) @ X9)),
% 0.40/0.58      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.40/0.58  thf('61', plain,
% 0.40/0.58      (![X3 : $i, X5 : $i]:
% 0.40/0.58         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.40/0.58      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.40/0.58  thf('62', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.40/0.58      inference('sup-', [status(thm)], ['60', '61'])).
% 0.40/0.58  thf('63', plain,
% 0.40/0.58      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.40/0.58      inference('sup+', [status(thm)], ['52', '53'])).
% 0.40/0.58  thf('64', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.40/0.58      inference('sup-', [status(thm)], ['60', '61'])).
% 0.40/0.58  thf('65', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0) @ X0) = (k1_xboole_0))),
% 0.40/0.58      inference('sup+', [status(thm)], ['63', '64'])).
% 0.40/0.58  thf('66', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         ((k4_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ X0))
% 0.40/0.58           = (k1_xboole_0))),
% 0.40/0.58      inference('sup+', [status(thm)], ['62', '65'])).
% 0.40/0.58  thf('67', plain,
% 0.40/0.58      (![X11 : $i, X12 : $i]:
% 0.40/0.58         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.40/0.58           = (k3_xboole_0 @ X11 @ X12))),
% 0.40/0.58      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.40/0.58  thf('68', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         ((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.40/0.58           = (k3_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.40/0.58      inference('sup+', [status(thm)], ['66', '67'])).
% 0.40/0.58  thf('69', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.40/0.58      inference('sup-', [status(thm)], ['50', '51'])).
% 0.40/0.58  thf('70', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         ((k1_xboole_0)
% 0.40/0.58           = (k3_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.40/0.58      inference('demod', [status(thm)], ['68', '69'])).
% 0.40/0.58  thf('71', plain,
% 0.40/0.58      (![X13 : $i, X14 : $i]:
% 0.40/0.58         ((k2_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ (k4_xboole_0 @ X13 @ X14))
% 0.40/0.58           = (X13))),
% 0.40/0.58      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.40/0.58  thf('72', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         ((k2_xboole_0 @ k1_xboole_0 @ 
% 0.40/0.58           (k4_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ X0)))
% 0.40/0.58           = (k1_xboole_0))),
% 0.40/0.58      inference('sup+', [status(thm)], ['70', '71'])).
% 0.40/0.58  thf('73', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         ((k4_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ X0))
% 0.40/0.58           = (k1_xboole_0))),
% 0.40/0.58      inference('sup+', [status(thm)], ['62', '65'])).
% 0.40/0.58  thf('74', plain,
% 0.40/0.58      (((k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.40/0.58      inference('demod', [status(thm)], ['72', '73'])).
% 0.40/0.58  thf('75', plain, (((k1_xboole_0) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.40/0.58      inference('demod', [status(thm)], ['59', '74'])).
% 0.40/0.58  thf('76', plain,
% 0.40/0.58      (![X3 : $i, X4 : $i]:
% 0.40/0.58         ((r1_tarski @ X3 @ X4) | ((k4_xboole_0 @ X3 @ X4) != (k1_xboole_0)))),
% 0.40/0.58      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.40/0.58  thf('77', plain,
% 0.40/0.58      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ sk_A @ sk_B))),
% 0.40/0.58      inference('sup-', [status(thm)], ['75', '76'])).
% 0.40/0.58  thf('78', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.40/0.58      inference('simplify', [status(thm)], ['77'])).
% 0.40/0.58  thf('79', plain, ($false), inference('demod', [status(thm)], ['0', '78'])).
% 0.40/0.58  
% 0.40/0.58  % SZS output end Refutation
% 0.40/0.58  
% 0.40/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
