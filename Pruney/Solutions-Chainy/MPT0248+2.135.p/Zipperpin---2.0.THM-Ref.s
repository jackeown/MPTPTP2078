%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.csHeDcYg3k

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:38 EST 2020

% Result     : Theorem 0.85s
% Output     : Refutation 0.85s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 349 expanded)
%              Number of leaves         :   21 ( 106 expanded)
%              Depth                    :   19
%              Number of atoms          :  817 (3685 expanded)
%              Number of equality atoms :  155 ( 762 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t43_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) )
        & ~ ( ( B
              = ( k1_tarski @ A ) )
            & ( C
              = ( k1_tarski @ A ) ) )
        & ~ ( ( B = k1_xboole_0 )
            & ( C
              = ( k1_tarski @ A ) ) )
        & ~ ( ( B
              = ( k1_tarski @ A ) )
            & ( C = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( ( k1_tarski @ A )
            = ( k2_xboole_0 @ B @ C ) )
          & ~ ( ( B
                = ( k1_tarski @ A ) )
              & ( C
                = ( k1_tarski @ A ) ) )
          & ~ ( ( B = k1_xboole_0 )
              & ( C
                = ( k1_tarski @ A ) ) )
          & ~ ( ( B
                = ( k1_tarski @ A ) )
              & ( C = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t43_zfmisc_1])).

thf('0',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('1',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ X8 @ ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('6',plain,(
    r1_tarski @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('7',plain,(
    ! [X44: $i,X45: $i] :
      ( ( X45
        = ( k1_tarski @ X44 ) )
      | ( X45 = k1_xboole_0 )
      | ~ ( r1_tarski @ X45 @ ( k1_tarski @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('8',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X14 @ X15 ) @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('11',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k5_xboole_0 @ X10 @ ( k5_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('12',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k5_xboole_0 @ X15 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_C @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf('14',plain,
    ( ( ( k3_xboole_0 @ sk_B @ sk_C )
      = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_C @ sk_B ) ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['8','13'])).

thf('15',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k5_xboole_0 @ X10 @ ( k5_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('16',plain,(
    ! [X13: $i] :
      ( ( k5_xboole_0 @ X13 @ X13 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X13: $i] :
      ( ( k5_xboole_0 @ X13 @ X13 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('19',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k5_xboole_0 @ X10 @ ( k5_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X13: $i] :
      ( ( k5_xboole_0 @ X13 @ X13 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('24',plain,(
    ! [X7: $i] :
      ( ( k5_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['20','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['17','26'])).

thf('28',plain,(
    ! [X7: $i] :
      ( ( k5_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['20','25'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['20','25'])).

thf('33',plain,
    ( ( ( k3_xboole_0 @ sk_B @ sk_C )
      = sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['14','31','32'])).

thf('34',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('35',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('36',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('37',plain,(
    ! [X44: $i,X45: $i] :
      ( ( X45
        = ( k1_tarski @ X44 ) )
      | ( X45 = k1_xboole_0 )
      | ~ ( r1_tarski @ X45 @ ( k1_tarski @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( sk_B = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ sk_B @ X0 )
        = ( k1_tarski @ sk_A ) )
      | ( ( k4_xboole_0 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ sk_B @ X0 )
        = sk_B )
      | ( sk_B = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( ( k4_xboole_0 @ sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['34','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( ( k4_xboole_0 @ sk_B @ X0 )
        = sk_B ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_C @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['20','25'])).

thf('44',plain,
    ( ( k5_xboole_0 @ sk_C @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('46',plain,
    ( ( k5_xboole_0 @ sk_C @ ( k1_tarski @ sk_A ) )
    = ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['20','25'])).

thf('48',plain,
    ( ( k1_tarski @ sk_A )
    = ( k5_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( ( k1_tarski @ sk_A )
      = ( k5_xboole_0 @ sk_C @ k1_xboole_0 ) )
    | ( ( k4_xboole_0 @ sk_B @ sk_C )
      = sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['41','48'])).

thf('50',plain,(
    ! [X7: $i] :
      ( ( k5_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('51',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_C )
    | ( ( k4_xboole_0 @ sk_B @ sk_C )
      = sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_C
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( sk_C
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['52'])).

thf('54',plain,
    ( ( sk_C
     != ( k1_tarski @ sk_A ) )
    | ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['52'])).

thf('55',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( sk_C
     != ( k1_tarski @ sk_A ) )
    | ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['55'])).

thf('57',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('58',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['58'])).

thf('60',plain,
    ( ( ( sk_B != sk_B )
      | ( sk_B = k1_xboole_0 ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['57','59'])).

thf('61',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['52'])).

thf('63',plain,
    ( ( sk_B != sk_B )
   <= ( ( sk_B != k1_xboole_0 )
      & ( sk_B
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    sk_C
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['54','56','64'])).

thf('66',plain,(
    sk_C
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['53','65'])).

thf('67',plain,
    ( ( ( k4_xboole_0 @ sk_B @ sk_C )
      = sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['51','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['20','25'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( ( k3_xboole_0 @ sk_B @ sk_C )
      = ( k5_xboole_0 @ sk_B @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['67','70'])).

thf('72',plain,(
    ! [X13: $i] :
      ( ( k5_xboole_0 @ X13 @ X13 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('73',plain,
    ( ( ( k3_xboole_0 @ sk_B @ sk_C )
      = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['33','73'])).

thf('75',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,
    ( ( sk_C != k1_xboole_0 )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(split,[status(esa)],['58'])).

thf('77',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('80',plain,
    ( ! [X0: $i] :
        ( ( k2_xboole_0 @ sk_B @ X0 )
        = X0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_C )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['77','80'])).

thf('82',plain,(
    sk_C
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['53','65'])).

thf('83',plain,
    ( sk_B
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( sk_C != k1_xboole_0 )
    | ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['58'])).

thf('85',plain,(
    sk_C != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['83','84'])).

thf('86',plain,(
    sk_C != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['76','85'])).

thf('87',plain,(
    sk_B = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['75','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_B @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['3','87'])).

thf('89',plain,
    ( ( k1_tarski @ sk_A )
    = sk_C ),
    inference(demod,[status(thm)],['0','88'])).

thf('90',plain,(
    sk_C
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['53','65'])).

thf('91',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['89','90'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.csHeDcYg3k
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:45:18 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.85/1.03  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.85/1.03  % Solved by: fo/fo7.sh
% 0.85/1.03  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.85/1.03  % done 1396 iterations in 0.612s
% 0.85/1.03  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.85/1.03  % SZS output start Refutation
% 0.85/1.03  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.85/1.03  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.85/1.03  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.85/1.03  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.85/1.03  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.85/1.03  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.85/1.03  thf(sk_B_type, type, sk_B: $i).
% 0.85/1.03  thf(sk_C_type, type, sk_C: $i).
% 0.85/1.03  thf(sk_A_type, type, sk_A: $i).
% 0.85/1.03  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.85/1.03  thf(t43_zfmisc_1, conjecture,
% 0.85/1.03    (![A:$i,B:$i,C:$i]:
% 0.85/1.03     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.85/1.03          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.85/1.03          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.85/1.03          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.85/1.03  thf(zf_stmt_0, negated_conjecture,
% 0.85/1.03    (~( ![A:$i,B:$i,C:$i]:
% 0.85/1.03        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.85/1.03             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.85/1.03             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.85/1.03             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.85/1.03    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 0.85/1.03  thf('0', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.85/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.03  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.85/1.03  thf('1', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.85/1.03      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.85/1.03  thf(t12_xboole_1, axiom,
% 0.85/1.03    (![A:$i,B:$i]:
% 0.85/1.03     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.85/1.03  thf('2', plain,
% 0.85/1.03      (![X2 : $i, X3 : $i]:
% 0.85/1.03         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 0.85/1.03      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.85/1.03  thf('3', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.85/1.03      inference('sup-', [status(thm)], ['1', '2'])).
% 0.85/1.03  thf('4', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.85/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.03  thf(t7_xboole_1, axiom,
% 0.85/1.03    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.85/1.03  thf('5', plain,
% 0.85/1.03      (![X8 : $i, X9 : $i]: (r1_tarski @ X8 @ (k2_xboole_0 @ X8 @ X9))),
% 0.85/1.03      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.85/1.03  thf('6', plain, ((r1_tarski @ sk_B @ (k1_tarski @ sk_A))),
% 0.85/1.03      inference('sup+', [status(thm)], ['4', '5'])).
% 0.85/1.03  thf(l3_zfmisc_1, axiom,
% 0.85/1.03    (![A:$i,B:$i]:
% 0.85/1.03     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.85/1.03       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.85/1.03  thf('7', plain,
% 0.85/1.03      (![X44 : $i, X45 : $i]:
% 0.85/1.03         (((X45) = (k1_tarski @ X44))
% 0.85/1.03          | ((X45) = (k1_xboole_0))
% 0.85/1.03          | ~ (r1_tarski @ X45 @ (k1_tarski @ X44)))),
% 0.85/1.03      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.85/1.03  thf('8', plain, ((((sk_B) = (k1_xboole_0)) | ((sk_B) = (k1_tarski @ sk_A)))),
% 0.85/1.03      inference('sup-', [status(thm)], ['6', '7'])).
% 0.85/1.03  thf('9', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.85/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.03  thf(t95_xboole_1, axiom,
% 0.85/1.03    (![A:$i,B:$i]:
% 0.85/1.03     ( ( k3_xboole_0 @ A @ B ) =
% 0.85/1.03       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.85/1.03  thf('10', plain,
% 0.85/1.03      (![X14 : $i, X15 : $i]:
% 0.85/1.03         ((k3_xboole_0 @ X14 @ X15)
% 0.85/1.03           = (k5_xboole_0 @ (k5_xboole_0 @ X14 @ X15) @ 
% 0.85/1.03              (k2_xboole_0 @ X14 @ X15)))),
% 0.85/1.03      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.85/1.03  thf(t91_xboole_1, axiom,
% 0.85/1.03    (![A:$i,B:$i,C:$i]:
% 0.85/1.03     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.85/1.03       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.85/1.03  thf('11', plain,
% 0.85/1.03      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.85/1.03         ((k5_xboole_0 @ (k5_xboole_0 @ X10 @ X11) @ X12)
% 0.85/1.03           = (k5_xboole_0 @ X10 @ (k5_xboole_0 @ X11 @ X12)))),
% 0.85/1.03      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.85/1.03  thf('12', plain,
% 0.85/1.03      (![X14 : $i, X15 : $i]:
% 0.85/1.03         ((k3_xboole_0 @ X14 @ X15)
% 0.85/1.03           = (k5_xboole_0 @ X14 @ 
% 0.85/1.03              (k5_xboole_0 @ X15 @ (k2_xboole_0 @ X14 @ X15))))),
% 0.85/1.03      inference('demod', [status(thm)], ['10', '11'])).
% 0.85/1.03  thf('13', plain,
% 0.85/1.03      (((k3_xboole_0 @ sk_B @ sk_C)
% 0.85/1.03         = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_C @ (k1_tarski @ sk_A))))),
% 0.85/1.03      inference('sup+', [status(thm)], ['9', '12'])).
% 0.85/1.03  thf('14', plain,
% 0.85/1.03      ((((k3_xboole_0 @ sk_B @ sk_C)
% 0.85/1.03          = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_C @ sk_B)))
% 0.85/1.03        | ((sk_B) = (k1_xboole_0)))),
% 0.85/1.03      inference('sup+', [status(thm)], ['8', '13'])).
% 0.85/1.03  thf('15', plain,
% 0.85/1.03      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.85/1.03         ((k5_xboole_0 @ (k5_xboole_0 @ X10 @ X11) @ X12)
% 0.85/1.03           = (k5_xboole_0 @ X10 @ (k5_xboole_0 @ X11 @ X12)))),
% 0.85/1.03      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.85/1.03  thf(t92_xboole_1, axiom,
% 0.85/1.03    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.85/1.03  thf('16', plain, (![X13 : $i]: ((k5_xboole_0 @ X13 @ X13) = (k1_xboole_0))),
% 0.85/1.03      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.85/1.03  thf('17', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         ((k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))
% 0.85/1.03           = (k1_xboole_0))),
% 0.85/1.03      inference('sup+', [status(thm)], ['15', '16'])).
% 0.85/1.03  thf('18', plain, (![X13 : $i]: ((k5_xboole_0 @ X13 @ X13) = (k1_xboole_0))),
% 0.85/1.03      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.85/1.03  thf('19', plain,
% 0.85/1.03      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.85/1.03         ((k5_xboole_0 @ (k5_xboole_0 @ X10 @ X11) @ X12)
% 0.85/1.03           = (k5_xboole_0 @ X10 @ (k5_xboole_0 @ X11 @ X12)))),
% 0.85/1.03      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.85/1.03  thf('20', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.85/1.03           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.85/1.03      inference('sup+', [status(thm)], ['18', '19'])).
% 0.85/1.03  thf('21', plain, (![X13 : $i]: ((k5_xboole_0 @ X13 @ X13) = (k1_xboole_0))),
% 0.85/1.03      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.85/1.03  thf('22', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.85/1.03           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.85/1.03      inference('sup+', [status(thm)], ['18', '19'])).
% 0.85/1.03  thf('23', plain,
% 0.85/1.03      (![X0 : $i]:
% 0.85/1.03         ((k5_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.85/1.03      inference('sup+', [status(thm)], ['21', '22'])).
% 0.85/1.03  thf(t5_boole, axiom,
% 0.85/1.03    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.85/1.03  thf('24', plain, (![X7 : $i]: ((k5_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.85/1.03      inference('cnf', [status(esa)], [t5_boole])).
% 0.85/1.03  thf('25', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.85/1.03      inference('demod', [status(thm)], ['23', '24'])).
% 0.85/1.03  thf('26', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.85/1.03      inference('demod', [status(thm)], ['20', '25'])).
% 0.85/1.03  thf('27', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 0.85/1.03           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 0.85/1.03      inference('sup+', [status(thm)], ['17', '26'])).
% 0.85/1.03  thf('28', plain, (![X7 : $i]: ((k5_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.85/1.03      inference('cnf', [status(esa)], [t5_boole])).
% 0.85/1.03  thf('29', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 0.85/1.03      inference('demod', [status(thm)], ['27', '28'])).
% 0.85/1.03  thf('30', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.85/1.03      inference('demod', [status(thm)], ['20', '25'])).
% 0.85/1.03  thf('31', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 0.85/1.03      inference('sup+', [status(thm)], ['29', '30'])).
% 0.85/1.03  thf('32', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.85/1.03      inference('demod', [status(thm)], ['20', '25'])).
% 0.85/1.03  thf('33', plain,
% 0.85/1.03      ((((k3_xboole_0 @ sk_B @ sk_C) = (sk_C)) | ((sk_B) = (k1_xboole_0)))),
% 0.85/1.03      inference('demod', [status(thm)], ['14', '31', '32'])).
% 0.85/1.03  thf('34', plain,
% 0.85/1.03      ((((sk_B) = (k1_xboole_0)) | ((sk_B) = (k1_tarski @ sk_A)))),
% 0.85/1.03      inference('sup-', [status(thm)], ['6', '7'])).
% 0.85/1.03  thf(t36_xboole_1, axiom,
% 0.85/1.03    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.85/1.03  thf('35', plain,
% 0.85/1.03      (![X5 : $i, X6 : $i]: (r1_tarski @ (k4_xboole_0 @ X5 @ X6) @ X5)),
% 0.85/1.03      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.85/1.03  thf('36', plain,
% 0.85/1.03      ((((sk_B) = (k1_xboole_0)) | ((sk_B) = (k1_tarski @ sk_A)))),
% 0.85/1.03      inference('sup-', [status(thm)], ['6', '7'])).
% 0.85/1.03  thf('37', plain,
% 0.85/1.03      (![X44 : $i, X45 : $i]:
% 0.85/1.03         (((X45) = (k1_tarski @ X44))
% 0.85/1.03          | ((X45) = (k1_xboole_0))
% 0.85/1.03          | ~ (r1_tarski @ X45 @ (k1_tarski @ X44)))),
% 0.85/1.03      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.85/1.03  thf('38', plain,
% 0.85/1.03      (![X0 : $i]:
% 0.85/1.03         (~ (r1_tarski @ X0 @ sk_B)
% 0.85/1.03          | ((sk_B) = (k1_xboole_0))
% 0.85/1.03          | ((X0) = (k1_xboole_0))
% 0.85/1.03          | ((X0) = (k1_tarski @ sk_A)))),
% 0.85/1.03      inference('sup-', [status(thm)], ['36', '37'])).
% 0.85/1.03  thf('39', plain,
% 0.85/1.03      (![X0 : $i]:
% 0.85/1.03         (((k4_xboole_0 @ sk_B @ X0) = (k1_tarski @ sk_A))
% 0.85/1.03          | ((k4_xboole_0 @ sk_B @ X0) = (k1_xboole_0))
% 0.85/1.03          | ((sk_B) = (k1_xboole_0)))),
% 0.85/1.03      inference('sup-', [status(thm)], ['35', '38'])).
% 0.85/1.03  thf('40', plain,
% 0.85/1.03      (![X0 : $i]:
% 0.85/1.03         (((k4_xboole_0 @ sk_B @ X0) = (sk_B))
% 0.85/1.03          | ((sk_B) = (k1_xboole_0))
% 0.85/1.03          | ((sk_B) = (k1_xboole_0))
% 0.85/1.03          | ((k4_xboole_0 @ sk_B @ X0) = (k1_xboole_0)))),
% 0.85/1.03      inference('sup+', [status(thm)], ['34', '39'])).
% 0.85/1.03  thf('41', plain,
% 0.85/1.03      (![X0 : $i]:
% 0.85/1.03         (((k4_xboole_0 @ sk_B @ X0) = (k1_xboole_0))
% 0.85/1.03          | ((sk_B) = (k1_xboole_0))
% 0.85/1.03          | ((k4_xboole_0 @ sk_B @ X0) = (sk_B)))),
% 0.85/1.03      inference('simplify', [status(thm)], ['40'])).
% 0.85/1.03  thf('42', plain,
% 0.85/1.03      (((k3_xboole_0 @ sk_B @ sk_C)
% 0.85/1.03         = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_C @ (k1_tarski @ sk_A))))),
% 0.85/1.03      inference('sup+', [status(thm)], ['9', '12'])).
% 0.85/1.03  thf('43', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.85/1.03      inference('demod', [status(thm)], ['20', '25'])).
% 0.85/1.03  thf('44', plain,
% 0.85/1.03      (((k5_xboole_0 @ sk_C @ (k1_tarski @ sk_A))
% 0.85/1.03         = (k5_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_B @ sk_C)))),
% 0.85/1.03      inference('sup+', [status(thm)], ['42', '43'])).
% 0.85/1.03  thf(t100_xboole_1, axiom,
% 0.85/1.03    (![A:$i,B:$i]:
% 0.85/1.03     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.85/1.03  thf('45', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         ((k4_xboole_0 @ X0 @ X1)
% 0.85/1.03           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.85/1.03      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.85/1.03  thf('46', plain,
% 0.85/1.03      (((k5_xboole_0 @ sk_C @ (k1_tarski @ sk_A)) = (k4_xboole_0 @ sk_B @ sk_C))),
% 0.85/1.03      inference('demod', [status(thm)], ['44', '45'])).
% 0.85/1.03  thf('47', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.85/1.03      inference('demod', [status(thm)], ['20', '25'])).
% 0.85/1.03  thf('48', plain,
% 0.85/1.03      (((k1_tarski @ sk_A) = (k5_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 0.85/1.03      inference('sup+', [status(thm)], ['46', '47'])).
% 0.85/1.03  thf('49', plain,
% 0.85/1.03      ((((k1_tarski @ sk_A) = (k5_xboole_0 @ sk_C @ k1_xboole_0))
% 0.85/1.03        | ((k4_xboole_0 @ sk_B @ sk_C) = (sk_B))
% 0.85/1.03        | ((sk_B) = (k1_xboole_0)))),
% 0.85/1.03      inference('sup+', [status(thm)], ['41', '48'])).
% 0.85/1.03  thf('50', plain, (![X7 : $i]: ((k5_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.85/1.03      inference('cnf', [status(esa)], [t5_boole])).
% 0.85/1.03  thf('51', plain,
% 0.85/1.03      ((((k1_tarski @ sk_A) = (sk_C))
% 0.85/1.03        | ((k4_xboole_0 @ sk_B @ sk_C) = (sk_B))
% 0.85/1.03        | ((sk_B) = (k1_xboole_0)))),
% 0.85/1.03      inference('demod', [status(thm)], ['49', '50'])).
% 0.85/1.03  thf('52', plain,
% 0.85/1.03      ((((sk_B) != (k1_xboole_0)) | ((sk_C) != (k1_tarski @ sk_A)))),
% 0.85/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.03  thf('53', plain,
% 0.85/1.03      ((((sk_C) != (k1_tarski @ sk_A))) <= (~ (((sk_C) = (k1_tarski @ sk_A))))),
% 0.85/1.03      inference('split', [status(esa)], ['52'])).
% 0.85/1.03  thf('54', plain,
% 0.85/1.03      (~ (((sk_C) = (k1_tarski @ sk_A))) | ~ (((sk_B) = (k1_xboole_0)))),
% 0.85/1.03      inference('split', [status(esa)], ['52'])).
% 0.85/1.03  thf('55', plain,
% 0.85/1.03      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C) != (k1_tarski @ sk_A)))),
% 0.85/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.03  thf('56', plain,
% 0.85/1.03      (~ (((sk_C) = (k1_tarski @ sk_A))) | ~ (((sk_B) = (k1_tarski @ sk_A)))),
% 0.85/1.03      inference('split', [status(esa)], ['55'])).
% 0.85/1.03  thf('57', plain,
% 0.85/1.03      ((((sk_B) = (k1_xboole_0)) | ((sk_B) = (k1_tarski @ sk_A)))),
% 0.85/1.03      inference('sup-', [status(thm)], ['6', '7'])).
% 0.85/1.03  thf('58', plain,
% 0.85/1.03      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C) != (k1_xboole_0)))),
% 0.85/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.03  thf('59', plain,
% 0.85/1.03      ((((sk_B) != (k1_tarski @ sk_A))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.85/1.03      inference('split', [status(esa)], ['58'])).
% 0.85/1.03  thf('60', plain,
% 0.85/1.03      (((((sk_B) != (sk_B)) | ((sk_B) = (k1_xboole_0))))
% 0.85/1.03         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.85/1.03      inference('sup-', [status(thm)], ['57', '59'])).
% 0.85/1.03  thf('61', plain,
% 0.85/1.03      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.85/1.03      inference('simplify', [status(thm)], ['60'])).
% 0.85/1.03  thf('62', plain,
% 0.85/1.03      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.85/1.03      inference('split', [status(esa)], ['52'])).
% 0.85/1.03  thf('63', plain,
% 0.85/1.03      ((((sk_B) != (sk_B)))
% 0.85/1.03         <= (~ (((sk_B) = (k1_xboole_0))) & ~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.85/1.03      inference('sup-', [status(thm)], ['61', '62'])).
% 0.85/1.03  thf('64', plain,
% 0.85/1.03      ((((sk_B) = (k1_xboole_0))) | (((sk_B) = (k1_tarski @ sk_A)))),
% 0.85/1.03      inference('simplify', [status(thm)], ['63'])).
% 0.85/1.03  thf('65', plain, (~ (((sk_C) = (k1_tarski @ sk_A)))),
% 0.85/1.03      inference('sat_resolution*', [status(thm)], ['54', '56', '64'])).
% 0.85/1.03  thf('66', plain, (((sk_C) != (k1_tarski @ sk_A))),
% 0.85/1.03      inference('simpl_trail', [status(thm)], ['53', '65'])).
% 0.85/1.03  thf('67', plain,
% 0.85/1.03      ((((k4_xboole_0 @ sk_B @ sk_C) = (sk_B)) | ((sk_B) = (k1_xboole_0)))),
% 0.85/1.03      inference('simplify_reflect-', [status(thm)], ['51', '66'])).
% 0.85/1.03  thf('68', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         ((k4_xboole_0 @ X0 @ X1)
% 0.85/1.03           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.85/1.03      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.85/1.03  thf('69', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.85/1.03      inference('demod', [status(thm)], ['20', '25'])).
% 0.85/1.03  thf('70', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         ((k3_xboole_0 @ X1 @ X0)
% 0.85/1.03           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.85/1.03      inference('sup+', [status(thm)], ['68', '69'])).
% 0.85/1.03  thf('71', plain,
% 0.85/1.03      ((((k3_xboole_0 @ sk_B @ sk_C) = (k5_xboole_0 @ sk_B @ sk_B))
% 0.85/1.03        | ((sk_B) = (k1_xboole_0)))),
% 0.85/1.03      inference('sup+', [status(thm)], ['67', '70'])).
% 0.85/1.03  thf('72', plain, (![X13 : $i]: ((k5_xboole_0 @ X13 @ X13) = (k1_xboole_0))),
% 0.85/1.03      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.85/1.03  thf('73', plain,
% 0.85/1.03      ((((k3_xboole_0 @ sk_B @ sk_C) = (k1_xboole_0))
% 0.85/1.03        | ((sk_B) = (k1_xboole_0)))),
% 0.85/1.03      inference('demod', [status(thm)], ['71', '72'])).
% 0.85/1.03  thf('74', plain,
% 0.85/1.03      ((((sk_C) = (k1_xboole_0))
% 0.85/1.03        | ((sk_B) = (k1_xboole_0))
% 0.85/1.03        | ((sk_B) = (k1_xboole_0)))),
% 0.85/1.03      inference('sup+', [status(thm)], ['33', '73'])).
% 0.85/1.03  thf('75', plain, ((((sk_B) = (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 0.85/1.03      inference('simplify', [status(thm)], ['74'])).
% 0.85/1.03  thf('76', plain,
% 0.85/1.03      ((((sk_C) != (k1_xboole_0))) <= (~ (((sk_C) = (k1_xboole_0))))),
% 0.85/1.03      inference('split', [status(esa)], ['58'])).
% 0.85/1.03  thf('77', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.85/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.03  thf('78', plain,
% 0.85/1.03      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.85/1.03      inference('simplify', [status(thm)], ['60'])).
% 0.85/1.03  thf('79', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.85/1.03      inference('sup-', [status(thm)], ['1', '2'])).
% 0.85/1.03  thf('80', plain,
% 0.85/1.03      ((![X0 : $i]: ((k2_xboole_0 @ sk_B @ X0) = (X0)))
% 0.85/1.03         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.85/1.03      inference('sup+', [status(thm)], ['78', '79'])).
% 0.85/1.03  thf('81', plain,
% 0.85/1.03      ((((k1_tarski @ sk_A) = (sk_C))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.85/1.03      inference('sup+', [status(thm)], ['77', '80'])).
% 0.85/1.03  thf('82', plain, (((sk_C) != (k1_tarski @ sk_A))),
% 0.85/1.03      inference('simpl_trail', [status(thm)], ['53', '65'])).
% 0.85/1.03  thf('83', plain, ((((sk_B) = (k1_tarski @ sk_A)))),
% 0.85/1.03      inference('simplify_reflect-', [status(thm)], ['81', '82'])).
% 0.85/1.03  thf('84', plain,
% 0.85/1.03      (~ (((sk_C) = (k1_xboole_0))) | ~ (((sk_B) = (k1_tarski @ sk_A)))),
% 0.85/1.03      inference('split', [status(esa)], ['58'])).
% 0.85/1.03  thf('85', plain, (~ (((sk_C) = (k1_xboole_0)))),
% 0.85/1.03      inference('sat_resolution*', [status(thm)], ['83', '84'])).
% 0.85/1.03  thf('86', plain, (((sk_C) != (k1_xboole_0))),
% 0.85/1.03      inference('simpl_trail', [status(thm)], ['76', '85'])).
% 0.85/1.03  thf('87', plain, (((sk_B) = (k1_xboole_0))),
% 0.85/1.03      inference('simplify_reflect-', [status(thm)], ['75', '86'])).
% 0.85/1.03  thf('88', plain, (![X0 : $i]: ((k2_xboole_0 @ sk_B @ X0) = (X0))),
% 0.85/1.03      inference('demod', [status(thm)], ['3', '87'])).
% 0.85/1.03  thf('89', plain, (((k1_tarski @ sk_A) = (sk_C))),
% 0.85/1.03      inference('demod', [status(thm)], ['0', '88'])).
% 0.85/1.03  thf('90', plain, (((sk_C) != (k1_tarski @ sk_A))),
% 0.85/1.03      inference('simpl_trail', [status(thm)], ['53', '65'])).
% 0.85/1.03  thf('91', plain, ($false),
% 0.85/1.03      inference('simplify_reflect-', [status(thm)], ['89', '90'])).
% 0.85/1.03  
% 0.85/1.03  % SZS output end Refutation
% 0.85/1.03  
% 0.85/1.04  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
