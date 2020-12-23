%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sA3I4w3BT6

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:18 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 252 expanded)
%              Number of leaves         :   22 (  75 expanded)
%              Depth                    :   17
%              Number of atoms          :  640 (2664 expanded)
%              Number of equality atoms :   40 ( 170 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t128_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ D ) )
    <=> ( ( A = C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ D ) )
      <=> ( ( A = C )
          & ( r2_hidden @ B @ D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t128_zfmisc_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_D )
    | ( sk_A != sk_C_1 )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ sk_D ) )
   <= ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ sk_D ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ sk_D ) )
    | ~ ( r2_hidden @ sk_B @ sk_D )
    | ( sk_A != sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( sk_A = sk_C_1 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ sk_D ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ sk_D ) ) ),
    inference(split,[status(esa)],['3'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('5',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( r2_hidden @ X13 @ X14 )
      | ~ ( r2_hidden @ ( k4_tarski @ X13 @ X15 ) @ ( k2_zfmisc_1 @ X14 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('6',plain,
    ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_C_1 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t69_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
      | ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = k1_xboole_0 ) ) )).

thf('7',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X20 ) @ X21 )
        = ( k1_tarski @ X20 ) )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X20 ) @ X21 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t69_zfmisc_1])).

thf(t90_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) @ B ) )).

thf('8',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) ) @ X10 ) ),
    inference(cnf,[status(esa)],[t90_xboole_1])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) )
      = ( k4_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('10',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X10 ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('11',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('12',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('13',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X3 @ X1 )
      | ~ ( r2_hidden @ X3 @ X4 )
      | ~ ( r1_xboole_0 @ X1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','16'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(l29_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k3_xboole_0 @ A @ ( k1_tarski @ B ) )
        = ( k1_tarski @ B ) )
     => ( r2_hidden @ B @ A ) ) )).

thf('19',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r2_hidden @ X11 @ X12 )
      | ( ( k3_xboole_0 @ X12 @ ( k1_tarski @ X11 ) )
       != ( k1_tarski @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[l29_zfmisc_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X3 @ X1 )
      | ~ ( r2_hidden @ X3 @ X4 )
      | ~ ( r1_xboole_0 @ X1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','24'])).

thf('26',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_C_1 ) @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['6','25'])).

thf(t21_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = k1_xboole_0 )
     => ( A = B ) ) )).

thf('27',plain,(
    ! [X18: $i,X19: $i] :
      ( ( X19 = X18 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X19 ) @ ( k1_tarski @ X18 ) )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t21_zfmisc_1])).

thf('28',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_C_1 = sk_A ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( sk_C_1 = sk_A )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ sk_D ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ( sk_A != sk_C_1 )
   <= ( sk_A != sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('31',plain,
    ( ( sk_A != sk_A )
   <= ( ( sk_A != sk_C_1 )
      & ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( sk_A = sk_C_1 )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ sk_D ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ( sk_A = sk_C_1 )
   <= ( sk_A = sk_C_1 ) ),
    inference(split,[status(esa)],['3'])).

thf('34',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ sk_D ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ sk_D ) ) ),
    inference(split,[status(esa)],['3'])).

thf('35',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_D ) )
   <= ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ sk_D ) )
      & ( sk_A = sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( r2_hidden @ X15 @ X16 )
      | ~ ( r2_hidden @ ( k4_tarski @ X13 @ X15 ) @ ( k2_zfmisc_1 @ X14 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('37',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
   <= ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ sk_D ) )
      & ( sk_A = sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_D )
   <= ~ ( r2_hidden @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('39',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ sk_D ) )
    | ( sk_A != sk_C_1 )
    | ( r2_hidden @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ sk_D ) ) ),
    inference('sat_resolution*',[status(thm)],['2','32','39'])).

thf('41',plain,(
    ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ sk_D ) ) ),
    inference(simpl_trail,[status(thm)],['1','40'])).

thf('42',plain,
    ( ( sk_A = sk_C_1 )
   <= ( sk_A = sk_C_1 ) ),
    inference(split,[status(esa)],['3'])).

thf('43',plain,
    ( ( sk_A = sk_C_1 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ sk_D ) ) ),
    inference(split,[status(esa)],['3'])).

thf('44',plain,(
    sk_A = sk_C_1 ),
    inference('sat_resolution*',[status(thm)],['2','32','39','43'])).

thf('45',plain,(
    sk_A = sk_C_1 ),
    inference(simpl_trail,[status(thm)],['42','44'])).

thf('46',plain,(
    ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_D ) ) ),
    inference(demod,[status(thm)],['41','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('48',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
   <= ( r2_hidden @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['48'])).

thf('50',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ sk_D ) ) ),
    inference(split,[status(esa)],['48'])).

thf('51',plain,(
    r2_hidden @ sk_B @ sk_D ),
    inference('sat_resolution*',[status(thm)],['2','32','39','50'])).

thf('52',plain,(
    r2_hidden @ sk_B @ sk_D ),
    inference(simpl_trail,[status(thm)],['49','51'])).

thf('53',plain,(
    ! [X13: $i,X14: $i,X15: $i,X17: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X13 @ X15 ) @ ( k2_zfmisc_1 @ X14 @ X17 ) )
      | ~ ( r2_hidden @ X15 @ X17 )
      | ~ ( r2_hidden @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ sk_B ) @ ( k2_zfmisc_1 @ X0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( k4_tarski @ X0 @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['47','54'])).

thf('56',plain,(
    $false ),
    inference(demod,[status(thm)],['46','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sA3I4w3BT6
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:12:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.51  % Solved by: fo/fo7.sh
% 0.20/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.51  % done 171 iterations in 0.077s
% 0.20/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.51  % SZS output start Refutation
% 0.20/0.51  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.51  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.51  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.51  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.51  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.51  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.51  thf(t128_zfmisc_1, conjecture,
% 0.20/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.51     ( ( r2_hidden @
% 0.20/0.51         ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ D ) ) <=>
% 0.20/0.51       ( ( ( A ) = ( C ) ) & ( r2_hidden @ B @ D ) ) ))).
% 0.20/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.51    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.51        ( ( r2_hidden @
% 0.20/0.51            ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ D ) ) <=>
% 0.20/0.51          ( ( ( A ) = ( C ) ) & ( r2_hidden @ B @ D ) ) ) )),
% 0.20/0.51    inference('cnf.neg', [status(esa)], [t128_zfmisc_1])).
% 0.20/0.51  thf('0', plain,
% 0.20/0.51      ((~ (r2_hidden @ sk_B @ sk_D)
% 0.20/0.51        | ((sk_A) != (sk_C_1))
% 0.20/0.51        | ~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.51             (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ sk_D)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('1', plain,
% 0.20/0.51      ((~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.51           (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ sk_D)))
% 0.20/0.51         <= (~
% 0.20/0.51             ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.51               (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ sk_D))))),
% 0.20/0.51      inference('split', [status(esa)], ['0'])).
% 0.20/0.51  thf('2', plain,
% 0.20/0.51      (~
% 0.20/0.51       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.51         (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ sk_D))) | 
% 0.20/0.51       ~ ((r2_hidden @ sk_B @ sk_D)) | ~ (((sk_A) = (sk_C_1)))),
% 0.20/0.51      inference('split', [status(esa)], ['0'])).
% 0.20/0.51  thf('3', plain,
% 0.20/0.51      ((((sk_A) = (sk_C_1))
% 0.20/0.51        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.51           (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ sk_D)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('4', plain,
% 0.20/0.51      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.51         (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ sk_D)))
% 0.20/0.51         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.51               (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ sk_D))))),
% 0.20/0.51      inference('split', [status(esa)], ['3'])).
% 0.20/0.51  thf(l54_zfmisc_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.51     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.20/0.51       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.20/0.51  thf('5', plain,
% 0.20/0.51      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.51         ((r2_hidden @ X13 @ X14)
% 0.20/0.51          | ~ (r2_hidden @ (k4_tarski @ X13 @ X15) @ (k2_zfmisc_1 @ X14 @ X16)))),
% 0.20/0.51      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.20/0.51  thf('6', plain,
% 0.20/0.51      (((r2_hidden @ sk_A @ (k1_tarski @ sk_C_1)))
% 0.20/0.51         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.51               (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ sk_D))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.51  thf(t69_zfmisc_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) | 
% 0.20/0.51       ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.51  thf('7', plain,
% 0.20/0.51      (![X20 : $i, X21 : $i]:
% 0.20/0.51         (((k4_xboole_0 @ (k1_tarski @ X20) @ X21) = (k1_tarski @ X20))
% 0.20/0.51          | ((k4_xboole_0 @ (k1_tarski @ X20) @ X21) = (k1_xboole_0)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t69_zfmisc_1])).
% 0.20/0.51  thf(t90_xboole_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( r1_xboole_0 @ ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) @ B ))).
% 0.20/0.51  thf('8', plain,
% 0.20/0.51      (![X9 : $i, X10 : $i]:
% 0.20/0.51         (r1_xboole_0 @ (k4_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)) @ X10)),
% 0.20/0.51      inference('cnf', [status(esa)], [t90_xboole_1])).
% 0.20/0.51  thf(t47_xboole_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.20/0.51  thf('9', plain,
% 0.20/0.51      (![X5 : $i, X6 : $i]:
% 0.20/0.51         ((k4_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6))
% 0.20/0.51           = (k4_xboole_0 @ X5 @ X6))),
% 0.20/0.51      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.20/0.51  thf('10', plain,
% 0.20/0.51      (![X9 : $i, X10 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X10)),
% 0.20/0.51      inference('demod', [status(thm)], ['8', '9'])).
% 0.20/0.51  thf(t3_xboole_0, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.20/0.51            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.51       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.20/0.51            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.20/0.51  thf('11', plain,
% 0.20/0.51      (![X1 : $i, X2 : $i]:
% 0.20/0.51         ((r1_xboole_0 @ X1 @ X2) | (r2_hidden @ (sk_C @ X2 @ X1) @ X1))),
% 0.20/0.51      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.51  thf('12', plain,
% 0.20/0.51      (![X1 : $i, X2 : $i]:
% 0.20/0.51         ((r1_xboole_0 @ X1 @ X2) | (r2_hidden @ (sk_C @ X2 @ X1) @ X2))),
% 0.20/0.51      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.51  thf('13', plain,
% 0.20/0.51      (![X1 : $i, X3 : $i, X4 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X3 @ X1)
% 0.20/0.51          | ~ (r2_hidden @ X3 @ X4)
% 0.20/0.51          | ~ (r1_xboole_0 @ X1 @ X4))),
% 0.20/0.51      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.51  thf('14', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.51         ((r1_xboole_0 @ X1 @ X0)
% 0.20/0.51          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.20/0.51          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.20/0.51      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.51  thf('15', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((r1_xboole_0 @ X0 @ X1)
% 0.20/0.51          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.20/0.51          | (r1_xboole_0 @ X0 @ X1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['11', '14'])).
% 0.20/0.51  thf('16', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.20/0.51      inference('simplify', [status(thm)], ['15'])).
% 0.20/0.51  thf('17', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['10', '16'])).
% 0.20/0.51  thf(idempotence_k3_xboole_0, axiom,
% 0.20/0.51    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.20/0.51  thf('18', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.20/0.51      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.20/0.51  thf(l29_zfmisc_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( k3_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( k1_tarski @ B ) ) =>
% 0.20/0.51       ( r2_hidden @ B @ A ) ))).
% 0.20/0.51  thf('19', plain,
% 0.20/0.51      (![X11 : $i, X12 : $i]:
% 0.20/0.51         ((r2_hidden @ X11 @ X12)
% 0.20/0.51          | ((k3_xboole_0 @ X12 @ (k1_tarski @ X11)) != (k1_tarski @ X11)))),
% 0.20/0.51      inference('cnf', [status(esa)], [l29_zfmisc_1])).
% 0.20/0.51  thf('20', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (((k1_tarski @ X0) != (k1_tarski @ X0))
% 0.20/0.51          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.51  thf('21', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.20/0.51      inference('simplify', [status(thm)], ['20'])).
% 0.20/0.51  thf('22', plain,
% 0.20/0.51      (![X1 : $i, X3 : $i, X4 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X3 @ X1)
% 0.20/0.51          | ~ (r2_hidden @ X3 @ X4)
% 0.20/0.51          | ~ (r1_xboole_0 @ X1 @ X4))),
% 0.20/0.51      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.51  thf('23', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (~ (r1_xboole_0 @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.51  thf('24', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ~ (r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['17', '23'])).
% 0.20/0.51  thf('25', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.20/0.51          | ((k4_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1))
% 0.20/0.51              = (k1_xboole_0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['7', '24'])).
% 0.20/0.51  thf('26', plain,
% 0.20/0.51      ((((k4_xboole_0 @ (k1_tarski @ sk_C_1) @ (k1_tarski @ sk_A))
% 0.20/0.51          = (k1_xboole_0)))
% 0.20/0.51         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.51               (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ sk_D))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['6', '25'])).
% 0.20/0.51  thf(t21_zfmisc_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.20/0.51         ( k1_xboole_0 ) ) =>
% 0.20/0.51       ( ( A ) = ( B ) ) ))).
% 0.20/0.51  thf('27', plain,
% 0.20/0.51      (![X18 : $i, X19 : $i]:
% 0.20/0.51         (((X19) = (X18))
% 0.20/0.51          | ((k4_xboole_0 @ (k1_tarski @ X19) @ (k1_tarski @ X18))
% 0.20/0.51              != (k1_xboole_0)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t21_zfmisc_1])).
% 0.20/0.51  thf('28', plain,
% 0.20/0.51      (((((k1_xboole_0) != (k1_xboole_0)) | ((sk_C_1) = (sk_A))))
% 0.20/0.51         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.51               (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ sk_D))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.51  thf('29', plain,
% 0.20/0.51      ((((sk_C_1) = (sk_A)))
% 0.20/0.51         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.51               (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ sk_D))))),
% 0.20/0.51      inference('simplify', [status(thm)], ['28'])).
% 0.20/0.51  thf('30', plain, ((((sk_A) != (sk_C_1))) <= (~ (((sk_A) = (sk_C_1))))),
% 0.20/0.51      inference('split', [status(esa)], ['0'])).
% 0.20/0.51  thf('31', plain,
% 0.20/0.51      ((((sk_A) != (sk_A)))
% 0.20/0.51         <= (~ (((sk_A) = (sk_C_1))) & 
% 0.20/0.51             ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.51               (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ sk_D))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.51  thf('32', plain,
% 0.20/0.51      ((((sk_A) = (sk_C_1))) | 
% 0.20/0.51       ~
% 0.20/0.51       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.51         (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ sk_D)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['31'])).
% 0.20/0.51  thf('33', plain, ((((sk_A) = (sk_C_1))) <= ((((sk_A) = (sk_C_1))))),
% 0.20/0.51      inference('split', [status(esa)], ['3'])).
% 0.20/0.51  thf('34', plain,
% 0.20/0.51      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.51         (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ sk_D)))
% 0.20/0.51         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.51               (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ sk_D))))),
% 0.20/0.51      inference('split', [status(esa)], ['3'])).
% 0.20/0.51  thf('35', plain,
% 0.20/0.51      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.51         (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_D)))
% 0.20/0.51         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.51               (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ sk_D))) & 
% 0.20/0.51             (((sk_A) = (sk_C_1))))),
% 0.20/0.51      inference('sup+', [status(thm)], ['33', '34'])).
% 0.20/0.51  thf('36', plain,
% 0.20/0.51      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.51         ((r2_hidden @ X15 @ X16)
% 0.20/0.51          | ~ (r2_hidden @ (k4_tarski @ X13 @ X15) @ (k2_zfmisc_1 @ X14 @ X16)))),
% 0.20/0.51      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.20/0.51  thf('37', plain,
% 0.20/0.51      (((r2_hidden @ sk_B @ sk_D))
% 0.20/0.51         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.51               (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ sk_D))) & 
% 0.20/0.51             (((sk_A) = (sk_C_1))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.51  thf('38', plain,
% 0.20/0.51      ((~ (r2_hidden @ sk_B @ sk_D)) <= (~ ((r2_hidden @ sk_B @ sk_D)))),
% 0.20/0.51      inference('split', [status(esa)], ['0'])).
% 0.20/0.51  thf('39', plain,
% 0.20/0.51      (~
% 0.20/0.51       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.51         (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ sk_D))) | 
% 0.20/0.51       ~ (((sk_A) = (sk_C_1))) | ((r2_hidden @ sk_B @ sk_D))),
% 0.20/0.51      inference('sup-', [status(thm)], ['37', '38'])).
% 0.20/0.51  thf('40', plain,
% 0.20/0.51      (~
% 0.20/0.51       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.51         (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ sk_D)))),
% 0.20/0.51      inference('sat_resolution*', [status(thm)], ['2', '32', '39'])).
% 0.20/0.51  thf('41', plain,
% 0.20/0.51      (~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.51          (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ sk_D))),
% 0.20/0.51      inference('simpl_trail', [status(thm)], ['1', '40'])).
% 0.20/0.51  thf('42', plain, ((((sk_A) = (sk_C_1))) <= ((((sk_A) = (sk_C_1))))),
% 0.20/0.51      inference('split', [status(esa)], ['3'])).
% 0.20/0.51  thf('43', plain,
% 0.20/0.51      ((((sk_A) = (sk_C_1))) | 
% 0.20/0.51       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.51         (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ sk_D)))),
% 0.20/0.51      inference('split', [status(esa)], ['3'])).
% 0.20/0.51  thf('44', plain, ((((sk_A) = (sk_C_1)))),
% 0.20/0.51      inference('sat_resolution*', [status(thm)], ['2', '32', '39', '43'])).
% 0.20/0.51  thf('45', plain, (((sk_A) = (sk_C_1))),
% 0.20/0.51      inference('simpl_trail', [status(thm)], ['42', '44'])).
% 0.20/0.51  thf('46', plain,
% 0.20/0.51      (~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.51          (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_D))),
% 0.20/0.51      inference('demod', [status(thm)], ['41', '45'])).
% 0.20/0.51  thf('47', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.20/0.51      inference('simplify', [status(thm)], ['20'])).
% 0.20/0.51  thf('48', plain,
% 0.20/0.51      (((r2_hidden @ sk_B @ sk_D)
% 0.20/0.51        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.51           (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ sk_D)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('49', plain,
% 0.20/0.51      (((r2_hidden @ sk_B @ sk_D)) <= (((r2_hidden @ sk_B @ sk_D)))),
% 0.20/0.51      inference('split', [status(esa)], ['48'])).
% 0.20/0.51  thf('50', plain,
% 0.20/0.51      (((r2_hidden @ sk_B @ sk_D)) | 
% 0.20/0.51       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.51         (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ sk_D)))),
% 0.20/0.51      inference('split', [status(esa)], ['48'])).
% 0.20/0.51  thf('51', plain, (((r2_hidden @ sk_B @ sk_D))),
% 0.20/0.51      inference('sat_resolution*', [status(thm)], ['2', '32', '39', '50'])).
% 0.20/0.51  thf('52', plain, ((r2_hidden @ sk_B @ sk_D)),
% 0.20/0.51      inference('simpl_trail', [status(thm)], ['49', '51'])).
% 0.20/0.51  thf('53', plain,
% 0.20/0.51      (![X13 : $i, X14 : $i, X15 : $i, X17 : $i]:
% 0.20/0.51         ((r2_hidden @ (k4_tarski @ X13 @ X15) @ (k2_zfmisc_1 @ X14 @ X17))
% 0.20/0.51          | ~ (r2_hidden @ X15 @ X17)
% 0.20/0.51          | ~ (r2_hidden @ X13 @ X14))),
% 0.20/0.51      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.20/0.51  thf('54', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X1 @ X0)
% 0.20/0.51          | (r2_hidden @ (k4_tarski @ X1 @ sk_B) @ (k2_zfmisc_1 @ X0 @ sk_D)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['52', '53'])).
% 0.20/0.51  thf('55', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (r2_hidden @ (k4_tarski @ X0 @ sk_B) @ 
% 0.20/0.51          (k2_zfmisc_1 @ (k1_tarski @ X0) @ sk_D))),
% 0.20/0.51      inference('sup-', [status(thm)], ['47', '54'])).
% 0.20/0.51  thf('56', plain, ($false), inference('demod', [status(thm)], ['46', '55'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.20/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
