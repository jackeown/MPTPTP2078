%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2z9xlyZf8d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:59 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 126 expanded)
%              Number of leaves         :   18 (  41 expanded)
%              Depth                    :   14
%              Number of atoms          :  533 ( 992 expanded)
%              Number of equality atoms :   19 (  22 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_ordinal1_type,type,(
    v2_ordinal1: $i > $o )).

thf(v1_ordinal1_type,type,(
    v1_ordinal1: $i > $o )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(t34_ordinal1,conjecture,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
          <=> ( r1_ordinal1 @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v3_ordinal1 @ A )
       => ! [B: $i] :
            ( ( v3_ordinal1 @ B )
           => ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
            <=> ( r1_ordinal1 @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t34_ordinal1])).

thf('0',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf(connectedness_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
        | ( r1_ordinal1 @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v3_ordinal1 @ X12 )
      | ~ ( v3_ordinal1 @ X13 )
      | ( r1_ordinal1 @ X12 @ X13 )
      | ( r1_ordinal1 @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[connectedness_r1_ordinal1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ X0 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(eq_fact,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v3_ordinal1 @ X12 )
      | ~ ( v3_ordinal1 @ X13 )
      | ( r1_ordinal1 @ X12 @ X13 )
      | ( r1_ordinal1 @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[connectedness_r1_ordinal1])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v3_ordinal1 @ X15 )
      | ~ ( v3_ordinal1 @ X16 )
      | ( r1_tarski @ X15 @ X16 )
      | ~ ( r1_ordinal1 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('10',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ~ ( v3_ordinal1 @ sk_B )
      | ( r1_tarski @ sk_B @ sk_A ) )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('14',plain,(
    ! [X8: $i,X10: $i] :
      ( ( r2_xboole_0 @ X8 @ X10 )
      | ( X8 = X10 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('15',plain,
    ( ( ( sk_B = sk_A )
      | ( r2_xboole_0 @ sk_B @ sk_A ) )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t21_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v1_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_xboole_0 @ A @ B )
           => ( r2_hidden @ A @ B ) ) ) ) )).

thf('16',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v3_ordinal1 @ X20 )
      | ( r2_hidden @ X21 @ X20 )
      | ~ ( r2_xboole_0 @ X21 @ X20 )
      | ~ ( v1_ordinal1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t21_ordinal1])).

thf('17',plain,
    ( ( ( sk_B = sk_A )
      | ~ ( v1_ordinal1 @ sk_B )
      | ( r2_hidden @ sk_B @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( ( v1_ordinal1 @ A )
        & ( v2_ordinal1 @ A ) ) ) )).

thf('19',plain,(
    ! [X11: $i] :
      ( ( v1_ordinal1 @ X11 )
      | ~ ( v3_ordinal1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc1_ordinal1])).

thf('20',plain,(
    v1_ordinal1 @ sk_B ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( ( sk_B = sk_A )
      | ( r2_hidden @ sk_B @ sk_A ) )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['17','20','21'])).

thf('23',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['23'])).

thf(t13_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
    <=> ( ( r2_hidden @ A @ B )
        | ( A = B ) ) ) )).

thf('25',plain,(
    ! [X17: $i,X18: $i] :
      ( ( X18 = X17 )
      | ( r2_hidden @ X18 @ X17 )
      | ~ ( r2_hidden @ X18 @ ( k1_ordinal1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('26',plain,
    ( ( ( r2_hidden @ sk_A @ sk_B )
      | ( sk_A = sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(antisymmetry_r2_hidden,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ~ ( r2_hidden @ B @ A ) ) )).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('28',plain,
    ( ( ( sk_A = sk_B )
      | ~ ( r2_hidden @ sk_B @ sk_A ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( ( sk_B = sk_A )
      | ( sk_A = sk_B ) )
   <= ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
      & ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['22','28'])).

thf('30',plain,
    ( ( sk_B = sk_A )
   <= ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
      & ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('32',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_A )
   <= ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
      & ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
   <= ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
      & ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['4','32'])).

thf('34',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['23'])).

thf('37',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['23'])).

thf('38',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v3_ordinal1 @ X15 )
      | ~ ( v3_ordinal1 @ X16 )
      | ( r1_tarski @ X15 @ X16 )
      | ~ ( r1_ordinal1 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('39',plain,
    ( ( ( r1_tarski @ sk_A @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,(
    ! [X8: $i,X10: $i] :
      ( ( r2_xboole_0 @ X8 @ X10 )
      | ( X8 = X10 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('44',plain,
    ( ( ( sk_A = sk_B )
      | ( r2_xboole_0 @ sk_A @ sk_B ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v3_ordinal1 @ X20 )
      | ( r2_hidden @ X21 @ X20 )
      | ~ ( r2_xboole_0 @ X21 @ X20 )
      | ~ ( v1_ordinal1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t21_ordinal1])).

thf('46',plain,
    ( ( ( sk_A = sk_B )
      | ~ ( v1_ordinal1 @ sk_A )
      | ( r2_hidden @ sk_A @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X11: $i] :
      ( ( v1_ordinal1 @ X11 )
      | ~ ( v3_ordinal1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc1_ordinal1])).

thf('49',plain,(
    v1_ordinal1 @ sk_A ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( ( sk_A = sk_B )
      | ( r2_hidden @ sk_A @ sk_B ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['46','49','50'])).

thf('52',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r2_hidden @ X18 @ ( k1_ordinal1 @ X19 ) )
      | ~ ( r2_hidden @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('53',plain,
    ( ( ( sk_A = sk_B )
      | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('55',plain,
    ( ( sk_A = sk_B )
   <= ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
      & ( r1_ordinal1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('57',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
      & ( r1_ordinal1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r2_hidden @ X18 @ ( k1_ordinal1 @ X19 ) )
      | ( X18 != X19 ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('59',plain,(
    ! [X19: $i] :
      ( r2_hidden @ X19 @ ( k1_ordinal1 @ X19 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['57','59'])).

thf('61',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','35','36','60'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2z9xlyZf8d
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:52:54 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.47/0.66  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.47/0.66  % Solved by: fo/fo7.sh
% 0.47/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.66  % done 228 iterations in 0.177s
% 0.47/0.66  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.47/0.66  % SZS output start Refutation
% 0.47/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.47/0.66  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.47/0.66  thf(sk_B_type, type, sk_B: $i).
% 0.47/0.66  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.47/0.66  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.47/0.66  thf(v2_ordinal1_type, type, v2_ordinal1: $i > $o).
% 0.47/0.66  thf(v1_ordinal1_type, type, v1_ordinal1: $i > $o).
% 0.47/0.66  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.47/0.66  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.47/0.66  thf(t34_ordinal1, conjecture,
% 0.47/0.66    (![A:$i]:
% 0.47/0.66     ( ( v3_ordinal1 @ A ) =>
% 0.47/0.66       ( ![B:$i]:
% 0.47/0.66         ( ( v3_ordinal1 @ B ) =>
% 0.47/0.66           ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.47/0.66             ( r1_ordinal1 @ A @ B ) ) ) ) ))).
% 0.47/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.66    (~( ![A:$i]:
% 0.47/0.66        ( ( v3_ordinal1 @ A ) =>
% 0.47/0.66          ( ![B:$i]:
% 0.47/0.66            ( ( v3_ordinal1 @ B ) =>
% 0.47/0.66              ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.47/0.66                ( r1_ordinal1 @ A @ B ) ) ) ) ) )),
% 0.47/0.66    inference('cnf.neg', [status(esa)], [t34_ordinal1])).
% 0.47/0.66  thf('0', plain,
% 0.47/0.66      ((~ (r1_ordinal1 @ sk_A @ sk_B)
% 0.47/0.66        | ~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('1', plain,
% 0.47/0.66      (~ ((r1_ordinal1 @ sk_A @ sk_B)) | 
% 0.47/0.66       ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.47/0.66      inference('split', [status(esa)], ['0'])).
% 0.47/0.66  thf(connectedness_r1_ordinal1, axiom,
% 0.47/0.66    (![A:$i,B:$i]:
% 0.47/0.66     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.47/0.66       ( ( r1_ordinal1 @ A @ B ) | ( r1_ordinal1 @ B @ A ) ) ))).
% 0.47/0.66  thf('2', plain,
% 0.47/0.66      (![X12 : $i, X13 : $i]:
% 0.47/0.66         (~ (v3_ordinal1 @ X12)
% 0.47/0.66          | ~ (v3_ordinal1 @ X13)
% 0.47/0.66          | (r1_ordinal1 @ X12 @ X13)
% 0.47/0.66          | (r1_ordinal1 @ X13 @ X12))),
% 0.47/0.66      inference('cnf', [status(esa)], [connectedness_r1_ordinal1])).
% 0.47/0.66  thf('3', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         ((r1_ordinal1 @ X0 @ X0) | ~ (v3_ordinal1 @ X0) | ~ (v3_ordinal1 @ X0))),
% 0.47/0.66      inference('eq_fact', [status(thm)], ['2'])).
% 0.47/0.66  thf('4', plain,
% 0.47/0.66      (![X0 : $i]: (~ (v3_ordinal1 @ X0) | (r1_ordinal1 @ X0 @ X0))),
% 0.47/0.66      inference('simplify', [status(thm)], ['3'])).
% 0.47/0.66  thf('5', plain,
% 0.47/0.66      (![X12 : $i, X13 : $i]:
% 0.47/0.66         (~ (v3_ordinal1 @ X12)
% 0.47/0.66          | ~ (v3_ordinal1 @ X13)
% 0.47/0.66          | (r1_ordinal1 @ X12 @ X13)
% 0.47/0.66          | (r1_ordinal1 @ X13 @ X12))),
% 0.47/0.66      inference('cnf', [status(esa)], [connectedness_r1_ordinal1])).
% 0.47/0.66  thf(redefinition_r1_ordinal1, axiom,
% 0.47/0.66    (![A:$i,B:$i]:
% 0.47/0.66     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.47/0.66       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 0.47/0.66  thf('6', plain,
% 0.47/0.66      (![X15 : $i, X16 : $i]:
% 0.47/0.66         (~ (v3_ordinal1 @ X15)
% 0.47/0.66          | ~ (v3_ordinal1 @ X16)
% 0.47/0.66          | (r1_tarski @ X15 @ X16)
% 0.47/0.66          | ~ (r1_ordinal1 @ X15 @ X16))),
% 0.47/0.66      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.47/0.66  thf('7', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         ((r1_ordinal1 @ X0 @ X1)
% 0.47/0.66          | ~ (v3_ordinal1 @ X0)
% 0.47/0.66          | ~ (v3_ordinal1 @ X1)
% 0.47/0.66          | (r1_tarski @ X1 @ X0)
% 0.47/0.66          | ~ (v3_ordinal1 @ X0)
% 0.47/0.66          | ~ (v3_ordinal1 @ X1))),
% 0.47/0.66      inference('sup-', [status(thm)], ['5', '6'])).
% 0.47/0.66  thf('8', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         ((r1_tarski @ X1 @ X0)
% 0.47/0.66          | ~ (v3_ordinal1 @ X1)
% 0.47/0.66          | ~ (v3_ordinal1 @ X0)
% 0.47/0.66          | (r1_ordinal1 @ X0 @ X1))),
% 0.47/0.66      inference('simplify', [status(thm)], ['7'])).
% 0.47/0.66  thf('9', plain,
% 0.47/0.66      ((~ (r1_ordinal1 @ sk_A @ sk_B)) <= (~ ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.47/0.66      inference('split', [status(esa)], ['0'])).
% 0.47/0.66  thf('10', plain,
% 0.47/0.66      (((~ (v3_ordinal1 @ sk_A)
% 0.47/0.66         | ~ (v3_ordinal1 @ sk_B)
% 0.47/0.66         | (r1_tarski @ sk_B @ sk_A))) <= (~ ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['8', '9'])).
% 0.47/0.66  thf('11', plain, ((v3_ordinal1 @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('12', plain, ((v3_ordinal1 @ sk_B)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('13', plain,
% 0.47/0.66      (((r1_tarski @ sk_B @ sk_A)) <= (~ ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.47/0.66      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.47/0.66  thf(d8_xboole_0, axiom,
% 0.47/0.66    (![A:$i,B:$i]:
% 0.47/0.66     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.47/0.66       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.47/0.66  thf('14', plain,
% 0.47/0.66      (![X8 : $i, X10 : $i]:
% 0.47/0.66         ((r2_xboole_0 @ X8 @ X10) | ((X8) = (X10)) | ~ (r1_tarski @ X8 @ X10))),
% 0.47/0.66      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.47/0.66  thf('15', plain,
% 0.47/0.66      (((((sk_B) = (sk_A)) | (r2_xboole_0 @ sk_B @ sk_A)))
% 0.47/0.66         <= (~ ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['13', '14'])).
% 0.47/0.66  thf(t21_ordinal1, axiom,
% 0.47/0.66    (![A:$i]:
% 0.47/0.66     ( ( v1_ordinal1 @ A ) =>
% 0.47/0.66       ( ![B:$i]:
% 0.47/0.66         ( ( v3_ordinal1 @ B ) =>
% 0.47/0.66           ( ( r2_xboole_0 @ A @ B ) => ( r2_hidden @ A @ B ) ) ) ) ))).
% 0.47/0.66  thf('16', plain,
% 0.47/0.66      (![X20 : $i, X21 : $i]:
% 0.47/0.66         (~ (v3_ordinal1 @ X20)
% 0.47/0.66          | (r2_hidden @ X21 @ X20)
% 0.47/0.66          | ~ (r2_xboole_0 @ X21 @ X20)
% 0.47/0.66          | ~ (v1_ordinal1 @ X21))),
% 0.47/0.66      inference('cnf', [status(esa)], [t21_ordinal1])).
% 0.47/0.66  thf('17', plain,
% 0.47/0.66      (((((sk_B) = (sk_A))
% 0.47/0.66         | ~ (v1_ordinal1 @ sk_B)
% 0.47/0.66         | (r2_hidden @ sk_B @ sk_A)
% 0.47/0.66         | ~ (v3_ordinal1 @ sk_A))) <= (~ ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['15', '16'])).
% 0.47/0.66  thf('18', plain, ((v3_ordinal1 @ sk_B)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf(cc1_ordinal1, axiom,
% 0.47/0.66    (![A:$i]:
% 0.47/0.66     ( ( v3_ordinal1 @ A ) => ( ( v1_ordinal1 @ A ) & ( v2_ordinal1 @ A ) ) ))).
% 0.47/0.66  thf('19', plain,
% 0.47/0.66      (![X11 : $i]: ((v1_ordinal1 @ X11) | ~ (v3_ordinal1 @ X11))),
% 0.47/0.66      inference('cnf', [status(esa)], [cc1_ordinal1])).
% 0.47/0.66  thf('20', plain, ((v1_ordinal1 @ sk_B)),
% 0.47/0.66      inference('sup-', [status(thm)], ['18', '19'])).
% 0.47/0.66  thf('21', plain, ((v3_ordinal1 @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('22', plain,
% 0.47/0.66      (((((sk_B) = (sk_A)) | (r2_hidden @ sk_B @ sk_A)))
% 0.47/0.66         <= (~ ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.47/0.66      inference('demod', [status(thm)], ['17', '20', '21'])).
% 0.47/0.66  thf('23', plain,
% 0.47/0.66      (((r1_ordinal1 @ sk_A @ sk_B) | (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('24', plain,
% 0.47/0.66      (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 0.47/0.66         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.47/0.66      inference('split', [status(esa)], ['23'])).
% 0.47/0.66  thf(t13_ordinal1, axiom,
% 0.47/0.66    (![A:$i,B:$i]:
% 0.47/0.66     ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.47/0.66       ( ( r2_hidden @ A @ B ) | ( ( A ) = ( B ) ) ) ))).
% 0.47/0.66  thf('25', plain,
% 0.47/0.66      (![X17 : $i, X18 : $i]:
% 0.47/0.66         (((X18) = (X17))
% 0.47/0.66          | (r2_hidden @ X18 @ X17)
% 0.47/0.66          | ~ (r2_hidden @ X18 @ (k1_ordinal1 @ X17)))),
% 0.47/0.66      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.47/0.66  thf('26', plain,
% 0.47/0.66      ((((r2_hidden @ sk_A @ sk_B) | ((sk_A) = (sk_B))))
% 0.47/0.66         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.47/0.66      inference('sup-', [status(thm)], ['24', '25'])).
% 0.47/0.66  thf(antisymmetry_r2_hidden, axiom,
% 0.47/0.66    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( ~( r2_hidden @ B @ A ) ) ))).
% 0.47/0.66  thf('27', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 0.47/0.66      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 0.47/0.66  thf('28', plain,
% 0.47/0.66      (((((sk_A) = (sk_B)) | ~ (r2_hidden @ sk_B @ sk_A)))
% 0.47/0.66         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.47/0.66      inference('sup-', [status(thm)], ['26', '27'])).
% 0.47/0.66  thf('29', plain,
% 0.47/0.66      (((((sk_B) = (sk_A)) | ((sk_A) = (sk_B))))
% 0.47/0.66         <= (~ ((r1_ordinal1 @ sk_A @ sk_B)) & 
% 0.47/0.66             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.47/0.66      inference('sup-', [status(thm)], ['22', '28'])).
% 0.47/0.66  thf('30', plain,
% 0.47/0.66      ((((sk_B) = (sk_A)))
% 0.47/0.66         <= (~ ((r1_ordinal1 @ sk_A @ sk_B)) & 
% 0.47/0.66             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.47/0.66      inference('simplify', [status(thm)], ['29'])).
% 0.47/0.66  thf('31', plain,
% 0.47/0.66      ((~ (r1_ordinal1 @ sk_A @ sk_B)) <= (~ ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.47/0.66      inference('split', [status(esa)], ['0'])).
% 0.47/0.66  thf('32', plain,
% 0.47/0.66      ((~ (r1_ordinal1 @ sk_A @ sk_A))
% 0.47/0.66         <= (~ ((r1_ordinal1 @ sk_A @ sk_B)) & 
% 0.47/0.66             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.47/0.66      inference('sup-', [status(thm)], ['30', '31'])).
% 0.47/0.66  thf('33', plain,
% 0.47/0.66      ((~ (v3_ordinal1 @ sk_A))
% 0.47/0.66         <= (~ ((r1_ordinal1 @ sk_A @ sk_B)) & 
% 0.47/0.66             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.47/0.66      inference('sup-', [status(thm)], ['4', '32'])).
% 0.47/0.66  thf('34', plain, ((v3_ordinal1 @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('35', plain,
% 0.47/0.66      (((r1_ordinal1 @ sk_A @ sk_B)) | 
% 0.47/0.66       ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.47/0.66      inference('demod', [status(thm)], ['33', '34'])).
% 0.47/0.66  thf('36', plain,
% 0.47/0.66      (((r1_ordinal1 @ sk_A @ sk_B)) | 
% 0.47/0.66       ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.47/0.66      inference('split', [status(esa)], ['23'])).
% 0.47/0.66  thf('37', plain,
% 0.47/0.66      (((r1_ordinal1 @ sk_A @ sk_B)) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.47/0.66      inference('split', [status(esa)], ['23'])).
% 0.47/0.66  thf('38', plain,
% 0.47/0.66      (![X15 : $i, X16 : $i]:
% 0.47/0.66         (~ (v3_ordinal1 @ X15)
% 0.47/0.66          | ~ (v3_ordinal1 @ X16)
% 0.47/0.66          | (r1_tarski @ X15 @ X16)
% 0.47/0.66          | ~ (r1_ordinal1 @ X15 @ X16))),
% 0.47/0.66      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.47/0.66  thf('39', plain,
% 0.47/0.66      ((((r1_tarski @ sk_A @ sk_B)
% 0.47/0.66         | ~ (v3_ordinal1 @ sk_B)
% 0.47/0.66         | ~ (v3_ordinal1 @ sk_A))) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['37', '38'])).
% 0.47/0.66  thf('40', plain, ((v3_ordinal1 @ sk_B)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('41', plain, ((v3_ordinal1 @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('42', plain,
% 0.47/0.66      (((r1_tarski @ sk_A @ sk_B)) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.47/0.66      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.47/0.66  thf('43', plain,
% 0.47/0.66      (![X8 : $i, X10 : $i]:
% 0.47/0.66         ((r2_xboole_0 @ X8 @ X10) | ((X8) = (X10)) | ~ (r1_tarski @ X8 @ X10))),
% 0.47/0.66      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.47/0.66  thf('44', plain,
% 0.47/0.66      (((((sk_A) = (sk_B)) | (r2_xboole_0 @ sk_A @ sk_B)))
% 0.47/0.66         <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['42', '43'])).
% 0.47/0.66  thf('45', plain,
% 0.47/0.66      (![X20 : $i, X21 : $i]:
% 0.47/0.66         (~ (v3_ordinal1 @ X20)
% 0.47/0.66          | (r2_hidden @ X21 @ X20)
% 0.47/0.66          | ~ (r2_xboole_0 @ X21 @ X20)
% 0.47/0.66          | ~ (v1_ordinal1 @ X21))),
% 0.47/0.66      inference('cnf', [status(esa)], [t21_ordinal1])).
% 0.47/0.66  thf('46', plain,
% 0.47/0.66      (((((sk_A) = (sk_B))
% 0.47/0.66         | ~ (v1_ordinal1 @ sk_A)
% 0.47/0.66         | (r2_hidden @ sk_A @ sk_B)
% 0.47/0.66         | ~ (v3_ordinal1 @ sk_B))) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['44', '45'])).
% 0.47/0.66  thf('47', plain, ((v3_ordinal1 @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('48', plain,
% 0.47/0.66      (![X11 : $i]: ((v1_ordinal1 @ X11) | ~ (v3_ordinal1 @ X11))),
% 0.47/0.66      inference('cnf', [status(esa)], [cc1_ordinal1])).
% 0.47/0.66  thf('49', plain, ((v1_ordinal1 @ sk_A)),
% 0.47/0.66      inference('sup-', [status(thm)], ['47', '48'])).
% 0.47/0.66  thf('50', plain, ((v3_ordinal1 @ sk_B)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('51', plain,
% 0.47/0.66      (((((sk_A) = (sk_B)) | (r2_hidden @ sk_A @ sk_B)))
% 0.47/0.66         <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.47/0.66      inference('demod', [status(thm)], ['46', '49', '50'])).
% 0.47/0.66  thf('52', plain,
% 0.47/0.66      (![X18 : $i, X19 : $i]:
% 0.47/0.66         ((r2_hidden @ X18 @ (k1_ordinal1 @ X19)) | ~ (r2_hidden @ X18 @ X19))),
% 0.47/0.66      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.47/0.66  thf('53', plain,
% 0.47/0.66      (((((sk_A) = (sk_B)) | (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))
% 0.47/0.66         <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['51', '52'])).
% 0.47/0.66  thf('54', plain,
% 0.47/0.66      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 0.47/0.66         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.47/0.66      inference('split', [status(esa)], ['0'])).
% 0.47/0.66  thf('55', plain,
% 0.47/0.66      ((((sk_A) = (sk_B)))
% 0.47/0.66         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) & 
% 0.47/0.66             ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['53', '54'])).
% 0.47/0.66  thf('56', plain,
% 0.47/0.66      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 0.47/0.66         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.47/0.66      inference('split', [status(esa)], ['0'])).
% 0.47/0.66  thf('57', plain,
% 0.47/0.66      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_A)))
% 0.47/0.66         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) & 
% 0.47/0.66             ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['55', '56'])).
% 0.47/0.66  thf('58', plain,
% 0.47/0.66      (![X18 : $i, X19 : $i]:
% 0.47/0.66         ((r2_hidden @ X18 @ (k1_ordinal1 @ X19)) | ((X18) != (X19)))),
% 0.47/0.66      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.47/0.66  thf('59', plain, (![X19 : $i]: (r2_hidden @ X19 @ (k1_ordinal1 @ X19))),
% 0.47/0.66      inference('simplify', [status(thm)], ['58'])).
% 0.47/0.66  thf('60', plain,
% 0.47/0.66      (~ ((r1_ordinal1 @ sk_A @ sk_B)) | 
% 0.47/0.66       ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.47/0.66      inference('demod', [status(thm)], ['57', '59'])).
% 0.47/0.66  thf('61', plain, ($false),
% 0.47/0.66      inference('sat_resolution*', [status(thm)], ['1', '35', '36', '60'])).
% 0.47/0.66  
% 0.47/0.66  % SZS output end Refutation
% 0.47/0.66  
% 0.47/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
