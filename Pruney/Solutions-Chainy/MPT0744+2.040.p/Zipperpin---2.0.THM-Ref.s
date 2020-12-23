%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.E5IzCZnZnV

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:05 EST 2020

% Result     : Theorem 0.77s
% Output     : Refutation 0.77s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 121 expanded)
%              Number of leaves         :   16 (  39 expanded)
%              Depth                    :   13
%              Number of atoms          :  480 ( 955 expanded)
%              Number of equality atoms :   14 (  17 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_ordinal1_type,type,(
    v2_ordinal1: $i > $o )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_ordinal1_type,type,(
    v1_ordinal1: $i > $o )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

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
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B_1 )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B_1 )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ( X6 != X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('3',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['2'])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X66: $i,X67: $i] :
      ( ~ ( v3_ordinal1 @ X66 )
      | ~ ( v3_ordinal1 @ X67 )
      | ( r1_ordinal1 @ X66 @ X67 )
      | ~ ( r1_tarski @ X66 @ X67 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ X0 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B_1 )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['7'])).

thf(t13_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
    <=> ( ( r2_hidden @ A @ B )
        | ( A = B ) ) ) )).

thf('9',plain,(
    ! [X68: $i,X69: $i] :
      ( ( X69 = X68 )
      | ( r2_hidden @ X69 @ X68 )
      | ~ ( r2_hidden @ X69 @ ( k1_ordinal1 @ X68 ) ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('10',plain,
    ( ( ( r2_hidden @ sk_A @ sk_B_1 )
      | ( sk_A = sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(d2_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v1_ordinal1 @ A )
    <=> ! [B: $i] :
          ( ( r2_hidden @ B @ A )
         => ( r1_tarski @ B @ A ) ) ) )).

thf('11',plain,(
    ! [X63: $i,X64: $i] :
      ( ~ ( r2_hidden @ X63 @ X64 )
      | ( r1_tarski @ X63 @ X64 )
      | ~ ( v1_ordinal1 @ X64 ) ) ),
    inference(cnf,[status(esa)],[d2_ordinal1])).

thf('12',plain,
    ( ( ( sk_A = sk_B_1 )
      | ~ ( v1_ordinal1 @ sk_B_1 )
      | ( r1_tarski @ sk_A @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( ( v1_ordinal1 @ A )
        & ( v2_ordinal1 @ A ) ) ) )).

thf('14',plain,(
    ! [X61: $i] :
      ( ( v1_ordinal1 @ X61 )
      | ~ ( v3_ordinal1 @ X61 ) ) ),
    inference(cnf,[status(esa)],[cc1_ordinal1])).

thf('15',plain,(
    v1_ordinal1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( ( sk_A = sk_B_1 )
      | ( r1_tarski @ sk_A @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X66: $i,X67: $i] :
      ( ~ ( v3_ordinal1 @ X66 )
      | ~ ( v3_ordinal1 @ X67 )
      | ( r1_ordinal1 @ X66 @ X67 )
      | ~ ( r1_tarski @ X66 @ X67 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('18',plain,
    ( ( ( sk_A = sk_B_1 )
      | ( r1_ordinal1 @ sk_A @ sk_B_1 )
      | ~ ( v3_ordinal1 @ sk_B_1 )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( ( sk_A = sk_B_1 )
      | ( r1_ordinal1 @ sk_A @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B_1 )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('23',plain,
    ( ( sk_A = sk_B_1 )
   <= ( ~ ( r1_ordinal1 @ sk_A @ sk_B_1 )
      & ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B_1 )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('25',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_A )
   <= ( ~ ( r1_ordinal1 @ sk_A @ sk_B_1 )
      & ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
   <= ( ~ ( r1_ordinal1 @ sk_A @ sk_B_1 )
      & ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['6','25'])).

thf('27',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B_1 )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B_1 )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['7'])).

thf(t26_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r1_ordinal1 @ A @ B )
            | ( r2_hidden @ B @ A ) ) ) ) )).

thf('30',plain,(
    ! [X71: $i,X72: $i] :
      ( ~ ( v3_ordinal1 @ X71 )
      | ( r1_ordinal1 @ X72 @ X71 )
      | ( r2_hidden @ X71 @ X72 )
      | ~ ( v3_ordinal1 @ X72 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('31',plain,(
    ! [X69: $i,X70: $i] :
      ( ( r2_hidden @ X69 @ ( k1_ordinal1 @ X70 ) )
      | ~ ( r2_hidden @ X69 @ X70 ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('34',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( r1_ordinal1 @ sk_B_1 @ sk_A )
      | ~ ( v3_ordinal1 @ sk_B_1 ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( r1_ordinal1 @ sk_B_1 @ sk_A )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,(
    ! [X66: $i,X67: $i] :
      ( ~ ( v3_ordinal1 @ X66 )
      | ~ ( v3_ordinal1 @ X67 )
      | ( r1_tarski @ X66 @ X67 )
      | ~ ( r1_ordinal1 @ X66 @ X67 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('39',plain,
    ( ( ( r1_tarski @ sk_B_1 @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A )
      | ~ ( v3_ordinal1 @ sk_B_1 ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( r1_tarski @ sk_B_1 @ sk_A )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B_1 )
   <= ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['7'])).

thf('44',plain,(
    ! [X66: $i,X67: $i] :
      ( ~ ( v3_ordinal1 @ X66 )
      | ~ ( v3_ordinal1 @ X67 )
      | ( r1_tarski @ X66 @ X67 )
      | ~ ( r1_ordinal1 @ X66 @ X67 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('45',plain,
    ( ( ( r1_tarski @ sk_A @ sk_B_1 )
      | ~ ( v3_ordinal1 @ sk_B_1 )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( r1_tarski @ sk_A @ sk_B_1 )
   <= ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,(
    ! [X6: $i,X8: $i] :
      ( ( X6 = X8 )
      | ~ ( r1_tarski @ X8 @ X6 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('50',plain,
    ( ( ~ ( r1_tarski @ sk_B_1 @ sk_A )
      | ( sk_B_1 = sk_A ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( sk_B_1 = sk_A )
   <= ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) )
      & ( r1_ordinal1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['42','50'])).

thf('52',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('53',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) )
      & ( r1_ordinal1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X69: $i,X70: $i] :
      ( ( r2_hidden @ X69 @ ( k1_ordinal1 @ X70 ) )
      | ( X69 != X70 ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('55',plain,(
    ! [X70: $i] :
      ( r2_hidden @ X70 @ ( k1_ordinal1 @ X70 ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B_1 )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['53','55'])).

thf('57',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','28','29','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.E5IzCZnZnV
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:37:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.77/0.94  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.77/0.94  % Solved by: fo/fo7.sh
% 0.77/0.94  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.77/0.94  % done 459 iterations in 0.471s
% 0.77/0.94  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.77/0.94  % SZS output start Refutation
% 0.77/0.94  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.77/0.94  thf(v2_ordinal1_type, type, v2_ordinal1: $i > $o).
% 0.77/0.94  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.77/0.94  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.77/0.94  thf(sk_A_type, type, sk_A: $i).
% 0.77/0.94  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.77/0.94  thf(v1_ordinal1_type, type, v1_ordinal1: $i > $o).
% 0.77/0.94  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.77/0.94  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.77/0.94  thf(t34_ordinal1, conjecture,
% 0.77/0.94    (![A:$i]:
% 0.77/0.94     ( ( v3_ordinal1 @ A ) =>
% 0.77/0.94       ( ![B:$i]:
% 0.77/0.94         ( ( v3_ordinal1 @ B ) =>
% 0.77/0.94           ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.77/0.94             ( r1_ordinal1 @ A @ B ) ) ) ) ))).
% 0.77/0.94  thf(zf_stmt_0, negated_conjecture,
% 0.77/0.94    (~( ![A:$i]:
% 0.77/0.94        ( ( v3_ordinal1 @ A ) =>
% 0.77/0.94          ( ![B:$i]:
% 0.77/0.94            ( ( v3_ordinal1 @ B ) =>
% 0.77/0.94              ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.77/0.94                ( r1_ordinal1 @ A @ B ) ) ) ) ) )),
% 0.77/0.94    inference('cnf.neg', [status(esa)], [t34_ordinal1])).
% 0.77/0.94  thf('0', plain,
% 0.77/0.94      ((~ (r1_ordinal1 @ sk_A @ sk_B_1)
% 0.77/0.94        | ~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('1', plain,
% 0.77/0.94      (~ ((r1_ordinal1 @ sk_A @ sk_B_1)) | 
% 0.77/0.94       ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))),
% 0.77/0.94      inference('split', [status(esa)], ['0'])).
% 0.77/0.94  thf(d10_xboole_0, axiom,
% 0.77/0.94    (![A:$i,B:$i]:
% 0.77/0.94     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.77/0.94  thf('2', plain,
% 0.77/0.94      (![X6 : $i, X7 : $i]: ((r1_tarski @ X6 @ X7) | ((X6) != (X7)))),
% 0.77/0.94      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.77/0.94  thf('3', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 0.77/0.94      inference('simplify', [status(thm)], ['2'])).
% 0.77/0.94  thf(redefinition_r1_ordinal1, axiom,
% 0.77/0.94    (![A:$i,B:$i]:
% 0.77/0.94     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.77/0.94       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 0.77/0.94  thf('4', plain,
% 0.77/0.94      (![X66 : $i, X67 : $i]:
% 0.77/0.94         (~ (v3_ordinal1 @ X66)
% 0.77/0.94          | ~ (v3_ordinal1 @ X67)
% 0.77/0.94          | (r1_ordinal1 @ X66 @ X67)
% 0.77/0.94          | ~ (r1_tarski @ X66 @ X67))),
% 0.77/0.94      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.77/0.94  thf('5', plain,
% 0.77/0.94      (![X0 : $i]:
% 0.77/0.94         ((r1_ordinal1 @ X0 @ X0) | ~ (v3_ordinal1 @ X0) | ~ (v3_ordinal1 @ X0))),
% 0.77/0.94      inference('sup-', [status(thm)], ['3', '4'])).
% 0.77/0.94  thf('6', plain,
% 0.77/0.94      (![X0 : $i]: (~ (v3_ordinal1 @ X0) | (r1_ordinal1 @ X0 @ X0))),
% 0.77/0.94      inference('simplify', [status(thm)], ['5'])).
% 0.77/0.94  thf('7', plain,
% 0.77/0.94      (((r1_ordinal1 @ sk_A @ sk_B_1)
% 0.77/0.94        | (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('8', plain,
% 0.77/0.94      (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))
% 0.77/0.94         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.77/0.94      inference('split', [status(esa)], ['7'])).
% 0.77/0.94  thf(t13_ordinal1, axiom,
% 0.77/0.94    (![A:$i,B:$i]:
% 0.77/0.94     ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.77/0.94       ( ( r2_hidden @ A @ B ) | ( ( A ) = ( B ) ) ) ))).
% 0.77/0.94  thf('9', plain,
% 0.77/0.94      (![X68 : $i, X69 : $i]:
% 0.77/0.94         (((X69) = (X68))
% 0.77/0.94          | (r2_hidden @ X69 @ X68)
% 0.77/0.94          | ~ (r2_hidden @ X69 @ (k1_ordinal1 @ X68)))),
% 0.77/0.94      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.77/0.94  thf('10', plain,
% 0.77/0.94      ((((r2_hidden @ sk_A @ sk_B_1) | ((sk_A) = (sk_B_1))))
% 0.77/0.94         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.77/0.94      inference('sup-', [status(thm)], ['8', '9'])).
% 0.77/0.94  thf(d2_ordinal1, axiom,
% 0.77/0.94    (![A:$i]:
% 0.77/0.94     ( ( v1_ordinal1 @ A ) <=>
% 0.77/0.94       ( ![B:$i]: ( ( r2_hidden @ B @ A ) => ( r1_tarski @ B @ A ) ) ) ))).
% 0.77/0.94  thf('11', plain,
% 0.77/0.94      (![X63 : $i, X64 : $i]:
% 0.77/0.94         (~ (r2_hidden @ X63 @ X64)
% 0.77/0.94          | (r1_tarski @ X63 @ X64)
% 0.77/0.94          | ~ (v1_ordinal1 @ X64))),
% 0.77/0.94      inference('cnf', [status(esa)], [d2_ordinal1])).
% 0.77/0.94  thf('12', plain,
% 0.77/0.94      (((((sk_A) = (sk_B_1))
% 0.77/0.94         | ~ (v1_ordinal1 @ sk_B_1)
% 0.77/0.94         | (r1_tarski @ sk_A @ sk_B_1)))
% 0.77/0.94         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.77/0.94      inference('sup-', [status(thm)], ['10', '11'])).
% 0.77/0.94  thf('13', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf(cc1_ordinal1, axiom,
% 0.77/0.94    (![A:$i]:
% 0.77/0.94     ( ( v3_ordinal1 @ A ) => ( ( v1_ordinal1 @ A ) & ( v2_ordinal1 @ A ) ) ))).
% 0.77/0.94  thf('14', plain,
% 0.77/0.94      (![X61 : $i]: ((v1_ordinal1 @ X61) | ~ (v3_ordinal1 @ X61))),
% 0.77/0.94      inference('cnf', [status(esa)], [cc1_ordinal1])).
% 0.77/0.94  thf('15', plain, ((v1_ordinal1 @ sk_B_1)),
% 0.77/0.94      inference('sup-', [status(thm)], ['13', '14'])).
% 0.77/0.94  thf('16', plain,
% 0.77/0.94      (((((sk_A) = (sk_B_1)) | (r1_tarski @ sk_A @ sk_B_1)))
% 0.77/0.94         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.77/0.94      inference('demod', [status(thm)], ['12', '15'])).
% 0.77/0.94  thf('17', plain,
% 0.77/0.94      (![X66 : $i, X67 : $i]:
% 0.77/0.94         (~ (v3_ordinal1 @ X66)
% 0.77/0.94          | ~ (v3_ordinal1 @ X67)
% 0.77/0.94          | (r1_ordinal1 @ X66 @ X67)
% 0.77/0.94          | ~ (r1_tarski @ X66 @ X67))),
% 0.77/0.94      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.77/0.94  thf('18', plain,
% 0.77/0.94      (((((sk_A) = (sk_B_1))
% 0.77/0.94         | (r1_ordinal1 @ sk_A @ sk_B_1)
% 0.77/0.94         | ~ (v3_ordinal1 @ sk_B_1)
% 0.77/0.94         | ~ (v3_ordinal1 @ sk_A)))
% 0.77/0.94         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.77/0.94      inference('sup-', [status(thm)], ['16', '17'])).
% 0.77/0.94  thf('19', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('20', plain, ((v3_ordinal1 @ sk_A)),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('21', plain,
% 0.77/0.94      (((((sk_A) = (sk_B_1)) | (r1_ordinal1 @ sk_A @ sk_B_1)))
% 0.77/0.94         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.77/0.94      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.77/0.94  thf('22', plain,
% 0.77/0.94      ((~ (r1_ordinal1 @ sk_A @ sk_B_1)) <= (~ ((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 0.77/0.94      inference('split', [status(esa)], ['0'])).
% 0.77/0.94  thf('23', plain,
% 0.77/0.94      ((((sk_A) = (sk_B_1)))
% 0.77/0.94         <= (~ ((r1_ordinal1 @ sk_A @ sk_B_1)) & 
% 0.77/0.94             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.77/0.94      inference('sup-', [status(thm)], ['21', '22'])).
% 0.77/0.94  thf('24', plain,
% 0.77/0.94      ((~ (r1_ordinal1 @ sk_A @ sk_B_1)) <= (~ ((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 0.77/0.94      inference('split', [status(esa)], ['0'])).
% 0.77/0.94  thf('25', plain,
% 0.77/0.94      ((~ (r1_ordinal1 @ sk_A @ sk_A))
% 0.77/0.94         <= (~ ((r1_ordinal1 @ sk_A @ sk_B_1)) & 
% 0.77/0.94             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.77/0.94      inference('sup-', [status(thm)], ['23', '24'])).
% 0.77/0.94  thf('26', plain,
% 0.77/0.94      ((~ (v3_ordinal1 @ sk_A))
% 0.77/0.94         <= (~ ((r1_ordinal1 @ sk_A @ sk_B_1)) & 
% 0.77/0.94             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.77/0.94      inference('sup-', [status(thm)], ['6', '25'])).
% 0.77/0.94  thf('27', plain, ((v3_ordinal1 @ sk_A)),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('28', plain,
% 0.77/0.94      (((r1_ordinal1 @ sk_A @ sk_B_1)) | 
% 0.77/0.94       ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))),
% 0.77/0.94      inference('demod', [status(thm)], ['26', '27'])).
% 0.77/0.94  thf('29', plain,
% 0.77/0.94      (((r1_ordinal1 @ sk_A @ sk_B_1)) | 
% 0.77/0.94       ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))),
% 0.77/0.94      inference('split', [status(esa)], ['7'])).
% 0.77/0.94  thf(t26_ordinal1, axiom,
% 0.77/0.94    (![A:$i]:
% 0.77/0.94     ( ( v3_ordinal1 @ A ) =>
% 0.77/0.94       ( ![B:$i]:
% 0.77/0.94         ( ( v3_ordinal1 @ B ) =>
% 0.77/0.94           ( ( r1_ordinal1 @ A @ B ) | ( r2_hidden @ B @ A ) ) ) ) ))).
% 0.77/0.94  thf('30', plain,
% 0.77/0.94      (![X71 : $i, X72 : $i]:
% 0.77/0.94         (~ (v3_ordinal1 @ X71)
% 0.77/0.94          | (r1_ordinal1 @ X72 @ X71)
% 0.77/0.94          | (r2_hidden @ X71 @ X72)
% 0.77/0.94          | ~ (v3_ordinal1 @ X72))),
% 0.77/0.94      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.77/0.94  thf('31', plain,
% 0.77/0.94      (![X69 : $i, X70 : $i]:
% 0.77/0.94         ((r2_hidden @ X69 @ (k1_ordinal1 @ X70)) | ~ (r2_hidden @ X69 @ X70))),
% 0.77/0.94      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.77/0.94  thf('32', plain,
% 0.77/0.94      (![X0 : $i, X1 : $i]:
% 0.77/0.94         (~ (v3_ordinal1 @ X0)
% 0.77/0.94          | (r1_ordinal1 @ X0 @ X1)
% 0.77/0.94          | ~ (v3_ordinal1 @ X1)
% 0.77/0.94          | (r2_hidden @ X1 @ (k1_ordinal1 @ X0)))),
% 0.77/0.94      inference('sup-', [status(thm)], ['30', '31'])).
% 0.77/0.94  thf('33', plain,
% 0.77/0.94      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))
% 0.77/0.94         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.77/0.94      inference('split', [status(esa)], ['0'])).
% 0.77/0.94  thf('34', plain,
% 0.77/0.94      (((~ (v3_ordinal1 @ sk_A)
% 0.77/0.94         | (r1_ordinal1 @ sk_B_1 @ sk_A)
% 0.77/0.94         | ~ (v3_ordinal1 @ sk_B_1)))
% 0.77/0.94         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.77/0.94      inference('sup-', [status(thm)], ['32', '33'])).
% 0.77/0.94  thf('35', plain, ((v3_ordinal1 @ sk_A)),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('36', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('37', plain,
% 0.77/0.94      (((r1_ordinal1 @ sk_B_1 @ sk_A))
% 0.77/0.94         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.77/0.94      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.77/0.94  thf('38', plain,
% 0.77/0.94      (![X66 : $i, X67 : $i]:
% 0.77/0.94         (~ (v3_ordinal1 @ X66)
% 0.77/0.94          | ~ (v3_ordinal1 @ X67)
% 0.77/0.94          | (r1_tarski @ X66 @ X67)
% 0.77/0.94          | ~ (r1_ordinal1 @ X66 @ X67))),
% 0.77/0.94      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.77/0.94  thf('39', plain,
% 0.77/0.94      ((((r1_tarski @ sk_B_1 @ sk_A)
% 0.77/0.94         | ~ (v3_ordinal1 @ sk_A)
% 0.77/0.94         | ~ (v3_ordinal1 @ sk_B_1)))
% 0.77/0.94         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.77/0.94      inference('sup-', [status(thm)], ['37', '38'])).
% 0.77/0.94  thf('40', plain, ((v3_ordinal1 @ sk_A)),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('41', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('42', plain,
% 0.77/0.94      (((r1_tarski @ sk_B_1 @ sk_A))
% 0.77/0.94         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.77/0.94      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.77/0.94  thf('43', plain,
% 0.77/0.94      (((r1_ordinal1 @ sk_A @ sk_B_1)) <= (((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 0.77/0.94      inference('split', [status(esa)], ['7'])).
% 0.77/0.94  thf('44', plain,
% 0.77/0.94      (![X66 : $i, X67 : $i]:
% 0.77/0.94         (~ (v3_ordinal1 @ X66)
% 0.77/0.94          | ~ (v3_ordinal1 @ X67)
% 0.77/0.94          | (r1_tarski @ X66 @ X67)
% 0.77/0.94          | ~ (r1_ordinal1 @ X66 @ X67))),
% 0.77/0.94      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.77/0.94  thf('45', plain,
% 0.77/0.94      ((((r1_tarski @ sk_A @ sk_B_1)
% 0.77/0.94         | ~ (v3_ordinal1 @ sk_B_1)
% 0.77/0.94         | ~ (v3_ordinal1 @ sk_A))) <= (((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 0.77/0.94      inference('sup-', [status(thm)], ['43', '44'])).
% 0.77/0.94  thf('46', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('47', plain, ((v3_ordinal1 @ sk_A)),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('48', plain,
% 0.77/0.94      (((r1_tarski @ sk_A @ sk_B_1)) <= (((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 0.77/0.94      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.77/0.94  thf('49', plain,
% 0.77/0.94      (![X6 : $i, X8 : $i]:
% 0.77/0.94         (((X6) = (X8)) | ~ (r1_tarski @ X8 @ X6) | ~ (r1_tarski @ X6 @ X8))),
% 0.77/0.94      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.77/0.94  thf('50', plain,
% 0.77/0.94      (((~ (r1_tarski @ sk_B_1 @ sk_A) | ((sk_B_1) = (sk_A))))
% 0.77/0.94         <= (((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 0.77/0.94      inference('sup-', [status(thm)], ['48', '49'])).
% 0.77/0.94  thf('51', plain,
% 0.77/0.94      ((((sk_B_1) = (sk_A)))
% 0.77/0.94         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))) & 
% 0.77/0.94             ((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 0.77/0.94      inference('sup-', [status(thm)], ['42', '50'])).
% 0.77/0.94  thf('52', plain,
% 0.77/0.94      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))
% 0.77/0.94         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.77/0.94      inference('split', [status(esa)], ['0'])).
% 0.77/0.94  thf('53', plain,
% 0.77/0.94      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_A)))
% 0.77/0.94         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))) & 
% 0.77/0.94             ((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 0.77/0.94      inference('sup-', [status(thm)], ['51', '52'])).
% 0.77/0.94  thf('54', plain,
% 0.77/0.94      (![X69 : $i, X70 : $i]:
% 0.77/0.94         ((r2_hidden @ X69 @ (k1_ordinal1 @ X70)) | ((X69) != (X70)))),
% 0.77/0.94      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.77/0.94  thf('55', plain, (![X70 : $i]: (r2_hidden @ X70 @ (k1_ordinal1 @ X70))),
% 0.77/0.94      inference('simplify', [status(thm)], ['54'])).
% 0.77/0.94  thf('56', plain,
% 0.77/0.94      (~ ((r1_ordinal1 @ sk_A @ sk_B_1)) | 
% 0.77/0.94       ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))),
% 0.77/0.94      inference('demod', [status(thm)], ['53', '55'])).
% 0.77/0.94  thf('57', plain, ($false),
% 0.77/0.94      inference('sat_resolution*', [status(thm)], ['1', '28', '29', '56'])).
% 0.77/0.94  
% 0.77/0.94  % SZS output end Refutation
% 0.77/0.94  
% 0.77/0.95  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
