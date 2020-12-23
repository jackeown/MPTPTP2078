%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Srm6PhRKOn

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:59 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 103 expanded)
%              Number of leaves         :   22 (  38 expanded)
%              Depth                    :   15
%              Number of atoms          :  428 ( 725 expanded)
%              Number of equality atoms :   70 ( 124 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(t20_mcart_1,conjecture,(
    ! [A: $i] :
      ( ? [B: $i,C: $i] :
          ( A
          = ( k4_tarski @ B @ C ) )
     => ( ( A
         != ( k1_mcart_1 @ A ) )
        & ( A
         != ( k2_mcart_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ? [B: $i,C: $i] :
            ( A
            = ( k4_tarski @ B @ C ) )
       => ( ( A
           != ( k1_mcart_1 @ A ) )
          & ( A
           != ( k2_mcart_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t20_mcart_1])).

thf('0',plain,
    ( sk_A
    = ( k4_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('1',plain,(
    ! [X31: $i,X33: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X31 @ X33 ) )
      = X33 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('2',plain,
    ( ( k2_mcart_1 @ sk_A )
    = sk_C ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( sk_A
      = ( k2_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ( sk_A = sk_C )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['2','4'])).

thf('6',plain,
    ( sk_A
    = ( k4_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_B @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t35_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
      = ( k1_tarski @ ( k4_tarski @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X23 ) @ ( k1_tarski @ X24 ) )
      = ( k1_tarski @ ( k4_tarski @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t35_zfmisc_1])).

thf(t135_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ A @ B ) )
        | ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ A ) ) )
     => ( A = k1_xboole_0 ) ) )).

thf('9',plain,(
    ! [X16: $i,X17: $i] :
      ( ( X16 = k1_xboole_0 )
      | ~ ( r1_tarski @ X16 @ ( k2_zfmisc_1 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t135_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

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

thf('14',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['11','13'])).

thf(d1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( k1_ordinal1 @ A )
      = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ) )).

thf('15',plain,(
    ! [X25: $i] :
      ( ( k1_ordinal1 @ X25 )
      = ( k2_xboole_0 @ X25 @ ( k1_tarski @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf('16',plain,
    ( ( ( k1_ordinal1 @ sk_A )
      = ( k2_xboole_0 @ sk_A @ k1_xboole_0 ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('17',plain,(
    ! [X3: $i] :
      ( ( k2_xboole_0 @ X3 @ k1_xboole_0 )
      = X3 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('18',plain,
    ( ( ( k1_ordinal1 @ sk_A )
      = sk_A )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( sk_A
    = ( k4_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X31 @ X32 ) )
      = X31 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('21',plain,
    ( ( k1_mcart_1 @ sk_A )
    = sk_B ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('23',plain,
    ( ( sk_A = sk_B )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,
    ( sk_A
    = ( k4_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_A @ sk_C ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X23 ) @ ( k1_tarski @ X24 ) )
      = ( k1_tarski @ ( k4_tarski @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t35_zfmisc_1])).

thf('27',plain,(
    ! [X16: $i,X17: $i] :
      ( ( X16 = k1_xboole_0 )
      | ~ ( r1_tarski @ X16 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t135_zfmisc_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      | ( ( k1_tarski @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('31',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X25: $i] :
      ( ( k1_ordinal1 @ X25 )
      = ( k2_xboole_0 @ X25 @ ( k1_tarski @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf('33',plain,
    ( ( ( k1_ordinal1 @ sk_A )
      = ( k2_xboole_0 @ sk_A @ k1_xboole_0 ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X3: $i] :
      ( ( k2_xboole_0 @ X3 @ k1_xboole_0 )
      = X3 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('35',plain,
    ( ( ( k1_ordinal1 @ sk_A )
      = sk_A )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf(t13_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
    <=> ( ( r2_hidden @ A @ B )
        | ( A = B ) ) ) )).

thf('36',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r2_hidden @ X27 @ ( k1_ordinal1 @ X28 ) )
      | ( X27 != X28 ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('37',plain,(
    ! [X28: $i] :
      ( r2_hidden @ X28 @ ( k1_ordinal1 @ X28 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('38',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( r2_hidden @ X29 @ X30 )
      | ~ ( r1_tarski @ X30 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('39',plain,(
    ! [X0: $i] :
      ~ ( r1_tarski @ ( k1_ordinal1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_A )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','39'])).

thf('41',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('42',plain,(
    sk_A
 != ( k1_mcart_1 @ sk_A ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( sk_A
      = ( k2_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('44',plain,
    ( sk_A
    = ( k2_mcart_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k1_ordinal1 @ sk_A )
    = sk_A ),
    inference(simpl_trail,[status(thm)],['18','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ~ ( r1_tarski @ ( k1_ordinal1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('47',plain,(
    ~ ( r1_tarski @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('49',plain,(
    $false ),
    inference(demod,[status(thm)],['47','48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Srm6PhRKOn
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:09:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.19/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.50  % Solved by: fo/fo7.sh
% 0.19/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.50  % done 98 iterations in 0.043s
% 0.19/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.50  % SZS output start Refutation
% 0.19/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.50  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.19/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.50  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.19/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.50  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.19/0.50  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.19/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.50  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.19/0.50  thf(t20_mcart_1, conjecture,
% 0.19/0.50    (![A:$i]:
% 0.19/0.50     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.19/0.50       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 0.19/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.50    (~( ![A:$i]:
% 0.19/0.50        ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.19/0.50          ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ) )),
% 0.19/0.50    inference('cnf.neg', [status(esa)], [t20_mcart_1])).
% 0.19/0.50  thf('0', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf(t7_mcart_1, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.19/0.50       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.19/0.50  thf('1', plain,
% 0.19/0.50      (![X31 : $i, X33 : $i]: ((k2_mcart_1 @ (k4_tarski @ X31 @ X33)) = (X33))),
% 0.19/0.50      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.19/0.50  thf('2', plain, (((k2_mcart_1 @ sk_A) = (sk_C))),
% 0.19/0.50      inference('sup+', [status(thm)], ['0', '1'])).
% 0.19/0.50  thf('3', plain,
% 0.19/0.50      ((((sk_A) = (k1_mcart_1 @ sk_A)) | ((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('4', plain,
% 0.19/0.50      ((((sk_A) = (k2_mcart_1 @ sk_A))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.19/0.50      inference('split', [status(esa)], ['3'])).
% 0.19/0.50  thf('5', plain, ((((sk_A) = (sk_C))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.19/0.50      inference('sup+', [status(thm)], ['2', '4'])).
% 0.19/0.50  thf('6', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('7', plain,
% 0.19/0.50      ((((sk_A) = (k4_tarski @ sk_B @ sk_A)))
% 0.19/0.50         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.19/0.50      inference('sup+', [status(thm)], ['5', '6'])).
% 0.19/0.50  thf(t35_zfmisc_1, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.19/0.50       ( k1_tarski @ ( k4_tarski @ A @ B ) ) ))).
% 0.19/0.50  thf('8', plain,
% 0.19/0.50      (![X23 : $i, X24 : $i]:
% 0.19/0.50         ((k2_zfmisc_1 @ (k1_tarski @ X23) @ (k1_tarski @ X24))
% 0.19/0.50           = (k1_tarski @ (k4_tarski @ X23 @ X24)))),
% 0.19/0.50      inference('cnf', [status(esa)], [t35_zfmisc_1])).
% 0.19/0.50  thf(t135_zfmisc_1, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ A @ B ) ) | 
% 0.19/0.50         ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.19/0.50       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.19/0.50  thf('9', plain,
% 0.19/0.50      (![X16 : $i, X17 : $i]:
% 0.19/0.50         (((X16) = (k1_xboole_0))
% 0.19/0.50          | ~ (r1_tarski @ X16 @ (k2_zfmisc_1 @ X17 @ X16)))),
% 0.19/0.50      inference('cnf', [status(esa)], [t135_zfmisc_1])).
% 0.19/0.50  thf('10', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         (~ (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 0.19/0.50          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['8', '9'])).
% 0.19/0.50  thf('11', plain,
% 0.19/0.50      (((~ (r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))
% 0.19/0.50         | ((k1_tarski @ sk_A) = (k1_xboole_0))))
% 0.19/0.50         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.19/0.50      inference('sup-', [status(thm)], ['7', '10'])).
% 0.19/0.50  thf(d10_xboole_0, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.19/0.50  thf('12', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.19/0.50      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.19/0.50  thf('13', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.19/0.50      inference('simplify', [status(thm)], ['12'])).
% 0.19/0.50  thf('14', plain,
% 0.19/0.50      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 0.19/0.50         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.19/0.50      inference('demod', [status(thm)], ['11', '13'])).
% 0.19/0.50  thf(d1_ordinal1, axiom,
% 0.19/0.50    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 0.19/0.50  thf('15', plain,
% 0.19/0.50      (![X25 : $i]:
% 0.19/0.50         ((k1_ordinal1 @ X25) = (k2_xboole_0 @ X25 @ (k1_tarski @ X25)))),
% 0.19/0.50      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.19/0.50  thf('16', plain,
% 0.19/0.50      ((((k1_ordinal1 @ sk_A) = (k2_xboole_0 @ sk_A @ k1_xboole_0)))
% 0.19/0.50         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.19/0.50      inference('sup+', [status(thm)], ['14', '15'])).
% 0.19/0.50  thf(t1_boole, axiom,
% 0.19/0.50    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.19/0.50  thf('17', plain, (![X3 : $i]: ((k2_xboole_0 @ X3 @ k1_xboole_0) = (X3))),
% 0.19/0.50      inference('cnf', [status(esa)], [t1_boole])).
% 0.19/0.50  thf('18', plain,
% 0.19/0.50      ((((k1_ordinal1 @ sk_A) = (sk_A))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.19/0.50      inference('demod', [status(thm)], ['16', '17'])).
% 0.19/0.50  thf('19', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('20', plain,
% 0.19/0.50      (![X31 : $i, X32 : $i]: ((k1_mcart_1 @ (k4_tarski @ X31 @ X32)) = (X31))),
% 0.19/0.50      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.19/0.50  thf('21', plain, (((k1_mcart_1 @ sk_A) = (sk_B))),
% 0.19/0.50      inference('sup+', [status(thm)], ['19', '20'])).
% 0.19/0.50  thf('22', plain,
% 0.19/0.50      ((((sk_A) = (k1_mcart_1 @ sk_A))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.19/0.50      inference('split', [status(esa)], ['3'])).
% 0.19/0.50  thf('23', plain, ((((sk_A) = (sk_B))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.19/0.50      inference('sup+', [status(thm)], ['21', '22'])).
% 0.19/0.50  thf('24', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('25', plain,
% 0.19/0.50      ((((sk_A) = (k4_tarski @ sk_A @ sk_C)))
% 0.19/0.50         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.19/0.50      inference('sup+', [status(thm)], ['23', '24'])).
% 0.19/0.50  thf('26', plain,
% 0.19/0.50      (![X23 : $i, X24 : $i]:
% 0.19/0.50         ((k2_zfmisc_1 @ (k1_tarski @ X23) @ (k1_tarski @ X24))
% 0.19/0.50           = (k1_tarski @ (k4_tarski @ X23 @ X24)))),
% 0.19/0.50      inference('cnf', [status(esa)], [t35_zfmisc_1])).
% 0.19/0.50  thf('27', plain,
% 0.19/0.50      (![X16 : $i, X17 : $i]:
% 0.19/0.50         (((X16) = (k1_xboole_0))
% 0.19/0.50          | ~ (r1_tarski @ X16 @ (k2_zfmisc_1 @ X16 @ X17)))),
% 0.19/0.50      inference('cnf', [status(esa)], [t135_zfmisc_1])).
% 0.19/0.50  thf('28', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         (~ (r1_tarski @ (k1_tarski @ X1) @ (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 0.19/0.50          | ((k1_tarski @ X1) = (k1_xboole_0)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['26', '27'])).
% 0.19/0.50  thf('29', plain,
% 0.19/0.50      (((~ (r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))
% 0.19/0.50         | ((k1_tarski @ sk_A) = (k1_xboole_0))))
% 0.19/0.50         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.19/0.50      inference('sup-', [status(thm)], ['25', '28'])).
% 0.19/0.50  thf('30', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.19/0.50      inference('simplify', [status(thm)], ['12'])).
% 0.19/0.50  thf('31', plain,
% 0.19/0.50      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 0.19/0.50         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.19/0.50      inference('demod', [status(thm)], ['29', '30'])).
% 0.19/0.50  thf('32', plain,
% 0.19/0.50      (![X25 : $i]:
% 0.19/0.50         ((k1_ordinal1 @ X25) = (k2_xboole_0 @ X25 @ (k1_tarski @ X25)))),
% 0.19/0.50      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.19/0.50  thf('33', plain,
% 0.19/0.50      ((((k1_ordinal1 @ sk_A) = (k2_xboole_0 @ sk_A @ k1_xboole_0)))
% 0.19/0.50         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.19/0.50      inference('sup+', [status(thm)], ['31', '32'])).
% 0.19/0.50  thf('34', plain, (![X3 : $i]: ((k2_xboole_0 @ X3 @ k1_xboole_0) = (X3))),
% 0.19/0.50      inference('cnf', [status(esa)], [t1_boole])).
% 0.19/0.50  thf('35', plain,
% 0.19/0.50      ((((k1_ordinal1 @ sk_A) = (sk_A))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.19/0.50      inference('demod', [status(thm)], ['33', '34'])).
% 0.19/0.50  thf(t13_ordinal1, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.19/0.50       ( ( r2_hidden @ A @ B ) | ( ( A ) = ( B ) ) ) ))).
% 0.19/0.50  thf('36', plain,
% 0.19/0.50      (![X27 : $i, X28 : $i]:
% 0.19/0.50         ((r2_hidden @ X27 @ (k1_ordinal1 @ X28)) | ((X27) != (X28)))),
% 0.19/0.50      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.19/0.50  thf('37', plain, (![X28 : $i]: (r2_hidden @ X28 @ (k1_ordinal1 @ X28))),
% 0.19/0.50      inference('simplify', [status(thm)], ['36'])).
% 0.19/0.50  thf(t7_ordinal1, axiom,
% 0.19/0.50    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.19/0.50  thf('38', plain,
% 0.19/0.50      (![X29 : $i, X30 : $i]:
% 0.19/0.50         (~ (r2_hidden @ X29 @ X30) | ~ (r1_tarski @ X30 @ X29))),
% 0.19/0.50      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.19/0.50  thf('39', plain, (![X0 : $i]: ~ (r1_tarski @ (k1_ordinal1 @ X0) @ X0)),
% 0.19/0.50      inference('sup-', [status(thm)], ['37', '38'])).
% 0.19/0.50  thf('40', plain,
% 0.19/0.50      ((~ (r1_tarski @ sk_A @ sk_A)) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.19/0.50      inference('sup-', [status(thm)], ['35', '39'])).
% 0.19/0.50  thf('41', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.19/0.50      inference('simplify', [status(thm)], ['12'])).
% 0.19/0.50  thf('42', plain, (~ (((sk_A) = (k1_mcart_1 @ sk_A)))),
% 0.19/0.50      inference('demod', [status(thm)], ['40', '41'])).
% 0.19/0.50  thf('43', plain,
% 0.19/0.50      ((((sk_A) = (k2_mcart_1 @ sk_A))) | (((sk_A) = (k1_mcart_1 @ sk_A)))),
% 0.19/0.50      inference('split', [status(esa)], ['3'])).
% 0.19/0.50  thf('44', plain, ((((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.19/0.50      inference('sat_resolution*', [status(thm)], ['42', '43'])).
% 0.19/0.50  thf('45', plain, (((k1_ordinal1 @ sk_A) = (sk_A))),
% 0.19/0.50      inference('simpl_trail', [status(thm)], ['18', '44'])).
% 0.19/0.50  thf('46', plain, (![X0 : $i]: ~ (r1_tarski @ (k1_ordinal1 @ X0) @ X0)),
% 0.19/0.50      inference('sup-', [status(thm)], ['37', '38'])).
% 0.19/0.50  thf('47', plain, (~ (r1_tarski @ sk_A @ sk_A)),
% 0.19/0.50      inference('sup-', [status(thm)], ['45', '46'])).
% 0.19/0.50  thf('48', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.19/0.50      inference('simplify', [status(thm)], ['12'])).
% 0.19/0.50  thf('49', plain, ($false), inference('demod', [status(thm)], ['47', '48'])).
% 0.19/0.50  
% 0.19/0.50  % SZS output end Refutation
% 0.19/0.50  
% 0.19/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
