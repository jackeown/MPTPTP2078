%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TAmf90xije

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:02 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   86 (2261 expanded)
%              Number of leaves         :   19 ( 621 expanded)
%              Depth                    :   25
%              Number of atoms          :  558 (20970 expanded)
%              Number of equality atoms :  109 (4122 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('0',plain,(
    ! [X27: $i,X28: $i] :
      ( ( X28 != X27 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X28 ) @ ( k1_tarski @ X27 ) )
       != ( k1_tarski @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('1',plain,(
    ! [X27: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X27 ) @ ( k1_tarski @ X27 ) )
     != ( k1_tarski @ X27 ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( X11 != X10 )
      | ( r2_hidden @ X11 @ X12 )
      | ( X12
       != ( k1_tarski @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('3',plain,(
    ! [X10: $i] :
      ( r2_hidden @ X10 @ ( k1_tarski @ X10 ) ) ),
    inference(simplify,[status(thm)],['2'])).

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

thf('4',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_2 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_2 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('8',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X39 @ X40 ) )
      = X39 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('9',plain,
    ( ( k1_mcart_1 @ sk_A )
    = sk_B_2 ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,
    ( sk_A
    = ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ sk_C_2 ) ),
    inference(demod,[status(thm)],['6','9'])).

thf('11',plain,
    ( sk_A
    = ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ sk_C_2 ) ),
    inference(demod,[status(thm)],['6','9'])).

thf('12',plain,(
    ! [X39: $i,X41: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X39 @ X41 ) )
      = X41 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('13',plain,
    ( ( k2_mcart_1 @ sk_A )
    = sk_C_2 ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,
    ( sk_A
    = ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ ( k2_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','13'])).

thf('15',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_A @ ( k2_mcart_1 @ sk_A ) ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['5','14'])).

thf('16',plain,(
    ! [X10: $i] :
      ( r2_hidden @ X10 @ ( k1_tarski @ X10 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('17',plain,
    ( ( sk_A
      = ( k2_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['4'])).

thf('18',plain,
    ( sk_A
    = ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ ( k2_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','13'])).

thf('19',plain,
    ( ( sk_A
      = ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(t9_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k4_tarski @ C @ D ) ) ) ) ) )).

thf('20',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ( X42 = k1_xboole_0 )
      | ~ ( r2_hidden @ X43 @ X42 )
      | ( ( sk_B_1 @ X42 )
       != ( k4_tarski @ X44 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('21',plain,
    ( ! [X0: $i] :
        ( ( ( sk_B_1 @ X0 )
         != sk_A )
        | ~ ( r2_hidden @ sk_A @ X0 )
        | ( X0 = k1_xboole_0 ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ( ( sk_B_1 @ ( k1_tarski @ sk_A ) )
       != sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','21'])).

thf('23',plain,(
    ! [X42: $i] :
      ( ( X42 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X42 ) @ X42 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('24',plain,(
    ! [X10: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X13 @ X12 )
      | ( X13 = X10 )
      | ( X12
       != ( k1_tarski @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('25',plain,(
    ! [X10: $i,X13: $i] :
      ( ( X13 = X10 )
      | ~ ( r2_hidden @ X13 @ ( k1_tarski @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( sk_B_1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['22','26'])).

thf('28',plain,(
    ! [X10: $i] :
      ( r2_hidden @ X10 @ ( k1_tarski @ X10 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('29',plain,
    ( ( r2_hidden @ sk_A @ k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('30',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k2_zfmisc_1 @ X25 @ X26 )
        = k1_xboole_0 )
      | ( X26 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('31',plain,(
    ! [X25: $i] :
      ( ( k2_zfmisc_1 @ X25 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['30'])).

thf(t12_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) )
     => ( ( ( k1_mcart_1 @ A )
          = B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('32',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( ( k1_mcart_1 @ X37 )
        = X36 )
      | ~ ( r2_hidden @ X37 @ ( k2_zfmisc_1 @ ( k1_tarski @ X36 ) @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t12_mcart_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ( ( k1_mcart_1 @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ! [X0: $i] :
        ( ( k1_mcart_1 @ sk_A )
        = X0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','33'])).

thf('35',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['22','26'])).

thf('36',plain,(
    ! [X27: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X27 ) @ ( k1_tarski @ X27 ) )
     != ( k1_tarski @ X27 ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf('37',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 )
     != ( k1_tarski @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['22','26'])).

thf('39',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['22','26'])).

thf('40',plain,
    ( ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,
    ( ! [X0: $i] :
        ( ( k1_mcart_1 @ sk_A )
        = X0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','33'])).

thf('42',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ! [X0: $i] : ( X0 != k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','42'])).

thf('44',plain,(
    sk_A
 != ( k2_mcart_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['4'])).

thf('46',plain,
    ( sk_A
    = ( k1_mcart_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['44','45'])).

thf('47',plain,
    ( sk_A
    = ( k4_tarski @ sk_A @ ( k2_mcart_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['15','46'])).

thf('48',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ( X42 = k1_xboole_0 )
      | ~ ( r2_hidden @ X44 @ X42 )
      | ( ( sk_B_1 @ X42 )
       != ( k4_tarski @ X44 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( ( sk_B_1 @ X0 )
       != sk_A )
      | ~ ( r2_hidden @ sk_A @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( sk_B_1 @ ( k1_tarski @ sk_A ) )
     != sk_A ) ),
    inference('sup-',[status(thm)],['3','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( sk_B_1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('52',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X10: $i] :
      ( r2_hidden @ X10 @ ( k1_tarski @ X10 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('54',plain,(
    r2_hidden @ sk_A @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ( ( k1_mcart_1 @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k1_mcart_1 @ sk_A )
      = X0 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['4'])).

thf('58',plain,
    ( sk_A
    = ( k1_mcart_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['44','45'])).

thf('59',plain,
    ( sk_A
    = ( k1_mcart_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] : ( sk_A = X0 ) ),
    inference(demod,[status(thm)],['56','59'])).

thf('61',plain,(
    ! [X0: $i] : ( sk_A = X0 ) ),
    inference(demod,[status(thm)],['56','59'])).

thf('62',plain,(
    ! [X0: $i] : ( sk_A = X0 ) ),
    inference(demod,[status(thm)],['56','59'])).

thf('63',plain,(
    ! [X0: $i] : ( sk_A = X0 ) ),
    inference(demod,[status(thm)],['56','59'])).

thf('64',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['1','60','61','62','63'])).

thf('65',plain,(
    $false ),
    inference(simplify,[status(thm)],['64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TAmf90xije
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:47:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.53  % Solved by: fo/fo7.sh
% 0.21/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.53  % done 139 iterations in 0.071s
% 0.21/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.53  % SZS output start Refutation
% 0.21/0.53  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.21/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.53  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.53  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.21/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.53  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.21/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.53  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.21/0.53  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.21/0.53  thf(t20_zfmisc_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.21/0.53         ( k1_tarski @ A ) ) <=>
% 0.21/0.53       ( ( A ) != ( B ) ) ))).
% 0.21/0.53  thf('0', plain,
% 0.21/0.53      (![X27 : $i, X28 : $i]:
% 0.21/0.53         (((X28) != (X27))
% 0.21/0.53          | ((k4_xboole_0 @ (k1_tarski @ X28) @ (k1_tarski @ X27))
% 0.21/0.53              != (k1_tarski @ X28)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.21/0.53  thf('1', plain,
% 0.21/0.53      (![X27 : $i]:
% 0.21/0.53         ((k4_xboole_0 @ (k1_tarski @ X27) @ (k1_tarski @ X27))
% 0.21/0.53           != (k1_tarski @ X27))),
% 0.21/0.53      inference('simplify', [status(thm)], ['0'])).
% 0.21/0.53  thf(d1_tarski, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.21/0.53       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.21/0.53  thf('2', plain,
% 0.21/0.53      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.53         (((X11) != (X10))
% 0.21/0.53          | (r2_hidden @ X11 @ X12)
% 0.21/0.53          | ((X12) != (k1_tarski @ X10)))),
% 0.21/0.53      inference('cnf', [status(esa)], [d1_tarski])).
% 0.21/0.53  thf('3', plain, (![X10 : $i]: (r2_hidden @ X10 @ (k1_tarski @ X10))),
% 0.21/0.53      inference('simplify', [status(thm)], ['2'])).
% 0.21/0.53  thf(t20_mcart_1, conjecture,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.21/0.53       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 0.21/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.53    (~( ![A:$i]:
% 0.21/0.53        ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.21/0.53          ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ) )),
% 0.21/0.53    inference('cnf.neg', [status(esa)], [t20_mcart_1])).
% 0.21/0.53  thf('4', plain,
% 0.21/0.53      ((((sk_A) = (k1_mcart_1 @ sk_A)) | ((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('5', plain,
% 0.21/0.53      ((((sk_A) = (k1_mcart_1 @ sk_A))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.21/0.53      inference('split', [status(esa)], ['4'])).
% 0.21/0.53  thf('6', plain, (((sk_A) = (k4_tarski @ sk_B_2 @ sk_C_2))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('7', plain, (((sk_A) = (k4_tarski @ sk_B_2 @ sk_C_2))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(t7_mcart_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.21/0.53       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.21/0.53  thf('8', plain,
% 0.21/0.53      (![X39 : $i, X40 : $i]: ((k1_mcart_1 @ (k4_tarski @ X39 @ X40)) = (X39))),
% 0.21/0.53      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.21/0.53  thf('9', plain, (((k1_mcart_1 @ sk_A) = (sk_B_2))),
% 0.21/0.53      inference('sup+', [status(thm)], ['7', '8'])).
% 0.21/0.53  thf('10', plain, (((sk_A) = (k4_tarski @ (k1_mcart_1 @ sk_A) @ sk_C_2))),
% 0.21/0.53      inference('demod', [status(thm)], ['6', '9'])).
% 0.21/0.53  thf('11', plain, (((sk_A) = (k4_tarski @ (k1_mcart_1 @ sk_A) @ sk_C_2))),
% 0.21/0.53      inference('demod', [status(thm)], ['6', '9'])).
% 0.21/0.53  thf('12', plain,
% 0.21/0.53      (![X39 : $i, X41 : $i]: ((k2_mcart_1 @ (k4_tarski @ X39 @ X41)) = (X41))),
% 0.21/0.53      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.21/0.53  thf('13', plain, (((k2_mcart_1 @ sk_A) = (sk_C_2))),
% 0.21/0.53      inference('sup+', [status(thm)], ['11', '12'])).
% 0.21/0.53  thf('14', plain,
% 0.21/0.53      (((sk_A) = (k4_tarski @ (k1_mcart_1 @ sk_A) @ (k2_mcart_1 @ sk_A)))),
% 0.21/0.53      inference('demod', [status(thm)], ['10', '13'])).
% 0.21/0.53  thf('15', plain,
% 0.21/0.53      ((((sk_A) = (k4_tarski @ sk_A @ (k2_mcart_1 @ sk_A))))
% 0.21/0.53         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.21/0.53      inference('sup+', [status(thm)], ['5', '14'])).
% 0.21/0.53  thf('16', plain, (![X10 : $i]: (r2_hidden @ X10 @ (k1_tarski @ X10))),
% 0.21/0.53      inference('simplify', [status(thm)], ['2'])).
% 0.21/0.53  thf('17', plain,
% 0.21/0.53      ((((sk_A) = (k2_mcart_1 @ sk_A))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.21/0.53      inference('split', [status(esa)], ['4'])).
% 0.21/0.53  thf('18', plain,
% 0.21/0.53      (((sk_A) = (k4_tarski @ (k1_mcart_1 @ sk_A) @ (k2_mcart_1 @ sk_A)))),
% 0.21/0.53      inference('demod', [status(thm)], ['10', '13'])).
% 0.21/0.53  thf('19', plain,
% 0.21/0.53      ((((sk_A) = (k4_tarski @ (k1_mcart_1 @ sk_A) @ sk_A)))
% 0.21/0.53         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.21/0.53      inference('sup+', [status(thm)], ['17', '18'])).
% 0.21/0.53  thf(t9_mcart_1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.53          ( ![B:$i]:
% 0.21/0.53            ( ~( ( r2_hidden @ B @ A ) & 
% 0.21/0.53                 ( ![C:$i,D:$i]:
% 0.21/0.53                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.21/0.53                        ( ( B ) = ( k4_tarski @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.53  thf('20', plain,
% 0.21/0.53      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.21/0.53         (((X42) = (k1_xboole_0))
% 0.21/0.53          | ~ (r2_hidden @ X43 @ X42)
% 0.21/0.53          | ((sk_B_1 @ X42) != (k4_tarski @ X44 @ X43)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.21/0.53  thf('21', plain,
% 0.21/0.53      ((![X0 : $i]:
% 0.21/0.53          (((sk_B_1 @ X0) != (sk_A))
% 0.21/0.53           | ~ (r2_hidden @ sk_A @ X0)
% 0.21/0.53           | ((X0) = (k1_xboole_0))))
% 0.21/0.53         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.53  thf('22', plain,
% 0.21/0.53      (((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.21/0.53         | ((sk_B_1 @ (k1_tarski @ sk_A)) != (sk_A))))
% 0.21/0.53         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['16', '21'])).
% 0.21/0.53  thf('23', plain,
% 0.21/0.53      (![X42 : $i]:
% 0.21/0.53         (((X42) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X42) @ X42))),
% 0.21/0.53      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.21/0.53  thf('24', plain,
% 0.21/0.53      (![X10 : $i, X12 : $i, X13 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X13 @ X12)
% 0.21/0.53          | ((X13) = (X10))
% 0.21/0.53          | ((X12) != (k1_tarski @ X10)))),
% 0.21/0.53      inference('cnf', [status(esa)], [d1_tarski])).
% 0.21/0.53  thf('25', plain,
% 0.21/0.53      (![X10 : $i, X13 : $i]:
% 0.21/0.53         (((X13) = (X10)) | ~ (r2_hidden @ X13 @ (k1_tarski @ X10)))),
% 0.21/0.53      inference('simplify', [status(thm)], ['24'])).
% 0.21/0.53  thf('26', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.21/0.53          | ((sk_B_1 @ (k1_tarski @ X0)) = (X0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['23', '25'])).
% 0.21/0.53  thf('27', plain,
% 0.21/0.53      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 0.21/0.53         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.21/0.53      inference('clc', [status(thm)], ['22', '26'])).
% 0.21/0.53  thf('28', plain, (![X10 : $i]: (r2_hidden @ X10 @ (k1_tarski @ X10))),
% 0.21/0.53      inference('simplify', [status(thm)], ['2'])).
% 0.21/0.53  thf('29', plain,
% 0.21/0.53      (((r2_hidden @ sk_A @ k1_xboole_0)) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.21/0.53      inference('sup+', [status(thm)], ['27', '28'])).
% 0.21/0.53  thf(t113_zfmisc_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.21/0.53       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.53  thf('30', plain,
% 0.21/0.53      (![X25 : $i, X26 : $i]:
% 0.21/0.53         (((k2_zfmisc_1 @ X25 @ X26) = (k1_xboole_0))
% 0.21/0.53          | ((X26) != (k1_xboole_0)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.21/0.53  thf('31', plain,
% 0.21/0.53      (![X25 : $i]: ((k2_zfmisc_1 @ X25 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.53      inference('simplify', [status(thm)], ['30'])).
% 0.21/0.53  thf(t12_mcart_1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) ) =>
% 0.21/0.53       ( ( ( k1_mcart_1 @ A ) = ( B ) ) & 
% 0.21/0.53         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.21/0.53  thf('32', plain,
% 0.21/0.53      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.21/0.53         (((k1_mcart_1 @ X37) = (X36))
% 0.21/0.53          | ~ (r2_hidden @ X37 @ (k2_zfmisc_1 @ (k1_tarski @ X36) @ X38)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t12_mcart_1])).
% 0.21/0.53  thf('33', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X1 @ k1_xboole_0) | ((k1_mcart_1 @ X1) = (X0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.53  thf('34', plain,
% 0.21/0.53      ((![X0 : $i]: ((k1_mcart_1 @ sk_A) = (X0)))
% 0.21/0.53         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['29', '33'])).
% 0.21/0.53  thf('35', plain,
% 0.21/0.53      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 0.21/0.53         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.21/0.53      inference('clc', [status(thm)], ['22', '26'])).
% 0.21/0.53  thf('36', plain,
% 0.21/0.53      (![X27 : $i]:
% 0.21/0.53         ((k4_xboole_0 @ (k1_tarski @ X27) @ (k1_tarski @ X27))
% 0.21/0.53           != (k1_tarski @ X27))),
% 0.21/0.53      inference('simplify', [status(thm)], ['0'])).
% 0.21/0.53  thf('37', plain,
% 0.21/0.53      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0) != (k1_tarski @ sk_A)))
% 0.21/0.53         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.53  thf('38', plain,
% 0.21/0.53      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 0.21/0.53         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.21/0.53      inference('clc', [status(thm)], ['22', '26'])).
% 0.21/0.53  thf('39', plain,
% 0.21/0.53      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 0.21/0.53         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.21/0.53      inference('clc', [status(thm)], ['22', '26'])).
% 0.21/0.53  thf('40', plain,
% 0.21/0.53      ((((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) != (k1_xboole_0)))
% 0.21/0.53         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.21/0.53      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.21/0.53  thf('41', plain,
% 0.21/0.53      ((![X0 : $i]: ((k1_mcart_1 @ sk_A) = (X0)))
% 0.21/0.53         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['29', '33'])).
% 0.21/0.53  thf('42', plain,
% 0.21/0.53      ((((k1_mcart_1 @ sk_A) != (k1_xboole_0)))
% 0.21/0.53         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.21/0.53      inference('demod', [status(thm)], ['40', '41'])).
% 0.21/0.53  thf('43', plain,
% 0.21/0.53      ((![X0 : $i]: ((X0) != (k1_xboole_0)))
% 0.21/0.53         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['34', '42'])).
% 0.21/0.53  thf('44', plain, (~ (((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.21/0.53      inference('simplify', [status(thm)], ['43'])).
% 0.21/0.53  thf('45', plain,
% 0.21/0.53      ((((sk_A) = (k1_mcart_1 @ sk_A))) | (((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.21/0.53      inference('split', [status(esa)], ['4'])).
% 0.21/0.53  thf('46', plain, ((((sk_A) = (k1_mcart_1 @ sk_A)))),
% 0.21/0.53      inference('sat_resolution*', [status(thm)], ['44', '45'])).
% 0.21/0.53  thf('47', plain, (((sk_A) = (k4_tarski @ sk_A @ (k2_mcart_1 @ sk_A)))),
% 0.21/0.53      inference('simpl_trail', [status(thm)], ['15', '46'])).
% 0.21/0.53  thf('48', plain,
% 0.21/0.53      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.21/0.53         (((X42) = (k1_xboole_0))
% 0.21/0.53          | ~ (r2_hidden @ X44 @ X42)
% 0.21/0.53          | ((sk_B_1 @ X42) != (k4_tarski @ X44 @ X43)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.21/0.53  thf('49', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (((sk_B_1 @ X0) != (sk_A))
% 0.21/0.53          | ~ (r2_hidden @ sk_A @ X0)
% 0.21/0.53          | ((X0) = (k1_xboole_0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['47', '48'])).
% 0.21/0.53  thf('50', plain,
% 0.21/0.53      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.21/0.53        | ((sk_B_1 @ (k1_tarski @ sk_A)) != (sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['3', '49'])).
% 0.21/0.53  thf('51', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.21/0.53          | ((sk_B_1 @ (k1_tarski @ X0)) = (X0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['23', '25'])).
% 0.21/0.53  thf('52', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.21/0.53      inference('clc', [status(thm)], ['50', '51'])).
% 0.21/0.53  thf('53', plain, (![X10 : $i]: (r2_hidden @ X10 @ (k1_tarski @ X10))),
% 0.21/0.53      inference('simplify', [status(thm)], ['2'])).
% 0.21/0.53  thf('54', plain, ((r2_hidden @ sk_A @ k1_xboole_0)),
% 0.21/0.53      inference('sup+', [status(thm)], ['52', '53'])).
% 0.21/0.53  thf('55', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X1 @ k1_xboole_0) | ((k1_mcart_1 @ X1) = (X0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.53  thf('56', plain, (![X0 : $i]: ((k1_mcart_1 @ sk_A) = (X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['54', '55'])).
% 0.21/0.53  thf('57', plain,
% 0.21/0.53      ((((sk_A) = (k1_mcart_1 @ sk_A))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.21/0.53      inference('split', [status(esa)], ['4'])).
% 0.21/0.53  thf('58', plain, ((((sk_A) = (k1_mcart_1 @ sk_A)))),
% 0.21/0.53      inference('sat_resolution*', [status(thm)], ['44', '45'])).
% 0.21/0.53  thf('59', plain, (((sk_A) = (k1_mcart_1 @ sk_A))),
% 0.21/0.53      inference('simpl_trail', [status(thm)], ['57', '58'])).
% 0.21/0.53  thf('60', plain, (![X0 : $i]: ((sk_A) = (X0))),
% 0.21/0.53      inference('demod', [status(thm)], ['56', '59'])).
% 0.21/0.53  thf('61', plain, (![X0 : $i]: ((sk_A) = (X0))),
% 0.21/0.53      inference('demod', [status(thm)], ['56', '59'])).
% 0.21/0.53  thf('62', plain, (![X0 : $i]: ((sk_A) = (X0))),
% 0.21/0.53      inference('demod', [status(thm)], ['56', '59'])).
% 0.21/0.53  thf('63', plain, (![X0 : $i]: ((sk_A) = (X0))),
% 0.21/0.53      inference('demod', [status(thm)], ['56', '59'])).
% 0.21/0.53  thf('64', plain, (((sk_A) != (sk_A))),
% 0.21/0.53      inference('demod', [status(thm)], ['1', '60', '61', '62', '63'])).
% 0.21/0.53  thf('65', plain, ($false), inference('simplify', [status(thm)], ['64'])).
% 0.21/0.53  
% 0.21/0.53  % SZS output end Refutation
% 0.21/0.53  
% 0.21/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
