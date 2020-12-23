%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.C1sszdlu0Q

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:00 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 157 expanded)
%              Number of leaves         :   21 (  54 expanded)
%              Depth                    :   15
%              Number of atoms          :  546 (1231 expanded)
%              Number of equality atoms :  102 ( 218 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k4_xboole_0 @ X23 @ ( k1_tarski @ X24 ) )
        = X23 )
      | ( r2_hidden @ X24 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('1',plain,(
    ! [X9: $i] :
      ( ( k2_tarski @ X9 @ X9 )
      = ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('2',plain,(
    ! [X19: $i,X20: $i] :
      ( ( X20 != X19 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X20 ) @ ( k1_tarski @ X19 ) )
       != ( k1_tarski @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('3',plain,(
    ! [X19: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X19 ) @ ( k1_tarski @ X19 ) )
     != ( k1_tarski @ X19 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k1_tarski @ X0 ) )
     != ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( ( k2_tarski @ X0 @ X0 )
       != ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','4'])).

thf('6',plain,(
    ! [X9: $i] :
      ( ( k2_tarski @ X9 @ X9 )
      = ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('7',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X0 ) ) ),
    inference('simplify_reflect+',[status(thm)],['5','6'])).

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

thf('8',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('9',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X27 @ X28 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('10',plain,
    ( ( k1_mcart_1 @ sk_A )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['11'])).

thf('13',plain,
    ( ( sk_A = sk_B_1 )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['10','12'])).

thf('14',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_A @ sk_C ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

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

thf('16',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( X30 = k1_xboole_0 )
      | ~ ( r2_hidden @ X32 @ X30 )
      | ( ( sk_B @ X30 )
       != ( k4_tarski @ X32 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('17',plain,
    ( ! [X0: $i] :
        ( ( ( sk_B @ X0 )
         != sk_A )
        | ~ ( r2_hidden @ sk_A @ X0 )
        | ( X0 = k1_xboole_0 ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( ( ( k2_tarski @ sk_A @ sk_A )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k2_tarski @ sk_A @ sk_A ) )
       != sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','17'])).

thf('19',plain,(
    ! [X9: $i] :
      ( ( k2_tarski @ X9 @ X9 )
      = ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('20',plain,(
    ! [X9: $i] :
      ( ( k2_tarski @ X9 @ X9 )
      = ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('21',plain,(
    ! [X30: $i] :
      ( ( X30 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X30 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('22',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X20 ) @ ( k1_tarski @ X21 ) )
        = ( k1_tarski @ X20 ) )
      | ( X20 = X21 ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('23',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X22 @ X23 )
      | ( ( k4_xboole_0 @ X23 @ ( k1_tarski @ X22 ) )
       != X23 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ X0 ) )
      | ( X0 = X1 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X0
        = ( sk_B @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['21','25'])).

thf('27',plain,(
    ! [X19: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X19 ) @ ( k1_tarski @ X19 ) )
     != ( k1_tarski @ X19 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('28',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( X1 != X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('29',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['28'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('30',plain,(
    ! [X4: $i,X6: $i] :
      ( ( ( k4_xboole_0 @ X4 @ X6 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X19: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X19 ) ) ),
    inference(demod,[status(thm)],['27','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( X0
      = ( sk_B @ ( k1_tarski @ X0 ) ) ) ),
    inference(clc,[status(thm)],['26','32'])).

thf('34',plain,
    ( ( ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ( sk_A != sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','19','20','33'])).

thf('35',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X0 ) ) ),
    inference('simplify_reflect+',[status(thm)],['5','6'])).

thf('37',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X27: $i,X29: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X27 @ X29 ) )
      = X29 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('39',plain,
    ( ( k2_mcart_1 @ sk_A )
    = sk_C ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( sk_A
      = ( k2_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['11'])).

thf('41',plain,
    ( ( sk_A = sk_C )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_B_1 @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( X30 = k1_xboole_0 )
      | ~ ( r2_hidden @ X31 @ X30 )
      | ( ( sk_B @ X30 )
       != ( k4_tarski @ X32 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('45',plain,
    ( ! [X0: $i] :
        ( ( ( sk_B @ X0 )
         != sk_A )
        | ~ ( r2_hidden @ sk_A @ X0 )
        | ( X0 = k1_xboole_0 ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( ( ( k2_tarski @ sk_A @ sk_A )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k2_tarski @ sk_A @ sk_A ) )
       != sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','45'])).

thf('47',plain,(
    ! [X9: $i] :
      ( ( k2_tarski @ X9 @ X9 )
      = ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('48',plain,(
    ! [X9: $i] :
      ( ( k2_tarski @ X9 @ X9 )
      = ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('49',plain,(
    ! [X0: $i] :
      ( X0
      = ( sk_B @ ( k1_tarski @ X0 ) ) ) ),
    inference(clc,[status(thm)],['26','32'])).

thf('50',plain,
    ( ( ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ( sk_A != sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','47','48','49'])).

thf('51',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X19: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X19 ) ) ),
    inference(demod,[status(thm)],['27','31'])).

thf('53',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    sk_A
 != ( k2_mcart_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['11'])).

thf('56',plain,
    ( sk_A
    = ( k1_mcart_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['35','56'])).

thf('58',plain,(
    ! [X19: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X19 ) ) ),
    inference(demod,[status(thm)],['27','31'])).

thf('59',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    $false ),
    inference(simplify,[status(thm)],['59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.C1sszdlu0Q
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:37:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 101 iterations in 0.042s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.50  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.20/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.50  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.50  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.50  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.50  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.50  thf(t65_zfmisc_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.20/0.50       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.20/0.50  thf('0', plain,
% 0.20/0.50      (![X23 : $i, X24 : $i]:
% 0.20/0.50         (((k4_xboole_0 @ X23 @ (k1_tarski @ X24)) = (X23))
% 0.20/0.50          | (r2_hidden @ X24 @ X23))),
% 0.20/0.50      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.20/0.50  thf(t69_enumset1, axiom,
% 0.20/0.50    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.50  thf('1', plain, (![X9 : $i]: ((k2_tarski @ X9 @ X9) = (k1_tarski @ X9))),
% 0.20/0.50      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.50  thf(t20_zfmisc_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.20/0.50         ( k1_tarski @ A ) ) <=>
% 0.20/0.50       ( ( A ) != ( B ) ) ))).
% 0.20/0.50  thf('2', plain,
% 0.20/0.50      (![X19 : $i, X20 : $i]:
% 0.20/0.50         (((X20) != (X19))
% 0.20/0.50          | ((k4_xboole_0 @ (k1_tarski @ X20) @ (k1_tarski @ X19))
% 0.20/0.50              != (k1_tarski @ X20)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.20/0.50  thf('3', plain,
% 0.20/0.50      (![X19 : $i]:
% 0.20/0.50         ((k4_xboole_0 @ (k1_tarski @ X19) @ (k1_tarski @ X19))
% 0.20/0.50           != (k1_tarski @ X19))),
% 0.20/0.50      inference('simplify', [status(thm)], ['2'])).
% 0.20/0.50  thf('4', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((k4_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k1_tarski @ X0))
% 0.20/0.50           != (k1_tarski @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['1', '3'])).
% 0.20/0.50  thf('5', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (((k2_tarski @ X0 @ X0) != (k1_tarski @ X0))
% 0.20/0.50          | (r2_hidden @ X0 @ (k2_tarski @ X0 @ X0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['0', '4'])).
% 0.20/0.50  thf('6', plain, (![X9 : $i]: ((k2_tarski @ X9 @ X9) = (k1_tarski @ X9))),
% 0.20/0.50      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.50  thf('7', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X0))),
% 0.20/0.50      inference('simplify_reflect+', [status(thm)], ['5', '6'])).
% 0.20/0.50  thf(t20_mcart_1, conjecture,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.20/0.50       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i]:
% 0.20/0.50        ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.20/0.50          ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t20_mcart_1])).
% 0.20/0.50  thf('8', plain, (((sk_A) = (k4_tarski @ sk_B_1 @ sk_C))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t7_mcart_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.20/0.50       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.20/0.50  thf('9', plain,
% 0.20/0.50      (![X27 : $i, X28 : $i]: ((k1_mcart_1 @ (k4_tarski @ X27 @ X28)) = (X27))),
% 0.20/0.50      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.50  thf('10', plain, (((k1_mcart_1 @ sk_A) = (sk_B_1))),
% 0.20/0.50      inference('sup+', [status(thm)], ['8', '9'])).
% 0.20/0.50  thf('11', plain,
% 0.20/0.50      ((((sk_A) = (k1_mcart_1 @ sk_A)) | ((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('12', plain,
% 0.20/0.50      ((((sk_A) = (k1_mcart_1 @ sk_A))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.20/0.50      inference('split', [status(esa)], ['11'])).
% 0.20/0.50  thf('13', plain,
% 0.20/0.50      ((((sk_A) = (sk_B_1))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.20/0.50      inference('sup+', [status(thm)], ['10', '12'])).
% 0.20/0.50  thf('14', plain, (((sk_A) = (k4_tarski @ sk_B_1 @ sk_C))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('15', plain,
% 0.20/0.50      ((((sk_A) = (k4_tarski @ sk_A @ sk_C)))
% 0.20/0.50         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.20/0.50      inference('sup+', [status(thm)], ['13', '14'])).
% 0.20/0.50  thf(t9_mcart_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.50          ( ![B:$i]:
% 0.20/0.50            ( ~( ( r2_hidden @ B @ A ) & 
% 0.20/0.50                 ( ![C:$i,D:$i]:
% 0.20/0.50                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.20/0.50                        ( ( B ) = ( k4_tarski @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf('16', plain,
% 0.20/0.50      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.20/0.50         (((X30) = (k1_xboole_0))
% 0.20/0.50          | ~ (r2_hidden @ X32 @ X30)
% 0.20/0.50          | ((sk_B @ X30) != (k4_tarski @ X32 @ X31)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.20/0.50  thf('17', plain,
% 0.20/0.50      ((![X0 : $i]:
% 0.20/0.50          (((sk_B @ X0) != (sk_A))
% 0.20/0.50           | ~ (r2_hidden @ sk_A @ X0)
% 0.20/0.50           | ((X0) = (k1_xboole_0))))
% 0.20/0.50         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.50  thf('18', plain,
% 0.20/0.50      (((((k2_tarski @ sk_A @ sk_A) = (k1_xboole_0))
% 0.20/0.50         | ((sk_B @ (k2_tarski @ sk_A @ sk_A)) != (sk_A))))
% 0.20/0.50         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['7', '17'])).
% 0.20/0.50  thf('19', plain, (![X9 : $i]: ((k2_tarski @ X9 @ X9) = (k1_tarski @ X9))),
% 0.20/0.50      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.50  thf('20', plain, (![X9 : $i]: ((k2_tarski @ X9 @ X9) = (k1_tarski @ X9))),
% 0.20/0.50      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.50  thf('21', plain,
% 0.20/0.50      (![X30 : $i]:
% 0.20/0.50         (((X30) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X30) @ X30))),
% 0.20/0.50      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.20/0.50  thf('22', plain,
% 0.20/0.50      (![X20 : $i, X21 : $i]:
% 0.20/0.50         (((k4_xboole_0 @ (k1_tarski @ X20) @ (k1_tarski @ X21))
% 0.20/0.50            = (k1_tarski @ X20))
% 0.20/0.50          | ((X20) = (X21)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.20/0.50  thf('23', plain,
% 0.20/0.50      (![X22 : $i, X23 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X22 @ X23)
% 0.20/0.50          | ((k4_xboole_0 @ X23 @ (k1_tarski @ X22)) != (X23)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.20/0.50  thf('24', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (((k1_tarski @ X0) != (k1_tarski @ X0))
% 0.20/0.50          | ((X0) = (X1))
% 0.20/0.50          | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.50  thf('25', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X0) = (X1)))),
% 0.20/0.50      inference('simplify', [status(thm)], ['24'])).
% 0.20/0.50  thf('26', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.20/0.50          | ((X0) = (sk_B @ (k1_tarski @ X0))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['21', '25'])).
% 0.20/0.50  thf('27', plain,
% 0.20/0.50      (![X19 : $i]:
% 0.20/0.50         ((k4_xboole_0 @ (k1_tarski @ X19) @ (k1_tarski @ X19))
% 0.20/0.50           != (k1_tarski @ X19))),
% 0.20/0.50      inference('simplify', [status(thm)], ['2'])).
% 0.20/0.50  thf(d10_xboole_0, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.50  thf('28', plain,
% 0.20/0.50      (![X1 : $i, X2 : $i]: ((r1_tarski @ X1 @ X2) | ((X1) != (X2)))),
% 0.20/0.50      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.50  thf('29', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 0.20/0.50      inference('simplify', [status(thm)], ['28'])).
% 0.20/0.50  thf(l32_xboole_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.50  thf('30', plain,
% 0.20/0.50      (![X4 : $i, X6 : $i]:
% 0.20/0.50         (((k4_xboole_0 @ X4 @ X6) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ X6))),
% 0.20/0.50      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.20/0.50  thf('31', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.50  thf('32', plain, (![X19 : $i]: ((k1_xboole_0) != (k1_tarski @ X19))),
% 0.20/0.50      inference('demod', [status(thm)], ['27', '31'])).
% 0.20/0.50  thf('33', plain, (![X0 : $i]: ((X0) = (sk_B @ (k1_tarski @ X0)))),
% 0.20/0.50      inference('clc', [status(thm)], ['26', '32'])).
% 0.20/0.50  thf('34', plain,
% 0.20/0.50      (((((k1_tarski @ sk_A) = (k1_xboole_0)) | ((sk_A) != (sk_A))))
% 0.20/0.50         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.20/0.50      inference('demod', [status(thm)], ['18', '19', '20', '33'])).
% 0.20/0.50  thf('35', plain,
% 0.20/0.50      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 0.20/0.50         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.20/0.50      inference('simplify', [status(thm)], ['34'])).
% 0.20/0.50  thf('36', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X0))),
% 0.20/0.50      inference('simplify_reflect+', [status(thm)], ['5', '6'])).
% 0.20/0.50  thf('37', plain, (((sk_A) = (k4_tarski @ sk_B_1 @ sk_C))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('38', plain,
% 0.20/0.50      (![X27 : $i, X29 : $i]: ((k2_mcart_1 @ (k4_tarski @ X27 @ X29)) = (X29))),
% 0.20/0.50      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.50  thf('39', plain, (((k2_mcart_1 @ sk_A) = (sk_C))),
% 0.20/0.50      inference('sup+', [status(thm)], ['37', '38'])).
% 0.20/0.50  thf('40', plain,
% 0.20/0.50      ((((sk_A) = (k2_mcart_1 @ sk_A))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.20/0.50      inference('split', [status(esa)], ['11'])).
% 0.20/0.50  thf('41', plain, ((((sk_A) = (sk_C))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.20/0.50      inference('sup+', [status(thm)], ['39', '40'])).
% 0.20/0.50  thf('42', plain, (((sk_A) = (k4_tarski @ sk_B_1 @ sk_C))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('43', plain,
% 0.20/0.50      ((((sk_A) = (k4_tarski @ sk_B_1 @ sk_A)))
% 0.20/0.50         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.20/0.50      inference('sup+', [status(thm)], ['41', '42'])).
% 0.20/0.50  thf('44', plain,
% 0.20/0.50      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.20/0.50         (((X30) = (k1_xboole_0))
% 0.20/0.50          | ~ (r2_hidden @ X31 @ X30)
% 0.20/0.50          | ((sk_B @ X30) != (k4_tarski @ X32 @ X31)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.20/0.50  thf('45', plain,
% 0.20/0.50      ((![X0 : $i]:
% 0.20/0.50          (((sk_B @ X0) != (sk_A))
% 0.20/0.50           | ~ (r2_hidden @ sk_A @ X0)
% 0.20/0.50           | ((X0) = (k1_xboole_0))))
% 0.20/0.50         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['43', '44'])).
% 0.20/0.50  thf('46', plain,
% 0.20/0.50      (((((k2_tarski @ sk_A @ sk_A) = (k1_xboole_0))
% 0.20/0.50         | ((sk_B @ (k2_tarski @ sk_A @ sk_A)) != (sk_A))))
% 0.20/0.50         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['36', '45'])).
% 0.20/0.50  thf('47', plain, (![X9 : $i]: ((k2_tarski @ X9 @ X9) = (k1_tarski @ X9))),
% 0.20/0.50      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.50  thf('48', plain, (![X9 : $i]: ((k2_tarski @ X9 @ X9) = (k1_tarski @ X9))),
% 0.20/0.50      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.50  thf('49', plain, (![X0 : $i]: ((X0) = (sk_B @ (k1_tarski @ X0)))),
% 0.20/0.50      inference('clc', [status(thm)], ['26', '32'])).
% 0.20/0.50  thf('50', plain,
% 0.20/0.50      (((((k1_tarski @ sk_A) = (k1_xboole_0)) | ((sk_A) != (sk_A))))
% 0.20/0.50         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.20/0.50      inference('demod', [status(thm)], ['46', '47', '48', '49'])).
% 0.20/0.50  thf('51', plain,
% 0.20/0.50      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 0.20/0.50         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.20/0.50      inference('simplify', [status(thm)], ['50'])).
% 0.20/0.50  thf('52', plain, (![X19 : $i]: ((k1_xboole_0) != (k1_tarski @ X19))),
% 0.20/0.50      inference('demod', [status(thm)], ['27', '31'])).
% 0.20/0.50  thf('53', plain,
% 0.20/0.50      ((((k1_xboole_0) != (k1_xboole_0))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['51', '52'])).
% 0.20/0.50  thf('54', plain, (~ (((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.20/0.50      inference('simplify', [status(thm)], ['53'])).
% 0.20/0.50  thf('55', plain,
% 0.20/0.50      ((((sk_A) = (k1_mcart_1 @ sk_A))) | (((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.20/0.50      inference('split', [status(esa)], ['11'])).
% 0.20/0.50  thf('56', plain, ((((sk_A) = (k1_mcart_1 @ sk_A)))),
% 0.20/0.50      inference('sat_resolution*', [status(thm)], ['54', '55'])).
% 0.20/0.50  thf('57', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.20/0.50      inference('simpl_trail', [status(thm)], ['35', '56'])).
% 0.20/0.50  thf('58', plain, (![X19 : $i]: ((k1_xboole_0) != (k1_tarski @ X19))),
% 0.20/0.50      inference('demod', [status(thm)], ['27', '31'])).
% 0.20/0.50  thf('59', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['57', '58'])).
% 0.20/0.50  thf('60', plain, ($false), inference('simplify', [status(thm)], ['59'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
