%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8wuooshC0p

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:02 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 116 expanded)
%              Number of leaves         :   20 (  43 expanded)
%              Depth                    :   17
%              Number of atoms          :  390 ( 832 expanded)
%              Number of equality atoms :   70 ( 145 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_3_type,type,(
    sk_B_3: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i > $i )).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('0',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( X4 != X3 )
      | ( r2_hidden @ X4 @ X5 )
      | ( X5
       != ( k1_tarski @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('1',plain,(
    ! [X3: $i] :
      ( r2_hidden @ X3 @ ( k1_tarski @ X3 ) ) ),
    inference(simplify,[status(thm)],['0'])).

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

thf('2',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_3 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('3',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X23 @ X24 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('4',plain,
    ( ( k1_mcart_1 @ sk_A )
    = sk_B_3 ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,
    ( ( sk_A = sk_B_3 )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['4','6'])).

thf('8',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_3 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_A @ sk_C_1 ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X3: $i] :
      ( r2_hidden @ X3 @ ( k1_tarski @ X3 ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf('11',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_3 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X23: $i,X25: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X23 @ X25 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('13',plain,
    ( ( k2_mcart_1 @ sk_A )
    = sk_C_1 ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( sk_A
      = ( k2_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['5'])).

thf('15',plain,
    ( ( sk_A = sk_C_1 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_3 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_B_3 @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

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

thf('18',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( X26 = k1_xboole_0 )
      | ~ ( r2_hidden @ X27 @ X26 )
      | ( ( sk_B_2 @ X26 )
       != ( k4_tarski @ X28 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('19',plain,
    ( ! [X0: $i] :
        ( ( ( sk_B_2 @ X0 )
         != sk_A )
        | ~ ( r2_hidden @ sk_A @ X0 )
        | ( X0 = k1_xboole_0 ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ( ( sk_B_2 @ ( k1_tarski @ sk_A ) )
       != sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','19'])).

thf('21',plain,(
    ! [X26: $i] :
      ( ( X26 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_2 @ X26 ) @ X26 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('22',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( X6 = X3 )
      | ( X5
       != ( k1_tarski @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('23',plain,(
    ! [X3: $i,X6: $i] :
      ( ( X6 = X3 )
      | ~ ( r2_hidden @ X6 @ ( k1_tarski @ X3 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( sk_B_2 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['20','24'])).

thf('26',plain,(
    ! [X3: $i] :
      ( r2_hidden @ X3 @ ( k1_tarski @ X3 ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('28',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf(rc2_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ( v1_xboole_0 @ B )
      & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('30',plain,(
    ! [X17: $i] :
      ( v1_xboole_0 @ ( sk_B_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[rc2_subset_1])).

thf('31',plain,(
    ! [X17: $i] :
      ( v1_xboole_0 @ ( sk_B_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[rc2_subset_1])).

thf('32',plain,(
    ! [X26: $i] :
      ( ( X26 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_2 @ X26 ) @ X26 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( sk_B_1 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['30','35'])).

thf('37',plain,(
    sk_A
 != ( k2_mcart_1 @ sk_A ) ),
    inference(demod,[status(thm)],['29','36'])).

thf('38',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['5'])).

thf('39',plain,
    ( sk_A
    = ( k1_mcart_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['37','38'])).

thf('40',plain,
    ( sk_A
    = ( k4_tarski @ sk_A @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['9','39'])).

thf('41',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( X26 = k1_xboole_0 )
      | ~ ( r2_hidden @ X28 @ X26 )
      | ( ( sk_B_2 @ X26 )
       != ( k4_tarski @ X28 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( ( sk_B_2 @ X0 )
       != sk_A )
      | ~ ( r2_hidden @ sk_A @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( sk_B_2 @ ( k1_tarski @ sk_A ) )
     != sk_A ) ),
    inference('sup-',[status(thm)],['1','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( sk_B_2 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('45',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('47',plain,(
    ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['30','35'])).

thf('49',plain,(
    $false ),
    inference(demod,[status(thm)],['47','48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8wuooshC0p
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:40:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 115 iterations in 0.051s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.50  thf(sk_B_3_type, type, sk_B_3: $i).
% 0.20/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.50  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.20/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.50  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.20/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.20/0.50  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.50  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.50  thf(sk_B_2_type, type, sk_B_2: $i > $i).
% 0.20/0.50  thf(d1_tarski, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.20/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.20/0.50  thf('0', plain,
% 0.20/0.50      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.50         (((X4) != (X3)) | (r2_hidden @ X4 @ X5) | ((X5) != (k1_tarski @ X3)))),
% 0.20/0.50      inference('cnf', [status(esa)], [d1_tarski])).
% 0.20/0.50  thf('1', plain, (![X3 : $i]: (r2_hidden @ X3 @ (k1_tarski @ X3))),
% 0.20/0.50      inference('simplify', [status(thm)], ['0'])).
% 0.20/0.50  thf(t20_mcart_1, conjecture,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.20/0.50       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i]:
% 0.20/0.50        ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.20/0.50          ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t20_mcart_1])).
% 0.20/0.50  thf('2', plain, (((sk_A) = (k4_tarski @ sk_B_3 @ sk_C_1))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t7_mcart_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.20/0.50       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.20/0.50  thf('3', plain,
% 0.20/0.50      (![X23 : $i, X24 : $i]: ((k1_mcart_1 @ (k4_tarski @ X23 @ X24)) = (X23))),
% 0.20/0.50      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.50  thf('4', plain, (((k1_mcart_1 @ sk_A) = (sk_B_3))),
% 0.20/0.50      inference('sup+', [status(thm)], ['2', '3'])).
% 0.20/0.50  thf('5', plain,
% 0.20/0.50      ((((sk_A) = (k1_mcart_1 @ sk_A)) | ((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('6', plain,
% 0.20/0.50      ((((sk_A) = (k1_mcart_1 @ sk_A))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.20/0.50      inference('split', [status(esa)], ['5'])).
% 0.20/0.50  thf('7', plain,
% 0.20/0.50      ((((sk_A) = (sk_B_3))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.20/0.50      inference('sup+', [status(thm)], ['4', '6'])).
% 0.20/0.50  thf('8', plain, (((sk_A) = (k4_tarski @ sk_B_3 @ sk_C_1))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('9', plain,
% 0.20/0.50      ((((sk_A) = (k4_tarski @ sk_A @ sk_C_1)))
% 0.20/0.50         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.20/0.50      inference('sup+', [status(thm)], ['7', '8'])).
% 0.20/0.50  thf('10', plain, (![X3 : $i]: (r2_hidden @ X3 @ (k1_tarski @ X3))),
% 0.20/0.50      inference('simplify', [status(thm)], ['0'])).
% 0.20/0.50  thf('11', plain, (((sk_A) = (k4_tarski @ sk_B_3 @ sk_C_1))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('12', plain,
% 0.20/0.50      (![X23 : $i, X25 : $i]: ((k2_mcart_1 @ (k4_tarski @ X23 @ X25)) = (X25))),
% 0.20/0.50      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.50  thf('13', plain, (((k2_mcart_1 @ sk_A) = (sk_C_1))),
% 0.20/0.50      inference('sup+', [status(thm)], ['11', '12'])).
% 0.20/0.50  thf('14', plain,
% 0.20/0.50      ((((sk_A) = (k2_mcart_1 @ sk_A))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.20/0.50      inference('split', [status(esa)], ['5'])).
% 0.20/0.50  thf('15', plain,
% 0.20/0.50      ((((sk_A) = (sk_C_1))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.20/0.50      inference('sup+', [status(thm)], ['13', '14'])).
% 0.20/0.50  thf('16', plain, (((sk_A) = (k4_tarski @ sk_B_3 @ sk_C_1))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('17', plain,
% 0.20/0.50      ((((sk_A) = (k4_tarski @ sk_B_3 @ sk_A)))
% 0.20/0.50         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.20/0.50      inference('sup+', [status(thm)], ['15', '16'])).
% 0.20/0.50  thf(t9_mcart_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.50          ( ![B:$i]:
% 0.20/0.50            ( ~( ( r2_hidden @ B @ A ) & 
% 0.20/0.50                 ( ![C:$i,D:$i]:
% 0.20/0.50                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.20/0.50                        ( ( B ) = ( k4_tarski @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf('18', plain,
% 0.20/0.50      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.20/0.50         (((X26) = (k1_xboole_0))
% 0.20/0.50          | ~ (r2_hidden @ X27 @ X26)
% 0.20/0.50          | ((sk_B_2 @ X26) != (k4_tarski @ X28 @ X27)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.20/0.50  thf('19', plain,
% 0.20/0.50      ((![X0 : $i]:
% 0.20/0.50          (((sk_B_2 @ X0) != (sk_A))
% 0.20/0.50           | ~ (r2_hidden @ sk_A @ X0)
% 0.20/0.50           | ((X0) = (k1_xboole_0))))
% 0.20/0.50         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.50  thf('20', plain,
% 0.20/0.50      (((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.20/0.50         | ((sk_B_2 @ (k1_tarski @ sk_A)) != (sk_A))))
% 0.20/0.50         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['10', '19'])).
% 0.20/0.50  thf('21', plain,
% 0.20/0.50      (![X26 : $i]:
% 0.20/0.50         (((X26) = (k1_xboole_0)) | (r2_hidden @ (sk_B_2 @ X26) @ X26))),
% 0.20/0.50      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.20/0.50  thf('22', plain,
% 0.20/0.50      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X6 @ X5) | ((X6) = (X3)) | ((X5) != (k1_tarski @ X3)))),
% 0.20/0.50      inference('cnf', [status(esa)], [d1_tarski])).
% 0.20/0.50  thf('23', plain,
% 0.20/0.50      (![X3 : $i, X6 : $i]:
% 0.20/0.50         (((X6) = (X3)) | ~ (r2_hidden @ X6 @ (k1_tarski @ X3)))),
% 0.20/0.50      inference('simplify', [status(thm)], ['22'])).
% 0.20/0.50  thf('24', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.20/0.50          | ((sk_B_2 @ (k1_tarski @ X0)) = (X0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['21', '23'])).
% 0.20/0.50  thf('25', plain,
% 0.20/0.50      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 0.20/0.50         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.20/0.50      inference('clc', [status(thm)], ['20', '24'])).
% 0.20/0.50  thf('26', plain, (![X3 : $i]: (r2_hidden @ X3 @ (k1_tarski @ X3))),
% 0.20/0.50      inference('simplify', [status(thm)], ['0'])).
% 0.20/0.50  thf(d1_xboole_0, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.50  thf('27', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.50      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.50  thf('28', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.50  thf('29', plain,
% 0.20/0.50      ((~ (v1_xboole_0 @ k1_xboole_0)) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['25', '28'])).
% 0.20/0.50  thf(rc2_subset_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ?[B:$i]:
% 0.20/0.50       ( ( v1_xboole_0 @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.20/0.50  thf('30', plain, (![X17 : $i]: (v1_xboole_0 @ (sk_B_1 @ X17))),
% 0.20/0.50      inference('cnf', [status(esa)], [rc2_subset_1])).
% 0.20/0.50  thf('31', plain, (![X17 : $i]: (v1_xboole_0 @ (sk_B_1 @ X17))),
% 0.20/0.50      inference('cnf', [status(esa)], [rc2_subset_1])).
% 0.20/0.50  thf('32', plain,
% 0.20/0.50      (![X26 : $i]:
% 0.20/0.50         (((X26) = (k1_xboole_0)) | (r2_hidden @ (sk_B_2 @ X26) @ X26))),
% 0.20/0.50      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.20/0.50  thf('33', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.50      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.50  thf('34', plain,
% 0.20/0.50      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['32', '33'])).
% 0.20/0.50  thf('35', plain, (![X0 : $i]: ((sk_B_1 @ X0) = (k1_xboole_0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['31', '34'])).
% 0.20/0.50  thf('36', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.50      inference('demod', [status(thm)], ['30', '35'])).
% 0.20/0.50  thf('37', plain, (~ (((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.20/0.50      inference('demod', [status(thm)], ['29', '36'])).
% 0.20/0.50  thf('38', plain,
% 0.20/0.50      ((((sk_A) = (k1_mcart_1 @ sk_A))) | (((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.20/0.50      inference('split', [status(esa)], ['5'])).
% 0.20/0.50  thf('39', plain, ((((sk_A) = (k1_mcart_1 @ sk_A)))),
% 0.20/0.50      inference('sat_resolution*', [status(thm)], ['37', '38'])).
% 0.20/0.50  thf('40', plain, (((sk_A) = (k4_tarski @ sk_A @ sk_C_1))),
% 0.20/0.50      inference('simpl_trail', [status(thm)], ['9', '39'])).
% 0.20/0.50  thf('41', plain,
% 0.20/0.50      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.20/0.50         (((X26) = (k1_xboole_0))
% 0.20/0.50          | ~ (r2_hidden @ X28 @ X26)
% 0.20/0.50          | ((sk_B_2 @ X26) != (k4_tarski @ X28 @ X27)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.20/0.50  thf('42', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (((sk_B_2 @ X0) != (sk_A))
% 0.20/0.50          | ~ (r2_hidden @ sk_A @ X0)
% 0.20/0.50          | ((X0) = (k1_xboole_0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['40', '41'])).
% 0.20/0.50  thf('43', plain,
% 0.20/0.50      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.20/0.50        | ((sk_B_2 @ (k1_tarski @ sk_A)) != (sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['1', '42'])).
% 0.20/0.50  thf('44', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.20/0.50          | ((sk_B_2 @ (k1_tarski @ X0)) = (X0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['21', '23'])).
% 0.20/0.50  thf('45', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.20/0.50      inference('clc', [status(thm)], ['43', '44'])).
% 0.20/0.50  thf('46', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.50  thf('47', plain, (~ (v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.50      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.50  thf('48', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.50      inference('demod', [status(thm)], ['30', '35'])).
% 0.20/0.50  thf('49', plain, ($false), inference('demod', [status(thm)], ['47', '48'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
