%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Vo3WazMAOu

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:05 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 143 expanded)
%              Number of leaves         :   22 (  50 expanded)
%              Depth                    :   17
%              Number of atoms          :  502 (1068 expanded)
%              Number of equality atoms :   82 ( 184 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('1',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
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
    = ( k4_tarski @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('3',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X20 @ X21 ) )
      = X20 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('4',plain,
    ( ( k1_mcart_1 @ sk_A )
    = sk_B_1 ),
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
    ( ( sk_A = sk_B_1 )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['4','6'])).

thf('8',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_A @ sk_C_1 ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X20: $i,X22: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X20 @ X22 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('12',plain,
    ( ( k2_mcart_1 @ sk_A )
    = sk_C_1 ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( sk_A
      = ( k2_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['5'])).

thf('14',plain,
    ( ( sk_A = sk_C_1 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_B_1 @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

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

thf('17',plain,(
    ! [X23: $i] :
      ( ( X23 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X23 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('18',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X2 )
      | ( X3 = X0 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('19',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( X23 = k1_xboole_0 )
      | ~ ( r2_hidden @ X24 @ X23 )
      | ( ( sk_B @ X23 )
       != ( k4_tarski @ X25 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( k4_tarski @ X2 @ X1 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ ( k4_tarski @ X2 @ X1 ) ) )
      | ( ( k1_tarski @ ( k4_tarski @ X2 @ X1 ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ( ~ ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) )
      | ( ( k1_tarski @ ( k4_tarski @ sk_B_1 @ sk_A ) )
        = k1_xboole_0 ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf('26',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_B_1 @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('27',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('29',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X18 @ X19 )
      | ~ ( r1_tarski @ X19 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('30',plain,(
    ! [X0: $i] :
      ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_A )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('32',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('33',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('34',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    sk_A
 != ( k2_mcart_1 @ sk_A ) ),
    inference(demod,[status(thm)],['31','34'])).

thf('36',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['5'])).

thf('37',plain,
    ( sk_A
    = ( k1_mcart_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['35','36'])).

thf('38',plain,
    ( sk_A
    = ( k4_tarski @ sk_A @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['9','37'])).

thf('39',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( X23 = k1_xboole_0 )
      | ~ ( r2_hidden @ X25 @ X23 )
      | ( ( sk_B @ X23 )
       != ( k4_tarski @ X25 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ X0 )
       != sk_A )
      | ~ ( r2_hidden @ sk_A @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( sk_B @ ( k1_tarski @ sk_A ) )
     != sk_A ) ),
    inference('sup-',[status(thm)],['1','40'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('42',plain,(
    ! [X5: $i] :
      ( ( k2_tarski @ X5 @ X5 )
      = ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('43',plain,(
    ! [X23: $i] :
      ( ( X23 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X23 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('44',plain,(
    ! [X5: $i] :
      ( ( k2_tarski @ X5 @ X5 )
      = ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('45',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X0 ) )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( ( k2_tarski @ X0 @ X0 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k2_tarski @ X0 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( k2_tarski @ X0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['42','47'])).

thf('49',plain,(
    ! [X5: $i] :
      ( ( k2_tarski @ X5 @ X5 )
      = ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('50',plain,(
    ! [X0: $i] :
      ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('51',plain,(
    ! [X0: $i] :
      ~ ( r1_tarski @ ( k2_tarski @ X0 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( sk_B @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( sk_A != sk_A ) ),
    inference(demod,[status(thm)],['41','54'])).

thf('56',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X0: $i] :
      ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('58',plain,(
    ~ ( r1_tarski @ k1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('60',plain,(
    $false ),
    inference(demod,[status(thm)],['58','59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Vo3WazMAOu
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:50:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.22/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.51  % Solved by: fo/fo7.sh
% 0.22/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.51  % done 98 iterations in 0.027s
% 0.22/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.51  % SZS output start Refutation
% 0.22/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.51  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.22/0.51  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.51  thf(sk_B_type, type, sk_B: $i > $i).
% 0.22/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.51  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.22/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.51  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.22/0.51  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.22/0.51  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.22/0.51  thf(d1_tarski, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.22/0.51       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.22/0.51  thf('0', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.51         (((X1) != (X0)) | (r2_hidden @ X1 @ X2) | ((X2) != (k1_tarski @ X0)))),
% 0.22/0.51      inference('cnf', [status(esa)], [d1_tarski])).
% 0.22/0.51  thf('1', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.22/0.51      inference('simplify', [status(thm)], ['0'])).
% 0.22/0.51  thf(t20_mcart_1, conjecture,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.22/0.51       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 0.22/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.51    (~( ![A:$i]:
% 0.22/0.51        ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.22/0.51          ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ) )),
% 0.22/0.51    inference('cnf.neg', [status(esa)], [t20_mcart_1])).
% 0.22/0.51  thf('2', plain, (((sk_A) = (k4_tarski @ sk_B_1 @ sk_C_1))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(t7_mcart_1, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.22/0.51       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.22/0.51  thf('3', plain,
% 0.22/0.51      (![X20 : $i, X21 : $i]: ((k1_mcart_1 @ (k4_tarski @ X20 @ X21)) = (X20))),
% 0.22/0.51      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.22/0.51  thf('4', plain, (((k1_mcart_1 @ sk_A) = (sk_B_1))),
% 0.22/0.51      inference('sup+', [status(thm)], ['2', '3'])).
% 0.22/0.51  thf('5', plain,
% 0.22/0.51      ((((sk_A) = (k1_mcart_1 @ sk_A)) | ((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('6', plain,
% 0.22/0.51      ((((sk_A) = (k1_mcart_1 @ sk_A))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.22/0.51      inference('split', [status(esa)], ['5'])).
% 0.22/0.51  thf('7', plain,
% 0.22/0.51      ((((sk_A) = (sk_B_1))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.22/0.51      inference('sup+', [status(thm)], ['4', '6'])).
% 0.22/0.51  thf('8', plain, (((sk_A) = (k4_tarski @ sk_B_1 @ sk_C_1))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('9', plain,
% 0.22/0.51      ((((sk_A) = (k4_tarski @ sk_A @ sk_C_1)))
% 0.22/0.51         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.22/0.51      inference('sup+', [status(thm)], ['7', '8'])).
% 0.22/0.51  thf('10', plain, (((sk_A) = (k4_tarski @ sk_B_1 @ sk_C_1))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('11', plain,
% 0.22/0.51      (![X20 : $i, X22 : $i]: ((k2_mcart_1 @ (k4_tarski @ X20 @ X22)) = (X22))),
% 0.22/0.51      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.22/0.51  thf('12', plain, (((k2_mcart_1 @ sk_A) = (sk_C_1))),
% 0.22/0.51      inference('sup+', [status(thm)], ['10', '11'])).
% 0.22/0.51  thf('13', plain,
% 0.22/0.51      ((((sk_A) = (k2_mcart_1 @ sk_A))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.22/0.51      inference('split', [status(esa)], ['5'])).
% 0.22/0.51  thf('14', plain,
% 0.22/0.51      ((((sk_A) = (sk_C_1))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.22/0.51      inference('sup+', [status(thm)], ['12', '13'])).
% 0.22/0.51  thf('15', plain, (((sk_A) = (k4_tarski @ sk_B_1 @ sk_C_1))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('16', plain,
% 0.22/0.51      ((((sk_A) = (k4_tarski @ sk_B_1 @ sk_A)))
% 0.22/0.51         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.22/0.51      inference('sup+', [status(thm)], ['14', '15'])).
% 0.22/0.51  thf(t9_mcart_1, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.22/0.51          ( ![B:$i]:
% 0.22/0.51            ( ~( ( r2_hidden @ B @ A ) & 
% 0.22/0.51                 ( ![C:$i,D:$i]:
% 0.22/0.51                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.22/0.51                        ( ( B ) = ( k4_tarski @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.51  thf('17', plain,
% 0.22/0.51      (![X23 : $i]:
% 0.22/0.51         (((X23) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X23) @ X23))),
% 0.22/0.51      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.22/0.51  thf('18', plain,
% 0.22/0.51      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.22/0.51         (~ (r2_hidden @ X3 @ X2) | ((X3) = (X0)) | ((X2) != (k1_tarski @ X0)))),
% 0.22/0.51      inference('cnf', [status(esa)], [d1_tarski])).
% 0.22/0.51  thf('19', plain,
% 0.22/0.51      (![X0 : $i, X3 : $i]:
% 0.22/0.51         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.22/0.51      inference('simplify', [status(thm)], ['18'])).
% 0.22/0.51  thf('20', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.22/0.51          | ((sk_B @ (k1_tarski @ X0)) = (X0)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['17', '19'])).
% 0.22/0.51  thf('21', plain,
% 0.22/0.51      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.22/0.51         (((X23) = (k1_xboole_0))
% 0.22/0.51          | ~ (r2_hidden @ X24 @ X23)
% 0.22/0.51          | ((sk_B @ X23) != (k4_tarski @ X25 @ X24)))),
% 0.22/0.51      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.22/0.51  thf('22', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.51         (((X0) != (k4_tarski @ X2 @ X1))
% 0.22/0.51          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.22/0.51          | ~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.22/0.51          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['20', '21'])).
% 0.22/0.51  thf('23', plain,
% 0.22/0.51      (![X1 : $i, X2 : $i]:
% 0.22/0.51         (~ (r2_hidden @ X1 @ (k1_tarski @ (k4_tarski @ X2 @ X1)))
% 0.22/0.51          | ((k1_tarski @ (k4_tarski @ X2 @ X1)) = (k1_xboole_0)))),
% 0.22/0.51      inference('simplify', [status(thm)], ['22'])).
% 0.22/0.51  thf('24', plain,
% 0.22/0.51      (((~ (r2_hidden @ sk_A @ (k1_tarski @ sk_A))
% 0.22/0.51         | ((k1_tarski @ (k4_tarski @ sk_B_1 @ sk_A)) = (k1_xboole_0))))
% 0.22/0.51         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.22/0.51      inference('sup-', [status(thm)], ['16', '23'])).
% 0.22/0.51  thf('25', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.22/0.51      inference('simplify', [status(thm)], ['0'])).
% 0.22/0.51  thf('26', plain,
% 0.22/0.51      ((((sk_A) = (k4_tarski @ sk_B_1 @ sk_A)))
% 0.22/0.51         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.22/0.51      inference('sup+', [status(thm)], ['14', '15'])).
% 0.22/0.51  thf('27', plain,
% 0.22/0.51      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 0.22/0.51         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.22/0.51      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.22/0.51  thf('28', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.22/0.51      inference('simplify', [status(thm)], ['0'])).
% 0.22/0.51  thf(t7_ordinal1, axiom,
% 0.22/0.51    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.51  thf('29', plain,
% 0.22/0.51      (![X18 : $i, X19 : $i]:
% 0.22/0.51         (~ (r2_hidden @ X18 @ X19) | ~ (r1_tarski @ X19 @ X18))),
% 0.22/0.51      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.22/0.51  thf('30', plain, (![X0 : $i]: ~ (r1_tarski @ (k1_tarski @ X0) @ X0)),
% 0.22/0.51      inference('sup-', [status(thm)], ['28', '29'])).
% 0.22/0.51  thf('31', plain,
% 0.22/0.51      ((~ (r1_tarski @ k1_xboole_0 @ sk_A))
% 0.22/0.51         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.22/0.51      inference('sup-', [status(thm)], ['27', '30'])).
% 0.22/0.51  thf(t4_subset_1, axiom,
% 0.22/0.51    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.22/0.51  thf('32', plain,
% 0.22/0.51      (![X11 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X11))),
% 0.22/0.51      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.22/0.51  thf(t3_subset, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.22/0.51  thf('33', plain,
% 0.22/0.51      (![X12 : $i, X13 : $i]:
% 0.22/0.51         ((r1_tarski @ X12 @ X13) | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.22/0.51      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.51  thf('34', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.22/0.51      inference('sup-', [status(thm)], ['32', '33'])).
% 0.22/0.51  thf('35', plain, (~ (((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.22/0.51      inference('demod', [status(thm)], ['31', '34'])).
% 0.22/0.51  thf('36', plain,
% 0.22/0.51      ((((sk_A) = (k1_mcart_1 @ sk_A))) | (((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.22/0.51      inference('split', [status(esa)], ['5'])).
% 0.22/0.51  thf('37', plain, ((((sk_A) = (k1_mcart_1 @ sk_A)))),
% 0.22/0.51      inference('sat_resolution*', [status(thm)], ['35', '36'])).
% 0.22/0.51  thf('38', plain, (((sk_A) = (k4_tarski @ sk_A @ sk_C_1))),
% 0.22/0.51      inference('simpl_trail', [status(thm)], ['9', '37'])).
% 0.22/0.51  thf('39', plain,
% 0.22/0.51      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.22/0.51         (((X23) = (k1_xboole_0))
% 0.22/0.51          | ~ (r2_hidden @ X25 @ X23)
% 0.22/0.51          | ((sk_B @ X23) != (k4_tarski @ X25 @ X24)))),
% 0.22/0.51      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.22/0.51  thf('40', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (((sk_B @ X0) != (sk_A))
% 0.22/0.51          | ~ (r2_hidden @ sk_A @ X0)
% 0.22/0.51          | ((X0) = (k1_xboole_0)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['38', '39'])).
% 0.22/0.51  thf('41', plain,
% 0.22/0.51      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.22/0.51        | ((sk_B @ (k1_tarski @ sk_A)) != (sk_A)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['1', '40'])).
% 0.22/0.51  thf(t69_enumset1, axiom,
% 0.22/0.51    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.22/0.51  thf('42', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 0.22/0.51      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.51  thf('43', plain,
% 0.22/0.51      (![X23 : $i]:
% 0.22/0.51         (((X23) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X23) @ X23))),
% 0.22/0.51      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.22/0.51  thf('44', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 0.22/0.51      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.51  thf('45', plain,
% 0.22/0.51      (![X0 : $i, X3 : $i]:
% 0.22/0.51         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.22/0.51      inference('simplify', [status(thm)], ['18'])).
% 0.22/0.51  thf('46', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]:
% 0.22/0.51         (~ (r2_hidden @ X1 @ (k2_tarski @ X0 @ X0)) | ((X1) = (X0)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['44', '45'])).
% 0.22/0.51  thf('47', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (((k2_tarski @ X0 @ X0) = (k1_xboole_0))
% 0.22/0.51          | ((sk_B @ (k2_tarski @ X0 @ X0)) = (X0)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['43', '46'])).
% 0.22/0.51  thf('48', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (((sk_B @ (k1_tarski @ X0)) = (X0))
% 0.22/0.51          | ((k2_tarski @ X0 @ X0) = (k1_xboole_0)))),
% 0.22/0.51      inference('sup+', [status(thm)], ['42', '47'])).
% 0.22/0.51  thf('49', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 0.22/0.51      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.51  thf('50', plain, (![X0 : $i]: ~ (r1_tarski @ (k1_tarski @ X0) @ X0)),
% 0.22/0.51      inference('sup-', [status(thm)], ['28', '29'])).
% 0.22/0.51  thf('51', plain, (![X0 : $i]: ~ (r1_tarski @ (k2_tarski @ X0 @ X0) @ X0)),
% 0.22/0.51      inference('sup-', [status(thm)], ['49', '50'])).
% 0.22/0.51  thf('52', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (r1_tarski @ k1_xboole_0 @ X0) | ((sk_B @ (k1_tarski @ X0)) = (X0)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['48', '51'])).
% 0.22/0.51  thf('53', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.22/0.51      inference('sup-', [status(thm)], ['32', '33'])).
% 0.22/0.51  thf('54', plain, (![X0 : $i]: ((sk_B @ (k1_tarski @ X0)) = (X0))),
% 0.22/0.51      inference('demod', [status(thm)], ['52', '53'])).
% 0.22/0.51  thf('55', plain,
% 0.22/0.51      ((((k1_tarski @ sk_A) = (k1_xboole_0)) | ((sk_A) != (sk_A)))),
% 0.22/0.51      inference('demod', [status(thm)], ['41', '54'])).
% 0.22/0.51  thf('56', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.22/0.51      inference('simplify', [status(thm)], ['55'])).
% 0.22/0.51  thf('57', plain, (![X0 : $i]: ~ (r1_tarski @ (k1_tarski @ X0) @ X0)),
% 0.22/0.51      inference('sup-', [status(thm)], ['28', '29'])).
% 0.22/0.51  thf('58', plain, (~ (r1_tarski @ k1_xboole_0 @ sk_A)),
% 0.22/0.51      inference('sup-', [status(thm)], ['56', '57'])).
% 0.22/0.51  thf('59', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.22/0.51      inference('sup-', [status(thm)], ['32', '33'])).
% 0.22/0.51  thf('60', plain, ($false), inference('demod', [status(thm)], ['58', '59'])).
% 0.22/0.51  
% 0.22/0.51  % SZS output end Refutation
% 0.22/0.51  
% 0.22/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
