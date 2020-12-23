%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4iqZkvP3oh

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:02 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 169 expanded)
%              Number of leaves         :   20 (  55 expanded)
%              Depth                    :   17
%              Number of atoms          :  427 (1373 expanded)
%              Number of equality atoms :   73 ( 252 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    = ( k4_tarski @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('1',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X21 @ X22 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('2',plain,
    ( ( k1_mcart_1 @ sk_A )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ( sk_A = sk_B_1 )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['2','4'])).

thf('6',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_A @ sk_C_1 ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

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

thf('8',plain,(
    ! [X24: $i] :
      ( ( X24 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X24 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('9',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X2 )
      | ( X3 = X0 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('10',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('13',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X21: $i,X23: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X21 @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('16',plain,
    ( ( k2_mcart_1 @ sk_A )
    = sk_C_1 ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( sk_A
      = ( k2_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('18',plain,
    ( ( sk_A = sk_C_1 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_B_1 @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( X24 = k1_xboole_0 )
      | ~ ( r2_hidden @ X25 @ X24 )
      | ( ( sk_B @ X24 )
       != ( k4_tarski @ X26 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('22',plain,
    ( ! [X0: $i] :
        ( ( ( sk_B @ X0 )
         != sk_A )
        | ~ ( r2_hidden @ sk_A @ X0 )
        | ( X0 = k1_xboole_0 ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k1_tarski @ sk_A ) )
       != sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','22'])).

thf('24',plain,
    ( ( ( sk_A != sk_A )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','23'])).

thf('25',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('27',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X19 @ X20 )
      | ~ ( r1_tarski @ X20 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('28',plain,(
    ! [X0: $i] :
      ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_A )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('30',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('31',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('32',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    sk_A
 != ( k2_mcart_1 @ sk_A ) ),
    inference(demod,[status(thm)],['29','32'])).

thf('34',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('35',plain,
    ( sk_A
    = ( k1_mcart_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['33','34'])).

thf('36',plain,
    ( sk_A
    = ( k4_tarski @ sk_A @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['7','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('38',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( X24 = k1_xboole_0 )
      | ~ ( r2_hidden @ X26 @ X24 )
      | ( ( sk_B @ X24 )
       != ( k4_tarski @ X26 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( k4_tarski @ X2 @ X1 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X2 @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k1_tarski @ ( k4_tarski @ X2 @ X1 ) ) )
      | ( ( k1_tarski @ ( k4_tarski @ X2 @ X1 ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ ( k4_tarski @ sk_A @ sk_C_1 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('43',plain,
    ( sk_A
    = ( k4_tarski @ sk_A @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['7','35'])).

thf('44',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('46',plain,(
    ~ ( r1_tarski @ k1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('48',plain,(
    $false ),
    inference(demod,[status(thm)],['46','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4iqZkvP3oh
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 09:49:41 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.33  % Python version: Python 3.6.8
% 0.12/0.33  % Running in FO mode
% 0.18/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.18/0.46  % Solved by: fo/fo7.sh
% 0.18/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.18/0.46  % done 63 iterations in 0.021s
% 0.18/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.18/0.46  % SZS output start Refutation
% 0.18/0.46  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.18/0.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.18/0.46  thf(sk_B_type, type, sk_B: $i > $i).
% 0.18/0.46  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.18/0.46  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.18/0.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.18/0.46  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.18/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.18/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.18/0.46  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.18/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.18/0.46  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.18/0.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.18/0.46  thf(t20_mcart_1, conjecture,
% 0.18/0.46    (![A:$i]:
% 0.18/0.46     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.18/0.46       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 0.18/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.18/0.46    (~( ![A:$i]:
% 0.18/0.46        ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.18/0.46          ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ) )),
% 0.18/0.46    inference('cnf.neg', [status(esa)], [t20_mcart_1])).
% 0.18/0.46  thf('0', plain, (((sk_A) = (k4_tarski @ sk_B_1 @ sk_C_1))),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf(t7_mcart_1, axiom,
% 0.18/0.46    (![A:$i,B:$i]:
% 0.18/0.46     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.18/0.46       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.18/0.46  thf('1', plain,
% 0.18/0.46      (![X21 : $i, X22 : $i]: ((k1_mcart_1 @ (k4_tarski @ X21 @ X22)) = (X21))),
% 0.18/0.46      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.18/0.46  thf('2', plain, (((k1_mcart_1 @ sk_A) = (sk_B_1))),
% 0.18/0.46      inference('sup+', [status(thm)], ['0', '1'])).
% 0.18/0.46  thf('3', plain,
% 0.18/0.46      ((((sk_A) = (k1_mcart_1 @ sk_A)) | ((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('4', plain,
% 0.18/0.46      ((((sk_A) = (k1_mcart_1 @ sk_A))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.18/0.46      inference('split', [status(esa)], ['3'])).
% 0.18/0.46  thf('5', plain,
% 0.18/0.46      ((((sk_A) = (sk_B_1))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.18/0.46      inference('sup+', [status(thm)], ['2', '4'])).
% 0.18/0.46  thf('6', plain, (((sk_A) = (k4_tarski @ sk_B_1 @ sk_C_1))),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('7', plain,
% 0.18/0.46      ((((sk_A) = (k4_tarski @ sk_A @ sk_C_1)))
% 0.18/0.46         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.18/0.46      inference('sup+', [status(thm)], ['5', '6'])).
% 0.18/0.46  thf(t9_mcart_1, axiom,
% 0.18/0.46    (![A:$i]:
% 0.18/0.46     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.18/0.46          ( ![B:$i]:
% 0.18/0.46            ( ~( ( r2_hidden @ B @ A ) & 
% 0.18/0.46                 ( ![C:$i,D:$i]:
% 0.18/0.46                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.18/0.46                        ( ( B ) = ( k4_tarski @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.18/0.46  thf('8', plain,
% 0.18/0.46      (![X24 : $i]:
% 0.18/0.46         (((X24) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X24) @ X24))),
% 0.18/0.46      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.18/0.46  thf(d1_tarski, axiom,
% 0.18/0.46    (![A:$i,B:$i]:
% 0.18/0.46     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.18/0.46       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.18/0.46  thf('9', plain,
% 0.18/0.46      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.18/0.46         (~ (r2_hidden @ X3 @ X2) | ((X3) = (X0)) | ((X2) != (k1_tarski @ X0)))),
% 0.18/0.46      inference('cnf', [status(esa)], [d1_tarski])).
% 0.18/0.46  thf('10', plain,
% 0.18/0.46      (![X0 : $i, X3 : $i]:
% 0.18/0.46         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.18/0.46      inference('simplify', [status(thm)], ['9'])).
% 0.18/0.46  thf('11', plain,
% 0.18/0.46      (![X0 : $i]:
% 0.18/0.46         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.18/0.46          | ((sk_B @ (k1_tarski @ X0)) = (X0)))),
% 0.18/0.46      inference('sup-', [status(thm)], ['8', '10'])).
% 0.18/0.46  thf('12', plain,
% 0.18/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.18/0.46         (((X1) != (X0)) | (r2_hidden @ X1 @ X2) | ((X2) != (k1_tarski @ X0)))),
% 0.18/0.46      inference('cnf', [status(esa)], [d1_tarski])).
% 0.18/0.46  thf('13', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.18/0.46      inference('simplify', [status(thm)], ['12'])).
% 0.18/0.46  thf('14', plain, (((sk_A) = (k4_tarski @ sk_B_1 @ sk_C_1))),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('15', plain,
% 0.18/0.46      (![X21 : $i, X23 : $i]: ((k2_mcart_1 @ (k4_tarski @ X21 @ X23)) = (X23))),
% 0.18/0.46      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.18/0.46  thf('16', plain, (((k2_mcart_1 @ sk_A) = (sk_C_1))),
% 0.18/0.46      inference('sup+', [status(thm)], ['14', '15'])).
% 0.18/0.46  thf('17', plain,
% 0.18/0.46      ((((sk_A) = (k2_mcart_1 @ sk_A))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.18/0.46      inference('split', [status(esa)], ['3'])).
% 0.18/0.46  thf('18', plain,
% 0.18/0.46      ((((sk_A) = (sk_C_1))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.18/0.46      inference('sup+', [status(thm)], ['16', '17'])).
% 0.18/0.46  thf('19', plain, (((sk_A) = (k4_tarski @ sk_B_1 @ sk_C_1))),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('20', plain,
% 0.18/0.46      ((((sk_A) = (k4_tarski @ sk_B_1 @ sk_A)))
% 0.18/0.46         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.18/0.46      inference('sup+', [status(thm)], ['18', '19'])).
% 0.18/0.46  thf('21', plain,
% 0.18/0.46      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.18/0.46         (((X24) = (k1_xboole_0))
% 0.18/0.46          | ~ (r2_hidden @ X25 @ X24)
% 0.18/0.46          | ((sk_B @ X24) != (k4_tarski @ X26 @ X25)))),
% 0.18/0.46      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.18/0.46  thf('22', plain,
% 0.18/0.46      ((![X0 : $i]:
% 0.18/0.46          (((sk_B @ X0) != (sk_A))
% 0.18/0.46           | ~ (r2_hidden @ sk_A @ X0)
% 0.18/0.46           | ((X0) = (k1_xboole_0))))
% 0.18/0.46         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.18/0.46      inference('sup-', [status(thm)], ['20', '21'])).
% 0.18/0.46  thf('23', plain,
% 0.18/0.46      (((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.18/0.46         | ((sk_B @ (k1_tarski @ sk_A)) != (sk_A))))
% 0.18/0.46         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.18/0.46      inference('sup-', [status(thm)], ['13', '22'])).
% 0.18/0.46  thf('24', plain,
% 0.18/0.46      (((((sk_A) != (sk_A))
% 0.18/0.46         | ((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.18/0.46         | ((k1_tarski @ sk_A) = (k1_xboole_0))))
% 0.18/0.46         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.18/0.46      inference('sup-', [status(thm)], ['11', '23'])).
% 0.18/0.46  thf('25', plain,
% 0.18/0.46      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 0.18/0.46         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.18/0.46      inference('simplify', [status(thm)], ['24'])).
% 0.18/0.46  thf('26', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.18/0.46      inference('simplify', [status(thm)], ['12'])).
% 0.18/0.46  thf(t7_ordinal1, axiom,
% 0.18/0.46    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.18/0.46  thf('27', plain,
% 0.18/0.46      (![X19 : $i, X20 : $i]:
% 0.18/0.46         (~ (r2_hidden @ X19 @ X20) | ~ (r1_tarski @ X20 @ X19))),
% 0.18/0.46      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.18/0.46  thf('28', plain, (![X0 : $i]: ~ (r1_tarski @ (k1_tarski @ X0) @ X0)),
% 0.18/0.46      inference('sup-', [status(thm)], ['26', '27'])).
% 0.18/0.46  thf('29', plain,
% 0.18/0.46      ((~ (r1_tarski @ k1_xboole_0 @ sk_A))
% 0.18/0.46         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.18/0.46      inference('sup-', [status(thm)], ['25', '28'])).
% 0.18/0.46  thf(t4_subset_1, axiom,
% 0.18/0.46    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.18/0.46  thf('30', plain,
% 0.18/0.46      (![X12 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X12))),
% 0.18/0.46      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.18/0.46  thf(t3_subset, axiom,
% 0.18/0.46    (![A:$i,B:$i]:
% 0.18/0.46     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.18/0.46  thf('31', plain,
% 0.18/0.46      (![X13 : $i, X14 : $i]:
% 0.18/0.46         ((r1_tarski @ X13 @ X14) | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 0.18/0.46      inference('cnf', [status(esa)], [t3_subset])).
% 0.18/0.46  thf('32', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.18/0.46      inference('sup-', [status(thm)], ['30', '31'])).
% 0.18/0.46  thf('33', plain, (~ (((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.18/0.46      inference('demod', [status(thm)], ['29', '32'])).
% 0.18/0.46  thf('34', plain,
% 0.18/0.46      ((((sk_A) = (k1_mcart_1 @ sk_A))) | (((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.18/0.46      inference('split', [status(esa)], ['3'])).
% 0.18/0.46  thf('35', plain, ((((sk_A) = (k1_mcart_1 @ sk_A)))),
% 0.18/0.46      inference('sat_resolution*', [status(thm)], ['33', '34'])).
% 0.18/0.46  thf('36', plain, (((sk_A) = (k4_tarski @ sk_A @ sk_C_1))),
% 0.18/0.46      inference('simpl_trail', [status(thm)], ['7', '35'])).
% 0.18/0.46  thf('37', plain,
% 0.18/0.46      (![X0 : $i]:
% 0.18/0.46         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.18/0.46          | ((sk_B @ (k1_tarski @ X0)) = (X0)))),
% 0.18/0.46      inference('sup-', [status(thm)], ['8', '10'])).
% 0.18/0.46  thf('38', plain,
% 0.18/0.46      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.18/0.46         (((X24) = (k1_xboole_0))
% 0.18/0.46          | ~ (r2_hidden @ X26 @ X24)
% 0.18/0.46          | ((sk_B @ X24) != (k4_tarski @ X26 @ X25)))),
% 0.18/0.46      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.18/0.46  thf('39', plain,
% 0.18/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.18/0.46         (((X0) != (k4_tarski @ X2 @ X1))
% 0.18/0.46          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.18/0.46          | ~ (r2_hidden @ X2 @ (k1_tarski @ X0))
% 0.18/0.46          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.18/0.46      inference('sup-', [status(thm)], ['37', '38'])).
% 0.18/0.46  thf('40', plain,
% 0.18/0.46      (![X1 : $i, X2 : $i]:
% 0.18/0.46         (~ (r2_hidden @ X2 @ (k1_tarski @ (k4_tarski @ X2 @ X1)))
% 0.18/0.46          | ((k1_tarski @ (k4_tarski @ X2 @ X1)) = (k1_xboole_0)))),
% 0.18/0.46      inference('simplify', [status(thm)], ['39'])).
% 0.18/0.46  thf('41', plain,
% 0.18/0.46      ((~ (r2_hidden @ sk_A @ (k1_tarski @ sk_A))
% 0.18/0.46        | ((k1_tarski @ (k4_tarski @ sk_A @ sk_C_1)) = (k1_xboole_0)))),
% 0.18/0.46      inference('sup-', [status(thm)], ['36', '40'])).
% 0.18/0.46  thf('42', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.18/0.46      inference('simplify', [status(thm)], ['12'])).
% 0.18/0.46  thf('43', plain, (((sk_A) = (k4_tarski @ sk_A @ sk_C_1))),
% 0.18/0.46      inference('simpl_trail', [status(thm)], ['7', '35'])).
% 0.18/0.46  thf('44', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.18/0.46      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.18/0.46  thf('45', plain, (![X0 : $i]: ~ (r1_tarski @ (k1_tarski @ X0) @ X0)),
% 0.18/0.46      inference('sup-', [status(thm)], ['26', '27'])).
% 0.18/0.46  thf('46', plain, (~ (r1_tarski @ k1_xboole_0 @ sk_A)),
% 0.18/0.46      inference('sup-', [status(thm)], ['44', '45'])).
% 0.18/0.46  thf('47', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.18/0.46      inference('sup-', [status(thm)], ['30', '31'])).
% 0.18/0.46  thf('48', plain, ($false), inference('demod', [status(thm)], ['46', '47'])).
% 0.18/0.46  
% 0.18/0.46  % SZS output end Refutation
% 0.18/0.46  
% 0.18/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
