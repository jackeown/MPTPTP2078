%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8cpKqTEdUr

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:08 EST 2020

% Result     : Theorem 0.66s
% Output     : Refutation 0.66s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 163 expanded)
%              Number of leaves         :   19 (  57 expanded)
%              Depth                    :   21
%              Number of atoms          :  561 (1386 expanded)
%              Number of equality atoms :   49 ( 147 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k4_xboole_0 @ X26 @ ( k1_tarski @ X27 ) )
        = X26 )
      | ( r2_hidden @ X27 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('2',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('3',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X9 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('4',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X25 @ X26 )
      | ( ( k4_xboole_0 @ X26 @ ( k1_tarski @ X25 ) )
       != X26 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['2','6'])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('8',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r2_xboole_0 @ X4 @ X6 )
      | ( X4 = X6 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( r2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_xboole_0 @ A @ B )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ B )
              & ~ ( r2_hidden @ C @ A ) ) ) )).

thf('10',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r2_xboole_0 @ X7 @ X8 )
      | ( r2_hidden @ ( sk_C_1 @ X8 @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('12',plain,(
    ! [X20: $i,X21: $i,X22: $i,X24: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X20 @ X22 ) @ ( k2_zfmisc_1 @ X21 @ X24 ) )
      | ~ ( r2_hidden @ X22 @ X24 )
      | ~ ( r2_hidden @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ ( sk_C_1 @ X0 @ k1_xboole_0 ) ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) )
        = X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ ( sk_C_1 @ X2 @ k1_xboole_0 ) ) @ ( k2_zfmisc_1 @ X0 @ X2 ) )
      | ( k1_xboole_0 = X2 ) ) ),
    inference('sup-',[status(thm)],['1','13'])).

thf(t114_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = ( k2_zfmisc_1 @ B @ A ) )
     => ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 )
        | ( A = B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k2_zfmisc_1 @ A @ B )
          = ( k2_zfmisc_1 @ B @ A ) )
       => ( ( A = k1_xboole_0 )
          | ( B = k1_xboole_0 )
          | ( A = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t114_zfmisc_1])).

thf('15',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( r2_hidden @ X20 @ X21 )
      | ~ ( r2_hidden @ ( k4_tarski @ X20 @ X22 ) @ ( k2_zfmisc_1 @ X21 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( r2_hidden @ X1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = sk_B )
      | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ X0 ) )
        = sk_A )
      | ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ X0 ) )
        = sk_A )
      | ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ ( sk_C @ sk_B @ X0 ) ) )
        = sk_A )
      | ( r1_tarski @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X25 @ X26 )
      | ( ( k4_xboole_0 @ X26 @ ( k1_tarski @ X25 ) )
       != X26 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( sk_A != sk_A )
      | ( r1_tarski @ X0 @ sk_B )
      | ~ ( r2_hidden @ ( sk_C @ sk_B @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ sk_B @ X0 ) @ sk_A )
      | ( r1_tarski @ X0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['0','25'])).

thf('27',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r2_xboole_0 @ X4 @ X6 )
      | ( X4 = X6 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('29',plain,
    ( ( sk_A = sk_B )
    | ( r2_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    r2_xboole_0 @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k4_xboole_0 @ X26 @ ( k1_tarski @ X27 ) )
        = X26 )
      | ( r2_hidden @ X27 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('33',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r2_xboole_0 @ X7 @ X8 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X8 @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ ( k1_tarski @ ( sk_C_1 @ X1 @ X0 ) ) )
        = X0 )
      | ~ ( r2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ ( sk_C_1 @ sk_B @ sk_A ) ) )
    = sk_A ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X25 @ X26 )
      | ( ( k4_xboole_0 @ X26 @ ( k1_tarski @ X25 ) )
       != X26 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('37',plain,
    ( ( sk_A != sk_A )
    | ~ ( r2_hidden @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ~ ( r2_hidden @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_A ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    r2_xboole_0 @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['29','30'])).

thf('40',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r2_xboole_0 @ X7 @ X8 )
      | ( r2_hidden @ ( sk_C_1 @ X8 @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_0])).

thf('41',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('43',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k4_xboole_0 @ X26 @ ( k1_tarski @ X27 ) )
        = X26 )
      | ( r2_hidden @ X27 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('44',plain,(
    ! [X20: $i,X21: $i,X22: $i,X24: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X20 @ X22 ) @ ( k2_zfmisc_1 @ X21 @ X24 ) )
      | ~ ( r2_hidden @ X22 @ X24 )
      | ~ ( r2_hidden @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) )
        = X0 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X1 ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X2 ) @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( ( k4_xboole_0 @ X1 @ ( k1_tarski @ X2 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf('47',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( r2_hidden @ X22 @ X23 )
      | ~ ( r2_hidden @ ( k4_tarski @ X20 @ X22 ) @ ( k2_zfmisc_1 @ X21 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ X0 ) )
        = sk_B )
      | ( k1_xboole_0 = sk_A )
      | ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ X0 ) )
        = sk_B )
      | ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X25 @ X26 )
      | ( ( k4_xboole_0 @ X26 @ ( k1_tarski @ X25 ) )
       != X26 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( sk_B != sk_B )
      | ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_A ),
    inference('sup-',[status(thm)],['41','55'])).

thf('57',plain,(
    $false ),
    inference(demod,[status(thm)],['38','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8cpKqTEdUr
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:33:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.66/0.91  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.66/0.91  % Solved by: fo/fo7.sh
% 0.66/0.91  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.66/0.91  % done 402 iterations in 0.455s
% 0.66/0.91  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.66/0.91  % SZS output start Refutation
% 0.66/0.91  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.66/0.91  thf(sk_A_type, type, sk_A: $i).
% 0.66/0.91  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.66/0.91  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.66/0.91  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.66/0.91  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.66/0.91  thf(sk_B_type, type, sk_B: $i).
% 0.66/0.91  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.66/0.91  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.66/0.91  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.66/0.91  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.66/0.91  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.66/0.91  thf(d3_tarski, axiom,
% 0.66/0.91    (![A:$i,B:$i]:
% 0.66/0.91     ( ( r1_tarski @ A @ B ) <=>
% 0.66/0.91       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.66/0.91  thf('0', plain,
% 0.66/0.91      (![X1 : $i, X3 : $i]:
% 0.66/0.91         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.66/0.91      inference('cnf', [status(esa)], [d3_tarski])).
% 0.66/0.91  thf(t65_zfmisc_1, axiom,
% 0.66/0.91    (![A:$i,B:$i]:
% 0.66/0.91     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.66/0.91       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.66/0.91  thf('1', plain,
% 0.66/0.91      (![X26 : $i, X27 : $i]:
% 0.66/0.91         (((k4_xboole_0 @ X26 @ (k1_tarski @ X27)) = (X26))
% 0.66/0.91          | (r2_hidden @ X27 @ X26))),
% 0.66/0.91      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.66/0.91  thf('2', plain,
% 0.66/0.91      (![X1 : $i, X3 : $i]:
% 0.66/0.91         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.66/0.91      inference('cnf', [status(esa)], [d3_tarski])).
% 0.66/0.91  thf(t4_boole, axiom,
% 0.66/0.91    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.66/0.91  thf('3', plain,
% 0.66/0.91      (![X9 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 0.66/0.91      inference('cnf', [status(esa)], [t4_boole])).
% 0.66/0.91  thf('4', plain,
% 0.66/0.91      (![X25 : $i, X26 : $i]:
% 0.66/0.91         (~ (r2_hidden @ X25 @ X26)
% 0.66/0.91          | ((k4_xboole_0 @ X26 @ (k1_tarski @ X25)) != (X26)))),
% 0.66/0.91      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.66/0.91  thf('5', plain,
% 0.66/0.91      (![X0 : $i]:
% 0.66/0.91         (((k1_xboole_0) != (k1_xboole_0)) | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 0.66/0.91      inference('sup-', [status(thm)], ['3', '4'])).
% 0.66/0.91  thf('6', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.66/0.91      inference('simplify', [status(thm)], ['5'])).
% 0.66/0.91  thf('7', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.66/0.91      inference('sup-', [status(thm)], ['2', '6'])).
% 0.66/0.91  thf(d8_xboole_0, axiom,
% 0.66/0.91    (![A:$i,B:$i]:
% 0.66/0.91     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.66/0.91       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.66/0.91  thf('8', plain,
% 0.66/0.91      (![X4 : $i, X6 : $i]:
% 0.66/0.91         ((r2_xboole_0 @ X4 @ X6) | ((X4) = (X6)) | ~ (r1_tarski @ X4 @ X6))),
% 0.66/0.91      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.66/0.91  thf('9', plain,
% 0.66/0.91      (![X0 : $i]: (((k1_xboole_0) = (X0)) | (r2_xboole_0 @ k1_xboole_0 @ X0))),
% 0.66/0.91      inference('sup-', [status(thm)], ['7', '8'])).
% 0.66/0.91  thf(t6_xboole_0, axiom,
% 0.66/0.91    (![A:$i,B:$i]:
% 0.66/0.91     ( ~( ( r2_xboole_0 @ A @ B ) & 
% 0.66/0.91          ( ![C:$i]:
% 0.66/0.91            ( ~( ( r2_hidden @ C @ B ) & ( ~( r2_hidden @ C @ A ) ) ) ) ) ) ))).
% 0.66/0.91  thf('10', plain,
% 0.66/0.91      (![X7 : $i, X8 : $i]:
% 0.66/0.91         (~ (r2_xboole_0 @ X7 @ X8) | (r2_hidden @ (sk_C_1 @ X8 @ X7) @ X8))),
% 0.66/0.91      inference('cnf', [status(esa)], [t6_xboole_0])).
% 0.66/0.91  thf('11', plain,
% 0.66/0.91      (![X0 : $i]:
% 0.66/0.91         (((k1_xboole_0) = (X0))
% 0.66/0.91          | (r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0))),
% 0.66/0.91      inference('sup-', [status(thm)], ['9', '10'])).
% 0.66/0.91  thf(l54_zfmisc_1, axiom,
% 0.66/0.91    (![A:$i,B:$i,C:$i,D:$i]:
% 0.66/0.91     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.66/0.91       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.66/0.91  thf('12', plain,
% 0.66/0.91      (![X20 : $i, X21 : $i, X22 : $i, X24 : $i]:
% 0.66/0.91         ((r2_hidden @ (k4_tarski @ X20 @ X22) @ (k2_zfmisc_1 @ X21 @ X24))
% 0.66/0.91          | ~ (r2_hidden @ X22 @ X24)
% 0.66/0.91          | ~ (r2_hidden @ X20 @ X21))),
% 0.66/0.91      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.66/0.91  thf('13', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.91         (((k1_xboole_0) = (X0))
% 0.66/0.91          | ~ (r2_hidden @ X2 @ X1)
% 0.66/0.91          | (r2_hidden @ (k4_tarski @ X2 @ (sk_C_1 @ X0 @ k1_xboole_0)) @ 
% 0.66/0.91             (k2_zfmisc_1 @ X1 @ X0)))),
% 0.66/0.91      inference('sup-', [status(thm)], ['11', '12'])).
% 0.66/0.91  thf('14', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.91         (((k4_xboole_0 @ X0 @ (k1_tarski @ X1)) = (X0))
% 0.66/0.91          | (r2_hidden @ (k4_tarski @ X1 @ (sk_C_1 @ X2 @ k1_xboole_0)) @ 
% 0.66/0.91             (k2_zfmisc_1 @ X0 @ X2))
% 0.66/0.91          | ((k1_xboole_0) = (X2)))),
% 0.66/0.91      inference('sup-', [status(thm)], ['1', '13'])).
% 0.66/0.91  thf(t114_zfmisc_1, conjecture,
% 0.66/0.91    (![A:$i,B:$i]:
% 0.66/0.91     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ B @ A ) ) =>
% 0.66/0.91       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.66/0.91         ( ( A ) = ( B ) ) ) ))).
% 0.66/0.91  thf(zf_stmt_0, negated_conjecture,
% 0.66/0.91    (~( ![A:$i,B:$i]:
% 0.66/0.91        ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ B @ A ) ) =>
% 0.66/0.91          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.66/0.91            ( ( A ) = ( B ) ) ) ) )),
% 0.66/0.91    inference('cnf.neg', [status(esa)], [t114_zfmisc_1])).
% 0.66/0.91  thf('15', plain,
% 0.66/0.91      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_B @ sk_A))),
% 0.66/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.91  thf('16', plain,
% 0.66/0.91      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.66/0.91         ((r2_hidden @ X20 @ X21)
% 0.66/0.91          | ~ (r2_hidden @ (k4_tarski @ X20 @ X22) @ (k2_zfmisc_1 @ X21 @ X23)))),
% 0.66/0.91      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.66/0.91  thf('17', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i]:
% 0.66/0.91         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.66/0.91          | (r2_hidden @ X1 @ sk_B))),
% 0.66/0.91      inference('sup-', [status(thm)], ['15', '16'])).
% 0.66/0.91  thf('18', plain,
% 0.66/0.91      (![X0 : $i]:
% 0.66/0.91         (((k1_xboole_0) = (sk_B))
% 0.66/0.91          | ((k4_xboole_0 @ sk_A @ (k1_tarski @ X0)) = (sk_A))
% 0.66/0.91          | (r2_hidden @ X0 @ sk_B))),
% 0.66/0.91      inference('sup-', [status(thm)], ['14', '17'])).
% 0.66/0.91  thf('19', plain, (((sk_B) != (k1_xboole_0))),
% 0.66/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.91  thf('20', plain,
% 0.66/0.91      (![X0 : $i]:
% 0.66/0.91         (((k4_xboole_0 @ sk_A @ (k1_tarski @ X0)) = (sk_A))
% 0.66/0.91          | (r2_hidden @ X0 @ sk_B))),
% 0.66/0.91      inference('simplify_reflect-', [status(thm)], ['18', '19'])).
% 0.66/0.91  thf('21', plain,
% 0.66/0.91      (![X1 : $i, X3 : $i]:
% 0.66/0.91         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.66/0.91      inference('cnf', [status(esa)], [d3_tarski])).
% 0.66/0.91  thf('22', plain,
% 0.66/0.91      (![X0 : $i]:
% 0.66/0.91         (((k4_xboole_0 @ sk_A @ (k1_tarski @ (sk_C @ sk_B @ X0))) = (sk_A))
% 0.66/0.91          | (r1_tarski @ X0 @ sk_B))),
% 0.66/0.91      inference('sup-', [status(thm)], ['20', '21'])).
% 0.66/0.91  thf('23', plain,
% 0.66/0.91      (![X25 : $i, X26 : $i]:
% 0.66/0.91         (~ (r2_hidden @ X25 @ X26)
% 0.66/0.91          | ((k4_xboole_0 @ X26 @ (k1_tarski @ X25)) != (X26)))),
% 0.66/0.91      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.66/0.91  thf('24', plain,
% 0.66/0.91      (![X0 : $i]:
% 0.66/0.91         (((sk_A) != (sk_A))
% 0.66/0.91          | (r1_tarski @ X0 @ sk_B)
% 0.66/0.91          | ~ (r2_hidden @ (sk_C @ sk_B @ X0) @ sk_A))),
% 0.66/0.91      inference('sup-', [status(thm)], ['22', '23'])).
% 0.66/0.91  thf('25', plain,
% 0.66/0.91      (![X0 : $i]:
% 0.66/0.91         (~ (r2_hidden @ (sk_C @ sk_B @ X0) @ sk_A) | (r1_tarski @ X0 @ sk_B))),
% 0.66/0.91      inference('simplify', [status(thm)], ['24'])).
% 0.66/0.91  thf('26', plain, (((r1_tarski @ sk_A @ sk_B) | (r1_tarski @ sk_A @ sk_B))),
% 0.66/0.91      inference('sup-', [status(thm)], ['0', '25'])).
% 0.66/0.91  thf('27', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.66/0.91      inference('simplify', [status(thm)], ['26'])).
% 0.66/0.91  thf('28', plain,
% 0.66/0.91      (![X4 : $i, X6 : $i]:
% 0.66/0.91         ((r2_xboole_0 @ X4 @ X6) | ((X4) = (X6)) | ~ (r1_tarski @ X4 @ X6))),
% 0.66/0.91      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.66/0.91  thf('29', plain, ((((sk_A) = (sk_B)) | (r2_xboole_0 @ sk_A @ sk_B))),
% 0.66/0.91      inference('sup-', [status(thm)], ['27', '28'])).
% 0.66/0.91  thf('30', plain, (((sk_A) != (sk_B))),
% 0.66/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.91  thf('31', plain, ((r2_xboole_0 @ sk_A @ sk_B)),
% 0.66/0.91      inference('simplify_reflect-', [status(thm)], ['29', '30'])).
% 0.66/0.91  thf('32', plain,
% 0.66/0.91      (![X26 : $i, X27 : $i]:
% 0.66/0.91         (((k4_xboole_0 @ X26 @ (k1_tarski @ X27)) = (X26))
% 0.66/0.91          | (r2_hidden @ X27 @ X26))),
% 0.66/0.91      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.66/0.91  thf('33', plain,
% 0.66/0.91      (![X7 : $i, X8 : $i]:
% 0.66/0.91         (~ (r2_xboole_0 @ X7 @ X8) | ~ (r2_hidden @ (sk_C_1 @ X8 @ X7) @ X7))),
% 0.66/0.91      inference('cnf', [status(esa)], [t6_xboole_0])).
% 0.66/0.91  thf('34', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i]:
% 0.66/0.91         (((k4_xboole_0 @ X0 @ (k1_tarski @ (sk_C_1 @ X1 @ X0))) = (X0))
% 0.66/0.91          | ~ (r2_xboole_0 @ X0 @ X1))),
% 0.66/0.91      inference('sup-', [status(thm)], ['32', '33'])).
% 0.66/0.91  thf('35', plain,
% 0.66/0.91      (((k4_xboole_0 @ sk_A @ (k1_tarski @ (sk_C_1 @ sk_B @ sk_A))) = (sk_A))),
% 0.66/0.91      inference('sup-', [status(thm)], ['31', '34'])).
% 0.66/0.91  thf('36', plain,
% 0.66/0.91      (![X25 : $i, X26 : $i]:
% 0.66/0.91         (~ (r2_hidden @ X25 @ X26)
% 0.66/0.91          | ((k4_xboole_0 @ X26 @ (k1_tarski @ X25)) != (X26)))),
% 0.66/0.91      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.66/0.91  thf('37', plain,
% 0.66/0.91      ((((sk_A) != (sk_A)) | ~ (r2_hidden @ (sk_C_1 @ sk_B @ sk_A) @ sk_A))),
% 0.66/0.91      inference('sup-', [status(thm)], ['35', '36'])).
% 0.66/0.91  thf('38', plain, (~ (r2_hidden @ (sk_C_1 @ sk_B @ sk_A) @ sk_A)),
% 0.66/0.91      inference('simplify', [status(thm)], ['37'])).
% 0.66/0.91  thf('39', plain, ((r2_xboole_0 @ sk_A @ sk_B)),
% 0.66/0.91      inference('simplify_reflect-', [status(thm)], ['29', '30'])).
% 0.66/0.91  thf('40', plain,
% 0.66/0.91      (![X7 : $i, X8 : $i]:
% 0.66/0.91         (~ (r2_xboole_0 @ X7 @ X8) | (r2_hidden @ (sk_C_1 @ X8 @ X7) @ X8))),
% 0.66/0.91      inference('cnf', [status(esa)], [t6_xboole_0])).
% 0.66/0.91  thf('41', plain, ((r2_hidden @ (sk_C_1 @ sk_B @ sk_A) @ sk_B)),
% 0.66/0.91      inference('sup-', [status(thm)], ['39', '40'])).
% 0.66/0.91  thf('42', plain,
% 0.66/0.91      (![X0 : $i]:
% 0.66/0.91         (((k1_xboole_0) = (X0))
% 0.66/0.91          | (r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0))),
% 0.66/0.91      inference('sup-', [status(thm)], ['9', '10'])).
% 0.66/0.91  thf('43', plain,
% 0.66/0.91      (![X26 : $i, X27 : $i]:
% 0.66/0.91         (((k4_xboole_0 @ X26 @ (k1_tarski @ X27)) = (X26))
% 0.66/0.91          | (r2_hidden @ X27 @ X26))),
% 0.66/0.91      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.66/0.91  thf('44', plain,
% 0.66/0.91      (![X20 : $i, X21 : $i, X22 : $i, X24 : $i]:
% 0.66/0.91         ((r2_hidden @ (k4_tarski @ X20 @ X22) @ (k2_zfmisc_1 @ X21 @ X24))
% 0.66/0.91          | ~ (r2_hidden @ X22 @ X24)
% 0.66/0.91          | ~ (r2_hidden @ X20 @ X21))),
% 0.66/0.91      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.66/0.91  thf('45', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.66/0.91         (((k4_xboole_0 @ X0 @ (k1_tarski @ X1)) = (X0))
% 0.66/0.91          | ~ (r2_hidden @ X3 @ X2)
% 0.66/0.91          | (r2_hidden @ (k4_tarski @ X3 @ X1) @ (k2_zfmisc_1 @ X2 @ X0)))),
% 0.66/0.91      inference('sup-', [status(thm)], ['43', '44'])).
% 0.66/0.91  thf('46', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.91         (((k1_xboole_0) = (X0))
% 0.66/0.91          | (r2_hidden @ (k4_tarski @ (sk_C_1 @ X0 @ k1_xboole_0) @ X2) @ 
% 0.66/0.91             (k2_zfmisc_1 @ X0 @ X1))
% 0.66/0.91          | ((k4_xboole_0 @ X1 @ (k1_tarski @ X2)) = (X1)))),
% 0.66/0.91      inference('sup-', [status(thm)], ['42', '45'])).
% 0.66/0.91  thf('47', plain,
% 0.66/0.91      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_B @ sk_A))),
% 0.66/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.91  thf('48', plain,
% 0.66/0.91      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.66/0.91         ((r2_hidden @ X22 @ X23)
% 0.66/0.91          | ~ (r2_hidden @ (k4_tarski @ X20 @ X22) @ (k2_zfmisc_1 @ X21 @ X23)))),
% 0.66/0.91      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.66/0.91  thf('49', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i]:
% 0.66/0.91         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.66/0.91          | (r2_hidden @ X0 @ sk_A))),
% 0.66/0.91      inference('sup-', [status(thm)], ['47', '48'])).
% 0.66/0.91  thf('50', plain,
% 0.66/0.91      (![X0 : $i]:
% 0.66/0.91         (((k4_xboole_0 @ sk_B @ (k1_tarski @ X0)) = (sk_B))
% 0.66/0.91          | ((k1_xboole_0) = (sk_A))
% 0.66/0.91          | (r2_hidden @ X0 @ sk_A))),
% 0.66/0.91      inference('sup-', [status(thm)], ['46', '49'])).
% 0.66/0.91  thf('51', plain, (((sk_A) != (k1_xboole_0))),
% 0.66/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.91  thf('52', plain,
% 0.66/0.91      (![X0 : $i]:
% 0.66/0.91         (((k4_xboole_0 @ sk_B @ (k1_tarski @ X0)) = (sk_B))
% 0.66/0.91          | (r2_hidden @ X0 @ sk_A))),
% 0.66/0.91      inference('simplify_reflect-', [status(thm)], ['50', '51'])).
% 0.66/0.91  thf('53', plain,
% 0.66/0.91      (![X25 : $i, X26 : $i]:
% 0.66/0.91         (~ (r2_hidden @ X25 @ X26)
% 0.66/0.91          | ((k4_xboole_0 @ X26 @ (k1_tarski @ X25)) != (X26)))),
% 0.66/0.91      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.66/0.91  thf('54', plain,
% 0.66/0.91      (![X0 : $i]:
% 0.66/0.91         (((sk_B) != (sk_B))
% 0.66/0.91          | (r2_hidden @ X0 @ sk_A)
% 0.66/0.91          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.66/0.91      inference('sup-', [status(thm)], ['52', '53'])).
% 0.66/0.91  thf('55', plain,
% 0.66/0.91      (![X0 : $i]: (~ (r2_hidden @ X0 @ sk_B) | (r2_hidden @ X0 @ sk_A))),
% 0.66/0.91      inference('simplify', [status(thm)], ['54'])).
% 0.66/0.91  thf('56', plain, ((r2_hidden @ (sk_C_1 @ sk_B @ sk_A) @ sk_A)),
% 0.66/0.91      inference('sup-', [status(thm)], ['41', '55'])).
% 0.66/0.91  thf('57', plain, ($false), inference('demod', [status(thm)], ['38', '56'])).
% 0.66/0.91  
% 0.66/0.91  % SZS output end Refutation
% 0.66/0.91  
% 0.66/0.92  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
