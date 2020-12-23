%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2a05SGee6K

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:14 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 125 expanded)
%              Number of leaves         :   19 (  43 expanded)
%              Depth                    :   11
%              Number of atoms          :  439 ( 953 expanded)
%              Number of equality atoms :   46 ( 115 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ( X13 != X14 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('1',plain,(
    ! [X14: $i] :
      ( r1_tarski @ X14 @ X14 ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('2',plain,(
    ! [X18: $i] :
      ( ( k2_tarski @ X18 @ X18 )
      = ( k1_tarski @ X18 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( r2_hidden @ X24 @ X25 )
      | ~ ( r1_tarski @ ( k2_tarski @ X24 @ X26 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('6',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t41_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ~ ( ( A
         != ( k1_tarski @ B ) )
        & ( A != k1_xboole_0 )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ A )
              & ( C != B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ~ ( ( A
           != ( k1_tarski @ B ) )
          & ( A != k1_xboole_0 )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( C != B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t41_zfmisc_1])).

thf('7',plain,(
    ! [X28: $i] :
      ( ~ ( r2_hidden @ X28 @ sk_A )
      | ( X28 = sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( ( sk_C @ X0 @ sk_A )
        = sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_B_1 @ X0 )
      | ( r1_tarski @ sk_A @ X0 )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ~ ( r2_hidden @ sk_B_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['5','11'])).

thf('13',plain,(
    ! [X13: $i,X15: $i] :
      ( ( X13 = X15 )
      | ~ ( r1_tarski @ X15 @ X13 )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('14',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_B_1 ) @ sk_A )
    | ( ( k1_tarski @ sk_B_1 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    sk_A
 != ( k1_tarski @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ~ ( r1_tarski @ ( k1_tarski @ sk_B_1 ) @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['14','15'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('17',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k4_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('18',plain,(
    ! [X17: $i] :
      ( ( k4_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('19',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('20',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','22'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('24',plain,(
    ! [X12: $i] :
      ( ( X12 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X12 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('25',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ X8 @ X5 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('26',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['21'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['23','29'])).

thf('31',plain,(
    ! [X12: $i] :
      ( ( X12 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X12 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('32',plain,(
    ! [X28: $i] :
      ( ~ ( r2_hidden @ X28 @ sk_A )
      | ( X28 = sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( sk_B @ sk_A )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( sk_B @ sk_A )
    = sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X12: $i] :
      ( ( X12 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X12 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('37',plain,
    ( ( r2_hidden @ sk_B_1 @ sk_A )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    r2_hidden @ sk_B_1 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X24: $i,X26: $i,X27: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X24 @ X26 ) @ X27 )
      | ~ ( r2_hidden @ X26 @ X27 )
      | ~ ( r2_hidden @ X24 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r1_tarski @ ( k2_tarski @ X0 @ sk_B_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ( r1_tarski @ ( k2_tarski @ ( sk_D @ sk_A @ X0 @ k1_xboole_0 ) @ sk_B_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['23','29'])).

thf('44',plain,(
    ! [X28: $i] :
      ( ~ ( r2_hidden @ X28 @ sk_A )
      | ( X28 = sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ( ( sk_D @ sk_A @ X0 @ k1_xboole_0 )
        = sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( sk_D @ sk_A @ X0 @ k1_xboole_0 )
      = sk_B_1 ) ),
    inference('simplify_reflect-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X18: $i] :
      ( ( k2_tarski @ X18 @ X18 )
      = ( k1_tarski @ X18 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('49',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( r1_tarski @ ( k1_tarski @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['42','47','48'])).

thf('50',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    r1_tarski @ ( k1_tarski @ sk_B_1 ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['49','50'])).

thf('52',plain,(
    $false ),
    inference(demod,[status(thm)],['16','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2a05SGee6K
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:09:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.52  % Solved by: fo/fo7.sh
% 0.21/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.52  % done 195 iterations in 0.068s
% 0.21/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.52  % SZS output start Refutation
% 0.21/0.52  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.52  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.52  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.21/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.52  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.52  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.52  thf(d10_xboole_0, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.52  thf('0', plain,
% 0.21/0.52      (![X13 : $i, X14 : $i]: ((r1_tarski @ X13 @ X14) | ((X13) != (X14)))),
% 0.21/0.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.52  thf('1', plain, (![X14 : $i]: (r1_tarski @ X14 @ X14)),
% 0.21/0.52      inference('simplify', [status(thm)], ['0'])).
% 0.21/0.52  thf(t69_enumset1, axiom,
% 0.21/0.52    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.52  thf('2', plain, (![X18 : $i]: ((k2_tarski @ X18 @ X18) = (k1_tarski @ X18))),
% 0.21/0.52      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.52  thf(t38_zfmisc_1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.21/0.52       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.21/0.52  thf('3', plain,
% 0.21/0.52      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.21/0.52         ((r2_hidden @ X24 @ X25)
% 0.21/0.52          | ~ (r1_tarski @ (k2_tarski @ X24 @ X26) @ X25))),
% 0.21/0.52      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.21/0.52  thf('4', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (~ (r1_tarski @ (k1_tarski @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 0.21/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.52  thf('5', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['1', '4'])).
% 0.21/0.52  thf(d3_tarski, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.52       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.52  thf('6', plain,
% 0.21/0.52      (![X1 : $i, X3 : $i]:
% 0.21/0.52         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.21/0.52      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.52  thf(t41_zfmisc_1, conjecture,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ~( ( ( A ) != ( k1_tarski @ B ) ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.52          ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( ( C ) != ( B ) ) ) ) ) ) ))).
% 0.21/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.52    (~( ![A:$i,B:$i]:
% 0.21/0.52        ( ~( ( ( A ) != ( k1_tarski @ B ) ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.52             ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( ( C ) != ( B ) ) ) ) ) ) ) )),
% 0.21/0.52    inference('cnf.neg', [status(esa)], [t41_zfmisc_1])).
% 0.21/0.52  thf('7', plain,
% 0.21/0.52      (![X28 : $i]: (~ (r2_hidden @ X28 @ sk_A) | ((X28) = (sk_B_1)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('8', plain,
% 0.21/0.52      (![X0 : $i]: ((r1_tarski @ sk_A @ X0) | ((sk_C @ X0 @ sk_A) = (sk_B_1)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.52  thf('9', plain,
% 0.21/0.52      (![X1 : $i, X3 : $i]:
% 0.21/0.52         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.21/0.52      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.52  thf('10', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (r2_hidden @ sk_B_1 @ X0)
% 0.21/0.52          | (r1_tarski @ sk_A @ X0)
% 0.21/0.52          | (r1_tarski @ sk_A @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.52  thf('11', plain,
% 0.21/0.52      (![X0 : $i]: ((r1_tarski @ sk_A @ X0) | ~ (r2_hidden @ sk_B_1 @ X0))),
% 0.21/0.52      inference('simplify', [status(thm)], ['10'])).
% 0.21/0.52  thf('12', plain, ((r1_tarski @ sk_A @ (k1_tarski @ sk_B_1))),
% 0.21/0.52      inference('sup-', [status(thm)], ['5', '11'])).
% 0.21/0.52  thf('13', plain,
% 0.21/0.52      (![X13 : $i, X15 : $i]:
% 0.21/0.52         (((X13) = (X15))
% 0.21/0.52          | ~ (r1_tarski @ X15 @ X13)
% 0.21/0.52          | ~ (r1_tarski @ X13 @ X15))),
% 0.21/0.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.52  thf('14', plain,
% 0.21/0.52      ((~ (r1_tarski @ (k1_tarski @ sk_B_1) @ sk_A)
% 0.21/0.52        | ((k1_tarski @ sk_B_1) = (sk_A)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.52  thf('15', plain, (((sk_A) != (k1_tarski @ sk_B_1))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('16', plain, (~ (r1_tarski @ (k1_tarski @ sk_B_1) @ sk_A)),
% 0.21/0.52      inference('simplify_reflect-', [status(thm)], ['14', '15'])).
% 0.21/0.52  thf(d5_xboole_0, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.21/0.52       ( ![D:$i]:
% 0.21/0.52         ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.52           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.21/0.52  thf('17', plain,
% 0.21/0.52      (![X5 : $i, X6 : $i, X9 : $i]:
% 0.21/0.52         (((X9) = (k4_xboole_0 @ X5 @ X6))
% 0.21/0.52          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X5)
% 0.21/0.52          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 0.21/0.52      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.21/0.52  thf(t3_boole, axiom,
% 0.21/0.52    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.52  thf('18', plain, (![X17 : $i]: ((k4_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 0.21/0.52      inference('cnf', [status(esa)], [t3_boole])).
% 0.21/0.52  thf('19', plain,
% 0.21/0.52      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X8 @ X7)
% 0.21/0.52          | ~ (r2_hidden @ X8 @ X6)
% 0.21/0.52          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 0.21/0.52      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.21/0.52  thf('20', plain,
% 0.21/0.52      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X8 @ X6)
% 0.21/0.52          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 0.21/0.52      inference('simplify', [status(thm)], ['19'])).
% 0.21/0.52  thf('21', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['18', '20'])).
% 0.21/0.52  thf('22', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.21/0.52      inference('condensation', [status(thm)], ['21'])).
% 0.21/0.52  thf('23', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 0.21/0.52          | ((X1) = (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['17', '22'])).
% 0.21/0.52  thf(t7_xboole_0, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.52          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.21/0.52  thf('24', plain,
% 0.21/0.52      (![X12 : $i]:
% 0.21/0.52         (((X12) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X12) @ X12))),
% 0.21/0.52      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.21/0.52  thf('25', plain,
% 0.21/0.52      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X8 @ X7)
% 0.21/0.52          | (r2_hidden @ X8 @ X5)
% 0.21/0.52          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 0.21/0.52      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.21/0.52  thf('26', plain,
% 0.21/0.52      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.21/0.52         ((r2_hidden @ X8 @ X5) | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 0.21/0.52      inference('simplify', [status(thm)], ['25'])).
% 0.21/0.52  thf('27', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.21/0.52          | (r2_hidden @ (sk_B @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 0.21/0.52      inference('sup-', [status(thm)], ['24', '26'])).
% 0.21/0.52  thf('28', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.21/0.52      inference('condensation', [status(thm)], ['21'])).
% 0.21/0.52  thf('29', plain,
% 0.21/0.52      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.52  thf('30', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 0.21/0.52          | ((X1) = (k1_xboole_0)))),
% 0.21/0.52      inference('demod', [status(thm)], ['23', '29'])).
% 0.21/0.52  thf('31', plain,
% 0.21/0.52      (![X12 : $i]:
% 0.21/0.52         (((X12) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X12) @ X12))),
% 0.21/0.52      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.21/0.52  thf('32', plain,
% 0.21/0.52      (![X28 : $i]: (~ (r2_hidden @ X28 @ sk_A) | ((X28) = (sk_B_1)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('33', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_B @ sk_A) = (sk_B_1)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.52  thf('34', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('35', plain, (((sk_B @ sk_A) = (sk_B_1))),
% 0.21/0.52      inference('simplify_reflect-', [status(thm)], ['33', '34'])).
% 0.21/0.52  thf('36', plain,
% 0.21/0.52      (![X12 : $i]:
% 0.21/0.52         (((X12) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X12) @ X12))),
% 0.21/0.52      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.21/0.52  thf('37', plain, (((r2_hidden @ sk_B_1 @ sk_A) | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.52      inference('sup+', [status(thm)], ['35', '36'])).
% 0.21/0.52  thf('38', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('39', plain, ((r2_hidden @ sk_B_1 @ sk_A)),
% 0.21/0.52      inference('simplify_reflect-', [status(thm)], ['37', '38'])).
% 0.21/0.52  thf('40', plain,
% 0.21/0.52      (![X24 : $i, X26 : $i, X27 : $i]:
% 0.21/0.52         ((r1_tarski @ (k2_tarski @ X24 @ X26) @ X27)
% 0.21/0.52          | ~ (r2_hidden @ X26 @ X27)
% 0.21/0.52          | ~ (r2_hidden @ X24 @ X27))),
% 0.21/0.52      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.21/0.52  thf('41', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X0 @ sk_A)
% 0.21/0.52          | (r1_tarski @ (k2_tarski @ X0 @ sk_B_1) @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['39', '40'])).
% 0.21/0.52  thf('42', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (((sk_A) = (k1_xboole_0))
% 0.21/0.52          | (r1_tarski @ 
% 0.21/0.52             (k2_tarski @ (sk_D @ sk_A @ X0 @ k1_xboole_0) @ sk_B_1) @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['30', '41'])).
% 0.21/0.52  thf('43', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 0.21/0.52          | ((X1) = (k1_xboole_0)))),
% 0.21/0.52      inference('demod', [status(thm)], ['23', '29'])).
% 0.21/0.52  thf('44', plain,
% 0.21/0.52      (![X28 : $i]: (~ (r2_hidden @ X28 @ sk_A) | ((X28) = (sk_B_1)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('45', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (((sk_A) = (k1_xboole_0))
% 0.21/0.52          | ((sk_D @ sk_A @ X0 @ k1_xboole_0) = (sk_B_1)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['43', '44'])).
% 0.21/0.52  thf('46', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('47', plain, (![X0 : $i]: ((sk_D @ sk_A @ X0 @ k1_xboole_0) = (sk_B_1))),
% 0.21/0.52      inference('simplify_reflect-', [status(thm)], ['45', '46'])).
% 0.21/0.52  thf('48', plain,
% 0.21/0.52      (![X18 : $i]: ((k2_tarski @ X18 @ X18) = (k1_tarski @ X18))),
% 0.21/0.52      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.52  thf('49', plain,
% 0.21/0.52      ((((sk_A) = (k1_xboole_0)) | (r1_tarski @ (k1_tarski @ sk_B_1) @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['42', '47', '48'])).
% 0.21/0.52  thf('50', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('51', plain, ((r1_tarski @ (k1_tarski @ sk_B_1) @ sk_A)),
% 0.21/0.52      inference('simplify_reflect-', [status(thm)], ['49', '50'])).
% 0.21/0.52  thf('52', plain, ($false), inference('demod', [status(thm)], ['16', '51'])).
% 0.21/0.52  
% 0.21/0.52  % SZS output end Refutation
% 0.21/0.52  
% 0.21/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
